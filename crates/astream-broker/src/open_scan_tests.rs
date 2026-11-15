// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The streaming open (`open_scan.rs`, `OpenFold`) against the whole-buffer reference it
//! replaced (`ReadOpen::whole`: the log read into one buffer, every record decoded by the
//! reference `scan_from`, the indices folded over the vector and the tier built by
//! `Tier::from_parts`), aterm F16.
//!
//! - The scan alone: over random logs, sealed and plain, each damaged at random (a byte
//!   flipped, cut short, zeros or garbage appended), the streaming scan through windows of 1
//!   byte to the shipped size reports what `scan_from` reports and hands on exactly its
//!   records, at their bytes.
//! - The open: random logs written through the real writer (single publishes with re-sent
//!   keys, batches, group commits, wills, bindings, retirements, retention cuts and
//!   compactions that carry state, clean and unclean stops), sealed and plain, at residency
//!   budgets of 0, 512 B, 16 MiB and unbounded, each reopened as two copies of the same
//!   files after a random tear (a cut inside its last batch, zeros, a torn header, garbage, a
//!   flipped byte, a lost identity sidecar): the reference opens one, the streaming open
//!   through a small random window and pending bound the other, and the two answer every
//!   query alike — the refusal (or the explicit repair) included, the records read back with
//!   the cold reads they cost, every index, the tier's pages and window, the identity settled
//!   and the bytes left on disk.
//! - NEGATIVE CONTROLS: a scan that passes over the record straddling its window's end, and
//!   a tier that keeps its window from the head, each make the two differ.

use super::*;
use crate::storage::Dir;
use crate::test_scratch::Scratch;

/// xorshift64*: the tests' deterministic PRNG.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    fn below(&mut self, n: u64) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D) % n.max(1)
    }

    fn pick<T: Copy>(&mut self, of: &[T]) -> T {
        of[self.below(of.len() as u64) as usize]
    }
}

const KEY: [u8; 32] = [0x5a; 32];

/// The windows the streaming side reads through, from one byte to the shipped size.
const WINDOWS: [usize; 6] = [1, 7, 61, 300, 4_096, open_scan::WINDOW];
/// The bytes of an unended unit's records it holds before it folds them anyway.
const PENDINGS: [usize; 4] = [0, 300, 4_096, OPEN_PENDING];
/// The residency budgets: the newest record alone, a few records, 16 MiB, all.
const BUDGETS: [usize; 4] = [0, 512, 16 << 20, crate::tier::Tier::RESIDENT_ALL];

// ---------------------------------------------------------------------------------------
// The scan alone.
// ---------------------------------------------------------------------------------------

/// A record a streaming scan handed on, with what it said of it.
struct Handed {
    rec: BrokerRecord,
    bt: Option<u64>,
    at: u64,
    frame: Vec<u8>,
    ends_unit: bool,
}

/// The records a streaming scan handed on.
#[derive(Default)]
struct Kept(Vec<Handed>);

impl open_scan::Sink for Kept {
    fn record(
        &mut self,
        rec: BrokerRecord,
        bt: Option<u64>,
        at: u64,
        frame: &[u8],
        ends_unit: bool,
    ) -> bool {
        self.0.push(Handed {
            rec,
            bt,
            at,
            frame: frame.to_vec(),
            ends_unit,
        });
        true
    }
}

/// A stored frame of record `seq` (sealed under [`KEY`] when `sealed`), marked as `mark`.
fn stored(seq: u64, sealed: bool, mark: Mark, rng: &mut Rng) -> Vec<u8> {
    let rec = BrokerRecord {
        seq: Offset(seq),
        producer_id: 1 + rng.below(3),
        producer_seq: seq,
        subject: format!("/f/scan/s{}", rng.below(4)),
        body: vec![(seq % 251) as u8; rng.below(90) as usize],
        commit: None,
    };
    let plain = rec.encode_payload_marked(mark).expect("a record encodes");
    let at_rest = AtRestKey {
        key: KEY,
        seal_id: None,
    };
    let key = if sealed { Some(at_rest.as_ref()) } else { None };
    let payload = seal_disk_payload(key, seq, plain);
    Frame::new(payload).encode().expect("a frame encodes")
}

/// A random log of records from `base`, in batches, and where each record starts.
fn random_log(rng: &mut Rng, base: u64, sealed: bool) -> Vec<u8> {
    let mut bytes = Vec::new();
    let mut seq = base;
    for _ in 0..rng.below(9) {
        let n = 1 + rng.below(5);
        for i in 0..n {
            let mark = if i + 1 == n {
                Mark::Seal(n as u32)
            } else {
                Mark::Continues
            };
            bytes.extend_from_slice(&stored(seq, sealed, mark, rng));
            seq += 1;
        }
    }
    bytes
}

/// `bytes` damaged at random, or left whole.
fn damage(rng: &mut Rng, mut bytes: Vec<u8>) -> Vec<u8> {
    match rng.below(7) {
        0 => {}
        1 if !bytes.is_empty() => {
            let at = rng.below(bytes.len() as u64) as usize;
            bytes[at] ^= 1 << rng.below(8);
        }
        2 => {
            let cut = rng.below(bytes.len() as u64 + 1) as usize;
            bytes.truncate(cut);
        }
        3 => bytes.extend(std::iter::repeat_n(0u8, 1 + rng.below(40) as usize)),
        4 => bytes.extend((0..1 + rng.below(40)).map(|_| rng.below(256) as u8)),
        5 => {
            // A torn header: magic, version and flags landed, then nothing or zeros.
            bytes.extend_from_slice(&[0xA5, 0x71, 0x01, 0x00]);
            bytes.extend(std::iter::repeat_n(0u8, rng.below(12) as usize));
        }
        _ => {
            // A copy of a frame from inside the log appended whole: an offset gap.
            if bytes.len() > 64 {
                let from = rng.below(bytes.len() as u64 / 2) as usize;
                let tail = bytes[from..].to_vec();
                bytes.extend_from_slice(&tail[..tail.len().min(80)]);
            }
        }
    }
    bytes
}

/// The streaming scan of `bytes` through `reading` against the reference's, or the first
/// difference.
fn scan_differs(
    bytes: &[u8],
    key: Option<AtRestRef<'_>>,
    base: u64,
    floor: Option<u64>,
    reading: open_scan::Reading,
) -> Result<(), String> {
    let want = scan_from(bytes, key, base, floor, Mutation::Off);
    let mut kept = Kept::default();
    let got = open_scan::scan(bytes, reading, key, base, floor, Mutation::Off, &mut kept)
        .map_err(|e| format!("the streaming scan failed: {e}"))?;
    let a = &want.scan;
    let b = &got.scan;
    let mine = (b.count, b.valid_len, &b.tail, b.seal_end, b.floor_at);
    let theirs = (a.count, a.valid_len, &a.tail, a.seal_end, a.floor_at);
    if mine != theirs {
        return Err(format!(
            "the scan: streamed {mine:?}, the reference {theirs:?}"
        ));
    }
    if got.rest != bytes.get(a.valid_len..).unwrap_or(&[]) && !matches!(a.tail, Tail::Clean) {
        return Err("the bytes after the prefix differ".to_string());
    }
    if kept.0.len() != want.records.len() {
        return Err(format!(
            "{} records handed on, the reference decoded {}",
            kept.0.len(),
            want.records.len()
        ));
    }
    // Where the last record handed on as ending its unit ends: the scan's seal mark.
    let mut sealed_at = (base, 0usize);
    for (i, h) in kept.0.iter().enumerate() {
        let Handed {
            rec,
            bt,
            at,
            frame,
            ends_unit,
        } = h;
        if *ends_unit {
            sealed_at = (base + i as u64 + 1, *at as usize + frame.len());
        }
        let theirs = (&want.records[i], want.record_bts[i], want.record_at[i]);
        if (rec, *bt, *at) != theirs {
            return Err(format!(
                "record {i}: streamed {rec:?} {bt:?} {at}, the reference {theirs:?}"
            ));
        }
        let start = *at as usize;
        if bytes.get(start..start + frame.len()) != Some(frame.as_slice()) {
            return Err(format!("record {i}'s frame is not the bytes at {start}"));
        }
    }
    if sealed_at != a.seal_end {
        return Err(format!(
            "the records handed on as ending their units end at {sealed_at:?}, the scan's \
             seal mark at {:?}",
            a.seal_end
        ));
    }
    Ok(())
}

fn reading(window: usize) -> open_scan::Reading {
    open_scan::Reading {
        window,
        drop_straddle: false,
    }
}

#[test]
fn the_streaming_scan_answers_as_the_whole_buffer_scan_over_damaged_logs() {
    for seed in 0..600u64 {
        let mut rng = Rng::new(seed);
        let sealed = seed % 3 == 0;
        let base = if seed % 5 == 0 { 0 } else { rng.below(1 << 40) };
        let log = random_log(&mut rng, base, sealed);
        let bytes = damage(&mut rng, log);
        let at_rest = AtRestKey {
            key: KEY,
            seal_id: None,
        };
        let key = if sealed { Some(at_rest.as_ref()) } else { None };
        let floor = match rng.below(3) {
            0 => None,
            1 => Some(base),
            _ => Some(base + rng.below(12)),
        };
        for window in WINDOWS {
            if let Err(e) = scan_differs(&bytes, key, base, floor, reading(window)) {
                panic!("seed {seed} window {window} sealed {sealed}: {e}");
            }
        }
    }
}

/// NEGATIVE CONTROL: a scan that passes over the record straddling its window's end differs
/// from the reference on a log longer than the window.
#[test]
fn a_scan_that_drops_the_record_straddling_its_window_is_caught() {
    let mut caught = 0;
    for seed in 0..40u64 {
        let mut rng = Rng::new(seed);
        let bytes = random_log(&mut rng, 0, false);
        if bytes.len() < 200 {
            continue;
        }
        let mutant = open_scan::Reading {
            window: 61,
            drop_straddle: true,
        };
        if scan_differs(&bytes, None, 0, None, mutant).is_err() {
            caught += 1;
        }
        assert!(
            scan_differs(&bytes, None, 0, None, reading(61)).is_ok(),
            "seed {seed}: the unmutated scan agrees"
        );
    }
    assert!(caught > 0, "no seed caught the dropped straddling record");
}

// ---------------------------------------------------------------------------------------
// The open.
// ---------------------------------------------------------------------------------------

/// How a seed's log is held.
#[derive(Clone, Copy, Debug)]
struct Shape {
    sealed: bool,
    /// Strict, sealed, and opened with the anti-rollback watermark verified.
    verified: bool,
    budget: usize,
}

fn options(shape: Shape, read: ReadOpen) -> OpenOptions {
    let mut opts = OpenOptions::new(if shape.verified {
        Durability::Strict
    } else {
        Durability::Relaxed
    });
    opts.resident_budget = Some(shape.budget);
    opts.read = read;
    opts
}

/// Open the log at `path` as `shape` holds it, reading it as `read` says (`repair`: the
/// explicit repair's open).
fn open(path: &Path, shape: Shape, read: ReadOpen, repair: bool) -> io::Result<BrokerLog> {
    let opts = options(shape, read);
    let key = if shape.sealed { Some(KEY) } else { None };
    #[cfg(feature = "anti-rollback")]
    let mode = match (shape.verified, hw_exists(path)) {
        (false, _) => AntiRollbackMode::Off,
        (true, true) => AntiRollbackMode::Verify,
        (true, false) => AntiRollbackMode::Init,
    };
    #[cfg(not(feature = "anti-rollback"))]
    let mode = AntiRollbackMode::Off;
    BrokerLog::open_core(
        Storage::Os(path),
        &opts,
        repair,
        key,
        mode,
        BrokerLog::prepare_nothing,
    )
    .map(|(log, _)| log)
}

#[cfg(feature = "anti-rollback")]
fn hw_exists(path: &Path) -> bool {
    let mut p = path.as_os_str().to_owned();
    p.push(".hw");
    Path::new(&p).exists()
}

/// Copy every file of the log at `from` (the log and its sidecars, `<log>*`) into `dir`.
fn copy_log(from: &Path, dir: &Path) -> std::path::PathBuf {
    std::fs::create_dir_all(dir).unwrap();
    let name = from.file_name().unwrap().to_string_lossy().to_string();
    for entry in std::fs::read_dir(from.parent().unwrap()).unwrap() {
        let entry = entry.unwrap();
        let file = entry.file_name().to_string_lossy().to_string();
        if file.starts_with(&name) && entry.file_type().unwrap().is_file() {
            std::fs::copy(entry.path(), dir.join(&file)).unwrap();
        }
    }
    dir.join(name)
}

fn sorted<K: Ord + std::fmt::Debug, V: std::fmt::Debug>(m: &HashMap<K, V>) -> String {
    let mut v: Vec<(&K, &V)> = m.iter().collect();
    v.sort_by(|a, b| a.0.cmp(b.0));
    format!("{v:?}")
}

/// Everything the open log at `path` answers, rendered; `prior_id`: the identity its `.id`
/// named before the open, if any (a fresh id is rendered as `fresh`, since each copy mints
/// its own).
fn answers(log: &BrokerLog, path: &Path, prior_id: Option<[u8; 16]>) -> Vec<String> {
    let mut out = Vec::new();
    let id = log.identity.identity.id;
    let derivable = prior_id.is_none() && log.next.0 > log.base.0;
    let id_said = if Some(id) == prior_id {
        "prior".to_string()
    } else if derivable {
        format!("{id:?}")
    } else {
        "fresh".to_string()
    };
    let mut sidecar = log.identity.clone();
    sidecar.identity.id = [0; 16];
    out.push(format!("identity {id_said} {sidecar:?}"));
    out.push(format!(
        "base {} head {} durable_len {} newest_at {:?} log_id {:?} durable_head {} replica {} \
         watermark {} served {:?} last_bt {}",
        log.base.0,
        log.next.0,
        log.durable_len,
        log.newest_at,
        log.log_id,
        log.durable_head,
        log.replica,
        log.head_watermark.is_some(),
        log.served,
        log.last_bt_ms,
    ));
    out.push(format!(
        "file {} bytes",
        std::fs::metadata(path).map(|m| m.len()).unwrap_or(0)
    ));
    out.push(format!("tally at open {:?}", log.tier_tally()));
    let tier = &log.tier;
    out.push(format!(
        "tier len {} resident {} bytes {} subjects {}",
        tier.len(),
        tier.resident(),
        tier.resident_bytes(),
        tier.live_subjects()
    ));
    for i in 0..tier.len() {
        out.push(format!(
            "summary {i}: {:?} at {:?} bt {:?} hot {}",
            tier.summary(i),
            tier.at(i),
            tier.bt(i),
            tier.hot(i).map(|r| r.seq.0).is_some()
        ));
    }
    log.reset_cold_reads();
    for i in 0..tier.len() {
        out.push(format!("record {i}: {:?}", log.record_arc(i)));
    }
    out.push(format!("cold reads {}", log.cold_reads()));
    out.push(format!("dedup {:?}", log.dedup.entries()));
    out.push(format!("last {:?}", log.last));
    out.push(format!("charges {}", sorted(&log.subject_charges)));
    out.push(format!(
        "per producer {}",
        sorted(&log.subjects_per_producer)
    ));
    out.push(format!("wills {}", sorted(&log.durable_latest_wills)));
    let by_subject: HashMap<&String, Vec<&u64>> = log
        .durable_wills_by_subject
        .iter()
        .map(|(k, v)| {
            let mut v: Vec<&u64> = v.iter().collect();
            v.sort();
            (k, v)
        })
        .collect();
    out.push(format!("wills by subject {}", sorted(&by_subject)));
    let reserved: HashMap<&u64, Vec<&String>> = log
        .will_reserved
        .iter()
        .map(|(k, v)| {
            let mut v: Vec<&String> = v.iter().collect();
            v.sort();
            (k, v)
        })
        .collect();
    out.push(format!("reserved {}", sorted(&reserved)));
    out.push(format!("pending wills {:?}", log.pending_wills()));
    out.push(format!("high water {}", sorted(&log.high_water)));
    out.push(format!("carried wills {}", sorted(&log.carried_wills)));
    out.push(format!("carried last {:?}", log.carried_last));
    out.push(format!("carried last bt {:?}", log.carried_last_bt));
    out.push(format!("carried charges {:?}", log.carried_charges));
    out.push(format!("tainted {}", log.uncarried_cut_tainted));
    out.push(format!("relay floors {:?}", log.relay_floors));
    out.push(format!("bind {}", sorted(&log.bind)));
    out.push(format!("producer bt {}", sorted(&log.producer_last_bt)));
    out.push(format!("groups {}", sorted(&log.group_commits)));
    out.push(format!("stats {:?}", log.stats()));
    #[cfg(feature = "retention")]
    out.push(plan(log));
    out.push(format!("read from base {:?}", log.read_from(log.base)));
    out
}

/// The retention plan over the open log's tier under rules of the test's own (one batch
/// subject by its last value, the rest as a prefix by bytes and age), a minute after its
/// newest record's broker time.
#[cfg(feature = "retention")]
fn plan(log: &BrokerLog) -> String {
    use crate::retention::{Retention, Rule};
    use std::time::Duration;
    let rules = Retention::new(
        vec![
            Rule::hold("/f/open/b1").unwrap().last_only(),
            Rule::prefix("/f/open/*")
                .unwrap()
                .max_bytes(6_000)
                .max_age(Duration::from_secs(60)),
        ],
        Rule::default_hold(),
    )
    .unwrap();
    let tier = &log.tier;
    let newest = tier.len().checked_sub(1).and_then(|i| tier.bt(i));
    let (groups, held, stamps) = (HashMap::new(), BTreeMap::new(), Vec::new());
    let scene = crate::retention::Scene {
        base: log.base.0,
        ceiling: log.next.0,
        stamps: &stamps,
        groups: &groups,
        held: &held,
        now: newest.unwrap_or(0).saturating_add(60_000),
    };
    format!(
        "plan {:?}",
        crate::retention::plan_over(&rules, &scene, tier, None)
    )
}

/// What one open of `path` (`read`, `repair`) answers: its refusal, with the copy's own
/// folder taken out of the message, or [`answers`].
fn opened(path: &Path, shape: Shape, read: ReadOpen, repair: bool) -> Vec<String> {
    let prior_id = match logid::read(&Dir::Os(path.to_path_buf())) {
        Ok(Prior::Recorded(s)) => Some(s.identity.id),
        _ => None,
    };
    match open(path, shape, read, repair) {
        Ok(log) => answers(&log, path, prior_id),
        Err(e) => {
            let folder = path.parent().unwrap().display().to_string();
            vec![format!(
                "refused {:?}: {}",
                e.kind(),
                e.to_string().replace(&folder, "<dir>")
            )]
        }
    }
}

/// The first line two answers differ in.
fn first_difference(a: &[String], b: &[String]) -> Option<String> {
    for (i, (x, y)) in a.iter().zip(b).enumerate() {
        if x != y {
            return Some(format!("line {i}:\n  reference {x}\n  streamed  {y}"));
        }
    }
    if a.len() != b.len() {
        return Some(format!("{} lines against {}", a.len(), b.len()));
    }
    None
}

/// Tear the log at `path` (which a log just wrote and was dropped from) at random, or leave
/// it: what was done, and the bytes it held before.
fn tear(rng: &mut Rng, path: &Path) -> (&'static str, Vec<u8>) {
    let before = std::fs::read(path).unwrap();
    let mut bytes = before.clone();
    let what = match rng.below(9) {
        0 if bytes.len() > 8 => {
            let cut = 1 + rng.below(bytes.len().min(160) as u64) as usize;
            bytes.truncate(bytes.len() - cut);
            "cut short"
        }
        1 => {
            bytes.extend(std::iter::repeat_n(0u8, 1 + rng.below(64) as usize));
            "zeros appended"
        }
        2 => {
            bytes.extend_from_slice(&[0xA5, 0x71, 0x01, 0x00]);
            bytes.extend(std::iter::repeat_n(0u8, rng.below(10) as usize));
            "a torn header"
        }
        3 => {
            bytes.extend((0..1 + rng.below(30)).map(|_| rng.below(256) as u8));
            "garbage appended"
        }
        4 if bytes.len() > 16 => {
            let at = bytes.len() - 1 - rng.below(bytes.len().min(400) as u64) as usize;
            bytes[at] ^= 1 << rng.below(8);
            "a byte flipped"
        }
        5 => {
            let mut id = path.as_os_str().to_owned();
            id.push(".id");
            let _ = std::fs::remove_file(id);
            "the identity sidecar lost"
        }
        _ => "whole",
    };
    std::fs::write(path, &bytes).unwrap();
    (what, before)
}

/// What the comparisons of a run of seeds met: opens that served, that cut bytes off the
/// log, that refused, and repairs that served.
#[derive(Debug, Default)]
struct Met {
    served: usize,
    cut: usize,
    refused: usize,
    repaired: usize,
}

/// The reference and the streaming open (`stream`) of copies of the log at `path`, and the
/// explicit repair of each when both refuse: the first difference, if any; whether they
/// refused.
fn compare(
    root: &Path,
    path: &Path,
    shape: Shape,
    stream: ReadOpen,
    tag: &str,
    met: &mut Met,
) -> Result<bool, String> {
    let before = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
    let whole = ReadOpen {
        whole: true,
        ..ReadOpen::default()
    };
    let a = copy_log(path, &root.join(format!("{tag}-ref")));
    let b = copy_log(path, &root.join(format!("{tag}-stream")));
    let ra = opened(&a, shape, whole, false);
    let rb = opened(&b, shape, stream, false);
    if let Some(d) = first_difference(&ra, &rb) {
        return Err(d);
    }
    let refused = ra.first().is_some_and(|l| l.starts_with("refused"));
    if !refused {
        met.served += 1;
        if std::fs::metadata(&a).map(|m| m.len()).unwrap_or(0) < before {
            met.cut += 1;
        }
    }
    if refused {
        met.refused += 1;
        let a = copy_log(path, &root.join(format!("{tag}-ref-repair")));
        let b = copy_log(path, &root.join(format!("{tag}-stream-repair")));
        let ra = opened(&a, shape, whole, true);
        let rb = opened(&b, shape, stream, true);
        if let Some(d) = first_difference(&ra, &rb) {
            return Err(format!("the repair: {d}"));
        }
        if !ra.first().is_some_and(|l| l.starts_with("refused")) {
            met.repaired += 1;
        }
    }
    Ok(refused)
}

/// One seeded stream: the real writer's records into a log held as `shape` says, and at
/// every reopen, after a random tear, the reference and the streaming open of its copies
/// compared ([`compare`]). The streaming side reads through `mutant`'s negative control when
/// one is set. `Err`: the first difference.
fn stream_differs(seed: u64, shape: Shape, mutant: ReadOpen, met: &mut Met) -> Result<(), String> {
    let root = Scratch::new(&format!("open-stream-{seed}"));
    let path = root.path().join("log");
    let mut rng = Rng::new(seed);
    let shipped = ReadOpen::default();
    let mut log = open(&path, shape, shipped, false).unwrap_or_else(|e| panic!("first open: {e}"));
    let mut next_seq = [0u64; 4];
    let mut reopen = 0usize;
    for step in 0..160 {
        let roll = rng.below(100);
        if roll < 40 {
            let pid = 1 + rng.below(4);
            let slot = &mut next_seq[pid as usize - 1];
            let pseq = if rng.below(6) == 0 && *slot > 0 {
                rng.below(*slot)
            } else {
                *slot += 1 + rng.below(2);
                *slot
            };
            let body = vec![(step % 251) as u8; rng.below(300) as usize];
            log.publish(pid, pseq, format!("/f/open/s{}", rng.below(7)), body)
                .unwrap_or_else(|e| panic!("step {step}: publish: {e}"));
        } else if roll < 58 {
            for _ in 0..1 + rng.below(30) {
                let pid = 1 + rng.below(4);
                next_seq[pid as usize - 1] += 1;
                let pseq = next_seq[pid as usize - 1];
                let body = vec![7u8; rng.below(200) as usize];
                let _ = log.stage_publish(pid, pseq, format!("/f/open/b{}", rng.below(4)), body);
            }
            log.commit_batch()
                .unwrap_or_else(|e| panic!("step {step}: batch: {e}"));
        } else if roll < 64 {
            let upto = rng.below(log.head().0 + 1);
            log.commit(format!("g{}", rng.below(3)), upto)
                .unwrap_or_else(|e| panic!("step {step}: commit: {e}"));
        } else if roll < 69 {
            let pid = 1 + rng.below(4);
            let will = WillRecord {
                producer_id: pid,
                producer_seq: next_seq[pid as usize - 1] + 1 + rng.below(3),
                subject: format!("/f/open/will{}", rng.below(3)),
                body: vec![9u8; rng.below(40) as usize],
            };
            if log.stage_will_register(&will).is_ok() {
                log.commit_batch()
                    .unwrap_or_else(|e| panic!("step {step}: will: {e}"));
            }
        } else if roll < 72 {
            let pid = 1 + rng.below(4);
            if log.stage_bind(pid, format!("principal-{pid}")).is_ok() {
                log.commit_batch()
                    .unwrap_or_else(|e| panic!("step {step}: bind: {e}"));
            }
        } else if roll < 75 {
            let pid = 1 + rng.below(4);
            let _ = log.retire_subject(pid, &format!("/f/open/s{}", rng.below(7)));
        } else if roll < 81 {
            #[cfg(feature = "retention")]
            {
                let span = log.head().0 - log.base().0;
                let cut = Offset(log.base().0 + rng.below(span / 2 + 1));
                // The plain cut refuses below a record only it keeps (a binding, a will);
                // the cut that carries state never does.
                if rng.below(2) == 0 {
                    let _ = log.retain_before(cut);
                } else {
                    log.retain_before_carrying_state(cut)
                        .unwrap_or_else(|e| panic!("step {step}: retention: {e}"));
                }
            }
        } else if roll < 93 {
            // Stop (cleanly or not), tear, and hold the two opens of the copies to each other.
            if rng.below(3) == 0 {
                log.close_clean()
                    .unwrap_or_else(|e| panic!("step {step}: close: {e}"));
            }
            drop(log);
            let (torn, before) = tear(&mut rng, &path);
            let stream = ReadOpen {
                window: Some(rng.pick(&WINDOWS)),
                pending: Some(rng.pick(&PENDINGS)),
                ..mutant
            };
            let refused = compare(
                root.path(),
                &path,
                shape,
                stream,
                &format!("r{reopen}"),
                met,
            )
            .map_err(|e| format!("step {step}, reopen {reopen} after {torn}, {stream:?}: {e}"))?;
            reopen += 1;
            // A tear even the repair refuses (an intact frame that fails to authenticate) is
            // undone, and the log goes on from what it held.
            log = match open(&path, shape, shipped, refused) {
                Ok(log) => log,
                Err(_) => {
                    std::fs::write(&path, &before).unwrap();
                    open(&path, shape, shipped, false)
                        .unwrap_or_else(|e| panic!("step {step}: the reopen after {torn}: {e}"))
                }
            };
        } else {
            log.publish(0, 0, "/f/open/zero".to_string(), Vec::new())
                .unwrap_or_else(|e| panic!("step {step}: publish: {e}"));
        }
    }
    drop(log);
    compare(root.path(), &path, shape, shipped, "last", met).map(|_| ())
}

fn shape_of(seed: u64) -> Shape {
    let sealed = cfg!(feature = "at-rest") && seed % 3 == 1;
    Shape {
        sealed,
        verified: cfg!(feature = "anti-rollback") && sealed && seed % 2 == 0,
        budget: BUDGETS[(seed % 4) as usize],
    }
}

#[test]
fn the_streaming_open_answers_every_query_as_the_whole_buffer_open() {
    let mut met = Met::default();
    let refolds = REFOLDS.with(std::cell::Cell::get);
    let windows = crate::tier::WINDOWS.with(std::cell::Cell::get);
    for seed in 0..24u64 {
        let shape = shape_of(seed);
        if let Err(e) = stream_differs(seed, shape, ReadOpen::default(), &mut met) {
            panic!("seed {seed} {shape:?}: {e}");
        }
    }
    let refolds = REFOLDS.with(std::cell::Cell::get) - refolds;
    let (held, reread) = crate::tier::WINDOWS.with(std::cell::Cell::get);
    let (held, reread) = (held - windows.0, reread - windows.1);
    // Every shape of open the comparison is for was met: opens that cut a torn tail, opens
    // that refused and repairs after them, streaming opens that folded the log again, and
    // streaming opens whose window was the records they held decoded or was read again.
    assert!(
        met.cut > 0 && met.refused > 0 && met.repaired > 0 && refolds > 0 && held > 0 && reread > 0,
        "the seeds met too little: {met:?}, {refolds} refolds, {held} windows held, {reread} \
         read again"
    );
}

/// NEGATIVE CONTROL: an open whose scan passes over the record straddling its window, and
/// one whose tier keeps its window from the head of the log, each differ from the reference.
#[test]
fn a_streaming_open_that_drops_a_straddling_record_or_windows_from_the_head_is_caught() {
    for (name, mutant, budget) in [
        (
            "a dropped straddling record",
            ReadOpen {
                drop_straddle: true,
                ..ReadOpen::default()
            },
            crate::tier::Tier::RESIDENT_ALL,
        ),
        (
            "a window from the head",
            ReadOpen {
                window_from_head: true,
                ..ReadOpen::default()
            },
            512,
        ),
    ] {
        let caught = (0..6u64).any(|seed| {
            let shape = Shape {
                sealed: false,
                verified: false,
                budget,
            };
            stream_differs(seed, shape, mutant, &mut Met::default()).is_err()
        });
        assert!(caught, "{name}: no seed caught it");
    }
}

// ---------------------------------------------------------------------------------------
// The tier's columns, reserved once.
// ---------------------------------------------------------------------------------------

/// Reopen the log at `path` as `shape` holds it: the log, and the capacities its open moved
/// the tier's columns off as records joined (`tier::MOVED`), each a block freed.
fn reopened_moving(path: &Path, shape: Shape) -> (BrokerLog, Vec<usize>) {
    crate::tier::MOVED.with(|m| m.borrow_mut().clear());
    let log =
        open(path, shape, ReadOpen::default(), false).unwrap_or_else(|e| panic!("the reopen: {e}"));
    let moved = crate::tier::MOVED.with(|m| std::mem::take(&mut *m.borrow_mut()));
    (log, moved)
}

/// Publish `n` more records of one size to `log`, in batches.
fn publish_uniform(log: &mut BrokerLog, n: u64) {
    let from = log.head().0;
    for seq in from..from + n {
        log.stage_publish(1, seq + 1, "/f/open/even".to_string(), vec![5u8; 64])
            .unwrap_or_else(|e| panic!("stage {seq}: {e:?}"));
        if (seq + 1) % 500 == 0 {
            log.commit_batch()
                .unwrap_or_else(|e| panic!("batch at {seq}: {e}"));
        }
    }
    log.commit_batch()
        .unwrap_or_else(|e| panic!("the last batch: {e}"));
}

/// An open reserves the tier's columns once for the records its log holds, after any stop:
/// a kill leaves the identity sidecar's head at what the last OPEN saw (0 for a log a run
/// created, or the count before that run's appends), and an open that reserved for that
/// head moved its columns off it, and grew them through every size past it, as soon as its
/// scan passed it (aterm F16's review). Past [`crate::tier::SAMPLE`] records no open here
/// moves its columns off a block: not after a run that created the log, not after one that
/// reopened it and appended as many again, and not after a clean close, whose count the
/// open reserves at once.
#[test]
fn an_open_reserves_its_columns_once_after_an_unclean_stop_as_after_a_clean_one() {
    let root = Scratch::new("open-reserve-once");
    let path = root.path().join("log");
    let shape = Shape {
        sealed: false,
        verified: false,
        budget: 16 << 20,
    };
    let sample = crate::tier::SAMPLE;
    let mut log = open(&path, shape, ReadOpen::default(), false)
        .unwrap_or_else(|e| panic!("the first open: {e}"));
    publish_uniform(&mut log, 20_000);
    drop(log);
    let (mut log, moved) = reopened_moving(&path, shape);
    assert_eq!(log.head().0, 20_000);
    assert!(
        moved.iter().all(|&c| c <= sample),
        "after a kill of the run that created the log, the open moved its columns off {moved:?}"
    );
    publish_uniform(&mut log, 20_000);
    drop(log);
    let (mut log, moved) = reopened_moving(&path, shape);
    assert_eq!(log.head().0, 40_000);
    assert!(
        moved.iter().all(|&c| c <= sample),
        "after a kill of a run that saw 20,000 records at its open, the open moved its \
         columns off {moved:?}"
    );
    log.close_clean()
        .unwrap_or_else(|e| panic!("the clean close: {e}"));
    drop(log);
    let (log, moved) = reopened_moving(&path, shape);
    assert_eq!(log.head().0, 40_000);
    assert!(
        moved.is_empty(),
        "after a clean close, the open moved its columns off {moved:?}"
    );
}
