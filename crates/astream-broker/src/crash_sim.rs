// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! THE CRASH SIMULATION: the power-loss law of the durable log, checked on the REAL
//! code. The real writer (`stage_*` + `commit_batch`, with its batch marks) and the
//! real open (recovery, the classifier, the identity rules, both sidecar phases, the
//! clean close) run unchanged against a simulated device through the storage seam
//! (`storage.rs`), and the device is "crashed" after every operation it sees.
//!
//! # The device (`sim_device.rs`)
//!
//! The log file is a byte array in fixed-size blocks (16, 32 or 64 bytes: every 4 KiB
//! outcome is one of these, and smaller blocks only add hole positions). Each block is
//! VOLATILE (written since the last flush, in the page cache only), ISSUED in barrier
//! epoch `k`, or DURABLE. A write makes blocks volatile; an ordering BARRIER
//! (`F_BARRIERFSYNC`, the Ordered tier's per-batch flush) moves the volatile blocks —
//! their contents then — and the file's size into a new epoch; a full flush
//! (`sync_data`/`sync_all`) makes every block, every issued epoch, and the file's size
//! durable. The identity sidecar is replaced atomically and is durable when the
//! replacement returns (it is tmp + fsync + rename, an `F_FULLFSYNC`): it DRAINS every
//! issued epoch — the device empties its queue — but does NOT make the log's volatile
//! blocks durable, which is what lets a sidecar written in the wrong order relative to
//! the log's flush be seen (negative control NC5).
//!
//! - A POWER LOSS image is every durable byte, then every block of a PREFIX of the
//!   issued epochs (each at its size), then a subset of the NEXT epoch's blocks — the
//!   volatile blocks counting as one more epoch after the newest barrier — with or
//!   without that epoch's size change; space nothing persisted reads zeros or `0xEE`
//!   garbage (alternating image by image). The image is then all durable. That is
//!   fcntl(2)'s barrier contract: nothing issued after a barrier reaches the media
//!   before everything issued before it. The DEVICE allows any subset of the next
//!   epoch; the sweep takes EVERY subset at a crash point, for each prefix of epochs,
//!   while they fit its budget (64 images, 16 in a second crash: at most 6 blocks, 5
//!   with a size change pending), and beyond that a SAMPLE trimmed to the budget —
//!   none and all always, the shortest prefixes, and a seeded pick of the longer
//!   prefixes, each block alone, all but each one and seeded random subsets — so a
//!   loss that needs two particular blocks among many is tried only if the sample
//!   lands on it.
//!   Each sweep prints how many crash points it enumerated and how many it sampled.
//! - The PLAIN-FSYNC device (negative control NC1) ignores barriers: every block written
//!   since the last full flush stays volatile, any subset of them persisting.
//! - A PROCESS CRASH (same boot) loses nothing the kernel holds: the device carries on
//!   as it was, its volatile blocks still volatile, which is how a crash during the
//!   NEXT open can still lose them. A process killed DURING an append leaves a SHORT
//!   WRITE: the bytes before it plus a block-aligned prefix of it (Linux stops a write
//!   between pages for a fatal signal), taken at every such boundary.
//!
//! # What is checked, on every image
//!
//! | id | property |
//! |----|----------|
//! | P1 | With a known floor, the open never refuses a power-loss or process-crash image. |
//! | P2 | The recovered records are byte-for-byte the first `k` written; for Strict and Ordered, `k` is at a batch boundary. |
//! | P3 | Every record a full flush covered before the loss is present: the open's flush, a batch's under Strict, an escalation's, the horizon's, `sync_full`'s, a clean close's — and every record below the durable head the PRODUCT claimed. |
//! | P3e | Every escalated record acked before the loss is present (Ordered and Relaxed). |
//! | P4 | If any acked record is missing, the identity moved. |
//! | P5 | After a clean close, a power loss loses nothing and moves nothing. |
//! | P6 | A same-boot crash outside an open — a short write included — loses nothing acked and moves nothing. |
//! | P7 | A reader resuming at `min(cursor, continues(...))` skips nothing and finds the records it saw. |
//! | P8 | Rot below the floor, or in any batch but the newest, is refused, never cut; rot in the newest batch above the floor is refused or cut with a move (Relaxed after an unclean stop: cut with a move anywhere above the floor). |
//!
//! What was ACKED when is not modelled: it is what the product did. The harness drives
//! the writer's steps on the real log — stage, `commit_batch`, and, when the commit's
//! pure answer ([`Committed`]) owes one, the full flush through the same flush handle the
//! broker's writer takes outside the lock — and marks a record acked when the product
//! would ack it: below `Committed::visible_now` at the commit, everything once the owed
//! flush is done. Which records are ESCALATED is the harness's own oracle (their
//! subjects, producers and groups), independent of the table the product holds, so a
//! product that stops escalating (NC3) is caught. A crash inside an open may recover
//! records of the run before it that the open was cutting (its cut not yet durable): P2
//! accepts a prefix of either run's writes there.
//!
//! Workloads escalate a batch through each kind of rule — a `Subject` rule, a
//! `PrincipalPrefix` rule bound by a `/a/bind` staged earlier in the same batch, a
//! `Group` commit — or not, and follow it with nothing, the Ordered horizon's full flush
//! (Ordered only: the writer keeps the horizon for that tier alone) or `sync_full`.
//!
//! Beside the sweeps: the ROT arm (every byte of a clean log flipped: P2, P4, P8), an
//! OLDER BUILD's records appended above the floor after a revert (P2, P3, P4, and never
//! a refusal the rules before the floor would not make), record frames PLANTED inside
//! record bodies (the sweep's properties, P1 above all), a restored copy (P7), and an
//! open that cuts on what the next open cannot re-derive — the inputs the sweep's opens
//! never take: a `Lossy` state, an embedder's prepare, a repair (of a FORMAT 1 log too),
//! a tier other than the last run's, rot in the newest batch in the run's own boot — and
//! dies at any point of its cut.
//!
//! # Negative controls
//!
//! Each re-introduces one bug and must break the property it names, which the test
//! asserts along with the failure's reason: NC1 (a device that ignores barriers, under
//! the Ordered tier: P1, a later batch completed behind a hole — while P2 still holds,
//! so the failure is a refusal, never a silent loss), NC2 (the writer before the marks,
//! whose torn batches read as damage behind completed units: P1), NC3 (the escalation
//! table emptied while the harness still expects escalated records durable: P3e), NC4
//! (power-loss images recovered as the same boot: P4), NC5 (the floor written before
//! the open's flush: P1), NC6 (cut at any damage: P8), NC7 (the horizon's full flush
//! issued as a barrier, the product told it was full: P3), NC8 (a Relaxed cut at the
//! first damage with no unclean verdict: P8, rot in an older batch cut), NC9 (lineage for
//! a restored shorter copy: P7), NC10 (a reader that re-bases at the head after a
//! covered move: P7), NC11 (no empty-frame rule: P1).
//!
//! No clock is read, nothing sleeps, nothing retries: every choice is the fixed seed's.

use std::collections::BTreeSet;
use std::fmt;

use astream_wire::{Offset, HEADER_SIZE};

use crate::brecord::BrokerRecord;
use crate::logid::{self, Lineage, Prior};
use crate::sim_device::{images, Device, Rng, Sim, SimDevice};
use crate::storage::Dir;
#[cfg(doc)]
use crate::store::Committed;
use crate::store::{
    is_hidden_subject, AntiRollbackMode, Boot, Durability, InjectedFaults, Mutation, OpenOptions,
    Prepared, Storage, Volume,
};
use crate::{BrokerLog, Escalate, Escalation, LogIdentity};

// --- the device's annotations ------------------------------------------------------

/// Annotations the harness keeps beside each recorded device state (`sim_device.rs`):
/// what the product had told clients when the device stood there.
#[derive(Clone, Debug, Default)]
pub(crate) struct Meta {
    /// The identity the last completed open settled (`None` before any).
    told: Option<LogIdentity>,
    /// Records visible (acked, or recovered by the open) under `told`.
    acked: usize,
    /// Records below the durable head the PRODUCT claimed (`BrokerLog::durable_head`):
    /// P3 holds every image to them, which is what catches a full flush the product
    /// believes it issued and did not (NC7).
    claimed: usize,
    /// One past the newest record the harness's oracle calls ESCALATED among those
    /// acked (P3e).
    escalated: usize,
    /// An open is in progress: its recovery may move the identity legitimately.
    in_open: bool,
    /// The log was closed cleanly and nothing followed.
    closed: bool,
}

// --- workloads ----------------------------------------------------------------------

/// One record a workload writes: a publish, or (the batch's last, now and then) a pure
/// group commit, so the seal follows either last field — or a producer binding staged
/// ahead of a publish, the `PrincipalPrefix` rule's way in.
#[derive(Clone, Debug)]
enum Op {
    Publish {
        pid: u64,
        seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    Commit {
        group: String,
        upto: u64,
    },
    Bind {
        pid: u64,
        principal: String,
    },
}

/// How a batch is escalated, if it is: through which kind of rule of [`table`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Esc {
    No,
    /// Its last publish goes to a subject the `Subject` rule names.
    Subject,
    /// A `/a/bind` of a person's principal, then a publish by that producer.
    Principal,
    /// Its last record is a pure commit of a person's group.
    Group,
}

const ESCS: [Esc; 4] = [Esc::No, Esc::Subject, Esc::Principal, Esc::Group];

/// What follows a batch: nothing, the Ordered horizon's full flush (the writer keeps the
/// horizon for that tier only; elsewhere it is nothing), or `sync_full`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum After {
    Nothing,
    Horizon,
    SyncFull,
}

const AFTERS: [After; 3] = [After::Nothing, After::Horizon, After::SyncFull];

/// The escalation table every simulated log opens with (but NC3's).
fn table() -> Escalation {
    Escalation::new([
        Escalate::Subject("/e/>".into()),
        Escalate::PrincipalPrefix("h-".into()),
        Escalate::Group("/cur/p/>".into()),
    ])
}

/// The producer a person's principal is bound to in the workloads.
const PERSON_PID: u64 = 7;

/// The HARNESS'S OWN ORACLE for an escalated record, independent of the table the
/// product holds (so NC3, the product with an empty table, is caught): the subjects,
/// producer and groups the workloads escalate by. A person's producer only ever writes
/// after its binding.
fn oracle_escalated(r: &BrokerRecord) -> bool {
    let visible = !is_hidden_subject(&r.subject);
    (visible && (r.subject.starts_with("/e/") || r.producer_id == PERSON_PID))
        || r.commit
            .as_ref()
            .is_some_and(|c| c.group.starts_with("/cur/p/"))
}

#[derive(Clone, Debug)]
struct Workload {
    tier: Durability,
    block: usize,
    /// Start from the upgrade prefix: 2 unsealed v2 records and a FORMAT 1 sidecar.
    prefix: bool,
    batches: Vec<Vec<Op>>,
    /// What follows each batch (missing: nothing).
    after: Vec<After>,
    close: bool,
}

impl fmt::Display for Workload {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let shape: Vec<usize> = self.batches.iter().map(Vec::len).collect();
        write!(
            f,
            "{:?} block={} prefix={} batches={shape:?} after={:?} close={}",
            self.tier, self.block, self.prefix, self.after, self.close
        )
    }
}

/// Body sizes picked to straddle blocks: with a 2-byte subject an unsealed frame is 48
/// bytes plus its body (53 sealed), so these put record starts at every residue that
/// matters, the empty-frame one (12 mod 16, a header split after its fourth byte)
/// included.
const BODIES: [usize; 5] = [7, 12, 20, 33, 2];

struct Gen {
    next_seq: u64,
    phase: usize,
}

impl Gen {
    fn new(phase: usize) -> Gen {
        Gen { next_seq: 1, phase }
    }

    fn batch(&mut self, len: usize, with_commit: bool) -> Vec<Op> {
        self.batch_esc(len, with_commit, Esc::No)
    }

    /// A batch of `len` records escalated as `esc` says (a `Principal` batch stages its
    /// binding first, one record more).
    fn batch_esc(&mut self, len: usize, with_commit: bool, esc: Esc) -> Vec<Op> {
        let mut ops: Vec<Op> = (0..len)
            .map(|i| {
                let n = self.next_seq;
                self.next_seq += 1;
                let last = i + 1 == len;
                if esc == Esc::Group && last {
                    return Op::Commit {
                        group: "/cur/p/a".to_string(),
                        upto: n,
                    };
                }
                if with_commit && last && len > 1 {
                    return Op::Commit {
                        group: "g".to_string(),
                        upto: n,
                    };
                }
                let size = BODIES[(self.phase + n as usize) % BODIES.len()];
                // The batch's LAST PUBLISH: its last record, or the one before an ordinary
                // commit that ends it (put on the last record, the commit took its place
                // and the batch was not escalated at all).
                let last_publish = i + 1 + usize::from(with_commit && len > 1) == len;
                let subject = if esc == Esc::Subject && last_publish {
                    format!("/e/{}", (b'a' + (n % 5) as u8) as char)
                } else {
                    format!("/{}", (b'a' + (n % 5) as u8) as char)
                };
                Op::Publish {
                    pid: if esc == Esc::Principal && i == 0 {
                        PERSON_PID
                    } else {
                        1 + n % 3
                    },
                    seq: n,
                    subject,
                    body: (0..size).map(|j| (n as usize * 31 + j) as u8).collect(),
                }
            })
            .collect();
        if esc == Esc::Principal {
            ops.insert(
                0,
                Op::Bind {
                    pid: PERSON_PID,
                    principal: "h-person".to_string(),
                },
            );
        }
        ops
    }
}

/// The exhaustive set: every sequence of 1..=`max_batches` batches of 1..=3 records,
/// each tier, block size and body phase, with and without a clean close, on an empty
/// log and on the upgrade prefix.
///
/// Each batch's escalation (none, or by each of the three rules) and what follows it
/// (nothing, the horizon, `sync_full`) are picked by `w`, the workload's place among the
/// block × phase × close × prefix runs of its tier and shape, so that EVERY PAIR of
/// choices meets at EVERY pair of adjacent batches — the same kind twice, none then
/// some, some then none — without multiplying the set: batch `i` takes choice
/// `(w + i·⌊w/k⌋ + shape) mod k` of `k`, and across `w = 0..k²` the first of two
/// neighbours runs through every choice while their difference, `⌊w/k⌋`, does too. That
/// needs at least 16 runs per tier and shape (k = 4 escalations); the default and the
/// full sweeps have 36 (3 blocks × 3 phases × 2 × 2). Whole triples are not all built:
/// the seeded random workloads reach the rest by sample.
fn exhaustive(
    tiers: &[Durability],
    blocks: &[usize],
    phases: usize,
    max_batches: usize,
) -> Vec<Workload> {
    fn shapes(max: usize) -> Vec<Vec<usize>> {
        let mut out = vec![Vec::new()];
        let mut all = Vec::new();
        for _ in 0..max {
            out = out
                .into_iter()
                .flat_map(|s| {
                    (1..=3).map(move |n| {
                        let mut t = s.clone();
                        t.push(n);
                        t
                    })
                })
                .collect();
            all.extend(out.iter().cloned());
        }
        all
    }
    /// Choice `(w + i·⌊w/k⌋ + s) mod k` for batch `i` (see above).
    fn pick(w: usize, i: usize, s: usize, k: usize) -> usize {
        (w + i * (w / k) + s) % k
    }
    let mut out = Vec::new();
    for &tier in tiers {
        for (b, &block) in blocks.iter().enumerate() {
            for phase in 0..phases {
                for (s, shape) in shapes(max_batches).into_iter().enumerate() {
                    for close in [false, true] {
                        for prefix in [false, true] {
                            let w = ((b * phases + phase) * 2 + usize::from(close)) * 2
                                + usize::from(prefix);
                            let mut g = Gen::new(phase + usize::from(prefix));
                            let batches = shape
                                .iter()
                                .enumerate()
                                .map(|(i, &n)| {
                                    let esc = ESCS[pick(w, i, s, ESCS.len())];
                                    g.batch_esc(n, (i + phase) % 2 == 1, esc)
                                })
                                .collect();
                            let after = (0..shape.len())
                                .map(|i| AFTERS[pick(w, i, s, AFTERS.len())])
                                .collect();
                            out.push(Workload {
                                tier,
                                block,
                                prefix,
                                batches,
                                after,
                                close,
                            });
                        }
                    }
                }
            }
        }
    }
    out
}

/// A seeded random workload: 4..=8 batches of 1..=4 records, each escalated or not and
/// followed by a flush or not, at random.
fn random_workload(rng: &mut Rng, tier: Durability) -> Workload {
    let mut g = Gen::new(rng.below(5) as usize);
    let count = 4 + rng.below(5);
    let batches = (0..count)
        .map(|_| {
            let n = 1 + rng.below(4) as usize;
            let esc = ESCS[rng.below(ESCS.len() as u64) as usize];
            g.batch_esc(n, rng.below(3) == 0, esc)
        })
        .collect();
    let after = (0..count)
        .map(|_| AFTERS[rng.below(AFTERS.len() as u64) as usize])
        .collect();
    Workload {
        tier,
        block: if rng.below(2) == 0 { 16 } else { 64 },
        prefix: rng.below(4) == 0,
        batches,
        after,
        close: rng.below(3) == 0,
    }
}

// --- running the real code ----------------------------------------------------------

/// Two boots: the one a run serves in, and the one a power loss leaves.
const BOOT_A: [u8; 16] = [0xA1; 16];
const BOOT_B: [u8; 16] = [0xB2; 16];

/// The knobs a negative control turns.
#[derive(Clone, Copy, Default)]
struct Controls {
    mutation: Mutation,
    unsealed_writer: bool,
    /// NC4: recover power-loss images as the same boot.
    power_loss_same_boot: bool,
    /// NC10: readers re-base at the head after a covered move.
    rebase_at_head: bool,
    /// NC1: the plain-fsync device, which ignores barriers.
    ignore_barriers: bool,
    /// NC3: the log opens with an EMPTY escalation table, while the harness's oracle
    /// still expects the escalated records durable once acked.
    no_escalation: bool,
    /// NC7: the horizon's full flush issued as a barrier, the product told it was full.
    horizon_as_barrier: bool,
    /// The at-rest key every open takes (`None`: plaintext), for the keyed arm.
    key: Option<[u8; 32]>,
}

/// What clients were shown under one identity: the records, in offset order.
#[derive(Clone, Debug)]
struct Generation {
    identity: LogIdentity,
    records: Vec<BrokerRecord>,
    /// Batch boundaries (record counts) within `records`, for reader cursors.
    cuts: Vec<usize>,
    /// How many of `records` a reader can have seen: all of them for a generation that
    /// ended before the crash in question; for the generation being served at the
    /// crash, the device's `acked` then (see `check`).
    visible: usize,
}

/// One traced run of the real code: the device states it passed through, the records
/// it wrote (in offset order, the recovered ones first), and batch boundaries.
struct Run {
    trace: Vec<Device>,
    written: Vec<BrokerRecord>,
    boundaries: Vec<usize>,
    /// The generation clients saw by the run's end, `None` if the open failed.
    seen: Option<Generation>,
    /// The open's error, when it refused.
    refused: Option<String>,
    /// The lineage the open settled.
    lineage: Lineage,
    /// Commits whose visible head was HELD below the log's head, a full flush owed
    /// before the rest could be acked (an escalated record, or a resend of one).
    held: usize,
}

fn opts(tier: Durability, boot: [u8; 16], c: &Controls) -> OpenOptions {
    let mut o = OpenOptions::new(tier);
    o.boot = Boot::Known(boot);
    o.volume = Volume::Boot;
    o.mutation = c.mutation;
    if !c.no_escalation {
        o.escalation = table();
    }
    o
}

/// THE OPEN AN EMBEDDER'S TEST TAKES ([`BrokerLog::open_sim`] on a [`SimDevice`]), the one every
/// recovery the sweeps check goes through: the inputs it never takes are [`open_as`]'s.
fn open(sim: &Sim, tier: Durability, boot: [u8; 16], c: &Controls) -> std::io::Result<BrokerLog> {
    #[cfg_attr(
        not(feature = "at-rest"),
        expect(unused_mut, reason = "the key is the at-rest arm's")
    )]
    let mut o = opts(tier, boot, c);
    #[cfg(feature = "at-rest")]
    {
        o.at_rest_key = c.key;
    }
    let mut log = BrokerLog::open_sim(&SimDevice::on(sim.clone()), o)?;
    log.unsealed_writer = c.unsealed_writer;
    Ok(log)
}

/// The open the harness takes as a `repair`, or with the embedder's `prepared` unclean
/// verdict: [`open`] with what [`BrokerLog::open_sim`] does not take.
fn open_as(
    sim: &Sim,
    tier: Durability,
    boot: [u8; 16],
    c: &Controls,
    repair: bool,
    prepared: Option<&str>,
) -> std::io::Result<BrokerLog> {
    let (mut log, _) = BrokerLog::open_core(
        Storage::Sim(sim.clone()),
        &opts(tier, boot, c),
        repair,
        c.key,
        AntiRollbackMode::Off,
        || Ok(prepared.map_or(Prepared::Nothing, |why| Prepared::Unclean(why.to_string()))),
    )?;
    log.unsealed_writer = c.unsealed_writer;
    Ok(log)
}

fn stage(log: &mut BrokerLog, op: &Op) {
    match op {
        Op::Publish {
            pid,
            seq,
            subject,
            body,
        } => {
            log.stage_publish(*pid, *seq, subject.clone(), body.clone())
                .unwrap_or_else(|e| panic!("staging {op:?}: {e:?}"));
        }
        Op::Commit { group, upto } => {
            log.stage_commit(group.clone(), *upto)
                .unwrap_or_else(|e| panic!("staging {op:?}: {e:?}"));
        }
        Op::Bind { pid, principal } => {
            log.stage_bind(*pid, principal.clone())
                .unwrap_or_else(|e| panic!("staging {op:?}: {e:?}"));
        }
    }
}

/// Every record the log holds, in offset order.
fn records_of(log: &BrokerLog) -> Vec<BrokerRecord> {
    log.read_from(Offset::ZERO)
        .iter()
        .map(|r| (**r).clone())
        .collect()
}

/// Mark the instant after the product told clients something: `acked` records are
/// acked (visible), and the durable head it claims is read off the log; the oracle's
/// newest escalated record among the acked rises with them.
fn tell(sim: &Sim, log: &BrokerLog, written: &[BrokerRecord], acked: usize) {
    let mut m = sim.meta();
    m.acked = acked;
    m.claimed = usize::try_from(log.durable_head().0).unwrap_or(usize::MAX);
    m.escalated = written[..acked]
        .iter()
        .rposition(oracle_escalated)
        .map_or(m.escalated, |i| m.escalated.max(i + 1));
    sim.set_meta(m);
    sim.mark();
}

/// A full flush through `target`, as the writer issues it outside the log lock: through
/// a flush handle, then reported to the log — or, `barrier_instead` (NC7's horizon), a
/// barrier issued where the full flush belongs and reported as one.
fn full_flush(log: &mut BrokerLog, target: u64, barrier_instead: bool) {
    let handle = log.flush_handle();
    if barrier_instead {
        handle.barrier_instead();
    } else {
        handle.full().expect("a simulated full flush succeeds");
    }
    log.full_flush_done(target);
}

/// Run `batches` (each followed by what `after` says; and maybe a clean close) against
/// `sim` from an open in `boot`, tracing every device state and marking each ack where
/// the product would send it: the records below the commit's visible head at once, the
/// rest once the full flush it owes is done (the broker writer's held head, step by
/// step).
fn run(
    sim: &Sim,
    tier: Durability,
    boot: [u8; 16],
    batches: &[Vec<Op>],
    after: &[After],
    close: bool,
    c: &Controls,
) -> Run {
    let before = sim.meta();
    sim.set_meta(Meta {
        in_open: true,
        closed: false,
        ..before
    });
    sim.trace_on();
    let mut log = match open(sim, tier, boot, c) {
        Ok(log) => log,
        Err(e) => {
            return Run {
                trace: sim.take_trace(),
                written: Vec::new(),
                boundaries: Vec::new(),
                seen: None,
                refused: Some(e.to_string()),
                lineage: Lineage::default(),
                held: 0,
            }
        }
    };
    let mut written = records_of(&log);
    let mut boundaries = vec![written.len()];
    let identity = log.identity();
    let lineage = log.lineage().clone();
    // Everything the open recovered is durable (its own flush): what P3 holds the next
    // crash to, through `claimed`.
    sim.set_meta(Meta {
        told: Some(identity),
        acked: written.len(),
        claimed: written.len(),
        escalated: 0,
        in_open: false,
        closed: false,
    });
    sim.mark();
    let mut held = 0usize;
    for (i, batch) in batches.iter().enumerate() {
        for op in batch {
            stage(&mut log, op);
        }
        let committed = log.commit_batch().expect("a simulated batch commits");
        written = records_of(&log);
        boundaries.push(written.len());
        // Step 3 of the held head: what the product acks now, by the predicate the
        // broker's writer answers each op by (`Committed::acks_now`), not a copy of it.
        // The run's records are never resends, so each is asked as an original. (Whether
        // the writer itself sends nothing more before the flush is the broker's own test,
        // `broker::tests::held_head`, which holds the flush at a pause seam.)
        let acked_now = (0..written.len())
            .take_while(|&o| committed.acks_now(o as u64, false))
            .count();
        tell(sim, &log, &written, acked_now);
        // Steps 4 and 5: the owed full flush, then the rest.
        if let Some(target) = committed.owe_full {
            held += usize::from(committed.visible_now < target);
            full_flush(&mut log, target.0, false);
            tell(sim, &log, &written, written.len());
        }
        let head = log.head().0;
        match after.get(i).copied().unwrap_or(After::Nothing) {
            After::Horizon if matches!(tier, Durability::Ordered { .. }) => {
                if log.full_flush_owed(head) {
                    full_flush(&mut log, head, c.horizon_as_barrier);
                    tell(sim, &log, &written, written.len());
                }
            }
            After::SyncFull => {
                log.sync_full().expect("a simulated sync_full succeeds");
                tell(sim, &log, &written, written.len());
            }
            After::Horizon | After::Nothing => {}
        }
    }
    if close {
        log.close_clean().expect("a simulated log closes cleanly");
        let mut m = sim.meta();
        m.closed = true;
        m.claimed = written.len();
        sim.set_meta(m);
        sim.mark();
    }
    drop(log);
    Run {
        trace: sim.take_trace(),
        seen: Some(Generation {
            identity,
            visible: written.len(),
            records: written.clone(),
            cuts: boundaries.clone(),
        }),
        written,
        boundaries,
        refused: None,
        lineage,
        held,
    }
}

// --- the properties -----------------------------------------------------------------

#[derive(Clone, Debug)]
struct Violation {
    property: &'static str,
    detail: String,
}

/// What one recovery is checked against.
struct Expect<'a> {
    /// The device state crashed at.
    at: &'a Device,
    power_loss: bool,
    written: &'a [BrokerRecord],
    boundaries: &'a [usize],
    /// For a crash inside an open: what the run before it wrote, and its boundaries (P2
    /// accepts a prefix of either history; see `check`).
    before: Option<(&'a [BrokerRecord], &'a [usize])>,
    tier: Durability,
    /// Every generation clients saw before the crash, oldest first.
    readers: &'a [Generation],
}

/// Records a full flush covered in `dev` (P3): the complete frames below `flushed`.
fn covered(dev: &Device) -> usize {
    let mut pos = 0usize;
    let mut n = 0usize;
    let bytes = &dev.durable[..dev.flushed.min(dev.durable.len())];
    while let Some(h) = bytes.get(pos..pos + HEADER_SIZE) {
        let len = u32::from_le_bytes([h[4], h[5], h[6], h[7]]) as usize;
        let end = pos + HEADER_SIZE + len;
        if end > bytes.len() {
            break;
        }
        n += 1;
        pos = end;
    }
    n
}

/// Whether `dev`'s sidecar records a durable floor (FORMAT 2).
fn floor_known(dev: &Device) -> bool {
    let sim = Sim::with(dev.clone());
    matches!(logid::read(&Dir::Sim(sim)), Ok(p @ Prior::Recorded(_)) if p.floor(0).is_some())
}

/// A recovery's outcome: the records, identity and lineage, or the refusal.
type Outcome = Result<(Vec<BrokerRecord>, LogIdentity, Lineage), String>;

fn check(e: &Expect<'_>, outcome: &Outcome, c: &Controls) -> Vec<Violation> {
    let mut v = Vec::new();
    let mut bad = |property, detail: String| v.push(Violation { property, detail });
    let (recovered, identity, lineage) = match outcome {
        Err(why) => {
            if floor_known(e.at) {
                bad("P1", format!("refused with a known floor: {why}"));
            }
            return v;
        }
        Ok(x) => x,
    };
    let k = recovered.len();
    // The history the records must come from: what this run wrote — or, for a crash
    // INSIDE an open, what the run before it wrote too: until that open's own cut is
    // durable, a power loss can bring back records it cut (a dead writer's unfinished
    // batch, never acked), which a later open in another boot is right to keep.
    let histories = std::iter::once((e.written, e.boundaries)).chain(e.before);
    let prefix_of = |(w, _): &(&[BrokerRecord], &[usize])| k <= w.len() && recovered[..] == w[..k];
    if !histories.clone().any(|h| prefix_of(&h)) {
        bad(
            "P2",
            format!("recovered {k} records that are not the first {k} written"),
        );
    }
    let at_boundary = |(w, b): &(&[BrokerRecord], &[usize])| {
        prefix_of(&(w, b)) && (b.contains(&k) || k < b.first().copied().unwrap_or(0))
    };
    if e.tier != Durability::Relaxed && !histories.clone().any(|h| at_boundary(&h)) {
        bad(
            "P2",
            format!(
                "{:?} recovered {k} records, not at a batch boundary {:?}",
                e.tier, e.boundaries
            ),
        );
    }
    let m = &e.at.meta;
    let flushed = covered(e.at);
    if k < flushed {
        bad(
            "P3",
            format!("{k} records recovered, but a full flush covered {flushed}"),
        );
    }
    if k < m.claimed {
        bad(
            "P3",
            format!(
                "{k} records recovered, but the product claimed {} durable",
                m.claimed
            ),
        );
    }
    if k < m.escalated {
        bad(
            "P3e",
            format!(
                "{k} records recovered, but an escalated record acked at offset {} is gone",
                m.escalated - 1
            ),
        );
    }
    // A log that has never held a record takes a fresh id at every open (no client
    // can hold an offset into it), so "moved" is asked only of a log with records.
    if let Some(told) = m.told.filter(|_| m.acked > 0) {
        if k < m.acked && *identity == told {
            bad(
                "P4",
                format!(
                    "{} acked records lost under the unchanged identity {told}",
                    m.acked - k
                ),
            );
        }
        if m.closed && e.power_loss && (k != m.acked || *identity != told) {
            bad(
                "P5",
                format!(
                    "after a clean close: {k} of {} records, identity {identity} (was {told})",
                    m.acked
                ),
            );
        }
        if !e.power_loss && !m.in_open && (k < m.acked || *identity != told) {
            bad(
                "P6",
                format!(
                    "same-boot crash: {k} of {} acked records, identity {identity} (was {told})",
                    m.acked
                ),
            );
        }
    }
    for (n, g) in e.readers.iter().enumerate() {
        // A reader saw at most what was visible: the generation served at the crash
        // (the last) only up to what was acked then. (Identities cannot tell the
        // generations apart: a run that moved nothing serves under its predecessor's.)
        let visible = if n + 1 == e.readers.len() {
            // Inside its open the run has served nothing yet.
            if m.in_open {
                0
            } else {
                m.acked
            }
        } else {
            g.visible
        }
        .min(g.records.len());
        let mut cursors: Vec<usize> = g.cuts.iter().copied().filter(|&c| c <= visible).collect();
        cursors.push(0);
        cursors.push(visible);
        for &cursor in &cursors {
            let resume = if c.rebase_at_head && *identity != g.identity {
                identity.continues(g.identity, lineage).map(|_| k)
            } else {
                identity
                    .continues(g.identity, lineage)
                    .map(|r| usize::try_from(r).unwrap_or(usize::MAX).min(cursor))
            };
            let Some(s) = resume else { continue };
            if s > cursor {
                bad("P7", format!("a reader at {cursor} under {} resumes at {s}: it skips records it never saw", g.identity));
            } else if s > k || recovered[..s] != g.records[..s] {
                bad("P7", format!("a reader at {cursor} under {} resumes at {s}, but the records below differ from what it saw", g.identity));
            }
        }
    }
    v
}

/// Recover an image the way the next open does; the records, identity and lineage, or
/// the refusal.
fn recover(sim: &Sim, tier: Durability, boot: [u8; 16], c: &Controls) -> Outcome {
    let log = open(sim, tier, boot, c).map_err(|e| e.to_string())?;
    let recs = log
        .read_from(Offset::ZERO)
        .iter()
        .map(|r| (**r).clone())
        .collect();
    Ok((recs, log.identity(), log.lineage().clone()))
}

/// Tallies and the first violations of each property.
#[derive(Default)]
struct Report {
    recoveries: usize,
    refusals: usize,
    /// Recoveries that lost acked records (every one must have moved the identity).
    lost: usize,
    /// Of `lost`, those of an Ordered run.
    lost_ordered: usize,
    /// Recoveries that moved the identity, and those of them that recorded lineage.
    moved: usize,
    with_lineage: usize,
    /// Crash points whose power-loss images were EVERY subset of the volatile blocks,
    /// and those that took a sample (see [`images`]).
    points_every: usize,
    points_sampled: usize,
    /// Process-crash images that were short writes of an append (of `recoveries`).
    short_writes: usize,
    /// Commits that held the visible head for a full flush owed (escalations).
    held: usize,
    counts: std::collections::BTreeMap<&'static str, usize>,
    examples: Vec<String>,
}

impl Report {
    fn add(&mut self, what: &str, v: Vec<Violation>) {
        for x in v {
            let n = self.counts.entry(x.property).or_insert(0);
            *n += 1;
            if *n <= 3 {
                self.examples
                    .push(format!("{} {}: {what}", x.property, x.detail));
            }
        }
    }

    /// Count what one recovery did, so a sweep that exercised nothing cannot pass.
    fn tally(&mut self, e: &Expect<'_>, outcome: &Outcome) {
        self.recoveries += 1;
        let Ok((recs, identity, lineage)) = outcome else {
            self.refusals += 1;
            return;
        };
        let m = &e.at.meta;
        if recs.len() < m.acked {
            self.lost += 1;
            self.lost_ordered += usize::from(matches!(e.tier, Durability::Ordered { .. }));
        }
        if m.told.is_some_and(|t| t != *identity) && m.acked > 0 {
            self.moved += 1;
            self.with_lineage += usize::from(
                lineage
                    .steps()
                    .last()
                    .is_some_and(|s| s.0 == identity.generation),
            );
        }
    }

    /// Add a [`sweep_part`]'s report to this one: every tally summed, and its examples
    /// kept while this report holds fewer than three of that property's.
    fn absorb(&mut self, other: Report) {
        let Report {
            recoveries,
            refusals,
            lost,
            lost_ordered,
            moved,
            with_lineage,
            points_every,
            points_sampled,
            short_writes,
            held,
            counts,
            examples,
        } = other;
        self.recoveries += recoveries;
        self.refusals += refusals;
        self.lost += lost;
        self.lost_ordered += lost_ordered;
        self.moved += moved;
        self.with_lineage += with_lineage;
        self.points_every += points_every;
        self.points_sampled += points_sampled;
        self.short_writes += short_writes;
        self.held += held;
        for (property, n) in counts {
            *self.counts.entry(property).or_insert(0) += n;
        }
        let property = |e: &str| e.split(' ').next().unwrap_or_default().to_string();
        for e in examples {
            let p = property(&e);
            if self.examples.iter().filter(|x| property(x) == p).count() < 3 {
                self.examples.push(e);
            }
        }
    }

    fn count_points(&mut self, every: bool) {
        if every {
            self.points_every += 1;
        } else {
            self.points_sampled += 1;
        }
    }

    fn violated(&self, property: &str) -> usize {
        self.counts.get(property).copied().unwrap_or(0)
    }

    fn clean(&self) -> bool {
        self.counts.is_empty()
    }
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "{} recoveries ({} of them short writes), {} refused, {} lost acked records ({} of \
             them Ordered), {} \
             moved the identity ({} with lineage), {} commits held the head for a full flush; \
             power-loss images: every subset at {} crash points, a sample at {}; violations {:?}",
            self.recoveries,
            self.short_writes,
            self.refusals,
            self.lost,
            self.lost_ordered,
            self.moved,
            self.with_lineage,
            self.held,
            self.points_every,
            self.points_sampled,
            self.counts
        )?;
        for e in &self.examples {
            writeln!(f, "  {e}")?;
        }
        Ok(())
    }
}

/// The device a workload starts from: empty, or the upgrade prefix.
fn start(w: &Workload, c: &Controls) -> (Sim, Vec<Generation>) {
    let mut dev = Device::new(w.block);
    dev.ignore_barriers = c.ignore_barriers;
    let mut readers = Vec::new();
    if w.prefix {
        let recs: Vec<BrokerRecord> = (0..2)
            .map(|i| BrokerRecord {
                seq: Offset(i),
                producer_id: 9,
                producer_seq: i + 1,
                subject: "/p".to_string(),
                body: vec![0x50 + i as u8; 5 + 3 * i as usize],
                commit: None,
            })
            .collect();
        for r in &recs {
            // Keyed, the older build sealed it too (the v1 AAD the simulated log reads: its
            // offset, little-endian).
            let framed = match c.key {
                #[cfg(feature = "at-rest")]
                Some(key) => {
                    let payload = r.encode_payload().expect("a prefix record encodes");
                    let sealed = astream_aead::seal(&key, &r.seq.0.to_le_bytes(), &payload);
                    astream_wire::Frame::new(sealed)
                        .encode()
                        .expect("it frames")
                }
                _ => r.encode().expect("a prefix record encodes"),
            };
            dev.logical.extend_from_slice(&framed);
        }
        let identity = LogIdentity {
            id: [0x77; 16],
            generation: 0,
        };
        dev.id = Some(logid::format1_for_test(identity, 0, 2, &dev.logical));
        dev.durable = dev.logical.clone();
        dev.flushed = dev.logical.len();
        dev.exists = true;
        dev.meta = Meta {
            told: Some(identity),
            acked: 2,
            claimed: 2,
            escalated: 0,
            in_open: false,
            closed: false,
        };
        readers.push(Generation {
            identity,
            records: recs,
            cuts: vec![0, 2],
            visible: 2,
        });
    }
    (Sim::with(dev), readers)
}

/// The sweep: run each workload, crash at every recorded state (power loss: up to
/// `budget` images; process crash: the state itself), recover, check; and for one in
/// `second_every` recoveries, write two more batches on the recovered log and crash
/// THAT run at every state too, checking across both crashes.
///
/// The workloads are dealt round-robin to [`PARTS`] threads, each a [`sweep_part`] of
/// its own share in order under its own fixed seed, and the reports summed: every
/// workload is still crashed at every state and every power-loss subset is still
/// taken wherever the budget allows. Only the images a crash point beyond the budget
/// samples, and which recoveries are crashed a second time, come from the part's
/// seed rather than from one seed threaded through every workload.
fn sweep(
    workloads: &[Workload],
    budget: usize,
    second_every: usize,
    c: &Controls,
    seed: u64,
) -> Report {
    std::thread::scope(|s| {
        let parts: Vec<_> = (0..PARTS)
            .map(|p| {
                let mine: Vec<&Workload> = workloads.iter().skip(p).step_by(PARTS).collect();
                let seed = seed ^ (p as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
                s.spawn(move || sweep_part(&mine, budget, second_every, c, seed))
            })
            .collect();
        let mut report = Report::default();
        for part in parts {
            report.absorb(
                part.join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic)),
            );
        }
        report
    })
}

/// How many threads a [`sweep`] deals its workloads to. Fixed, never the machine's
/// core count, so what a sweep samples does not depend on where it runs.
const PARTS: usize = 8;

/// One part of a [`sweep`]: its workloads in order, one seed threaded through them.
fn sweep_part(
    workloads: &[&Workload],
    budget: usize,
    second_every: usize,
    c: &Controls,
    seed: u64,
) -> Report {
    let mut rng = Rng(seed | 1);
    let mut report = Report::default();
    let mut tick = 0usize;
    for w in workloads {
        let (sim, mut readers) = start(w, c);
        let first = run(&sim, w.tier, BOOT_A, &w.batches, &w.after, w.close, c);
        assert!(
            first.refused.is_none(),
            "{w}: the first open refused: {:?}",
            first.refused
        );
        if let Some(g) = &first.seen {
            readers.push(g.clone());
        }
        report.held += first.held;
        for (i, dev) in first.trace.iter().enumerate() {
            let (losses, every) = images(dev, budget, &mut rng);
            report.count_points(every);
            let mut crashes: Vec<(Device, bool)> = losses.into_iter().map(|d| (d, true)).collect();
            crashes.push((dev.clone(), false));
            // A process killed mid-append leaves a short write: the same boot, no ack.
            let shorts = dev.short_writes();
            report.short_writes += shorts.len();
            crashes.extend(shorts.into_iter().map(|d| (d, false)));
            for (img, power_loss) in crashes {
                let boot = if power_loss && !c.power_loss_same_boot {
                    BOOT_B
                } else {
                    BOOT_A
                };
                let expect = Expect {
                    at: dev,
                    power_loss,
                    written: &first.written,
                    boundaries: &first.boundaries,
                    before: None,
                    tier: w.tier,
                    readers: &readers,
                };
                tick += 1;
                let second = tick.is_multiple_of(second_every.max(1));
                let rsim = Sim::with(img);
                if !second {
                    let outcome = recover(&rsim, w.tier, boot, c);
                    report.tally(&expect, &outcome);
                    report.add(
                        &format!("{w} state {i} power_loss={power_loss}"),
                        check(&expect, &outcome, c),
                    );
                    continue;
                }
                // The recovery IS the second run's open: traced, then two more batches.
                let mut g = Gen::new(i);
                g.next_seq = 1000;
                let more = vec![g.batch(2, false), g.batch(1, false)];
                let again = run(&rsim, w.tier, boot, &more, &[], false, c);
                let outcome = match &again.refused {
                    Some(why) => Err(why.clone()),
                    None => {
                        let s = again.seen.as_ref().expect("an open that did not refuse");
                        let k = again.boundaries[0];
                        Ok((s.records[..k].to_vec(), s.identity, again.lineage.clone()))
                    }
                };
                report.tally(&expect, &outcome);
                report.add(
                    &format!("{w} state {i} power_loss={power_loss}"),
                    check(&expect, &outcome, c),
                );
                report.held += again.held;
                let Some(seen2) = &again.seen else { continue };
                // The generations of the first run were seen up to what was acked at
                // the first crash.
                let last = readers.len().saturating_sub(1);
                let mut readers2: Vec<Generation> = readers
                    .iter()
                    .enumerate()
                    .map(|(n, g)| Generation {
                        visible: if n == last { dev.meta.acked } else { g.visible },
                        ..g.clone()
                    })
                    .collect();
                readers2.push(seen2.clone());
                for (j, dev2) in again.trace.iter().enumerate() {
                    let (losses2, every2) = images(dev2, budget / 4, &mut rng);
                    report.count_points(every2);
                    let mut crashes2: Vec<(Device, bool)> =
                        losses2.into_iter().map(|d| (d, true)).collect();
                    crashes2.push((dev2.clone(), false));
                    let shorts2 = dev2.short_writes();
                    report.short_writes += shorts2.len();
                    crashes2.extend(shorts2.into_iter().map(|d| (d, false)));
                    for (img2, power_loss2) in crashes2 {
                        let boot2 = if power_loss2 && !c.power_loss_same_boot {
                            [boot[0] ^ 0x0F; 16]
                        } else {
                            boot
                        };
                        let expect2 = Expect {
                            at: dev2,
                            power_loss: power_loss2,
                            written: &again.written,
                            boundaries: &again.boundaries,
                            before: dev2
                                .meta
                                .in_open
                                .then_some((&first.written[..], &first.boundaries[..])),
                            tier: w.tier,
                            readers: &readers2,
                        };
                        let outcome2 = recover(&Sim::with(img2), w.tier, boot2, c);
                        report.tally(&expect2, &outcome2);
                        report.add(
                            &format!(
                                "{w} state {i} then {j} power_loss={power_loss}/{power_loss2}"
                            ),
                            check(&expect2, &outcome2, c),
                        );
                    }
                }
            }
        }
    }
    report
}

// --- the rot arm --------------------------------------------------------------------

/// Flip every byte of a clean multi-batch log once and recover it as a power loss and
/// as a same-boot reopen, with the floor below the newest batch (no clean close) and
/// above it (after one). Checked for each: P2 (what is kept is the records written, a
/// prefix of them), P4 (acked records cut only with a move) and P8 (rot below the floor
/// or behind a later batch refused, rot in the newest batch refused or cut with a move —
/// a whole last record under a rotted LENGTH included, which reads as a write cut short
/// until its CRC is asked). Not P1 (rot is no crash image, and refusing it is the
/// point), P3, P5–P7 (a reader's view is P4's, after a move).
fn rot(tier: Durability, c: &Controls) -> Report {
    let mut report = Report::default();
    for close in [false, true] {
        let w = Workload {
            tier,
            block: 16,
            prefix: false,
            batches: {
                let mut g = Gen::new(1);
                vec![
                    g.batch(2, false),
                    g.batch(1, false),
                    g.batch(2, true),
                    g.batch(1, false),
                ]
            },
            after: Vec::new(),
            close,
        };
        let (sim, _) = start(&w, c);
        let r = run(&sim, tier, BOOT_A, &w.batches, &w.after, close, c);
        let clean = sim.device();
        let seen = r.seen.clone().expect("the clean run opened");
        // Byte ranges of the batches, and where the floor is (the open's head, or the
        // close's).
        let mut ends = Vec::new();
        let mut pos = 0usize;
        while let Some(h) = clean.logical.get(pos..pos + HEADER_SIZE) {
            let len = u32::from_le_bytes([h[4], h[5], h[6], h[7]]) as usize;
            pos += HEADER_SIZE + len;
            ends.push(pos);
        }
        let batch_of_record = |rec: usize| r.boundaries.iter().position(|&b| rec < b).unwrap_or(0);
        let newest = r.boundaries.len() - 1;
        let floor_records = if close { seen.records.len() } else { 0 };
        for at in 0..clean.logical.len() {
            let rec = ends.iter().position(|&e| at < e).unwrap_or(0);
            let batch = batch_of_record(rec);
            for power_loss in [true, false] {
                let mut dev = clean.clone();
                dev.logical[at] ^= 0x5A;
                dev.durable = dev.logical.clone();
                let boot = if power_loss && !c.power_loss_same_boot {
                    BOOT_B
                } else {
                    BOOT_A
                };
                let outcome = recover(&Sim::with(dev.clone()), tier, boot, c);
                report.recoveries += 1;
                report.refusals += usize::from(outcome.is_err());
                let what = format!("{tier:?} close={close} byte {at} (record {rec}, batch {batch}) power_loss={power_loss}");
                let mut v = Vec::new();
                let below_floor = rec < floor_records;
                let unclean_relaxed =
                    tier == Durability::Relaxed && power_loss && !close && !c.power_loss_same_boot;
                match &outcome {
                    Err(_) => {}
                    Ok((recs, identity, _)) => {
                        let lost = recs.len() < seen.records.len();
                        let moved = *identity != seen.identity;
                        if recs.len() > seen.records.len() || recs[..] != seen.records[..recs.len()]
                        {
                            v.push(Violation {
                                property: "P2",
                                detail: format!(
                                    "kept {} records that are not the first {} written",
                                    recs.len(),
                                    recs.len()
                                ),
                            });
                        }
                        if below_floor {
                            v.push(Violation {
                                property: "P8",
                                detail: "rot below the floor was cut, not refused".to_string(),
                            });
                        } else if batch != newest && !unclean_relaxed {
                            v.push(Violation {
                                property: "P8",
                                detail: format!(
                                    "rot in batch {batch}, not the newest, was cut, not refused"
                                ),
                            });
                        } else if lost && !moved {
                            v.push(Violation {
                                property: "P8",
                                detail: "rot in the newest batch was cut without a move"
                                    .to_string(),
                            });
                        }
                        if lost && !moved {
                            v.push(Violation {
                                property: "P4",
                                detail: format!(
                                    "{} acked records cut under an unchanged identity",
                                    seen.records.len() - recs.len()
                                ),
                            });
                        }
                    }
                }
                report.add(&what, v);
            }
        }
    }
    report
}

// --- an older build's records above the floor ---------------------------------------

/// The record frames a build that predates the batch marks writes: no mark at all.
fn unmarked_frames(records: &[BrokerRecord]) -> Vec<u8> {
    records
        .iter()
        .flat_map(|r| r.encode().expect("an unmarked record encodes"))
        .collect()
}

/// A sealing run, then a REVERT to a build that predates the batch marks and log
/// identity: its open recovers by the rules before the floor and flushes what it
/// keeps, then it appends unmarked records — a batch of one, then one of three, each
/// flushed before its ack when it serves Strict — and it never touches `<log>.id`, so
/// the floor the sealing run recorded still stands. Then this build opens the log again,
/// after a power loss at any point of the older build's run (every subset of its
/// unflushed blocks, as [`images`] takes them), a process crash, or a short write.
///
/// Checked, on every image: P2 (what is kept is the records written, a prefix of them);
/// P3 (every record a full flush covered is present, the older build's own included —
/// the property cutting its records as a torn batch broke); P4 when the older build
/// served Strict (an acked record lost only with a move; an older RELAXED build's power
/// loss is the one no build can announce, since it recorded nothing); and that this
/// build refuses no image the rules before the floor — the older build's own — recover.
fn older_build_appends(c: &Controls) -> Report {
    let mut report = Report::default();
    let mut rng = Rng(0x01DB_111D);
    for tier in TIERS {
        for old_strict in [true, false] {
            for close in [false, true] {
                let mut g = Gen::new(2);
                let sealed = vec![g.batch(2, false), g.batch(1, false)];
                let w = Workload {
                    tier,
                    block: 16,
                    prefix: false,
                    batches: sealed.clone(),
                    after: Vec::new(),
                    close,
                };
                let (sim, _) = start(&w, c);
                let first = run(&sim, tier, BOOT_A, &sealed, &[], close, c);
                let mut written = first.written.clone();
                // The older build's open: it recovers (nothing to cut) and flushes.
                sim.trace_on();
                sim.full_flush();
                for len in [1usize, 3] {
                    let base = written.len();
                    let batch: Vec<BrokerRecord> = (0..len)
                        .map(|i| {
                            let n = (base + i) as u64;
                            BrokerRecord {
                                seq: Offset(n),
                                producer_id: 40,
                                producer_seq: n + 1,
                                subject: "/old".to_string(),
                                body: vec![0x60 + i as u8; 9 + 7 * i],
                                commit: None,
                            }
                        })
                        .collect();
                    written.extend(batch.iter().cloned());
                    sim.write_at(sim.log_len() as u64, &unmarked_frames(&batch));
                    if old_strict {
                        sim.full_flush();
                    }
                    let mut m = sim.meta();
                    m.acked = written.len();
                    m.closed = false;
                    sim.set_meta(m);
                    sim.mark();
                }
                for dev in sim.take_trace() {
                    let (losses, every) = images(&dev, 64, &mut rng);
                    report.count_points(every);
                    let mut crashes: Vec<(Device, bool)> =
                        losses.into_iter().map(|d| (d, true)).collect();
                    crashes.push((dev.clone(), false));
                    let shorts = dev.short_writes();
                    report.short_writes += shorts.len();
                    crashes.extend(shorts.into_iter().map(|d| (d, false)));
                    for (img, power_loss) in crashes {
                        let boot = if power_loss { BOOT_B } else { BOOT_A };
                        let legacy = Controls {
                            mutation: Mutation::IgnoreFloor,
                            ..*c
                        };
                        let before_floor = recover(&Sim::with(img.clone()), tier, boot, &legacy);
                        let outcome = recover(&Sim::with(img), tier, boot, c);
                        let expect = Expect {
                            at: &dev,
                            power_loss,
                            written: &written,
                            boundaries: &[],
                            before: None,
                            tier,
                            readers: &[],
                        };
                        report.tally(&expect, &outcome);
                        let what = format!(
                            "{tier:?} close={close} older build strict={old_strict} \
                             power_loss={power_loss}"
                        );
                        let mut v = Vec::new();
                        match &outcome {
                            Err(why) => {
                                if before_floor.is_ok() {
                                    v.push(Violation {
                                        property: "P1",
                                        detail: format!(
                                            "an older build's records refused where the rules \
                                             before the floor recover them: {why}"
                                        ),
                                    });
                                }
                            }
                            Ok((recs, identity, _)) => {
                                let k = recs.len();
                                if k > written.len() || recs[..] != written[..k] {
                                    v.push(Violation {
                                        property: "P2",
                                        detail: format!(
                                            "kept {k} records that are not the first {k} written"
                                        ),
                                    });
                                }
                                let flushed = covered(&dev);
                                if k < flushed {
                                    v.push(Violation {
                                        property: "P3",
                                        detail: format!(
                                            "{k} records recovered, but a full flush covered \
                                             {flushed}"
                                        ),
                                    });
                                }
                                let m = &dev.meta;
                                if old_strict && k < m.acked && m.told == Some(*identity) {
                                    v.push(Violation {
                                        property: "P4",
                                        detail: format!(
                                            "{} acked records lost under the unchanged identity",
                                            m.acked - k
                                        ),
                                    });
                                }
                            }
                        }
                        report.add(&what, v);
                    }
                }
            }
        }
    }
    report
}

// --- frames inside record bodies ----------------------------------------------------

/// Workloads whose every record's BODY holds a whole record frame: one with offset 0
/// (a forwarded frame of another log's first record — below every offset the torn
/// batch can hold) or one with an offset far past any it can reach. A torn write that
/// takes a carrying record's header lets the resync meet the inner frame; it is at no
/// record's place, so the sweep's P1 holds — no torn batch is refused for it.
fn planted_frame_workloads() -> Vec<Workload> {
    let inner = |seq: u64| {
        BrokerRecord {
            seq: Offset(seq),
            producer_id: 9,
            producer_seq: 1,
            subject: "/fwd".to_string(),
            body: b"inner".to_vec(),
            commit: None,
        }
        .encode()
        .expect("an inner record encodes")
    };
    let op = |n: u64| Op::Publish {
        pid: 1,
        seq: n,
        subject: "/p".to_string(),
        body: [
            &b"payload:"[..],
            &inner(if n % 2 == 1 { 0 } else { 1 << 40 }),
        ]
        .concat(),
    };
    let mut out = Vec::new();
    for tier in TIERS {
        for block in [16, 64] {
            for shape in [&[1usize][..], &[2], &[3], &[1, 2], &[2, 1], &[1, 3]] {
                let mut n = 0u64;
                let batches = shape
                    .iter()
                    .map(|&len| {
                        (0..len)
                            .map(|_| {
                                n += 1;
                                op(n)
                            })
                            .collect()
                    })
                    .collect();
                out.push(Workload {
                    tier,
                    block,
                    prefix: false,
                    batches,
                    after: Vec::new(),
                    close: false,
                });
            }
        }
    }
    out
}

// --- NC9: a restored copy under the current sidecar -----------------------------------

/// A log that took a covered move and regrew different records at the reused offsets,
/// then has an older copy of itself restored under its current sidecar. Correct: the
/// shorter log moves the generation with NO lineage, and a reader forgets. The
/// mutation records lineage anyway, and a reader resumes into records it never saw.
fn restored_copy(c: &Controls) -> Report {
    let mut report = Report::default();
    let w = Workload {
        tier: Durability::Relaxed,
        block: 16,
        prefix: false,
        batches: Vec::new(),
        after: Vec::new(),
        close: false,
    };
    let (sim, _) = start(&w, c);
    let mut g = Gen::new(0);
    let first = run(
        &sim,
        Durability::Relaxed,
        BOOT_A,
        &[g.batch(2, false), g.batch(1, false), g.batch(1, false)],
        &[],
        false,
        c,
    );
    let gen0 = first.seen.expect("opened");
    // The backup: the first three records.
    let backup = {
        let d = sim.device();
        let mut pos = 0usize;
        for _ in 0..3 {
            let h = &d.logical[pos..pos + HEADER_SIZE];
            pos += HEADER_SIZE + u32::from_le_bytes([h[4], h[5], h[6], h[7]]) as usize;
        }
        d.logical[..pos].to_vec()
    };
    // A power loss that keeps only the first batch: recovered in another boot, the
    // generation moves with lineage at offset 2.
    let lost = {
        let d = sim.device();
        let h0 = &d.logical[..HEADER_SIZE];
        let first = HEADER_SIZE + u32::from_le_bytes([h0[4], h0[5], h0[6], h0[7]]) as usize;
        let h1 = &d.logical[first..first + HEADER_SIZE];
        let end = first + HEADER_SIZE + u32::from_le_bytes([h1[4], h1[5], h1[6], h1[7]]) as usize;
        let keep: BTreeSet<usize> = (0..end.div_ceil(d.block)).collect();
        d.image(0, &keep, true, 0)
    };
    let rsim = Sim::with(lost);
    let mut g2 = Gen::new(3);
    g2.next_seq = 500;
    let regrown = run(
        &rsim,
        Durability::Relaxed,
        BOOT_B,
        &[g2.batch(1, false), g2.batch(1, false)],
        &[],
        true,
        c,
    );
    let gen1 = regrown.seen.expect("recovered");
    assert_eq!(
        gen1.records[..2],
        gen0.records[..2],
        "the move kept the first batch"
    );
    // Restore the backup under the current (closed) sidecar.
    rsim.restore(&backup);
    let outcome = recover(&rsim, Durability::Relaxed, BOOT_B, c);
    report.recoveries += 1;
    let at = rsim.device();
    let expect = Expect {
        at: &at,
        power_loss: false,
        written: &[],
        boundaries: &[],
        before: None,
        tier: Durability::Relaxed,
        readers: &[gen1],
    };
    // Only P7 is asked of a restored copy: it is no crash image, so P2–P6 do not apply.
    let v = check(&expect, &outcome, c)
        .into_iter()
        .filter(|x| x.property == "P7")
        .collect();
    report.add("restored copy", v);
    report
}

// --- the tests ----------------------------------------------------------------------

/// The tiers every sweep runs. The simulated Ordered log has no horizon of its own (a
/// `BrokerLog` used directly never has one): the harness issues the horizon's full flush
/// where a workload says, as the writer would.
const TIERS: [Durability; 3] = [Durability::Strict, ORDERED, Durability::Relaxed];

/// The Ordered tier as the sweeps open it.
const ORDERED: Durability = Durability::Ordered { horizon: None };

/// The exhaustive sets build what their doc says: at every pair of adjacent batches,
/// in every tier and shape, every pair of escalations (none twice, none then some, the
/// same kind twice) and every pair of what follows them. Before, each batch took the
/// NEXT choice in a cycle after its neighbour's, so two plain barrier-only batches in a
/// row — the tier's commonest shape — were never built.
#[test]
fn the_exhaustive_sets_meet_every_pair_at_every_adjacent_place() {
    use std::collections::{HashMap, HashSet};
    fn esc_of(batch: &[Op]) -> Esc {
        match (batch.first(), batch.last()) {
            (Some(Op::Bind { .. }), _) => Esc::Principal,
            (_, Some(Op::Commit { group, .. })) if group.starts_with("/cur/p/") => Esc::Group,
            _ if batch.iter().any(
                |op| matches!(op, Op::Publish { subject, .. } if subject.starts_with("/e/")),
            ) =>
            {
                Esc::Subject
            }
            _ => Esc::No,
        }
    }
    type Pairs = (HashSet<(Esc, Esc)>, HashSet<(After, After)>);
    for max in [2, 3] {
        let mut seen: HashMap<(String, Vec<usize>, usize), Pairs> = HashMap::new();
        for w in exhaustive(&TIERS, &[16, 32, 64], 3, max) {
            let shape: Vec<usize> = w
                .batches
                .iter()
                .map(|b| b.len() - usize::from(matches!(b.first(), Some(Op::Bind { .. }))))
                .collect();
            for i in 1..w.batches.len() {
                let key = (format!("{:?}", w.tier), shape.clone(), i);
                let (escs, afters) = seen.entry(key).or_default();
                escs.insert((esc_of(&w.batches[i - 1]), esc_of(&w.batches[i])));
                afters.insert((w.after[i - 1], w.after[i]));
            }
        }
        assert!(!seen.is_empty());
        for ((tier, shape, i), (escs, afters)) in &seen {
            assert_eq!(
                escs.len(),
                16,
                "{tier} {shape:?} batches {i}-1,{i}: {escs:?}"
            );
            assert_eq!(
                afters.len(),
                9,
                "{tier} {shape:?} batches {i}-1,{i}: {afters:?}"
            );
        }
    }
}

/// The default sweep: the 2-batch exhaustive set at 16-, 32- and 64-byte blocks, then
/// the seeded random sample, each recovered and checked, a sample crashed twice.
#[test]
fn the_power_loss_law_holds_on_the_real_writer_and_open() {
    default_sweep(&Controls::default());
}

/// THE SAME LAW ON A LOG SEALED AT REST (`at-rest`): every open takes a key, so every
/// record's payload is sealed on the device (40 bytes longer, which moves every frame
/// boundary against the blocks) and recovery authenticates each one it keeps; the sweep's
/// properties and its not-vacuous checks hold as on a plaintext log. The simulated device
/// keeps no `<log>.seal`, so its records are sealed under the v1 index-only AAD
/// (`resolve_at_rest_key` on simulated storage); the v2 binding's AAD differs only in its
/// prefix and seal id, which changes no frame's size or place.
#[cfg(feature = "at-rest")]
#[test]
fn the_power_loss_law_holds_on_a_log_sealed_at_rest() {
    default_sweep(&Controls {
        key: Some([0x5a; 32]),
        ..Controls::default()
    });
}

/// [`the_power_loss_law_holds_on_the_real_writer_and_open`]'s sweep under `c`.
fn default_sweep(c: &Controls) {
    let c = *c;
    let workloads = exhaustive(&TIERS, &[16, 32, 64], 3, 2);
    let report = sweep(&workloads, 64, 16, &c, 0x5EED);
    eprintln!("exhaustive sweep: {report}");
    assert!(report.clean(), "exhaustive sweep:\n{report}");
    // Not vacuous: power losses did lose acked records (Relaxed), every such loss moved
    // the identity, and the moves carried lineage; short writes were taken.
    assert!(
        report.lost > 0
            && report.moved >= report.lost
            && report.with_lineage > 0
            && report.short_writes > 0,
        "the sweep exercised no loss:\n{report}"
    );
    // The Ordered arm too: its power losses lost acked (barrier-only) records, which P4
    // above held to a move, and escalated commits held the visible head for the full
    // flush they owed — so P3e was asked of records acked only after one.
    assert!(
        report.lost_ordered > 0 && report.held > 0,
        "the Ordered arm exercised no loss or no held head:\n{report}"
    );
    let mut rng = Rng(0xA57E);
    let random: Vec<Workload> = (0..60)
        .map(|i| random_workload(&mut rng, TIERS[i % TIERS.len()]))
        .collect();
    let report = sweep(&random, 64, 31, &c, 0xF00D);
    eprintln!("random sweep: {report}");
    assert!(report.clean(), "random sweep:\n{report}");
}

#[test]
fn rot_below_the_floor_or_behind_a_later_batch_is_refused_never_cut() {
    for tier in TIERS {
        let report = rot(tier, &Controls::default());
        assert!(report.clean(), "{tier:?} rot:\n{report}");
    }
}

/// The rot arm on a log sealed at rest: every byte of a clean keyed log flipped, each held
/// to the properties the plaintext arm is (P2, P4, P8); a record recovery keeps is also
/// authenticated.
#[cfg(feature = "at-rest")]
#[test]
fn rot_in_a_log_sealed_at_rest_is_refused_never_cut() {
    let c = Controls {
        key: Some([0x5a; 32]),
        ..Controls::default()
    };
    for tier in TIERS {
        let report = rot(tier, &c);
        assert!(report.clean(), "{tier:?} rot, sealed:\n{report}");
    }
}

#[test]
fn a_restored_copy_gets_no_lineage() {
    let report = restored_copy(&Controls::default());
    assert!(report.clean(), "{report}");
}

/// A revert to a build that predates the marks and log identity, then the upgrade
/// again: the older build's records above the floor are units of their own — every one
/// a flush covered is kept, and nothing is refused that the older build's own rules
/// recover.
#[test]
fn an_older_builds_records_above_the_floor_are_never_cut_as_a_torn_batch() {
    let report = older_build_appends(&Controls::default());
    eprintln!("older build above the floor: {report}");
    assert!(report.clean(), "{report}");
    assert!(
        report.recoveries > 0 && report.short_writes > 0,
        "nothing exercised:\n{report}"
    );
}

/// A record frame inside a record's body is no record behind a tear: no torn batch is
/// refused for one, on any image (P1), and every other property holds.
#[test]
fn a_record_frame_inside_a_body_never_refuses_a_torn_batch() {
    let report = sweep(
        &planted_frame_workloads(),
        64,
        8,
        &Controls::default(),
        0xB0D1,
    );
    eprintln!("frames inside bodies: {report}");
    assert!(report.clean(), "{report}");
    assert!(report.recoveries > 0, "{report}");
}

/// An open that cuts on a verdict the next open cannot re-derive from the device and the
/// boot, and dies (a process crash: the same boot) at ANY point after it first touched
/// the device: the next plain open makes the SAME cut under the identity and lineage the
/// first one settled. Phase 1 is what remembers what the dead open decided by — the
/// run's `Lossy` state (which phase 1 replaces), the embedder's one-shot prepare, the
/// tier the LAST run served where this open asks another, the floor it cut to on a log
/// whose sidecar recorded none, and the absence of any verdict — and the move a repair's
/// cut made. Forgetting the verdict, the next open resyncs the hole the first one cut
/// at, finds the later batch behind it and refuses the log; forgetting the move, it
/// finds the log already cut and serves it under the identity it had; reading this
/// open's tier as the last run's, it cuts a torn Strict batch at its first damage
/// instead of its start, keeping records no client was acked, and moves the generation
/// twice; holding a verdict the first open did not, it keeps the torn batch's intact
/// records the first one cut; with no floor at the cut, it judges the damage by the
/// batch seals from offset 0 and cuts below the repair's cut.
#[test]
fn a_cut_that_died_after_phase_1_is_made_again_under_the_same_verdict() {
    let c = Controls::default();
    let (relaxed, strict) = (Durability::Relaxed, Durability::Strict);
    let mut g = Gen::new(0);
    let batches = [g.batch(1, false), g.batch(2, false), g.batch(1, false)];
    // How the run's sidecar is left: as it wrote it; `Lossy`, a full durability flush
    // failed while it served; or in FORMAT 1 (the release before), which has no floor.
    #[derive(Clone, Copy)]
    enum Side {
        Recorded,
        Lossy,
        Format1,
    }
    // A run of `tier` in BOOT_A, then every byte it wrote landed but four: inside
    // record 1 (batch 1..=2) with batch 3 intact behind, or, `torn`, the last four of
    // batch 2 with batch 3 never written.
    let damaged = |tier: Durability, torn: bool, side: Side| {
        let batches = &batches[..if torn { 2 } else { 3 }];
        let w = Workload {
            tier,
            block: 16,
            prefix: false,
            batches: batches.to_vec(),
            after: Vec::new(),
            close: false,
        };
        let (sim, _) = start(&w, &c);
        let written = run(&sim, tier, BOOT_A, batches, &[], false, &c).written;
        let dir = Dir::Sim(sim.clone());
        let Ok(Prior::Recorded(s)) = logid::read(&dir) else {
            panic!("the run recorded its sidecar")
        };
        if let Side::Lossy = side {
            logid::write(&dir, &s.lossy()).expect("the sidecar is replaced");
        }
        let dev = sim.device();
        let mut img = dev.image(dev.epochs.len(), &dev.dirty, true, 0);
        if let Side::Format1 = side {
            let head = written.len() as u64;
            img.id = Some(logid::format1_for_test(s.identity, 0, head, &img.logical));
        }
        let h = &img.logical[..HEADER_SIZE];
        let second = HEADER_SIZE + u32::from_le_bytes([h[4], h[5], h[6], h[7]]) as usize;
        let at = if torn {
            img.logical.len() - 4
        } else {
            second + 20
        };
        img.logical[at..at + 4].fill(0);
        img.durable = img.logical.clone();
        (img, s.identity)
    };
    // What open #1 decides by, how it opens and the records it keeps; open #2 is a
    // plain open in its boot.
    struct Arm {
        why: &'static str,
        run_tier: Durability,
        torn: bool,
        side: Side,
        boot: [u8; 16],
        tier: Durability,
        repair: bool,
        prepared: Option<&'static str>,
        kept: usize,
    }
    let plain = Arm {
        why: "",
        run_tier: relaxed,
        torn: false,
        side: Side::Recorded,
        boot: BOOT_A,
        tier: relaxed,
        repair: false,
        prepared: None,
        kept: 1,
    };
    let arms = [
        Arm {
            why: "the Lossy state",
            side: Side::Lossy,
            ..plain
        },
        Arm {
            why: "the embedder's prepare",
            prepared: Some("mark"),
            ..plain
        },
        Arm {
            why: "a repair",
            repair: true,
            ..plain
        },
        Arm {
            why: "the last run's tier",
            run_tier: strict,
            torn: true,
            boot: BOOT_B,
            ..plain
        },
        // The run's own boot, so no verdict: the damaged frame is whole-sized (rot, which
        // the recovery cannot tell from a tear), and its batch is cut whole, at its start.
        Arm {
            why: "no verdict",
            torn: true,
            ..plain
        },
        // No floor to judge by: the repair cuts at the damage, inside the torn batch.
        Arm {
            why: "a repair of a FORMAT 1 log",
            torn: true,
            side: Side::Format1,
            repair: true,
            kept: 2,
            ..plain
        },
    ];
    for a in arms {
        let (arm, tier, boot) = (a.why, a.tier, a.boot);
        let (img, before) = damaged(a.run_tier, a.torn, a.side);
        let one = Sim::with(img.clone());
        one.trace_on();
        let opened = open_as(&one, tier, boot, &c, a.repair, a.prepared)
            .unwrap_or_else(|e| panic!("{arm}: open #1 cuts at the hole: {e}"));
        let cut = (
            opened.read_from(Offset::ZERO).len(),
            opened.identity(),
            opened.lineage().clone(),
        );
        drop(opened);
        assert_eq!(
            (cut.0, cut.1.generation),
            (a.kept, before.generation + 1),
            "{arm}: open #1 kept the records before the cut and moved the generation"
        );
        let mut crashed = 0;
        for (i, died) in one.take_trace().into_iter().enumerate() {
            let untouched = died.logical == img.logical;
            if untouched && died.id == img.id {
                continue;
            }
            crashed += 1;
            match open(&Sim::with(died), tier, boot, &c) {
                // A repair is the operator's, not a verdict the log keeps: until its
                // cut lands, a plain open may refuse the hole as it did before.
                Err(_) if a.repair && untouched => {}
                Err(e) => panic!("{arm}, a crash at state {i}: open #2 refused: {e}"),
                Ok(again) => assert_eq!(
                    (
                        again.read_from(Offset::ZERO).len(),
                        again.identity(),
                        again.lineage().clone()
                    ),
                    cut,
                    "{arm}, a crash at state {i}: the same cut, under what open #1 settled"
                ),
            }
        }
        assert!(crashed > 1, "{arm}: open #1 wrote phase 1, then cut");
    }
}

/// THE OUTCOME-UNKNOWN RESEND LANDS EXACTLY ONCE, whatever the device kept
/// (`broker.poisoned-refusal`): the cure an embedder relies on after a FAILED full flush
/// poisoned the open. The batch held an escalated publish and an ordinary one behind it;
/// both ops were answered "outcome unknown", the embedder reopens the log, and the
/// producer resends both under the same pinned `(producer_id, producer_seq)`s, in order.
/// Two branches, one law, for each op:
///
/// - KEPT: the supervisor's reopen in the same boot (the broker exits on the poison: a
///   process exit, which loses nothing the kernel holds), and every power-loss image that
///   kept the record. The resend DEDUPS to the recovered record — its offset, `deduped`,
///   acked at once — and nothing is written for it. Here the open's flush covers the
///   record, because the injected fault fails the flush before it touches the device and
///   leaves the record's blocks dirty for the open to write. A real device is not bound
///   to that: a failed flush can leave the pages clean but unwritten (Linux's
///   `fdatasync` after EIO; on Apple, a drive-cache reset after the barrier), and the
///   open's flush then has nothing to rewrite — the HONEST BOUNDARY
///   `BrokerLog::flush_failed_lossy` states. The same-boot dedup then acks a record that
///   may be on no media; a later power loss that takes it is REFUSED at the next open
///   (damage below the floor) and `asb repair` cuts it: loud, never silent, but the op
///   acked has then landed zero times. This simulation cannot reach that case.
/// - CUT: a power-loss image in which the device dropped the record — on Relaxed its
///   blocks still volatile after the `Lossy` sidecar, whose flush leaves the log's page
///   cache alone; on Ordered issued in the batch's barrier epoch before the sidecar
///   drained it — or tore the batch it was in. Recovery cuts it as a torn tail, the dedup
///   map it rebuilds holds no entry for its key, and the resend appends it FRESH at the
///   cut point (the recovered head, the ops in order), once; the escalated one owes and
///   takes its full flush.
///
/// EVERY power-loss image of every device state from the one before the batch's write
/// through the poison is recovered in the next boot: every subset of each epoch prefix's
/// blocks, with and without its size change (`images` says it enumerated them all, and
/// the test asserts it did). On each, and on the same-boot reopen, the generation has
/// moved under the same id (the run was recorded `Lossy`, or it served a weak tier and
/// did not stop cleanly in another boot) — or, on an image that kept no record at all,
/// the log took a fresh id — and the log ends holding exactly one record under each key,
/// the one its resend was answered with. The REVERSE holds on every one too: `deduped` is
/// answered exactly when the recovered log holds the key, at that record's own offset —
/// never for a record the recovered log lacks, such as one whose frame survived intact in
/// a batch the recovery cut. Not vacuous, counted over the images of a state after the
/// batch's write (one before it dropped nothing): each tier reaches both branches, the
/// cut one with the record before the batch kept and with the escalated body still on
/// the image (a torn batch the recovery cut, where an open that rebuilt dedup before its
/// cut would answer `deduped`); Relaxed also keeps the escalated record and cuts the one
/// behind it.
#[test]
fn the_outcome_unknown_resend_after_a_poison_lands_exactly_once() {
    // The held batch: an escalated publish (the op whose flush failed), then an ordinary
    // one the held head kept back behind it.
    const OPS: [(u64, &str, &[u8]); 2] = [
        (2, "/e/a", b"a person's word"),
        (3, "/o/b", b"machine chatter after it"),
    ];
    let c = Controls::default();
    // Room for every image of every epoch prefix: 2^15 subsets of Relaxed's 15 volatile
    // blocks (including each record's 9-byte `bt` trailer), each with and without the
    // size change, is 2^16.
    const IMAGES: usize = 1 << 17;
    let mut rng = Rng(0x0D0B_1E5E);
    for tier in [ORDERED, Durability::Relaxed] {
        let sim = Sim::with(Device::new(16));
        let mut log = open(&sim, tier, BOOT_A, &c).expect("the first open");
        log.stage_publish(1, 1, "/o/a".into(), b"before".to_vec())
            .expect("staged");
        log.commit_batch().expect("committed");
        let told = log.identity();
        sim.trace_on();
        for (seq, subject, body) in OPS {
            log.stage_publish(1, seq, subject.into(), body.to_vec())
                .expect("staged");
        }
        let committed = log.commit_batch().expect("committed");
        assert_eq!(committed.visible_now, Offset(1), "{tier:?}: both held");
        assert_eq!(
            committed.owe_full,
            Some(Offset(3)),
            "{tier:?}: owes a flush"
        );
        log.inject_faults(InjectedFaults {
            write: false,
            sync: true,
            truncate: false,
        });
        let err = log.flush_handle().full().expect_err("the injected fault");
        log.full_flush_failed(&err);
        assert!(log.poisoned().is_some(), "{tier:?}: the open is poisoned");
        // The broker exits on the poison: no clean close.
        drop(log);
        let trace = sim.take_trace();
        // The trace starts at the state before the batch's write, which grows the file:
        // an image of a state at that size never held the batch, so nothing was dropped.
        let unwritten = trace[0].logical.len();
        let poisoned = sim.device();
        assert!(
            poisoned.logical.len() > unwritten,
            "{tier:?}: the batch's write grew the file"
        );
        // The escalated body as the batch wrote it: an image the recovery cut the record
        // from that still holds it held a torn batch, not merely a dropped one.
        let body = OPS[0].2;
        let mut recoveries = vec![(
            Sim::with(poisoned),
            BOOT_A,
            true,
            "the supervisor's reopen in the same boot".to_string(),
        )];
        let mut enumerated = 0;
        for (state, dev) in trace.iter().enumerate() {
            let (imgs, every) = images(dev, IMAGES, &mut rng);
            assert!(
                every,
                "{tier:?}: every power-loss image of state {state}, not a sample"
            );
            let written = dev.logical.len() > unwritten;
            enumerated += imgs.len();
            for (i, img) in imgs.into_iter().enumerate() {
                recoveries.push((
                    Sim::with(img),
                    BOOT_B,
                    written,
                    format!("a power loss at state {state}, image {i}"),
                ));
            }
        }
        // Recoveries that kept both records; that kept the escalated record but cut the
        // one behind it; that cut the escalated record after the batch was written — of
        // those, the ones that kept the record before the batch, and the ones whose image
        // still held the escalated body (a torn batch the recovery cut) — and those of a
        // state before the batch's write, which dropped nothing.
        let (mut kept, mut split, mut cut, mut cut_after_before, mut cut_torn, mut unwritten) =
            (0, 0, 0, 0, 0, 0);
        for (image, boot, written, what) in recoveries {
            let torn = written
                && image
                    .device()
                    .logical
                    .windows(body.len())
                    .any(|w| w == body);
            let mut rec = open(&image, tier, boot, &c)
                .unwrap_or_else(|e| panic!("{tier:?}, {what}: the open refused: {e}"));
            let recovered = records_of(&rec);
            let identity = rec.identity();
            if recovered.is_empty() {
                // A log that holds no record takes a fresh id: no offset names anything.
                assert_ne!(
                    identity.id, told.id,
                    "{tier:?}, {what}: an empty log takes a fresh id ({identity}, was {told})"
                );
            } else {
                assert!(
                    identity.id == told.id && identity.generation > told.generation,
                    "{tier:?}, {what}: the generation moved ({identity}, was {told})"
                );
            }
            let head = rec.head().0;
            let at = |seq: u64| {
                recovered
                    .iter()
                    .find(|r| (r.producer_id, r.producer_seq) == (1, seq))
                    .map(|r| r.seq.0)
            };
            let mut answers = Vec::new();
            let mut fresh = head;
            for (seq, subject, body) in OPS {
                let (off, deduped) = rec
                    .stage_publish(1, seq, subject.into(), body.to_vec())
                    .unwrap_or_else(|e| panic!("{tier:?}, {what}: resending {seq}: {e:?}"));
                assert_eq!(
                    deduped,
                    at(seq).is_some(),
                    "{tier:?}, {what}: {seq} deduped exactly when the recovered log holds it"
                );
                let want = at(seq).unwrap_or_else(|| {
                    fresh += 1;
                    fresh - 1
                });
                assert_eq!(
                    off.0, want,
                    "{tier:?}, {what}: {seq} answered with its record's offset, or the cut point"
                );
                answers.push((seq, off, deduped));
            }
            let committed = rec.commit_batch().expect("the resends' batch commits");
            let escalated_fresh = at(2).is_none();
            assert_eq!(
                committed.owe_full.is_some(),
                escalated_fresh,
                "{tier:?}, {what}: a flush is owed exactly for a fresh escalated record"
            );
            for &(_, off, deduped) in &answers {
                if deduped {
                    assert!(
                        committed.acks_now(off.0, true),
                        "{tier:?}, {what}: a covered original is acked at once"
                    );
                }
            }
            if let Some(target) = committed.owe_full {
                full_flush(&mut rec, target.0, false);
            }
            assert_eq!(
                (rec.head().0, rec.visible_head().0),
                (fresh, fresh),
                "{tier:?}, {what}: only the cut records were written, and all are shown"
            );
            let after = records_of(&rec);
            assert_eq!(
                after[..recovered.len()],
                recovered[..],
                "{tier:?}, {what}: nothing recovered is rewritten"
            );
            for ((seq, subject, body), &(_, off, _)) in OPS.iter().zip(&answers) {
                let copies: Vec<&BrokerRecord> = after
                    .iter()
                    .filter(|r| (r.producer_id, r.producer_seq) == (1, *seq))
                    .collect();
                assert_eq!(copies.len(), 1, "{tier:?}, {what}: {seq} exactly once");
                assert_eq!(
                    (
                        copies[0].seq,
                        copies[0].subject.as_str(),
                        copies[0].body.as_slice()
                    ),
                    (off, *subject, *body),
                    "{tier:?}, {what}: {seq} is the record its resend was answered with"
                );
            }
            match (at(2).is_some(), at(3).is_some()) {
                (true, true) => kept += 1,
                (true, false) => split += 1,
                (false, _) if !written => unwritten += 1,
                (false, _) => {
                    cut += 1;
                    cut_after_before += usize::from(head == 1);
                    cut_torn += usize::from(torn);
                }
            }
        }
        eprintln!(
            "{tier:?}: {enumerated} power-loss images (every one of {} states) and the \
             same-boot reopen: {kept} kept both records (the resends dedup); {split} kept the \
             escalated one and cut the one behind it; {cut} written and then cut the escalated \
             one (its resend appends; {cut_after_before} with the record before the batch \
             kept, {cut_torn} with its body still on the image); {unwritten} of a state \
             before the batch's write",
            trace.len()
        );
        assert!(
            kept > 0 && cut > 0 && cut_after_before > 0 && cut_torn > 0,
            "{tier:?}: both branches reached ({kept} kept; {cut} written and cut, \
             {cut_after_before} right after the record before the batch, {cut_torn} with the \
             escalated body on the image)"
        );
        if matches!(tier, Durability::Relaxed) {
            assert!(
                split > 0,
                "{tier:?}: an image keeps the escalated record and cuts the one behind it"
            );
        }
    }
}

/// The baseline the floor rules improve on: the rules that predate the floor (the
/// floor ignored, so the recovery cannot tell a torn batch from damage) REFUSE power-loss
/// images the floor rules recover — at these small blocks, so not a field rate.
#[test]
fn the_rules_before_the_floor_refuse_images_the_floor_rules_recover() {
    for tier in TIERS {
        let c = Controls {
            mutation: Mutation::IgnoreFloor,
            ..Controls::default()
        };
        let report = control_sweep(tier, &c);
        eprintln!("{tier:?} under the rules before the floor: {report}");
        must_fail(&report, "P1", "refused with a known floor");
        assert!(report.refusals > 0, "{report}");
    }
}

/// A small sweep for the negative controls: one tier, both block sizes, the 2-batch set.
fn control_sweep(tier: Durability, c: &Controls) -> Report {
    sweep(&exhaustive(&[tier], &[16, 64], 1, 2), 32, 8, c, 0xC0DE)
}

/// Assert `report` violates `property` and that one of its examples says `reason`.
fn must_fail(report: &Report, property: &str, reason: &str) {
    assert!(
        report.violated(property) > 0,
        "the control did not break {property}:\n{report}"
    );
    assert!(
        report
            .examples
            .iter()
            .any(|e| e.starts_with(property) && e.contains(reason)),
        "{property} broke, but not for the reason {reason:?}:\n{report}"
    );
}

/// NC2: the writer before the marks. Its records carry no mark, so each is a unit of
/// its own — what an older build's records are — and a torn multi-record batch with a
/// hole in an early record and a later one intact reads as damage behind a completed
/// write: refused, as the rules before the floor refuse it.
#[test]
fn nc2_a_writer_without_marks_has_its_torn_batches_refused() {
    let c = Controls {
        unsealed_writer: true,
        ..Controls::default()
    };
    must_fail(
        &control_sweep(Durability::Strict, &c),
        "P1",
        "carries no batch mark",
    );
}

#[test]
fn nc4_power_loss_recovered_as_the_same_boot_loses_acked_records_silently() {
    let c = Controls {
        power_loss_same_boot: true,
        ..Controls::default()
    };
    must_fail(
        &control_sweep(Durability::Relaxed, &c),
        "P4",
        "under the unchanged identity",
    );
}

#[test]
fn nc5_a_floor_written_before_the_flush_refuses_honest_power_losses() {
    let c = Controls {
        mutation: Mutation::FloorBeforeFlush,
        ..Controls::default()
    };
    // Process-crash images (records only in the page cache) reopened, and the reopen
    // crashed before its flush: the second-crash arm on every recovery.
    let report = sweep(
        &exhaustive(&[Durability::Strict], &[16], 1, 2),
        32,
        1,
        &c,
        0xC0DE,
    );
    must_fail(&report, "P1", "below the log's durable floor");
}

#[test]
fn nc6_cutting_at_any_damage_cuts_rot_below_the_floor() {
    let c = Controls {
        mutation: Mutation::CutAtAnyDamage,
        ..Controls::default()
    };
    must_fail(&rot(Durability::Strict, &c), "P8", "was cut, not refused");
}

/// NC8: the cut-at-the-first-damage rule with no unclean verdict (a design's
/// unconditioned rule), everything else of that rule kept — the intact records behind
/// the cut, and a written frame at it, still move the generation. What it breaks is
/// P8: rot in an OLDER batch, which the verdict-less rules refuse (a later batch is
/// intact behind it), is cut away with every acked batch after it.
#[test]
fn nc8_a_relaxed_cut_without_the_unclean_verdict_cuts_rot_in_an_older_batch() {
    let c = Controls {
        mutation: Mutation::RelaxedCutWithoutVerdict,
        ..Controls::default()
    };
    must_fail(
        &rot(Durability::Relaxed, &c),
        "P8",
        "not the newest, was cut, not refused",
    );
}

#[test]
fn nc9_lineage_for_a_restored_shorter_copy_misleads_a_reader() {
    let c = Controls {
        mutation: Mutation::LineageOnShorter,
        ..Controls::default()
    };
    must_fail(&restored_copy(&c), "P7", "differ from what it saw");
}

#[test]
fn nc10_a_reader_that_rebases_at_the_head_skips_records() {
    let c = Controls {
        rebase_at_head: true,
        ..Controls::default()
    };
    must_fail(&control_sweep(Durability::Relaxed, &c), "P7", "never saw");
}

#[test]
fn nc11_without_the_empty_frame_rule_a_torn_header_refuses() {
    let c = Controls {
        mutation: Mutation::NoEmptyFrameRule,
        ..Controls::default()
    };
    must_fail(
        &control_sweep(Durability::Strict, &c),
        "P1",
        "record payload does not parse",
    );
}

/// NC1: the Ordered tier on a device that IGNORES barriers (the plain-fsync device): a
/// power loss can keep a later batch and lose an earlier one, which the floor rules
/// refuse as damage behind a completed batch (P1) — and nothing is silently lost: every
/// open that does not refuse still keeps a prefix of whole batches (P2 holds). This is
/// what a device that broke Apple's barrier contract would cost: a refusal, never a
/// quiet hole.
#[test]
fn nc1_a_device_that_ignores_barriers_refuses_the_ordered_log_never_loses_silently() {
    let c = Controls {
        ignore_barriers: true,
        ..Controls::default()
    };
    let report = control_sweep(ORDERED, &c);
    must_fail(&report, "P1", "a later batch completed behind the damage");
    assert_eq!(
        report.violated("P2"),
        0,
        "the barrier-less device's failure is a refusal, never a silent loss:\n{report}"
    );
}

/// NC3: the escalation table emptied while the harness's oracle still expects the
/// escalated records durable once acked: the product acks them at the barrier (Ordered)
/// or the page-cache write (Relaxed), and a power loss takes one (P3e).
#[test]
fn nc3_without_the_escalation_table_an_acked_escalated_record_is_lost() {
    for tier in [ORDERED, Durability::Relaxed] {
        let c = Controls {
            no_escalation: true,
            ..Controls::default()
        };
        must_fail(
            &control_sweep(tier, &c),
            "P3e",
            "an escalated record acked at offset",
        );
    }
}

/// NC7: the horizon's full flush issued as a BARRIER while the product is told it was
/// full: the durable head it claims runs ahead of the media, and a power loss takes a
/// record below it (P3).
#[test]
fn nc7_a_horizon_issued_as_a_barrier_loses_records_claimed_durable() {
    let c = Controls {
        horizon_as_barrier: true,
        ..Controls::default()
    };
    must_fail(&control_sweep(ORDERED, &c), "P3", "the product claimed");
}

/// The full exhaustive sweep the evidence claim runs: the 3-batch set at every block
/// size, one recovery in 16 crashed a second time.
#[test]
#[ignore = "the full sweep (about eight minutes for both, debug, on the dev Mac): run by the broker.crash-sim.prefix-law claim"]
fn the_power_loss_law_holds_over_the_full_exhaustive_sweep() {
    let c = Controls::default();
    let workloads = exhaustive(&TIERS, &[16, 32, 64], 3, 3);
    let report = sweep(&workloads, 64, 16, &c, 0x5EED_F011);
    eprintln!("full exhaustive sweep: {report}");
    assert!(report.clean(), "full exhaustive sweep:\n{report}");
    assert!(report.lost > 0 && report.with_lineage > 0, "{report}");
}

/// The full random sample the evidence claim runs: 3000 seeded workloads of 4–8
/// batches, one recovery in 31 crashed a second time.
#[test]
#[ignore = "the full sweep (about eight minutes for both, debug, on the dev Mac): run by the broker.crash-sim.prefix-law claim"]
fn the_power_loss_law_holds_over_the_full_random_sample() {
    let c = Controls::default();
    let mut rng = Rng(0x00DD_BA11);
    let random: Vec<Workload> = (0..3000)
        .map(|i| random_workload(&mut rng, TIERS[i % TIERS.len()]))
        .collect();
    let report = sweep(&random, 64, 31, &c, 0xF00D_F00D);
    eprintln!("full random sample: {report}");
    assert!(report.clean(), "full random sample:\n{report}");
    assert!(report.lost > 0 && report.with_lineage > 0, "{report}");
}
