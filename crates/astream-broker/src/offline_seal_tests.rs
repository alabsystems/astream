// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The offline seal's tests (`offline_seal.rs`), on real logs: a seal reads back as the
//! plaintext log it replaced (every record at its offset, the identity, the carried state and
//! the held store) and leaves no plaintext in the log, `.state` or `.held`; a crash after every
//! durable step, the process stopped dead or the power gone (every directory `power_loss.rs`
//! says it can leave), opens wholly plaintext or wholly sealed, never a mix, whichever open
//! comes first; a copy that does not read back is never switched in; and the refusals.
//!
//! NEGATIVE CONTROLS. Live: the sentinel scan finds every sentinel in the plaintext log's own
//! files before the seal (so the scan can see one), and none after it; a keyed open refuses
//! the plaintext log a failed seal leaves (so "wholly plaintext" is not a sealed log in
//! disguise), and a keyless one refuses the sealed log a finished one leaves; a staged copy
//! altered in one record, one held frame or the carried state, each sealed validly, is
//! refused by the read-back, the plaintext log untouched (`a_copy_that_does_not_read_back_*`).
//! Planted, each a break scratch-reverted that fails the test named: an open whose settle
//! does nothing (the crash law: a staging left beside the log); a switch made with no marker
//! (the crash law: an image a rename into opens as neither side); and a read-back that only
//! opens the copy, comparing nothing (`a_copy_that_does_not_read_back_*`: the altered copy
//! is switched in). Seen failing before their fixes landed, each against the code before it:
//! a switch finished with no look at the log it was made for (`a_switch_is_never_finished_*`:
//! the acked record dropped), a retry's keyless open reported as not plaintext
//! (`a_retried_seal_*`: InvalidData), a settle that relocks the name only after the rename
//! (`a_finished_switch_hands_back_*`: the name lockable in between), and the replica and `.hw`
//! refusals taken before the plaintext log is closed (`a_seal_refuses_*`: left open). Live:
//! a log an older build only read finishes its switch (the check refuses no open that changed
//! nothing).
//! Nothing sleeps and no clock is read: the retention tick runs on a hand clock.

use super::*;
use crate::retention::{Retention, Rule};
use crate::test_scratch::Scratch;
use astream_wire::Filter;
use std::time::Duration;

const KEY: [u8; 32] = [0x3c; 32];
const OTHER_KEY: [u8; 32] = [0x3d; 32];

const EV: &str = "/f/F/pub/n1/s1/ev";
/// The mail the hold rule keeps below the cut, unread: the `.held` sentinel's record.
const MAIL: &str = "/f/F/in/n1/from/a";
/// A quiet subject whose one record falls below the cut: its `Last` row is carried in
/// `.state`, its name and body with it.
const QUIET: &str = "/a/q/SENTINEL-QUIET-SUBJECT";
const WILL_TO: &str = "/a/w/SENTINEL-WILL-SUBJECT";

const LOG_SENTINEL: &[u8] = b"SENTINEL-IN-THE-LOG";
const HELD_SENTINEL: &[u8] = b"SENTINEL-IN-HELD";
const STATE_SENTINEL: &[u8] = b"SENTINEL-IN-STATE";
const DAY: u64 = 24 * 3_600_000;
/// The hand clock's start (unix ms).
const T0: u64 = 1_800_000_000_000;

/// The newest publish's key: a resend must dedup to its offset after any seal or crash.
const NEWEST: (u64, u64) = (7, 500);

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle)
}

/// One log in its own scratch directory.
struct Fx {
    root: Scratch,
    path: PathBuf,
}

impl Fx {
    fn new(tag: &str) -> Fx {
        let root = Scratch::new(tag);
        let path = root.path().join("bus.log");
        Fx { root, path }
    }

    fn dir(&self) -> &Path {
        self.root.path()
    }

    fn file(&self, sfx: &str) -> PathBuf {
        beside(&self.path, sfx)
    }

    fn plain(&self) -> io::Result<BrokerLog> {
        BrokerLog::open(&self.path)
    }

    fn sealed(&self) -> io::Result<BrokerLog> {
        BrokerLog::open_encrypted_bound(&self.path, KEY)
    }

    /// The seal's own files beside the log that are present: the staging and the marker.
    fn leftovers(&self) -> Vec<String> {
        let mut out = Vec::new();
        for name in std::fs::read_dir(self.dir()).unwrap().flatten() {
            let n = name.file_name().to_string_lossy().into_owned();
            if n.starts_with("bus.log.sealing") || n.starts_with("bus.log.sealmove") {
                out.push(n);
            }
        }
        out
    }

    /// Whether `needle` is in the log or in its `sfx` sidecar.
    fn holds(&self, sfx: &str, needle: &[u8]) -> bool {
        let p = if sfx.is_empty() {
            self.path.clone()
        } else {
            self.file(sfx)
        };
        contains(&std::fs::read(p).unwrap_or_default(), needle)
    }
}

/// aterm's shape of rules, small: the bulk stream by bytes, mail held until its node's inbox
/// reads it, presence by its last value, everything else by its last value.
fn rules() -> Retention {
    Retention::new(
        vec![
            Rule::prefix("/f/F/pub/*/*/ev").unwrap().max_bytes(2_000),
            Rule::hold("/f/F/in/>")
                .unwrap()
                .max_age(Duration::from_millis(7 * DAY))
                .until_read("/f/{2}/cur/{4}/node/inbox")
                .unwrap(),
            Rule::hold("/f/F/pub/*/*/presence").unwrap().last_only(),
        ],
        Rule::default_hold(),
    )
    .unwrap()
}

fn will() -> WillRecord {
    WillRecord {
        producer_id: 9,
        producer_seq: 4,
        subject: WILL_TO.to_string(),
        body: STATE_SENTINEL.to_vec(),
    }
}

/// A plaintext log as aterm's broker leaves one: rules set (so a `.held` store), a binding,
/// a pending will, a group commit, a quiet subject and an unread mail below a cut the rules
/// make (so a `.base` and a carried `.state`), and records after it. Its last open is left
/// open, as a killed broker's (Strict, so nothing moves).
fn seed(fx: &Fx) {
    let mut log = fx.plain().unwrap();
    log.set_retention(rules()).unwrap();
    log.stage_bind(7, "h-alice".into()).unwrap();
    log.stage_will_register(&will()).unwrap();
    log.stage_publish(9, 1, QUIET.into(), STATE_SENTINEL.to_vec())
        .unwrap();
    log.stage_publish(9, 2, MAIL.into(), HELD_SENTINEL.to_vec())
        .unwrap();
    log.stage_commit("g1".into(), 1).unwrap();
    log.commit_batch().unwrap();
    for i in 0..60u64 {
        log.stage_publish(
            7,
            10 + i,
            EV.into(),
            format!("ev-{i:04}-padding-padding").into_bytes(),
        )
        .unwrap();
        if i % 7 == 6 {
            log.commit_batch().unwrap();
        }
    }
    log.commit_batch().unwrap();
    let tick = log.retain_by_rules(T0).unwrap();
    assert!(tick.base > 5, "the rules cut below the head: {tick:?}");
    log.publish(7, 499, EV.into(), LOG_SENTINEL.to_vec())
        .unwrap();
    log.publish(NEWEST.0, NEWEST.1, EV.into(), b"newest".to_vec())
        .unwrap();
    drop(log);
    for sfx in [".base", ".state", ".held", ".id"] {
        assert!(fx.file(sfx).exists(), "the seed has {sfx}");
    }
}

/// What a reader can see of a log: every record (each offset from the base to the head
/// once), every `Last` row, the binding, the pending wills, the group's resume point, the
/// held mail below the base, and the identity.
#[derive(Debug, PartialEq, Eq)]
struct Snap {
    identity: crate::LogIdentity,
    base: u64,
    head: u64,
    records: Vec<(u64, u64, u64, String, Vec<u8>)>,
    last: Vec<(String, u64, Vec<u8>)>,
    binding: Option<(String, u64)>,
    wills: Vec<WillRecord>,
    group: u64,
    held_mail: Vec<(u64, Vec<u8>)>,
}

fn snap(log: &mut BrokerLog) -> Snap {
    let (base, head) = (log.base().0, log.head().0);
    let recs = log.read_from(Offset(0));
    for (i, r) in recs.iter().enumerate() {
        assert_eq!(
            r.seq.0,
            base + i as u64,
            "a record read twice, or one missing"
        );
    }
    let all = Filter::new("/>").unwrap();
    drop(log.publish_last_visible(head).unwrap());
    let mut view = log.last_view_at(head).unwrap();
    let (page, _) = log
        .last_matching(&all, "", 1000, 100_000, &mut view)
        .unwrap()
        .into_page()
        .expect("one bounded step");
    let (mail, _) = log.fetch(0, &Filter::new("/f/F/in/>").unwrap(), 100, 100_000, head);
    Snap {
        identity: log.identity(),
        base,
        head,
        records: recs
            .iter()
            .map(|r| {
                (
                    r.seq.0,
                    r.producer_id,
                    r.producer_seq,
                    r.subject.clone(),
                    r.body.clone(),
                )
            })
            .collect(),
        last: page
            .iter()
            .map(|r| (r.subject.clone(), r.seq.0, r.body.clone()))
            .collect(),
        binding: log.binding(7).map(|(p, off)| (p.to_string(), off.0)),
        wills: log.pending_wills(),
        group: log.group_start("g1").0,
        held_mail: mail.iter().map(|r| (r.seq.0, r.body.clone())).collect(),
    }
}

/// The reference: the seeded log as an open reads it.
fn reference(fx: &Fx) -> Snap {
    let mut log = fx.plain().unwrap();
    let s = snap(&mut log);
    assert!(s.base > 0 && !s.held_mail.is_empty() && s.binding.is_some());
    assert!(
        s.last.iter().any(|(subj, ..)| subj == QUIET),
        "{:?}",
        s.last
    );
    assert_eq!(s.wills.len(), 1);
    s
}

/// The sentinel scan: which of the log, `.state` and `.held` hold their sentinel.
fn sentinels(fx: &Fx) -> [bool; 3] {
    [
        fx.holds("", LOG_SENTINEL),
        fx.holds(".state", STATE_SENTINEL),
        fx.holds(".held", HELD_SENTINEL),
    ]
}

/// A log read back whole after its seal, or its plaintext kept whole after a failed one:
/// `want` from the open that fits, a resend of the newest key dedups, a new record lands,
/// and the open that does not fit refuses.
fn reads_whole(fx: &Fx, sealed: bool, want: &Snap, at: &str) {
    let mut log = if sealed { fx.sealed() } else { fx.plain() }
        .unwrap_or_else(|e| panic!("{at}: the open refused: {e}"));
    assert_eq!(&snap(&mut log), want, "{at}");
    let resend = log
        .publish(NEWEST.0, NEWEST.1, EV.into(), b"newest".to_vec())
        .unwrap();
    assert_eq!(
        resend,
        (Offset(want.head - 1), true),
        "{at}: the newest key dedups"
    );
    log.publish(7, 900, EV.into(), b"after".to_vec()).unwrap();
    log.close_clean().unwrap();
    drop(log);
    let refused = if sealed {
        fx.plain().err()
    } else {
        BrokerLog::open_encrypted(&fx.path, KEY).err()
    };
    assert_eq!(
        refused.map(|e| e.kind()),
        Some(io::ErrorKind::InvalidData),
        "{at}: the open that does not fit the log refuses it"
    );
}

/// THE SEAL READS BACK AS THE LOG: every record at its offset, the identity, every `Last`
/// row (a carried quiet subject's included), the binding, the will, the group's resume point
/// and the held mail, under the key and bound; no sentinel is left in the log, `.state` or
/// `.held` (NC: all three were there before); `.seal` exists and nothing of the seal's own is
/// left; a keyless open refuses; a second seal refuses, changing nothing.
#[test]
fn a_sealed_log_reads_back_as_the_plaintext_one_and_holds_no_plaintext() {
    let fx = Fx::new("seal-ok");
    seed(&fx);
    let want = reference(&fx);
    assert_eq!(
        sentinels(&fx),
        [true; 3],
        "NC: the scan sees each sentinel in the clear"
    );
    let sealed = BrokerLog::seal_plaintext(&fx.path, KEY).unwrap();
    assert_eq!(
        (sealed.identity, sealed.base.0, sealed.head.0),
        (want.identity, want.base, want.head)
    );
    assert_eq!(sealed.bytes, std::fs::metadata(&fx.path).unwrap().len());
    assert_eq!(sentinels(&fx), [false; 3], "a sentinel survived the seal");
    assert!(fx.file(".seal").exists());
    assert!(fx.leftovers().is_empty(), "{:?}", fx.leftovers());
    let before = std::fs::read(&fx.path).unwrap();
    let err = BrokerLog::seal_plaintext(&fx.path, KEY).unwrap_err();
    assert!(err.to_string().contains("sealed already"), "{err}");
    assert_eq!(
        std::fs::read(&fx.path).unwrap(),
        before,
        "a second seal changed the log"
    );
    let err = BrokerLog::open_encrypted_bound(&fx.path, OTHER_KEY)
        .err()
        .expect("another key opened the sealed log");
    assert_eq!(err.kind(), io::ErrorKind::InvalidData, "another key: {err}");
    reads_whole(&fx, true, &want, "sealed");
}

/// A log with no record and no sidecar but its identity seals too: the empty sealed log opens
/// bound and takes records. (An empty log takes a fresh id at every open, `logid.rs`: nobody
/// can hold an offset into it, so the seal keeps none.)
#[test]
fn an_empty_log_seals() {
    let fx = Fx::new("seal-empty");
    drop(fx.plain().unwrap());
    let sealed = BrokerLog::seal_plaintext(&fx.path, KEY).unwrap();
    assert_eq!((sealed.base.0, sealed.head.0, sealed.bytes), (0, 0, 0));
    assert!(fx.file(".seal").exists() && fx.leftovers().is_empty());
    let mut log = fx.sealed().unwrap();
    log.publish(1, 1, "/a/x".into(), b"secret-first".to_vec())
        .unwrap();
    drop(log);
    assert!(!fx.holds("", b"secret-first"));
}

/// Whether the log's identity sidecar says its last run was closed cleanly.
fn closed_cleanly(fx: &Fx) -> bool {
    matches!(
        logid::read(&Dir::Os(fx.path.clone())).unwrap(),
        logid::Prior::Recorded(s) if s.state == logid::State::Closed
    )
}

/// THE REFUSALS, each leaving everything as it was: no log (none is created), a log a broker
/// holds (`AlreadyExists`, nothing staged), a replica, a log beside a watermark. A refusal after the plaintext open
/// leaves the log closed cleanly (NC: it was left open before).
#[test]
fn a_seal_refuses_what_it_must_not_touch() {
    let fx = Fx::new("seal-refuse");
    let err = BrokerLog::seal_plaintext(&fx.path, KEY).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::NotFound, "{err}");
    assert!(!fx.path.exists(), "a seal created a log");

    seed(&fx);
    let held = fx.plain().unwrap();
    let err = BrokerLog::seal_plaintext(&fx.path, KEY).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::AlreadyExists, "{err}");
    assert!(fx.leftovers().is_empty() && !fx.file(".seal").exists());
    drop(held);

    drop(fx.plain().unwrap());
    assert!(
        !closed_cleanly(&fx),
        "NC: the log is left open, as a killed broker leaves it"
    );
    std::fs::write(fx.file(".hw"), b"x").unwrap();
    let err = BrokerLog::seal_plaintext(&fx.path, KEY).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::Unsupported, "{err}");
    assert!(
        closed_cleanly(&fx),
        "a seal refused for `.hw` left the log open"
    );
    std::fs::remove_file(fx.file(".hw")).unwrap();

    drop(fx.plain().unwrap());
    std::fs::write(fx.file(".replica"), b"x").unwrap();
    let err = BrokerLog::seal_plaintext(&fx.path, KEY).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::Unsupported, "{err}");
    assert!(
        closed_cleanly(&fx),
        "a seal refused for a replica left the log open"
    );
    std::fs::remove_file(fx.file(".replica")).unwrap();
    assert!(fx.leftovers().is_empty() && !fx.file(".seal").exists());
    assert_eq!(sentinels(&fx), [true; 3], "a refused seal sealed something");
}

/// A marker an open cannot read names a switch it can neither finish nor undo: the open
/// refuses, naming it, and touches nothing.
#[test]
fn an_open_refuses_a_marker_it_cannot_read() {
    let fx = Fx::new("seal-marker");
    seed(&fx);
    let log_before = std::fs::read(&fx.path).unwrap();
    std::fs::write(fx.file(".sealmove"), b"not a marker").unwrap();
    let err = fx
        .plain()
        .err()
        .expect("an open read past a marker it cannot read");
    assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{err}");
    assert!(err.to_string().contains("bus.log.sealmove"), "{err}");
    assert_eq!(std::fs::read(&fx.path).unwrap(), log_before);
    assert!(fx.file(".sealmove").exists());
}

/// The seal with `alter` planted in its staged copy: a VALID seal of different content, so
/// only reading the copy back can tell. Record: the newest record's body; held: the held
/// mail's body; state: the pending will's body.
fn plant(fx: &Fx, alter: Alter) -> io::Error {
    let needle: &'static [u8] = match alter {
        Alter::Record => b"newest",
        Alter::Held => HELD_SENTINEL,
        Alter::State => STATE_SENTINEL,
    };
    let seam = Seam {
        crash_after: None,
        alter: Some((alter, needle)),
    };
    seal(&fx.path, KEY, &seam).expect_err("the altered copy was switched in")
}

/// A COPY THAT DOES NOT READ BACK IS NEVER SWITCHED IN: a record, a held frame or the carried
/// state altered in the staged copy (each sealed validly) refuses the seal by name, the
/// plaintext log untouched and readable, and the next open undoes the staging.
#[test]
fn a_copy_that_does_not_read_back_is_never_switched_in() {
    for alter in [Alter::Record, Alter::Held, Alter::State] {
        let fx = Fx::new("seal-alter");
        seed(&fx);
        let want = reference(&fx);
        let err = plant(&fx, alter);
        assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{alter:?}: {err}");
        assert!(
            err.to_string().contains("does not read back"),
            "{alter:?}: {err}"
        );
        assert!(!fx.file(".sealmove").exists(), "{alter:?}: a marker");
        assert_eq!(sentinels(&fx), [true; 3], "{alter:?}");
        reads_whole(&fx, false, &want, &format!("{alter:?}"));
        assert!(fx.leftovers().is_empty(), "{alter:?}: {:?}", fx.leftovers());
    }
}

/// Every step the seal takes on the seeded log, in order.
const STEPS: [Step; 12] = [
    Step::Staged,
    Step::Sidecars,
    Step::Verified,
    Step::Marker,
    Step::Moved(".seal"),
    Step::Moved(".base"),
    Step::Moved(".state"),
    Step::Moved(".held"),
    Step::Moved(".id"),
    Step::LogMoved,
    Step::Synced,
    Step::Done,
];

/// Whether the log is sealed once `step` is durable: from the marker on.
fn switched(step: Step) -> bool {
    !matches!(step, Step::Staged | Step::Sidecars | Step::Verified)
}

/// THE CRASH LAW: after a crash following any durable step of the seal, the process stopped
/// dead or the power gone (every directory `power_loss.rs` says can be left), the log is
/// WHOLLY plaintext (before the marker) or WHOLLY sealed (from it on), whichever open comes
/// first: a keyless open first either reads the plaintext log whole or, the switch finished
/// by it, refuses the sealed one; nothing of the seal's own is left after it; and the open
/// that fits then reads every record, the identity and the state as before, and the log
/// takes records. A plaintext log left so seals again.
#[test]
fn a_crash_after_any_durable_step_leaves_the_log_wholly_plaintext_or_wholly_sealed() {
    // Not vacuous: images that held a switch half done (the marker and a staged file), a
    // staging and no marker, and power losses at all.
    let (mut mid_switch, mut staged_only, mut power) = (0usize, 0usize, 0usize);
    for step in STEPS {
        let fx = Fx::new("seal-crash");
        seed(&fx);
        let want = reference(&fx);
        crate::power_loss::arm(fx.dir());
        let seam = Seam {
            crash_after: Some(step),
            alter: None,
        };
        let err = seal(&fx.path, KEY, &seam).expect_err("the armed crash");
        let lost = crate::power_loss::disarm()
            .expect("the power-loss model was armed")
            .images();
        assert!(
            err.to_string().contains("injected crash"),
            "{step:?}: {err}"
        );
        let stood = crate::power_loss::capture(fx.dir());
        let left = std::iter::once(("a process crash", stood))
            .chain(lost.into_iter().map(|image| ("a power loss", image)));
        let sealed = switched(step);
        for (i, (how, image)) in left.enumerate() {
            let at = format!("{step:?}, {how} (image {i})");
            let staging = image
                .keys()
                .any(|n| n.to_string_lossy().starts_with("bus.log.sealing"));
            let marked = image.contains_key(std::ffi::OsStr::new("bus.log.sealmove"));
            mid_switch += usize::from(marked && staging);
            staged_only += usize::from(!marked && staging);
            power += usize::from(how == "a power loss");
            crate::power_loss::apply(fx.dir(), &image);
            // The first open is keyless on even images, keyed and bound on odd ones: whichever
            // it is finishes or undoes the switch, then reads the log or refuses it.
            let first = if i % 2 == 0 { fx.plain() } else { fx.sealed() };
            match first {
                Ok(mut log) => {
                    assert_eq!(
                        i % 2 == 1,
                        sealed,
                        "{at}: the open that does not fit read it"
                    );
                    assert_eq!(&snap(&mut log), &want, "{at}: the first open");
                }
                Err(e) => {
                    assert_eq!(i % 2 == 0, sealed, "{at}: the open that fits refused: {e}");
                    assert_eq!(e.kind(), io::ErrorKind::InvalidData, "{at}: {e}");
                }
            }
            assert!(fx.leftovers().is_empty(), "{at}: left {:?}", fx.leftovers());
            assert_eq!(fx.file(".seal").exists(), sealed, "{at}: `.seal`");
            assert_eq!(
                sentinels(&fx),
                [!sealed; 3],
                "{at}: the sentinels (wholly one or the other)"
            );
            reads_whole(&fx, sealed, &want, &at);
            if !sealed {
                BrokerLog::seal_plaintext(&fx.path, KEY)
                    .unwrap_or_else(|e| panic!("{at}: the log left plaintext does not seal: {e}"));
                assert_eq!(sentinels(&fx), [false; 3], "{at}: sealed after");
            }
        }
    }
    eprintln!(
        "seal crash law: {power} power-loss images, {mid_switch} mid-switch, {staged_only} \
         staged without a marker"
    );
    assert!(
        power > 0 && mid_switch > 0 && staged_only > 0,
        "the crash law met no power loss, no half-done switch or no bare staging"
    );
}

/// What a build that does not settle (an older astream) does to a log it opens in the middle
/// of a switch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Older {
    /// It only opens the log and closes it.
    Reads,
    /// It acks a record.
    Acks,
    /// It sets other rules: a rules frame added to `.held`, the log file untouched.
    Rules,
}

/// Move the seal's own files (the staging and the marker), and a `.seal` the switch moved in
/// already, from `from` into `to`: what an older build's keyless open never looks at (it has
/// no settle, and no refusal of a log a `.seal` sits beside).
fn shelve(from: &Path, to: &Path) {
    for entry in std::fs::read_dir(from).unwrap().flatten() {
        let name = entry.file_name();
        let n = name.to_string_lossy();
        if n == "bus.log.seal"
            || n.starts_with("bus.log.sealing")
            || n.starts_with("bus.log.sealmove")
        {
            std::fs::rename(entry.path(), to.join(&name)).unwrap();
        }
    }
}

/// A SWITCH IS FINISHED ONLY OVER THE LOG ITS MARKER WAS WRITTEN FOR. A seal stopped in its
/// switch, then a build that does not settle opens the log (here, this build with the marker,
/// the staging and a `.seal` the switch moved in already out of its sight, as an older one
/// never looks): when it acked a record (the log's length differs) or added a rules frame to
/// `.held` (the log file the same, `.held` not), the next open, keyed or keyless, refuses
/// (InvalidData, naming the marker and what changed) and moves nothing, so the acked record
/// stays at its offset; when it only read the log (the control: the check does not refuse an
/// open that changed nothing), the next open finishes the switch and reads the log sealed,
/// whole.
#[test]
fn a_switch_is_never_finished_over_a_log_that_changed_after_its_marker() {
    for (step, older, what) in [
        (Step::Moved(".base"), Older::Acks, "the log's length"),
        (Step::Marker, Older::Acks, "the log's length"),
        (Step::Marker, Older::Rules, "`.held` has changed"),
        (Step::Moved(".base"), Older::Reads, ""),
    ] {
        let at = format!("{step:?}, {older:?}");
        let fx = Fx::new("seal-stale");
        seed(&fx);
        let want = reference(&fx);
        let seam = Seam {
            crash_after: Some(step),
            alter: None,
        };
        seal(&fx.path, KEY, &seam).expect_err("the armed crash");
        assert!(fx.file(".sealmove").exists(), "{at}: no marker");
        let aside = Scratch::new("seal-stale-aside");
        shelve(fx.dir(), aside.path());
        let mut log = fx
            .plain()
            .unwrap_or_else(|e| panic!("{at}: the older build's open: {e}"));
        match older {
            Older::Reads => {}
            Older::Acks => {
                log.publish(7, 777, EV.into(), b"OLDER-BUILD-ACKED".to_vec())
                    .unwrap();
            }
            Older::Rules => log
                .set_retention(
                    Retention::new(
                        vec![Rule::prefix(EV).unwrap().max_bytes(4_000)],
                        Rule::default_hold(),
                    )
                    .unwrap(),
                )
                .unwrap(),
        }
        log.close_clean().unwrap();
        drop(log);
        shelve(aside.path(), fx.dir());
        let before = crate::power_loss::capture(fx.dir());
        if older == Older::Reads {
            reads_whole(&fx, true, &want, &at);
            assert!(fx.leftovers().is_empty(), "{at}: {:?}", fx.leftovers());
            continue;
        }
        for (how, open) in [("keyed", fx.sealed()), ("keyless", fx.plain())] {
            let err = open
                .err()
                .unwrap_or_else(|| panic!("{at}: a {how} open finished a stale switch"));
            assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{at}, {how}: {err}");
            assert!(
                err.to_string().contains("bus.log.sealmove") && err.to_string().contains(what),
                "{at}, {how}: {err}"
            );
            assert!(
                crate::power_loss::capture(fx.dir()) == before,
                "{at}, {how}: the refusing open moved something"
            );
        }
        if older == Older::Acks {
            assert!(fx.holds("", b"OLDER-BUILD-ACKED"), "{at}: the acked record");
        }
    }
}

/// A RETRY OF A SEAL A CRASH STOPPED PAST ITS MARKER says the log is sealed already
/// (InvalidInput), wherever in the switch the crash fell, and leaves it sealed whole.
#[test]
fn a_retried_seal_past_its_marker_says_sealed_already() {
    for step in STEPS.into_iter().filter(|s| switched(*s)) {
        let at = format!("{step:?}");
        let fx = Fx::new("seal-retry");
        seed(&fx);
        let want = reference(&fx);
        let seam = Seam {
            crash_after: Some(step),
            alter: None,
        };
        seal(&fx.path, KEY, &seam).expect_err("the armed crash");
        let err = BrokerLog::seal_plaintext(&fx.path, KEY).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput, "{at}: {err}");
        assert!(err.to_string().contains("sealed already"), "{at}: {err}");
        assert!(fx.leftovers().is_empty(), "{at}: {:?}", fx.leftovers());
        reads_whole(&fx, true, &want, &at);
    }
}

/// AN OPEN THAT FINISHES A SWITCH KEEPS THE LOG'S NAME LOCKED THROUGHOUT: the settle locks the
/// staged log before it renames it over the name and hands it back locked, so no other open
/// can take the name between the rename and the open's own hold on the sealed log.
#[test]
fn a_finished_switch_hands_back_the_sealed_log_locked() {
    let fx = Fx::new("seal-lock");
    seed(&fx);
    let seam = Seam {
        crash_after: Some(Step::Marker),
        alter: None,
    };
    seal(&fx.path, KEY, &seam).expect_err("the armed crash");
    let held = settle(&fx.path).unwrap();
    assert!(fx.leftovers().is_empty(), "{:?}", fx.leftovers());
    let other = std::fs::File::open(&fx.path).unwrap();
    assert!(
        matches!(other.try_lock(), Err(std::fs::TryLockError::WouldBlock)),
        "the name was free between the switch and the open's hold on the sealed log"
    );
    drop(held);
    other.try_lock().unwrap();
}

/// A sealed log with one record and a `.held` and no `.state`, the store's first frame resealed
/// until its nonce reads, keyless, as rules cut above the base. Answers the store's bytes.
fn held_that_reads_as_a_cut(fx: &Fx) -> Vec<u8> {
    {
        let mut log = fx.sealed().unwrap();
        log.set_retention(rules()).unwrap();
        log.publish(7, 1, EV.into(), LOG_SENTINEL.to_vec()).unwrap();
        assert_eq!(log.base().0, 0);
    }
    assert!(fx.file(".seal").exists() && fx.file(".held").exists());
    assert!(!fx.file(".state").exists(), "no carrying compaction yet");
    let id = read_seal(&fx.path, &KEY).unwrap().expect("a bound log");
    let kref = Some(AtRestRef {
        key: &KEY,
        seal_id: Some(id),
    });
    let frames = payloads(&std::fs::read(fx.file(".held")).unwrap()).expect("whole frames");
    let rules_frame = crate::held::unseal(kref, 0, frames[0].clone()).expect("the rules");
    let reads_as_a_cut = |s: &Vec<u8>| {
        s.first() == Some(&b'R')
            && s.get(1..9)
                .and_then(|b| <[u8; 8]>::try_from(b).ok())
                .is_some_and(|b| u64::from_le_bytes(b) > 0)
    };
    let first = (0..1u32 << 16)
        .map(|_| crate::held::seal(kref, 0, &rules_frame))
        .find(reads_as_a_cut)
        .expect("a nonce that reads as rules cut above the base");
    let mut held = framed(first, "held").unwrap();
    for p in &frames[1..] {
        held.extend_from_slice(&framed(p.clone(), "held").unwrap());
    }
    std::fs::write(fx.file(".held"), &held).unwrap();
    held
}

/// A SEALED LOG WHOSE `.seal` IS GONE KEEPS ITS `.held` THROUGH EVERY KEYLESS WAY IN. The open
/// cannot tell it is sealed before the log's scan, and the store's read that came first found
/// the same nonce reading as a cut (about one sealed `.held` in 256): the cut waits until nothing
/// refuses the open, and the scan refuses this one. A keyless open, a keyless repair and a seal
/// each refuse, `.held` byte for byte, and with `.seal` back the key reads the log whole. The same
/// path covers a v1 log, which never had a `.seal`. Seen failing before the wait: `.held` cut to
/// nothing by each of the three.
#[test]
fn a_sealed_log_whose_seal_is_gone_keeps_its_held_through_every_keyless_way_in() {
    let fx = Fx::new("no-seal-held");
    let held = held_that_reads_as_a_cut(&fx);
    let seal = std::fs::read(fx.file(".seal")).unwrap();
    std::fs::remove_file(fx.file(".seal")).unwrap();
    let untouched = |way: &str, refused: io::Error| {
        assert_eq!(
            std::fs::read(fx.file(".held")).unwrap(),
            held,
            "{way} changed `.held`"
        );
        assert_eq!(
            refused.kind(),
            io::ErrorKind::InvalidData,
            "{way}: {refused}"
        );
    };
    untouched("a keyless open", fx.plain().err().expect("it opens"));
    untouched(
        "a keyless repair",
        BrokerLog::open_repair(&fx.path, Durability::Strict)
            .err()
            .expect("it repairs"),
    );
    untouched(
        "a seal",
        BrokerLog::seal_plaintext(&fx.path, KEY).expect_err("it seals"),
    );
    std::fs::write(fx.file(".seal"), seal).unwrap();
    let log = fx.sealed().unwrap();
    assert_eq!(log.read_from(Offset(0))[0].body, LOG_SENTINEL);
}

/// A KEYLESS OPEN OF A SEALED LOG REFUSES BEFORE IT READS `.held`, and leaves it as it
/// was. Read without the key, a sealed frame is its nonce first: a `.held` whose first frame's
/// nonce starts with the rules kind, the next eight bytes a cut above the base, reads as rules
/// that a compaction never landed, and the held store's load (`held.rs`) truncates the file
/// to nothing, before the log's scan would refuse the open. That is about one sealed `.held`
/// in 256, before a log's first carrying compaction (no `.state`, whose keyless read refuses
/// first). The test reseals the store's first frame until its nonce is that one, so the
/// hazard is there every run. Seen failing before the open's check: `.held` cut to nothing.
#[test]
fn a_keyless_open_of_a_sealed_log_refuses_before_it_reads_held() {
    let fx = Fx::new("keyless-held");
    let held = held_that_reads_as_a_cut(&fx);

    let err = fx
        .plain()
        .err()
        .expect("a keyless open read the sealed log");
    assert_eq!(
        std::fs::read(fx.file(".held")).unwrap(),
        held,
        "the keyless open changed `.held`"
    );
    assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{err}");
    assert!(err.to_string().contains(".seal"), "{err}");
    // The resealed store is a sealed store: the keyed open reads it, rules and record whole.
    let log = fx.sealed().unwrap();
    assert_eq!(log.head().0, 1);
    assert_eq!(log.read_from(Offset(0))[0].body, LOG_SENTINEL);
}

/// A `.seal` LEFT BY A DELETED LOG SEALS NOTHING: a keyless open that creates the log clears
/// it, as it clears the deleted log's other sidecars, so the plaintext log it creates is not
/// taken for a sealed one at its next open, and can be sealed. Seen failing before the clear:
/// the second keyless open refused its own plaintext log. Beside an anti-rollback watermark
/// the `.seal` stays (a verified open reads the pair to refuse the deleted log), and the
/// keyless open that reopens the log refuses.
#[test]
fn a_keyless_create_clears_the_seal_a_deleted_log_left() {
    let fx = Fx::new("stale-seal");
    {
        let mut log = fx.sealed().unwrap();
        log.publish(7, 1, EV.into(), LOG_SENTINEL.to_vec()).unwrap();
    }
    std::fs::remove_file(&fx.path).unwrap();
    assert!(fx.file(".seal").exists());
    {
        let mut log = fx.plain().unwrap();
        log.publish(7, 1, EV.into(), LOG_SENTINEL.to_vec()).unwrap();
        log.close_clean().unwrap();
    }
    assert!(
        !fx.file(".seal").exists(),
        "the deleted log's `.seal` stayed"
    );
    {
        let mut log = fx
            .plain()
            .expect("a keyless open refused its own plaintext log");
        assert_eq!(log.read_from(Offset(0))[0].body, LOG_SENTINEL);
        log.close_clean().unwrap();
    }
    BrokerLog::seal_plaintext(&fx.path, KEY).expect("it seals");

    let fx = Fx::new("stale-seal-hw");
    drop(fx.sealed().unwrap());
    let seal = std::fs::read(fx.file(".seal")).unwrap();
    std::fs::write(fx.file(".hw"), b"a watermark").unwrap();
    std::fs::remove_file(&fx.path).unwrap();
    drop(fx.plain().unwrap());
    assert_eq!(std::fs::read(fx.file(".seal")).unwrap(), seal);
    let err = fx.plain().err().expect("it reopened beside a watermark");
    assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{err}");
}
