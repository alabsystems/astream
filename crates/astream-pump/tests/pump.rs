//! Claim `pump.wake-on-boundaries`: the pump, subscribed to a target session's
//! `/out` subtree on a live in-process broker, classifies the delivered session
//! into the semantic wake boundaries a driving agent acts on — prompt-ready,
//! command-start, command-end (+exit), quiescence — proving the composition
//! `broker SUBSCRIBE -> fold -> classify -> wake` end to end. Each delivery is
//! asserted on its own (the wake surfaces on the delivery that carries it, not
//! batched into quiesce), with the broker offset it was delivered at; and the
//! resume contract (attach from `next_offset()`, never from `offset()`) is
//! checked over the real bus.
//!
//! And claim `pump.attach-subject-and-group` (`DESIGN-aterm-fabric.md` §12 R10):
//! `attach_subject` on a fabric node's `/f/F/term/n1/s1/out` face yields exactly
//! the wake lines `attach` yields on the built `/a/stream/term/s1/out`, and a
//! record on another subject of the same log is never delivered to it; while
//! `attach_group` puts the cursor on the broker — a replacement pump given no
//! offset at all resumes at `committed + 1` and, joined with its predecessor,
//! reproduces the uninterrupted pump's wakes exactly.
//!
//! Fully in-process, std-only, NO sleeps: the producer blocks for each publish
//! ack and the pump blocks for an exact, known number of deliveries.
#![cfg(unix)]

use astream_broker::{Broker, BrokerHandle, Client};
use astream_pump::{out_subject, wake_line, Pump};
use astream_term::events::{Profile, SessionEvent};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
struct Cleanup(Vec<std::path::PathBuf>);

impl Cleanup {
    fn new<P: AsRef<std::path::Path>>(paths: &[P]) -> Cleanup {
        Cleanup(paths.iter().map(|p| p.as_ref().to_path_buf()).collect())
    }
}

impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            remove_with_sidecars(path);
        }
    }
}

/// Remove `path` and every `<path>.*` sidecar in its directory.
fn remove_with_sidecars(path: impl AsRef<std::path::Path>) {
    let path = path.as_ref();
    let _ = std::fs::remove_file(path);
    let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
        return;
    };
    let prefix = format!("{}.", name.to_string_lossy());
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        if entry.file_name().to_string_lossy().starts_with(&prefix) {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}

fn fresh(tag: &str) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/asp_{pid}_{tag}_{n}.sock");
    let log = format!("/tmp/asp_{pid}_{tag}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&sock, &log]);
    let broker = Broker::open(&log).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock)
}

// A realistic OSC-133 command cycle, as raw Out payloads.
fn session() -> Vec<&'static [u8]> {
    vec![
        b"\x1b[2J\x1b[H",
        b"\x1b]133;A\x07user@host % ",
        b"echo hi\r\n",
        b"\x1b]133;C\x07",
        b"hi\r\n",
        b"\x1b]133;D;0\x07",
        b"\x1b]133;A\x07user@host % ",
    ]
}

// Publish the session to `subj` on a fresh log; the records land at broker
// offsets 0..=6, which the assertions below rely on.
fn publish_session(sock: &str, subj: &str) {
    let mut prod = Client::connect(sock).unwrap();
    for (i, body) in session().iter().enumerate() {
        let (off, dup) = prod.publish(1, i as u64, subj, body).unwrap();
        assert_eq!((off, dup), (i as u64, false), "fixture offsets are 0..=6");
    }
}

#[test]
fn pump_classifies_a_live_broker_session_into_wake_events() {
    let (_tmp, _b, _h, sock) = fresh("wake");
    let sid = "s1";
    publish_session(&sock, &out_subject(sid));

    // The pump attaches from offset 0 and classifies the delivered stream.
    let client = Client::connect(&sock).unwrap();
    let mut pump = Pump::attach(client, sid, 0, 80, 24, Profile::common()).unwrap();
    // Nothing delivered yet: both offsets are the attach point.
    assert_eq!((pump.offset(), pump.next_offset()), (0, 0));

    // Per delivery: the wake surfaces on the delivery that carries it — an OSC
    // mark fires from `next_wake`, never deferred to `quiesce` — and the pump's
    // offset is that delivery's broker offset.
    let expected: Vec<(u64, Vec<SessionEvent>)> = vec![
        (0, vec![]),
        (1, vec![SessionEvent::PromptReady { offset: 1 }]),
        (2, vec![]),
        (3, vec![SessionEvent::CommandStart { offset: 3 }]),
        (4, vec![]),
        (
            5,
            vec![SessionEvent::CommandEnd {
                offset: 5,
                exit: Some(0),
            }],
        ),
        (6, vec![SessionEvent::PromptReady { offset: 6 }]),
    ];
    for (boffset, events) in expected {
        let got = pump
            .next_wake()
            .unwrap()
            .expect("a delivery, not end of stream");
        assert_eq!(got, events, "wake events of delivery {boffset}");
        assert_eq!(
            pump.offset(),
            boffset,
            "the broker offset a woken agent reads at"
        );
        assert_eq!(pump.next_offset(), boffset + 1);
    }

    // The debounce boundary: the screen settled at the last prompt. No glyph
    // PromptReady — the session is integrated, its A mark already fired.
    assert_eq!(
        pump.quiesce(),
        vec![SessionEvent::Quiesced { offset: 6 }],
        "quiesce surfaces only the settle event"
    );
}

#[test]
fn pump_resumes_from_next_offset_without_re_delivery() {
    let (_tmp, _b, _h, sock) = fresh("resume");
    let sid = "s2";
    let subj = out_subject(sid);
    publish_session(&sock, &subj);

    // Pump A drains the whole session, then stops (a bridge restart).
    let mut a = Pump::attach(
        Client::connect(&sock).unwrap(),
        sid,
        0,
        80,
        24,
        Profile::common(),
    )
    .unwrap();
    for _ in 0..7 {
        a.next_wake().unwrap().unwrap();
    }
    assert_eq!((a.offset(), a.next_offset()), (6, 7));

    // Meanwhile the target prints one more prompt: broker offset 7.
    let mut prod = Client::connect(&sock).unwrap();
    let (off, _) = prod
        .publish(2, 0, &subj, b"\x1b]133;A\x07user@host % ")
        .unwrap();
    assert_eq!(off, 7);

    // Pump B resumes at A's next_offset(): its FIRST delivery is the new record
    // — nothing re-delivered, nothing skipped. The event's offset is B's own
    // record index (0: first delivery since attach); the broker offset is 7.
    let mut b = Pump::attach(
        Client::connect(&sock).unwrap(),
        sid,
        a.next_offset(),
        80,
        24,
        Profile::common(),
    )
    .unwrap();
    assert_eq!(
        (b.offset(), b.next_offset()),
        (7, 7),
        "attach point until delivered"
    );
    assert_eq!(
        b.next_wake().unwrap().unwrap(),
        vec![SessionEvent::PromptReady { offset: 0 }]
    );
    assert_eq!((b.offset(), b.next_offset()), (7, 8));

    // Attaching AT offset() instead (the off-by-one the contract warns about)
    // delivers record 6 — A's last wake — a second time: `from_offset` is inclusive.
    let mut c = Pump::attach(
        Client::connect(&sock).unwrap(),
        sid,
        a.offset(),
        80,
        24,
        Profile::common(),
    )
    .unwrap();
    assert_eq!(
        c.next_wake().unwrap().unwrap(),
        vec![SessionEvent::PromptReady { offset: 0 }]
    );
    assert_eq!(c.offset(), 6, "from_offset is inclusive: record 6 again");
}

// ---------------------------------------------------------------------------
// Claim `pump.attach-subject-and-group` (DESIGN-aterm-fabric.md §12 R10).
// ---------------------------------------------------------------------------

/// A fabric node's PTY face (`DESIGN-aterm-fabric.md` §3.3) — a subject the
/// built `out_subject` shape knows nothing about.
const FABRIC_SUBJECT: &str = "/f/F/term/n1/s1/out";

/// The consumer-group name is itself a subject under the fabric's `cur` face, so
/// a capability can grant it (§3.3).
const FABRIC_GROUP: &str = "/f/F/cur/n1/pump";

// The wake lines of the fixture published at offsets 0..=6, as `aspump` prints
// them. Named so an equality between two pumps cannot pass vacuously on two
// empty vectors.
fn fixture_wake_lines() -> Vec<String> {
    [
        "PROMPT_READY boffset=1",
        "COMMAND_START boffset=3",
        "COMMAND_END boffset=5 exit=0",
        "PROMPT_READY boffset=6",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect()
}

// Drain exactly `n` deliveries, returning the wake lines they produced (each
// tagged with the broker offset of the delivery that carried it) and the broker
// offsets delivered, in order.
fn drain<S: std::io::Read + std::io::Write>(
    pump: &mut Pump<S>,
    n: usize,
) -> (Vec<String>, Vec<u64>) {
    let (mut lines, mut offsets) = (Vec::new(), Vec::new());
    for _ in 0..n {
        let evs = pump
            .next_wake()
            .unwrap()
            .expect("a delivery, not end of stream");
        offsets.push(pump.offset());
        lines.extend(evs.iter().map(|e| wake_line(e, pump.offset())));
    }
    (lines, offsets)
}

#[test]
fn attach_subject_on_a_fabric_subject_wakes_exactly_like_attach_on_the_built_one() {
    // Two logs, so the same fixture lands at the same offsets 0..=6 on each and
    // the `boffset=` in every wake line is comparable.
    let (_tmp1, _b1, _h1, built_sock) = fresh("subj_built");
    let (_tmp2, _b2, _h2, fabric_sock) = fresh("subj_fabric");
    publish_session(&built_sock, &out_subject("s1"));
    publish_session(&fabric_sock, FABRIC_SUBJECT);

    let mut built = Pump::attach(
        Client::connect(&built_sock).unwrap(),
        "s1",
        0,
        80,
        24,
        Profile::common(),
    )
    .unwrap();
    let mut fabric = Pump::attach_subject(
        Client::connect(&fabric_sock).unwrap(),
        FABRIC_SUBJECT,
        0,
        80,
        24,
        Profile::common(),
    )
    .unwrap();

    let (built_lines, built_offsets) = drain(&mut built, 7);
    let (fabric_lines, fabric_offsets) = drain(&mut fabric, 7);
    assert_eq!(
        built_lines,
        fixture_wake_lines(),
        "the built face's wake lines are the fixture's"
    );
    assert_eq!(
        fabric_lines, built_lines,
        "an arbitrary subject wakes identically to the built /a/stream/term/<sid>/out"
    );
    assert_eq!(fabric_offsets, built_offsets, "and at the same offsets");
    assert_eq!(built.quiesce(), fabric.quiesce(), "settle boundary too");
    // This form has no durable cursor, and says so rather than silently doing
    // nothing when asked to commit.
    assert_eq!(fabric.group(), None);
    assert_eq!(
        fabric.commit().unwrap_err().kind(),
        std::io::ErrorKind::Unsupported,
        "attach_subject holds its cursor in the pump process"
    );

    // Routing, not prefix-blindness: a record on the BUILT subject of the same
    // log is not delivered to the fabric pump. Offset 7 is the decoy, 8 the next
    // fabric record — so the fabric pump's next delivery is 8, not 7.
    let mut prod = Client::connect(&fabric_sock).unwrap();
    let (decoy, _) = prod
        .publish(9, 0, &out_subject("s1"), b"\x1b]133;A\x07decoy % ")
        .unwrap();
    let (next, _) = prod
        .publish(9, 1, FABRIC_SUBJECT, b"\x1b]133;C\x07")
        .unwrap();
    assert_eq!((decoy, next), (7, 8), "fixture offsets");
    fabric.next_wake().unwrap().unwrap();
    assert_eq!(
        fabric.offset(),
        8,
        "the decoy on another subject was never delivered"
    );
}

#[test]
fn attach_group_resumes_from_the_durable_commit_across_a_pump_restart() {
    let (_tmp, _b, _h, sock) = fresh("group");
    publish_session(&sock, FABRIC_SUBJECT); // offsets 0..=6

    // The reference: one uninterrupted client-cursor pump over the whole session.
    let mut reference = Pump::attach_subject(
        Client::connect(&sock).unwrap(),
        FABRIC_SUBJECT,
        0,
        80,
        24,
        Profile::common(),
    )
    .unwrap();
    let (reference_lines, reference_offsets) = drain(&mut reference, 7);
    assert_eq!(reference_lines, fixture_wake_lines());
    drop(reference);

    // Pump A: the durable form. It is given NO offset — the broker holds the
    // cursor — and a group that has never committed starts at 0.
    let mut a = Pump::attach_group(
        Client::connect(&sock).unwrap(),
        Client::connect(&sock).unwrap(),
        FABRIC_GROUP,
        FABRIC_SUBJECT,
        80,
        24,
        Profile::common(),
    )
    .unwrap();
    assert_eq!(a.group(), Some(FABRIC_GROUP));
    assert_eq!(a.committed(), None, "nothing committed yet");
    assert_eq!(
        a.commit().unwrap(),
        None,
        "nothing delivered: there is no record to commit"
    );

    // It acts on four deliveries, then commits through the last of them.
    let (a_lines, a_offsets) = drain(&mut a, 4);
    assert_eq!(a_offsets, vec![0, 1, 2, 3]);
    assert_eq!(a.commit().unwrap(), Some(3), "committed THROUGH offset 3");
    assert_eq!(a.committed(), Some(3));
    // Committing again with nothing new delivered reports the same cursor and
    // appends no second commit record (the broker's head does not move).
    let mut probe = Client::connect(&sock).unwrap();
    let head = |c: &mut Client<_>| c.fetch(0, "/a/>", 0).unwrap().1 .1;
    let before = head(&mut probe);
    assert_eq!(
        a.commit().unwrap(),
        Some(3),
        "a repeated commit is the same cursor"
    );
    assert_eq!(head(&mut probe), before, "and appends nothing");
    // The two cursor contracts agree: the group's next start is exactly the
    // offset the client-cursor form would have to be handed explicitly.
    assert_eq!(a.next_offset(), 4);
    drop(a); // the pump dies — the cursor does not

    // Pump B: a fresh pump with no knowledge of A's offsets at all.
    let mut b = Pump::attach_group(
        Client::connect(&sock).unwrap(),
        Client::connect(&sock).unwrap(),
        FABRIC_GROUP,
        FABRIC_SUBJECT,
        80,
        24,
        Profile::common(),
    )
    .unwrap();
    let (b_lines, b_offsets) = drain(&mut b, 3);
    assert_eq!(
        b_offsets,
        vec![4, 5, 6],
        "resumed at committed+1, and the /a/commit record is never delivered"
    );

    // No gap and no duplicate: the restarted pair saw exactly what one
    // uninterrupted pump saw, in order, at the same offsets.
    let joined_lines: Vec<String> = a_lines.iter().chain(&b_lines).cloned().collect();
    let joined_offsets: Vec<u64> = a_offsets.iter().chain(&b_offsets).copied().collect();
    assert_eq!(
        joined_lines, reference_lines,
        "same wakes across the restart"
    );
    assert_eq!(joined_offsets, reference_offsets);

    // And the cursor keeps moving: after B commits through 6, a third pump on the
    // group is delivered only what was published after it.
    assert_eq!(b.commit().unwrap(), Some(6));
    drop(b);
    let mut prod = Client::connect(&sock).unwrap();
    let (fresh_offset, _) = prod
        .publish(3, 0, FABRIC_SUBJECT, b"\x1b]133;C\x07")
        .unwrap();
    assert!(
        fresh_offset > 6,
        "the two commit records took offsets 7 and 8"
    );
    let mut c = Pump::attach_group(
        Client::connect(&sock).unwrap(),
        Client::connect(&sock).unwrap(),
        FABRIC_GROUP,
        FABRIC_SUBJECT,
        80,
        24,
        Profile::common(),
    )
    .unwrap();
    assert_eq!(
        c.next_wake().unwrap().unwrap(),
        vec![SessionEvent::CommandStart { offset: 0 }]
    );
    assert_eq!(
        c.offset(),
        fresh_offset,
        "nothing already committed was re-delivered"
    );
}
