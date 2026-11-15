// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! [`astream_sys::flush_tally`] moves by EXACTLY the calls made, each in its own kind
//! and no other, and [`astream_sys::flush_times`] by exactly their time. The tally is
//! process-wide and the library's own tests flush concurrently, so there a count can only
//! be bounded from below; this binary holds one test, so nothing else flushes through
//! astream-sys while it reads, and every reading is exact. A call counted in a second kind
//! as well as its own (a `plain_fsync` that also raised `full`) fails here, which no bound
//! can catch, and so does a flush that skips the timing: its kind's total must move, by no
//! more than the span the test read around the call, every other kind's must not, and the
//! ring must gain that one flush exactly when its time is past `SLOW_FLUSH_NS` (one more
//! slow flush counted, its kind, the next index, its start and end inside the test's span,
//! its length the total's move), and nothing otherwise; the readings around it count no call
//! running, so a door that never counts a call's return fails here too.
//!
//! NEGATIVE CONTROL: the same file flushed through `File::sync_all` and
//! `File::sync_data` directly leaves the tally, the totals and the ring where they were:
//! they count and time calls into astream-sys, and only those.

use astream_sys::{
    barrier_sync, clock_ns, flush_tally, flush_times, full_sync, full_sync_data, FlushKind,
    FlushTally, FlushTimes, SlowFlush, SLOW_FLUSH_NS,
};
use std::fs::File;
use std::io::Write;

/// The tally's move from `before` to `after`, as (full, barrier, plain).
fn moved(before: FlushTally, after: FlushTally) -> (u64, u64, u64) {
    (
        after.full - before.full,
        after.barrier - before.barrier,
        after.plain - before.plain,
    )
}

/// The slow flushes `after` holds that `before` did not.
fn gained(before: &FlushTimes, after: &FlushTimes) -> Vec<SlowFlush> {
    after
        .slow
        .iter()
        .filter(|f| !before.slow.contains(f))
        .copied()
        .collect()
}

/// One call of `flush`, a `kind` flush (`None`: no call here), read around: its tally moves
/// by exactly one in its kind, its kind's total by its time and no other's, and the ring
/// gains it exactly when it was slow.
fn check_one(what: &str, kind: Option<FlushKind>, flush: &dyn Fn() -> std::io::Result<()>) {
    let (count, times, opened) = (flush_tally(), flush_times(), clock_ns());
    let answer = flush();
    let closed = clock_ns();
    let (count_after, times_after) = (flush_tally(), flush_times());
    if let Err(e) = &answer {
        // Only a barrier the device refuses may fail: counted and timed all the same.
        assert!(
            kind == Some(FlushKind::Barrier) && astream_sys::barrier_refused(e),
            "{what}: {e}"
        );
    }
    let want = match kind {
        Some(FlushKind::Full) => (1, 0, 0),
        Some(FlushKind::Barrier) => (0, 1, 0),
        Some(FlushKind::Plain) => (0, 0, 1),
        None => (0, 0, 0),
    };
    assert_eq!(moved(count, count_after), want, "{what}: the tally");
    assert_eq!(
        (times.running, times_after.running),
        (0, 0),
        "{what}: no call runs before it or once it has returned"
    );
    let new = gained(&times, &times_after);
    let slow_counted = times_after.slow_count - times.slow_count;
    for k in FlushKind::ALL {
        let ns = times_after.total_ns(k) - times.total_ns(k);
        if Some(k) != kind {
            assert_eq!(ns, 0, "{what}: timed as {} too", k.word());
            continue;
        }
        assert!(ns > 0, "{what}: a flush that skipped its timing");
        assert!(
            ns <= closed - opened,
            "{what}: {ns} ns timed inside a span of {} ns",
            closed - opened
        );
        let slow = ns > SLOW_FLUSH_NS;
        assert_eq!(
            slow_counted,
            u64::from(slow),
            "{what}: {ns} ns is {}a slow flush",
            if slow { "" } else { "not " }
        );
        if slow {
            assert_eq!(
                new.len(),
                1,
                "{what}: the ring gains the one flush: {new:?}"
            );
            let f = new[0];
            assert_eq!(f.kind, k, "{what}");
            assert_eq!(
                f.index, times.slow_count,
                "{what}: the next index, the reading before's count"
            );
            assert_eq!(
                times_after.missed(times.slow_count),
                0,
                "{what}: the window, whole"
            );
            assert_eq!(f.ns(), ns, "{what}: the ring's span is the total's move");
            assert!(
                opened <= f.start_ns && f.end_ns <= closed,
                "{what}: {f:?} outside the span {opened}..{closed}"
            );
        } else {
            assert!(new.is_empty(), "{what}: a fast flush in the ring: {new:?}");
        }
    }
    if kind.is_none() {
        assert!(
            new.is_empty(),
            "{what}: no call here, no slow flush: {new:?}"
        );
        assert_eq!(slow_counted, 0, "{what}");
    }
}

#[test]
fn each_flush_moves_its_own_kind_by_one_and_no_other() {
    let dir = std::env::temp_dir().join(format!("astream-sys-tally-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut f = File::create(dir.join("tally")).unwrap();
    f.write_all(b"counted").unwrap();

    let full = Some(FlushKind::Full);
    check_one("full_sync", full, &|| full_sync(&f));
    check_one("full_sync_data", full, &|| full_sync_data(&f));
    check_one("barrier_sync", Some(FlushKind::Barrier), &|| {
        barrier_sync(&f)
    });
    #[cfg(unix)]
    check_one("plain_fsync", Some(FlushKind::Plain), &|| {
        astream_sys::plain_fsync(&f)
    });
    // A directory held as a bare descriptor, as aterm's handle-relative trees hold one.
    #[cfg(unix)]
    {
        let folder = std::os::fd::OwnedFd::from(File::open(&dir).unwrap());
        check_one(
            "plain_fsync of a directory's descriptor",
            Some(FlushKind::Plain),
            &|| astream_sys::plain_fsync(&folder),
        );
    }

    // NEGATIVE CONTROL: std's own flushes are no call here.
    check_one("File::sync_all", None, &|| f.sync_all());
    check_one("File::sync_data", None, &|| f.sync_data());

    // A barrier the device refuses is one barrier all the same, and nothing else.
    #[cfg(target_vendor = "apple")]
    {
        let null = File::open("/dev/null").unwrap();
        let refused = barrier_sync(&null);
        assert!(
            refused.as_ref().is_err_and(astream_sys::barrier_refused),
            "devfs takes no barrier: {refused:?}"
        );
        check_one("a refused barrier", Some(FlushKind::Barrier), &|| {
            barrier_sync(&null)
        });
    }
    drop(f);
    let _ = std::fs::remove_dir_all(&dir);
}
