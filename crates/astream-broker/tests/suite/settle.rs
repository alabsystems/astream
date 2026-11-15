// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `broker.settle`: a broker names its log's DEVICE in the answer to every
//! `Hello` (the extension block's tag 0x06, `Client::log_device`) and SETTLES it on request
//! (`Request::Settle`, `Client::settle` / `send_settle`): a full flush its writer issues
//! after it read the request, whatever already covers the head, answered with the durable
//! head after it. That is what lets a writer outside the log, whose own file is on that
//! device, order its writes by a barrier and know them on stable media by the broker's
//! flush instead of draining the device again with one of its own.
//!
//! What is asserted is what the broker counts and answers over a real socket: the device
//! it names is the log file's `st_dev`, the drain flag is the platform's (`F_FULLFSYNC` on
//! Apple), and every settle is one more full flush in `Broker::flush_counts` with none
//! skipped, where `Broker::flush_durable` on the same clean log is skipped (the control).

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{
    Broker, Client, Durability, LogDevice, OpenOptions, Prepared, REQUEST_SETTLE,
};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it.
struct Cleanup(Vec<String>);

impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            let path = std::path::Path::new(path);
            let _ = std::fs::remove_file(path);
            let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
                continue;
            };
            let prefix = format!("{}.", name.to_string_lossy());
            for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
                if entry.file_name().to_string_lossy().starts_with(&prefix) {
                    let _ = std::fs::remove_file(entry.path());
                }
            }
        }
    }
}

/// A fresh log and socket path, and their cleanup.
fn paths(tag: &str) -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asst_{tag}_{pid}_{n}.log");
    let sock = format!("/tmp/asst_{tag}_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    (Cleanup(vec![log.clone(), sock.clone()]), log, sock)
}

/// THE DEVICE IS THE LOG FILE'S, AND A SETTLE IS NEVER SKIPPED. On Relaxed (no horizon,
/// no escalation: nothing but a request flushes the log in full):
///
/// - `Hello` announces the settle (bit 8 of the request set) and names the device the log
///   file is on, its `st_dev` as `fstat` reads it here, draining it exactly on Apple;
/// - a settle behind a publish is one full flush, answered with the durable head past
///   that record;
/// - a settle on a log a full flush already covers is one more, none skipped, answered
///   with the same head;
/// - pipelined behind a publish on one connection, in send order: the publish's ack, then
///   the settle's, whose durable head covers the publish;
/// - the CONTROL: `flush_durable` on the same clean log is skipped, and counted so, with
///   no full flush, so what the settle counts is its own.
#[test]
fn a_settle_drains_the_device_after_the_request_whatever_covers_the_head() {
    use std::os::unix::fs::MetadataExt as _;
    let (_tmp, log, sock) = paths("never-skipped");
    let b = Broker::open_opts(&log, OpenOptions::new(Durability::Relaxed), || {
        Ok(Prepared::Nothing)
    })
    .unwrap();
    let _h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.log_identity().unwrap();
    assert!(c.supports_settle(), "the request set announces the settle");
    assert_eq!(REQUEST_SETTLE, 1 << 8);
    let dev = std::fs::metadata(&log).unwrap().dev();
    assert_eq!(
        c.log_device(),
        Some(LogDevice {
            dev,
            flush_drains_device: cfg!(target_vendor = "apple"),
        }),
        "the device is the log file's, and its full flush drains it on Apple"
    );
    assert_eq!(
        c.log_device().map(|d| d.settles(dev)),
        Some(cfg!(target_vendor = "apple"))
    );

    c.publish(1, 1, "/o/a", b"a write the settle covers")
        .unwrap();
    let before = b.flush_counts();
    assert_eq!(
        c.settle().unwrap(),
        1,
        "the durable head is past the record"
    );
    let after = b.flush_counts();
    assert_eq!(
        (after.full, after.skipped),
        (before.full + 1, before.skipped)
    );

    assert_eq!(c.settle().unwrap(), 1, "the head is unchanged");
    let again = b.flush_counts();
    assert_eq!(
        (again.full, again.skipped),
        (after.full + 1, after.skipped),
        "a clean log's settle is a full flush too, never skipped"
    );

    c.send_publish(1, 2, "/o/a", b"pipelined").unwrap();
    c.send_settle().unwrap();
    assert_eq!(c.owed_acks(), 2);
    assert_eq!(c.recv_publish_ack().unwrap(), (1, false));
    assert_eq!(
        c.recv_publish_ack().unwrap(),
        (2, false),
        "the settle's answer covers the publish sent ahead of it"
    );
    let pipelined = b.flush_counts();
    assert_eq!(pipelined.full, again.full + 1);

    // The control: the embedder's flush, which covers what is there, skips a clean log.
    assert_eq!(b.flush_durable().unwrap(), 2);
    let control = b.flush_counts();
    assert_eq!(
        (control.full, control.skipped),
        (pipelined.full, pipelined.skipped + 1),
        "flush_durable on a covered head is skipped"
    );
    assert_eq!(b.durable_head(), 2);
}

/// ON A GUARDED BROKER A SETTLE NEEDS A READ-WRITE GRANT: it spends the device's time, as a
/// write does. A ring holding only a read grant is refused where the ack would be, which
/// pays it and keeps the connection in step; the same ask on a connection whose ring holds a
/// read-write grant of another subtree is answered (any filter will do: a settle names
/// nothing). With no attach at all it is refused too.
#[cfg(feature = "cap")]
#[test]
fn a_guarded_broker_settles_for_a_read_write_grant_alone() {
    const SECRET: &[u8] = b"settle-test-secret-0123456789abcdef";
    let (_tmp, log, sock) = paths("guarded");
    let b = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let _h = b.serve(&sock).unwrap();
    let connect = |grant: Option<&str>| {
        let mut c = Client::connect(&sock).unwrap();
        if let Some(grant) = grant {
            let cap = astream_cap::mint(SECRET, grant).unwrap();
            c.attach(&cap.filter, &cap.tag).unwrap();
        }
        c
    };
    let mut none = connect(None);
    assert!(
        none.settle().is_err(),
        "an unattached connection settles nothing"
    );
    let mut read = connect(Some("ro:/r/>"));
    assert!(read.settle().is_err(), "a read grant settles nothing");
    assert_eq!(read.owed_acks(), 0, "the refusal paid the ack");
    let full = b.flush_counts().full;
    let mut write = connect(Some("rw:/w/>"));
    assert_eq!(write.settle().unwrap(), b.durable_head());
    assert_eq!(
        b.flush_counts().full,
        full + 1,
        "the read-write grant's settle flushed"
    );
}
