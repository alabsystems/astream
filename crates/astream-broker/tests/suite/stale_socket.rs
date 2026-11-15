// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Establish a stale socket using a broker that actually crashed. The listener
//! is created after spawning the child, so the parallel parent never owns its fd.

use std::io::{BufRead, BufReader, ErrorKind};
use std::os::unix::fs::FileTypeExt;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::process::{Child, Command, Stdio};

struct OwnedChild(Option<Child>);

impl Drop for OwnedChild {
    fn drop(&mut self) {
        if let Some(mut child) = self.0.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

pub(super) fn from_crashed_broker(socket: impl AsRef<Path>, log: impl AsRef<Path>) {
    let socket = socket.as_ref();
    let log = log.as_ref();
    let mut owned = OwnedChild(Some(
        Command::new(env!("CARGO_BIN_EXE_asb"))
            .arg("serve")
            .arg(socket)
            .arg(log)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn owned stale-socket broker"),
    ));
    let child = owned.0.as_mut().unwrap();
    let mut ready = String::new();
    BufReader::new(child.stdout.take().unwrap())
        .read_line(&mut ready)
        .expect("read broker readiness");
    assert!(ready.starts_with("listening "), "{ready:?}");
    assert!(
        UnixStream::connect(socket).is_ok(),
        "child listener is live"
    );
    child.kill().expect("kill owned broker");
    assert!(!child.wait().expect("reap owned broker").success());
    drop(owned.0.take());

    assert!(std::fs::symlink_metadata(socket)
        .expect("crashed broker leaves a socket file")
        .file_type()
        .is_socket());
    let error = UnixStream::connect(socket).expect_err("no listener remains after the child exits");
    assert_eq!(error.kind(), ErrorKind::ConnectionRefused, "{error}");
}
