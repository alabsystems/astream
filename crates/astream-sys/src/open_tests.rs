// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A folder an open for writing meets is named as the folder it is on every host
//! (`write_open_refusal`, and through it `open_nonblocking_rw`): `IsADirectory`, which
//! Unix's `open(2)` answers itself and Windows' `CreateFileW` answers as access denied.
//!
//! NEGATIVE CONTROLS, each run on Windows: `write_open_refusal` that returns every
//! refusal as it is fails the folder's law there (`PermissionDenied`); one that names
//! every access denial a folder, whatever the path is, fails the read-only file's control.

use std::fs::OpenOptions;
use std::io;
use std::path::PathBuf;

use crate::{open_nonblocking_rw, write_open_refusal, Links};

/// A scratch folder of this test's own, removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Scratch {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let dir =
            std::env::temp_dir().join(format!("astream-sys-open-{tag}-{}-{n}", std::process::id()));
        std::fs::create_dir(&dir).expect("an exclusive scratch folder");
        Scratch(dir)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A FOLDER OPENED FOR WRITING IS REFUSED AS A FOLDER, `IsADirectory`, on every host:
/// by `open_nonblocking_rw` (a link at its last component followed or refused), and by
/// `write_open_refusal` of a plain read-write open's refusal, and of one that would
/// create the file, which Windows refuses at a folder before it says the name is taken.
#[test]
fn a_folder_opened_for_writing_is_refused_as_a_folder() {
    let scratch = Scratch::new("folder");
    let folder = scratch.0.join("log");
    std::fs::create_dir(&folder).unwrap();
    for links in [Links::Follow, Links::Refuse] {
        let refused = open_nonblocking_rw(&folder, links).expect_err("a folder takes no write");
        assert_eq!(
            refused.kind(),
            io::ErrorKind::IsADirectory,
            "{links:?}: {refused}"
        );
    }
    let plain = OpenOptions::new().read(true).write(true).open(&folder);
    let refused = write_open_refusal(plain.expect_err("a folder takes no write"), &folder);
    assert_eq!(refused.kind(), io::ErrorKind::IsADirectory, "{refused}");
    let fresh = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(&folder);
    let refused = write_open_refusal(fresh.expect_err("a folder is there"), &folder);
    assert!(
        matches!(
            refused.kind(),
            io::ErrorKind::IsADirectory | io::ErrorKind::AlreadyExists
        ),
        "the name is a folder's, or taken: {refused}"
    );
    assert!(folder.is_dir(), "the folder is as it was");
}

/// CONTROL: a refusal of a path that is no folder is the open's own, its code
/// unchanged: a read-only file's (Windows' `ERROR_ACCESS_DENIED`, the code a folder is
/// refused with there; Unix's `EACCES`, which root writes past) stays `PermissionDenied`,
/// and a missing path's `NotFound`.
#[test]
fn a_refusal_of_what_is_no_folder_is_the_opens_own() {
    let scratch = Scratch::new("control");
    let file = scratch.0.join("log");
    std::fs::write(&file, b"held").unwrap();
    let writable = std::fs::metadata(&file).unwrap().permissions();
    let mut read_only = writable.clone();
    read_only.set_readonly(true);
    std::fs::set_permissions(&file, read_only).unwrap();
    let opened = OpenOptions::new().read(true).write(true).open(&file);
    std::fs::set_permissions(&file, writable).unwrap();
    match opened {
        Err(denied) => {
            let code = denied.raw_os_error();
            let refused = write_open_refusal(denied, &file);
            assert_eq!(refused.kind(), io::ErrorKind::PermissionDenied, "{refused}");
            assert_eq!(refused.raw_os_error(), code, "{refused}");
        }
        #[cfg(unix)]
        Ok(_) if crate::euid() == 0 => {}
        Ok(_) => panic!("a read-only file opened for writing"),
    }

    let missing = scratch.0.join("none");
    let open = OpenOptions::new().read(true).write(true).open(&missing);
    let refused = open.expect_err("nothing is there");
    let code = refused.raw_os_error();
    let refused = write_open_refusal(refused, &missing);
    assert_eq!(refused.kind(), io::ErrorKind::NotFound, "{refused}");
    assert_eq!(refused.raw_os_error(), code, "{refused}");
    let refused = open_nonblocking_rw(&missing, Links::Follow).expect_err("nothing is there");
    assert_eq!(refused.kind(), io::ErrorKind::NotFound, "{refused}");
}
