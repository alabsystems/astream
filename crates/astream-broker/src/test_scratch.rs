// Copyright 2026 Andrew Yates

//! Exclusive scratch roots for in-memory/direct-file broker regressions.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

pub(crate) struct Scratch(PathBuf);

impl Scratch {
    pub(crate) fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let mut builder = std::fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            builder.mode(0o700);
        }
        // Name collisions allocate another name; no preexisting entry is adopted or removed.
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let p = std::env::temp_dir().join(format!("astream-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Self(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create owned scratch: {e}"),
            }
        }
        panic!("could not allocate an exclusive scratch name");
    }

    pub(crate) fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("broker failure world retained: {}", self.0.display());
            return;
        }
        // Only a directory this value successfully created can reach this cleanup.
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
