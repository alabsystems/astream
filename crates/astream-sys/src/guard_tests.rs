// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::fs::{File, OpenOptions, TryLockError};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::PathBuf;

/// A file of `bytes` in a folder of this test's own, removed on drop.
struct Scratch {
    dir: PathBuf,
    file: PathBuf,
}

impl Scratch {
    fn new(name: &str, bytes: &[u8]) -> Scratch {
        let dir =
            std::env::temp_dir().join(format!("astream-sys-guard-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("log");
        std::fs::write(&file, bytes).unwrap();
        Scratch { dir, file }
    }

    fn open(&self) -> File {
        OpenOptions::new()
            .read(true)
            .write(true)
            .open(&self.file)
            .unwrap()
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn would_block(answer: Result<(), TryLockError>) -> bool {
    matches!(answer, Err(TryLockError::WouldBlock))
}

/// THE GUARD KEEPS A SECOND WRITER OUT AND NO READER: while one handle holds it, another
/// handle of the same file (this process's, the case a Windows lock refuses as surely as
/// another process's) is refused the guard both ways, and reads and writes every byte of
/// the file. Once it is let go, the other takes it.
#[test]
fn a_guard_refuses_a_second_and_leaves_every_byte_readable_beside_it() {
    let bytes: Vec<u8> = (0..=255u8).cycle().take(64 * 1024).collect();
    let scratch = Scratch::new("beside", &bytes);
    let writer = scratch.open();
    super::try_lock(&writer).unwrap();

    let other = scratch.open();
    assert!(
        would_block(super::try_lock(&other)),
        "a second exclusive guard"
    );
    assert!(
        would_block(super::try_lock_shared(&other)),
        "a shared guard beside it"
    );

    let read = std::fs::read(&scratch.file).expect("a read beside the guard");
    assert_eq!(read, bytes, "every byte, through another handle");
    let mut tail = vec![0; 16];
    let mut reader: &File = &other;
    reader.seek(SeekFrom::End(-16)).unwrap();
    reader.read_exact(&mut tail).unwrap();
    assert_eq!(tail, bytes[bytes.len() - 16..]);
    let mut appender: &File = &other;
    appender.seek(SeekFrom::End(0)).unwrap();
    appender
        .write_all(b"beside")
        .expect("a write beside the guard");
    assert_eq!(
        std::fs::metadata(&scratch.file).unwrap().len(),
        bytes.len() as u64 + 6,
        "the guard byte is past the file and grows nothing"
    );

    super::unlock(&writer).unwrap();
    super::try_lock(&other).expect("the guard, once let go");
    assert!(
        would_block(super::try_lock(&writer)),
        "now the first is kept out"
    );
    super::unlock(&other).unwrap();
}

/// Shared guards stand together and keep an exclusive one out until the last goes.
#[test]
fn shared_guards_stand_together_and_keep_an_exclusive_one_out() {
    let scratch = Scratch::new("shared", b"x");
    let (one, two, three) = (scratch.open(), scratch.open(), scratch.open());
    super::try_lock_shared(&one).unwrap();
    super::try_lock_shared(&two).expect("a second shared guard");
    assert!(would_block(super::try_lock(&three)));
    super::unlock(&one).unwrap();
    assert!(
        would_block(super::try_lock(&three)),
        "one shared guard still stands"
    );
    super::unlock(&two).unwrap();
    super::try_lock(&three).expect("no guard stands");
    super::unlock(&three).unwrap();
}

/// A whole-file lock taken by anything else (`File::try_lock`, an older build's) covers
/// the guard, so it and a guard keep each other out, either way round.
#[test]
fn a_whole_file_lock_and_a_guard_keep_each_other_out() {
    let scratch = Scratch::new("whole", b"x");
    let (whole, guard) = (scratch.open(), scratch.open());
    whole.try_lock().unwrap();
    assert!(would_block(super::try_lock(&guard)));
    assert!(would_block(super::try_lock_shared(&guard)));
    whole.unlock().unwrap();
    super::try_lock(&guard).unwrap();
    assert!(matches!(whole.try_lock(), Err(TryLockError::WouldBlock)));
    assert!(matches!(
        whole.try_lock_shared(),
        Err(TryLockError::WouldBlock)
    ));
    super::unlock(&guard).unwrap();
    whole
        .try_lock()
        .expect("the whole file, once the guard is let go");
    whole.unlock().unwrap();
}
