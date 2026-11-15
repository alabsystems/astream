// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The owner-only rule on real files: `open_nonblocking`, `owner_private` and
//! `owner_private_dir` (claim cap.secret-file-owner-only, through astream-cap's capfile),
//! and laws A1-A6 (claim os.cordon): the clauses both entries share, the kind words, the
//! path entry `owner_private_dir_by_path` against the opened verdict, its decision over
//! every Libc outcome, the bound of the buffer `lstatx_np` writes, and
//! `kind_and_owner_of`.

use std::os::unix::fs::{DirBuilderExt as _, PermissionsExt as _};
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::Duration;

use crate::{
    euid, open_nonblocking, open_nonblocking_rw, owner_private, owner_private_dir, Links,
    NotPrivate,
};

/// A wait for something that must happen: a hang detector, not a latency budget.
const HANG: Duration = Duration::from_secs(60);

/// A scratch directory, 0700, removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "astream-sys-owner-{tag}-{}-{n}",
            std::process::id()
        ));
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&dir)
            .expect("an exclusive scratch directory");
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        Self(dir)
    }

    fn file(&self, name: &str, mode: u32) -> PathBuf {
        let path = self.0.join(name);
        std::fs::write(&path, b"secret").unwrap();
        chmod(&path, mode);
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn chmod(path: &Path, mode: u32) {
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).unwrap();
}

fn judge(path: &Path) -> Result<std::fs::Metadata, NotPrivate> {
    let file = open_nonblocking(path, Links::Refuse).expect("open");
    owner_private(&file).expect("judged")
}

/// A file of ours at 0600, 0400 or 0700 passes and hands back the descriptor's
/// metadata; any group or other bit is refused as `Mode`, naming the bits. The same
/// file and bytes, only the mode moved: each pass is the control of the refusals.
#[test]
fn owner_private_passes_owner_only_modes_and_names_any_other() {
    let scratch = Scratch::new("mode");
    let path = scratch.file("k", 0o600);
    for (mode, ok) in [
        (0o600, true),
        (0o400, true),
        (0o700, true),
        (0o640, false),
        (0o604, false),
        (0o644, false),
        (0o660, false),
    ] {
        chmod(&path, mode);
        match judge(&path) {
            Ok(meta) => {
                assert!(ok, "{mode:o} passed");
                assert_eq!(meta.len(), 6);
            }
            Err(refused) => {
                assert!(!ok, "{mode:o}: {refused}");
                assert_eq!(refused, NotPrivate::Mode(mode));
                assert_eq!(refused.to_string(), format!("is mode {mode:04o}"));
            }
        }
    }
}

/// The kind is the first clause: a directory is not a file to `owner_private`, and a
/// file is not a directory to `owner_private_dir`, each private by its mode. A
/// directory of ours at 0700 passes `owner_private_dir`, at 0755 is refused as `Mode`.
#[test]
fn the_kind_is_judged_first_and_a_directory_has_its_own_judge() {
    let scratch = Scratch::new("kind");
    let file = scratch.file("k", 0o600);
    let sub = scratch.0.join("sub");
    std::fs::DirBuilder::new().mode(0o700).create(&sub).unwrap();
    chmod(&sub, 0o700);
    let opened = open_nonblocking(&sub, Links::Refuse).expect("a directory opens");
    assert_eq!(
        owner_private(&opened).unwrap().unwrap_err(),
        NotPrivate::Kind("a directory")
    );
    assert!(owner_private_dir(&opened).unwrap().is_ok());
    let opened = open_nonblocking(&file, Links::Refuse).unwrap();
    assert_eq!(
        owner_private_dir(&opened).unwrap().unwrap_err(),
        NotPrivate::Kind("a regular file")
    );
    chmod(&sub, 0o755);
    let opened = open_nonblocking(&sub, Links::Refuse).unwrap();
    assert_eq!(
        owner_private_dir(&opened).unwrap().unwrap_err(),
        NotPrivate::Mode(0o755)
    );
}

/// Another user's file is refused as `Owner`, before its mode: `/` is root's (0755),
/// so a reader that is not root is refused for the owner and root is refused for the
/// mode. Either way it never passes.
#[test]
fn another_users_directory_is_refused_for_its_owner() {
    let root = open_nonblocking(Path::new("/"), Links::Refuse).expect("/ opens");
    let refused = owner_private_dir(&root).unwrap().unwrap_err();
    if euid() == 0 {
        assert_eq!(refused, NotPrivate::Mode(0o755));
    } else {
        assert_eq!(refused, NotPrivate::Owner(0));
        assert_eq!(refused.to_string(), "is owned by uid 0, not this user");
    }
}

/// A FIFO at the path opens AT ONCE, non-blocking, and is refused as one: a plain open
/// would wait for a writer that never comes. The open runs on its own thread behind
/// the one-minute hang detector, so a blocking open fails the test rather than hanging
/// it.
#[test]
fn a_fifo_is_refused_without_waiting_for_a_writer() {
    let scratch = Scratch::new("fifo");
    let fifo = scratch.0.join("k");
    let made = std::process::Command::new("mkfifo")
        .arg("-m")
        .arg("600")
        .arg(&fifo)
        .status()
        .expect("run mkfifo");
    assert!(made.success(), "mkfifo");
    let (tx, rx) = mpsc::channel();
    let at = fifo.clone();
    std::thread::spawn(move || {
        let opened = open_nonblocking(&at, Links::Refuse).map(|f| owner_private(&f));
        let _ = tx.send(opened);
    });
    let judged = rx
        .recv_timeout(HANG)
        .expect("a non-blocking open of a FIFO returns");
    assert_eq!(
        judged.expect("opened").expect("judged").unwrap_err(),
        NotPrivate::Kind("a FIFO")
    );
}

/// A READ-WRITE open is refused where a writer in place would be, and writes nothing: a file
/// of ours at 0400 opens read-only (the control) and is refused read-write (`PermissionDenied`)
/// with its bytes as they were, the same file at 0600 opens read-write with its bytes as they
/// were, and a FIFO opens read-write AT ONCE, behind the one-minute hang detector. Root
/// writes past a mode, so as root the 0400 file opens read-write too.
#[test]
fn a_read_write_open_is_refused_as_a_writer_is_and_writes_nothing() {
    let scratch = Scratch::new("rw");
    let path = scratch.file("k", 0o400);
    assert!(
        open_nonblocking(&path, Links::Refuse).is_ok(),
        "CONTROL: it opens read-only"
    );
    let rw = open_nonblocking_rw(&path, Links::Refuse);
    if euid() == 0 {
        assert!(rw.is_ok(), "root writes past a mode");
    } else {
        let refused = rw.expect_err("a 0400 file is no writer's");
        assert_eq!(
            refused.kind(),
            std::io::ErrorKind::PermissionDenied,
            "{refused}"
        );
    }
    assert_eq!(std::fs::read(&path).unwrap(), b"secret");
    chmod(&path, 0o600);
    let opened = open_nonblocking_rw(&path, Links::Refuse).expect("a 0600 file opens read-write");
    drop(opened);
    assert_eq!(
        std::fs::read(&path).unwrap(),
        b"secret",
        "the open wrote nothing"
    );

    let fifo = scratch.0.join("f");
    let made = std::process::Command::new("mkfifo")
        .arg("-m")
        .arg("600")
        .arg(&fifo)
        .status()
        .expect("run mkfifo");
    assert!(made.success(), "mkfifo");
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let opened = open_nonblocking_rw(&fifo, Links::Refuse).map(|f| owner_private(&f));
        let _ = tx.send(opened);
    });
    let judged = rx
        .recv_timeout(HANG)
        .expect("a non-blocking read-write open of a FIFO returns");
    assert_eq!(
        judged.expect("opened").expect("judged").unwrap_err(),
        NotPrivate::Kind("a FIFO")
    );
}

/// `Links::Refuse` refuses a symlink at the last component and opens nothing through
/// it; `Links::Follow` opens the file it names (the control).
#[test]
fn a_link_is_refused_or_followed_as_asked() {
    let scratch = Scratch::new("link");
    let real = scratch.file("real", 0o600);
    let link = scratch.0.join("link");
    std::os::unix::fs::symlink(&real, &link).unwrap();
    assert!(open_nonblocking(&link, Links::Refuse).is_err());
    let followed = open_nonblocking(&link, Links::Follow).expect("followed");
    assert!(owner_private(&followed).unwrap().is_ok());
}

/// On macOS an access-list entry that ALLOWS is refused as `Acl` on a 0600 file and a
/// 0700 directory, both private by their mode; `chmod -N` clears it and the same file
/// passes. A DENY entry takes nothing away and passes: the negative control.
#[cfg(target_vendor = "apple")]
#[test]
fn an_access_list_that_allows_others_is_refused() {
    let acl = |args: &[&str], path: &Path| {
        let ran = std::process::Command::new("/bin/chmod")
            .args(args)
            .arg(path)
            .status()
            .expect("run chmod");
        assert!(ran.success(), "chmod {args:?}");
    };
    let scratch = Scratch::new("acl");
    let path = scratch.file("k", 0o600);
    acl(&["+a", "everyone allow read"], &path);
    assert_eq!(judge(&path).unwrap_err(), NotPrivate::Acl);
    acl(&["-N"], &path);
    assert!(judge(&path).is_ok());
    acl(&["+a", "everyone deny write"], &path);
    assert!(judge(&path).is_ok(), "a deny entry passes");

    let sub = scratch.0.join("sub");
    std::fs::DirBuilder::new().mode(0o700).create(&sub).unwrap();
    acl(&["+a", "everyone allow list"], &sub);
    let opened = open_nonblocking(&sub, Links::Refuse).unwrap();
    assert_eq!(
        owner_private_dir(&opened).unwrap().unwrap_err(),
        NotPrivate::Acl
    );
}

/// On Apple a file's verdict never rests on errno once Libc's frees have run
/// (ATERM-KI-1111-30): with errno left EINVAL as each `filesec_free` returns, as
/// libmalloc's `free` leaves it when XNU refuses the `madvise` that hands a chunk back, a
/// 0600 file and a 0700 directory with no list, and a file carrying only a deny entry,
/// still pass, and an allow entry is still `Acl`. Negative control: the earlier read,
/// `acl_get_fd_np` and then errno (ENOENT for no list, anything else an error), with the
/// same EINVAL left after it, fails the first judgement with "Invalid argument (os error
/// 22)", the refusal agh met on a loaded Mac for a worktree's `.git` and its `vault.toml`.
#[cfg(target_vendor = "apple")]
#[test]
fn a_file_with_no_list_passes_whatever_libcs_frees_leave_in_errno() {
    use crate::owner::errno_seam;
    let scratch = Scratch::new("errno");
    let path = scratch.file("k", 0o600);
    errno_seam::clobbered(|| {
        assert!(judge(&path).is_ok(), "no list, EINVAL left in errno");
        let opened = open_nonblocking(&scratch.0, Links::Refuse).unwrap();
        assert!(owner_private_dir(&opened).unwrap().is_ok());
    });
    let acl = |args: &[&str]| {
        let ran = std::process::Command::new("/bin/chmod")
            .args(args)
            .arg(&path)
            .status()
            .expect("run chmod");
        assert!(ran.success(), "chmod {args:?}");
    };
    acl(&["+a", "everyone deny write"]);
    errno_seam::clobbered(|| assert!(judge(&path).is_ok(), "a deny entry passes"));
    acl(&["+a", "everyone allow read"]);
    errno_seam::clobbered(|| assert_eq!(judge(&path).unwrap_err(), NotPrivate::Acl));
}

/// Every reading of the list maps to its verdict by itself, errno no part of it: no list
/// is `Ok(false)`, a list the allow walk's answer, and every unread state an error, the
/// realloc failure statx1 returns 0 for (no mode set) included, which a decision on the
/// list bit alone would read as no list.
#[cfg(target_vendor = "apple")]
#[test]
fn each_list_reading_has_one_verdict() {
    use crate::owner::ListRead;
    assert!(!ListRead::Unlisted.allows().unwrap());
    assert!(ListRead::Listed(true).allows().unwrap());
    assert!(!ListRead::Listed(false).allows().unwrap());
    for unread in [
        ListRead::NoFilesec,
        ListRead::Failed(-1),
        ListRead::Failed(12),
        ListRead::Unset,
        ListRead::Uncopied(None),
        ListRead::Uncopied(Some(12)),
    ] {
        assert!(unread.allows().is_err(), "{unread:?}");
    }
}

/// On macOS the access list is judged BEFORE the mode: a 0755 directory and a 0644 file,
/// each open by its mode bits as well, that carry an `everyone allow read` entry are `Acl`,
/// never `Mode`. A caller that narrows the mode it is told of (aterm-uds's
/// `ensure_private_dir`) relies on it: a `Mode` answer must mean every other clause held,
/// or narrowing the mode would leave the allow entry in place and call the directory
/// private. Control: once `chmod -N` clears the entry, the same directory and file are
/// `Mode`, naming their bits.
#[cfg(target_vendor = "apple")]
#[test]
fn the_access_list_is_judged_before_the_mode() {
    let acl = |args: &[&str], path: &Path| {
        let ran = std::process::Command::new("/bin/chmod")
            .args(args)
            .arg(path)
            .status()
            .expect("run chmod");
        assert!(ran.success(), "chmod {args:?}");
    };
    let scratch = Scratch::new("order");
    let path = scratch.file("k", 0o644);
    let sub = scratch.0.join("sub");
    std::fs::DirBuilder::new().mode(0o700).create(&sub).unwrap();
    chmod(&sub, 0o755);
    for at in [&path, &sub] {
        acl(&["+a", "everyone allow read"], at);
    }
    assert_eq!(judge(&path).unwrap_err(), NotPrivate::Acl);
    let opened = open_nonblocking(&sub, Links::Refuse).unwrap();
    assert_eq!(
        owner_private_dir(&opened).unwrap().unwrap_err(),
        NotPrivate::Acl
    );
    for at in [&path, &sub] {
        acl(&["-N"], at);
    }
    assert_eq!(judge(&path).unwrap_err(), NotPrivate::Mode(0o644));
    let opened = open_nonblocking(&sub, Links::Refuse).unwrap();
    assert_eq!(
        owner_private_dir(&opened).unwrap().unwrap_err(),
        NotPrivate::Mode(0o755)
    );
}

/// What std's `FileType` predicates call a file type: the oracle `kind_word` is held to.
fn std_word(file_type: std::fs::FileType) -> &'static str {
    use std::os::unix::fs::FileTypeExt as _;
    if file_type.is_fifo() {
        "a FIFO"
    } else if file_type.is_socket() {
        "a socket"
    } else if file_type.is_char_device() || file_type.is_block_device() {
        "a device"
    } else if file_type.is_dir() {
        "a directory"
    } else if file_type.is_file() {
        "a regular file"
    } else if file_type.is_symlink() {
        "a symlink"
    } else {
        "not a regular file"
    }
}

/// Makes a FIFO at `path` with `mkfifo -m 600`, asserted.
fn mkfifo(path: &Path) {
    let made = std::process::Command::new("mkfifo")
        .arg("-m")
        .arg("600")
        .arg(path)
        .status()
        .expect("run mkfifo");
    assert!(made.success(), "mkfifo {}", path.display());
}

/// Makes a directory at `path` and sets its mode to exactly `mode`.
fn mkdir(path: &Path, mode: u32) {
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(path)
        .expect("a fixture directory");
    chmod(path, mode);
}

/// LAW A1: the owner-only clauses are one order, written once, for every entry that
/// judges an object: `kind_and_owner` (the kind asked for, then the owner) and only then
/// `Owned::list_and_mode` (an allow entry, then the group and other bits), the first one
/// broken the answer. Pure, over made-up `st_mode`s and uids with an explicit euid of 501;
/// "not reached" rows hand the list clause `allows = true`, so a clause judged early shows.
///
/// NCs, each applied by hand once to owner_rule.rs and reverted: the owner judged before
/// the kind (the FIFO row answers `Owner(0)`); the mode judged before the list (the 0755
/// row with an allow entry answers `Mode(0o755)`); `& 0o007` in place of `& 0o077` (the
/// 0750 row passes).
#[test]
fn the_owner_clauses_are_one_order_for_both_entries() {
    use crate::owner_rule::{kind_and_owner, Seen, S_IFDIR, S_IFIFO, S_IFREG};
    use NotPrivate::{Acl, Kind, Mode, Owner};
    const ME: u32 = 501;
    const WHITEOUT: u32 = 0o160_000;
    // (st_mode, uid, dir, allows, expected)
    let rows = [
        (S_IFIFO | 0o600, 0, true, true, Err(Kind("a FIFO"))),
        (S_IFDIR | 0o777, 0, true, true, Err(Owner(0))),
        (S_IFDIR | 0o755, ME, true, true, Err(Acl)),
        (S_IFDIR | 0o755, ME, true, false, Err(Mode(0o755))),
        (S_IFDIR | 0o750, ME, true, false, Err(Mode(0o750))),
        (S_IFDIR | 0o700, ME, true, false, Ok(())),
        (S_IFDIR | 0o1700, ME, true, false, Ok(())),
        (S_IFREG | 0o600, ME, true, true, Err(Kind("a regular file"))),
        (S_IFREG | 0o600, ME, false, false, Ok(())),
        (S_IFDIR | 0o700, ME, false, true, Err(Kind("a directory"))),
        (
            WHITEOUT | 0o700,
            ME,
            true,
            true,
            Err(Kind("not a regular file")),
        ),
    ];
    let mut wrong = Vec::new();
    for (st_mode, uid, dir, allows, expected) in rows {
        let judged = match kind_and_owner(Seen { st_mode, uid }, dir, ME) {
            Ok(owned) => owned.list_and_mode(allows),
            Err(broken) => Err(broken),
        };
        if judged != expected {
            wrong.push(format!(
                "st_mode {st_mode:o} uid {uid} dir {dir} allows {allows}: {judged:?}, expected {expected:?}"
            ));
        }
    }
    assert!(wrong.is_empty(), "A1: {wrong:#?}");
}

/// LAW A2: `kind_word` over `st_mode & S_IFMT` names every kind as std's `FileType`
/// predicates do (the descriptor entry's words before the clauses were shared): a regular
/// file, a directory, a FIFO, a socket, `/dev/null` (a device) and a symlink (read through
/// `symlink_metadata`), each also its absolute word.
///
/// NC, applied by hand once to owner_rule.rs and reverted: `S_IFSOCK = 0o120000` (the
/// symlink's number).
#[test]
fn a_kind_word_agrees_with_std() {
    use crate::owner_rule::{kind_word, S_IFMT};
    use std::os::unix::fs::MetadataExt as _;
    let scratch = Scratch::new("k");
    let file = scratch.file("f", 0o600);
    let dir = scratch.0.join("d");
    mkdir(&dir, 0o700);
    let fifo = scratch.0.join("q");
    mkfifo(&fifo);
    let socket = scratch.0.join("s");
    let listener = std::os::unix::net::UnixListener::bind(&socket).expect("a socket");
    let link = scratch.0.join("l");
    std::os::unix::fs::symlink(&file, &link).unwrap();
    let mut wrong = Vec::new();
    for (path, word) in [
        (file.as_path(), "a regular file"),
        (dir.as_path(), "a directory"),
        (fifo.as_path(), "a FIFO"),
        (socket.as_path(), "a socket"),
        (Path::new("/dev/null"), "a device"),
        (link.as_path(), "a symlink"),
    ] {
        let meta = std::fs::symlink_metadata(path).expect("lstat");
        let ours = kind_word(meta.mode() & S_IFMT);
        let std = std_word(meta.file_type());
        if ours != std || ours != word {
            wrong.push(format!(
                "{}: kind_word {ours:?}, std {std:?}, expected {word:?}",
                path.display()
            ));
        }
    }
    drop(listener);
    assert!(wrong.is_empty(), "A2: {wrong:#?}");
}

/// LAW A6: `kind_and_owner_of` holds a caller's own metadata to the kind and owner clauses
/// the descriptor entry judges, and to nothing else: over real objects it answers the
/// first of the two broken, else `Ok(())` (a 0755 directory passes it, the mode not being
/// its clause), and where the object opens, every `Kind` or `Owner` refusal of
/// `owner_private` / `owner_private_dir` on the descriptor is its answer, and every other
/// descriptor verdict is its `Ok(())`. `/` is root's: `Owner(0)` unless the reader is root.
///
/// NC, applied by hand once to lib.rs and reverted: `uid: meta.gid()` in
/// `kind_and_owner_of`.
#[test]
fn kind_and_owner_of_holds_metadata_to_the_descriptors_clauses() {
    use crate::kind_and_owner_of;
    let root = euid() == 0;
    let scratch = Scratch::new("m");
    let file = scratch.file("f", 0o600);
    let open_dir = scratch.0.join("o");
    mkdir(&open_dir, 0o755);
    let dir = scratch.0.join("d");
    mkdir(&dir, 0o700);
    let fifo = scratch.0.join("q");
    mkfifo(&fifo);
    let link = scratch.0.join("l");
    std::os::unix::fs::symlink(&dir, &link).unwrap();
    let slash = if root {
        Ok(())
    } else {
        Err(NotPrivate::Owner(0))
    };
    let mut wrong = Vec::new();
    for (path, dir_wanted, expected) in [
        (file.as_path(), false, Ok(())),
        (
            file.as_path(),
            true,
            Err(NotPrivate::Kind("a regular file")),
        ),
        (dir.as_path(), true, Ok(())),
        (dir.as_path(), false, Err(NotPrivate::Kind("a directory"))),
        (open_dir.as_path(), true, Ok(())),
        (fifo.as_path(), true, Err(NotPrivate::Kind("a FIFO"))),
        (
            Path::new("/dev/null"),
            true,
            Err(NotPrivate::Kind("a device")),
        ),
        (Path::new("/"), true, slash),
        (link.as_path(), true, Err(NotPrivate::Kind("a symlink"))),
    ] {
        let meta = std::fs::symlink_metadata(path).expect("lstat");
        let answer = kind_and_owner_of(&meta, dir_wanted);
        if answer != expected {
            wrong.push(format!(
                "{} (dir {dir_wanted}): {answer:?}, expected {expected:?}",
                path.display()
            ));
        }
        let at = path.to_path_buf();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let judged = open_nonblocking(&at, Links::Refuse).map(|opened| {
                if dir_wanted {
                    owner_private_dir(&opened).map(|v| v.map(drop))
                } else {
                    owner_private(&opened).map(|v| v.map(drop))
                }
            });
            let _ = tx.send(judged);
        });
        let opened = rx.recv_timeout(HANG).expect("a non-blocking open returns");
        if let Ok(judged) = opened {
            let descriptor = match judged.expect("judged") {
                Err(broken @ (NotPrivate::Kind(_) | NotPrivate::Owner(_))) => Err(broken),
                Ok(()) | Err(NotPrivate::Mode(_) | NotPrivate::Acl) => Ok(()),
            };
            if descriptor != answer {
                wrong.push(format!(
                    "{} (dir {dir_wanted}): {answer:?}, the descriptor's clauses {descriptor:?}",
                    path.display()
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "A6: {wrong:#?}");
}

/// Darwin's `ELOOP`, `ENOTDIR`, `EACCES` and `EOPNOTSUPP`.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const ELOOP: i32 = 62;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const ENOTDIR: i32 = 20;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const EACCES: i32 = 13;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const EOPNOTSUPP: i32 = 102;

/// A3's oracle: what `open_nonblocking(path, Links::Refuse)` and `owner_private_dir` on
/// the descriptor it opens say of a path.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Opened {
    /// It opened: `owner_private_dir`'s verdict.
    Verdict(Result<(), NotPrivate>),
    /// `NotFound`.
    NotFound,
    /// `ELOOP`: a link at the last component.
    Loop,
    /// Any other refusal of the open, by its errno.
    Refused(i32),
}

/// The oracle for `path`, its open on a thread of its own behind the one-minute hang
/// detector (a FIFO opens at once non-blocking; a blocking open would hang here).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn opened(path: &Path) -> Opened {
    let at = path.to_path_buf();
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let oracle = match open_nonblocking(&at, Links::Refuse) {
            Ok(file) => Opened::Verdict(owner_private_dir(&file).expect("judged").map(drop)),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Opened::NotFound,
            Err(e) if e.raw_os_error() == Some(ELOOP) => Opened::Loop,
            Err(e) => Opened::Refused(e.raw_os_error().expect("an OS error")),
        };
        let _ = tx.send(oracle);
    });
    rx.recv_timeout(HANG).expect("a non-blocking open returns")
}

/// Whether the path entry's answer stands for the oracle: a decided answer is the
/// oracle's, and a `Kind` or `Owner` refusal where the open is refused is
/// `kind_and_owner_of` over std's `symlink_metadata`. `Undecided` stands for anything.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn agrees(path: &Path, answer: crate::DirByPath, oracle: Opened) -> bool {
    use crate::DirByPath;
    let lstat = std::fs::symlink_metadata(path);
    match (answer, oracle) {
        (DirByPath::Missing, Opened::NotFound) => true,
        (DirByPath::Symlink, Opened::Loop) => lstat.is_ok_and(|meta| meta.file_type().is_symlink()),
        (DirByPath::Judged(verdict), Opened::Verdict(seen)) => verdict == seen,
        (
            DirByPath::Judged(verdict @ Err(NotPrivate::Kind(_) | NotPrivate::Owner(_))),
            Opened::Refused(_),
        ) => lstat.is_ok_and(|meta| crate::kind_and_owner_of(&meta, true) == verdict),
        (DirByPath::Undecided(_), _) => true,
        _ => false,
    }
}

/// Runs `/bin/chmod <args> <path>`, asserted.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn chmod_acl(args: &[&str], path: &Path) {
    let ran = std::process::Command::new("/bin/chmod")
        .args(args)
        .arg(path)
        .status()
        .expect("run chmod");
    assert!(ran.success(), "chmod {args:?} {}", path.display());
}

/// The access lists and modes a fixture set, put back before its Scratch drops (a
/// 0000 or 0300 directory and a deny entry block `remove_dir_all`). `put_back` runs at
/// the end of the law and is asserted; a law that panics first has its fixtures put
/// back as best it can by `Drop`, which `Scratch`'s `Drop` follows.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
struct PutBack {
    lists: Vec<PathBuf>,
    modes: Vec<PathBuf>,
    done: bool,
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl PutBack {
    /// `chmod 700` each changed mode, then `chmod -N` each list; whether every one ran.
    fn put_back(&mut self) -> bool {
        self.done = true;
        let mut all = true;
        for path in &self.modes {
            all &= std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).is_ok();
        }
        for path in &self.lists {
            all &= std::process::Command::new("/bin/chmod")
                .arg("-N")
                .arg(path)
                .status()
                .is_ok_and(|ran| ran.success());
        }
        all
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl Drop for PutBack {
    fn drop(&mut self) {
        if !self.done {
            let _ = self.put_back();
        }
    }
}

/// The principals of the 20-entry list: 12 users and 8 groups every Mac has, each a
/// distinct qualifier, so `chmod +a` adds an entry for each rather than merging it into
/// one already there (file_cmds chmod_acl.c merges an entry of the same qualifier and
/// tag).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const DISTINCT: [&str; 20] = [
    "user:root",
    "user:daemon",
    "user:nobody",
    "user:_www",
    "user:_uucp",
    "user:_lp",
    "user:_postfix",
    "user:_sshd",
    "user:_spotlight",
    "user:_windowserver",
    "user:_coreaudiod",
    "user:_locationd",
    "group:staff",
    "group:admin",
    "group:wheel",
    "group:everyone",
    "group:tty",
    "group:operator",
    "group:kmem",
    "group:_lpadmin",
];

/// How many entries `/bin/ls -lde` lists for `path` (its ` <n>: ` lines).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn entries_listed(path: &Path) -> usize {
    let listed = std::process::Command::new("/bin/ls")
        .arg("-lde")
        .arg(path)
        .output()
        .expect("run ls");
    assert!(listed.status.success(), "ls -lde {}", path.display());
    String::from_utf8_lossy(&listed.stdout)
        .lines()
        .filter(|line| {
            line.trim_start()
                .split_once(": ")
                .is_some_and(|(n, _)| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
        })
        .count()
}

/// LAW A3: the path entry's judgement is the opened one. Over real fixtures, each row's
/// answer from `owner_private_dir_by_path` is its absolute expectation, reason included,
/// the oracle (`open_nonblocking(path, Links::Refuse)`, then `owner_private_dir`) is its
/// absolute expectation, and every decided answer stands for the oracle (`agrees`): a
/// verdict is the opened verdict, `Missing` is `NotFound`, `Symlink` is `ELOOP` on a
/// link, and a `Kind` or `Owner` refusal where the open is refused is
/// `kind_and_owner_of` over `symlink_metadata`. Two trailing-slash rows hold only to the
/// oracle. Two `/dev/fd/N` rows name a directory the law holds open, a 0733 one and a
/// 0700 one carrying `everyone allow list`: devfs's node shows the held directory with
/// every search bit clear, and its open dups the held descriptor (XNU
/// bsd/miscfs/devfs/devfs_fdesc_support.c:453-463, 497-505), so the node is
/// `NoOwnerRead` where the opened verdict is `Mode(0o733)` or `Acl`. Rows whose answer or
/// oracle differs for root branch on `euid() == 0`.
///
/// CONTROL: the 20-entry list holds at least 17 entries (`ls -lde`) before it is judged,
/// so its stat passes statx1's first 16-entry buffer (Libc sys/statx_np.c:34, 177-188).
///
/// NCs, each applied by hand once and reverted: in lib.rs's `by_path`, the S_IRUSR test
/// dropped, the S_IXUSR test dropped, `Missing` for any `rc == -1`, and the `S_IFLNK`
/// test dropped; in owner.rs, the list read as `valid == 1` and `FILESEC_GROUP` (2) read
/// for the owner; in owner_rule.rs, the owner judged before the kind.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn the_path_judgement_is_the_opened_one() {
    use crate::{owner_private_dir_by_path, DirByPath, PathUndecided};
    let root = euid() == 0;
    let scratch = Scratch::new("p");
    let at = |name: &str| scratch.0.join(name);
    let mut put_back = PutBack {
        lists: Vec::new(),
        modes: Vec::new(),
        done: false,
    };

    let file = scratch.file("f", 0o600);
    let mut file_slash = file.clone().into_os_string();
    file_slash.push("/");
    let file_slash = PathBuf::from(file_slash);
    for (name, mode) in [
        ("d700", 0o700),
        ("d500", 0o500),
        ("d755", 0o755),
        ("d750", 0o750),
        ("d711", 0o711),
    ] {
        mkdir(&at(name), mode);
    }
    for (name, mode) in [("d300", 0o300), ("d000", 0o000)] {
        mkdir(&at(name), mode);
        put_back.modes.push(at(name));
    }
    std::os::unix::fs::symlink(at("d700"), at("l")).unwrap();
    std::os::unix::fs::symlink(at("nothing"), at("dangling")).unwrap();
    let mut link_slash = at("l").into_os_string();
    link_slash.push("/");
    let link_slash = PathBuf::from(link_slash);
    mkfifo(&at("q"));
    let listener = std::os::unix::net::UnixListener::bind(at("s")).expect("a socket");
    mkdir(&at("locked"), 0o700);
    mkdir(&at("locked").join("inner"), 0o700);
    chmod(&at("locked"), 0o000);
    put_back.modes.push(at("locked"));
    for (name, mode, entry) in [
        ("allow-list", 0o700, "everyone allow list"),
        ("allow-read", 0o755, "everyone allow read"),
        ("deny-delete", 0o700, "everyone deny delete"),
        ("deny-list", 0o700, "everyone deny list"),
    ] {
        mkdir(&at(name), mode);
        put_back.lists.push(at(name));
        chmod_acl(&["+a", entry], &at(name));
    }
    mkdir(&at("deny-20"), 0o700);
    put_back.lists.push(at("deny-20"));
    for (who, right) in DISTINCT
        .iter()
        .zip(["delete", "writeattr", "writeextattr"].iter().cycle())
    {
        chmod_acl(&["+a", &format!("{who} deny {right}")], &at("deny-20"));
    }
    let listed = entries_listed(&at("deny-20"));
    assert!(
        listed >= 17,
        "CONTROL: the long list holds {listed} entries, not 17 or more"
    );
    mkdir(&at("h733"), 0o733);
    mkdir(&at("h700-allow"), 0o700);
    put_back.lists.push(at("h700-allow"));
    chmod_acl(&["+a", "everyone allow list"], &at("h700-allow"));
    let held_733 = open_nonblocking(&at("h733"), Links::Refuse).expect("hold h733");
    let held_listed = open_nonblocking(&at("h700-allow"), Links::Refuse).expect("hold h700-allow");
    let node = |held: &std::fs::File| {
        use std::os::fd::AsRawFd as _;
        PathBuf::from(format!("/dev/fd/{}", held.as_raw_fd()))
    };

    let judged = |verdict| Some(DirByPath::Judged(verdict));
    let undecided = |why| Some(DirByPath::Undecided(why));
    let opened_ok = Some(Opened::Verdict(Ok(())));
    let refused_unless_root = |errno| {
        if root {
            opened_ok
        } else {
            Some(Opened::Refused(errno))
        }
    };
    let rows: Vec<(PathBuf, Option<DirByPath>, Option<Opened>)> = vec![
        (
            at("missing"),
            Some(DirByPath::Missing),
            Some(Opened::NotFound),
        ),
        (
            at("missing").join("sub"),
            Some(DirByPath::Missing),
            Some(Opened::NotFound),
        ),
        (
            file.clone(),
            judged(Err(NotPrivate::Kind("a regular file"))),
            Some(Opened::Verdict(Err(NotPrivate::Kind("a regular file")))),
        ),
        (
            file.join("sub"),
            undecided(PathUndecided::Lookup),
            Some(Opened::Refused(ENOTDIR)),
        ),
        (at("l"), Some(DirByPath::Symlink), Some(Opened::Loop)),
        (at("dangling"), Some(DirByPath::Symlink), Some(Opened::Loop)),
        (
            at("q"),
            judged(Err(NotPrivate::Kind("a FIFO"))),
            Some(Opened::Verdict(Err(NotPrivate::Kind("a FIFO")))),
        ),
        (
            at("s"),
            judged(Err(NotPrivate::Kind("a socket"))),
            Some(Opened::Refused(EOPNOTSUPP)),
        ),
        (
            PathBuf::from("/dev/null"),
            judged(Err(NotPrivate::Kind("a device"))),
            Some(Opened::Verdict(Err(NotPrivate::Kind("a device")))),
        ),
        (at("d700"), judged(Ok(())), opened_ok),
        (at("d500"), judged(Ok(())), opened_ok),
        (
            at("d755"),
            judged(Err(NotPrivate::Mode(0o755))),
            Some(Opened::Verdict(Err(NotPrivate::Mode(0o755)))),
        ),
        (
            at("d750"),
            judged(Err(NotPrivate::Mode(0o750))),
            Some(Opened::Verdict(Err(NotPrivate::Mode(0o750)))),
        ),
        (
            at("d711"),
            judged(Err(NotPrivate::Mode(0o711))),
            Some(Opened::Verdict(Err(NotPrivate::Mode(0o711)))),
        ),
        (
            at("d300"),
            undecided(PathUndecided::NoOwnerRead),
            refused_unless_root(EACCES),
        ),
        (
            at("d000"),
            undecided(PathUndecided::NoOwnerRead),
            refused_unless_root(EACCES),
        ),
        (
            at("allow-list"),
            undecided(PathUndecided::Listed),
            Some(Opened::Verdict(Err(NotPrivate::Acl))),
        ),
        (
            at("allow-read"),
            undecided(PathUndecided::Listed),
            Some(Opened::Verdict(Err(NotPrivate::Acl))),
        ),
        (
            at("deny-delete"),
            undecided(PathUndecided::Listed),
            opened_ok,
        ),
        (
            at("deny-list"),
            undecided(PathUndecided::Listed),
            refused_unless_root(EACCES),
        ),
        (at("deny-20"), undecided(PathUndecided::Listed), opened_ok),
        (
            at("locked").join("inner"),
            if root {
                judged(Ok(()))
            } else {
                undecided(PathUndecided::Lookup)
            },
            refused_unless_root(EACCES),
        ),
        (
            PathBuf::from("/"),
            judged(Err(if root {
                NotPrivate::Mode(0o755)
            } else {
                NotPrivate::Owner(0)
            })),
            Some(Opened::Verdict(Err(if root {
                NotPrivate::Mode(0o755)
            } else {
                NotPrivate::Owner(0)
            }))),
        ),
        (
            node(&held_733),
            undecided(PathUndecided::NoOwnerRead),
            Some(Opened::Verdict(Err(NotPrivate::Mode(0o733)))),
        ),
        (
            node(&held_listed),
            undecided(PathUndecided::NoOwnerRead),
            Some(Opened::Verdict(Err(NotPrivate::Acl))),
        ),
        (link_slash, None, None),
        (file_slash, None, None),
    ];
    let mut wrong = Vec::new();
    let mut seen = Vec::new();
    for (path, expected, expected_oracle) in &rows {
        let answer = owner_private_dir_by_path(path);
        let oracle = opened(path);
        seen.push(format!("{}: {answer:?} / {oracle:?}", path.display()));
        if expected.is_some_and(|want| want != answer) {
            wrong.push(format!(
                "{}: answered {answer:?}, expected {expected:?}",
                path.display()
            ));
        }
        if expected_oracle.is_some_and(|want| want != oracle) {
            wrong.push(format!(
                "{}: the oracle {oracle:?}, expected {expected_oracle:?}",
                path.display()
            ));
        }
        if !agrees(path, answer, oracle) {
            wrong.push(format!(
                "{}: {answer:?} does not stand for the oracle {oracle:?}",
                path.display()
            ));
        }
    }
    drop(listener);
    drop((held_733, held_listed));
    assert!(
        put_back.put_back(),
        "every fixture's mode and list put back"
    );
    assert!(wrong.is_empty(), "A3: {wrong:#?}\nevery row: {seen:#?}");
}

/// LAW A4: the path entry's decision maps every Libc outcome of one `lstatx_np`
/// (Libc-1752.120.2 sys/statx_np.c:141-220, gen/filesec.c:101-188, 303-341) as Libc
/// gives it, reachable or not, over made-up readings with an explicit euid of 501: only
/// -1 with `ENOENT` and 0 with the owner, the mode and a clear list bit are decided;
/// every other reading is `Undecided`, and the list is never read as a verdict.
///
/// NCs, each applied by hand once to lib.rs's `by_path` and reverted: `rc == -1` in place
/// of `rc != 0` (the 12 row is decided); errno tested before `rc` (the stale-errno row
/// reads `Missing`).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn the_libc_outcomes_map_as_libc_does() {
    use crate::owner::{Looked, ENOENT};
    use crate::owner_rule::{S_IFDIR, S_IFIFO, S_IFLNK, S_IFREG};
    use crate::{by_path, DirByPath, PathUndecided};
    const ME: u32 = 501;
    let stat = |rc, errno, uid, mode: Option<u32>, listed| Looked {
        rc,
        errno,
        uid,
        mode: mode.map(|m| u16::try_from(m).expect("a mode_t")),
        listed,
    };
    let failed = |errno| Some(stat(-1, errno, None, None, None));
    let own = |mode, listed| Some(stat(0, None, Some(ME), Some(mode), listed));
    let unread = DirByPath::Undecided(PathUndecided::Unread);
    let lookup = DirByPath::Undecided(PathUndecided::Lookup);
    let listed = DirByPath::Undecided(PathUndecided::Listed);
    let rows: Vec<(&str, Option<Looked>, DirByPath)> = vec![
        ("filesec_init failed", None, unread),
        ("ENOENT", failed(Some(ENOENT)), DirByPath::Missing),
        ("ENOTDIR", failed(Some(20)), lookup),
        ("EACCES", failed(Some(13)), lookup),
        ("ELOOP", failed(Some(62)), lookup),
        ("EPERM", failed(Some(1)), lookup),
        ("ENOMEM", failed(Some(12)), lookup),
        ("EBADF", failed(Some(9)), lookup),
        ("no errno", failed(None), lookup),
        (
            "statx1's first malloc failed",
            Some(stat(12, None, Some(ME), Some(S_IFDIR | 0o700), Some(false))),
            unread,
        ),
        (
            "owner unset",
            Some(stat(0, None, None, Some(S_IFDIR | 0o700), Some(false))),
            unread,
        ),
        (
            "mode unset",
            Some(stat(0, None, Some(ME), None, Some(false))),
            unread,
        ),
        (
            "a stale ENOENT",
            Some(stat(
                0,
                Some(ENOENT),
                Some(ME),
                Some(S_IFDIR | 0o700),
                Some(false),
            )),
            DirByPath::Judged(Ok(())),
        ),
        (
            "a link",
            own(S_IFLNK | 0o755, Some(false)),
            DirByPath::Symlink,
        ),
        ("a listed link", own(S_IFLNK | 0o755, Some(true)), listed),
        ("the query refused", own(S_IFDIR | 0o700, None), unread),
        (
            "a listed own 0700",
            own(S_IFDIR | 0o700, Some(true)),
            listed,
        ),
        (
            "own 0300",
            own(S_IFDIR | 0o300, Some(false)),
            DirByPath::Undecided(PathUndecided::NoOwnerRead),
        ),
        (
            "own 0600",
            own(S_IFDIR | 0o600, Some(false)),
            DirByPath::Undecided(PathUndecided::NoOwnerRead),
        ),
        (
            "own 0400",
            own(S_IFDIR | 0o400, Some(false)),
            DirByPath::Undecided(PathUndecided::NoOwnerRead),
        ),
        (
            "own 0755",
            own(S_IFDIR | 0o755, Some(false)),
            DirByPath::Judged(Err(NotPrivate::Mode(0o755))),
        ),
        (
            "own 0700",
            own(S_IFDIR | 0o700, Some(false)),
            DirByPath::Judged(Ok(())),
        ),
        (
            "another uid's listed dir",
            Some(stat(0, None, Some(0), Some(S_IFDIR | 0o700), Some(true))),
            listed,
        ),
        (
            "another uid's dir",
            Some(stat(0, None, Some(0), Some(S_IFDIR | 0o300), Some(false))),
            DirByPath::Judged(Err(NotPrivate::Owner(0))),
        ),
        (
            "a FIFO, the query refused",
            own(S_IFIFO | 0o600, None),
            unread,
        ),
        (
            "a FIFO",
            own(S_IFIFO | 0o600, Some(false)),
            DirByPath::Judged(Err(NotPrivate::Kind("a FIFO"))),
        ),
        (
            "a regular file",
            own(S_IFREG | 0o600, Some(false)),
            DirByPath::Judged(Err(NotPrivate::Kind("a regular file"))),
        ),
    ];
    let mut wrong = Vec::new();
    for (name, looked, expected) in rows {
        let answer = by_path(looked, ME);
        if answer != expected {
            wrong.push(format!("{name}: {answer:?}, expected {expected:?}"));
        }
    }
    assert!(wrong.is_empty(), "A4: {wrong:#?}");
}

/// LAW A5: `lstatx_np` writes within the buffer it is given: of 32 words filled with a
/// pattern, words 18-31 (bytes 144-255, past the 144-byte `struct stat` the kernel copies
/// out on arm64) are the pattern still after a stat of a directory.
///
/// CONTROL: word 17 (`st_qspare[1]`, which the kernel zeroes, XNU
/// bsd/vfs/vfs_syscalls.c:7482-7486) is no longer the pattern, so the call wrote the
/// buffer.
///
/// NC, applied by hand once to owner.rs and reverted: the buffer handed to `lstatx_np`
/// 14 words in (`sb.as_mut_ptr().wrapping_add(14)`, still within its 256 bytes).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn lstatx_np_writes_within_its_buffer() {
    use crate::owner::{look, STAT_WORDS};
    const FILL: u64 = 0xA5A5_A5A5_A5A5_A5A5;
    let scratch = Scratch::new("b");
    let named = std::ffi::CString::new(scratch.0.as_os_str().as_encoded_bytes()).unwrap();
    let mut sb = [FILL; STAT_WORDS];
    let looked = look(&named, &mut sb).expect("a filesec");
    assert_eq!(looked.rc, 0, "{looked:?}");
    let past: Vec<(usize, u64)> = sb
        .iter()
        .copied()
        .enumerate()
        .skip(18)
        .filter(|(_, word)| *word != FILL)
        .collect();
    assert!(past.is_empty(), "A5: written past byte 144: {past:x?}");
    assert!(
        sb.get(17).is_some_and(|word| *word != FILL),
        "CONTROL: word 17 was written"
    );
}
