// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE READ-ONLY OPEN CHECK ([`BrokerLog::check_open`]): whether an open would serve a log as
//! its files stand, judged by the open's own steps with every write left out.
//!
//! An open writes even where it changes nothing a reader sees. It records its run in
//! `<log>.id` (the tier, the boot and `Open`, then the durable floor after its flush), cuts a
//! torn tail, finishes or undoes an offline seal's switch or a compaction a crash
//! interrupted, cuts the held store back, and syncs the directory; and a clean close rewrites
//! `.id` again. So an open closed at once is no probe: a caller that asks whether a log opens
//! before it gives the log up (aterm's `--retire-log`) and says it left the log as it was would
//! have rewritten `.id` before saying so. The check takes the open's steps in the open's order
//! (`BrokerLog::open_core`) and writes none of them:
//!
//! 1. The log is opened READ-WRITE, as the open opens it, but non-blocking (a FIFO planted at
//!    the name answers at once) and never created: no log is `NotFound`, and a log the open
//!    could not open for writing (its mode, an immutable flag, a read-only volume) is refused
//!    with the open's own error, `PermissionDenied` for its mode. Nothing is written through
//!    it. A folder is refused as the open refuses it (`IsADirectory`), and any other path
//!    that is not a regular file `InvalidInput`. Its lock is taken as an open takes it, so a
//!    log another open holds is refused `AlreadyExists`, and it is released when the check
//!    returns.
//! 2. An offline seal's switch a crash interrupted is judged as the open's settle judges it
//!    (`offline_seal::pending`): a marker this build does not read, or a log changed since
//!    its marker, refuses as the open refuses; a staging no marker covers, which the open
//!    would undo, leaves the log as it stands and is passed over.
//! 3. The binding. With a key the check is the BOUND open's (`open_encrypted_bound`):
//!    `<log>.seal` must authenticate under the key, and a keyed log without one is refused
//!    (one never written to, with no sidecar at all, is an empty log that opens). With no key
//!    a log beside a `.seal` is refused, as every keyless open refuses it.
//! 4. A compaction's intent is judged as the open's recovery judges it (`compact::pending`):
//!    a log that starts with neither frame it names refuses, and so does one whose rename
//!    landed where the finish would refuse (a base sidecar at neither base, a carried state
//!    gone); one it would discard, or that does not read, is passed over, since the open
//!    leaves the log, its base and its state.
//! 5. The base, the carried state and the held store are read and authenticated as the open
//!    reads them, the held store opened read-write as the open opens it for the appends it
//!    makes later, so one the open could not append to is refused as the open refuses it.
//! 6. The identity sidecar, its durable floor and its last run, then the scan and the
//!    recovery's classification, exactly the open's: a corrupt record, or one in a newer
//!    format, is refused with the open's own error, and a torn tail the open would cut is
//!    counted ([`OpenCheck::Opens`]'s `torn`), not cut.
//!
//! WHAT THE ANSWER DOES NOT COVER. Where the open would first settle a step a crash
//! interrupted (step 2's switch, step 4's compaction), the check answers
//! [`OpenCheck::Unsettled`] once every refusal of that settle is ruled out, so the open's settle
//! can then fail only by a write, and judges no further: what that open finds after its writes
//! is not read. The anti-rollback watermark (`<log>.hw`) is not read, so a verified open can
//! refuse a log the check says opens. An embedder's own `prepare` verdict is not taken: the
//! check judges as an open whose prepare said nothing (`Prepared::Nothing`), at the boot it
//! detects. And an open can still fail where no look that writes nothing can see: a write it
//! makes that the folder refuses (it replaces `<log>.id` through a temporary and a rename,
//! which a folder its user cannot write to refuses) or that the volume refuses (full, or an
//! I/O error). Claim `broker.check-open`.

use super::*;

/// What [`BrokerLog::check_open`] found of a log it could judge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum OpenCheck {
    /// An open would serve the log: its records from `base` up to `head` read (and, sealed,
    /// authenticate), and `torn` bytes past them are a torn tail the open would cut (`0` when
    /// there is none).
    Opens {
        /// The retention base: the offset of the first stored record.
        base: Offset,
        /// The offset the next record would take.
        head: Offset,
        /// The bytes past the last whole record that the open would cut.
        torn: u64,
    },
    /// An open would first settle this step a crash interrupted, by writing, and then judge
    /// the log that leaves. The check writes nothing, so it names the step and judges no
    /// further.
    Unsettled(InterruptedStep),
}

/// A step a crash interrupted, which an open settles before it reads the log
/// ([`OpenCheck::Unsettled`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum InterruptedStep {
    /// An offline seal's switch whose marker (`<log>.sealmove`) is durable: the open finishes
    /// it, and the log is sealed from then on (`BrokerLog::seal_plaintext`).
    SealSwitch,
    /// A compaction whose rename landed (its intent, `<log>.compact`): the open finishes it,
    /// and the log's base is `new_base` from then on.
    Compaction {
        /// The base the compaction moves the log to.
        new_base: u64,
    },
}

impl BrokerLog {
    /// A CHECK THAT WRITES NOTHING of whether an open would serve the log at `path` as its
    /// files stand: under `key` by `open_encrypted_bound`'s rules (with `at-rest`), or
    /// keyless by [`open_with`]'s. It opens the log and its held store read-write, as the
    /// open does, and writes through neither: no file is created, cut, flushed, renamed or
    /// removed, and every sidecar stays byte for byte as it was, `<log>.id` included, which
    /// every open rewrites (`check_open.rs` has the steps, and what the answer does not
    /// cover). The log's lock is held while it reads and released when it returns. Claim
    /// `broker.check-open`.
    ///
    /// [`open_with`]: BrokerLog::open_with
    ///
    /// # Errors
    /// What the open would refuse, by the open's own kind: `NotFound` for no log (none is
    /// created); `AlreadyExists` while another open holds it; the open's own refusal of a log
    /// or a held store it could not open for writing (`PermissionDenied` for its mode), and of
    /// a folder (`IsADirectory`); `InvalidData` for a corrupt record, a sealed log with no key
    /// or the wrong one, a keyed log with no `<log>.seal`, a sidecar that does not read or
    /// authenticate, or a seal's switch or a compaction that cannot be settled; `Unsupported`
    /// for a record in a newer format, or a key given to a build without `at-rest`;
    /// `InvalidInput` for any other path that is not a regular file; and the I/O error of any
    /// read.
    pub fn check_open(path: impl AsRef<Path>, key: Option<[u8; 32]>) -> io::Result<OpenCheck> {
        let mut key = key;
        let checked = check(path.as_ref(), key.as_ref());
        if let Some(k) = key.as_mut() {
            k.fill(0);
            std::hint::black_box(k);
        }
        checked
    }
}

/// The log's file, opened read-write as an open opens it (writing nothing) and locked as an
/// open locks it, released on drop.
struct Locked(File);

impl Locked {
    fn take(path: &Path) -> io::Result<Locked> {
        let file = astream_sys::open_nonblocking_rw(path, astream_sys::Links::Follow)?;
        if !file.metadata()?.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("{} is not a regular file, so no log", path.display()),
            ));
        }
        lock_exclusive(&file, path)?;
        let locked = Locked(file);
        if !astream_sys::file_matches_path(&locked.0, path)? {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "log ownership changed during the check",
            ));
        }
        Ok(locked)
    }
}

impl Drop for Locked {
    fn drop(&mut self) {
        let _ = self.0.unlock();
    }
}

fn check(path: &Path, key: Option<&[u8; 32]>) -> io::Result<OpenCheck> {
    let locked = Locked::take(path)?;
    if offline_seal::pending(path)? {
        return Ok(OpenCheck::Unsettled(InterruptedStep::SealSwitch));
    }
    // Read as the open reads it, through the scan's window (`open_scan.rs`).
    let len = locked.0.metadata()?.len();
    let at_rest = match key {
        Some(key) => match bound(path, len == 0, key)? {
            Some(at_rest) => Some(at_rest),
            None => {
                return Ok(OpenCheck::Opens {
                    base: Offset::ZERO,
                    head: Offset::ZERO,
                    torn: 0,
                })
            }
        },
        None => {
            refuse_keyless_sealed(path)?;
            None
        }
    };
    let key_ref = match &at_rest {
        Some(k) => Some(k.as_ref()),
        None => None,
    };
    #[cfg(feature = "retention")]
    if let Some(new_base) = crate::compact::pending(
        path,
        open_scan::first_frame(&locked.0, len)?.as_deref(),
        key_ref,
    )? {
        return Ok(OpenCheck::Unsettled(InterruptedStep::Compaction {
            new_base,
        }));
    }
    let base = read_base(path)?;
    read_state(path, key_ref, base.0)?;
    #[cfg(feature = "retention")]
    crate::held::HeldStore::read(path, key_ref, base.0)?;
    let prior = logid::read(&Dir::Os(path.to_path_buf()))?;
    let boot = Boot::Detect.resolve();
    let boot_volume = on_boot_volume(&locked.0);
    let floor = prior.floor(base.0);
    let unclean = prior.unclean(None, boot);
    let open_scan::Streamed { scan, rest } = open_scan::scan(
        &locked.0,
        open_scan::Reading::shipped(),
        key_ref,
        base.0,
        floor,
        Mutation::Off,
        &mut open_scan::Discard,
    )?;
    let judged = recover::classify(
        &scan,
        &recover::Judge {
            rest: &rest,
            key: key_ref,
            base: base.0,
            floor,
            unclean_relaxed: unclean.is_some() && prior.served_relaxed() && floor.is_some(),
            prior_relaxed: prior.served_relaxed(),
            same_boot: prior.same_boot(boot, boot_volume),
            mutation: Mutation::Off,
        },
    );
    match judged {
        Classified::Keep { keep, records, .. } => Ok(OpenCheck::Opens {
            base,
            head: Offset(base.0.saturating_add(records as u64)),
            torn: len.saturating_sub(keep as u64),
        }),
        Classified::Corrupt {
            offset,
            at_byte,
            reason,
            repair_at,
        } => Err(
            match BrokerLog::refuse_or_repair(
                path,
                usize::try_from(len).unwrap_or(usize::MAX),
                (false, key_ref.is_some()),
                (offset, at_byte),
                &reason,
                repair_at,
            ) {
                Err(refused) => refused,
                // An open that does not repair refuses every corrupt record; this arm is
                // that refusal's kind if it ever did not.
                Ok(()) => io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "{}: corrupt record at offset {offset} (byte {at_byte}): {reason}",
                        path.display()
                    ),
                ),
            },
        ),
        Classified::Newer {
            offset,
            at_byte,
            version,
        } => Err(newer_record(path, offset, at_byte, version)),
    }
}

/// The bound open's key for the log at `path` (`empty`: it holds no byte), read without
/// writing: its `<log>.seal` authenticated under `key`, or the bound open's refusal of a log
/// with none. `None` for a log never written to (empty, with no sidecar), where the open
/// would mint a binding and serve an empty log.
#[cfg(feature = "at-rest")]
fn bound(path: &Path, empty: bool, key: &[u8; 32]) -> io::Result<Option<AtRestKey>> {
    match read_seal(path, key)? {
        Some(seal_id) => Ok(Some(AtRestKey {
            key: *key,
            seal_id: Some(seal_id),
        })),
        None if is_virgin_empty_log(path, empty)? => Ok(None),
        None => Err(unbound_refusal(path)),
    }
}

/// A build without `at-rest` opens no log under a key.
#[cfg(not(feature = "at-rest"))]
fn bound(_path: &Path, _empty: bool, _key: &[u8; 32]) -> io::Result<Option<AtRestKey>> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "at-rest encryption is not compiled into this build",
    ))
}

#[cfg(all(test, feature = "retention"))]
#[path = "check_open_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "check_open_basic_tests.rs"]
mod basic_tests;
