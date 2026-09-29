//! The cooperative effect seam: the three doors a program reads the world through,
//! and the typed tape of what it read.

/// The effect seam a program is written against. Implemented by
/// [`RecordingSeam`](crate::RecordingSeam) (real OS, taped) and
/// [`ReplaySeam`](crate::ReplaySeam) (tape only, no OS).
pub trait EffectSeam {
    /// Read a wall-clock value, in nanoseconds.
    fn now_nanos(&mut self) -> u64;
    /// Draw the next random word.
    fn next_rand(&mut self) -> u64;
    /// Read a file's bytes. A read that fails yields empty bytes — the lossy
    /// door; use [`try_read_file`](EffectSeam::try_read_file) when the program
    /// must see (and the tape must carry) the failure.
    fn read_file(&mut self, path: &str) -> Vec<u8>;
    /// Read a file's bytes, surfacing an I/O failure as `Err`. The default just
    /// wraps [`read_file`](EffectSeam::read_file) in `Ok`; the recording and
    /// replay seams override it so a failed read is taped as
    /// [`EffectRecord::FileErr`] and replayed as the same [`std::io::ErrorKind`].
    fn try_read_file(&mut self, path: &str) -> std::io::Result<Vec<u8>> {
        Ok(self.read_file(path))
    }
}

/// One recorded effect, tagged by kind so replay can detect a kind mismatch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EffectRecord {
    /// A wall-clock read (nanoseconds).
    Clock(u64),
    /// A random word.
    Rand(u64),
    /// A file read that succeeded: the path requested and the bytes returned.
    File {
        /// The path read.
        path: String,
        /// The bytes returned.
        bytes: Vec<u8>,
    },
    /// A file read that FAILED: the path requested and the I/O error kind the OS
    /// returned. Distinct from `File { bytes: [] }` (an empty file read cleanly)
    /// so a tape written by [`RecordingSeam`](crate::RecordingSeam) — the audit
    /// trail for "what did this program read?" — can tell "read `/etc/shadow`,
    /// got 1 KiB" from "read `/etc/shadow`, permission denied", and replay
    /// reproduces the failure rather than an empty success. The distinction is
    /// the RECORDING SEAM's, not the type's: the other producer of this log, the
    /// Linux `astream-host::foreign` tracer, does not emit this variant yet — it
    /// still tapes a failed read as `File { bytes: [] }`, so a foreign-process
    /// tape cannot be read for that difference.
    FileErr {
        /// The path the read was attempted on.
        path: String,
        /// The error kind the real read returned.
        kind: std::io::ErrorKind,
    },
}

/// An ordered tape of the effects a program consumed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EffectsLog(pub Vec<EffectRecord>);
