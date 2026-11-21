// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(clippy::manual_unwrap_or)]

//! Per-claim wall-clock timeout enforcement for the evidence runner
//! (`Astream.Evidence.TlaClaimTimeout`).
//!
//! Bounds every claim command by a strictly positive wall-clock deadline
//! (`DEFAULT_CLAIM_TIMEOUT_SECS` when a claim omits `timeout_secs`, floored at 1 ms via
//! Clean-origin [`claim_timeout_floor`]), captures `stdout` and `stderr` into private
//! unlinked-on-drop temporary files so neither multi-megabyte output nor leaked grandchild
//! file descriptors can deadlock the runner (with zero background threads or closures so
//! `astream-evidence` stays at `0 mandated` in `scripts/verify-ready.sh`), and kills hung
//! child processes fail-closed once [`claim_timed_out`] fires.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(clean_islands)]
#[path = "timeout_island.rs"]
mod timeout_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{claim_elapsed_clamp, claim_timeout_floor};
#[cfg(clean_islands)]
pub use timeout_island::{claim_elapsed_clamp, claim_timeout_floor};

contract_fn! {
    /// Kernel-certified check that `elapsed_ms` has reached or exceeded `limit_ms`
    /// (`limit_ms <= elapsed_ms`), linked via `clean-kernel-defeq` to `claim_timed_out_isl`.
    #[must_use]
    pub const fn claim_timed_out(elapsed_ms: u64, limit_ms: u64) -> bool
    clauses [ensures result == (limit_ms <= elapsed_ms)]
    {
        limit_ms <= elapsed_ms
    }
}

/// Default per-claim wall-clock timeout in seconds (15 minutes) when neither the manifest
/// `[[claim]]` entry (`timeout_secs`) nor the CLI `--timeout-secs` override specifies one.
pub const DEFAULT_CLAIM_TIMEOUT_SECS: u64 = 900;

/// Minimum legal timeout floor in milliseconds (`1 ms`).
pub const MIN_CLAIM_TIMEOUT_MS: u64 = 1;

static CAPTURE_SEQ: AtomicU64 = AtomicU64::new(0);

/// Resolve the effective wall-clock timeout in milliseconds from a claim's optional
/// `timeout_secs` and an optional runner/CLI ceiling override (`override_timeout_ms`).
#[must_use]
pub const fn effective_claim_timeout_ms(
    claim_timeout_secs: Option<u64>,
    override_timeout_ms: Option<u64>,
) -> u64 {
    let base_ms = match claim_timeout_secs {
        Some(secs) => secs.saturating_mul(1_000),
        None => DEFAULT_CLAIM_TIMEOUT_SECS.saturating_mul(1_000),
    };
    let raw_ms = match override_timeout_ms {
        Some(cap_ms) if cap_ms < base_ms => cap_ms,
        _ => base_ms,
    };
    claim_timeout_floor(raw_ms, MIN_CLAIM_TIMEOUT_MS)
}

/// Captured outcome of running a shell command under a wall-clock timeout.
#[derive(Debug)]
pub struct BoundedCommandOutput {
    /// Exit status when the child terminated normally or via `kill() + wait()`.
    pub status: ExitStatus,
    /// Captured `stdout` bytes (complete on normal exit; prefix up to timeout when killed).
    pub stdout: Vec<u8>,
    /// Captured `stderr` bytes (complete on normal exit; prefix up to timeout when killed).
    pub stderr: Vec<u8>,
    /// Whether the command was killed because [`claim_timed_out`] fired.
    pub timed_out: bool,
    /// Clamped elapsed duration (`<= limit_ms` while running; `== limit_ms` on timeout).
    pub elapsed_ms: u64,
    /// Enforced deadline in milliseconds (`>= MIN_CLAIM_TIMEOUT_MS`).
    pub limit_ms: u64,
}

struct TempCaptureFile {
    path: PathBuf,
    reader: File,
}

impl TempCaptureFile {
    fn create(tag: &str) -> io::Result<(Self, File)> {
        let dir = std::env::temp_dir();
        let pid = std::process::id();
        let mut tries = 0u32;
        loop {
            let seq = CAPTURE_SEQ.fetch_add(1, Ordering::Relaxed);
            let path = dir.join(format!("astream_ev_{tag}_{pid}_{seq}.cap"));
            match OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .open(&path)
            {
                Ok(reader) => {
                    let writer = match reader.try_clone() {
                        Ok(w) => w,
                        Err(e) => {
                            let _ = fs::remove_file(&path);
                            return Err(e);
                        }
                    };
                    return Ok((Self { path, reader }, writer));
                }
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists && tries < 64 => {
                    tries = tries.saturating_add(1);
                }
                Err(e) => return Err(e),
            }
        }
    }

    fn read_all(&mut self) -> io::Result<Vec<u8>> {
        self.reader.seek(SeekFrom::Start(0))?;
        let mut out = Vec::new();
        self.reader.read_to_end(&mut out)?;
        Ok(out)
    }
}

impl Drop for TempCaptureFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

/// Spawn `sh -c <command>` in `root` and enforce a hard wall-clock ceiling of `timeout_ms`.
pub fn run_command_with_timeout(
    root: &Path,
    command: &str,
    timeout_ms: u64,
) -> io::Result<BoundedCommandOutput> {
    let limit_ms = claim_timeout_floor(timeout_ms, MIN_CLAIM_TIMEOUT_MS);
    let (mut out_cap, out_writer) = TempCaptureFile::create("out")?;
    let (mut err_cap, err_writer) = TempCaptureFile::create("err")?;

    let mut child = Command::new("sh")
        .arg("-c")
        .arg(command)
        .current_dir(root)
        .stdout(Stdio::from(out_writer))
        .stderr(Stdio::from(err_writer))
        .spawn()?;

    let start = Instant::now();
    let poll_sleep = Duration::from_millis(5);

    loop {
        let raw_elapsed = match u64::try_from(start.elapsed().as_millis()) {
            Ok(ms) => ms,
            Err(_) => u64::MAX,
        };

        if let Some(status) = child.try_wait()? {
            let stdout = out_cap.read_all()?;
            let stderr = err_cap.read_all()?;
            return Ok(BoundedCommandOutput {
                status,
                stdout,
                stderr,
                timed_out: false,
                elapsed_ms: claim_elapsed_clamp(raw_elapsed, limit_ms),
                limit_ms,
            });
        }

        if claim_timed_out(raw_elapsed, limit_ms) {
            match child.kill() {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::InvalidInput => {}
                Err(e) => return Err(e),
            }
            let status = child.wait()?;
            let stdout = out_cap.read_all()?;
            let stderr = err_cap.read_all()?;
            return Ok(BoundedCommandOutput {
                status,
                stdout,
                stderr,
                timed_out: true,
                elapsed_ms: limit_ms,
                limit_ms,
            });
        }

        let rem_ms = limit_ms.saturating_sub(raw_elapsed);
        let sleep_dur = if rem_ms < 5 {
            Duration::from_millis(rem_ms.max(1))
        } else {
            poll_sleep
        };
        thread::sleep(sleep_dur);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fast_command_succeeds_and_hung_command_is_killed_fail_closed() {
        let root = std::env::temp_dir();
        assert_eq!(effective_claim_timeout_ms(None, None), 900_000);
        assert_eq!(effective_claim_timeout_ms(Some(5), None), 5_000);
        assert_eq!(effective_claim_timeout_ms(Some(0), None), 1);
        assert_eq!(effective_claim_timeout_ms(Some(10), Some(250)), 250);

        let ok = run_command_with_timeout(&root, "printf 'hello-timeout'", 5_000).unwrap();
        assert!(!ok.timed_out);
        assert!(ok.status.success());
        assert_eq!(ok.stdout, b"hello-timeout");

        let hung = run_command_with_timeout(&root, "printf 'partial'; exec sleep 10", 60).unwrap();
        assert!(hung.timed_out);
        assert_eq!(hung.elapsed_ms, 60);
        assert_eq!(hung.limit_ms, 60);
        assert!(!hung.status.success());
    }
}
