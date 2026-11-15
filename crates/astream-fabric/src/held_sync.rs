// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(clippy::assign_op_pattern)]

//! Held-store (`<log>.held`) and carried-state (`<log>.state`) snapshot replication for
//! followers and promoted leaders (`REQUIREMENTS-fabric-operations` R4; `DESIGN-aterm-fabric`
//! §10, §15).
//!
//! A leader running retention rules compacts its bulk log to `leader_base` while carrying
//! unread `in/` mail, quiet `Last` rows, pending wills, producer bindings, consumer-group
//! watermarks, and retire charges in `<log>.held` and `<log>.state`. Replicating an
//! authenticated, CRC-checked [`HeldReplicaSnapshot`] lets a replica (or a follower about to
//! be promoted to leader) advance its base monotonically to `leader_base` via
//! [`held_sync_admissible_code`] and [`held_sync_next_base`] (`Astream.Broker.TlaHeldReplicaSync`)
//! and atomically install `<replica>.state` and `<replica>.held`.

use astream_broker::{BrokerLog, Durability, LogIdentity, OpenOptions};
use astream_wire::hash::crc32_ieee_update;
use astream_wire::Offset;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

#[cfg(clean_islands)]
#[path = "held_sync_island.rs"]
mod held_sync_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn held_sync_base_advance(replica_base: u64, leader_base: u64) -> u64 {
    if replica_base < leader_base {
        leader_base
    } else {
        replica_base
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn held_sync_order_ok_code(low: u64, high: u64) -> u64 {
    if high < low {
        0
    } else {
        1
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn held_sync_gate_select(admissible: u64, keep_val: u64, next_val: u64) -> u64 {
    if admissible < 1 {
        keep_val
    } else {
        next_val
    }
}
#[cfg(clean_islands)]
pub use held_sync_island::{
    held_sync_base_advance, held_sync_gate_select, held_sync_order_ok_code,
};

/// Four-parameter held-replica snapshot admission kernel (`held_sync_admissible_code_isl`),
/// composed over Clean-origin [`held_sync_gate_select`] and [`held_sync_order_ok_code`]:
/// returns `1` iff `id_ok > 0 && replica_base <= leader_base && leader_base <= replica_head`.
#[must_use]
pub const fn held_sync_admissible_code(
    id_ok: u64,
    replica_base: u64,
    leader_base: u64,
    replica_head: u64,
) -> u64 {
    held_sync_gate_select(
        id_ok,
        0,
        held_sync_gate_select(
            held_sync_order_ok_code(replica_base, leader_base),
            0,
            held_sync_order_ok_code(leader_base, replica_head),
        ),
    )
}

/// Three-parameter monotone replica-base advance (`held_sync_next_base_isl`), composed over
/// Clean-origin [`held_sync_gate_select`] and [`held_sync_base_advance`].
#[must_use]
pub const fn held_sync_next_base(admissible: u64, replica_base: u64, leader_base: u64) -> u64 {
    held_sync_gate_select(
        admissible,
        replica_base,
        held_sync_base_advance(replica_base, leader_base),
    )
}

contract_fn! {
    /// Verified check that a held-replica snapshot sync admission code equals `1`, linked via
    /// `clean-kernel-defeq` to `held_sync_code_is_admissible_isl`.
    #[must_use]
    pub const fn held_sync_code_is_admissible(code: u64) -> bool
    clauses [ensures result == (code == 1)]
    {
        code == 1
    }
}

/// Wire magic for [`HeldReplicaSnapshot`] frames (`"AHRP"`).
pub const HELD_SNAPSHOT_MAGIC: [u8; 4] = *b"AHRP";

/// Format version `1` for [`HeldReplicaSnapshot`].
pub const HELD_SNAPSHOT_VERSION: u8 = 1;

/// Hard ceiling (64 MiB) on an encoded [`HeldReplicaSnapshot`] or individual sidecar payload.
pub const MAX_HELD_SNAPSHOT_BYTES: usize = 64 * 1024 * 1024;

/// Fixed header width: `magic[4] + version[1] + flags[1] + reserved[2] + id[16] + gen[8] + base[8] + state_len[4] + held_len[4] = 48` (+ trailing `crc32[4]`).
const SNAPSHOT_HEADER_LEN: usize = 48;

const FLAG_HAS_STATE: u8 = 0x01;
const FLAG_HAS_HELD: u8 = 0x02;

/// Portable snapshot of a leader's compacted base, `<log>.state`, and `<log>.held`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeldReplicaSnapshot {
    /// Leader's [`LogIdentity`] at export time.
    pub leader_id: LogIdentity,
    /// Leader's compacted retention base offset (`<log>.base`).
    pub leader_base: u64,
    /// Exact bytes of `<leader>.state`, when present at export time.
    pub state_bytes: Option<Vec<u8>>,
    /// Exact bytes of `<leader>.held`, when present at export time.
    pub held_bytes: Option<Vec<u8>>,
}

/// Outcome of installing a [`HeldReplicaSnapshot`] onto a replica log.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HeldSyncOutcome {
    /// Replica base before installation.
    pub previous_base: u64,
    /// Replica base after installation (`>= previous_base`).
    pub installed_base: u64,
    /// Whether `<replica>.state` was written.
    pub installed_state: bool,
    /// Whether `<replica>.held` was written.
    pub installed_held: bool,
}

fn state_path(log: &Path) -> PathBuf {
    let mut p = log.to_path_buf();
    p.as_mut_os_string().push(".state");
    p
}

fn create_like(path: &Path, perms: &std::fs::Permissions) -> io::Result<File> {
    let _ = std::fs::remove_file(path);
    let mut opts = std::fs::OpenOptions::new();
    opts.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
        opts.mode(perms.mode());
    }
    let f = opts.open(path)?;
    if let Err(e) = f.set_permissions(perms.clone()) {
        drop(f);
        let _ = std::fs::remove_file(path);
        return Err(e);
    }
    Ok(f)
}

fn flush_file(f: &File, _at: &Path) -> io::Result<()> {
    astream_sys::full_sync(f)
}

fn rename_path(from: &Path, to: &Path) -> io::Result<()> {
    std::fs::rename(from, to)
}

#[cfg(unix)]
fn sync_parent_dir(path: &Path) -> io::Result<()> {
    let parent = match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let res = File::open(parent).and_then(|dir| astream_sys::full_sync(&dir));
    match res {
        Ok(()) => Ok(()),
        Err(e) if astream_sys::dir_flush_unavailable(&e) => Ok(()),
        Err(e) => Err(e),
    }
}

#[cfg(not(unix))]
fn sync_parent_dir(_path: &Path) -> io::Result<()> {
    Ok(())
}

fn held_sidecar_path(log: &Path) -> PathBuf {
    let mut p = log.to_path_buf();
    p.as_mut_os_string().push(".held");
    p
}

fn temp_sidecar_path(sidecar: &Path) -> PathBuf {
    let mut p = sidecar.to_path_buf();
    p.as_mut_os_string().push(".sync.tmp");
    p
}

fn read_optional_bounded(path: &Path) -> io::Result<Option<Vec<u8>>> {
    let mut f = match File::open(path) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let meta = f.metadata()?;
    let len_u64 = meta.len();
    if len_u64 > MAX_HELD_SNAPSHOT_BYTES as u64 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "held/state sidecar exceeds MAX_HELD_SNAPSHOT_BYTES",
        ));
    }
    let cap = if (len_u64 as usize) < MAX_HELD_SNAPSHOT_BYTES {
        len_u64 as usize
    } else {
        MAX_HELD_SNAPSHOT_BYTES
    };
    let mut buf = {
        let _ = cap;
        Vec::new()
    };
    let read_n = (&mut f)
        .take((MAX_HELD_SNAPSHOT_BYTES as u64).saturating_add(1))
        .read_to_end(&mut buf)?;
    if read_n > MAX_HELD_SNAPSHOT_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "sidecar grew past MAX_HELD_SNAPSHOT_BYTES during export",
        ));
    }
    Ok(Some(buf))
}

fn write_sidecar_atomic(log_for_perms: &Path, dst: &Path, bytes: &[u8]) -> io::Result<()> {
    let perms = std::fs::metadata(log_for_perms)?.permissions();
    let tmp = temp_sidecar_path(dst);
    let mut file = create_like(&tmp, &perms)?;
    file.write_all(bytes)?;
    flush_file(&file, &tmp)?;
    drop(file);
    rename_path(&tmp, dst)?;
    sync_parent_dir(dst)
}

fn remove_if_present(path: &Path) -> io::Result<()> {
    match std::fs::remove_file(path) {
        Ok(()) => sync_parent_dir(path),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(e),
    }
}

fn apply_optional_sidecar(
    log_for_perms: &Path,
    dst: &Path,
    bytes: Option<&[u8]>,
) -> io::Result<bool> {
    match bytes {
        Some(b) => {
            write_sidecar_atomic(log_for_perms, dst, b)?;
            Ok(true)
        }
        None => {
            remove_if_present(dst)?;
            Ok(false)
        }
    }
}

fn restore_sidecar_backups(
    log_for_perms: &Path,
    s_path: &Path,
    prev_state: Option<&[u8]>,
    h_path: &Path,
    prev_held: Option<&[u8]>,
) {
    let _ = apply_optional_sidecar(log_for_perms, s_path, prev_state);
    let _ = apply_optional_sidecar(log_for_perms, h_path, prev_held);
}

fn open_cold_strict(path: &Path) -> io::Result<BrokerLog> {
    BrokerLog::open_opts(
        path,
        OpenOptions::new(Durability::Strict).with_resident_budget(0),
        BrokerLog::prepare_nothing,
    )
}

/// Export `<leader_log>`'s current [`LogIdentity`], compacted `base_offset`, `<log>.state`,
/// and `<log>.held` into a self-contained [`HeldReplicaSnapshot`].
pub fn export_held_snapshot(leader_log: &Path) -> io::Result<HeldReplicaSnapshot> {
    let mut log = open_cold_strict(leader_log)?;
    let leader_id = log.identity();
    let leader_base = log.base().0;
    log.close_clean()?;
    drop(log);
    let state_bytes = read_optional_bounded(&state_path(leader_log))?;
    let held_bytes = read_optional_bounded(&held_sidecar_path(leader_log))?;
    Ok(HeldReplicaSnapshot {
        leader_id,
        leader_base,
        state_bytes,
        held_bytes,
    })
}

/// Encode `snap` into a CRC-32-authenticated binary frame bounded by [`MAX_HELD_SNAPSHOT_BYTES`].
pub fn encode_held_snapshot(snap: &HeldReplicaSnapshot) -> io::Result<Vec<u8>> {
    let s_len = match &snap.state_bytes {
        Some(b) => b.len(),
        None => 0,
    };
    let h_len = match &snap.held_bytes {
        Some(b) => b.len(),
        None => 0,
    };
    let total_payload = SNAPSHOT_HEADER_LEN
        .saturating_add(s_len)
        .saturating_add(h_len)
        .saturating_add(4);
    if total_payload > MAX_HELD_SNAPSHOT_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "HeldReplicaSnapshot exceeds MAX_HELD_SNAPSHOT_BYTES",
        ));
    }
    let Ok(s_u32) = u32::try_from(s_len) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "state sidecar exceeds u32::MAX",
        ));
    };
    let Ok(h_u32) = u32::try_from(h_len) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "held sidecar exceeds u32::MAX",
        ));
    };

    let mut flags = 0u8;
    if snap.state_bytes.is_some() {
        flags = flags | (FLAG_HAS_STATE);
    }
    if snap.held_bytes.is_some() {
        flags = flags | (FLAG_HAS_HELD);
    }

    let out_cap = if total_payload < MAX_HELD_SNAPSHOT_BYTES {
        total_payload
    } else {
        MAX_HELD_SNAPSHOT_BYTES
    };
    let mut out = {
        let _ = out_cap;
        Vec::new()
    };
    out.extend_from_slice(&HELD_SNAPSHOT_MAGIC);
    out.push(HELD_SNAPSHOT_VERSION);
    out.push(flags);
    out.extend_from_slice(&[0u8; 2]);
    out.extend_from_slice(&snap.leader_id.id);
    out.extend_from_slice(&snap.leader_id.generation.to_le_bytes());
    out.extend_from_slice(&snap.leader_base.to_le_bytes());
    out.extend_from_slice(&s_u32.to_le_bytes());
    out.extend_from_slice(&h_u32.to_le_bytes());
    if let Some(sb) = &snap.state_bytes {
        out.extend_from_slice(sb);
    }
    if let Some(hb) = &snap.held_bytes {
        out.extend_from_slice(hb);
    }
    let crc = crc32_ieee_update(0xFFFF_FFFF, &out) ^ 0xFFFF_FFFF;
    out.extend_from_slice(&crc.to_le_bytes());
    Ok(out)
}

/// Decode and CRC-verify a [`HeldReplicaSnapshot`] produced by [`encode_held_snapshot`].
pub fn decode_held_snapshot(raw: &[u8]) -> io::Result<HeldReplicaSnapshot> {
    if raw.len() < SNAPSHOT_HEADER_LEN + 4 || raw.len() > MAX_HELD_SNAPSHOT_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid HeldReplicaSnapshot length",
        ));
    }
    let body_end = raw.len() - 4;
    let Some(body) = raw.get(..body_end) else {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "short snapshot"));
    };
    let Some(crc_slice) = raw.get(body_end..) else {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "missing crc"));
    };
    let &[c0, c1, c2, c3] = crc_slice else {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "short crc"));
    };
    let want_crc = u32::from_le_bytes([c0, c1, c2, c3]);
    let got_crc = crc32_ieee_update(0xFFFF_FFFF, body) ^ 0xFFFF_FFFF;
    if want_crc != got_crc {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "HeldReplicaSnapshot CRC-32 mismatch",
        ));
    }

    let Some(hdr) = body.get(..SNAPSHOT_HEADER_LEN) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "HeldReplicaSnapshot header truncated",
        ));
    };
    let &[m0, m1, m2, m3, ver, flags, _r0, _r1, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, g0, g1, g2, g3, g4, g5, g6, g7, b0, b1, b2, b3, b4, b5, b6, b7, s0, s1, s2, s3, h0, h1, h2, h3] =
        hdr
    else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "HeldReplicaSnapshot header size mismatch",
        ));
    };
    if [m0, m1, m2, m3] != HELD_SNAPSHOT_MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "HeldReplicaSnapshot bad magic",
        ));
    }
    if ver != HELD_SNAPSHOT_VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "unsupported HeldReplicaSnapshot version",
        ));
    }
    if (flags & !(FLAG_HAS_STATE | FLAG_HAS_HELD)) != 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "unknown HeldReplicaSnapshot flags",
        ));
    }

    let id_bytes = [
        i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15,
    ];
    let gen_val = u64::from_le_bytes([g0, g1, g2, g3, g4, g5, g6, g7]);
    let leader_base = u64::from_le_bytes([b0, b1, b2, b3, b4, b5, b6, b7]);
    let s_len = u32::from_le_bytes([s0, s1, s2, s3]) as usize;
    let h_len = u32::from_le_bytes([h0, h1, h2, h3]) as usize;

    let expected_body = SNAPSHOT_HEADER_LEN
        .saturating_add(s_len)
        .saturating_add(h_len);
    if expected_body != body.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "HeldReplicaSnapshot payload length mismatch",
        ));
    }

    let s_end = SNAPSHOT_HEADER_LEN.saturating_add(s_len);
    let state_bytes = if (flags & FLAG_HAS_STATE) != 0 {
        let Some(sb) = body.get(SNAPSHOT_HEADER_LEN..s_end) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "short state"));
        };
        Some(sb.to_vec())
    } else if s_len == 0 {
        None
    } else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "state_len non-zero without FLAG_HAS_STATE",
        ));
    };

    let held_bytes = if (flags & FLAG_HAS_HELD) != 0 {
        let Some(hb) = body.get(s_end..expected_body) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "short held"));
        };
        Some(hb.to_vec())
    } else if h_len == 0 {
        None
    } else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "held_len non-zero without FLAG_HAS_HELD",
        ));
    };

    Ok(HeldReplicaSnapshot {
        leader_id: LogIdentity {
            id: id_bytes,
            generation: gen_val,
        },
        leader_base,
        state_bytes,
        held_bytes,
    })
}

/// Atomically install `snap` onto `<replica_log>`:
///
/// 1. Verifies `<replica_log>`'s [`LogIdentity`] matches `snap.leader_id` (same `id` and
///    `replica.generation <= snap.leader_id.generation`), and checks
///    `replica_base <= snap.leader_base <= replica_head` via Clean-origin
///    [`held_sync_admissible_code`].
/// 2. When `replica_base < snap.leader_base`, compacts `<replica_log>` up to
///    [`held_sync_next_base`] (`snap.leader_base`) so the replica's suffix starts at the
///    exact base `snap` was cut for.
/// 3. Atomically writes `<replica_log>.state` and `<replica_log>.held` via crash-safe
///    `tmp + flush + rename + parent-dir sync`, then reopens `<replica_log>` to validate
///    that both sidecars load cleanly.
pub fn install_held_snapshot(
    replica_log: &Path,
    snap: &HeldReplicaSnapshot,
) -> io::Result<HeldSyncOutcome> {
    let mut rep = open_cold_strict(replica_log)?;
    let rep_id = rep.identity();
    let rep_base = rep.base().0;
    let rep_head = rep.head().0;
    let id_ok: u64 =
        if rep_id.id == snap.leader_id.id && rep_id.generation <= snap.leader_id.generation {
            1
        } else {
            0
        };
    let adm = held_sync_admissible_code(id_ok, rep_base, snap.leader_base, rep_head);
    if !held_sync_code_is_admissible(adm) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "refusing HeldReplicaSnapshot: id_ok={id_ok} replica=[{rep_base}..{rep_head}) snap_base={}",
                snap.leader_base
            ),
        ));
    }
    let target_base = held_sync_next_base(adm, rep_base, snap.leader_base);
    if rep_base < target_base {
        rep.retain_before_carrying_state(Offset(target_base))?;
    }
    rep.close_clean()?;
    drop(rep);

    let s_path = state_path(replica_log);
    let h_path = held_sidecar_path(replica_log);
    let prev_state = read_optional_bounded(&s_path)?;
    let prev_held = read_optional_bounded(&h_path)?;

    let installed_state =
        match apply_optional_sidecar(replica_log, &s_path, snap.state_bytes.as_deref()) {
            Ok(flag) => flag,
            Err(e) => {
                restore_sidecar_backups(
                    replica_log,
                    &s_path,
                    prev_state.as_deref(),
                    &h_path,
                    prev_held.as_deref(),
                );
                return Err(e);
            }
        };
    let installed_held =
        match apply_optional_sidecar(replica_log, &h_path, snap.held_bytes.as_deref()) {
            Ok(flag) => flag,
            Err(e) => {
                restore_sidecar_backups(
                    replica_log,
                    &s_path,
                    prev_state.as_deref(),
                    &h_path,
                    prev_held.as_deref(),
                );
                return Err(e);
            }
        };

    // Verify the replica reopens cleanly with the newly installed sidecars, rolling back
    // sidecars on failure so a corrupt snapshot never leaves `<replica_log>` unopenable.
    let mut reopened = match open_cold_strict(replica_log) {
        Ok(log) => log,
        Err(e) => {
            restore_sidecar_backups(
                replica_log,
                &s_path,
                prev_state.as_deref(),
                &h_path,
                prev_held.as_deref(),
            );
            return Err(e);
        }
    };
    let installed_base = reopened.base().0;
    reopened.close_clean()?;
    drop(reopened);

    Ok(HeldSyncOutcome {
        previous_base: rep_base,
        installed_base,
        installed_state,
        installed_held,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct ScopedTempDir(PathBuf);

    impl ScopedTempDir {
        fn new(tag: &str) -> Self {
            static SEQ: AtomicU64 = AtomicU64::new(0);
            let n = SEQ.fetch_add(1, Ordering::Relaxed);
            let p = std::env::temp_dir().join(format!(
                "astream-held-sync-{}-{}-{}",
                std::process::id(),
                tag,
                n
            ));
            let _ = std::fs::remove_dir_all(&p);
            std::fs::create_dir_all(&p).expect("create temp dir");
            Self(p)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for ScopedTempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn held_snapshot_roundtrips_and_enables_replica_held_reads() {
        use astream_broker::{parse_rules, Broker, Client};
        use astream_wire::Filter;

        let dir = ScopedTempDir::new("rt");
        let leader_path = dir.path().join("leader.log");
        let replica_path = dir.path().join("replica.log");

        let rules = parse_rules(
            "prefix bytes=512 /f/t/pub/*/*/ev\n\
             hold bytes=65536 /f/t/in/>\n\
             default bytes=65536\n",
        )
        .expect("parse rules");

        let replica = Broker::open_replica(&replica_path).expect("open replica");
        let rep_handle = replica.serve_tcp("127.0.0.1:0").expect("serve replica");
        let rep_addr = rep_handle.tcp_addr().expect("tcp addr").to_string();
        let followers = vec![rep_addr];
        let leader = Broker::open_replicated(&leader_path, &followers, 1).expect("open leader");
        leader.set_retention(rules).expect("set retention");
        let ldr_handle = leader.serve_tcp("127.0.0.1:0").expect("serve leader");
        let ldr_addr = ldr_handle.tcp_addr().expect("leader tcp addr");
        let mut client = Client::connect_tcp(ldr_addr).expect("connect leader");

        // Publish held mail at offset 0, followed by bulk `ev` records so retention moves base > 0.
        let ack0 = client
            .publish(1, 1, "/f/t/in/n1/s1/mgr/task", b"important-held-mail")
            .expect("pub mail");
        assert_eq!(ack0, (0, false));

        for seq in 2..=30u64 {
            client
                .publish(1, seq, "/f/t/pub/n1/s1/ev", &[b'x'; 64])
                .expect("pub ev");
        }
        drop(client);
        let tick = leader
            .retention_tick_at(1_800_000_000_000)
            .expect("retention tick");
        assert!(tick.base >= 20, "unexpected tick base {}", tick.base);
        drop(ldr_handle);
        drop(leader);
        drop(rep_handle);
        drop(replica);

        // Export from leader, roundtrip wire bytes, and install on replica.
        let snap = export_held_snapshot(&leader_path).expect("export");
        assert!(snap.leader_base >= 20);
        assert!(snap.held_bytes.is_some());
        let wire = encode_held_snapshot(&snap).expect("encode");
        let decoded = decode_held_snapshot(&wire).expect("decode");
        assert_eq!(decoded, snap);

        let outcome = install_held_snapshot(&replica_path, &decoded).expect("install");
        assert_eq!(outcome.previous_base, 0);
        assert_eq!(outcome.installed_base, snap.leader_base);
        assert!(outcome.installed_held);

        // Replica now serves the held mail at offset 0 below its compacted base!
        let mut rep_log = BrokerLog::open(&replica_path).expect("reopen replica log");
        let in_filter = Filter::new("/f/t/in/>").expect("in filter");
        let head = rep_log.head().0;
        let (rows, _next) = rep_log.fetch(0, &in_filter, 16, 1024, head);
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].seq, Offset(0));
        assert_eq!(rows[0].body, b"important-held-mail");
        rep_log.close_clean().expect("close replica");
    }

    #[test]
    fn held_snapshot_rejects_corrupt_crc_and_preserves_roundtrip_without_retention() {
        let dir = ScopedTempDir::new("crc");
        let leader_a = dir.path().join("a.log");

        let mut la = BrokerLog::open(&leader_a).expect("open a");
        la.publish(1, 1, "/f/t/pub/n1/s1/ev".to_string(), b"a".to_vec())
            .expect("pub");
        la.close_clean().expect("close a");
        drop(la);

        let snap = export_held_snapshot(&leader_a).expect("export a");
        let mut wire = encode_held_snapshot(&snap).expect("encode");
        wire[10] ^= 0xFF;
        assert!(decode_held_snapshot(&wire).is_err());

        {
            let replica_b = dir.path().join("b.log");
            let mut rb = BrokerLog::open(&replica_b).expect("open b");
            rb.publish(2, 1, "/f/t/pub/n1/s1/ev".to_string(), b"b".to_vec())
                .expect("pub b");
            rb.close_clean().expect("close b");
            drop(rb);
            // Different log identity is rejected fail-closed.
            assert!(install_held_snapshot(&replica_b, &snap).is_err());
        }

        // Corrupt held_bytes in snapshot rolls back `<leader_a>` sidecars on install failure
        // so the log still reopens cleanly.
        let mut bad_snap = snap.clone();
        bad_snap.held_bytes = Some(b"not-a-valid-held-sidecar".to_vec());
        assert!(install_held_snapshot(&leader_a, &bad_snap).is_err());
        let mut reopened_a = BrokerLog::open(&leader_a).expect("reopen a after rollback");
        assert_eq!(reopened_a.head().0, 1);
        reopened_a.close_clean().expect("close reopened a");
    }
}
