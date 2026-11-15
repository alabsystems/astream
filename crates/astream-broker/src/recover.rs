// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! RECOVERY's classifier: what the open does with the bytes after the log's intact
//! prefix — keep them, cut them, or refuse the log — once the recovery scan
//! ([`scan_from`](crate::store::scan_from)) has found where that prefix ends.
//!
//! # Two sets of rules, chosen by what the log's sidecar knows
//!
//! **The durable floor unknown** (no sidecar, a FORMAT 1 sidecar, the open right after
//! a revert): the rules that predate the floor, verbatim. A torn tail — an incomplete
//! last frame, or nothing but zeros — is cut; anything else after the prefix is
//! refused until an operator repairs the log. Every log a sealing build has not yet
//! opened classifies exactly as it did before, marked records being ordinary records.
//!
//! **The durable floor known** (a FORMAT 2 sidecar: everything below the floor was
//! flushed in full by an open or a clean close). Above the floor the log is a run of
//! UNITS: a batch a sealing build wrote, whose records say "the batch continues" until
//! its last carries the seal with its count, or a single record with no mark at all,
//! which a build that predates the marks wrote whole, on its own — a revert to such a
//! build appends those above the floor and never rewrites the sidecar (see
//! [`BREC_VERSION`](crate::BREC_VERSION)). Let `p` be the first byte that is not an
//! intact, in-order record, `e` the offset expected there, and `b0` the start of the
//! unit `p` falls in: the later of the end of the last record that ends a unit before
//! `p` and the floor.
//!
//! - A shape only a writer makes at `p` — a CRC-valid frame that is not the next
//!   record, does not parse, or fails to authenticate, or a record in a newer format —
//!   is refused, as before: no torn write leaves one.
//! - Damage below the floor (`e < floor`) is refused: those bytes were durable when the
//!   floor was recorded, so whatever happened to them is not a torn write. The one
//!   exception is a file that simply ENDS below its floor, inside a frame (a copy taken
//!   while the log was written, restored alone): that is a shorter log, not damage, and
//!   is cut to its last whole record exactly as one that ends on a record boundary is
//!   kept — the identity rules move the generation, with no lineage, for the
//!   shortening.
//! - After an UNCLEAN stop of a Relaxed run (its sidecar names another boot, or none —
//!   [`Prior::unclean`](crate::logid::Prior::unclean)), the log is cut at `p`, keeping the
//!   longest intact prefix: Relaxed issues no flush between opens, so a power loss
//!   leaves holes anywhere above the floor and a complete batch behind one is expected.
//!   The identity's generation moves for the unclean stop itself.
//! - Otherwise (a Strict run, or a Relaxed run reopened in the boot it served in) the
//!   bytes after `p` are RESYNCED: every intact record frame found AT A RECORD'S PLACE
//!   there (below) must belong to the torn batch — at or after `e`, marked as a batch's,
//!   and at or before that batch's own seal, found at most once. Anything else — an
//!   unmarked record (a unit of its own, written whole), one past the batch's seal, a
//!   sealed batch that starts after `b0` (a LATER batch that completed behind the
//!   damage, which the order of writes forbids), a newer-format record — is refused:
//!   the damage is not a torn write. When everything after `p` is allowed, the batch is
//!   torn and the log is cut at `b0`, so it is always a prefix of WHOLE units. A file
//!   that ends inside a sealing build's batch above the floor (records that say the
//!   batch continues, then nothing) is cut at `b0` the same way.
//!
//! Why `b0` and not `p`: rot in the newest batch above the floor cannot be told from a
//! tear by its bytes, so the cut takes the batch's intact records too and the open
//! moves the generation for it (with lineage: nothing below `b0` changed), instead of
//! silently keeping a partial batch whose missing record may have been acked. Cutting
//! at unit boundaries also means a later crash never meets a half-kept batch.
//!
//! # A record's place, and the frames inside record bodies
//!
//! A record's BODY is opaque bytes, and may hold a whole, CRC-valid record frame (a
//! forwarded frame, a bridged one, or one a hostile publisher planted). The resync
//! reads the bytes after `p` with a magic scan, so it meets such a frame when a torn
//! write took the header of the record carrying it. Records from `e` on are dense, so a
//! record with offset `s` can only start a span the `s - e` records before it can fill
//! — at least a minimal frame each, at most a maximal one — and record `e` itself only
//! at `p`. A frame anywhere else is not a record of this log at its place: it is
//! ignored, never refused for. The residual: a planted frame whose offset is exactly
//! one a record of the torn batch could hold at that byte, marked as a different unit,
//! still refuses the torn write it sits in (never a silent cut: the log stays as it is
//! until a repair). A log sealed at rest has no such frames: its bodies are ciphertext.
//!
//! # What "written" means for a cut
//!
//! A cut moves the generation when it may remove a record a client was told about: when
//! it discards an intact record (the torn batch's own, before or after `p`), or when the
//! damaged frame at `p` is the shape a WRITTEN record leaves damaged — WHOLE-SIZED WITH
//! DATA (its header claims a length the file holds and what it claims is not all zeros:
//! the shape rot leaves, since a record's payload always holds its nonzero version byte),
//! or WHOLE TO THE END OF THE FILE under a length field that says otherwise (its CRC
//! holds over exactly the bytes to the end: a whole last record whose length rotted). A
//! header cut short, a length running past the end over bytes that are not the frame
//! its CRC names, a payload that never landed (zeros behind a header), or a header torn
//! after its first four bytes with nothing behind it is a write that never finished, and
//! cutting it moves nothing. Under Strict, the batch a power loss tears was never acked,
//! so a move for it is precaution; it buys an announced loss for rot in an ACKED newest
//! batch.
//!
//! One exception keeps a process crash free: in the SAME BOOT as the run that wrote the
//! log, with the log on the boot volume, the page cache held every byte the dead process
//! wrote, so a file that ends inside the newest batch — its last records cut short, or
//! missing — is a write that process never finished (a `kill -9` stops a write between
//! pages), never acked, and cutting its intact records moves nothing.

use astream_wire::frame::{MAGIC, VERSION};
use astream_wire::{crc32_ieee, Frame, HEADER_SIZE, MAX_PAYLOAD_LEN};

use crate::brecord::{BrokerRecord, Mark};
use crate::store::{open_disk_payload, AtRestRef, Mutation, RepairAt, Scan, Tail};

#[cfg(clean_islands)]
#[path = "recover_island.rs"]
mod recover_island;
#[cfg(not(clean_islands))]
pub use crate::twins::recover_unit_start_advance;
#[cfg(clean_islands)]
pub use recover_island::recover_unit_start_advance;

contract_fn! {
    /// Verified check that a recovery cut point `keep` lies within the log byte length
    /// (`keep <= len`), linked via `clean-kernel-defeq` to `recover_keep_within_len_isl`.
    #[must_use]
    pub fn recover_keep_within_len(keep: usize, len: usize) -> bool
    clauses [ensures result == (keep <= len)]
    {
        keep <= len
    }
}

/// What recovery decided about the bytes after the intact prefix.
#[derive(Debug, Eq)]
pub(crate) enum Classified {
    /// Keep the first `keep` bytes, which hold the first `records` records, and cut
    /// the rest. `written`: the cut removes bytes a client may have been told about
    /// (see the module docs), so the identity's generation moves for it.
    Keep {
        keep: usize,
        records: usize,
        written: bool,
    },
    /// Refuse the log: damage that is not a torn write (the open's error names it; an
    /// explicit repair may cut at `at_byte` when `repair_at` allows).
    Corrupt {
        offset: u64,
        at_byte: usize,
        reason: String,
        repair_at: RepairAt,
    },
    /// A record in a newer format: refused by every open, never repaired.
    Newer {
        offset: u64,
        at_byte: usize,
        version: u8,
    },
}

impl PartialEq for Classified {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Classified::Keep {
                    keep: a_k,
                    records: a_r,
                    written: a_w,
                },
                Classified::Keep {
                    keep: b_k,
                    records: b_r,
                    written: b_w,
                },
            ) => *a_k == *b_k && *a_r == *b_r && *a_w == *b_w,
            (
                Classified::Corrupt {
                    offset: a_o,
                    at_byte: a_b,
                    reason: a_r,
                    repair_at: a_ra,
                },
                Classified::Corrupt {
                    offset: b_o,
                    at_byte: b_b,
                    reason: b_r,
                    repair_at: b_ra,
                },
            ) => *a_o == *b_o && *a_b == *b_b && a_r.as_str() == b_r.as_str() && *a_ra == *b_ra,
            (
                Classified::Newer {
                    offset: a_o,
                    at_byte: a_b,
                    version: a_v,
                },
                Classified::Newer {
                    offset: b_o,
                    at_byte: b_b,
                    version: b_v,
                },
            ) => *a_o == *b_o && *a_b == *b_b && *a_v == *b_v,
            _ => false,
        }
    }
}

/// What the classifier knows besides the scan.
pub(crate) struct Judge<'a> {
    /// The stored bytes after the scan's intact prefix: from its end
    /// ([`Scan::valid_len`]) to the end of the file, empty when the scan reached it.
    pub(crate) rest: &'a [u8],
    /// The at-rest key and optional `<log>.seal` binding, when the log is sealed at rest.
    pub(crate) key: Option<AtRestRef<'a>>,
    /// The retention base: the offset of the first stored record.
    pub(crate) base: u64,
    /// The durable floor (`None`: the rules that predate it).
    pub(crate) floor: Option<u64>,
    /// The last run served Relaxed and stopped uncleanly (the cut-at-`p` rule).
    pub(crate) unclean_relaxed: bool,
    /// The last run served Relaxed, unclean or not (for the NC8 mutation only).
    pub(crate) prior_relaxed: bool,
    /// This open is in the boot the last run named, with the log on the boot volume
    /// then and now: a file ending inside its newest batch is that run's unfinished
    /// write ([`Prior::same_boot`](crate::logid::Prior::same_boot)).
    pub(crate) same_boot: bool,
    /// The crash simulation's recovery mutation (always `Off` outside it).
    pub(crate) mutation: Mutation,
}

/// The smallest payload a stored record has: a 25-byte record header, two length
/// prefixes and the commit tag.
const MIN_PAYLOAD: usize = 34;
/// The smallest stored frame a plaintext record can take.
const MIN_FRAME: u64 = (HEADER_SIZE + MIN_PAYLOAD) as u64;
/// The largest stored frame any record can take: a header and the frame cap.
const MAX_FRAME: u64 = (HEADER_SIZE + MAX_PAYLOAD_LEN) as u64;
/// The smallest stored frame a record can take on a log sealed at rest: a plaintext
/// one plus the AEAD nonce and tag. Bounds the offsets a frame found at a given byte can
/// carry, so a keyed resync tries few candidate offsets per frame.
const MIN_SEALED_FRAME: u64 = MIN_FRAME + 40;

const fn first_newer_after(after: &[Found]) -> Option<(u64, usize, u8)> {
    let mut rest = after;
    while let [f, tail @ ..] = rest {
        if let Found::Newer {
            offset,
            at_byte,
            version,
        } = f
        {
            return Some((*offset, *at_byte, *version));
        }
        rest = tail;
    }
    None
}

const fn keep_all(keep: usize, records: usize) -> Classified {
    Classified::Keep {
        keep,
        records,
        written: false,
    }
}

/// Classify the bytes after `scan`'s intact prefix — see the module docs.
pub(crate) fn classify(scan: &Scan, j: &Judge<'_>) -> Classified {
    let records = scan.count;
    let e = j.base.saturating_add(records as u64);
    let p = scan.valid_len;
    // A later intact record in a newer format must refuse before ANY path that
    // could cut the damaged tail, including explicit repair and unclean Relaxed
    // recovery. Preserve its own location, not the earlier damage's cut point.
    let after = if matches!(&scan.tail, Tail::Clean | Tail::Newer { .. }) {
        Vec::new()
    } else {
        frames_after(j.rest, p, e, j.key)
    };
    if let Some((offset, at_byte, version)) = first_newer_after(&after) {
        return Classified::Newer {
            offset,
            at_byte,
            version,
        };
    }
    match &scan.tail {
        Tail::Newer {
            offset,
            at_byte,
            version,
        } => Classified::Newer {
            offset: *offset,
            at_byte: *at_byte,
            version: *version,
        },
        Tail::Clean => match j.floor {
            // The floor unknown: the rules that predate it, verbatim — a clean log or a
            // torn tail is kept up to its prefix, anything else refused.
            None => keep_all(p, records),
            Some(floor) => {
                // A log that ends cleanly below its floor is SHORTER than its last open saw
                // — a restored copy, or another file — not damaged: nothing here is cut, and
                // the identity rules move the generation for the shortening.
                let Some((b0, b0_at)) = batch_start(scan, floor) else {
                    return keep_all(p, records);
                };
                if b0 < e && !j.unclean_relaxed {
                    // The file ends inside a sealing build's batch above the floor: its
                    // records say the batch continues, and its sealed last record never
                    // landed. Cut it whole. No rot ends a file early, so this is a write
                    // that never finished; in the boot that wrote it, a dead process's own
                    // (never acked), so the cut moves nothing — in another, the power loss
                    // that cut it short is announced as a precaution.
                    Classified::Keep {
                        keep: b0_at,
                        records: b0.saturating_sub(j.base) as usize,
                        written: !j.same_boot,
                    }
                } else {
                    keep_all(p, records)
                }
            }
        },
        Tail::Torn => match j.floor {
            None => keep_all(p, records),
            Some(floor) => damaged(scan, j, &after, floor, e, p, "a torn tail"),
        },
        Tail::Corrupt {
            offset,
            at_byte,
            reason,
            repair_at,
            tear,
        } => match j.floor {
            Some(floor) if *tear => damaged(scan, j, &after, floor, e, p, reason),
            // A shape only a writer makes (`!tear`), or any corruption when the floor is
            // unknown, is refused.
            _ => Classified::Corrupt {
                offset: *offset,
                at_byte: *at_byte,
                reason: reason.clone(),
                repair_at: *repair_at,
            },
        },
    }
}

/// The damage at `p` on a log whose durable floor is known; `found` is what the scan
/// saw there, which a refusal names first.
fn damaged(
    scan: &Scan,
    j: &Judge<'_>,
    after: &[Found],
    floor: u64,
    e: u64,
    p: usize,
    found: &str,
) -> Classified {
    let records = scan.count;
    let cut_at_any = j.mutation.cut_at_any_damage();
    // The file ends inside the frame at `p` — its header or payload cut short, no placed
    // record behind it (a planted record frame inside the unfinished record's own body is
    // `Found::Nothing`, even when `scan_from`'s un-placed `later_record_exists` reported
    // `Tail::Corrupt { tear: true }`) — and that frame is no whole record under a rotted
    // length.
    let ends_short =
        !intact_records_after(after) && ends_inside_a_frame(j.rest) && !whole_to_eof(j.rest);
    if e < floor && !cut_at_any {
        if ends_short {
            // A log that ENDS below its floor is shorter than its last open saw — a copy
            // taken while the log was written, restored alone — not damaged: a power loss
            // never shortens a file below bytes a full flush covered. Cut to the last
            // whole record, as the rules that predate the floor do; the identity rules
            // move the generation, with no lineage, for the shortening.
            return Classified::Keep {
                keep: p,
                records,
                written: false,
            };
        }
        return Classified::Corrupt {
            offset: e,
            at_byte: p,
            reason: format!(
                "{found}, below the log's durable floor (offset {floor}): every record \
                 below it was flushed in full when the last open (or clean close) recorded \
                 it, so this is not a torn write"
            ),
            repair_at: RepairAt::Cut,
        };
    }
    // NC8, the negative control: the cut-at-`p` rule with no unclean verdict.
    let flag_rule = j.mutation.relaxed_cut_without_verdict() && j.prior_relaxed;
    if cut_at_any || j.unclean_relaxed || flag_rule {
        // Keep the longest intact prefix. What follows `p` is judged only for whether
        // the cut removes written bytes.
        let behind = intact_records_after(after);
        return Classified::Keep {
            keep: p,
            records,
            written: behind || written_frame(j.rest),
        };
    }
    let Some((b0, b0_at)) = batch_start(scan, floor) else {
        // Unreachable while `e >= floor` (the scan noted where the floor's record
        // starts); refuse rather than guess a cut.
        return Classified::Corrupt {
            offset: e,
            at_byte: p,
            reason: "the durable floor is not at a record boundary of the intact prefix"
                .to_string(),
            repair_at: RepairAt::Cut,
        };
    };
    match resync(after, e, b0, floor, scan.seal_end.0) {
        Err(reason) => Classified::Corrupt {
            offset: e,
            at_byte: p,
            reason: format!("{found}; and {reason}"),
            repair_at: RepairAt::Cut,
        },
        Ok(found) => {
            // The batch's intact records before `p` count as written unless the file
            // simply ends inside the batch in the boot that wrote it: a dead process's
            // unfinished write, which the page cache held whole up to where it stopped.
            let unfinished = j.same_boot && ends_short;
            Classified::Keep {
                keep: b0_at,
                records: b0.saturating_sub(j.base) as usize,
                written: (b0_at < p && !unfinished) || found || written_frame(j.rest),
            }
        }
    }
}

/// Where the unit the first damage (or the end) falls in starts, by offset and byte:
/// the later of the end of the last record that ends a unit and the floor. `None` when
/// the floor is above the intact prefix.
const fn batch_start(scan: &Scan, floor: u64) -> Option<(u64, usize)> {
    let Some(floor_at) = scan.floor_at else {
        return None;
    };
    Some(if scan.seal_end.0 >= floor {
        scan.seal_end
    } else {
        (floor, floor_at)
    })
}

const fn has_nonzero(mut bytes: &[u8]) -> bool {
    while let &[b, ref tail @ ..] = bytes {
        if b != 0 {
            return true;
        }
        bytes = tail;
    }
    false
}

/// Whether the file ends inside the frame `rest` (the bytes from `p` to the end) starts
/// with: something other than zeros is
/// there, and it is a frame's beginning that runs past the end (`Frame::decode` asks
/// for more bytes) — what a write stopped part-way leaves, and what a copy taken while
/// the log was written ends in. Nothing but zeros is a size that landed without its
/// data, never a write that stopped.
fn ends_inside_a_frame(rest: &[u8]) -> bool {
    has_nonzero(rest) && matches!(Frame::decode(rest), Ok(None))
}

/// Whether the damaged frame `rest` starts with (at byte `p`) is the shape a WRITTEN
/// record leaves damaged (see the module docs): whole-sized with data, or whole to the end of the file.
fn written_frame(rest: &[u8]) -> bool {
    whole_sized(rest) || whole_to_eof(rest)
}

/// Whether the damaged frame at byte `p` is WHOLE-SIZED with data in it — its header
/// present, claiming a length the file holds, and some byte of what it claims not zero
/// — the shape rot leaves (a stored record's payload always holds its nonzero version
/// byte), and a torn write leaves only when its size landed with some of its data. A
/// header cut short, a length running past the end, or a frame whose payload never
/// landed (nothing but zeros behind its header) is a write that never finished. An
/// EMPTY frame claims no payload, so what decides is whether anything follows it: a
/// header torn after its first four bytes ends the file, or is followed by zeros, while
/// a real record whose header's last eight bytes were zeroed has its payload behind it.
const fn header_len_field(hdr: &[u8; HEADER_SIZE]) -> usize {
    ((hdr[4] as u32) | ((hdr[5] as u32) << 8) | ((hdr[6] as u32) << 16) | ((hdr[7] as u32) << 24))
        as usize
}

const fn split_header_len_field(rest: &[u8]) -> Option<(usize, &[u8])> {
    let &[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ref after_hdr @ ..] = rest else {
        return None;
    };
    let len = header_len_field(&[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]);
    Some((len, after_hdr))
}

const fn header_crc_and_magic_v1(hdr: &[u8; HEADER_SIZE]) -> Option<u32> {
    let crc = (hdr[8] as u32)
        | ((hdr[9] as u32) << 8)
        | ((hdr[10] as u32) << 16)
        | ((hdr[11] as u32) << 24);
    if hdr[0] != MAGIC[0] || hdr[1] != MAGIC[1] || hdr[2] != VERSION {
        return None;
    }
    Some(crc)
}

const fn split_header_crc_and_magic_v1(rest: &[u8]) -> Option<(u32, &[u8])> {
    let &[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ref payload @ ..] = rest else {
        return None;
    };
    let Some(crc) = header_crc_and_magic_v1(&[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11])
    else {
        return None;
    };
    Some((crc, payload))
}

fn whole_sized(rest: &[u8]) -> bool {
    let Some((len, after_hdr)) = split_header_len_field(rest) else {
        return false;
    };
    let Some(claimed) = (if len == 0 {
        Some(after_hdr)
    } else {
        after_hdr.get(..len)
    }) else {
        return false;
    };
    has_nonzero(claimed)
}

/// Whether the frame `rest` starts with (at byte `p`) is a WHOLE record running exactly to the end of the
/// file under a length field that says otherwise: its magic and version stand, and its
/// CRC holds over every byte after its header — at least a minimal record's payload. A
/// record's CRC never holds over a part of it (one chance in 2^32), so this is the last
/// record of the file with its LENGTH rotted, a shape that otherwise reads as a write
/// cut short (running past the end) or a frame that does not decode (above the cap).
fn whole_to_eof(rest: &[u8]) -> bool {
    let Some((crc, payload)) = split_header_crc_and_magic_v1(rest) else {
        return false;
    };
    if payload.len() < MIN_PAYLOAD {
        return false;
    }
    crc32_ieee(payload) == crc
}

/// Whether a record with offset `s` can START `q` bytes after the damaged record `e`:
/// records from `e` on are dense, each one frame of `MIN_FRAME..=MAX_FRAME` bytes, so
/// the `s - e` records before it fill exactly `q` bytes, and record `e` itself starts
/// at the damage, never after it. A frame anywhere else is not a record at its place:
/// one carried inside another record's body (see the module docs).
const fn placed(s: u64, e: u64, q: usize) -> bool {
    let Some(n) = s.checked_sub(e) else {
        return false;
    };
    if n == 0 {
        return false;
    }
    let q = q as u64;
    let lo_ok = match n.checked_mul(MIN_FRAME) {
        Some(lo) => lo <= q,
        None => false,
    };
    let hi_ok = match n.checked_mul(MAX_FRAME) {
        Some(hi) => q <= hi,
        None => true,
    };
    lo_ok && hi_ok
}

/// One intact frame found after the damage, parsed as a record: the record and its mark.
enum Found {
    Record(BrokerRecord, Mark),
    /// A CRC-valid frame that is no record of this log at its place (ignored): no
    /// record this build reads, or a record frame where no record of the log can start.
    Nothing,
    /// A record in a newer format (never part of a torn batch of this build's).
    Newer {
        offset: u64,
        at_byte: usize,
        version: u8,
    },
    /// A keyed log's intact frame that authenticates at no offset the torn batch can
    /// hold: a record from elsewhere in the log, or a rewrite.
    Foreign,
}

/// Every intact frame after the first byte of `rest` (the bytes from `p`), in order, each
/// parsed — the magic scan
/// `later_record_exists` does, stepping past each record frame it accepts so a
/// record's own body is never read as a frame, and judging every other by its place
/// ([`placed`]), since the damaged record's body was never stepped past. `e` is the
/// offset expected at `p`; a keyed log's frame is tried at every offset it can hold (it
/// is sealed under its own).
fn frames_after(rest: &[u8], p: usize, e: u64, key: Option<AtRestRef<'_>>) -> Vec<Found> {
    let mut out = Vec::new();
    let mut q = 1usize;
    let mut next = e;
    while q.saturating_add(HEADER_SIZE) <= rest.len() {
        let Some(tail) = rest.get(q..) else {
            break;
        };
        if tail.get(..2) != Some(MAGIC.as_slice()) {
            q = q.saturating_add(1);
            continue;
        }
        let Ok(Some(d)) = Frame::decode(tail) else {
            q = q.saturating_add(1);
            continue;
        };
        // An EMPTY frame is never a record (the scan's own rule): its CRC holds only
        // because the CRC-32 of nothing is 0.
        if d.frame.payload.is_empty() || d.consumed == 0 {
            q = q.saturating_add(1);
            continue;
        }
        let found = match key {
            None => match BrokerRecord::from_payload_marked(&d.frame.payload) {
                Some((r, mark)) if placed(r.seq.0, e, q) => Found::Record(r, mark),
                Some(_) => Found::Nothing,
                None => match crate::brecord::newer_format(&d.frame.payload, None) {
                    Some(version) if placed(seq_of(&d.frame.payload), e, q) => Found::Newer {
                        offset: seq_of(&d.frame.payload),
                        at_byte: p.saturating_add(q),
                        version,
                    },
                    _ => Found::Nothing,
                },
            },
            Some(_) => {
                // Records from `p` on are dense and each takes at least a minimal sealed
                // frame, so the one at byte `q` carries an offset below this bound.
                let last = e.saturating_add((q as u64 / MIN_SEALED_FRAME).saturating_add(1));
                let mut keyed_found = Found::Foreign;
                for o in next..=last {
                    let Some(pt) = open_disk_payload(key, o, d.frame.payload.clone()) else {
                        continue;
                    };
                    if let Some((r, mark)) = BrokerRecord::from_payload_marked(&pt) {
                        if r.seq.0 == o {
                            keyed_found = Found::Record(r, mark);
                            break;
                        }
                        continue;
                    }
                    if let Some(version) = crate::brecord::newer_format(&pt, Some(o)) {
                        if placed(o, e, q) {
                            keyed_found = Found::Newer {
                                offset: o,
                                at_byte: p.saturating_add(q),
                                version,
                            };
                            break;
                        }
                    }
                }
                keyed_found
            }
        };
        match &found {
            // A record at its place: step past it, so its body is never scanned.
            Found::Record(r, _) => {
                next = r.seq.0.saturating_add(1);
                q = q.saturating_add(d.consumed);
            }
            // A frame where no record starts may sit inside a body: look at every byte
            // after its first, so nothing it overlaps is skipped.
            Found::Nothing => q = q.saturating_add(1),
            Found::Newer { .. } | Found::Foreign => q = q.saturating_add(d.consumed),
        }
        out.push(found);
    }
    out
}

const fn seq_prefix_of(prefix: &[u8; 9]) -> u64 {
    (prefix[1] as u64)
        | ((prefix[2] as u64) << 8)
        | ((prefix[3] as u64) << 16)
        | ((prefix[4] as u64) << 24)
        | ((prefix[5] as u64) << 32)
        | ((prefix[6] as u64) << 40)
        | ((prefix[7] as u64) << 48)
        | ((prefix[8] as u64) << 56)
}

/// The offset a payload's version-independent prefix names (its bytes 1..9).
const fn seq_of(payload: &[u8]) -> u64 {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, ref _rest @ ..] = payload else {
        return 0;
    };
    seq_prefix_of(&[b0, b1, b2, b3, b4, b5, b6, b7, b8])
}

/// Whether any intact record at its place (or any frame a keyed log cannot place)
/// follows byte `p`.
const fn intact_records_after(mut after: &[Found]) -> bool {
    while let &[ref f, ref tail @ ..] = after {
        if !matches!(f, Found::Nothing) {
            return true;
        }
        after = tail;
    }
    false
}

/// Whether a sealed batch ending at `s` with `count` records is the torn batch's own
/// seal (`(start, own)`).
const fn seal_is_own(
    s: u64,
    count: u32,
    own_seal: Option<u64>,
    b0: u64,
    floor: u64,
    seal_end: u64,
) -> (u64, bool) {
    let start = s.saturating_add(1).saturating_sub(count as u64);
    // The batch the damage falls in starts at `b0` — or, where retention
    // raised the base above where it started, somewhere below a floor no
    // unit's end reached.
    let own =
        own_seal.is_none() && (start == b0 || (start < b0 && b0 == floor && seal_end < floor));
    (start, own)
}

/// Judge every intact frame after the damage at byte `p` (offset `e`) against the torn
/// batch starting at offset `b0` — see the module docs. `Ok(found)`: all of them belong
/// to it (`found` says whether there were any); `Err(why)`: the damage is not a torn
/// write.
fn resync(after: &[Found], e: u64, b0: u64, floor: u64, seal_end: u64) -> Result<bool, String> {
    let mut own_seal: Option<u64> = None;
    let mut found = false;
    for f in after {
        let (r, mark) = match f {
            Found::Nothing => continue,
            Found::Newer { .. } => {
                return Err(format!(
                    "a record in a newer format is intact behind the damage at offset {e}: \
                     it was written, so the damage is not a torn write"
                ))
            }
            Found::Foreign => {
                return Err(format!(
                    "an intact frame behind the damage at offset {e} is no record the torn \
                     batch can hold: the damage is not a torn write"
                ))
            }
            Found::Record(r, mark) => (r, *mark),
        };
        let s = r.seq.0;
        if let Some(end) = own_seal {
            if s > end {
                return Err(format!(
                    "the record at offset {s} lies past the torn batch's own seal (offset \
                     {end}): a later batch completed behind the damage at offset {e}, which no \
                     torn write leaves"
                ));
            }
        }
        match mark {
            Mark::Unmarked => {
                return Err(format!(
                    "the record at offset {s}, intact behind the damage at offset {e}, \
                     carries no batch mark: a build that predates the marks wrote it whole, \
                     on its own, so the damage is not a torn write"
                ))
            }
            Mark::Continues => {}
            Mark::Seal(count) => {
                let (start, own) = seal_is_own(s, count, own_seal, b0, floor, seal_end);
                if !own {
                    return Err(format!(
                        "a sealed batch (offsets {start}..={s}) is intact behind the damage at \
                         offset {e}, but the torn batch starts at offset {b0}: a later batch \
                         completed behind the damage, which no torn write leaves"
                    ));
                }
                own_seal = Some(s);
            }
        }
        found = true;
    }
    Ok(found)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::scan_from;
    use astream_wire::Offset;

    fn rec(seq: u64) -> BrokerRecord {
        BrokerRecord {
            seq: Offset(seq),
            producer_id: 1,
            producer_seq: seq + 1,
            subject: "/a/s".to_string(),
            body: vec![seq as u8; 9],
            commit: None,
        }
    }

    fn frame(r: &BrokerRecord, mark: Mark) -> Vec<u8> {
        Frame::new(r.encode_payload_marked(mark).unwrap())
            .encode()
            .unwrap()
    }

    /// A log of `batches`, each a list of offsets, every batch's last record sealed and
    /// every other marked as continuing it.
    fn log(batches: &[&[u64]]) -> (Vec<u8>, Vec<usize>) {
        log_of(batches, rec)
    }

    fn log_of(batches: &[&[u64]], make: impl Fn(u64) -> BrokerRecord) -> (Vec<u8>, Vec<usize>) {
        let mut bytes = Vec::new();
        let mut starts = Vec::new();
        for batch in batches {
            for (i, &seq) in batch.iter().enumerate() {
                starts.push(bytes.len());
                let mark = if i + 1 == batch.len() {
                    Mark::Seal(batch.len() as u32)
                } else {
                    Mark::Continues
                };
                bytes.extend_from_slice(&frame(&make(seq), mark));
            }
        }
        starts.push(bytes.len());
        (bytes, starts)
    }

    fn judge(bytes: &[u8], floor: Option<u64>, unclean_relaxed: bool) -> Classified {
        judge_in(bytes, floor, unclean_relaxed, false)
    }

    fn judge_in(
        bytes: &[u8],
        floor: Option<u64>,
        unclean_relaxed: bool,
        same_boot: bool,
    ) -> Classified {
        let scan = scan_from(bytes, None, 0, floor, Mutation::Off).scan;
        classify(
            &scan,
            &Judge {
                rest: bytes.get(scan.valid_len..).unwrap_or(&[]),
                key: None,
                base: 0,
                floor,
                unclean_relaxed,
                prior_relaxed: unclean_relaxed,
                same_boot,
                mutation: Mutation::Off,
            },
        )
    }

    /// Zero `len` bytes at `at`: a block that never landed.
    fn hole(bytes: &[u8], at: usize, len: usize) -> Vec<u8> {
        let mut b = bytes.to_vec();
        b[at..at + len].fill(0);
        b
    }

    #[test]
    fn a_torn_newest_batch_is_cut_at_its_start_and_a_later_seal_behind_damage_refuses() {
        let (bytes, at) = log(&[&[0], &[1, 2, 3], &[4, 5]]);
        // A hole in record 2 (inside batch 1..=3), its batch's seal intact behind it:
        // batch 4..=5 completed behind it, so this is no torn write.
        let damaged = hole(&bytes, at[2] + 29, 4);
        match judge(&damaged, Some(1), false) {
            Classified::Corrupt { offset, reason, .. } => {
                assert_eq!(offset, 2);
                assert!(reason.contains("later batch"), "{reason}");
            }
            other => panic!("{other:?}"),
        }
        // The same hole when batch 1..=3 is the newest: torn, cut at its start, and the
        // cut removes written bytes (record 1 is intact, record 3 holds the seal).
        let newest = &bytes[..at[4]];
        let damaged = hole(newest, at[2] + 29, 4);
        assert_eq!(
            judge(&damaged, Some(1), false),
            Classified::Keep {
                keep: at[1],
                records: 1,
                written: true
            }
        );
        // Below the floor it refuses, whatever follows.
        let damaged = hole(newest, at[0] + 29, 4);
        match judge(&damaged, Some(1), false) {
            Classified::Corrupt { reason, .. } => assert!(reason.contains("floor"), "{reason}"),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn after_an_unclean_relaxed_stop_the_longest_intact_prefix_is_kept() {
        let (bytes, at) = log(&[&[0], &[1, 2, 3], &[4, 5]]);
        let damaged = hole(&bytes, at[2] + 29, 4);
        assert_eq!(
            judge(&damaged, Some(1), true),
            Classified::Keep {
                keep: at[2],
                records: 2,
                written: true
            }
        );
        // Below the floor it still refuses.
        assert!(matches!(
            judge(&hole(&bytes, at[0] + 29, 4), Some(1), true),
            Classified::Corrupt { .. }
        ));
    }

    #[test]
    fn a_file_ending_inside_an_unsealed_batch_above_the_floor_is_cut_whole() {
        let (bytes, at) = log(&[&[0], &[1, 2, 3]]);
        // The file ends after record 2: batch 1..=3's seal never landed.
        let short = &bytes[..at[3]];
        assert_eq!(
            judge(short, Some(1), false),
            Classified::Keep {
                keep: at[1],
                records: 1,
                written: true
            }
        );
        // In the boot that wrote it, the same shape is a dead process's unfinished
        // write: cut, and nothing moves.
        assert_eq!(
            judge_in(short, Some(1), false, true),
            Classified::Keep {
                keep: at[1],
                records: 1,
                written: false
            }
        );
        // With the floor unknown, the old rules keep every intact record.
        assert_eq!(
            judge(short, None, false),
            Classified::Keep {
                keep: at[3],
                records: 3,
                written: false
            }
        );
        // Below the floor it is a shorter log, not damage: kept.
        assert_eq!(
            judge(&bytes[..at[1]], Some(3), false),
            Classified::Keep {
                keep: at[1],
                records: 1,
                written: false
            }
        );
    }

    #[test]
    fn a_tear_that_never_finished_moves_nothing_and_whole_sized_damage_does() {
        let (bytes, at) = log(&[&[0], &[1]]);
        // The newest record cut short: a write that never finished.
        let cut = &bytes[..at[1] + 20];
        assert_eq!(
            judge(cut, Some(1), false),
            Classified::Keep {
                keep: at[1],
                records: 1,
                written: false
            }
        );
        // The newest record whole-sized with a byte flipped: rot or a torn write whose
        // size landed — the cut is announced.
        let mut rot = bytes.clone();
        rot[at[1] + 20] ^= 0x40;
        assert_eq!(
            judge(&rot, Some(1), false),
            Classified::Keep {
                keep: at[1],
                records: 1,
                written: true
            }
        );
        // Nothing but zeros where the newest record was: never written.
        assert_eq!(
            judge(&hole(&bytes, at[1], at[2] - at[1]), Some(1), false),
            Classified::Keep {
                keep: at[1],
                records: 1,
                written: false
            }
        );
    }

    /// The newest record's LENGTH rotted, so it runs past the end (or above the cap):
    /// the shape of a write cut short, but its CRC holds over exactly the bytes to the
    /// end — a whole record, so the cut is announced, in the boot that wrote it too.
    #[test]
    fn a_whole_last_record_under_a_rotted_length_is_announced() {
        let (bytes, at) = log(&[&[0], &[1]]);
        for (byte, flip) in [(at[1] + 4, 0x01), (at[1] + 6, 0x40), (at[1] + 7, 0x80)] {
            let mut rot = bytes.clone();
            rot[byte] ^= flip;
            for same_boot in [false, true] {
                assert_eq!(
                    judge_in(&rot, Some(1), false, same_boot),
                    Classified::Keep {
                        keep: at[1],
                        records: 1,
                        written: true
                    },
                    "byte {byte} flipped by {flip:#x}, same boot {same_boot}"
                );
            }
        }
        // The same record cut short is no whole record: a write that never finished.
        assert!(!whole_to_eof(&bytes[at[1]..at[2] - 1]));
        assert!(
            whole_to_eof(&bytes[at[1]..]),
            "an intact last frame is whole too"
        );
    }

    #[test]
    fn a_written_shape_is_refused_whatever_the_floor() {
        let (mut bytes, _) = log(&[&[0], &[1]]);
        // An offset gap: a CRC-valid record 7 where 2 belongs.
        bytes.extend_from_slice(&frame(&rec(7), Mark::Seal(1)));
        match judge(&bytes, Some(1), true) {
            Classified::Corrupt { reason, .. } => assert!(reason.contains("gap"), "{reason}"),
            other => panic!("{other:?}"),
        }
    }

    /// Records a build that predates the marks appended above a floor a sealing build
    /// recorded (a revert, then the upgrade again) are units of their own: kept when
    /// the file ends cleanly, kept up to a torn last one, and an intact one behind
    /// damage refuses as the rules before the floor would — never cut as a torn batch.
    #[test]
    fn unmarked_records_above_the_floor_are_units_of_their_own() {
        let (mut bytes, at) = log(&[&[0], &[1]]);
        let mut starts = at[..2].to_vec();
        for seq in 2..=4 {
            starts.push(bytes.len());
            bytes.extend_from_slice(&frame(&rec(seq), Mark::Unmarked));
        }
        starts.push(bytes.len());
        let all = Classified::Keep {
            keep: bytes.len(),
            records: 5,
            written: false,
        };
        assert_eq!(judge(&bytes, Some(2), false), all, "a clean end keeps them");
        assert_eq!(judge_in(&bytes, Some(2), false, true), all);
        // Its own write cut short: only that record goes.
        let torn = &bytes[..starts[4] + 20];
        assert_eq!(
            judge(torn, Some(2), false),
            Classified::Keep {
                keep: starts[4],
                records: 4,
                written: false
            }
        );
        // A hole in record 3 with record 4 intact behind it: a write that completed
        // behind the damage — refused, as the rules before the floor refuse it.
        match judge(&hole(&bytes, starts[3] + 29, 4), Some(2), false) {
            Classified::Corrupt { reason, .. } => {
                assert!(reason.contains("no batch mark"), "{reason}")
            }
            other => panic!("{other:?}"),
        }
    }

    /// A record whose BODY holds a whole record frame (a forwarded one): a torn write
    /// that takes the header of that record lets the resync meet the inner frame, which
    /// is at no record's place — ignored, so the torn batch is cut, not refused.
    #[test]
    fn a_record_frame_inside_a_body_is_no_record_behind_a_tear() {
        let inner = |seq: u64, mark: Mark| frame(&rec(seq), mark);
        for planted in [
            inner(0, Mark::Unmarked),
            inner(0, Mark::Seal(1)),
            inner(1, Mark::Continues),
            inner(1_000_000, Mark::Seal(1)),
        ] {
            let carrying = |seq: u64| BrokerRecord {
                body: [&b"payload:"[..], &planted].concat(),
                ..rec(seq)
            };
            let (bytes, at) = log_of(&[&[0], &[1, 2]], carrying);
            // The 16 bytes holding record 1's header never landed; its body did.
            let damaged = hole(&bytes, at[1], 16);
            assert_eq!(
                judge(&damaged, Some(1), false),
                Classified::Keep {
                    keep: at[1],
                    records: 1,
                    written: true
                },
                "planted {planted:?}"
            );
            // In a one-record newest batch, too.
            let (bytes, at) = log_of(&[&[0], &[1]], carrying);
            assert!(matches!(
                judge(&hole(&bytes, at[1], 16), Some(1), false),
                Classified::Keep { keep, records: 1, .. } if keep == at[1]
            ));
        }
        // A frame at a record's place is still read: record 2 of the torn batch, intact
        // behind the hole in record 1, is found, so the cut is announced.
        assert!(placed(2, 1, MIN_FRAME as usize) && !placed(1, 1, 1) && !placed(0, 1, 99));
        assert!(
            !placed(3, 1, MIN_FRAME as usize),
            "two records need two frames"
        );
    }

    /// A copy that ends inside a frame BELOW its floor is a shorter log restored alone,
    /// not damage: cut to its last whole record (the identity rules move the generation
    /// for the shortening). Zeros there, or a whole last record under a rotted length,
    /// are damage below the floor and still refuse.
    #[test]
    fn a_copy_ending_inside_a_frame_below_its_floor_is_a_shorter_log() {
        let (bytes, at) = log(&[&[0], &[1], &[2], &[3], &[4]]);
        let copy = &bytes[..at[3] + 20];
        assert_eq!(
            judge(copy, Some(5), false),
            Classified::Keep {
                keep: at[3],
                records: 3,
                written: false
            }
        );
        let zeros = [&bytes[..at[3]], &[0u8; 20][..]].concat();
        assert!(matches!(
            judge(&zeros, Some(5), false),
            Classified::Corrupt { .. }
        ));
        let mut rot = bytes[..at[4]].to_vec();
        rot[at[3] + 5] ^= 0x10;
        assert!(matches!(
            judge(&rot, Some(5), false),
            Classified::Corrupt { .. }
        ));
    }

    /// The actual recovery classifier must preserve the future-format refusal even
    /// when an earlier damaged frame prevents the prefix scanner from reaching it.
    #[test]
    fn a_newer_plaintext_record_after_damage_is_never_a_repairable_cut() {
        let first = frame(&rec(0), Mark::Continues);
        let second = frame(&rec(1), Mark::Seal(2));
        let clean = [&first[..], &second[..]].concat();
        assert_eq!(
            judge(&clean, Some(0), false),
            Classified::Keep {
                keep: clean.len(),
                records: 2,
                written: false
            }
        );
        let mut damaged_first = first.clone();
        damaged_first[0] ^= 0x80;
        let ordinary = [&damaged_first[..], &second[..]].concat();
        for unclean in [false, true] {
            assert!(matches!(
                judge(&ordinary, Some(0), unclean),
                Classified::Keep {
                    keep: 0,
                    records: 0,
                    ..
                }
            ));
        }
        let future = |seq| {
            let mut payload = rec(seq).encode_payload_marked(Mark::Seal(2)).unwrap();
            payload[0] = crate::brecord::BREC_VERSION + 1;
            Frame::new(payload).encode().unwrap()
        };
        let version = crate::brecord::BREC_VERSION + 1;
        assert_eq!(
            judge(&future(0), Some(0), false),
            Classified::Newer {
                offset: 0,
                at_byte: 0,
                version
            }
        );
        let mut damaged_future = future(1);
        *damaged_future.last_mut().unwrap() ^= 1;
        let bad_crc = [&damaged_first[..], &damaged_future[..]].concat();
        assert!(matches!(
            judge(&bad_crc, Some(0), false),
            Classified::Keep {
                keep: 0,
                records: 0,
                ..
            }
        ));
        // An intact future frame at no record's place is still ignored.
        let misplaced = [&damaged_first[..], &future(9)[..]].concat();
        assert!(matches!(
            judge(&misplaced, Some(0), false),
            Classified::Keep {
                keep: 0,
                records: 0,
                ..
            }
        ));
        let later = [&damaged_first[..], &future(1)[..]].concat();
        let observed: Vec<_> = [
            (Some(0), false),
            (Some(0), true),
            (None, false),
            (Some(2), false),
        ]
        .into_iter()
        .map(|(floor, unclean)| judge(&later, floor, unclean))
        .collect();
        assert!(observed.iter().all(|c| c == &Classified::Newer {
            offset: 1, at_byte: first.len(), version
        }), "a later plaintext newer record must stay unsupported, never a repairable cut: {observed:?}");
    }

    #[cfg(feature = "at-rest")]
    #[test]
    fn an_authenticated_newer_record_after_damage_is_never_a_repairable_cut() {
        const KEY: [u8; 32] = [0x51; 32];
        let sealed = |aad_seq: u64, payload_seq: u64, version: u8, mark: Mark, nonce_tag: u8| {
            let mut payload = rec(payload_seq).encode_payload_marked(mark).unwrap();
            payload[0] = version;
            // Public fixture bytes only; distinct deterministic nonces keep this a
            // RAM-only exercise of the real AEAD, without an entropy/OS call.
            let mut nonce = [0; 24];
            nonce[0] = nonce_tag;
            nonce[1..9].copy_from_slice(&aad_seq.to_le_bytes());
            let ciphertext =
                astream_aead::seal_with_nonce(&KEY, &nonce, &aad_seq.to_le_bytes(), &payload);
            Frame::new(ciphertext).encode().unwrap()
        };
        let keyed_judge = |bytes: &[u8], floor, unclean_relaxed| {
            let scan = scan_from(bytes, Some(AtRestRef::v1(&KEY)), 0, floor, Mutation::Off).scan;
            classify(
                &scan,
                &Judge {
                    rest: bytes.get(scan.valid_len..).unwrap_or(&[]),
                    key: Some(AtRestRef::v1(&KEY)),
                    base: 0,
                    floor,
                    unclean_relaxed,
                    prior_relaxed: unclean_relaxed,
                    same_boot: false,
                    mutation: Mutation::Off,
                },
            )
        };
        let current = crate::brecord::BREC_VERSION;
        let version = current + 1;
        let first = sealed(0, 0, current, Mark::Continues, 1);
        let second = sealed(1, 1, current, Mark::Seal(2), 2);
        let clean = [&first[..], &second[..]].concat();
        assert_eq!(
            keyed_judge(&clean, Some(0), false),
            Classified::Keep {
                keep: clean.len(),
                records: 2,
                written: false
            }
        );
        let mut damaged_first = first.clone();
        damaged_first[0] ^= 0x80;
        let ordinary = [&damaged_first[..], &second[..]].concat();
        for unclean in [false, true] {
            assert!(matches!(
                keyed_judge(&ordinary, Some(0), unclean),
                Classified::Keep {
                    keep: 0,
                    records: 0,
                    ..
                }
            ));
        }
        let future = sealed(1, 1, version, Mark::Seal(2), 3);
        let direct = sealed(0, 0, version, Mark::Seal(1), 4);
        assert_eq!(
            keyed_judge(&direct, Some(0), false),
            Classified::Newer {
                offset: 0,
                at_byte: 0,
                version
            }
        );
        let mut damaged_future = future.clone();
        *damaged_future.last_mut().unwrap() ^= 1;
        let bad_crc = [&damaged_first[..], &damaged_future[..]].concat();
        assert!(matches!(
            keyed_judge(&bad_crc, Some(0), false),
            Classified::Keep {
                keep: 0,
                records: 0,
                ..
            }
        ));
        // Reframe a bad tag so its frame CRC is valid: it must not become newer.
        let mut bad_tag = Frame::decode(&future).unwrap().unwrap().frame.payload;
        *bad_tag.last_mut().unwrap() ^= 1;
        let bad_tag = Frame::new(bad_tag).encode().unwrap();
        let foreign = [&damaged_first[..], &bad_tag[..]].concat();
        assert!(matches!(
            keyed_judge(&foreign, Some(0), false),
            Classified::Corrupt { .. }
        ));
        // Authentication alone is insufficient: the mandatory version-independent
        // offset prefix must match the authenticated index and a record's place.
        for invalid in [
            sealed(1, 2, version, Mark::Seal(2), 5),
            sealed(0, 0, version, Mark::Seal(1), 6),
        ] {
            let bytes = [&damaged_first[..], &invalid[..]].concat();
            assert!(matches!(
                keyed_judge(&bytes, Some(0), false),
                Classified::Corrupt { .. }
            ));
        }
        let later = [&damaged_first[..], &future[..]].concat();
        let observed: Vec<_> = [
            (Some(0), false),
            (Some(0), true),
            (None, false),
            (Some(2), false),
        ]
        .into_iter()
        .map(|(floor, unclean)| keyed_judge(&later, floor, unclean))
        .collect();
        assert!(observed.iter().all(|c| c == &Classified::Newer {
            offset: 1, at_byte: first.len(), version
        }), "an authenticated later newer record must stay unsupported, never a repairable cut: {observed:?}");
    }
}
