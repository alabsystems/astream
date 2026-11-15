//! A log's IDENTITY: WHICH log a broker serves, and WHICH incarnation of that log's
//! offsets — what a client that keeps an offset OUTSIDE the log has to check before it
//! trusts that offset again.
//!
//! An offset names a record in ONE log. A consumer that persists one — a
//! delivered-up-to watermark, a topic cursor, "I already acked offset N" — and later
//! reads a DIFFERENT log at the same address applies it to records it never saw: it
//! skips mail below a stale watermark, replays a foreign log's history as new, or
//! answers for the wrong record. The address stays the same when the log file is
//! deleted and recreated, when a repair truncates it and later appends reuse the cut
//! offsets, when an older copy is restored over it, or when the client is pointed at
//! another host's broker. [`LogIdentity`] is how the consumer tells.
//!
//! # What a consumer does when the identity changes
//!
//! Compare the identity a connection reports — `Client::log_identity`, or
//! `Client::seen_log_identity` after an attach, which already sent the `Hello` that
//! carries it — with the identity its persisted offsets were read under. ANY
//! difference, in [`id`](LogIdentity::id) or in
//! [`generation`](LogIdentity::generation), means EVERY offset persisted under the old
//! identity is meaningless against this log: not too high or too low, meaningless.
//! Drop them (or keep them filed under the OLD identity, to resume only if exactly that
//! identity comes back — the same log after an off/on), and start the way a first run
//! does, from a cursor resolved against THIS log: its head, a `Last` snapshot, or a
//! consumer group (group cursors live inside the log and move with it). `None` — a
//! broker that predates log identity — says nothing either way: the client is exactly
//! where it was before this type existed.
//!
//! # Where it lives, and when it changes
//!
//! In a sidecar beside the log, `<log>.id` ([`identity_path`]): a CRC frame holding the
//! identity and what the open that wrote it saw (the retention base, the head, and a
//! fingerprint of the newest record's stored frame) — and, since FORMAT 2, how the run
//! that wrote it stood with the log (serving, stopped cleanly, a flush failed, or
//! cutting), the tier it served, its boot, whether the log was on the boot volume, the
//! DURABLE FLOOR (a head the log is flushed in full through) and the lineage. It is
//! written atomically (tmp file, fsync, rename, directory fsync) during
//! [`BrokerLog`](crate::BrokerLog)'s open,
//! BEFORE the open returns, so no client can be told an identity that a crash then
//! loses — in two phases: before a cut that removes written bytes (the moved identity,
//! so the cut cannot outlive its announcement) and after the open's own fsync (the run
//! serving, the floor at the head: only then is the head durable). A clean close
//! rewrites it once more (`Closed`, the floor raised to the head). An open that cannot
//! write it FAILS, naming it. It is not IN the log because a record there
//! would take an offset (every new log's first publish would move off offset 0) and
//! would be one more hidden record retention must carry; a replica's log is the
//! leader's spine and may not hold a record of its own either.
//!
//! - A log that has never held a record — every log an open creates — gets a fresh
//!   random `id`, generation 0, at each open: nobody can hold an offset into it, and
//!   a sidecar beside it can only be a deleted predecessor's (or its own, from before
//!   it held anything).
//! - A log that holds records and has NO sidecar — one written before log identity
//!   existed — gets a DERIVED `id`, deterministic in its stored bytes (base, head,
//!   first and newest frame), generation 0. A leader and a follower holding the same
//!   records derive the same one. (One whose every record retention pruned stores no
//!   frame to derive from, and is minted a fresh `id` instead.)
//! - A log that holds records beside a sidecar this build cannot read (damaged, or
//!   another sidecar format) gets a fresh random `id`, generation 0 — never a derived
//!   one, which could be an identity the log already had: the sidecar existed, so the
//!   log has had an identity, and only a new one is certainly not it.
//! - Otherwise the sidecar's `id` stands, and the `generation` goes up by one — by
//!   one, whatever the number of causes — when this log's offsets may now name
//!   different records than a client was told:
//!   - [`open_repair`](crate::BrokerLog::open_repair) truncated records, or this
//!     open's recovery cut a torn batch that held written bytes (a record of it, or a
//!     whole-sized frame of it: the recovery cannot tell a torn write from rot in the
//!     newest batch, so a cut that may have removed an acked record is announced);
//!   - the last run SERVED a weak tier ([`Durability::Ordered`](crate::Durability) or
//!     [`Durability::Relaxed`](crate::Durability); an Ordered request served Strict is
//!     recorded as Strict) and did not stop cleanly in THIS boot: its sidecar still
//!     says `Open` and names another boot, a boot it could not read, or a log off the
//!     boot volume — or it says `Lossy` (a durability flush failed), or the embedder's
//!     own prepare said so ([`Prepared::Unclean`](crate::Prepared)). A power loss may
//!     have taken acked records the page cache held (Relaxed), or the newest batches an
//!     ordering barrier had issued but not yet made durable (Ordered), and only a reboot
//!     can have done that: a process crash (`kill -9`) in the same boot loses nothing
//!     (the kernel still holds every byte, and the open's flush makes it durable) and
//!     moves nothing — a batch it left half-written included, which the open cuts as a
//!     write that never finished (see the recovery's same-boot rule). A Strict run never
//!     moves the generation for stopping uncleanly: its acks were on stable media;
//!   - the log is SHORTER than the last open saw, its retention base went backwards,
//!     or the record at the newest offset the last open saw is not the record it saw
//!     there (another log was put under this name).
//!
//!   A move caused by a cut is written to the sidecar BEFORE the cut (phase 1), so a
//!   crash right after a truncation cannot lose it; an open that dies there and is
//!   run again finds the cut already announced and moves nothing more for it.
//! - LINEAGE says where two generations still agree. When the generation moves because
//!   of an unclean stop, this open's own cut or a repair's — and the log before the cut
//!   is neither shorter than the last open saw, nor re-based, nor missing the record it
//!   saw last — the sidecar records `(new generation, common)`, `common` being the
//!   recovered head: offsets below it name the same records under both generations.
//!   [`LogIdentity::continues`] reads the chain (the newest [`Lineage::MAX`] steps), so
//!   a reader holding offsets under an earlier generation resumes at the lower of its
//!   cursor and every `common` since, instead of forgetting: it skips nothing and
//!   re-reads nothing below the fork. A log found shorter, re-based or foreign may be a
//!   restored copy or another file entirely, so it gets NO lineage, and readers forget
//!   as before.
//! - A REPLICA reports its leader's identity: the leader sends it with every
//!   replicated record, and a log that is a replication target adopts it (rewriting
//!   its sidecar) once a batch carrying it commits AND reaches the replica's newest
//!   record. The leader ships in order from what the replica confirmed, so by then
//!   every record the replica holds was appended or compared byte for byte; an echo
//!   of a shared PREFIX vouches for nothing above it (a replica that kept records its
//!   leader has since cut matches below the cut only), and an open that refused a
//!   replicated record for holding a different one adopts nothing more. A leader that
//!   predates log identity sends none, and its followers report their own. A replica never
//!   advances its leader's generation itself — only the leader numbers its own
//!   rewrites, and a follower's `(id, generation + 1)` could be the very name the
//!   leader later gives a rewrite of its own. A replica found rewritten (any of the
//!   cases above) takes a fresh random `id` instead, until its next replicated batch
//!   hands it the leader's again.
//!
//! # Honest boundary
//!
//! - An identity names a LINEAGE of bytes, not a file. A log COPIED elsewhere, with or
//!   without its sidecar, is two logs under one identity as soon as both take writes;
//!   nothing here can tell those copies apart.
//! - A power loss under a weak tier is announced, not prevented: the next open after
//!   the reboot moves the generation (with lineage), so no offset a client kept from
//!   the lost records is trusted against the records that reuse it. Under Ordered the
//!   loss is at most the batches acked since the last full flush (the horizon's, an
//!   escalation's, a clean close's), never an escalated record; under Relaxed, any batch
//!   no full flush covered (the open's, a clean close's, an escalated record's). The
//!   rule rests on the boot id (`astream-sys`): on a host that names none, or a log off
//!   the boot volume, every unclean weak open moves the generation, `kill -9` included
//!   — the price of not knowing. Hibernation keeps the boot and the page cache, and
//!   rightly moves nothing. A Strict-tier log loses no acked record to a power loss:
//!   the torn batch it cuts was never acknowledged.
//! - Rewriting by anything else is detected only against what the LAST OPEN (or clean
//!   close) saw: a rollback that ends at or above that head and keeps the record it saw
//!   last reuses the rolled-back offsets under an unchanged identity.
//! - A log restored from a backup TOGETHER WITH its sidecar carries the backup's
//!   identity, which is also the identity it carried while it grew past the backup:
//!   offsets a client kept from that growth are trusted against the records that will
//!   reuse them. Restore the log file alone — the sidecar already beside it then finds
//!   it shorter, or different, and moves the generation. (A copy taken while the log
//!   was written ends inside a frame; restored alone it is cut to its last whole record,
//!   as a shorter log, never refused as damage below the floor. A copy holding records
//!   past the sidecar's head is read whole, whichever build wrote them — but nothing
//!   here can see that those records are not the ones clients were told about at those
//!   offsets: the rollback residual above.)
//! - A revert to a build that predates log identity never reads or writes `<log>.id`:
//!   the records it appends carry no batch mark, and the next open of a sealing build
//!   reads each as a unit of its own, so none is cut. Its runs record nothing either —
//!   a Relaxed run of such a build that loses power is the one loss no build can
//!   announce.
//! - Deleting `<log>.id` makes the log read as one that predates identity: it
//!   re-derives its id from its bytes at generation 0. That is a new identity unless
//!   the bytes are exactly those of an EARLIER derivation — a pre-identity log that
//!   grew and was then restored to the copy it was derived from derives the identity
//!   it had before the growth, and offsets kept under it past those bytes are
//!   trusted. To give a log a new identity by hand, make its sidecar unreadable
//!   (overwrite it) rather than delete it: an unreadable sidecar always yields a
//!   fresh one.
//! - The `id` is minted from std's per-thread OS-seeded `RandomState` (the same source
//!   as the broker's handshake nonce), and derived with FNV-1a-128: distinct and
//!   collision-resistant against accident, not claimed cryptographic. Anyone who can
//!   write the log's directory can write any identity there.
//! - The identity is told to every peer that sends `Hello`, before it authenticates:
//!   it is a random name for the log, not a secret.

use std::io;
use std::path::{Path, PathBuf};

use astream_wire::{Frame, HEADER_SIZE};

use crate::storage::Dir;

/// The vocabulary, astream-wire's: the identity and lineage types with their text and wire
/// forms and [`LogIdentity::continues`], so a reader that keeps offsets outside the log
/// parses and compares them without linking the broker. This module keeps what only a
/// broker does with them: the sidecar, minting and deriving an `id`, settling an open, and
/// recording a lineage step.
pub use astream_wire::logid::{Lineage, LogIdentity};

#[cfg(clean_islands)]
#[path = "logid_island.rs"]
mod logid_island;
#[cfg(not(clean_islands))]
pub use crate::twins::logid_generation_advance;
#[cfg(clean_islands)]
pub use logid_island::logid_generation_advance;

contract_fn! {
    /// Verified check that a lineage chain entry count is within the 8-entry cap
    /// (`entries <= 8`), linked via `clean-kernel-defeq` to `logid_lineage_within_cap_isl`.
    #[must_use]
    pub fn logid_lineage_within_cap(entries: usize) -> bool
    clauses [ensures result == (entries <= 8)]
    {
        entries <= 8
    }
}

const fn encode_u64_le_bytes(v: u64) -> [u8; 8] {
    [
        v as u8,
        (v >> 8) as u8,
        (v >> 16) as u8,
        (v >> 24) as u8,
        (v >> 32) as u8,
        (v >> 40) as u8,
        (v >> 48) as u8,
        (v >> 56) as u8,
    ]
}

const fn encode_u128_le_bytes(v: u128) -> [u8; 16] {
    [
        v as u8,
        (v >> 8) as u8,
        (v >> 16) as u8,
        (v >> 24) as u8,
        (v >> 32) as u8,
        (v >> 40) as u8,
        (v >> 48) as u8,
        (v >> 56) as u8,
        (v >> 64) as u8,
        (v >> 72) as u8,
        (v >> 80) as u8,
        (v >> 88) as u8,
        (v >> 96) as u8,
        (v >> 104) as u8,
        (v >> 112) as u8,
        (v >> 120) as u8,
    ]
}

/// `lineage` with the step to `generation` added (`common` the recovered head): every
/// older step is clamped to `common` too — the log now agrees with an older generation at
/// most as far as it agrees with the newest — and only the newest [`Lineage::MAX`] are
/// kept. Only an open records a step, so this is the broker's, built on the wire type's
/// public [`steps`](Lineage::steps) and [`from_steps`](Lineage::from_steps).
///
/// A step that does not rise past the newest one is no lineage the wire can carry, and
/// records none: readers then forget, as for a move without lineage. An open's step
/// always rises (the generation it moved to is one past every step before it) except
/// when the generation is already `u64::MAX` and cannot move.
pub(crate) fn step(lineage: &Lineage, generation: u64, common: u64) -> Lineage {
    let older = lineage.steps();
    let skip = older.len().saturating_sub(Lineage::MAX.saturating_sub(1));
    let mut steps = Vec::new();
    if let Some(tail) = older.get(skip..) {
        for &(g, c) in tail {
            steps.push((g, c.min(common)));
        }
    }
    steps.push((generation, common));
    Lineage::from_steps(&steps).unwrap_or_default()
}

/// How the run that last wrote `<log>.id` stood with the log. Only FORMAT 2 records
/// it; a FORMAT 1 sidecar reads as `Closed`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum State {
    /// Stopped cleanly at `head`, everything below flushed in full (`close_clean`), or
    /// written by a build that predates the field.
    Closed,
    /// Serving. A weak-tier run still `Open` in another boot did not stop cleanly, and
    /// a power loss may have taken acked records: the next open moves the generation.
    Open,
    /// A full durability flush failed while serving, so acked records may not be on
    /// stable media whatever the boot: the next open moves the generation.
    Lossy,
    /// Written by an open BEFORE a cut that removes written bytes (phase 1): the
    /// generation already moved for a cut to `head`. An open that finds the same cut to
    /// make (the last one died before it was durable) moves nothing more for it, and
    /// classifies the log exactly as the one that died: the fields the boot rule reads
    /// (tier, boot, volume) are the run's before the cut, and `unclean` carries the
    /// verdict that open held for any other reason — the run's `Lossy` state, or the
    /// embedder's one-shot [`Prepared::Unclean`](crate::Prepared) — which this record
    /// replaces and which nothing else would remember.
    Cutting { unclean: bool },
}

impl State {
    const fn code(self) -> u8 {
        match self {
            State::Closed => 0,
            State::Open => 1,
            State::Lossy => 2,
            State::Cutting { unclean: false } => 3,
            State::Cutting { unclean: true } => 4,
        }
    }
}

/// The served-tier codes `<log>.id` and the `Hello` block use: 0 Strict, 1 Ordered,
/// 2 Relaxed. A code this build does not know reads as a weak tier (the direction that
/// moves the generation after an unclean stop, never the one that trusts it).
pub(crate) const SERVED_STRICT: u8 = 0;
/// See [`SERVED_STRICT`]. An Ordered run is a weak tier for the unclean-stop rule: its
/// acks were ordered, not durable, so a power loss can take the newest of them.
pub(crate) const SERVED_ORDERED: u8 = 1;
/// See [`SERVED_STRICT`].
pub(crate) const SERVED_RELAXED: u8 = 2;

/// What `<log>.id` holds: the identity, and what the open (or adoption, or clean close)
/// that wrote it saw — the evidence the NEXT open checks the log against.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Sidecar {
    pub(crate) identity: LogIdentity,
    /// The retention base then.
    base: u64,
    /// The head then.
    head: u64,
    /// Fingerprint of the stored frame at offset `head - 1`, the newest record then
    /// (all zero when there was none).
    newest: [u8; 16],
    /// The format this was READ in (1 or 2): a FORMAT 1 record is rewritten as
    /// FORMAT 2 at the next open, since the two never compare equal.
    format: u8,
    /// How the writing run stood with the log ([`State`]).
    pub(crate) state: State,
    /// The tier that run served ([`SERVED_STRICT`] and its siblings), or Strict for an
    /// Ordered run whose embedder acked only what a full flush covered
    /// ([`Acks::FullFlush`](crate::Acks)): the tier its acks stood at.
    pub(crate) served: u8,
    /// That run's boot ([`astream_sys::boot_session`]); all zero when unknown.
    pub(crate) boot: [u8; 16],
    /// Whether the log was on the boot volume, the device that loses power only
    /// together with the kernel (so the same-boot rule can trust its page cache).
    pub(crate) boot_volume: bool,
    /// A head the log is DURABLE through: everything below it was flushed in full by an
    /// open (after its flush) or a clean close. `None` for a FORMAT 1 record. Above a
    /// FORMAT 2 floor recovery judges damage by the batch marks — a sealing build's
    /// batches, or an older build's unmarked records, each a unit of its own; damage
    /// below it is never a torn write.
    pub(crate) floor: Option<u64>,
    /// Where generations agree ([`Lineage`]).
    pub(crate) lineage: Lineage,
}

const MAGIC: &[u8; 4] = b"ASID";
/// The sidecar's own format: 2 adds the run's state, tier, boot and volume, the durable
/// floor and the lineage. FORMAT 1 is still READ (as `Closed`, floor unknown, no
/// lineage). A sidecar this build cannot read (another format, a torn or tampered
/// write) is treated as absent: the log takes a new identity, which is the direction
/// that costs a consumer a re-read and never a skipped record — and what an older
/// build does with a FORMAT 2 sidecar after a revert (one log change, never a reused
/// offset; it then writes FORMAT 1, whose unknown floor the next open reads by the
/// rules that predate it). A build older still, from before log identity, never reads
/// or writes the sidecar at all: what it appends above the floor carries no batch mark,
/// which recovery reads as units of their own, never a torn batch.
const FORMAT: u8 = 2;
/// FORMAT 1's body: magic, format, identity, base, head, newest.
const BODY_LEN_1: usize = 4 + 1 + LogIdentity::WIRE_LEN + 8 + 8 + 16;
/// FORMAT 2's fixed extension before the lineage count: state, served, boot, volume, floor.
const BODY_V2_EXT_LEN: usize = 1 + 1 + 16 + 1 + 8;
/// FORMAT 2's fixed prefix before lineage steps: BODY_LEN_1 + BODY_V2_EXT_LEN.
const BODY_V2_FIXED_LEN: usize = BODY_LEN_1 + BODY_V2_EXT_LEN;
/// FORMAT 2's fixed part: FORMAT 1's, then state, served, boot, volume, floor and the
/// lineage count.
const BODY_LEN_2: usize = BODY_V2_FIXED_LEN + 1;

const fn encode_sidecar_fixed(sidecar: &Sidecar, floor: u64) -> [u8; BODY_V2_FIXED_LEN] {
    let g = sidecar.identity.generation;
    let b = sidecar.base;
    let h = sidecar.head;
    let f = floor;
    let state_code = sidecar.state.code();
    let vol_byte = (!sidecar.boot_volume) as u8;
    [
        MAGIC[0],
        MAGIC[1],
        MAGIC[2],
        MAGIC[3],
        FORMAT,
        sidecar.identity.id[0],
        sidecar.identity.id[1],
        sidecar.identity.id[2],
        sidecar.identity.id[3],
        sidecar.identity.id[4],
        sidecar.identity.id[5],
        sidecar.identity.id[6],
        sidecar.identity.id[7],
        sidecar.identity.id[8],
        sidecar.identity.id[9],
        sidecar.identity.id[10],
        sidecar.identity.id[11],
        sidecar.identity.id[12],
        sidecar.identity.id[13],
        sidecar.identity.id[14],
        sidecar.identity.id[15],
        g as u8,
        (g >> 8) as u8,
        (g >> 16) as u8,
        (g >> 24) as u8,
        (g >> 32) as u8,
        (g >> 40) as u8,
        (g >> 48) as u8,
        (g >> 56) as u8,
        b as u8,
        (b >> 8) as u8,
        (b >> 16) as u8,
        (b >> 24) as u8,
        (b >> 32) as u8,
        (b >> 40) as u8,
        (b >> 48) as u8,
        (b >> 56) as u8,
        h as u8,
        (h >> 8) as u8,
        (h >> 16) as u8,
        (h >> 24) as u8,
        (h >> 32) as u8,
        (h >> 40) as u8,
        (h >> 48) as u8,
        (h >> 56) as u8,
        sidecar.newest[0],
        sidecar.newest[1],
        sidecar.newest[2],
        sidecar.newest[3],
        sidecar.newest[4],
        sidecar.newest[5],
        sidecar.newest[6],
        sidecar.newest[7],
        sidecar.newest[8],
        sidecar.newest[9],
        sidecar.newest[10],
        sidecar.newest[11],
        sidecar.newest[12],
        sidecar.newest[13],
        sidecar.newest[14],
        sidecar.newest[15],
        state_code,
        sidecar.served,
        sidecar.boot[0],
        sidecar.boot[1],
        sidecar.boot[2],
        sidecar.boot[3],
        sidecar.boot[4],
        sidecar.boot[5],
        sidecar.boot[6],
        sidecar.boot[7],
        sidecar.boot[8],
        sidecar.boot[9],
        sidecar.boot[10],
        sidecar.boot[11],
        sidecar.boot[12],
        sidecar.boot[13],
        sidecar.boot[14],
        sidecar.boot[15],
        vol_byte,
        f as u8,
        (f >> 8) as u8,
        (f >> 16) as u8,
        (f >> 24) as u8,
        (f >> 32) as u8,
        (f >> 40) as u8,
        (f >> 48) as u8,
        (f >> 56) as u8,
    ]
}

type SidecarV1Fields = (u8, LogIdentity, u64, u64, [u8; 16]);
type SidecarV2ExtFields = (State, u8, [u8; 16], bool, u64);

const fn decode_sidecar_v1(raw: &[u8; BODY_LEN_1]) -> Option<SidecarV1Fields> {
    let format = raw[4];
    let id = [
        raw[5], raw[6], raw[7], raw[8], raw[9], raw[10], raw[11], raw[12], raw[13], raw[14],
        raw[15], raw[16], raw[17], raw[18], raw[19], raw[20],
    ];
    let generation = (raw[21] as u64)
        | ((raw[22] as u64) << 8)
        | ((raw[23] as u64) << 16)
        | ((raw[24] as u64) << 24)
        | ((raw[25] as u64) << 32)
        | ((raw[26] as u64) << 40)
        | ((raw[27] as u64) << 48)
        | ((raw[28] as u64) << 56);
    let identity = LogIdentity { id, generation };
    let base = (raw[29] as u64)
        | ((raw[30] as u64) << 8)
        | ((raw[31] as u64) << 16)
        | ((raw[32] as u64) << 24)
        | ((raw[33] as u64) << 32)
        | ((raw[34] as u64) << 40)
        | ((raw[35] as u64) << 48)
        | ((raw[36] as u64) << 56);
    let head = (raw[37] as u64)
        | ((raw[38] as u64) << 8)
        | ((raw[39] as u64) << 16)
        | ((raw[40] as u64) << 24)
        | ((raw[41] as u64) << 32)
        | ((raw[42] as u64) << 40)
        | ((raw[43] as u64) << 48)
        | ((raw[44] as u64) << 56);
    let newest = [
        raw[45], raw[46], raw[47], raw[48], raw[49], raw[50], raw[51], raw[52], raw[53], raw[54],
        raw[55], raw[56], raw[57], raw[58], raw[59], raw[60],
    ];
    if raw[0] != MAGIC[0] || raw[1] != MAGIC[1] || raw[2] != MAGIC[2] || raw[3] != MAGIC[3] {
        return None;
    }
    Some((format, identity, base, head, newest))
}

const fn split_sidecar_v1(raw: &[u8]) -> Option<(SidecarV1Fields, &[u8])> {
    let &[r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, ref rest @ ..] =
        raw
    else {
        return None;
    };
    let Some(fields) = decode_sidecar_v1(&[
        r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
        r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37,
        r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55,
        r56, r57, r58, r59, r60,
    ]) else {
        return None;
    };
    Some((fields, rest))
}

const fn decode_sidecar_v2_ext(raw: &[u8; BODY_V2_EXT_LEN]) -> Option<SidecarV2ExtFields> {
    let served = raw[1];
    let boot = [
        raw[2], raw[3], raw[4], raw[5], raw[6], raw[7], raw[8], raw[9], raw[10], raw[11], raw[12],
        raw[13], raw[14], raw[15], raw[16], raw[17],
    ];
    let floor = (raw[19] as u64)
        | ((raw[20] as u64) << 8)
        | ((raw[21] as u64) << 16)
        | ((raw[22] as u64) << 24)
        | ((raw[23] as u64) << 32)
        | ((raw[24] as u64) << 40)
        | ((raw[25] as u64) << 48)
        | ((raw[26] as u64) << 56);
    let state = match raw[0] {
        0 => State::Closed,
        1 => State::Open,
        2 => State::Lossy,
        3 => State::Cutting { unclean: false },
        4 => State::Cutting { unclean: true },
        _ => return None,
    };
    let boot_volume = match raw[18] {
        0 => true,
        1 => false,
        _ => return None,
    };
    Some((state, served, boot, boot_volume, floor))
}

const fn split_sidecar_v2_ext(raw: &[u8]) -> Option<(SidecarV2ExtFields, &[u8])> {
    let &[r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, ref lineage_wire @ ..] =
        raw
    else {
        return None;
    };
    let Some(fields) = decode_sidecar_v2_ext(&[
        r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
        r20, r21, r22, r23, r24, r25, r26,
    ]) else {
        return None;
    };
    Some((fields, lineage_wire))
}

/// The identity sidecar beside the log at `path`: `<log>.id`, the file the module docs
/// describe — what [`health_path`](crate::health_path) is to `<log>.health`.
///
/// Public so that nothing outside astream spells the name itself: a tool that copies or
/// restores a log WITH its sidecar (the honest boundary above says what that keeps), and
/// a test that reads its bytes to show an open refused before it rewrote anything. Its
/// CONTENTS are astream's and change by FORMAT; read them through an open, never
/// parse or write them. A test that needs a run that stopped uncleanly arms
/// [`Broker::arm_unclean_stop`](crate::Broker::arm_unclean_stop) instead of writing the
/// sidecar back, and one that needs a lineage builds it with
/// [`Lineage::from_steps`].
#[must_use]
pub fn identity_path(path: &Path) -> PathBuf {
    let mut p = path.to_path_buf();
    p.as_mut_os_string().push(".id");
    p
}

impl Sidecar {
    fn encode(&self) -> Vec<u8> {
        let mut p = Vec::with_capacity(BODY_LEN_2);
        let fixed = encode_sidecar_fixed(self, self.floor.unwrap_or(self.head));
        p.extend_from_slice(&fixed);
        self.lineage.put(&mut p);
        p
    }

    fn decode(bytes: &[u8]) -> Option<Sidecar> {
        let Ok(Some(d)) = Frame::decode(bytes) else {
            return None;
        };
        let p = d.frame.payload;
        if d.consumed != bytes.len() {
            return None;
        }
        let ((format, identity, base, head, newest), rest) = split_sidecar_v1(&p)?;
        let mut sidecar = Sidecar {
            identity,
            base,
            head,
            newest,
            format,
            state: State::Closed,
            served: SERVED_STRICT,
            boot: [0u8; 16],
            boot_volume: true,
            floor: None,
            lineage: Lineage::default(),
        };
        match format {
            1 if rest.is_empty() => {}
            2 => {
                let ((state, served, boot, boot_volume, floor), lineage_wire) =
                    split_sidecar_v2_ext(rest)?;
                sidecar.state = state;
                sidecar.served = served;
                sidecar.boot = boot;
                sidecar.boot_volume = boot_volume;
                sidecar.floor = Some(floor);
                sidecar.lineage = Lineage::from_wire(lineage_wire)?;
            }
            _ => return None,
        }
        Some(sidecar)
    }

    /// Where, among the log's stored frames from `base`, the newest record this sidecar
    /// saw sits: `None` when it saw none, or retention has since pruned it.
    fn newest_place(&self, base: u64) -> Option<usize> {
        let prev = self.head.checked_sub(1)?;
        let index = prev.checked_sub(base)?;
        usize::try_from(index).ok()
    }

    /// Whether the log still holds, at the newest offset this sidecar saw, the record it
    /// saw there: `named` is the stored frame at its place ([`Prior::newest_place`]). True
    /// when there is nothing to compare: it saw no record, retention has since pruned it,
    /// or the frames end before its place (a log SHORTER than it saw is caught by the head
    /// check, not here).
    fn still_names(&self, named: Option<&[u8]>) -> bool {
        match named {
            Some(frame) => fingerprint(frame) == self.newest,
            None => true,
        }
    }

    /// The lineage told beside the identity.
    pub(crate) const fn lineage(&self) -> &Lineage {
        &self.lineage
    }

    /// This record as a CLEAN CLOSE writes it: the run stopped at `head` with every
    /// byte below flushed in full, so the floor rises to it and the next open, in any
    /// boot, finds nothing it must move the generation for. `kept`: stored frames whose
    /// last is the newest (that frame alone, as a clean close reads it), for its fingerprint.
    pub(crate) fn closed(&self, base: u64, head: u64, kept: &[u8]) -> Sidecar {
        Sidecar {
            base,
            head,
            newest: newest_of(kept),
            format: FORMAT,
            state: State::Closed,
            floor: Some(head),
            ..self.clone()
        }
    }

    /// This record marked `Lossy`: a full durability flush failed, so the next open
    /// moves the generation whatever the boot.
    pub(crate) fn lossy(&self) -> Sidecar {
        Sidecar {
            format: FORMAT,
            state: State::Lossy,
            ..self.clone()
        }
    }
}

/// The fingerprint of the newest of `frames` (all zero when there are none).
fn newest_of(frames_bytes: &[u8]) -> [u8; 16] {
    match frames(frames_bytes).last() {
        Some(frame) => fingerprint(frame),
        None => [0u8; 16],
    }
}

/// What an open finds at `<log>.id`.
pub(crate) enum Prior {
    /// No sidecar: a log created before log identity, or by this open.
    Absent,
    /// A file this build cannot read as a sidecar (damaged, or another format): the log
    /// HAS had an identity, and this cannot say which.
    Unreadable,
    /// The identity the last open (or adoption, or clean close) recorded, with what it
    /// saw.
    Recorded(Sidecar),
}

impl Prior {
    pub(crate) const fn is_recorded(&self) -> bool {
        matches!(self, Prior::Recorded(_))
    }

    fn recorded(&self) -> Option<&Sidecar> {
        match self {
            Prior::Recorded(p) => Some(p),
            Prior::Absent | Prior::Unreadable => None,
        }
    }

    /// Where, among the log's stored frames from `base`, the newest record the last open
    /// saw sits, when it recorded one this log still retains: the frame the identity rules
    /// compare with what it saw ([`Facts::named`]).
    pub(crate) fn newest_place(&self, base: u64) -> Option<usize> {
        match self.recorded() {
            Some(p) => p.newest_place(base),
            None => None,
        }
    }

    /// Whether the head recorded is where the log stopped: a clean close wrote it
    /// ([`State::Closed`], as a FORMAT 1 record reads). Any other record's head is what an
    /// open, a lossy record or a cut saw, and the run may have appended past it before it
    /// stopped.
    pub(crate) fn closed_clean(&self) -> bool {
        matches!(self.recorded(), Some(p) if p.state == State::Closed)
    }

    /// The durable floor recovery judges by: a FORMAT 2 record's floor, raised to the
    /// retention base (records below it are gone); `None` — the rules that predate the
    /// floor — for anything else.
    pub(crate) fn floor(&self, base: u64) -> Option<u64> {
        let f = self.recorded()?.floor?;
        Some(f.max(base))
    }

    /// Whether the last run served the Relaxed tier, whose power loss can leave holes
    /// across batches (it issues no barrier at all).
    pub(crate) fn served_relaxed(&self) -> bool {
        match self.recorded() {
            Some(p) => p.served == SERVED_RELAXED,
            None => false,
        }
    }

    /// Why the last run may have lost acked records that this open cannot see were
    /// lost — the UNCLEAN verdict — or `None`. `prepared` is the embedder's own verdict
    /// ([`Prepared::Unclean`](crate::Prepared)); `boot` is this open's. Only a weak
    /// tier's run is ever unclean by astream's own rule: a Strict run's acks were on
    /// stable media. (Where THIS run serves matters to the next open, which reads it from
    /// the sidecar this open writes.)
    pub(crate) fn unclean(&self, prepared: Option<&str>, boot: Option<[u8; 16]>) -> Option<String> {
        if let Some(why) = prepared {
            return Some(format!("the embedder's prepare said so: {why}"));
        }
        let p = self.recorded()?;
        let weak_run =
            matches!(p.state, State::Open | State::Cutting { .. }) && p.served != SERVED_STRICT;
        let known_boot = p.boot != [0u8; 16];
        match p.state {
            State::Lossy => Some("a full flush failed while it served".to_string()),
            State::Cutting { unclean: true } => Some(
                "the open before this one held that verdict and died before its cut was durable"
                    .to_string(),
            ),
            _ if !weak_run => None,
            _ if !known_boot => Some("it served in a boot it could not name".to_string()),
            _ if !p.boot_volume => Some(
                "it served a log off the boot volume, whose cache a crash can lose".to_string(),
            ),
            _ => match boot {
                None => Some("this host cannot name the boot it is in".to_string()),
                Some(now) if now != p.boot => {
                    Some("it served in another boot and did not stop cleanly".to_string())
                }
                Some(_) => None,
            },
        }
    }

    /// Whether this open is in the SAME BOOT as the run the sidecar names, with the log
    /// on the boot volume then and now (`boot_volume`, this open's): the kernel that held
    /// that run's page cache has run throughout, so the bytes read are exactly the ones
    /// it wrote, and a file that ends inside its newest batch is a write its process
    /// never finished — never a power loss, never acked. Any tier: the boot is recorded
    /// by every open. False when either boot cannot be named.
    pub(crate) fn same_boot(&self, boot: Option<[u8; 16]>, boot_volume: bool) -> bool {
        match self.recorded() {
            Some(p) => p.boot != [0u8; 16] && Some(p.boot) == boot && p.boot_volume && boot_volume,
            None => false,
        }
    }
}

/// Read `<log>.id` through `dir` ([`Prior`]; a file that cannot be decoded is said on
/// stderr, since the log then takes a new identity); an I/O error otherwise.
pub(crate) fn read(dir: &Dir) -> io::Result<Prior> {
    let log = dir.log_path();
    let path = identity_path(log);
    let bytes = match dir.read_id() {
        Ok(Some(b)) => b,
        Ok(None) => return Ok(Prior::Absent),
        Err(e) => {
            return Err(io::Error::new(
                e.kind(),
                format!(
                    "cannot read the identity of {} from {}: {e}",
                    log.display(),
                    path.display()
                ),
            ))
        }
    };
    match Sidecar::decode(&bytes) {
        Some(sidecar) => Ok(Prior::Recorded(sidecar)),
        None => {
            eprintln!(
                "astream-broker: {} is not a log identity this build reads; {} takes a new \
                 identity, so every client re-reads it from scratch",
                path.display(),
                log.display()
            );
            Ok(Prior::Unreadable)
        }
    }
}

/// Durably replace `<log>.id` with `sidecar` through `dir` (on disk: tmp file, fsync,
/// rename, directory fsync, never following a link planted at either name), naming it
/// in the error.
pub(crate) fn write(dir: &Dir, sidecar: &Sidecar) -> io::Result<()> {
    let framed = match Frame::new(sidecar.encode()).encode() {
        Ok(f) => f,
        Err(e) => return Err(io::Error::new(io::ErrorKind::InvalidData, e)),
    };
    match dir.replace_id(&framed) {
        Ok(()) => Ok(()),
        Err(e) => Err(io::Error::new(
            e.kind(),
            format!(
                "cannot record the identity of {} in {}: {e}",
                dir.log_path().display(),
                identity_path(dir.log_path()).display()
            ),
        )),
    }
}

/// Everything one open knows about the log when it settles the identity: see
/// [`settle`].
pub(crate) struct Facts<'a> {
    /// The log is a replication target.
    pub(crate) replica: bool,
    /// The stored frame, among the intact ones from `base` up to the first damage (or the
    /// end) BEFORE any cut, at the place of the newest record the last open saw
    /// ([`Prior::newest_place`]): what that open's evidence is checked against. `None` when
    /// those frames hold none there.
    pub(crate) named: Option<&'a [u8]>,
    /// The head those frames reach.
    pub(crate) pre_cut_head: u64,
    /// The first and the newest of the stored frames that survive this open's cut, as
    /// stored ([`ends`]); `None` when none does.
    pub(crate) kept: Option<(&'a [u8], &'a [u8])>,
    /// The retention base.
    pub(crate) base: u64,
    /// The head after the cut.
    pub(crate) kept_head: u64,
    /// The unclean verdict ([`Prior::unclean`]), if any.
    pub(crate) unclean: bool,
    /// This open's recovery cut written bytes (a torn batch's records, or a whole-sized
    /// frame of it).
    pub(crate) cut_records: bool,
    /// This open is a repair that truncates.
    pub(crate) repair_cut: bool,
    /// The crash simulation's negative control NC9: record lineage even for a log found
    /// shorter than the last open saw (a restored copy). Never set outside it.
    pub(crate) lineage_on_shorter: bool,
    /// A fresh id, used when the rules call for one.
    pub(crate) minted: [u8; 16],
}

/// The identity (and lineage) one open settles, and whether it moved.
pub(crate) struct Settled {
    pub(crate) identity: LogIdentity,
    pub(crate) lineage: Lineage,
}

fn minted_settled(minted: [u8; 16]) -> Settled {
    Settled {
        identity: LogIdentity {
            id: minted,
            generation: 0,
        },
        lineage: Lineage::default(),
    }
}

/// Settle the identity of a log as one open finds it — see the module docs for the
/// rules. Pure: the caller records the result (phase 1 before a cut, phase 2 after the
/// flush).
pub(crate) fn settle(prior: &Prior, f: &Facts<'_>) -> Settled {
    match prior {
        // Never held a record (a created log always): no client can hold an offset
        // into it, so a fresh id is always right — and a sidecar beside it can only be
        // a deleted predecessor's, or this log's own from before it held anything.
        _ if f.kept_head == 0 => minted_settled(f.minted),
        // Every record pruned: nothing stored to derive from but two numbers, which
        // another such log can share — a fresh id instead.
        Prior::Absent if f.kept.is_none() => minted_settled(f.minted),
        Prior::Absent => Settled {
            identity: LogIdentity {
                id: derived_id(f.kept, f.base, f.kept_head),
                generation: 0,
            },
            lineage: Lineage::default(),
        },
        // It had an identity this cannot read: a derived id could be that very one
        // (or an earlier one), so only a fresh id is certainly a different name.
        Prior::Unreadable => minted_settled(f.minted),
        Prior::Recorded(p) => {
            // A cut the LAST open already announced (it wrote phase 1 and died before
            // the cut was durable): finding the same cut again moves nothing more.
            let announced = matches!(p.state, State::Cutting { .. }) && f.kept_head == p.head;
            let own_loss = (f.unclean || f.cut_records || f.repair_cut) && !announced;
            let other_log = f.base < p.base || f.kept_head < p.head || !p.still_names(f.named);
            if !(own_loss || other_log) {
                return Settled {
                    identity: p.identity,
                    lineage: p.lineage.clone(),
                };
            }
            if f.replica {
                // A replica's identity is its leader's lineage, numbered by the leader
                // alone: `generation + 1` here could be the name of a rewrite the
                // leader makes later. A fresh id is no name the leader can give; the
                // next replicated batch hands the leader's back.
                return minted_settled(f.minted);
            }
            let generation = p.identity.generation.saturating_add(1);
            // Lineage only for a loss this log can bound, judged on the bytes BEFORE
            // this open's cut: a repair below the last open's head keeps it (the
            // shortening is its own cut), a restored backup does not.
            let continuous = f.pre_cut_head >= p.head && f.base >= p.base && p.still_names(f.named);
            let lineage = if (own_loss && continuous) || f.lineage_on_shorter {
                step(&p.lineage, generation, f.kept_head)
            } else {
                Lineage::default()
            };
            Settled {
                identity: LogIdentity {
                    id: p.identity.id,
                    generation,
                },
                lineage,
            }
        }
    }
}

/// What an open records about the log it settled, around its flush.
pub(crate) struct Record<'a> {
    pub(crate) settled: &'a Settled,
    pub(crate) base: u64,
    pub(crate) head: u64,
    /// Stored frames whose last is the newest kept one (that frame alone, or every kept
    /// frame from `base`), for its fingerprint; empty when none is kept.
    pub(crate) kept: &'a [u8],
    pub(crate) served: u8,
    pub(crate) boot: Option<[u8; 16]>,
    pub(crate) boot_volume: bool,
}

impl Record<'_> {
    /// PHASE 2, written after the open's flush: the run is `Open` at this tier and
    /// boot, and the log is durable through its head — the new floor.
    pub(crate) fn serving(&self) -> Sidecar {
        Sidecar {
            identity: self.settled.identity,
            base: self.base,
            head: self.head,
            newest: newest_of(self.kept),
            format: FORMAT,
            state: State::Open,
            served: self.served,
            boot: self.boot.unwrap_or([0u8; 16]),
            boot_volume: self.boot_volume,
            floor: Some(self.head),
            lineage: self.settled.lineage.clone(),
        }
    }

    /// PHASE 1, written BEFORE a cut that removes written bytes: the moved identity and
    /// lineage, durable before their evidence goes, `Cutting` to `head`. The fields the
    /// boot rule reads (tier, boot, volume) are the LAST run's, and `unclean` is this
    /// open's verdict (from any cause), so an open that meets this record after this one
    /// dies decides exactly as this one did — even when the verdict came from the
    /// `Lossy` state this record replaces, or from the embedder's one-shot prepare. The
    /// floor never rises here (nothing new is durable yet).
    pub(crate) fn cutting(&self, prior: &Prior, unclean: bool) -> Sidecar {
        let last = prior.recorded();
        let (floor, served, boot, boot_volume) = match last {
            Some(p) => {
                let fl = match p.floor {
                    Some(f) => f.min(self.head),
                    None => self.head,
                };
                (fl, p.served, p.boot, p.boot_volume)
            }
            None => (
                self.head,
                self.served,
                self.boot.unwrap_or([0u8; 16]),
                self.boot_volume,
            ),
        };
        Sidecar {
            state: State::Cutting { unclean },
            served,
            boot,
            boot_volume,
            floor: Some(floor),
            ..self.serving()
        }
    }
}

/// A FORMAT 1 sidecar as the release before FORMAT 2 wrote it, framed: the crash
/// simulation's upgrade path starts from one.
#[cfg(test)]
pub(crate) fn format1_for_test(
    identity: LogIdentity,
    base: u64,
    head: u64,
    frames_bytes: &[u8],
) -> Vec<u8> {
    let mut p = Vec::with_capacity(BODY_LEN_1);
    p.extend_from_slice(MAGIC);
    p.push(1);
    identity.put(&mut p);
    p.extend_from_slice(&encode_u64_le_bytes(base));
    p.extend_from_slice(&encode_u64_le_bytes(head));
    p.extend_from_slice(&newest_of(frames_bytes));
    Frame::new(p).encode().expect("a sidecar frames")
}

/// Whether `recorded` already says exactly what `now` would (no write needed).
pub(crate) fn unchanged(prior: &Prior, now: &Sidecar) -> bool {
    prior.recorded() == Some(now)
}

/// Take `leader` as this log's identity (a replica reporting its leader's), keeping
/// what the open saw. A no-op when it already is. The replica's own lineage names its
/// own generations, not its leader's, so it is dropped.
pub(crate) fn adopt(dir: &Dir, sidecar: &Sidecar, leader: LogIdentity) -> io::Result<Sidecar> {
    if sidecar.identity == leader {
        return Ok(sidecar.clone());
    }
    let adopted = Sidecar {
        identity: leader,
        base: sidecar.base,
        head: sidecar.head,
        newest: sidecar.newest,
        format: FORMAT,
        state: sidecar.state,
        served: sidecar.served,
        boot: sidecar.boot,
        boot_volume: sidecar.boot_volume,
        floor: sidecar.floor,
        lineage: Lineage::default(),
    };
    write(dir, &adopted).map(|()| adopted)
}

/// Promote a replica sidecar to cluster leader: advances `identity.generation`
/// monotonically past `min_cluster_epoch` (when sharing `sidecar.identity.id`),
/// records a [`Lineage`] step `(next_gen, sidecar.head)` when `sidecar.head > 0`
/// and `next_gen == sidecar.identity.generation + 1`, and writes `<log>.id` durably.
pub(crate) fn promote(
    dir: &Dir,
    sidecar: &Sidecar,
    min_cluster_epoch: Option<LogIdentity>,
) -> io::Result<Sidecar> {
    let base_gen = match min_cluster_epoch {
        Some(ep) if ep.id == sidecar.identity.id => {
            crate::failover::failover_epoch_advance(sidecar.identity.generation, ep.generation)
        }
        _ => sidecar.identity.generation,
    };
    let next_gen = crate::failover::failover_epoch_advance(base_gen, base_gen.saturating_add(1));
    let lineage =
        if sidecar.head > 0 && sidecar.identity.generation.checked_add(1) == Some(next_gen) {
            step(&sidecar.lineage, next_gen, sidecar.head)
        } else {
            Lineage::default()
        };
    let promoted = Sidecar {
        identity: LogIdentity {
            id: sidecar.identity.id,
            generation: next_gen,
        },
        base: sidecar.base,
        head: sidecar.head,
        newest: sidecar.newest,
        format: FORMAT,
        state: sidecar.state,
        served: sidecar.served,
        boot: sidecar.boot,
        boot_volume: sidecar.boot_volume,
        floor: sidecar.floor,
        lineage,
    };
    write(dir, &promoted).map(|()| promoted)
}

const fn frame_header_len(header: &[u8; HEADER_SIZE]) -> usize {
    ((header[4] as u32)
        | ((header[5] as u32) << 8)
        | ((header[6] as u32) << 16)
        | ((header[7] as u32) << 24)) as usize
}

const fn split_frame_header_len(tail: &[u8]) -> Option<usize> {
    let &[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ref _rest @ ..] = tail else {
        return None;
    };
    Some(frame_header_len(&[
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ]))
}

struct Frames<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Iterator for Frames<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        let tail = self.bytes.get(self.pos..)?;
        let len = split_frame_header_len(tail)?;
        let end = self.pos.checked_add(HEADER_SIZE)?.checked_add(len)?;
        let frame = self.bytes.get(self.pos..end)?;
        self.pos = end;
        Some(frame)
    }
}

/// The stored frames in `bytes`, in order, without decoding a payload. `bytes` is a
/// prefix the log's recovery scan already accepted, so every header is well formed;
/// one that is short, or announces more bytes than follow, ends the walk. The length
/// is the header's `u32` at bytes 4..8 (the layout `astream_wire::frame` documents).
fn frames(bytes: &[u8]) -> Frames<'_> {
    Frames { bytes, pos: 0 }
}

/// The first of `bytes`' stored frames, header and payload as stored, or `None` when it
/// holds none: what an interrupted compaction is judged by at the next open
/// (`compact.rs`), and the first of the frames an open keeps ([`Facts::kept`]), which the
/// open reads alone (`open_scan::first_frame`).
pub(crate) fn first_frame(bytes: &[u8]) -> Option<&[u8]> {
    frames(bytes).next()
}

/// The `n`th of `bytes`' stored frames (from 0), as stored: the whole-buffer reference's
/// [`Facts::named`] (`open_scan_tests.rs`).
#[cfg(test)]
pub(crate) fn nth_frame(bytes: &[u8], n: usize) -> Option<&[u8]> {
    frames(bytes).nth(n)
}

/// A stored frame's [`fingerprint`], for the compaction intent's identities
/// (`compact.rs`).
#[cfg(feature = "retention")]
pub(crate) fn frame_fingerprint(frame: &[u8]) -> [u8; 16] {
    fingerprint(frame)
}

/// Where the last of `bytes`' stored frames starts, or `None` when it holds none.
pub(crate) fn last_frame_start(bytes: &[u8]) -> Option<usize> {
    let mut at = None;
    let mut pos = 0usize;
    for frame in frames(bytes) {
        at = Some(pos);
        pos = pos.saturating_add(frame.len());
    }
    at
}

/// FNV-1a-128 over `parts`, each prefixed with its length so no two different lists
/// hash the same bytes.
pub(crate) fn fnv1a_128(parts: &[&[u8]]) -> [u8; 16] {
    const OFFSET: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
    const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;
    let mut h = OFFSET;
    for part in parts {
        for &b in encode_u64_le_bytes(part.len() as u64)
            .iter()
            .chain(part.iter())
        {
            h ^= u128::from(b);
            h = h.wrapping_mul(PRIME);
        }
    }
    encode_u128_le_bytes(h)
}

/// A stored frame's fingerprint — over the bytes as stored, so an encrypted log's is
/// over ciphertext and says nothing about the plaintext.
fn fingerprint(frame: &[u8]) -> [u8; 16] {
    fnv1a_128(&[b"astream-log-id/frame/1", frame])
}

/// The id of a log that holds records and has no identity of its own yet:
/// deterministic in what it stores, so it is the same whichever build derives it and
/// however often — and different once the log holds anything else. `kept`: the first and
/// the newest of its stored frames ([`ends`]).
fn derived_id(kept: Option<(&[u8], &[u8])>, base: u64, head: u64) -> [u8; 16] {
    let base_bytes = encode_u64_le_bytes(base);
    let head_bytes = encode_u64_le_bytes(head);
    let (first, newest) = kept.unwrap_or((&[], &[]));
    fnv1a_128(&[
        b"astream-log-id/derived/1",
        &base_bytes,
        &head_bytes,
        first,
        newest,
    ])
}

/// The first and the newest of `bytes`' stored frames, each as stored, or `None` when it
/// holds none: what the identity rules read of the frames an open keeps ([`Facts::kept`]).
/// The open reads the two alone; the whole-buffer reference reads them here.
#[cfg(test)]
pub(crate) fn ends(bytes: &[u8]) -> Option<(&[u8], &[u8])> {
    let first = frames(bytes).next()?;
    let newest = frames(bytes).last()?;
    Some((first, newest))
}

/// A fresh id for a log that has just been created (or never held a record): two
/// independent std `RandomState`s — keyed from the OS once per thread, then stepped per
/// construction — over a process-wide counter, the wall clock, the process id and the
/// path. Distinct per creation; not claimed cryptographically random.
pub(crate) fn minted_id(log: &Path) -> [u8; 16] {
    use std::collections::hash_map::RandomState;
    use std::hash::{BuildHasher, Hash, Hasher};
    use std::sync::atomic::{AtomicU64, Ordering};
    static MINTED: AtomicU64 = AtomicU64::new(0);
    let seq = MINTED.fetch_add(1, Ordering::Relaxed);
    let now = match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_nanos(),
        Err(_) => 0,
    };
    let pid = std::process::id();
    let mut hasher0 = RandomState::new().build_hasher();
    hasher0.write_u64(seq);
    hasher0.write_u64(0);
    hasher0.write_u128(now);
    hasher0.write_u32(pid);
    log.hash(&mut hasher0);
    let h0 = encode_u64_le_bytes(hasher0.finish());
    let mut hasher1 = RandomState::new().build_hasher();
    hasher1.write_u64(seq);
    hasher1.write_u64(1);
    hasher1.write_u128(now);
    hasher1.write_u32(pid);
    log.hash(&mut hasher1);
    let h1 = encode_u64_le_bytes(hasher1.finish());
    [
        h0[0], h0[1], h0[2], h0[3], h0[4], h0[5], h0[6], h0[7], h1[0], h1[1], h1[2], h1[3], h1[4],
        h1[5], h1[6], h1[7],
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ident(byte: u8, generation: u64) -> LogIdentity {
        LogIdentity {
            id: [byte; 16],
            generation,
        }
    }

    fn sidecar(identity: LogIdentity, lineage: Lineage) -> Sidecar {
        Sidecar {
            identity,
            base: 4,
            head: 11,
            newest: [5u8; 16],
            format: FORMAT,
            state: State::Open,
            served: SERVED_RELAXED,
            boot: [9u8; 16],
            boot_volume: true,
            floor: Some(11),
            lineage,
        }
    }

    #[test]
    fn a_sidecar_round_trips_and_a_damaged_one_reads_as_none() {
        let s = sidecar(ident(3, 9), step(&Lineage::default(), 9, 7));
        let framed = Frame::new(s.encode()).encode().unwrap();
        assert_eq!(Sidecar::decode(&framed), Some(s.clone()));
        let mut flipped = framed.clone();
        *flipped.last_mut().unwrap() ^= 1;
        assert_eq!(Sidecar::decode(&flipped), None, "a CRC-failing sidecar");
        assert_eq!(Sidecar::decode(&framed[..framed.len() - 1]), None, "torn");
        let mut other_format = s.encode();
        other_format[4] = FORMAT + 1;
        let framed = Frame::new(other_format).encode().unwrap();
        assert_eq!(Sidecar::decode(&framed), None, "another sidecar format");
        let mut bad_state = s.encode();
        bad_state[BODY_LEN_1] = 9;
        let framed = Frame::new(bad_state).encode().unwrap();
        assert_eq!(
            Sidecar::decode(&framed),
            None,
            "a state this build does not know"
        );
        let mut long = s.encode();
        long.push(0);
        let framed = Frame::new(long).encode().unwrap();
        assert_eq!(
            Sidecar::decode(&framed),
            None,
            "a lineage longer than it says"
        );
    }

    /// FORMAT 1 (the release before) still reads: `Closed`, the floor unknown, no
    /// lineage — and it never compares equal to the FORMAT 2 record the next open
    /// writes, so that open rewrites it.
    #[test]
    fn a_format_1_sidecar_reads_as_closed_with_no_floor() {
        let framed = format1_for_test(ident(4, 2), 0, 3, &[]);
        let s = Sidecar::decode(&framed).expect("FORMAT 1 reads");
        assert_eq!(s.identity, ident(4, 2));
        assert_eq!((s.format, s.state, s.floor), (1, State::Closed, None));
        assert!(s.lineage.steps().is_empty());
        let prior = Prior::Recorded(s.clone());
        assert_eq!(prior.floor(0), None);
        assert_eq!(prior.unclean(None, Some([1; 16])), None);
        let rewritten = Sidecar {
            format: FORMAT,
            ..s
        };
        assert!(!unchanged(&prior, &rewritten));
    }

    /// The unclean verdict: only a weak tier's run still `Open` (or cutting) in another
    /// boot, an unnamed boot, off the boot volume, or `Lossy` whatever the tier — and the
    /// embedder's own verdict.
    #[test]
    fn the_unclean_verdict_follows_the_tier_the_boot_and_the_state() {
        let boot = Some([9u8; 16]);
        let other = Some([8u8; 16]);
        let with = |f: fn(&mut Sidecar)| {
            let mut s = sidecar(ident(1, 0), Lineage::default());
            f(&mut s);
            Prior::Recorded(s)
        };
        assert_eq!(
            with(|_| {}).unclean(None, boot),
            None,
            "same boot: a process crash"
        );
        assert!(with(|_| {}).unclean(None, other).is_some(), "another boot");
        assert!(
            with(|_| {}).unclean(None, None).is_some(),
            "this boot unnamed"
        );
        assert!(
            with(|s| s.boot = [0; 16]).unclean(None, boot).is_some(),
            "that boot unnamed"
        );
        assert!(
            with(|s| s.boot_volume = false)
                .unclean(None, boot)
                .is_some(),
            "off the boot volume"
        );
        assert!(
            with(|s| s.state = State::Cutting { unclean: false })
                .unclean(None, other)
                .is_some(),
            "a cut that died"
        );
        assert_eq!(
            with(|s| s.state = State::Cutting { unclean: false }).unclean(None, boot),
            None,
            "a cut that died in the run's own boot, for no verdict"
        );
        assert!(
            with(|s| {
                s.served = SERVED_STRICT;
                s.state = State::Cutting { unclean: true };
            })
            .unclean(None, boot)
            .is_some(),
            "a cut that died holding a verdict, at any tier and boot"
        );
        assert_eq!(
            with(|s| s.state = State::Closed).unclean(None, other),
            None,
            "a clean close"
        );
        assert_eq!(
            with(|s| s.served = SERVED_STRICT).unclean(None, other),
            None,
            "Strict never"
        );
        assert!(
            with(|s| {
                s.served = SERVED_STRICT;
                s.state = State::Lossy;
            })
            .unclean(None, boot)
            .is_some(),
            "Lossy at any tier"
        );
        assert!(with(|s| s.state = State::Closed)
            .unclean(Some("mark"), boot)
            .is_some());
        assert!(Prior::Absent.unclean(None, other).is_none());
    }

    /// PHASE 1 carries the verdict of the open that writes it, whatever its cause: a
    /// `Lossy` record (which `Cutting` replaces) or the embedder's one-shot prepare
    /// would otherwise be forgotten, and an open after a death between phase 1 and the
    /// cut would classify the log differently from the one that died — refusing what it
    /// cut, or moving the generation a second time.
    #[test]
    fn phase_1_remembers_the_verdict_it_cut_under() {
        let boot = [9u8; 16];
        for (prior_state, prepared) in [(State::Lossy, None), (State::Open, Some("mark"))] {
            // The last open recorded its head, 7, as the floor; its run then wrote
            // records 7..11, which this open keeps but has not yet flushed.
            let prior = Prior::Recorded(Sidecar {
                state: prior_state,
                head: 7,
                floor: Some(7),
                ..sidecar(ident(1, 0), Lineage::default())
            });
            let verdict = prior.unclean(prepared, Some(boot));
            assert!(verdict.is_some(), "{prior_state:?}");
            let settled = Settled {
                identity: ident(1, 1),
                lineage: step(&Lineage::default(), 1, 11),
            };
            let record = Record {
                settled: &settled,
                base: 4,
                head: 11,
                kept: &[],
                served: SERVED_RELAXED,
                boot: Some(boot),
                boot_volume: true,
            };
            let cutting = Prior::Recorded(record.cutting(&prior, verdict.is_some()));
            assert!(
                cutting.unclean(None, Some(boot)).is_some(),
                "the next open, same boot, no prepare, still holds the verdict ({prior_state:?})"
            );
            assert_eq!(
                cutting.floor(4),
                Some(7),
                "the floor never rises in phase 1"
            );
        }
    }

    /// The same-boot test: a named boot equal to this open's, the log on the boot
    /// volume then and now. Anything unknown is not the same boot.
    #[test]
    fn the_same_boot_needs_a_named_boot_and_the_boot_volume() {
        let boot = Some([9u8; 16]);
        let with = |f: fn(&mut Sidecar)| {
            let mut s = sidecar(ident(1, 0), Lineage::default());
            f(&mut s);
            Prior::Recorded(s)
        };
        assert!(with(|_| {}).same_boot(boot, true));
        assert!(with(|s| s.served = SERVED_STRICT).same_boot(boot, true));
        assert!(
            !with(|_| {}).same_boot(Some([8u8; 16]), true),
            "another boot"
        );
        assert!(!with(|_| {}).same_boot(None, true), "this boot unnamed");
        assert!(!with(|s| s.boot = [0; 16]).same_boot(None, true));
        assert!(!with(|s| s.boot_volume = false).same_boot(boot, true));
        assert!(
            !with(|_| {}).same_boot(boot, false),
            "off the boot volume now"
        );
        assert!(!Prior::Absent.same_boot(boot, true));
    }

    /// An open's lineage step clamps older steps to each newer common and keeps the
    /// newest eight, and `continues` (astream-wire's) reads the chain it builds: the same
    /// identity continues everywhere, a gap in the chain, a window outrun or another id
    /// does not. A step that does not rise records no lineage at all.
    #[test]
    fn a_step_clamps_keeps_eight_and_continues_reads_the_chain() {
        let l = step(&step(&step(&Lineage::default(), 1, 10), 2, 7), 3, 9);
        assert_eq!(l.steps(), &[(1, 7), (2, 7), (3, 9)]);
        let now = ident(5, 3);
        assert_eq!(now.continues(ident(5, 3), &l), Some(u64::MAX));
        assert_eq!(now.continues(ident(5, 2), &l), Some(9));
        assert_eq!(now.continues(ident(5, 0), &l), Some(7));
        assert_eq!(now.continues(ident(6, 0), &l), None, "another log");
        let gap = step(&step(&Lineage::default(), 1, 10), 3, 9);
        assert_eq!(
            now.continues(ident(5, 0), &gap),
            None,
            "a move without lineage"
        );
        let mut long = Lineage::default();
        for g in 1..=10 {
            long = step(&long, g, 100 - g);
        }
        assert_eq!(long.steps().len(), Lineage::MAX);
        assert_eq!(long.steps()[0], (3, 90));
        assert_eq!(
            ident(5, 10).continues(ident(5, 1), &long),
            None,
            "older than the window"
        );
        assert_eq!(ident(5, 10).continues(ident(5, 2), &long), Some(90));
        let mut wire = Vec::new();
        long.put(&mut wire);
        assert_eq!(
            Lineage::from_wire(&wire),
            Some(long.clone()),
            "the wire carries it"
        );
        let at_max = step(&Lineage::default(), u64::MAX, 4);
        assert_eq!(at_max.steps(), &[(u64::MAX, 4)]);
        assert_eq!(
            step(&at_max, u64::MAX, 3),
            Lineage::default(),
            "a step that does not rise records none"
        );
    }

    #[test]
    fn frames_walks_headers_and_stops_at_a_short_tail() {
        let mut bytes = Vec::new();
        for body in [&b"a"[..], b"bcd", b""] {
            bytes.extend_from_slice(&Frame::new(body.to_vec()).encode().unwrap());
        }
        let walked: Vec<&[u8]> = frames(&bytes).collect();
        assert_eq!(walked.len(), 3);
        assert_eq!(walked.concat(), bytes);
        assert_eq!(
            frames(&bytes[..bytes.len() - 1]).count(),
            2,
            "a short last frame"
        );
        assert_eq!(frames(&[]).count(), 0);
    }

    #[test]
    fn minted_ids_differ_and_derived_ones_repeat_only_for_the_same_bytes() {
        let p = Path::new("/nonexistent/log");
        assert_ne!(minted_id(p), minted_id(p));
        let one = Frame::new(b"one".to_vec()).encode().unwrap();
        let two = [one.clone(), Frame::new(b"two".to_vec()).encode().unwrap()].concat();
        assert_eq!(derived_id(ends(&two), 0, 2), derived_id(ends(&two), 0, 2));
        assert_ne!(derived_id(ends(&two), 0, 2), derived_id(ends(&one), 0, 1));
        assert_ne!(
            derived_id(ends(&two), 0, 2),
            derived_id(ends(&two), 5, 7),
            "base and head count"
        );
    }
}
