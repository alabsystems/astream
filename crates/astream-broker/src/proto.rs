//! The broker wire protocol: each message is exactly one `astream_wire::Frame`
//! (inheriting CRC + the 16 MiB cap). The frame payload is a tiny tagged codec —
//! `| PROTO_VERSION:u8 | tag:u8 | body |`, every variable `u32` length
//! bounds-checked before slicing, the same fail-closed discipline as the engine
//! envelope. `read_frame`/`write_frame` are generic over `Read`/`Write`, so the
//! codec is unit-testable in memory with no socket.
//!
//! # Refusal codes
//!
//! `Response::Error::code` is the CLASS of a refusal; the message says why in words,
//! and is the same whatever the code. A client branches on the code — through
//! [`crate::client::BrokerRefusal`], which the client puts inside the `io::Error` a
//! refused request returns.
//!
//! | code | name                   | the same request, resent unchanged             |
//! |------|------------------------|------------------------------------------------|
//! | 2    | [`ERR_BAD_SUBJECT`]    | is refused again: the subject is not a subject |
//! | 3    | [`ERR_BAD_FILTER`]     | is refused again: the filter is not a filter   |
//! | 5    | [`ERR_REFUSED`]        | may land: NOT known to be permanent            |
//! | 6    | [`ERR_TOO_MANY_CONNS`] | may be served on a later connection            |
//! | 7    | [`ERR_RECORD_REFUSED`] | is refused again, on the request's own terms   |
//! | 8    | [`ERR_UNAUTHORIZED`]   | is refused again on this connection's grants   |
//! | 9    | [`ERR_PROTOCOL`]       | is refused again: another protocol; it closes  |
//! | 10   | [`ERR_SUBJECT_BOUND`]  | lands only once the subject enters the index   |
//! | 11   | [`ERR_RETIRE_REFUSED`] | lands once the retire guard condition lifts    |
//! | 12   | [`ERR_RATE_LIMITED`]   | lands once the producer's token bucket refills |
//! | 13   | [`ERR_ORIGIN_REFUSED`] | is refused again: the relayed record is not its origin's |
//! | 14   | [`ERR_RELAY_NOT_READY`] | lands once this broker has been given origin keys |
//! | 15   | [`ERR_ORIGIN_UNKNOWN`] | lands once this broker takes the record's origin |
//! | 16   | [`ERR_FRESH_HELD`]     | its key was held; choose a new key after reconnect |
//! | 17   | [`ERR_FRESH_FENCED`]   | was not attempted after an earlier fresh failure |
//!
//! Codes 2, 3, 7, 8, 9 and 13 are PERMANENT for the request that drew them: sent again,
//! unchanged, on the same connection, it is refused again, so a retry is a loop.
//! Code 5 is the fail-safe reading. A broker older than codes 7 and 8 answered every
//! refusal but 2, 3 and 6 with 5, permanent ones included, so a client reads 5 as
//! "not known to be permanent" — it may retry — and never as "will succeed". An
//! unknown code reads as 5. (Code 4 once meant a malformed request and is not
//! reused.)
//!
//! Code 10 is NOT permanent, and it is not 5 either: it names one condition, a
//! producer at its distinct-subject budget asking for one subject more, so a client
//! can tell it from every other refusal and decide by what it knows. The broker
//! cannot know whether another producer will ever introduce the subject — after
//! which the identical request is an update and lands — but the producer often can:
//! one that is the only writer of its subjects (its own lanes) may drop the record
//! for good, while one that shares a subject may wait for it. A broker older than
//! code 10 answers it with 5.
//!
//! Code 15 is NOT permanent either, and it is the same kind of answer: the broker
//! names one condition, a relayed record whose origin it does not take now (it holds
//! no key for it, or that key stands revoked), and the carrier decides. The broker
//! cannot know whether its embedder will give it the key or lift the revocation (a
//! node seated, or its removal voided, after the record set out), but the carrier
//! often can: its own standings say whether it still seats the origin. A relay bridge
//! holds such a record while its embedder says so
//! ([`FederationBridge::hold_while`](crate::federation::FederationBridge::hold_while)).
//! A broker older than code 15 answers it with 13.
//!
//! Codes 16 and 17 identify fresh-publish recovery, not permanently invalid records. Either
//! leaves later fresh publishes fenced until reconnect. An unknown transport outcome is not
//! one of these refusals and says nothing about whether a complete request committed.
//!
//! One code-8 refusal is told apart by its WORDS, not by a code of its own: an
//! expired capability's message starts [`CAP_EXPIRED_PREFIX`], and
//! [`BrokerRefusal::is_expired`](crate::client::BrokerRefusal::is_expired) reads it.
//! So is one code-5 refusal: every write a POISONED log refuses starts
//! [`LOG_POISONED_PREFIX`], and
//! [`BrokerRefusal::is_poisoned`](crate::client::BrokerRefusal::is_poisoned) reads it.
//!
//! # The one layout every version keeps
//!
//! A refusal is `[version:u8][0x83][code:u8][len:u32 LE][msg]` under EVERY
//! `PROTO_VERSION` — protocol 1 wrote exactly this, 2 does, and a later version must
//! too — and a decoder reads nothing after `msg`. Everything else on the wire may
//! change with the version byte; this may not. It is what lets a broker answer a peer
//! that speaks ANOTHER protocol at all: [`encode_protocol_refusal`] stamps this layout
//! with the PEER's version byte, so the peer's own decoder reads it, whichever version
//! that is.
//!
//! # What the wire says about durability
//!
//! Four things, all additive, none spending a request tag, a protocol version or an
//! error code:
//!
//! - **The health of the log**: tag 0x04 of the `Hello` answer's extension block
//!   ([`NonceExt::health`], [`HelloHealth`]) — whether the log is POISONED (it refuses
//!   every write until it is reopened) and why, and the flushes it has issued since it
//!   opened (barriers, full, skipped, failed). Read by the broker without the log's
//!   lock, so a status line on the host learns from the broker itself whether the log
//!   it is about to call `connected` takes writes.
//! - **The tier served**: tag 0x01 of the `Hello` answer's extension block
//!   ([`NonceExt::durability`], [`ServedInfo`]) — the tier asked for, the tier in force
//!   and why they differ, the Ordered horizon and the escalation table's size. A status
//!   line on any host reads the tier from the broker, never from how it was started. It
//!   can change in a running broker in one direction only: a log that latches to Strict
//!   (a barrier refused, a full flush failed) answers `served = Strict` from then on.
//! - **The durable head**: [`Response::Mark`]'s optional `durable` trailer, on EVERY
//!   `Mark` a broker of this build sends — every record below it is on stable media by
//!   a full flush. It is the in-band proof a reader on another host needs: a `Fetch` head
//!   query (`max = 0`) answers "is offset `o` durable?" with `durable > o`. An older
//!   broker sends none; it serves Strict or Relaxed, never Ordered, and the one before
//!   Ordered says which in its `Hello` block: on Strict read `None` as "durable =
//!   visible", on Relaxed as "nothing acked since the open (or a clean close) is
//!   durable". A broker older still sends no block and may serve Relaxed unannounced:
//!   "durable = visible" holds there only for a reader that knows its broker strict. In
//!   process the same value is [`Broker::durable_head`](crate::Broker::durable_head).
//! - **Durable marks**: on a broker that SERVES Ordered, a subscriber that asked for
//!   idle marks (`Request::IdleMarks`, which `Client::subscribe` negotiates) gets one
//!   extra `Mark` when a full flush covers records it was delivered and not yet told are
//!   durable — at most one per such flush. Not on Strict (the durable head is the
//!   visible head after every batch, so a mark per delivery would say nothing) and not
//!   on Relaxed (it does not move between opens). A log that LATCHES from Ordered to
//!   Strict while serving keeps sending them for the rest of its open — then one per
//!   delivered batch, every batch being flushed in full — because a subscriber that was
//!   told Ordered may be holding back what it was delivered until a durable mark covers
//!   it, and nothing on its stream says the tier changed.
//!
//! And one thing more for a writer OUTSIDE the log, which spends a request tag: the log's
//! DEVICE, tag 0x06 of the `Hello` answer's extension block ([`NonceExt::device`],
//! [`LogDevice`]) — its `st_dev` and whether its full flush drains the device — and
//! [`Request::Settle`] (`0x19`, [`REQUEST_SETTLE`]), a full flush issued after the broker
//! read it, never skipped. A writer whose own file is on that device orders its writes by a
//! barrier, sends the settle, and knows them on stable media once it is answered: one drain
//! of the device, the broker's, where its own full flush would be another.
//!
//! An escalated record (the broker's escalation table; see
//! [`Escalation`](crate::Escalation)) never needs any of these to be safe: the broker
//! holds the visible head at it until its full flush has succeeded, so no reader is ever
//! delivered, and no producer acked, an escalated record that a power loss can take.

use astream_wire::frame::{MAGIC as FRAME_MAGIC, VERSION as FRAME_VERSION};
use astream_wire::{crc32_ieee, Frame, FrameError, HEADER_SIZE, MAX_PAYLOAD_LEN};
use std::io::{self, Read, Write};

use crate::logid::{Lineage, LogIdentity};

/// Protocol version (the payload's first byte).
pub const PROTO_VERSION: u8 = 2;

/// Refused, and NOT known to be permanent: a write that failed to append, commit or
/// fsync, a batch another record's I/O failure aborted, a quorum not reached, a will
/// the log could not persist, a broker stopping, a request this broker cannot decode
/// — and ANY refusal decided inside a batch that then rolled back, which was judged
/// against records that never landed (a subject-bound refusal included: the batch's
/// own new subjects it counted never landed). Resending may land. A broker that
/// predates [`ERR_RECORD_REFUSED`] and [`ERR_UNAUTHORIZED`] sent this code for every
/// refusal but 2, 3 and 6, and one that predates [`ERR_SUBJECT_BOUND`] sends it for a
/// producer at its distinct-subject budget, so it is also what a refusal of unknown
/// permanence looks like.
pub const ERR_REFUSED: u8 = 5;

/// A subject the request names is not a valid subject (permanent).
pub const ERR_BAD_SUBJECT: u8 = 2;

/// A filter the request names is not a valid filter (permanent).
pub const ERR_BAD_FILTER: u8 = 3;

/// The broker is at its connection cap (`MAX_CONNS`): it answered this connection
/// with the refusal and closed it. Not about the request — a later connection may be
/// served.
pub const ERR_TOO_MANY_CONNS: u8 = 6;

/// The request is refused ON ITS OWN TERMS, whatever capability carried it: a record
/// too large for the log, a reserved (broker-internal) subject, a will at a sequence
/// in the reserved ack half, a name past the length bound, a second will under
/// another producer id on one connection. Resent unchanged, it is refused again
/// (permanent).
pub const ERR_RECORD_REFUSED: u8 = 7;

/// The connection's capabilities do not authorize the request (the message starts
/// `unauthorized:`): no attached grant covers it, the grant that did has expired, a
/// publish names a producer id its grant does not bind, or an `Attach` was refused —
/// a proof that does not verify, no `Hello` first, a full keyring, a producer id
/// bound to another principal — or a guarded connection stayed unattached past its
/// deadline. Resent unchanged on this connection it is refused again (permanent); a
/// different capability is a different request.
///
/// One of those causes is told apart from the rest: a capability whose `exp=` has
/// passed answers with a message that starts [`CAP_EXPIRED_PREFIX`].
pub const ERR_UNAUTHORIZED: u8 = 8;

/// How an EXPIRED capability's [`ERR_UNAUTHORIZED`] refusal begins, word for word.
/// The broker sends it at all three places an expiry is decided: at the `Attach`
/// door, on a request every grant that covered has lapsed for, and when a stream
/// ends at its grants' deadline. No other refusal starts with it, and every refusal
/// for an expired capability does.
///
/// An expiry needs a different remedy from every other refusal of code 8: the
/// capability is genuine, its time is up, and minting it again with a later `exp=`
/// fixes it. A forged or tampered grant needs a new secret or a new capability, and a
/// request outside the grants needs a wider one. Code 8 is one class, so the
/// difference is carried in the words, and astream owns both the words and the
/// client that reads them:
/// [`BrokerRefusal::is_expired`](crate::client::BrokerRefusal::is_expired) is the
/// test. Adding a code instead would have changed the wire, which this does not.
///
/// A broker older than this constant sent the same words at the attach and at a
/// stream's deadline. On a request whose grants had lapsed it said "does not grant",
/// so against such a broker that one refusal reads as not expired.
pub const CAP_EXPIRED_PREFIX: &str = "unauthorized: capability expired";

/// How every write a POISONED log refuses begins, word for word: an [`ERR_REFUSED`]
/// refusal of a publish, a commit, a will, a binding or a flush the writer answers
/// while the log is poisoned ([`BrokerLog::poisoned`](crate::BrokerLog::poisoned)),
/// followed by the reason in parentheses. No other refusal starts with it.
///
/// A poisoned log is a refusal of a kind no resend on this broker cures: a full flush
/// failed with acked or held records no full flush covers, or a rollback could not put
/// the file back, and every write is refused until the log is REOPENED — a new open,
/// which only the embedder can make (exit, and let a supervisor start the broker
/// again). Code 5 is right for it, because to the producer it is transient: the same
/// record lands once the log is reopened. But a producer that retries a code-5
/// refusal on the same connection waits for ever, and one that reads code 5 as "the
/// broker is answering" reports a broker as working while it takes nothing. So the
/// condition is carried in the words, which astream owns, and
/// [`BrokerRefusal::is_poisoned`](crate::client::BrokerRefusal::is_poisoned) is the
/// test: a producer that sees it knows the connection is worth nothing until the
/// broker restarts. Adding a code instead would have changed the wire, which this
/// does not.
///
/// The op whose own flush POISONED the log (an escalated publish, a held commit, a
/// `flush_durable`) is answered with what happened to it — "outcome unknown, resend" —
/// not with this; its resend is answered with this. A broker older than this constant
/// answered the first op of a batch on a poisoned log with `append failed: log
/// poisoned (…)` and every later one with `batch aborted (prior append I/O error)`, so
/// against it this is `false`: the fail-safe reading, under which a producer retries.
pub const LOG_POISONED_PREFIX: &str = "log poisoned";

/// The request is in ANOTHER astream protocol: its version byte is not this broker's
/// [`PROTO_VERSION`]. The broker answers it once, with [`encode_protocol_refusal`] —
/// the refusal layout every version keeps, stamped with the PEER's version byte so the
/// peer can read it — and closes the connection, because nothing more the peer sends
/// can be decoded here. Permanent: only a client of the same protocol is served. This
/// crate's client reads it — it names the broker's version — and any reply stamped
/// with another version as a [`ProtocolMismatch`](crate::client::ProtocolMismatch)
/// naming both versions, not as a [`BrokerRefusal`](crate::client::BrokerRefusal).
pub const ERR_PROTOCOL: u8 = 9;

/// The producer already holds its whole distinct-subject budget
/// ([`MAX_SUBJECTS_PER_PRODUCER`](crate::store::MAX_SUBJECTS_PER_PRODUCER), counting
/// the subjects its registered wills have reserved), and this publish, transaction or
/// will names a subject NEW to the last-value index. Nothing was appended.
///
/// NOT permanent. A producer at the budget can still UPDATE a subject the index
/// holds, whoever introduced it, so the identical request lands once another
/// producer introduces this subject; it also lands once the producer's own count
/// falls. What it is NOT is a transient write failure: on a broker that nothing else
/// changes, resending it is refused again. So a client that knows no other producer
/// ever writes the subject — a producer's own lanes — may treat it as final for that
/// record, and one that shares the subject may hold the record for the subject to
/// appear. [`Request::Budget`] reads the count and the budget.
///
/// A refusal of this kind inside a batch that then rolled back is [`ERR_REFUSED`]
/// instead: the subjects it was counted against never landed. A broker that predates
/// this code sends [`ERR_REFUSED`].
pub const ERR_SUBJECT_BOUND: u8 = 10;

/// A subject retirement was refused because the subject's index entry is charged to
/// another producer ([`RETIRE_CHARGED_PREFIX`]), because a will that can still append
/// targets the subject ([`RETIRE_WILL_PREFIX`]), or because the retirement's conditional
/// log identity or offset does not match ([`RETIRE_LOG_PREFIX`]).
///
/// NOT permanent: `charged` lifts when the subject changes, `will` when the targeting
/// will fires, is fenced, or is replaced, and `log` once the client re-reads `Last`.
pub const ERR_RETIRE_REFUSED: u8 = 11;

/// Fixed prefix for a [`ERR_RETIRE_REFUSED`] refusal when the subject is charged to
/// another producer.
pub const RETIRE_CHARGED_PREFIX: &str = "charged: ";

/// Fixed prefix for a [`ERR_RETIRE_REFUSED`] refusal when a will that can still append
/// targets the subject.
pub const RETIRE_WILL_PREFIX: &str = "will: ";

/// Fixed prefix for a [`ERR_RETIRE_REFUSED`] refusal when the conditional log identity
/// or offset does not match.
pub const RETIRE_LOG_PREFIX: &str = "log: ";

/// Fixed prefix for a [`ERR_RECORD_REFUSED`] refusal when a retire is offered to a log
/// that prefix retention has cut (`base > 0`).
pub const RETIRE_CUT_PREFIX: &str = "cut: ";

/// A publish or `ProcessAndProduce` was refused because the producer's (or bound
/// capability principal's) monotone token bucket has insufficient record or byte tokens
/// ([`crate::RateLimit`], `DESIGN-aterm-fabric` T9 & T17). Nothing was appended or queued
/// to the writer thread.
///
/// NOT permanent: the identical request lands once the bucket refills (see
/// [`BrokerRefusal::is_rate_limited`](crate::client::BrokerRefusal::is_rate_limited) and
/// [`BrokerRefusal::retry_after_ms`](crate::client::BrokerRefusal::retry_after_ms)). An
/// older client that does not know code 12 reads it as non-permanent (`!is_permanent()`).
pub const ERR_RATE_LIMITED: u8 = 12;

/// A relayed record was refused for what it is, not for who carried it or whose it is: its
/// sequence is in the reserved ack half, its subject names no owner or another producer's, or its
/// signature does not verify against its origin's key. Nothing was appended. PERMANENT: the
/// record will never be its origin's. A bridge counts it and carries on: the next record is not
/// this one's fault, and one forged record must not stop an edge.
pub const ERR_ORIGIN_REFUSED: u8 = 13;

/// A relayed record was refused because of this broker, not the record: it holds no origin keys
/// yet, or was built without the `relay` feature. A bridge stops and commits nothing, so what it
/// was carrying is still there when the keys come.
pub const ERR_RELAY_NOT_READY: u8 = 14;

/// A relayed record's origin is not one this broker takes now: it holds no key for it among its
/// origin keys, or that key (or the principal it derives) stands revoked. Nothing was appended,
/// and the record was not judged. NOT permanent: the embedder may yet give the broker the key, or
/// lift the revocation (a node seated, or its removal voided, after the record set out). Whether
/// to wait is the carrier's question
/// ([`BrokerRefusal::is_origin_unknown`](crate::client::BrokerRefusal::is_origin_unknown)): a relay
/// bridge holds such a record back while its embedder says the origin is still seated, offering it
/// again and committing its group below it, so an edge whose destination was only behind passes
/// nothing ([`FederationBridge::hold_while`](crate::federation::FederationBridge::hold_while)). A
/// broker that predates this code sends [`ERR_ORIGIN_REFUSED`].
pub const ERR_ORIGIN_UNKNOWN: u8 = 15;

/// A [`Request::FreshPublish`] key was already held, including through producer lineage.
/// Nothing was appended, even when the subject and body equal the held record. Every later
/// fresh publish on this connection is refused until reconnect; ordinary publishes keep their
/// existing semantics. A caller may choose a new producer key after handling the collision.
pub const ERR_FRESH_HELD: u8 = 16;

/// A [`Request::FreshPublish`] followed a failed fresh publish on this connection. Nothing was
/// appended. Reconnect before sending fresh publishes again; this is not another key collision.
pub const ERR_FRESH_FENCED: u8 = 17;

/// Fixed prefix for every [`ERR_RATE_LIMITED`] refusal, followed immediately by the
/// minimum millisecond wait `<ms>` (`>= 1`) before the bucket refills enough to admit
/// the request (or, if a single record exceeds `burst_bytes`, the burst-deficit hint).
pub const RATE_LIMITED_PREFIX: &str = "rate limited: retry-after-ms=";

/// How a `Fetch` below the OLDEST offset of its filter is refused, word for word: an
/// [`ERR_RECORD_REFUSED`] whose message starts `retained-from=<off>`, the offset at and
/// above which the filter is complete (`REQUIREMENTS` R4). Retention gave records of the
/// filter below it up — the prefix rule's cut, or a hold class past its age or bytes, or
/// read — so not all of them are kept, and the fetch is told, never answered with a page
/// that silently starts later. Of a filter whose subjects have different floors, some
/// records below it can still be held: a connection that asked for gap notices
/// ([`Request::GapNotices`]) is read them, the notice ahead of the page, and is refused
/// only when the filter holds none there. Permanent: the floor never falls, so the same
/// fetch is refused again; a fetch from `<off>` reads on.
/// [`BrokerRefusal::retained_from`](crate::client::BrokerRefusal::retained_from) reads
/// it. A head query (`max = 0`) is never refused: its `Mark` says the oldest
/// ([`Response::Mark`]'s `oldest`). A broker that predates it clamped such a fetch to
/// its base.
pub const RETAINED_FROM_PREFIX: &str = "retained-from=";

const TAG_PUBLISH: u8 = 0x01;
const TAG_SUBSCRIBE: u8 = 0x02;
const TAG_FORK_SUBSCRIBE: u8 = 0x03;
const TAG_COMMIT: u8 = 0x04;
const TAG_PROCESS: u8 = 0x05;
const TAG_SUBSCRIBE_GROUP: u8 = 0x06;
const TAG_ATTACH: u8 = 0x07;
const TAG_REPLICATE: u8 = 0x08;
const TAG_LAST: u8 = 0x09;
const TAG_FETCH: u8 = 0x0A;
const TAG_WILL: u8 = 0x0B;
const TAG_HELLO: u8 = 0x0C;
const TAG_KEEPALIVE: u8 = 0x0D;
const TAG_IDLE_MARKS: u8 = 0x0E;
const TAG_BUDGET: u8 = 0x0F;
const TAG_RETIRE: u8 = 0x10;
const TAG_GAP_NOTICES: u8 = 0x11;
const TAG_BROKER_TIMES: u8 = 0x12;
const TAG_STATS: u8 = 0x13;
const TAG_CLEAR_GAP_FENCES: u8 = 0x14;
const TAG_FENCE_GAPS: u8 = 0x15;
const TAG_BURST_MARKS: u8 = 0x16;
const TAG_RELAY: u8 = 0x17;
const TAG_ORIGIN_STAMPS: u8 = 0x18;
const TAG_SETTLE: u8 = 0x19;
const TAG_FRESH_PUBLISH: u8 = 0x1A;
const TAG_ACK: u8 = 0x81;
const TAG_DELIVERY: u8 = 0x82;
const TAG_ERROR: u8 = 0x83;
const TAG_MARK: u8 = 0x84;
const TAG_NONCE: u8 = 0x85;
const TAG_BUDGET_REPLY: u8 = 0x86;
const TAG_GAP: u8 = 0x87;
const TAG_STATS_RESP: u8 = 0x88;

/// Whether a payload names the fresh-publish opcode in this protocol, even when its remaining
/// fields are malformed. Used to order a decoding refusal with this connection's fresh writes.
pub(crate) fn is_fresh_request(payload: &[u8]) -> bool {
    payload.starts_with(&[PROTO_VERSION, TAG_FRESH_PUBLISH])
}

/// Bit 0 of [`NonceExt::requests`]: the broker accepts [`Request::Retire`] (`0x10`).
pub const REQUEST_RETIRE: u64 = 1 << 0;

/// Bit 1 of [`NonceExt::requests`]: the broker accepts [`Request::GapNotices`] (`0x11`)
/// and tells a tail that asked what retention gave up below it ([`Response::Gap`]).
pub const REQUEST_GAP_NOTICES: u64 = 1 << 1;

/// Bit 2 of [`NonceExt::requests`]: TOLD FETCHES. On a connection that asked for gap
/// notices ([`Request::GapNotices`]) the broker reads a `Fetch` below its filter's oldest
/// from its `from` while retention still holds records of the filter there, the notice
/// ahead of the page (`REQUIREMENTS-fabric-operations` R4, addendum A9), so its
/// `retained-from=` there says the filter holds none of them. A broker that announces
/// [`REQUEST_GAP_NOTICES`] without it tells tails only: its `retained-from=` to such a
/// `Fetch` says nothing of what it still holds below the oldest, and a reader that must not
/// skip a held record reads a filter whose subjects share one floor instead (one reader
/// group's mail).
pub const REQUEST_TOLD_FETCH: u64 = 1 << 2;

/// Bit 3 of [`NonceExt::requests`]: the broker accepts [`Request::BrokerTimes`] (`0x12`)
/// and stamps `Delivery` frames on asking connections with `bt=<unix ms>`
/// (`REQUIREMENTS` R3).
pub const REQUEST_BROKER_TIMES: u64 = 1 << 3;

/// Bit 4 of [`NonceExt::requests`]: the broker accepts [`Request::Stats`] (`0x13`)
/// and answers with [`Response::Stats`] (`REQUIREMENTS` R5).
pub const REQUEST_STATS: u64 = 1 << 4;

/// Bit 5 of [`NonceExt::requests`]: the broker GAP-FENCES each producer's writes on a
/// connection THAT ASKS ([`Request::FenceGaps`], `0x15`; the broker was opened with
/// `OpenOptions::sticky_batch_refusal`): once one of a producer's writes sent after the ask is
/// refused, every later one it sends on that connection above the refused sequence is refused
/// `gap-fenced=<seq>` in send order, until a write at or under that sequence commits, the
/// connection closes, or it asks [`Request::ClearGapFences`] (`0x14`), which this bit
/// announces too. A producer that pipelines writes whose order must hold on the log asks
/// before it keeps more than one in flight: unasked, a refused batch is rolled back and the
/// next write lands, ahead of the refused one's retry (`DESIGN-aterm-fabric` §14 Q7). A
/// connection that never asks, one of a client that predates the verb among them, is served
/// unfenced on any broker, so a refusal it does not retry next fences nothing it sends after
/// it. A broker opened without the option leaves the bit clear, refuses the ask, and still
/// answers `ClearGapFences` (it clears nothing).
pub const REQUEST_GAP_FENCES: u64 = 1 << 5;

/// Bit 6 of [`NonceExt::requests`]: the broker accepts [`Request::BurstMarks`] (`0x16`).
pub const REQUEST_BURST_MARKS: u64 = 1 << 6;

/// Bit 7 of [`NonceExt::requests`]: the broker accepts [`Request::Relay`] (`0x17`) and
/// [`Request::OriginStamps`] (`0x18`).
pub const REQUEST_RELAY: u64 = 1 << 7;

/// Bit 8 of [`NonceExt::requests`]: the broker accepts [`Request::Settle`] (`0x19`): a full
/// flush of its log issued after it read the request, never skipped, answered in send order
/// with the durable head after it. Read beside the log's device ([`NonceExt::device`],
/// [`LogDevice`]), it is what settles a writer's own barriered writes on that device.
pub const REQUEST_SETTLE: u64 = 1 << 8;

/// Bit 9 of [`NonceExt::requests`]: [`Request::FreshPublish`] (`0x1A`) is supported. A fresh
/// publish appends only when its producer key is absent. A staging refusal fences later fresh
/// publishes before they stage. A late commit, flush or quorum error fences subsequent staging;
/// requests already staged in that batch follow their own commit outcomes. The fence lasts until
/// reconnect, independently of the optional gap-fence setting. Ordinary `Publish` is unchanged.
pub const REQUEST_FRESH_PUBLISH: u64 = 1 << 9;

const STATS_MAX_ITEMS: usize = 65_536;

/// Commit-tag byte in a [`Request::Replicate`] frame for a marked `/a/retire` record:
/// an older follower only knows `0` (none) and `1` (group commit) and refuses `2` as
/// malformed (`_ => return None`), stalling the replication link rather than diverging.
const REPLICATE_COMMIT_RETIRE: u8 = 2;

/// Internal sentinel group name used in [`Request::Replicate::commit`] to represent
/// [`REPLICATE_COMMIT_RETIRE`] in memory without changing the `Request::Replicate` shape.
pub(crate) const REPLICATE_RETIRE_GROUP: &str = "\0retire";

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "proto_island.rs"]
mod proto_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{
    committed_watermark, compact_floor_monotone, credit_horizon_monotone, epoch_advance_monotone,
    fenced_ack_select, group_commit_monotone, high_water_monotone, replica_ack_monotone,
    window_gate_send,
};
#[cfg(clean_islands)]
pub use proto_island::{
    committed_watermark, compact_floor_monotone, credit_horizon_monotone, epoch_advance_monotone,
    fenced_ack_select, group_commit_monotone, high_water_monotone, replica_ack_monotone,
    window_gate_send,
};

/// 5-parameter epoch-fenced replication watermark kernel:
/// rejects stale-epoch follower acks (`req_epoch < leader_epoch`), otherwise
/// advances `cur_ack` monotonically to `max(cur_ack, cand_ack)` and clamps the
/// committed watermark at `min(primary_head, next_ack)`.
///
/// Composes the 4-parameter Clean-origin [`fenced_ack_select`] with
/// [`committed_watermark`] and [`replica_ack_monotone`]
/// (`TlaEpochWatermarkReplication::fenced_replica_watermark_le_head`).
#[must_use]
pub const fn fenced_replica_watermark(
    leader_epoch: u64,
    req_epoch: u64,
    primary_head: u64,
    cur_ack: u64,
    cand_ack: u64,
) -> u64 {
    committed_watermark(
        primary_head,
        fenced_ack_select(
            req_epoch,
            leader_epoch,
            cur_ack,
            replica_ack_monotone(cur_ack, cand_ack),
        ),
    )
}

/// 4-parameter credit-windowed send advance kernel:
/// verifies well-formedness (`ack_seq <= sent_seq`) and available credit
/// (`sent_seq < credit_horizon`), then advances `sent_seq` toward `cand_seq`
/// clamped by `credit_horizon`.
///
/// Composes the 4-parameter Clean-origin [`window_gate_send`] with
/// [`credit_horizon_monotone`] and [`committed_watermark`]
/// (`TlaCreditFlowWindow::windowed_send_advance_ge_sent`).
#[must_use]
pub const fn windowed_send_advance(
    sent_seq: u64,
    ack_seq: u64,
    credit_horizon: u64,
    cand_seq: u64,
) -> u64 {
    if ack_seq <= sent_seq {
        window_gate_send(
            sent_seq,
            credit_horizon,
            credit_horizon_monotone(sent_seq, committed_watermark(credit_horizon, cand_seq)),
            sent_seq,
        )
    } else {
        sent_seq
    }
}

contract_fn! {
    /// Kernel-certified incarnation fence predicate `will_seq < high_water`, used by
    /// [`crate::store::BrokerLog`] when deciding whether a pending last will is fenced
    /// by a later normal publish from the same producer (`TlaWillFencing`). It fences a
    /// dead incarnation's will only if the producer keeps the obligation
    /// [`crate::will_seq`] states: a later incarnation's sequences sit above the old will.
    #[must_use]
    pub const fn will_is_fenced(high_water: u64, will_seq: u64) -> bool
    clauses [ensures result == (will_seq < high_water)]
    {
        will_seq < high_water
    }
}

contract_fn! {
    /// Kernel-certified replication epoch fence predicate `req_epoch < cur_epoch`,
    /// used by [`crate::store::BrokerLog`] and [`crate::broker`] to reject stale
    /// primary replication frames (`TlaEpochWatermarkReplication`).
    #[must_use]
    pub const fn epoch_is_fenced(cur_epoch: u64, req_epoch: u64) -> bool
    clauses [ensures result == (req_epoch < cur_epoch)]
    {
        req_epoch < cur_epoch
    }
}

contract_fn! {
    /// Kernel-certified committed-offset visibility predicate `offset < committed_upto`,
    /// used by [`crate::store::BrokerLog::is_offset_replicated_committed`] and
    /// [`crate::store::BrokerLog::fetch_replicated_committed`] (`TlaEpochWatermarkReplication`).
    #[must_use]
    pub const fn offset_is_committed(committed_upto: u64, offset: u64) -> bool
    clauses [ensures result == (offset < committed_upto)]
    {
        offset < committed_upto
    }
}

contract_fn! {
    /// Kernel-certified pipelined flow-control window guard `next_seq < horizon`,
    /// used by [`crate::client::CreditWindow`] when pipelining frames over high-RTT links
    /// (`TlaCreditFlowWindow`).
    #[must_use]
    pub const fn can_send_in_window(horizon: u64, next_seq: u64) -> bool
    clauses [ensures result == (next_seq < horizon)]
    {
        next_seq < horizon
    }
}

/// A client → broker request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Request {
    /// Append `body` to `subject`, deduped by `(producer_id, producer_seq)`.
    Publish {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// Append only if the producer key is absent, including from the staged batch and producer
    /// lineage. A held key is [`ERR_FRESH_HELD`] even for an equal subject and body. A staging
    /// refusal fences later fresh publishes on this connection with [`ERR_FRESH_FENCED`] before
    /// they stage. Late commit, flush or quorum errors fence subsequent staging, but requests
    /// already staged in the same batch retain their own outcomes. Reconnect clears the fence.
    /// Success uses the ordinary publish acknowledgement and durability tier. A transport failure
    /// leaves the outcome unknown; it is not success.
    FreshPublish {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// Stream every record matching `filter` from `from_offset`, then tail live.
    Subscribe { from_offset: u64, filter: String },
    /// COUNTERFACTUAL fork-delivery: stream the alternate timeline that results from
    /// forking the log at `fork_at` and swapping that one record for
    /// `(replacement_subject, replacement_body)`, filtered by `filter`. The live log
    /// is untouched (a sandbox view); delivery is the frozen counterfactual snapshot.
    ForkSubscribe {
        fork_at: u64,
        replacement_subject: String,
        replacement_body: Vec<u8>,
        filter: String,
    },
    /// Durably advance consumer `group`'s committed offset to `upto` (a pure commit).
    Commit { group: String, upto: u64 },
    /// The read-process-write TRANSACTION: append `out_body` to `out_subject` AND
    /// commit `group` to `upto` atomically (one durable record), deduped by
    /// `(producer_id, producer_seq)` — exactly-once processing.
    ProcessAndProduce {
        producer_id: u64,
        producer_seq: u64,
        out_subject: String,
        out_body: Vec<u8>,
        group: String,
        upto: u64,
    },
    /// Subscribe as consumer `group`: deliver matching records from the group's
    /// committed offset (broker-enforced resume) — the newest commit not held back for a
    /// full flush, at what the tier promises of it (durable on Strict, and on Ordered and
    /// Relaxed when the escalation table names the group; on the Replicated tier, one a
    /// quorum may not hold yet) — then tail live.
    SubscribeGroup { group: String, filter: String },
    /// Add a capability to this connection's KEYRING. `grant` is the signed grant
    /// string (`[rw|ro][,p=<principal>]:<filter>`, or a bare filter for the
    /// read-write unbound form); `proof` is a PROOF OF POSSESSION —
    /// `HMAC-SHA256(tag, nonce ‖ grant)` over the nonce this connection got from
    /// [`Request::Hello`] — so the capability's tag never crosses the wire and a
    /// captured `Attach` frame cannot be replayed onto another connection.
    ///
    /// It APPENDS (a repeated grant string replaces; the ring is bounded), and it is
    /// ACKNOWLEDGED with a [`Response::Mark`] — a rejected attach is visible at once
    /// rather than only at the next request. An unguarded broker acknowledges it and
    /// enforces nothing.
    Attach { grant: String, proof: Vec<u8> },
    /// REPLICATION (leader → follower): append this record at EXACTLY leader offset
    /// `seq`, with its producer key, subject, body, and any consumer-group commit
    /// annotation — so a follower's log is an identical prefix of the leader's
    /// (commit records and annotations included). Idempotent: a record already held
    /// at `seq` acks `deduped = true`; a gap, or a different record at `seq`, is
    /// refused (never silently overwritten). Acked like a publish.
    Replicate {
        seq: u64,
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
        /// `Some((group, upto))` for a commit-carrying record.
        commit: Option<(String, u64)>,
        /// The LEADER's [`LogIdentity`], which a replica adopts as its own once the
        /// record commits and is the replica's newest — the record's offset is the
        /// leader's, so a client that fails over keeps its offsets. An OPTIONAL TRAILER after `commit`: a leader
        /// that predates log identity sends none (`None`), and a follower that
        /// predates it never reads the bytes (its decoder stops after `commit`).
        leader: Option<LogIdentity>,
    },
    /// LAST-VALUE (retained state): deliver the most recent record of EVERY subject
    /// matching `filter` whose subject sorts strictly after `after` (`""` for the
    /// first page), at most `max` of them, in ascending SUBJECT order — then a
    /// [`Response::Mark`] carrying the head the page was read with. Non-terminal: the
    /// connection stays usable, so `Subscribe { from_offset: mark.next, filter }` on
    /// the same connection tails on gap-free from THAT page's snapshot. Each page of a
    /// PAGED query is read at its own, later head, so a paged reader tails from the
    /// FIRST page's `next` and folds newest-wins across the pages — tailing from the
    /// last page's `next` skips whatever superseded a value an earlier page reported.
    ///
    /// BOTH bounds are the BROKER's, not the client's: `max` is clamped to
    /// `LAST_PAGE_MAX` and the scan of the subject index is cut off after
    /// `LAST_SCAN_MAX` entries VISITED, matched or not. So the page may be shorter
    /// than `max` for a reason that is not "the answer ended", and the closing
    /// `Mark`'s `resume` is the cursor that continues it: page until `resume` is
    /// empty, passing it back as `after`, or the answer is silently truncated.
    Last {
        filter: String,
        after: String,
        max: u32,
    },
    /// BOUNDED, NON-TERMINAL read: deliver at most `max` records matching `filter`
    /// with offset >= `from_offset`, scanning at most `FETCH_SCAN_MAX` records — then
    /// a [`Response::Mark`] whose `next` is the offset after the LAST SCANNED record,
    /// so a sparse filter still advances the cursor instead of re-scanning. `max = 0`
    /// delivers nothing and is the head query. Unlike `Subscribe` it never tails and
    /// never ends the connection.
    Fetch {
        from_offset: u64,
        filter: String,
        max: u32,
    },
    /// REGISTER A LAST WILL: the record the broker appends ON THIS CONNECTION'S
    /// BEHALF when the connection ends, for any reason. Persisted first (a hidden
    /// `/a/will` record) and acknowledged with a [`Response::Mark`]; one per
    /// connection, a second replacing the first — under the SAME producer id, which is
    /// the only shape the durable record can express, so a second `Will` naming a
    /// DIFFERENT producer id is refused rather than silently leaving two wills on the
    /// log for the next broker open to fire.
    ///
    /// It fires as an ORDINARY publish under `(producer_id, producer_seq)`, so it is
    /// deduped like any other — a graceful goodbye that publishes the same key first
    /// makes the will a no-op — and it is FENCED: it appends nothing if a record with
    /// a HIGHER `producer_seq` from the same producer has since landed, which is how
    /// a reconnected producer structurally suppresses its previous incarnation's will.
    ///
    /// THE PRODUCER'S OBLIGATION, which a reconnect needs to fence the old will and the
    /// broker cannot check (a will is a hidden record, and incarnations are the
    /// producer's own count): a new incarnation's sequences sit ABOVE every sequence of
    /// any incarnation the producer ever presented to a broker, and the incarnation is
    /// FLUSHED on the producer's side before its will is registered. A producer that
    /// reuses an incarnation is not fenced. Its two wills share one key, so whichever
    /// connection ends first fires its will and the other dedups away; when that is the
    /// old one, its goodbye lands over the new incarnation's records.
    /// [`crate::will_seq`] has the layout that meets the first half (aterm's,
    /// `(inc << 32) | 0xFFFF_FFFF`, up to [`crate::INC_MAX`]) and the argument. In the
    /// `TlaWillFencing` island, `WillFencingInv` (a fired will was not fenced) holds for
    /// every producer; the obligation is the hypothesis of what it buys
    /// (`newer_incarnation_publish_fences_the_will`, and over the spec
    /// `obliged_spec_fences_the_will_once_landed`): from the newer incarnation's first
    /// publish on, the will is fenced in every later state and cannot fire.
    Will {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// Open the capability handshake: ask for this connection's fresh
    /// [`Response::Nonce`], which an [`Attach`](Request::Attach)'s proof is computed
    /// over. Always allowed (it grants nothing); a guarded broker refuses an `Attach`
    /// with no preceding `Hello`.
    Hello,
    /// KEEP THIS CONNECTION ALIVE: append nothing and answer a [`Response::Mark`]
    /// carrying the head — and, on a TCP connection, hold it from now on to the
    /// broker's keepalive deadline (`KEEPALIVE_DEADLINE`, `Broker::set_keepalive_deadline`):
    /// a connection that then goes that long with nothing read from it is ended
    /// exactly as a closed one is, its will fired and its slot freed. That is how a
    /// request/reply peer that vanished without a FIN is noticed at all; the broker
    /// writes to such a connection only to answer it, so silence is all it ever sees.
    ///
    /// THE FIRST ONE ARMS THE DEADLINE, so a client that never sends one is never
    /// cut. A Unix-socket connection is answered and never held: its peer cannot
    /// vanish without its kernel closing the socket. A broker that predates the verb
    /// answers `Error 5 "malformed request"` and keeps the connection. On a guarded
    /// broker it needs a capability attached (it grants nothing, but the `Mark` names
    /// the log's head). A wire frame, never a log record.
    Keepalive,
    /// Opt in to catch-up and idle [`Response::Mark`] frames on this connection's
    /// next `Subscribe` or `SubscribeGroup`. Answered with a `Mark` before the
    /// stream handoff; append nothing. A broker that predates this verb answers
    /// `Error 5 "malformed request"` and leaves the connection usable, so a client
    /// falls back to that broker's existing tail behavior. No read deadline is
    /// armed here.
    ///
    /// Without this request a tail sends deliveries only: older clients skip marks
    /// inside `recv`, and unsolicited idle marks would keep resetting their socket
    /// timeout forever. On a guarded broker any unexpired capability permits this
    /// request (the acknowledgement names the head), as for `Keepalive`.
    IdleMarks,
    /// READ A PRODUCER'S DISTINCT-SUBJECT BUDGET: answered with a
    /// [`Response::Budget`] — how many subjects of the last-value index are charged to
    /// `producer_id`, how many its registered wills hold in reserve, and the budget
    /// both count against. Appends nothing and changes nothing.
    ///
    /// The count is the one the broker refuses by ([`ERR_SUBJECT_BOUND`]), read from
    /// the durable index after this connection's pending acks: a subject is charged to
    /// the producer whose record first put it in the index, and never to a producer
    /// that only updated it. It is per LOG (one shard of a sharded broker is one log).
    ///
    /// On a guarded broker it is answered only to a connection that could PUBLISH as
    /// `producer_id`: its ring holds a genuine, unexpired read-write grant that is
    /// bound to that producer (`p=<principal>` deriving it) or unbound. A broker that
    /// predates the verb answers `Error 5 "malformed request"` and keeps the
    /// connection. A wire frame, never a log record.
    Budget { producer_id: u64 },
    /// CONDITIONAL SUBJECT RETIREMENT (`DESIGN-aterm-fabric` §5.2): remove `subject` from
    /// the last-value index (`Last`) and credit `producer_id`'s distinct-subject budget
    /// by one if and only if `subject`'s current entry in `Last` is at `offset` on `log`.
    ///
    /// Answered with a [`Response::PublishAck`]:
    /// - When `subject` is in `Last` at `offset` on `log`, charged to `producer_id`, and
    ///   no live or durable will that can still append targets `subject`, the broker
    ///   appends a marked `/a/retire` record and replies `PublishAck { offset: r, deduped: false }`.
    /// - When `subject` is already absent from `Last` (and `offset` is below the log's
    ///   head) or its current entry in `Last` is at a newer offset `o > offset`, the
    ///   retirement is moot: nothing is appended and the broker replies
    ///   `PublishAck { offset: o_or_head, deduped: true }`.
    /// - Refused with [`ERR_RETIRE_REFUSED`] (`"charged: ..."`, `"will: ..."`, or
    ///   `"log: ..."`), [`ERR_RECORD_REFUSED`] (`"cut: ..."` or reserved `/a/...`),
    ///   [`ERR_BAD_SUBJECT`], [`ERR_UNAUTHORIZED`], or [`ERR_REFUSED`] (replica).
    Retire {
        producer_id: u64,
        subject: String,
        offset: u64,
        log: LogIdentity,
    },
    /// Opt in to GAP NOTICES ([`Response::Gap`]) on this connection's next `Subscribe` or
    /// `SubscribeGroup` (`REQUIREMENTS-fabric-operations` R4, addendum A9): before it
    /// delivers any record past ones retention gave up, the tail says so. Answered with a
    /// `Mark` before the stream handoff, as [`IdleMarks`](Request::IdleMarks) is; appends
    /// nothing. A broker that predates the verb answers `Error 5 "malformed request"` and
    /// keeps the connection, and its tail says nothing of what it skipped, as before.
    ///
    /// It holds for this connection's `Fetch`es too: one below its filter's oldest, while
    /// retention still holds records of the filter there, is read from its `from`, the held
    /// records in offset order, with the notice ahead of the page, where a connection that
    /// did not ask is refused `retained-from=` ([`RETAINED_FROM_PREFIX`]). A broker that
    /// predates this answers that `Fetch` with the refusal, as before; Hello's request set
    /// says which a broker does ([`REQUEST_TOLD_FETCH`]).
    ///
    /// Without this request a tail sends no notice: a client that predates them reads its
    /// tail exactly as it did. On a guarded broker any unexpired capability permits it (the
    /// acknowledgement names the head), as for `IdleMarks`. Hello's request set announces
    /// it ([`REQUEST_GAP_NOTICES`]).
    GapNotices,
    /// Opt in to BROKER-STAMPED WALL TIMES (`bt=<unix ms>`, `REQUIREMENTS` R3) on this
    /// connection's `Fetch`, `Last`, `Subscribe`, and `SubscribeGroup` deliveries.
    /// Answered with a `Mark`, like `IdleMarks` and `GapNotices`; appends nothing.
    /// On a guarded broker, any unexpired capability permits it. Announced by
    /// [`REQUEST_BROKER_TIMES`].
    BrokerTimes,
    /// Ask this connection's `Subscribe` and `SubscribeGroup` tails for a `Mark` each time they
    /// catch up after delivering, and once as they first catch up: the boundary of a burst, with
    /// no timer on either side. A reader that batches work per burst (a federation bridge's
    /// commit) waits on it instead of on a clock. Answered with a `Mark`.
    /// [`REQUEST_BURST_MARKS`].
    BurstMarks,
    /// Append a record that ORIGINATED ELSEWHERE, under its origin's `(producer_id, producer_seq)`:
    /// the exactly-once ingest of [`Publish`](Self::Publish), so the key is the same on every
    /// broker it reaches, whichever path it took, and a record relayed around a cycle stops at the
    /// first broker that holds it. Charged to the origin's subject budget. On a guarded broker it
    /// needs a relay grant, and `subject`'s owner must derive `producer_id`
    /// (`astream_cap::grants_relay`). [`REQUEST_RELAY`].
    Relay {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// Stamp this connection's `Delivery` frames with each record's own
    /// `(producer_id, producer_seq)`, which a [`Relay`](Self::Relay) carries on. Answered with a
    /// `Mark`. [`REQUEST_RELAY`].
    OriginStamps,
    /// Attach-gated operator status query (`REQUIREMENTS` R5): broker start time,
    /// listeners, attached producers (principal, transport, attach time, last publish
    /// `bt=`), record and byte counts per face prefix matching `filter`, `oldest`/`head`,
    /// pending wills, dedup-table size, and log segments and bytes on disk. Requires a
    /// fleet-wide read grant (`/f/<F>/>` or `/>`) on a guarded broker; never returns
    /// record bodies. Answered with [`Response::Stats`]. Announced by [`REQUEST_STATS`].
    Stats { filter: String },
    /// LIFT THIS CONNECTION'S GAP FENCES (`OpenOptions::sticky_batch_refusal`,
    /// [`REQUEST_GAP_FENCES`]): answered in the request loop once every write the
    /// connection sent before it is answered, so each of those was judged under the fences
    /// as they stood; then every fence the connection holds is dropped, as a close drops
    /// them, and a write it sends after this one is judged afresh. A producer sends it once
    /// it has READ the answer to every write it sent, so it knows which were refused, which
    /// of them it will send again and in what order. Answered with a `Mark`; appends
    /// nothing; on a guarded broker any unexpired capability permits it (it lifts only the
    /// fences this connection's own writes set). The connection stays fenced: its next
    /// refused write fences again. A connection that never asked [`Request::FenceGaps`],
    /// and a broker opened without the option, hold no fence and are answered the same;
    /// a broker that predates the verb answers `Error 5 "malformed request"` and keeps the
    /// connection.
    ClearGapFences,
    /// GAP-FENCE THIS CONNECTION'S WRITES from now on (`OpenOptions::sticky_batch_refusal`,
    /// [`REQUEST_GAP_FENCES`]): answered in the request loop once every write the connection
    /// sent before it is answered, each of those judged unfenced; then a refused `Publish` or
    /// `ProcessAndProduce` it sends latches a fence on its producer, and every later write of
    /// that producer above the refused sequence is refused `gap-fenced=<seq>` until a write
    /// at or under it commits, [`Request::ClearGapFences`] lifts it, or the connection
    /// closes. The ask holds for the connection's life. A producer asks once, before it keeps
    /// several writes in flight whose order must hold; a connection that never asks is never
    /// fenced, so a client that predates the verb, and does not lift fences, is served as
    /// before. Answered with a `Mark`; appends nothing; on a guarded broker any unexpired
    /// capability permits it (it fences only this connection's own writes). A broker opened
    /// without the option, and one that predates the verb, answer `Error 5` and keep the
    /// connection, which stays unfenced.
    FenceGaps,
    /// SETTLE THE LOG'S DEVICE ([`REQUEST_SETTLE`]): a full flush of the log that the writer
    /// issues AFTER the broker read this request, in the batch the request rides, and issues
    /// even when one already covers the head (where [`Broker::flush_durable`] skips it):
    /// the flush is the point, not what it covers. A writer outside the log that ordered its
    /// own writes on the log's device ahead of this request by a barrier
    /// (`astream_sys::barrier_sync`) knows them on stable media once the answer comes, when
    /// the `Hello` block says the log is on that device and its full flush drains it
    /// ([`LogDevice`]); with no such word, the answer says nothing of any write but the
    /// log's. Pipelined: answered in send order through the ack stream, as a publish is,
    /// with a `PublishAck` whose offset is the log's DURABLE head after the flush and whose
    /// dedup flag is false; a flush that fails is the refusal every write of the batch
    /// gets (the log is then poisoned until it is reopened), and a poisoned log refuses
    /// it in the poison's words. Appends nothing. On a guarded broker it needs a genuine,
    /// unexpired read-write grant of any filter: it spends the device's time, as a write
    /// does. A broker that predates the verb answers `Error 5` and keeps the connection.
    ///
    /// [`Broker::flush_durable`]: crate::Broker::flush_durable
    Settle,
}

/// Per-connection attached producer row in [`WireStats`] (`REQUIREMENTS` R5).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AttachedProducerStats {
    /// Authenticated capability principal (`p=`), or `""` when unattached/unbound.
    pub principal: String,
    /// Listener transport (`"unix"`, `"tcp"`, `"sealed"`, `"handshake"`, `"identity"`).
    pub transport: String,
    /// Derived 64-bit producer identifier (`producer_id_of(&principal)`).
    pub producer_id: u64,
    /// Monotone broker Unix-millisecond timestamp when this connection attached.
    pub attached_at_ms: u64,
    /// Most recent broker-stamped wall time (`bt=`) published by `producer_id`, if any.
    pub last_bt_ms: Option<u64>,
}

/// Record and plaintext-frame byte counts for one face prefix (`/f/<F>/<face>`) in
/// [`WireStats`] (`REQUIREMENTS` R5).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FaceStats {
    /// Face prefix (e.g. `"/f/alpha/pub"`, `"/f/alpha/in"`, `"/f/alpha/fleet"`).
    pub face: String,
    /// Visible non-hidden records matching the query filter under this face.
    pub records: u64,
    /// Plaintext frame bytes (`HEADER_SIZE + RECORD_FIXED_LEN + subject + body + commit`)
    /// across those records.
    pub bytes: u64,
}

/// Attach-gated operator status snapshot returned by [`Response::Stats`]
/// (`REQUIREMENTS` R5). Contains zero record bodies.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WireStats {
    /// Monotone Unix-millisecond timestamp when this `Broker` opened.
    pub started_at_ms: u64,
    /// Oldest offset at and above which the queried filter is complete (`BrokerLog::oldest`).
    pub oldest: u64,
    /// Subscriber-visible head offset at the time of the snapshot.
    pub head: u64,
    /// Count of unfired, unfenced durable wills on the log.
    pub pending_wills: u64,
    /// Count of retained entries in the exactly-once `(producer_id, producer_seq)` dedup table.
    pub dedup_entries: u64,
    /// Count of on-disk log and durable sidecar files (`<log>`, `.id`, `.base`, `.state`, `.hw`, `.held`, `.replica`).
    pub disk_segments: u32,
    /// Total bytes across the on-disk log and its durable sidecar files.
    pub disk_bytes: u64,
    /// Active listener endpoints (`"<scheme>:<addr>"`) currently serving this broker.
    pub listeners: Vec<String>,
    /// Currently attached producer connections on this broker.
    pub producers: Vec<AttachedProducerStats>,
    /// Per-face record and byte counts matching the query filter.
    pub faces: Vec<FaceStats>,
}

/// A GAP NOTICE ([`Response::Gap`]): every record of the tail's filter at an offset in
/// `from..to` that the tail is not delivered was given up by retention. `from` is the
/// tail's cursor and `to` its filter's oldest, the offset at and above which the filter is
/// complete (a `Fetch` that did not ask for notices is refused below it); a record it IS
/// delivered inside the range is one retention still held below the base. `records` is how
/// many records of the filter in the range were given up that no notice on this stream
/// counted before, where the broker's held store knows it; `None` where it cannot (the
/// prefix rule's or a last-value class's records, which a cut drops as a range; give-ups
/// before the broker's last restart), and then the range alone is told, and covers every
/// later give-up inside it.
///
/// Ahead of a `Fetch`'s page ([`Request::GapNotices`]) it is that read's own: `from` is the
/// fetch's `from`, `records` counts the range's give-ups (each fetch is told afresh), and a
/// read paged on from a `next` below `to` is told the rest of the range again while the
/// filter still holds records there; where it holds none there, that continuation is
/// refused `retained-from=<oldest>` ([`RETAINED_FROM_PREFIX`]), however the page before it
/// ended. A reader told the range follows it: what it skips below `to` the notice told it
/// of, and an offset above `to` says the records of `to..offset` were given up since.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Gap {
    /// Where the read that was told starts: the tail's cursor, or the `Fetch`'s `from`.
    pub from: u64,
    /// The filter's oldest when it was told: the offset at and above which the filter is
    /// complete (the greatest floor over what it matches).
    pub to: u64,
    /// How many records of the filter in `from..to` were given up and not counted
    /// before on this stream; `None`: not known.
    pub records: Option<u64>,
}

impl Gap {
    /// What `self` and a LATER notice on the same stream say together: one range from the
    /// lower `from` to the higher `to`, and the counts summed (unknown if either is). Sound
    /// because a stream's notices never count a record twice, and every record between
    /// two ranges that the tail was not delivered lies in one of them.
    #[must_use]
    pub fn and(self, later: Gap) -> Gap {
        Gap {
            from: self.from.min(later.from),
            to: self.to.max(later.to),
            records: match (self.records, later.records) {
                (Some(a), Some(b)) => Some(a.saturating_add(b)),
                _ => None,
            },
        }
    }
}

/// A broker → client response.
#[derive(Debug, Clone, Eq)]
pub enum Response {
    /// A publish landed (or deduped) at `offset`.
    PublishAck { offset: u64, deduped: bool },
    /// One delivered record.
    Delivery {
        offset: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// The request was refused: `code` is its class (the module docs' table of
    /// refusal codes) and `msg` says why in words. Its layout is the one every
    /// protocol version keeps (the module docs).
    Error { code: u8, msg: String },
    /// The end of a bounded, NON-TERMINAL read: `next` is the offset to resume from
    /// (a `Subscribe`/`Fetch` cursor) and `head` is the subscriber-visible head the
    /// answer was read with. Also the acknowledgement of an `Attach`.
    ///
    /// `resume` is the SUBJECT cursor of a [`Request::Last`] page: pass it back as
    /// `after` for the next page, and an EMPTY `resume` means the scan reached the end
    /// of the filter's range — this was the last page. It is empty on every other
    /// verb's `Mark` (`Fetch` pages by offset through `next`; `Attach` and `Will`
    /// carry no cursor at all).
    ///
    /// `resume` is not an optional trailer. A broker that predates the field stamps
    /// payload byte 0 with its own `PROTO_VERSION`, and [`decode_response`] refuses
    /// the frame at that byte, so a `Mark` that ends after `head` is a current peer's
    /// frame cut short: it decodes as malformed like every other short body (read as
    /// `resume = ""` it would report "this was the last page" for a truncated answer).
    ///
    /// `durable` IS an optional trailer, after `resume`: the broker's DURABLE head when
    /// it wrote the `Mark` — every record below it is on stable media by a full flush
    /// (never above `head`). A broker of this build writes it on EVERY `Mark`; an older
    /// client never checked where a `Mark` body ends and ignores it, and an older broker
    /// sends none (`None`): it serves Strict or Relaxed, never Ordered, and a reader
    /// reads which from its `Hello` block where it sends one — on Strict "durable =
    /// visible", on Relaxed nothing acked since its open (see the module docs). A body that ends one to seven bytes after `resume` is a frame
    /// cut short (malformed); bytes after the eight are a later trailer, skipped. On a
    /// broker that serves [`Tier::Ordered`] (or served it at its open, and latched to
    /// Strict since), a subscriber that asked for idle marks also gets a DURABLE mark
    /// when a full flush covers records it was delivered.
    ///
    /// `oldest` is a second optional trailer, after `durable`: on a `Fetch`'s `Mark`, the
    /// OLDEST offset of the fetch's filter, at and above which the filter is complete
    /// (`REQUIREMENTS` R4: the base, or for what a hold rule keeps records of, the greatest
    /// floor over the subjects it matches; records some subject still holds can lie below
    /// it, which a `Fetch` that asked for gap notices reads) — a
    /// head query (`max = 0`) is the `Head`-style query that answers `oldest=`. `None` on
    /// every other verb's `Mark`, and from a broker that predates it. It rides only
    /// behind `durable`: one that has no `durable` to send writes `0` there, which claims
    /// nothing. One to seven bytes after `durable` is a frame cut short (malformed);
    /// bytes after its eight are a later trailer, skipped.
    Mark {
        next: u64,
        head: u64,
        resume: String,
        durable: Option<u64>,
        oldest: Option<u64>,
    },
    /// This connection's fresh nonce (32 bytes), the answer to
    /// [`Request::Hello`]. An `Attach`'s proof is `HMAC-SHA256(tag, nonce ‖ grant)`
    /// over it, which binds the attach to THIS connection.
    ///
    /// `log` is the [`LogIdentity`] of the log the broker serves: a client that kept
    /// offsets from an earlier connection compares it before it uses one. An
    /// OPTIONAL TRAILER after the nonce, so the frame stays readable both ways: a
    /// broker that predates log identity sends none (`None` — nothing known either
    /// way), and a client that predates it never reads the bytes (its decoder stops
    /// after the nonce).
    ///
    /// `ext` is the EXTENSION BLOCK after the identity: what the broker says about the
    /// log beside its name — the tier it serves ([`NonceExt::durability`]), where the
    /// log's generations agree ([`NonceExt::lineage`]) and its health
    /// ([`NonceExt::health`]). Present only when `log` is, and additive both ways: an
    /// older client never reads past the identity, and an older broker sends none (every
    /// field `None`). See [`NonceExt`] for the layout. The WIRE
    /// is additive; the variant is not: code that builds a `Response::Nonce` literal (a
    /// test's stand-in broker) names the field — `ext: NonceExt::default()` says
    /// nothing, as a broker before the block did.
    Nonce {
        nonce: Vec<u8>,
        log: Option<LogIdentity>,
        ext: NonceExt,
    },
    /// The answer to [`Request::Budget`]: `subjects` index entries are charged to the
    /// producer, its registered wills hold `reserved` more, and a publish that would
    /// add a subject past `subjects + reserved == max` is refused
    /// ([`ERR_SUBJECT_BOUND`]).
    Budget {
        subjects: u64,
        reserved: u64,
        max: u64,
    },
    /// A GAP NOTICE on a `Subscribe` or `SubscribeGroup` stream that asked for them
    /// ([`Request::GapNotices`]): written before anything the tail delivers after the
    /// records retention gave up below it (see [`Gap`]), and, on a connection that asked,
    /// ahead of a `Fetch`'s page read from below its filter's oldest. The body is
    /// `from u64, to u64`, a flag byte (`1`: `records` is known) and `records u64` (`0`
    /// when unknown); bytes after it are a later build's, skipped. A wire frame, never a
    /// log record.
    Gap(Gap),
    /// The answer to [`Request::Stats`] (`REQUIREMENTS` R5): operational broker, producer,
    /// face-prefix, and disk telemetry with zero record bodies.
    Stats(WireStats),
}

impl PartialEq for Response {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Response::PublishAck {
                    offset: a_o,
                    deduped: a_d,
                },
                Response::PublishAck {
                    offset: b_o,
                    deduped: b_d,
                },
            ) => *a_o == *b_o && *a_d == *b_d,
            (
                Response::Delivery {
                    offset: a_o,
                    subject: a_s,
                    body: a_b,
                },
                Response::Delivery {
                    offset: b_o,
                    subject: b_s,
                    body: b_b,
                },
            ) => *a_o == *b_o && a_s.as_str() == b_s.as_str() && a_b.as_slice() == b_b.as_slice(),
            (
                Response::Error {
                    code: a_c,
                    msg: a_m,
                },
                Response::Error {
                    code: b_c,
                    msg: b_m,
                },
            ) => *a_c == *b_c && a_m.as_str() == b_m.as_str(),
            (
                Response::Mark {
                    next: a_n,
                    head: a_h,
                    resume: a_r,
                    durable: a_d,
                    oldest: a_o,
                },
                Response::Mark {
                    next: b_n,
                    head: b_h,
                    resume: b_r,
                    durable: b_d,
                    oldest: b_o,
                },
            ) => {
                *a_n == *b_n
                    && *a_h == *b_h
                    && a_r.as_str() == b_r.as_str()
                    && *a_d == *b_d
                    && *a_o == *b_o
            }
            (
                Response::Nonce {
                    nonce: a_n,
                    log: a_l,
                    ext: a_e,
                },
                Response::Nonce {
                    nonce: b_n,
                    log: b_l,
                    ext: b_e,
                },
            ) => a_n.as_slice() == b_n.as_slice() && *a_l == *b_l && *a_e == *b_e,
            (
                Response::Budget {
                    subjects: a_s,
                    reserved: a_r,
                    max: a_m,
                },
                Response::Budget {
                    subjects: b_s,
                    reserved: b_r,
                    max: b_m,
                },
            ) => *a_s == *b_s && *a_r == *b_r && *a_m == *b_m,
            (Response::Gap(a), Response::Gap(b)) => a == b,
            (Response::Stats(a), Response::Stats(b)) => a == b,
            _ => false,
        }
    }
}

/// A durability tier as the `Hello` block (and `<log>.id`) codes it: 0 Strict,
/// 1 Ordered, 2 Relaxed. A code this build does not know is kept as [`Tier::Other`].
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Tier {
    /// An ack is on stable media.
    Strict,
    /// An ack is ordered on the device (a broker that serves it is newer than this
    /// build's tiers; reported as told).
    Ordered,
    /// An ack is in the page cache.
    Relaxed,
    /// A code this build does not know.
    Other(u8),
}

impl Tier {
    pub(crate) const fn code(self) -> u8 {
        match self {
            Tier::Strict => 0,
            Tier::Ordered => 1,
            Tier::Relaxed => 2,
            Tier::Other(c) => c,
        }
    }

    pub(crate) const fn from_code(c: u8) -> Tier {
        match c {
            0 => Tier::Strict,
            1 => Tier::Ordered,
            2 => Tier::Relaxed,
            c => Tier::Other(c),
        }
    }
}

/// Why a broker serves a tier other than the one it was asked for.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ServedReason {
    /// It serves what it was asked for.
    None,
    /// The ordering-only flush exists only on Apple.
    NotApple,
    /// The log is not on the boot volume.
    NotBootVolume,
    /// The device refused the barrier when the log was opened.
    BarrierRefused,
    /// A barrier failed while serving, so the log latched to Strict.
    LatchedAfterBarrierError,
    /// A full flush failed while serving: the log latched to Strict, and refuses every
    /// write until it is reopened (the records that flush was to cover may be lost).
    LatchedAfterFlushFailure,
    /// A code this build does not know.
    Other(u8),
}

impl ServedReason {
    pub(crate) const fn code(self) -> u8 {
        match self {
            ServedReason::None => 0,
            ServedReason::NotApple => 1,
            ServedReason::NotBootVolume => 2,
            ServedReason::BarrierRefused => 3,
            ServedReason::LatchedAfterBarrierError => 4,
            ServedReason::LatchedAfterFlushFailure => 5,
            ServedReason::Other(c) => c,
        }
    }

    pub(crate) const fn from_code(c: u8) -> ServedReason {
        match c {
            0 => ServedReason::None,
            1 => ServedReason::NotApple,
            2 => ServedReason::NotBootVolume,
            3 => ServedReason::BarrierRefused,
            4 => ServedReason::LatchedAfterBarrierError,
            5 => ServedReason::LatchedAfterFlushFailure,
            c => ServedReason::Other(c),
        }
    }
}

/// What a broker says about the durability it serves: the `Hello` block's tag 0x01, so
/// a status line or a doctor on any host reads the tier in force from the broker itself
/// and never infers it from an argv.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ServedInfo {
    /// The tier the broker was opened at.
    pub requested: Tier,
    /// The tier in force.
    pub served: Tier,
    /// Why they differ ([`ServedReason::None`] when they do not).
    pub reason: ServedReason,
    /// The Ordered HORIZON asked for, in milliseconds rounded UP (a sub-millisecond
    /// horizon reads 1, never 0): the writer issues a full flush once this long has passed
    /// since the first ack no full flush covers, after the batch in hand — so the oldest
    /// such ack is at most this plus one batch plus one full flush old. `Some(0)`: a full
    /// flush after every batch. `None` for `Ordered { horizon: None }` — NO bound: only
    /// an escalation, a `flush_durable` and a clean close flush in full, so a power loss
    /// can take every batch since the last of them — and `None` whenever the tier asked
    /// for is not Ordered (Strict flushes every batch; Relaxed keeps no horizon).
    ///
    /// The two Ordered cases that are opposite promises — no bound, and a flush after
    /// every batch — never read alike: the wire carries `u32::MAX` for no horizon and
    /// saturates a real one at `u32::MAX - 1` (49 days).
    pub horizon_ms: Option<u32>,
    /// How many escalation rules the broker holds (records it flushes in full).
    pub rules: u16,
}

/// The wire's `horizon_ms` for "no horizon" ([`ServedInfo::horizon_ms`] `None`).
const HORIZON_NONE: u32 = u32::MAX;

impl ServedInfo {
    /// The horizon `h` as [`horizon_ms`](Self::horizon_ms) reports it: milliseconds
    /// rounded up, saturating below the wire's "none".
    #[must_use]
    pub const fn horizon_ms_of(h: std::time::Duration) -> u32 {
        let ms = h.as_nanos().div_ceil(1_000_000);
        if ms >= (HORIZON_NONE - 1) as u128 {
            HORIZON_NONE - 1
        } else {
            ms as u32
        }
    }
}

const fn encode_u16_le_bytes(v: u16) -> [u8; 2] {
    [v as u8, (v >> 8) as u8]
}

const fn encode_u32_le_bytes(v: u32) -> [u8; 4] {
    [v as u8, (v >> 8) as u8, (v >> 16) as u8, (v >> 24) as u8]
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

const fn encode_served_info_bytes(d: &ServedInfo) -> [u8; 9] {
    let horizon = match d.horizon_ms {
        Some(ms) => ms,
        None => HORIZON_NONE,
    };
    let h = encode_u32_le_bytes(horizon);
    let r = encode_u16_le_bytes(d.rules);
    [
        d.requested.code(),
        d.served.code(),
        d.reason.code(),
        h[0],
        h[1],
        h[2],
        h[3],
        r[0],
        r[1],
    ]
}

const fn decode_u16_le_bytes(b: &[u8; 2]) -> u16 {
    (b[0] as u16) | ((b[1] as u16) << 8)
}

const fn decode_u32_le_bytes(b: &[u8; 4]) -> u32 {
    (b[0] as u32) | ((b[1] as u32) << 8) | ((b[2] as u32) << 16) | ((b[3] as u32) << 24)
}

const fn decode_u64_le_bytes(b: &[u8; 8]) -> u64 {
    (b[0] as u64)
        | ((b[1] as u64) << 8)
        | ((b[2] as u64) << 16)
        | ((b[3] as u64) << 24)
        | ((b[4] as u64) << 32)
        | ((b[5] as u64) << 40)
        | ((b[6] as u64) << 48)
        | ((b[7] as u64) << 56)
}

const fn decode_served_info_bytes(raw: &[u8; 9]) -> ServedInfo {
    let horizon = (raw[3] as u32)
        | ((raw[4] as u32) << 8)
        | ((raw[5] as u32) << 16)
        | ((raw[6] as u32) << 24);
    let rules = (raw[7] as u16) | ((raw[8] as u16) << 8);
    let requested = Tier::from_code(raw[0]);
    let served = Tier::from_code(raw[1]);
    let reason = ServedReason::from_code(raw[2]);
    let horizon_ms = if matches!(requested, Tier::Ordered) && horizon != HORIZON_NONE {
        Some(horizon)
    } else {
        None
    };
    ServedInfo {
        requested,
        served,
        reason,
        // A horizon belongs to Ordered alone; the broker that predates
        // Ordered sent 0 for Strict and Relaxed, which is no horizon.
        horizon_ms,
        rules,
    }
}

const fn decode_served_info(body: &[u8]) -> Option<ServedInfo> {
    let &[req, served, reason, h0, h1, h2, h3, r0, r1] = body else {
        return None;
    };
    Some(decode_served_info_bytes(&[
        req, served, reason, h0, h1, h2, h3, r0, r1,
    ]))
}

const fn take_ext_entry_header(b: &[u8]) -> Option<(u8, usize, &[u8])> {
    let &[tag, l0, l1, ref rest @ ..] = b else {
        return None;
    };
    let len = decode_u16_le_bytes(&[l0, l1]) as usize;
    if rest.len() < len {
        return None;
    }
    Some((tag, len, rest))
}

/// The `Nonce` answer's EXTENSION BLOCK: after the identity trailer, `(tag u8, len u16
/// LE, bytes)*` to the end of the body. A tag a reader does not know is skipped by its
/// length; an entry cut short is a malformed frame. It is sent only with an identity,
/// and, like the identity, before authentication: tiers, generations and offsets are
/// not secrets.
///
/// | tag  | entry      | bytes |
/// |------|------------|-------|
/// | 0x01 | durability | `requested u8, served u8, reason u8, horizon_ms u32 LE, rules u16 LE` ([`ServedInfo`]) |
/// | 0x02 | lineage    | `n u8`, then `n × (generation u64 LE, common u64 LE)` ([`Lineage`]) |
/// | 0x03 | 8 bytes    | the request set a broker announces (`u64` LE bitmask; bit 0 = [`REQUEST_RETIRE`], bit 1 = [`REQUEST_GAP_NOTICES`], bit 2 = [`REQUEST_TOLD_FETCH`], bit 3 = [`REQUEST_BROKER_TIMES`], bit 4 = [`REQUEST_STATS`], bit 5 = [`REQUEST_GAP_FENCES`], bit 6 = [`REQUEST_BURST_MARKS`], bit 7 = [`REQUEST_RELAY`], bit 8 = [`REQUEST_SETTLE`], bit 9 = [`REQUEST_FRESH_PUBLISH`]) |
/// | 0x04 | health     | `flags u8` (bit 0: poisoned), `barrier u64 LE, full u64 LE, skipped u64 LE, failed u64 LE`, `n u16 LE`, `n` bytes of the poison's reason (UTF-8); bytes after it are a later build's, skipped ([`HelloHealth`]) |
/// | 0x05 | retention  | the rules the log is retained by, as `Retention::encode` writes them (the `retention` feature) |
/// | 0x06 | device     | `dev u64 LE` (the log file's `st_dev`), `flags u8` (bit 0: its full flush drains the device); bytes after it are a later build's, skipped ([`LogDevice`]) |
///
/// No request tag, no protocol version and no error code are spent on it: a broker
/// that predates the block sends a frame that ends at the identity, which reads here
/// as every field `None`; one that predates an entry sends a block without it, which
/// reads as that field `None`. A decoder skips every tag it does not know by its
/// length, so a client built before an entry reads a block carrying it exactly as it
/// read the block before (`the_health_entry_is_skipped_by_a_decoder_that_predates_it`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NonceExt {
    /// Tag 0x01: the tier the broker serves.
    pub durability: Option<ServedInfo>,
    /// Tag 0x02: where the log's generations agree.
    pub lineage: Option<Lineage>,
    /// Tag 0x03: the request-set bitmask announced by the broker (bit 0 = [`REQUEST_RETIRE`],
    /// bit 1 = [`REQUEST_GAP_NOTICES`], bit 2 = [`REQUEST_TOLD_FETCH`], bit 3 = [`REQUEST_BROKER_TIMES`],
    /// bit 4 = [`REQUEST_STATS`], bit 5 = [`REQUEST_GAP_FENCES`], bit 6 = [`REQUEST_BURST_MARKS`],
    /// bit 7 = [`REQUEST_RELAY`], bit 8 = [`REQUEST_SETTLE`]).
    pub requests: Option<u64>,
    /// Tag 0x04: whether the log is poisoned, and the flushes it has issued.
    pub health: Option<HelloHealth>,
    /// Tag 0x05: the RETENTION RULES the log is retained by (`REQUIREMENTS` R4), encoded
    /// as `Retention::encode` writes them, so the block reads the same in a build without
    /// the `retention` feature; `NonceExt::retention_rules` (that feature's) reads them. `None`: no rules, or a
    /// broker that predates them.
    pub retention: Option<Vec<u8>>,
    /// Tag 0x06: the device the log is on, and whether its full flush drains it ([`LogDevice`]).
    /// `None`: a broker that predates it, or one that could not read its file's device.
    pub device: Option<LogDevice>,
}

/// What a broker says about its log's health in the answer to every `Hello` — the
/// extension block's tag 0x04: whether the log is POISONED, and why (it then refuses
/// every write until it is reopened — [`Broker::poisoned`](crate::Broker::poisoned)),
/// and the flushes it has issued since it opened
/// ([`Broker::flush_counts`](crate::Broker::flush_counts)).
///
/// PUBLIC FACTS, like the tier served beside them (whose
/// [`ServedReason::LatchedAfterFlushFailure`] already says, before authentication,
/// that a full flush failed): the reason is the one every write the poisoned log
/// refuses carries after [`LOG_POISONED_PREFIX`], to whichever producer sent it. So
/// they ride the answer every client already asks for, and no request tag is spent:
/// a status line on the host reads, from the broker itself, whether the log it is
/// about to call `connected` takes writes. The broker reads both without the log's lock
/// (`LogVitals`), so the answer never waits on the writer — not even on the rollback or
/// identity I/O of the failure it reports.
///
/// The counts are since this OPEN: a reopen (the poison's cure) starts them at zero.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HelloHealth {
    /// `Some(reason)` while the log is poisoned: the broker's own words, cut to
    /// [`HELLO_REASON_MAX`] bytes at a character boundary.
    pub poisoned: Option<String>,
    /// The flushes the log has issued since it opened, by kind.
    pub flushes: crate::store::FlushCounts,
}

/// The most bytes of a poison's reason the `Hello` health entry carries
/// ([`HelloHealth::poisoned`]): astream's reasons run to about 200, and the entry's own
/// length is a `u16`.
pub const HELLO_REASON_MAX: usize = 1024;

/// The fixed part of the health entry: flags, four counts, the reason's length.
const HEALTH_FIXED_LEN: usize = 1 + 4 * 8 + 2;

/// THE LOG'S DEVICE, as a broker says it in the answer to every `Hello` — the extension
/// block's tag 0x06: the device its log file is on (`st_dev`, from `fstat` on the descriptor
/// the log is written through, never its directory's: a link can point the name elsewhere),
/// and whether the log's FULL FLUSH DRAINS THAT DEVICE, every write any process issued to it
/// before the flush reaching stable media by the time it returns.
///
/// On Apple the full flush is `F_FULLFSYNC` (`astream_sys::full_sync_data`), and fcntl(2) says
/// what that settles: it "drains the entire queue of the device and acts as a barrier, data
/// that had been fsync'd on the same device before is guaranteed to be persisted when this
/// call returns"; `F_BARRIERFSYNC` (`astream_sys::barrier_sync`) "does the same thing as
/// fsync(2) then issues a barrier command to the drive". So a write another process made on
/// the same device and ordered by a barrier that returned before the broker READ a
/// [`Request::Settle`] is on stable media once the settle is answered. Elsewhere it is `fdatasync(2)`, which promises the log's own
/// writes only, and the flag is clear. In a test's process tree on Apple a full flush is the
/// plain `fsync(2)` astream_sys substitutes for it (`TEST_PLAIN_FSYNC_ENV`), which no power
/// loss tells apart in a test, so the flag says what the build's flush is, as every full flush
/// there stands for it.
///
/// What it names is the DEVICE NUMBER, not the drive: two APFS volumes of one container
/// have different numbers and one drive. A reader that compares its own file's `st_dev` with
/// it and trusts the drain only on equality is right when they match and pays a flush of its
/// own when they do not, which is the safe direction. A PUBLIC FACT, like the tier served
/// beside it: a device number names no file and no record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LogDevice {
    /// The log file's `st_dev`.
    pub dev: u64,
    /// The log's full flush drains the whole device (`F_FULLFSYNC` on Apple).
    pub flush_drains_device: bool,
}

impl LogDevice {
    /// The entry's body: `dev u64 LE`, then `flags u8` (bit 0: the full flush drains the
    /// device).
    fn put(self, b: &mut Vec<u8>) {
        b.extend_from_slice(&encode_u64_le_bytes(self.dev));
        b.push(u8::from(self.flush_drains_device));
    }

    /// The entry's body; `None` for one cut short. Flag bits other than bit 0, and bytes after
    /// the flags, are a later build's: ignored.
    fn from_wire(body: &[u8]) -> Option<LogDevice> {
        let mut r = Reader { b: body };
        let dev = r.u64()?;
        let flags = r.u8()?;
        Some(LogDevice {
            dev,
            flush_drains_device: flags & 1 == 1,
        })
    }

    /// Whether a writer's barriered writes to a file on device `dev` are on stable media once
    /// a [`Request::Settle`] sent after them is answered: the log is on that device and its
    /// full flush drains it.
    #[must_use]
    pub const fn settles(self, dev: u64) -> bool {
        self.flush_drains_device && self.dev == dev
    }
}

/// The extension-block tags ([`NonceExt`]).
const EXT_DURABILITY: u8 = 0x01;
const EXT_LINEAGE: u8 = 0x02;
const EXT_REQUESTS: u8 = 0x03;
const EXT_HEALTH: u8 = 0x04;
const EXT_RETENTION: u8 = 0x05;
const EXT_DEVICE: u8 = 0x06;

fn put_ext_entry(p: &mut Vec<u8>, tag: u8, body: &[u8]) {
    p.push(tag);
    p.extend_from_slice(&encode_u16_le_bytes(body.len() as u16));
    p.extend_from_slice(body);
}

/// `reason`'s longest prefix of at most `max` bytes that ends on a character boundary.
fn reason_prefix(reason: &str, max: usize) -> &str {
    if reason.len() <= max {
        return reason;
    }
    let mut end = max;
    while end > 0 && !reason.is_char_boundary(end) {
        end -= 1;
    }
    match reason.get(..end) {
        Some(s) => s,
        None => "",
    }
}

impl HelloHealth {
    fn put(&self, b: &mut Vec<u8>) {
        let reason = match &self.poisoned {
            Some(r) => reason_prefix(r, HELLO_REASON_MAX),
            None => "",
        };
        b.push(u8::from(self.poisoned.is_some()));
        b.extend_from_slice(&encode_u64_le_bytes(self.flushes.barrier));
        b.extend_from_slice(&encode_u64_le_bytes(self.flushes.full));
        b.extend_from_slice(&encode_u64_le_bytes(self.flushes.skipped));
        b.extend_from_slice(&encode_u64_le_bytes(self.flushes.failed));
        b.extend_from_slice(&encode_u16_le_bytes(reason.len() as u16));
        b.extend_from_slice(reason.as_bytes());
    }

    /// The entry's body; `None` for one cut short or a reason that is not UTF-8. Flag
    /// bits other than bit 0, and bytes after the reason, are a later build's: ignored.
    fn from_wire(body: &[u8]) -> Option<HelloHealth> {
        let mut r = Reader { b: body };
        let flags = r.u8()?;
        let flushes = crate::store::FlushCounts {
            barrier: r.u64()?,
            full: r.u64()?,
            skipped: r.u64()?,
            failed: r.u64()?,
        };
        let n = {
            let raw = r.take(2)?;
            let &[l0, l1] = raw.as_slice() else {
                return None;
            };
            decode_u16_le_bytes(&[l0, l1]) as usize
        };
        let raw = r.take(n)?;
        let Ok(reason) = String::from_utf8(raw) else {
            return None;
        };
        let poisoned = if flags & 1 == 1 { Some(reason) } else { None };
        Some(HelloHealth { poisoned, flushes })
    }
}

impl NonceExt {
    /// Whether this `Hello` extension block announces [`Request::Retire`] (`0x10`).
    #[must_use]
    pub const fn supports_retire(&self) -> bool {
        match self.requests {
            Some(r) => (r & REQUEST_RETIRE) != 0,
            None => false,
        }
    }

    /// Whether this `Hello` extension block announces [`Request::GapNotices`] (`0x11`).
    #[must_use]
    pub const fn supports_gap_notices(&self) -> bool {
        match self.requests {
            Some(r) => (r & REQUEST_GAP_NOTICES) != 0,
            None => false,
        }
    }

    /// Whether this `Hello` extension block announces told fetches ([`REQUEST_TOLD_FETCH`]):
    /// a `Fetch` on a connection that asked for gap notices reads what retention still
    /// holds below its filter's oldest.
    #[must_use]
    pub const fn supports_told_fetch(&self) -> bool {
        match self.requests {
            Some(r) => (r & REQUEST_TOLD_FETCH) != 0,
            None => false,
        }
    }

    /// Whether this `Hello` extension block announces [`Request::BrokerTimes`] (`0x12`,
    /// `REQUIREMENTS` R3).
    #[must_use]
    pub const fn supports_broker_times(&self) -> bool {
        match self.requests {
            Some(r) => (r & REQUEST_BROKER_TIMES) != 0,
            None => false,
        }
    }

    /// Whether this `Hello` extension block announces [`Request::Stats`] (`0x13`,
    /// `REQUIREMENTS` R5).
    #[must_use]
    pub const fn supports_stats(&self) -> bool {
        match self.requests {
            Some(r) => (r & REQUEST_STATS) != 0,
            None => false,
        }
    }

    /// Whether this `Hello` extension block announces that the broker GAP-FENCES each
    /// producer's writes on a connection that asks ([`Request::FenceGaps`], `0x15`) after a
    /// refused one, and lifts a connection's fences on [`Request::ClearGapFences`] (`0x14`):
    /// [`REQUEST_GAP_FENCES`].
    #[must_use]
    pub const fn supports_gap_fences(&self) -> bool {
        match self.requests {
            Some(r) => (r & REQUEST_GAP_FENCES) != 0,
            None => false,
        }
    }

    /// Whether this `Hello` extension block announces [`Request::Settle`] (`0x19`,
    /// [`REQUEST_SETTLE`]): a full flush issued after the broker read the request, never
    /// skipped, answered with the durable head after it.
    #[must_use]
    pub const fn supports_settle(&self) -> bool {
        match self.requests {
            Some(r) => (r & REQUEST_SETTLE) != 0,
            None => false,
        }
    }

    /// Whether this `Hello` extension announces [`Request::FreshPublish`] and its mandatory
    /// connection fence ([`REQUEST_FRESH_PUBLISH`]).
    #[must_use]
    pub const fn supports_fresh_publish(&self) -> bool {
        match self.requests {
            Some(r) => (r & REQUEST_FRESH_PUBLISH) != 0,
            None => false,
        }
    }

    fn put(&self, p: &mut Vec<u8>) {
        if let Some(d) = &self.durability {
            let b = encode_served_info_bytes(d);
            put_ext_entry(p, EXT_DURABILITY, &b);
        }
        if let Some(l) = &self.lineage {
            let mut b = Vec::new();
            l.put(&mut b);
            put_ext_entry(p, EXT_LINEAGE, &b);
        }
        if let Some(req) = self.requests {
            put_ext_entry(p, EXT_REQUESTS, &encode_u64_le_bytes(req));
        }
        if let Some(h) = &self.health {
            let mut b = Vec::with_capacity(HEALTH_FIXED_LEN);
            h.put(&mut b);
            put_ext_entry(p, EXT_HEALTH, &b);
        }
        if let Some(d) = self.device {
            let mut b = Vec::with_capacity(9);
            d.put(&mut b);
            put_ext_entry(p, EXT_DEVICE, &b);
        }
        // An entry's length is a u16: rules that do not fit are not advertised
        // (`Retention::new` refuses them, so none are).
        if let Some(r) = &self.retention {
            if r.len() <= usize::from(u16::MAX) {
                put_ext_entry(p, EXT_RETENTION, r);
            }
        }
    }

    /// The retention rules this block advertises, decoded (`None`: none advertised, or
    /// bytes that are not rules).
    #[cfg(feature = "retention")]
    #[must_use]
    pub fn retention_rules(&self) -> Option<crate::Retention> {
        match &self.retention {
            Some(b) => crate::Retention::decode(b),
            None => None,
        }
    }

    /// Read the block from `b` (the bytes after the identity) to its end; `None` for an
    /// entry cut short, or a known entry whose bytes are not its layout.
    fn read(mut b: &[u8]) -> Option<NonceExt> {
        let mut ext = NonceExt::default();
        while !b.is_empty() {
            let (tag, len, rest) = take_ext_entry_header(b)?;
            let body = rest.get(..len)?;
            b = rest.get(len..)?;
            match tag {
                EXT_DURABILITY => ext.durability = Some(decode_served_info(body)?),
                EXT_LINEAGE => ext.lineage = Some(Lineage::from_wire(body)?),
                EXT_REQUESTS => {
                    let &[b0, b1, b2, b3, b4, b5, b6, b7] = body else {
                        return None;
                    };
                    ext.requests = Some(decode_u64_le_bytes(&[b0, b1, b2, b3, b4, b5, b6, b7]));
                }
                EXT_HEALTH => ext.health = Some(HelloHealth::from_wire(body)?),
                // Kept as sent, bounded by the entry's u16 length; a build reads it with
                // `retention_rules`.
                EXT_RETENTION => {
                    if body.len() > usize::from(u16::MAX) {
                        return None;
                    }
                    ext.retention = Some(body.to_vec());
                }
                EXT_DEVICE => ext.device = Some(LogDevice::from_wire(body)?),
                // Unknown tags: skipped by their length.
                _ => {}
            }
        }
        Some(ext)
    }
}

fn put_str(p: &mut Vec<u8>, s: &str) {
    p.extend_from_slice(&encode_u32_le_bytes(s.len() as u32));
    p.extend_from_slice(s.as_bytes());
}
fn put_bytes(p: &mut Vec<u8>, b: &[u8]) {
    p.extend_from_slice(&encode_u32_le_bytes(b.len() as u32));
    p.extend_from_slice(b);
}

const fn take_u8(b: &[u8]) -> Option<(u8, &[u8])> {
    let &[v, ref rest @ ..] = b else {
        return None;
    };
    Some((v, rest))
}

const fn take_u32(b: &[u8]) -> Option<(usize, &[u8])> {
    let &[b0, b1, b2, b3, ref rest @ ..] = b else {
        return None;
    };
    Some((decode_u32_le_bytes(&[b0, b1, b2, b3]) as usize, rest))
}

const fn take_u64(b: &[u8]) -> Option<(u64, &[u8])> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, ref rest @ ..] = b else {
        return None;
    };
    Some((decode_u64_le_bytes(&[b0, b1, b2, b3, b4, b5, b6, b7]), rest))
}

const fn take_identity_trailer(b: &[u8]) -> Option<(Option<LogIdentity>, &[u8])> {
    if b.is_empty() {
        return Some((None, b));
    }
    let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, ref rest @ ..] =
        b
    else {
        return None;
    };
    let Some(ident) = LogIdentity::from_wire(&[
        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
        b20, b21, b22, b23,
    ]) else {
        return None;
    };
    Some((Some(ident), rest))
}

/// A `Mark`'s optional trailers after `resume`: `durable`, then `oldest`
/// ([`Response::Mark`]).
const fn decode_mark_trailers(b: &[u8]) -> Option<(Option<u64>, Option<u64>)> {
    match b {
        [] => Some((None, None)),
        &[d0, d1, d2, d3, d4, d5, d6, d7] => Some((
            Some(decode_u64_le_bytes(&[d0, d1, d2, d3, d4, d5, d6, d7])),
            None,
        )),
        &[d0, d1, d2, d3, d4, d5, d6, d7, o0, o1, o2, o3, o4, o5, o6, o7, ref _rest @ ..] => {
            Some((
                Some(decode_u64_le_bytes(&[d0, d1, d2, d3, d4, d5, d6, d7])),
                Some(decode_u64_le_bytes(&[o0, o1, o2, o3, o4, o5, o6, o7])),
            ))
        }
        _ => None,
    }
}

struct Reader<'a> {
    b: &'a [u8],
}
impl<'a> Reader<'a> {
    const fn u8(&mut self) -> Option<u8> {
        let Some((v, rest)) = take_u8(self.b) else {
            return None;
        };
        self.b = rest;
        Some(v)
    }
    const fn u64(&mut self) -> Option<u64> {
        let Some((v, rest)) = take_u64(self.b) else {
            return None;
        };
        self.b = rest;
        Some(v)
    }
    const fn u32(&mut self) -> Option<usize> {
        let Some((v, rest)) = take_u32(self.b) else {
            return None;
        };
        self.b = rest;
        Some(v)
    }
    fn take(&mut self, n: usize) -> Option<Vec<u8>> {
        let v = self.b.get(..n)?.to_vec();
        self.b = self.b.get(n..)?;
        Some(v)
    }
    fn string(&mut self) -> Option<String> {
        let n = self.u32()?;
        let raw = self.b.get(..n)?;
        let rest = self.b.get(n..)?;
        let Ok(s) = core::str::from_utf8(raw) else {
            return None;
        };
        self.b = rest;
        Some(s.to_owned())
    }
    fn bytes(&mut self) -> Option<Vec<u8>> {
        let n = self.u32()?;
        self.take(n)
    }
    /// An OPTIONAL [`LogIdentity`] trailer: `Some(None)` when the body ends here (a
    /// peer that predates it), `Some(Some(_))` when it follows — and `None`
    /// (malformed) for a body that ends INSIDE one, which is a frame cut short, never
    /// "no identity". Bytes after it are left unread, the room the next trailer takes.
    const fn identity_trailer(&mut self) -> Option<Option<LogIdentity>> {
        let Some((ident, rest)) = take_identity_trailer(self.b) else {
            return None;
        };
        self.b = rest;
        Some(ident)
    }
}

/// Append an optional identity trailer: nothing for `None`, so a frame without one is
/// byte-identical to the frame a peer that predates log identity sends.
fn put_identity(p: &mut Vec<u8>, ident: Option<&LogIdentity>) {
    if let Some(ident) = ident {
        ident.put(p);
    }
}

const fn decode_bt_trailer(b: &[u8]) -> Option<Option<u64>> {
    match b {
        [] => Some(None),
        &[crate::brecord::BT_TAG, b0, b1, b2, b3, b4, b5, b6, b7, ref _rest @ ..] => {
            Some(Some(decode_u64_le_bytes(&[b0, b1, b2, b3, b4, b5, b6, b7])))
        }
        &[crate::brecord::BT_TAG, ..] => None,
        _ => Some(None),
    }
}

fn put_wire_stats(p: &mut Vec<u8>, s: &WireStats) {
    p.extend_from_slice(&encode_u64_le_bytes(s.started_at_ms));
    p.extend_from_slice(&encode_u64_le_bytes(s.oldest));
    p.extend_from_slice(&encode_u64_le_bytes(s.head));
    p.extend_from_slice(&encode_u64_le_bytes(s.pending_wills));
    p.extend_from_slice(&encode_u64_le_bytes(s.dedup_entries));
    p.extend_from_slice(&encode_u32_le_bytes(s.disk_segments));
    p.extend_from_slice(&encode_u64_le_bytes(s.disk_bytes));
    let listeners_len = s.listeners.len().min(STATS_MAX_ITEMS);
    p.extend_from_slice(&encode_u32_le_bytes(listeners_len as u32));
    if let Some(slice) = s.listeners.get(..listeners_len) {
        for l in slice {
            put_str(p, l);
        }
    }
    let producers_len = s.producers.len().min(STATS_MAX_ITEMS);
    p.extend_from_slice(&encode_u32_le_bytes(producers_len as u32));
    if let Some(slice) = s.producers.get(..producers_len) {
        for pr in slice {
            put_str(p, &pr.principal);
            put_str(p, &pr.transport);
            p.extend_from_slice(&encode_u64_le_bytes(pr.producer_id));
            p.extend_from_slice(&encode_u64_le_bytes(pr.attached_at_ms));
            match pr.last_bt_ms {
                Some(bt) => {
                    p.push(1);
                    p.extend_from_slice(&encode_u64_le_bytes(bt));
                }
                None => {
                    p.push(0);
                    p.extend_from_slice(&[0u8; 8]);
                }
            }
        }
    }
    let faces_len = s.faces.len().min(STATS_MAX_ITEMS);
    p.extend_from_slice(&encode_u32_le_bytes(faces_len as u32));
    if let Some(slice) = s.faces.get(..faces_len) {
        for f in slice {
            put_str(p, &f.face);
            p.extend_from_slice(&encode_u64_le_bytes(f.records));
            p.extend_from_slice(&encode_u64_le_bytes(f.bytes));
        }
    }
}

fn decode_stats_listeners(r: &mut Reader<'_>) -> Option<Vec<String>> {
    let n = r.u32()?;
    if n > STATS_MAX_ITEMS {
        return None;
    }
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < n {
        out.push(r.string()?);
        i = i.saturating_add(1);
    }
    Some(out)
}

fn decode_stats_producers(r: &mut Reader<'_>) -> Option<Vec<AttachedProducerStats>> {
    let n = r.u32()?;
    if n > STATS_MAX_ITEMS {
        return None;
    }
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < n {
        let principal = r.string()?;
        let transport = r.string()?;
        let producer_id = r.u64()?;
        let attached_at_ms = r.u64()?;
        let has_bt = r.u8()?;
        let bt_raw = r.u64()?;
        let last_bt_ms = match has_bt {
            0 => None,
            1 => Some(bt_raw),
            _ => return None,
        };
        out.push(AttachedProducerStats {
            principal,
            transport,
            producer_id,
            attached_at_ms,
            last_bt_ms,
        });
        i = i.saturating_add(1);
    }
    Some(out)
}

fn decode_stats_faces(r: &mut Reader<'_>) -> Option<Vec<FaceStats>> {
    let n = r.u32()?;
    if n > STATS_MAX_ITEMS {
        return None;
    }
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < n {
        let face = r.string()?;
        let records = r.u64()?;
        let bytes = r.u64()?;
        out.push(FaceStats {
            face,
            records,
            bytes,
        });
        i = i.saturating_add(1);
    }
    Some(out)
}

fn decode_wire_stats(r: &mut Reader<'_>) -> Option<WireStats> {
    let started_at_ms = r.u64()?;
    let oldest = r.u64()?;
    let head = r.u64()?;
    let pending_wills = r.u64()?;
    let dedup_entries = r.u64()?;
    let disk_segments = r.u32()? as u32;
    let disk_bytes = r.u64()?;
    let listeners = decode_stats_listeners(r)?;
    let producers = decode_stats_producers(r)?;
    let faces = decode_stats_faces(r)?;
    Some(WireStats {
        started_at_ms,
        oldest,
        head,
        pending_wills,
        dedup_entries,
        disk_segments,
        disk_bytes,
        listeners,
        producers,
        faces,
    })
}

/// Encode a request to a frame payload.
pub fn encode_request(req: &Request) -> Vec<u8> {
    let mut p = vec![PROTO_VERSION, 0];
    match req {
        Request::Publish {
            producer_id,
            producer_seq,
            subject,
            body,
        } => {
            p[1] = TAG_PUBLISH;
            p.extend_from_slice(&encode_u64_le_bytes(*producer_id));
            p.extend_from_slice(&encode_u64_le_bytes(*producer_seq));
            put_str(&mut p, subject);
            put_bytes(&mut p, body);
        }
        Request::FreshPublish {
            producer_id,
            producer_seq,
            subject,
            body,
        } => {
            p[1] = TAG_FRESH_PUBLISH;
            p.extend_from_slice(&encode_u64_le_bytes(*producer_id));
            p.extend_from_slice(&encode_u64_le_bytes(*producer_seq));
            put_str(&mut p, subject);
            put_bytes(&mut p, body);
        }
        Request::Subscribe {
            from_offset,
            filter,
        } => {
            p[1] = TAG_SUBSCRIBE;
            p.extend_from_slice(&encode_u64_le_bytes(*from_offset));
            put_str(&mut p, filter);
        }
        Request::ForkSubscribe {
            fork_at,
            replacement_subject,
            replacement_body,
            filter,
        } => {
            p[1] = TAG_FORK_SUBSCRIBE;
            p.extend_from_slice(&encode_u64_le_bytes(*fork_at));
            put_str(&mut p, replacement_subject);
            put_bytes(&mut p, replacement_body);
            put_str(&mut p, filter);
        }
        Request::Commit { group, upto } => {
            p[1] = TAG_COMMIT;
            put_str(&mut p, group);
            p.extend_from_slice(&encode_u64_le_bytes(*upto));
        }
        Request::ProcessAndProduce {
            producer_id,
            producer_seq,
            out_subject,
            out_body,
            group,
            upto,
        } => {
            p[1] = TAG_PROCESS;
            p.extend_from_slice(&encode_u64_le_bytes(*producer_id));
            p.extend_from_slice(&encode_u64_le_bytes(*producer_seq));
            put_str(&mut p, out_subject);
            put_bytes(&mut p, out_body);
            put_str(&mut p, group);
            p.extend_from_slice(&encode_u64_le_bytes(*upto));
        }
        Request::SubscribeGroup { group, filter } => {
            p[1] = TAG_SUBSCRIBE_GROUP;
            put_str(&mut p, group);
            put_str(&mut p, filter);
        }
        Request::Attach { grant, proof } => {
            p[1] = TAG_ATTACH;
            put_str(&mut p, grant);
            put_bytes(&mut p, proof);
        }
        Request::Will {
            producer_id,
            producer_seq,
            subject,
            body,
        } => {
            p[1] = TAG_WILL;
            p.extend_from_slice(&encode_u64_le_bytes(*producer_id));
            p.extend_from_slice(&encode_u64_le_bytes(*producer_seq));
            put_str(&mut p, subject);
            put_bytes(&mut p, body);
        }
        Request::Hello => p[1] = TAG_HELLO,
        Request::Keepalive => p[1] = TAG_KEEPALIVE,
        Request::IdleMarks => p[1] = TAG_IDLE_MARKS,
        Request::GapNotices => p[1] = TAG_GAP_NOTICES,
        Request::BrokerTimes => p[1] = TAG_BROKER_TIMES,
        Request::BurstMarks => p[1] = TAG_BURST_MARKS,
        Request::OriginStamps => p[1] = TAG_ORIGIN_STAMPS,
        Request::Relay {
            producer_id,
            producer_seq,
            subject,
            body,
        } => {
            p[1] = TAG_RELAY;
            p.extend_from_slice(&encode_u64_le_bytes(*producer_id));
            p.extend_from_slice(&encode_u64_le_bytes(*producer_seq));
            put_str(&mut p, subject);
            put_bytes(&mut p, body);
        }
        Request::ClearGapFences => p[1] = TAG_CLEAR_GAP_FENCES,
        Request::FenceGaps => p[1] = TAG_FENCE_GAPS,
        Request::Settle => p[1] = TAG_SETTLE,
        Request::Stats { filter } => {
            p[1] = TAG_STATS;
            put_str(&mut p, filter);
        }
        Request::Budget { producer_id } => {
            p[1] = TAG_BUDGET;
            p.extend_from_slice(&encode_u64_le_bytes(*producer_id));
        }
        Request::Replicate {
            seq,
            producer_id,
            producer_seq,
            subject,
            body,
            commit,
            leader,
        } => {
            let commit_ref = match commit {
                Some((g, u)) => Some((g.as_str(), *u)),
                None => None,
            };
            return encode_replicate(
                *seq,
                *producer_id,
                *producer_seq,
                subject,
                body,
                commit_ref,
                leader.as_ref(),
            );
        }
        Request::Last { filter, after, max } => {
            p[1] = TAG_LAST;
            put_str(&mut p, filter);
            put_str(&mut p, after);
            p.extend_from_slice(&encode_u32_le_bytes(*max));
        }
        Request::Fetch {
            from_offset,
            filter,
            max,
        } => {
            p[1] = TAG_FETCH;
            p.extend_from_slice(&encode_u64_le_bytes(*from_offset));
            put_str(&mut p, filter);
            p.extend_from_slice(&encode_u32_le_bytes(*max));
        }
        Request::Retire {
            producer_id,
            subject,
            offset,
            log,
        } => {
            p[1] = TAG_RETIRE;
            p.extend_from_slice(&encode_u64_le_bytes(*producer_id));
            put_str(&mut p, subject);
            p.extend_from_slice(&encode_u64_le_bytes(*offset));
            log.put(&mut p);
        }
    }
    p
}

/// Encode a `Replicate` payload directly from BORROWED fields — the leader's
/// replication path ships shared `Arc`'d log records without cloning subject/body
/// into a `Request` first. Byte-identical to `encode_request(&Request::Replicate {..})`.
/// `leader` is the identity trailer (`None` writes the frame a leader that predates
/// log identity sends).
pub fn encode_replicate(
    seq: u64,
    producer_id: u64,
    producer_seq: u64,
    subject: &str,
    body: &[u8],
    commit: Option<(&str, u64)>,
    leader: Option<&LogIdentity>,
) -> Vec<u8> {
    let mut p = Vec::new();
    p.extend_from_slice(&[PROTO_VERSION, TAG_REPLICATE]);
    p.extend_from_slice(&encode_u64_le_bytes(seq));
    p.extend_from_slice(&encode_u64_le_bytes(producer_id));
    p.extend_from_slice(&encode_u64_le_bytes(producer_seq));
    put_str(&mut p, subject);
    put_bytes(&mut p, body);
    match commit {
        None => p.push(0),
        Some((group, 0))
            if group == REPLICATE_RETIRE_GROUP
                && subject == crate::store::RETIRE_SUBJECT
                && producer_seq == crate::brecord::RETIRE_PRODUCER_SEQ =>
        {
            p.push(REPLICATE_COMMIT_RETIRE);
        }
        Some((group, upto)) => {
            p.push(1);
            put_str(&mut p, group);
            p.extend_from_slice(&encode_u64_le_bytes(upto));
        }
    }
    put_identity(&mut p, leader);
    p
}

/// [`encode_replicate`], appending the leader's optional `bt=<unix ms>` trailer
/// (`[BT_TAG, bt_le_8]`) after the 24-byte `leader` identity trailer when both `leader`
/// and `bt_ms` are `Some` (`REQUIREMENTS` R3).
#[allow(clippy::too_many_arguments)]
pub fn encode_replicate_stamped(
    seq: u64,
    producer_id: u64,
    producer_seq: u64,
    subject: &str,
    body: &[u8],
    commit: Option<(&str, u64)>,
    leader: Option<&LogIdentity>,
    bt_ms: Option<u64>,
) -> Vec<u8> {
    let mut p = encode_replicate(
        seq,
        producer_id,
        producer_seq,
        subject,
        body,
        commit,
        leader,
    );
    if leader.is_some() {
        if let Some(bt) = bt_ms {
            p.push(crate::brecord::BT_TAG);
            p.extend_from_slice(&encode_u64_le_bytes(bt));
        }
    }
    p
}

/// Decode a request from a frame payload (bounds-checked; `None` on malformed).
pub fn decode_request(p: &[u8]) -> Option<Request> {
    decode_request_with_bt(p).map(|(req, _)| req)
}

/// [`decode_request`], also returning any `bt=<unix ms>` trailer carried on a
/// [`Request::Replicate`] frame (`REQUIREMENTS` R3).
pub(crate) fn decode_request_with_bt(p: &[u8]) -> Option<(Request, Option<u64>)> {
    let mut r = Reader { b: p };
    if r.u8()? != PROTO_VERSION {
        return None;
    }
    let req = match r.u8()? {
        TAG_PUBLISH => Request::Publish {
            producer_id: r.u64()?,
            producer_seq: r.u64()?,
            subject: r.string()?,
            body: r.bytes()?,
        },
        TAG_FRESH_PUBLISH => Request::FreshPublish {
            producer_id: r.u64()?,
            producer_seq: r.u64()?,
            subject: r.string()?,
            body: r.bytes()?,
        },
        TAG_SUBSCRIBE => Request::Subscribe {
            from_offset: r.u64()?,
            filter: r.string()?,
        },
        TAG_FORK_SUBSCRIBE => Request::ForkSubscribe {
            fork_at: r.u64()?,
            replacement_subject: r.string()?,
            replacement_body: r.bytes()?,
            filter: r.string()?,
        },
        TAG_COMMIT => Request::Commit {
            group: r.string()?,
            upto: r.u64()?,
        },
        TAG_PROCESS => Request::ProcessAndProduce {
            producer_id: r.u64()?,
            producer_seq: r.u64()?,
            out_subject: r.string()?,
            out_body: r.bytes()?,
            group: r.string()?,
            upto: r.u64()?,
        },
        TAG_SUBSCRIBE_GROUP => Request::SubscribeGroup {
            group: r.string()?,
            filter: r.string()?,
        },
        TAG_ATTACH => Request::Attach {
            grant: r.string()?,
            proof: r.bytes()?,
        },
        TAG_WILL => Request::Will {
            producer_id: r.u64()?,
            producer_seq: r.u64()?,
            subject: r.string()?,
            body: r.bytes()?,
        },
        TAG_HELLO => Request::Hello,
        TAG_KEEPALIVE => Request::Keepalive,
        TAG_IDLE_MARKS => Request::IdleMarks,
        TAG_GAP_NOTICES => Request::GapNotices,
        TAG_BROKER_TIMES => Request::BrokerTimes,
        TAG_BURST_MARKS => Request::BurstMarks,
        TAG_ORIGIN_STAMPS => Request::OriginStamps,
        TAG_RELAY => Request::Relay {
            producer_id: r.u64()?,
            producer_seq: r.u64()?,
            subject: r.string()?,
            body: r.bytes()?,
        },
        TAG_CLEAR_GAP_FENCES => Request::ClearGapFences,
        TAG_FENCE_GAPS => Request::FenceGaps,
        TAG_SETTLE => Request::Settle,
        TAG_STATS => Request::Stats {
            filter: r.string()?,
        },
        TAG_BUDGET => Request::Budget {
            producer_id: r.u64()?,
        },
        TAG_REPLICATE => {
            let seq = r.u64()?;
            let producer_id = r.u64()?;
            let producer_seq = r.u64()?;
            let subject = r.string()?;
            let body = r.bytes()?;
            let commit = match r.u8()? {
                0 => {
                    if subject == crate::store::RETIRE_SUBJECT
                        && producer_seq == crate::brecord::RETIRE_PRODUCER_SEQ
                    {
                        return None;
                    }
                    None
                }
                1 => {
                    let group = r.string()?;
                    let upto = r.u64()?;
                    if group == REPLICATE_RETIRE_GROUP {
                        return None;
                    }
                    Some((group, upto))
                }
                REPLICATE_COMMIT_RETIRE => {
                    if subject != crate::store::RETIRE_SUBJECT
                        || producer_seq != crate::brecord::RETIRE_PRODUCER_SEQ
                    {
                        return None;
                    }
                    Some((REPLICATE_RETIRE_GROUP.to_string(), 0))
                }
                _ => return None,
            };
            let leader = r.identity_trailer()?;
            let bt_ms = if leader.is_some() {
                decode_bt_trailer(r.b)?
            } else {
                None
            };
            return Some((
                Request::Replicate {
                    seq,
                    producer_id,
                    producer_seq,
                    subject,
                    body,
                    commit,
                    leader,
                },
                bt_ms,
            ));
        }
        TAG_LAST => Request::Last {
            filter: r.string()?,
            after: r.string()?,
            max: r.u32()? as u32,
        },
        TAG_FETCH => Request::Fetch {
            from_offset: r.u64()?,
            filter: r.string()?,
            max: r.u32()? as u32,
        },
        TAG_RETIRE => {
            let producer_id = r.u64()?;
            let subject = r.string()?;
            let offset = r.u64()?;
            let raw = r.take(LogIdentity::WIRE_LEN)?;
            let log = LogIdentity::from_wire(&raw)?;
            Request::Retire {
                producer_id,
                subject,
                offset,
                log,
            }
        }
        _ => return None,
    };
    Some((req, None))
}

/// Encode a response to a frame payload.
pub fn encode_response(resp: &Response) -> Vec<u8> {
    let mut p = vec![PROTO_VERSION, 0];
    match resp {
        Response::PublishAck { offset, deduped } => {
            p[1] = TAG_ACK;
            p.extend_from_slice(&encode_u64_le_bytes(*offset));
            p.push(*deduped as u8);
        }
        Response::Delivery {
            offset,
            subject,
            body,
        } => {
            p[1] = TAG_DELIVERY;
            p.extend_from_slice(&encode_u64_le_bytes(*offset));
            put_str(&mut p, subject);
            put_bytes(&mut p, body);
        }
        Response::Error { code, msg } => {
            p[1] = TAG_ERROR;
            p.push(*code);
            put_str(&mut p, msg);
        }
        Response::Mark {
            next,
            head,
            resume,
            durable,
            oldest,
        } => {
            p[1] = TAG_MARK;
            p.extend_from_slice(&encode_u64_le_bytes(*next));
            p.extend_from_slice(&encode_u64_le_bytes(*head));
            put_str(&mut p, resume);
            // `oldest` rides behind `durable`; with none to say, `0` claims nothing.
            if let Some(o) = oldest {
                let d = if let Some(d) = durable { *d } else { 0 };
                p.extend_from_slice(&encode_u64_le_bytes(d));
                p.extend_from_slice(&encode_u64_le_bytes(*o));
            } else if let Some(d) = durable {
                p.extend_from_slice(&encode_u64_le_bytes(*d));
            }
        }
        Response::Nonce { nonce, log, ext } => {
            p[1] = TAG_NONCE;
            put_bytes(&mut p, nonce);
            put_identity(&mut p, log.as_ref());
            // The block rides only behind an identity: a frame without one stays the
            // frame a broker that predates log identity sends.
            if log.is_some() {
                ext.put(&mut p);
            }
        }
        Response::Budget {
            subjects,
            reserved,
            max,
        } => {
            p[1] = TAG_BUDGET_REPLY;
            p.extend_from_slice(&encode_u64_le_bytes(*subjects));
            p.extend_from_slice(&encode_u64_le_bytes(*reserved));
            p.extend_from_slice(&encode_u64_le_bytes(*max));
        }
        Response::Gap(g) => {
            p[1] = TAG_GAP;
            p.extend_from_slice(&encode_u64_le_bytes(g.from));
            p.extend_from_slice(&encode_u64_le_bytes(g.to));
            let (known, n) = match g.records {
                Some(n) => (1u8, n),
                None => (0u8, 0),
            };
            p.push(known);
            p.extend_from_slice(&encode_u64_le_bytes(n));
        }
        Response::Stats(s) => {
            p[1] = TAG_STATS_RESP;
            put_wire_stats(&mut p, s);
        }
    }
    p
}

/// Encode a `Delivery` payload directly from BORROWED fields — the egress hot path.
/// Byte-identical to `encode_response(&Response::Delivery { offset, subject, body })`,
/// but it does not construct/own a `Response`, so a shared `Arc`'d log record's subject
/// and body are read by reference (no deep copy on the read path; the only copy is the
/// one unavoidable assembly into the outgoing frame).
pub fn encode_delivery(offset: u64, subject: &str, body: &[u8]) -> Vec<u8> {
    let mut p = Vec::new();
    put_delivery(&mut p, offset, subject, body);
    p
}

fn put_delivery(p: &mut Vec<u8>, offset: u64, subject: &str, body: &[u8]) {
    p.extend_from_slice(&[PROTO_VERSION, TAG_DELIVERY]);
    p.extend_from_slice(&encode_u64_le_bytes(offset));
    put_str(p, subject);
    put_bytes(p, body);
}

fn put_publish(p: &mut Vec<u8>, producer_id: u64, producer_seq: u64, subject: &str, body: &[u8]) {
    put_keyed(p, TAG_PUBLISH, producer_id, producer_seq, subject, body);
}

fn put_keyed(
    p: &mut Vec<u8>,
    tag: u8,
    producer_id: u64,
    producer_seq: u64,
    subject: &str,
    body: &[u8],
) {
    p.extend_from_slice(&[PROTO_VERSION, tag]);
    p.extend_from_slice(&encode_u64_le_bytes(producer_id));
    p.extend_from_slice(&encode_u64_le_bytes(producer_seq));
    put_str(p, subject);
    put_bytes(p, body);
}

const fn encode_header_bytes(len32: u32, crc: u32) -> [u8; HEADER_SIZE] {
    [
        FRAME_MAGIC[0],
        FRAME_MAGIC[1],
        FRAME_VERSION,
        0,
        len32 as u8,
        (len32 >> 8) as u8,
        (len32 >> 16) as u8,
        (len32 >> 24) as u8,
        crc as u8,
        (crc >> 8) as u8,
        (crc >> 16) as u8,
        (crc >> 24) as u8,
    ]
}

fn finish_framed(
    out: &mut Vec<u8>,
    start: usize,
    payload_start: usize,
    precomputed_crc: Option<u32>,
) -> io::Result<u32> {
    let len = out.len().saturating_sub(payload_start);
    let Ok(len32) = u32::try_from(len) else {
        out.truncate(start);
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "payload exceeds cap",
        ));
    };
    if len > MAX_PAYLOAD_LEN {
        out.truncate(start);
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "payload exceeds cap",
        ));
    }
    let payload_slice = out.get(payload_start..).unwrap_or(&[]);
    let crc = match precomputed_crc {
        Some(c) => c,
        None => crc32_ieee(payload_slice),
    };
    if let Some(tail) = out.get_mut(start..) {
        if let Some((hdr, _)) = tail.split_first_chunk_mut::<HEADER_SIZE>() {
            *hdr = encode_header_bytes(len32, crc);
        }
    }
    Ok(crc)
}

/// Append one framed `Publish` request to `out`, assembled in place: `subject` and
/// `body` are copied once into `out` instead of allocating a `String`, a `Vec<u8>`,
/// a request payload buffer, and a framed buffer.
pub(crate) fn append_publish_frame(
    out: &mut Vec<u8>,
    producer_id: u64,
    producer_seq: u64,
    subject: &str,
    body: &[u8],
) -> io::Result<()> {
    let start = out.len();
    out.extend_from_slice(&[0u8; HEADER_SIZE]);
    let payload_start = out.len();
    put_publish(out, producer_id, producer_seq, subject, body);
    let _ = finish_framed(out, start, payload_start, None)?;
    Ok(())
}

/// The exact framed size of a fresh publish, checked before allocating or copying its fields.
pub(crate) fn fresh_publish_frame_len(subject_len: usize, body_len: usize) -> io::Result<usize> {
    let payload_len = 26usize
        .checked_add(subject_len)
        .and_then(|n| n.checked_add(body_len))
        .filter(|&n| n <= MAX_PAYLOAD_LEN)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "payload exceeds cap"))?;
    payload_len
        .checked_add(HEADER_SIZE)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "framed payload exceeds cap"))
}

/// Append one framed [`Request::FreshPublish`] from borrowed fields.
pub(crate) fn append_fresh_publish_frame(
    out: &mut Vec<u8>,
    producer_id: u64,
    producer_seq: u64,
    subject: &str,
    body: &[u8],
) -> io::Result<()> {
    let _ = fresh_publish_frame_len(subject.len(), body.len())?;
    let start = out.len();
    out.extend_from_slice(&[0u8; HEADER_SIZE]);
    let payload_start = out.len();
    put_keyed(
        out,
        TAG_FRESH_PUBLISH,
        producer_id,
        producer_seq,
        subject,
        body,
    );
    let _ = finish_framed(out, start, payload_start, None)?;
    Ok(())
}

/// Append one framed `Relay` to `out`, assembled in place as [`append_publish_frame`] is.
pub(crate) fn append_relay_frame(
    out: &mut Vec<u8>,
    producer_id: u64,
    producer_seq: u64,
    subject: &str,
    body: &[u8],
) -> io::Result<()> {
    let start = out.len();
    out.extend_from_slice(&[0u8; HEADER_SIZE]);
    let payload_start = out.len();
    put_keyed(out, TAG_RELAY, producer_id, producer_seq, subject, body);
    let _ = finish_framed(out, start, payload_start, None)?;
    Ok(())
}

/// Append one framed `Commit` of consumer `group` to `upto` to `out`.
pub(crate) fn append_commit_frame(out: &mut Vec<u8>, group: &str, upto: u64) -> io::Result<()> {
    append_frame(
        out,
        &encode_request(&Request::Commit {
            group: group.to_string(),
            upto,
        }),
    )
}

/// Append one framed `Retire` request to `out`, assembled in place.
pub(crate) fn append_retire_frame(
    out: &mut Vec<u8>,
    producer_id: u64,
    subject: &str,
    offset: u64,
    log: LogIdentity,
) -> io::Result<()> {
    let start = out.len();
    out.extend_from_slice(&[0u8; HEADER_SIZE]);
    let payload_start = out.len();
    out.extend_from_slice(&[PROTO_VERSION, TAG_RETIRE]);
    out.extend_from_slice(&encode_u64_le_bytes(producer_id));
    put_str(out, subject);
    out.extend_from_slice(&encode_u64_le_bytes(offset));
    log.put(out);
    let _ = finish_framed(out, start, payload_start, None)?;
    Ok(())
}

const fn encode_delivery_crc_header(offset: u64, subject_len: u32) -> [u8; 14] {
    [
        PROTO_VERSION,
        TAG_DELIVERY,
        offset as u8,
        (offset >> 8) as u8,
        (offset >> 16) as u8,
        (offset >> 24) as u8,
        (offset >> 32) as u8,
        (offset >> 40) as u8,
        (offset >> 48) as u8,
        (offset >> 56) as u8,
        subject_len as u8,
        (subject_len >> 8) as u8,
        (subject_len >> 16) as u8,
        (subject_len >> 24) as u8,
    ]
}

/// Compute the exact wire CRC-32/IEEE of a `Response::Delivery { offset, subject, body }`
/// payload without allocating or copying a temporary payload buffer.
#[must_use]
pub fn compute_delivery_crc(offset: u64, subject: &str, body: &[u8]) -> u32 {
    let hdr = encode_delivery_crc_header(offset, subject.len() as u32);
    let crc = astream_wire::crc32_ieee_update(0, &hdr);
    let crc = astream_wire::crc32_ieee_update(crc, subject.as_bytes());
    let crc = astream_wire::crc32_ieee_update(crc, &encode_u32_le_bytes(body.len() as u32));
    astream_wire::crc32_ieee_update(crc, body)
}

/// Append one framed `Delivery` to `out`, assembled in place: the body is copied once,
/// into `out`, instead of into a payload, then a `Frame`, then the encoded frame. A
/// streaming verb gathers several into one buffer and writes them with one call.
pub(crate) fn append_delivery_frame(
    out: &mut Vec<u8>,
    offset: u64,
    subject: &str,
    body: &[u8],
) -> io::Result<()> {
    let _ = append_delivery_frame_with_crc(out, offset, subject, body, None)?;
    Ok(())
}

/// [`append_delivery_frame`], appending the optional `bt=<unix ms>` trailer
/// (`[BT_TAG, bt_le_8]`) when `bt_ms` is `Some` (`REQUIREMENTS` R3).
pub(crate) fn append_delivery_frame_stamped(
    out: &mut Vec<u8>,
    offset: u64,
    subject: &str,
    body: &[u8],
    bt_ms: Option<u64>,
    origin: Option<(u64, u64)>,
) -> io::Result<()> {
    if bt_ms.is_none() && origin.is_none() {
        return append_delivery_frame(out, offset, subject, body);
    }
    let start = out.len();
    out.extend_from_slice(&[0u8; HEADER_SIZE]);
    let payload_start = out.len();
    put_delivery(out, offset, subject, body);
    if let Some(bt) = bt_ms {
        out.push(crate::brecord::BT_TAG);
        out.extend_from_slice(&encode_u64_le_bytes(bt));
    }
    if let Some((producer_id, producer_seq)) = origin {
        out.push(crate::brecord::ORIGIN_TAG);
        out.extend_from_slice(&encode_u64_le_bytes(producer_id));
        out.extend_from_slice(&encode_u64_le_bytes(producer_seq));
    }
    let _ = finish_framed(out, start, payload_start, None)?;
    Ok(())
}

/// The `(producer_id, producer_seq)` a `Delivery` payload's origin trailer carries
/// ([`Request::OriginStamps`]); `None` for any other payload, or a delivery without one.
#[must_use]
pub fn decode_delivery_origin(p: &[u8]) -> Option<(u64, u64)> {
    let mut r = Reader { b: p };
    if r.u8()? != PROTO_VERSION || r.u8()? != TAG_DELIVERY {
        return None;
    }
    r.u64()?;
    let subject = r.u32()?;
    r.b = r.b.get(subject..)?;
    let body = r.u32()?;
    r.b = r.b.get(body..)?;
    if r.b.first() == Some(&crate::brecord::BT_TAG) {
        r.b = r.b.get(9..)?;
    }
    if r.u8()? != crate::brecord::ORIGIN_TAG {
        return None;
    }
    Some((r.u64()?, r.u64()?))
}

/// Append one framed `Delivery` to `out`, reusing `precomputed_crc` when `Some` so a
/// 64-subscriber fan-out computes the frame CRC once per record instead of 64 times.
/// Returns the frame's CRC-32/IEEE so the caller can populate a lock-free cache.
pub(crate) fn append_delivery_frame_with_crc(
    out: &mut Vec<u8>,
    offset: u64,
    subject: &str,
    body: &[u8],
    precomputed_crc: Option<u32>,
) -> io::Result<u32> {
    let start = out.len();
    out.extend_from_slice(&[0u8; HEADER_SIZE]);
    let payload_start = out.len();
    put_delivery(out, offset, subject, body);
    finish_framed(out, start, payload_start, precomputed_crc)
}

/// Append `payload`, framed, to `out` (one copy). See [`append_delivery_frame`].
pub(crate) fn append_frame(out: &mut Vec<u8>, payload: &[u8]) -> io::Result<()> {
    let start = out.len();
    out.extend_from_slice(&[0u8; HEADER_SIZE]);
    let payload_start = out.len();
    out.extend_from_slice(payload);
    let _ = finish_framed(out, start, payload_start, None)?;
    Ok(())
}

/// The broker's answer to a request in ANOTHER protocol, whose version byte was
/// `peer`: an [`ERR_PROTOCOL`] refusal in the layout every version keeps (the module
/// docs), stamped with `peer` so the peer's own decoder reads it, and carrying this
/// broker's [`PROTO_VERSION`] in the one byte after the message, where no decoder
/// looks — the byte [`foreign_protocol`] reads back.
///
/// Written out byte by byte, not through [`encode_response`]: whatever a later version
/// does to its own encoder, this is the frame a peer of every version must still read.
pub fn encode_protocol_refusal(peer: u8) -> Vec<u8> {
    let msg = format!(
        "protocol mismatch: this broker speaks astream protocol {PROTO_VERSION}, the request \
         came in protocol {peer} (run the same astream release on both ends)"
    );
    let mut p = vec![peer, TAG_ERROR, ERR_PROTOCOL];
    put_str(&mut p, &msg);
    p.push(PROTO_VERSION);
    p
}

/// The astream protocol a broker REPLY says its sender speaks, when that is not this
/// build's [`PROTO_VERSION`]: the version byte of a reply stamped with another one (an
/// older or newer broker answering in its own protocol — "malformed request", which is
/// all a broker that predates [`ERR_PROTOCOL`] can say), or the broker's version that
/// an [`encode_protocol_refusal`] refusal stamped with ours carries after its message.
/// `None` for a reply in this protocol, and for an empty one.
pub fn foreign_protocol(reply: &[u8]) -> Option<u8> {
    foreign_protocol_at(PROTO_VERSION, reply)
}

/// [`foreign_protocol`] as a client of protocol `ours` reads it.
fn foreign_protocol_at(ours: u8, reply: &[u8]) -> Option<u8> {
    let &[version, ref rest @ ..] = reply else {
        return None;
    };
    if version != ours {
        return Some(version);
    }
    let &[TAG_ERROR, ERR_PROTOCOL, l0, l1, l2, l3, ref after_len @ ..] = rest else {
        return None;
    };
    let len = decode_u32_le_bytes(&[l0, l1, l2, l3]) as usize;
    let &[b] = after_len.get(len..)? else {
        return None;
    };
    if b != ours {
        Some(b)
    } else {
        None
    }
}

/// Decode a response from a frame payload (bounds-checked; `None` on malformed).
pub fn decode_response(p: &[u8]) -> Option<Response> {
    decode_response_with_bt(p).map(|(resp, _)| resp)
}

/// [`decode_response`], also returning any `bt=<unix ms>` trailer attached to a
/// [`Response::Delivery`] frame (`REQUIREMENTS` R3).
pub fn decode_response_with_bt(p: &[u8]) -> Option<(Response, Option<u64>)> {
    let mut r = Reader { b: p };
    if r.u8()? != PROTO_VERSION {
        return None;
    }
    let resp = match r.u8()? {
        TAG_ACK => Response::PublishAck {
            offset: r.u64()?,
            deduped: r.u8()? != 0,
        },
        TAG_DELIVERY => {
            let offset = r.u64()?;
            let subject = r.string()?;
            let body = r.bytes()?;
            let bt_ms = decode_bt_trailer(r.b)?;
            return Some((
                Response::Delivery {
                    offset,
                    subject,
                    body,
                },
                bt_ms,
            ));
        }
        TAG_ERROR => Response::Error {
            code: r.u8()?,
            msg: r.string()?,
        },
        TAG_MARK => {
            let next = r.u64()?;
            let head = r.u64()?;
            // NOT optional. An older broker is refused at the version byte above, so a
            // Mark that ends after `head` is a current peer's truncated frame, and an
            // empty `resume` means something specific ("the scan reached the end of the
            // filter's range") that a truncation must not be read as.
            let resume = r.string()?;
            // Optional: an older broker ends the body here, or after `durable`. One to
            // seven bytes more than either is a frame cut short; anything past `oldest`'s
            // eight is a later trailer, skipped.
            let (durable, oldest) = decode_mark_trailers(r.b)?;
            Response::Mark {
                next,
                head,
                resume,
                durable,
                oldest,
            }
        }
        TAG_NONCE => {
            let nonce = r.bytes()?;
            let log = r.identity_trailer()?;
            let ext = NonceExt::read(r.b)?;
            Response::Nonce { nonce, log, ext }
        }
        TAG_BUDGET_REPLY => Response::Budget {
            subjects: r.u64()?,
            reserved: r.u64()?,
            max: r.u64()?,
        },
        TAG_GAP => {
            let from = r.u64()?;
            let to = r.u64()?;
            let known = r.u8()?;
            let n = r.u64()?;
            // A range that ends below where it starts, or a flag this build does not
            // know, is no notice: malformed, never read as one that says less.
            if from > to {
                return None;
            }
            let records = match known {
                0 => None,
                1 => Some(n),
                _ => return None,
            };
            Response::Gap(Gap { from, to, records })
        }
        TAG_STATS_RESP => Response::Stats(decode_wire_stats(&mut r)?),
        _ => return None,
    };
    Some((resp, None))
}

/// Bytes of a frame's payload read per `read_exact` call: a frame's buffer GROWS as its
/// bytes arrive rather than being allocated at the declared length up front, so a peer
/// that announces a 16 MiB frame and then stalls pins one chunk (plus what it actually
/// sent) until its read times out — not the whole declared length.
#[cfg(test)]
const READ_CHUNK: usize = 64 * 1024;

/// Read exactly one frame's payload from `r` (blocking). `Ok(None)` on a clean EOF
/// (peer closed at a frame boundary); `Err` on a malformed/oversized frame, or
/// `UnexpectedEof` on a frame cut short — in its header or its payload. `read_exact`
/// handles partial reads (it loops until each chunk arrives).
pub fn read_frame(r: &mut impl Read) -> io::Result<Option<Vec<u8>>> {
    let mut hdr = [0u8; HEADER_SIZE];
    // The first read decides between a clean close (nothing at all) and a frame;
    // once any header byte has arrived, a short header is a truncated frame.
    let first = loop {
        match r.read(&mut hdr) {
            Ok(n) => break n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    };
    if first == 0 {
        return Ok(None);
    }
    let Some(hdr_rem) = hdr.get_mut(first..) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid read length",
        ));
    };
    r.read_exact(hdr_rem)?;
    // The header is judged BEFORE the payload it announces is read: a bad magic,
    // version or flags byte, or a length over the cap, is refused on these 12 bytes.
    // A header on its own decodes as "need more bytes" — or, announcing an empty
    // payload, as the whole frame.
    match Frame::decode(&hdr) {
        Ok(None) => {}
        Ok(Some(d)) => return Ok(Some(d.frame.payload)),
        Err(FrameError::TooLarge) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "frame exceeds cap",
            ))
        }
        Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidData, "corrupt frame")),
    }
    let len = decode_u32_le_bytes(&[hdr[4], hdr[5], hdr[6], hdr[7]]) as usize;
    let crc = decode_u32_le_bytes(&[hdr[8], hdr[9], hdr[10], hdr[11]]);
    // Read straight into the payload buffer (no header copy, no second copy out).
    let mut payload = Vec::new();
    (&mut *r).take(len as u64).read_to_end(&mut payload)?;
    if payload.len() < len {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "truncated frame",
        ));
    }
    if crc32_ieee(&payload) != crc {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "corrupt frame"));
    }
    Ok(Some(payload))
}

/// Frame `payload` and write it to `w` (blocking), in one `write_all`.
pub fn write_frame(w: &mut impl Write, payload: &[u8]) -> io::Result<()> {
    let mut out = Vec::new();
    append_frame(&mut out, payload)?;
    w.write_all(&out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requests_round_trip() {
        let p = Request::Publish {
            producer_id: 9,
            producer_seq: 4,
            subject: "/a/stream/x".into(),
            body: b"hi".to_vec(),
        };
        assert_eq!(decode_request(&encode_request(&p)), Some(p));
        let s = Request::Subscribe {
            from_offset: 7,
            filter: "/a/stream/>".into(),
        };
        assert_eq!(decode_request(&encode_request(&s)), Some(s));
        let b = Request::Budget {
            producer_id: 0x0102_0304_0506_0708,
        };
        assert_eq!(decode_request(&encode_request(&b)), Some(b));
    }

    #[test]
    fn fresh_publish_changes_only_the_request_tag_and_checks_frame_lengths() {
        let plain = Request::Publish {
            producer_id: 0x0102_0304_0506_0708,
            producer_seq: 0x1112_1314_1516_1718,
            subject: "/fresh/β".into(),
            body: vec![0, 1, 127, 255],
        };
        let fresh = Request::FreshPublish {
            producer_id: 0x0102_0304_0506_0708,
            producer_seq: 0x1112_1314_1516_1718,
            subject: "/fresh/β".into(),
            body: vec![0, 1, 127, 255],
        };
        let normal_bytes = encode_request(&plain);
        assert_eq!(
            &normal_bytes[..18],
            &[
                PROTO_VERSION,
                0x01,
                8,
                7,
                6,
                5,
                4,
                3,
                2,
                1,
                24,
                23,
                22,
                21,
                20,
                19,
                18,
                17,
            ]
        );
        let mut expected = normal_bytes.clone();
        expected[1] = 0x1A;
        assert_eq!(encode_request(&fresh), expected);
        assert_eq!(decode_request(&expected), Some(fresh));
        assert!(is_fresh_request(&expected));
        assert!(is_fresh_request(&[PROTO_VERSION, 0x1A]));
        assert!(!is_fresh_request(&[PROTO_VERSION + 1, 0x1A]));
        assert!(!is_fresh_request(&normal_bytes));
        for cut in 0..expected.len() {
            assert!(decode_request(&expected[..cut]).is_none(), "cut={cut}");
        }
        let mut framed = Vec::new();
        append_fresh_publish_frame(
            &mut framed,
            0x0102_0304_0506_0708,
            0x1112_1314_1516_1718,
            "/fresh/β",
            &[0, 1, 127, 255],
        )
        .unwrap();
        assert_eq!(
            framed.len(),
            fresh_publish_frame_len("/fresh/β".len(), 4).unwrap()
        );
        assert_eq!(read_frame(&mut framed.as_slice()).unwrap(), Some(expected));
        assert!(fresh_publish_frame_len(usize::MAX, 0).is_err());
        assert!(fresh_publish_frame_len(0, usize::MAX).is_err());
        assert_eq!(
            fresh_publish_frame_len(0, MAX_PAYLOAD_LEN - 26).unwrap(),
            HEADER_SIZE + MAX_PAYLOAD_LEN
        );
        assert!(fresh_publish_frame_len(0, MAX_PAYLOAD_LEN - 25).is_err());
    }

    #[test]
    fn fresh_publish_offer_uses_only_bit_nine() {
        let offered = NonceExt {
            requests: Some(REQUEST_FRESH_PUBLISH),
            ..NonceExt::default()
        };
        assert_eq!(REQUEST_FRESH_PUBLISH, 1 << 9);
        assert!(offered.supports_fresh_publish());
        assert!(!NonceExt::default().supports_fresh_publish());
        assert!(!NonceExt {
            requests: Some(!REQUEST_FRESH_PUBLISH),
            ..NonceExt::default()
        }
        .supports_fresh_publish());
        let reply = Response::Nonce {
            nonce: vec![0; 32],
            log: Some(LogIdentity {
                id: [7; 16],
                generation: 4,
            }),
            ext: offered,
        };
        assert_eq!(decode_response(&encode_response(&reply)), Some(reply));
    }

    #[test]
    fn replicate_round_trips_with_and_without_a_commit() {
        let plain = Request::Replicate {
            seq: 11,
            producer_id: 3,
            producer_seq: 4,
            subject: "/a/r/x".into(),
            body: b"m".to_vec(),
            commit: None,
            leader: None,
        };
        assert_eq!(decode_request(&encode_request(&plain)), Some(plain.clone()));
        let with_commit = Request::Replicate {
            seq: 11,
            producer_id: 3,
            producer_seq: 4,
            subject: "/a/r/x".into(),
            body: b"m".to_vec(),
            commit: Some(("g1".to_string(), 10)),
            leader: None,
        };
        let bytes = encode_request(&with_commit);
        assert_eq!(decode_request(&bytes), Some(with_commit));
        // The borrowed-field encoder is byte-identical to the Request encoder.
        assert_eq!(
            encode_replicate(11, 3, 4, "/a/r/x", b"m", Some(("g1", 10)), None),
            bytes
        );
        // An unknown commit tag byte is malformed, not misread.
        let mut bad = encode_replicate(1, 1, 1, "/a/x", b"", None, None);
        *bad.last_mut().unwrap() = 2;
        assert_eq!(decode_request(&bad), None);
    }

    /// A reader that hands out at most `step` bytes per call — the shape of a socket
    /// delivering a large frame in pieces.
    struct Trickle<'a> {
        bytes: &'a [u8],
        step: usize,
    }
    impl std::io::Read for Trickle<'_> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let n = self.bytes.len().min(self.step).min(buf.len());
            buf[..n].copy_from_slice(&self.bytes[..n]);
            self.bytes = &self.bytes[n..];
            Ok(n)
        }
    }

    /// A frame larger than one read chunk is assembled chunk by chunk (from a reader
    /// that trickles it) byte-identically, and a frame cut short mid-payload is
    /// `UnexpectedEof`, never a partial payload.
    #[test]
    fn large_frames_are_read_in_chunks_and_a_short_one_is_unexpected_eof() {
        let payload: Vec<u8> = (0..(3 * READ_CHUNK + 17))
            .map(|i| (i % 251) as u8)
            .collect();
        let mut wire = Vec::new();
        write_frame(&mut wire, &payload).unwrap();
        let mut trickle = Trickle {
            bytes: &wire,
            step: 1000,
        };
        assert_eq!(read_frame(&mut trickle).unwrap(), Some(payload));
        assert_eq!(
            read_frame(&mut trickle).unwrap(),
            None,
            "clean EOF after the frame"
        );
        let mut short = Trickle {
            bytes: &wire[..wire.len() - 5],
            step: 4096,
        };
        assert_eq!(
            read_frame(&mut short).unwrap_err().kind(),
            io::ErrorKind::UnexpectedEof
        );
    }

    /// Only a stream that ends exactly at a frame boundary is a clean close. One cut
    /// short INSIDE the 12-byte header is `UnexpectedEof`, like one cut inside its
    /// payload — a subscriber must not read a broker that died mid-header as a
    /// stream that ended.
    #[test]
    fn a_frame_cut_inside_its_header_is_unexpected_eof() {
        let mut wire = Vec::new();
        write_frame(&mut wire, b"payload").unwrap();
        for cut in 1..HEADER_SIZE {
            let mut short = Trickle {
                bytes: &wire[..cut],
                step: 4096,
            };
            assert_eq!(
                read_frame(&mut short).map_err(|e| e.kind()),
                Err(io::ErrorKind::UnexpectedEof),
                "header cut after {cut} bytes"
            );
        }
        let mut empty = Trickle {
            bytes: &[],
            step: 4096,
        };
        assert_eq!(read_frame(&mut empty).unwrap(), None);
    }

    #[test]
    fn bt_trailers_are_additive_and_reject_truncation() {
        let ident = LogIdentity {
            id: [0xAB; 16],
            generation: 7,
        };
        let rep = encode_replicate_stamped(
            42,
            11,
            22,
            "/f/alpha/pub/n1/s1/ev",
            b"body",
            None,
            Some(&ident),
            Some(1_700_000_000_123),
        );
        let (req, bt) = decode_request_with_bt(&rep).unwrap();
        assert_eq!(bt, Some(1_700_000_000_123));
        assert!(matches!(req, Request::Replicate { seq: 42, .. }));
        // Truncated bt trailer (`BT_TAG` + <8 bytes) is rejected:
        assert_eq!(decode_request_with_bt(&rep[..rep.len() - 1]), None);

        let mut framed = Vec::new();
        append_delivery_frame_stamped(
            &mut framed,
            9,
            "/f/alpha/pub/n1/s1/ev",
            b"body",
            Some(1_700_000_000_456),
            None,
        )
        .unwrap();
        let payload = read_frame(&mut &framed[..]).unwrap().unwrap();
        let (resp, rbt) = decode_response_with_bt(&payload).unwrap();
        assert_eq!(rbt, Some(1_700_000_000_456));
        assert!(matches!(resp, Response::Delivery { offset: 9, .. }));
        assert_eq!(
            decode_response_with_bt(&payload[..payload.len() - 1]),
            None,
            "truncated Delivery bt trailer must be rejected"
        );
    }

    /// The in-place framer is byte-identical to the wire crate's `Frame::encode`, a
    /// framed delivery to `encode_delivery` framed, and an over-cap payload is refused
    /// leaving the buffer as it was.
    #[test]
    fn in_place_framing_matches_frame_encode() {
        for payload in [&b""[..], b"x", &[7u8; 70_000]] {
            let mut out = b"prefix".to_vec();
            append_frame(&mut out, payload).unwrap();
            assert_eq!(&out[..6], b"prefix");
            assert_eq!(out[6..], Frame::new(payload.to_vec()).encode().unwrap()[..]);
        }
        let mut out = Vec::new();
        append_delivery_frame(&mut out, 9, "/a/x", b"body").unwrap();
        assert_eq!(
            out,
            Frame::new(encode_delivery(9, "/a/x", b"body"))
                .encode()
                .unwrap()
        );
        let mut out = b"kept".to_vec();
        let big = vec![0u8; MAX_PAYLOAD_LEN + 1];
        assert_eq!(
            append_frame(&mut out, &big).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        assert_eq!(out, b"kept");
    }

    /// A header that announces a frame the reader must refuse is refused on the header
    /// alone: the reader never waits for (or buffers) the payload it announces.
    #[test]
    fn a_bad_header_is_refused_before_its_payload_is_read() {
        let mut wire = Vec::new();
        write_frame(&mut wire, &[1u8; 32]).unwrap();
        // Bad magic, over-cap length: only the 12 header bytes are available.
        let mut bad_magic = wire[..HEADER_SIZE].to_vec();
        bad_magic[0] ^= 0xFF;
        let mut over_cap = wire[..HEADER_SIZE].to_vec();
        over_cap[4..8].copy_from_slice(&(MAX_PAYLOAD_LEN as u32 + 1).to_le_bytes());
        for hdr in [bad_magic, over_cap] {
            let mut r = Trickle {
                bytes: &hdr,
                step: 4096,
            };
            assert_eq!(
                read_frame(&mut r).unwrap_err().kind(),
                io::ErrorKind::InvalidData
            );
        }
        // A flipped payload byte is still caught by the CRC.
        let mut corrupt = wire.clone();
        *corrupt.last_mut().unwrap() ^= 1;
        let mut r = Trickle {
            bytes: &corrupt,
            step: 4096,
        };
        assert_eq!(
            read_frame(&mut r).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
    }

    #[test]
    fn responses_round_trip() {
        let a = Response::PublishAck {
            offset: 3,
            deduped: true,
        };
        assert_eq!(decode_response(&encode_response(&a)), Some(a));
        let d = Response::Delivery {
            offset: 5,
            subject: "/a/stream/x".into(),
            body: b"body".to_vec(),
        };
        assert_eq!(decode_response(&encode_response(&d)), Some(d));
        // Three u64s of one shape: distinct values, so a swapped field cannot pass.
        let b = Response::Budget {
            subjects: 4095,
            reserved: 1,
            max: 4096,
        };
        assert_eq!(decode_response(&encode_response(&b)), Some(b));
    }

    #[test]
    fn frame_round_trip_in_memory_and_clean_eof() {
        let mut buf = Vec::new();
        write_frame(
            &mut buf,
            &encode_request(&Request::Subscribe {
                from_offset: 0,
                filter: "/a/>".into(),
            }),
        )
        .unwrap();
        let mut cur = std::io::Cursor::new(buf);
        let payload = read_frame(&mut cur).unwrap().unwrap();
        assert!(matches!(
            decode_request(&payload),
            Some(Request::Subscribe { .. })
        ));
        // No more bytes => clean EOF.
        assert_eq!(read_frame(&mut cur).unwrap(), None);
    }

    /// PROTOCOL ECONOMY, PINNED. The whole fabric —
    /// retained values, bounded reads, a last will, a proof-of-possession attach, an
    /// exactly-once inbox, request/reply, barriers, presence, negotiated liveness and a
    /// producer's view of its own subject budget, a conditional retire, a tail told what
    /// retention gave up, broker-stamped wall times (`bt=`), read-grant-gated operator
    /// `Stats`, a gap fence a connection asks for and its producer lifts once it read its
    /// answers, burst marks, relayed records and their origin stamps, and a settle of the
    /// log's device and conditional fresh publishes — rides on TWENTY-SIX request tags and EIGHT response tags. This test is
    /// the budget: it enumerates every byte and fails if an undeclared request tag or a
    /// ninth response tag ever decodes, and it pins each tag's NUMBER, so a renumbering that
    /// would silently re-interpret an old client's frames breaks the build instead.
    /// `Keepalive` at 0x0D, `IdleMarks` at 0x0E, `Budget` at 0x0F, `Retire` at 0x10,
    /// `GapNotices` at 0x11, `BrokerTimes` at 0x12, `Stats` at 0x13, `ClearGapFences` at
    /// 0x14, `FenceGaps` at 0x15, `BurstMarks` at 0x16, `Relay` at 0x17, `OriginStamps` at 0x18,
    /// `Settle` at 0x19, `FreshPublish` at 0x1A, `Budget`'s reply at 0x86, `Gap` at 0x87 and `Stats` reply
    /// at 0x88 took numbers no earlier version
    /// decoded: an older broker refuses each request as malformed and keeps the connection,
    /// and never sends the reply. Additions, not reinterpretations; no version change.
    #[test]
    fn a_delivery_carries_its_origin_alongside_or_without_a_broker_time() {
        for bt_ms in [None, Some(1_700_000_000_456)] {
            let mut framed = Vec::new();
            append_delivery_frame_stamped(
                &mut framed,
                9,
                "/m/n-a/x",
                b"body",
                bt_ms,
                Some((u64::MAX, 7)),
            )
            .unwrap();
            let p = &framed[HEADER_SIZE..];
            assert_eq!(decode_delivery_origin(p), Some((u64::MAX, 7)));
            let (resp, bt) = decode_response_with_bt(p).unwrap();
            assert_eq!(bt, bt_ms);
            assert!(matches!(resp, Response::Delivery { offset: 9, .. }));
        }
        let mut framed = Vec::new();
        append_delivery_frame_stamped(&mut framed, 9, "/m/n-a/x", b"body", Some(5), None).unwrap();
        assert_eq!(decode_delivery_origin(&framed[HEADER_SIZE..]), None);
        let mut framed = Vec::new();
        append_delivery_frame(&mut framed, 9, "/m/n-a/x", b"body").unwrap();
        assert_eq!(decode_delivery_origin(&framed[HEADER_SIZE..]), None);
    }

    #[test]
    fn the_tag_budget_is_the_declared_requests_and_eight_responses() {
        // Version 2: `Attach` kept its tag (0x07) and its wire SHAPE (a str then a
        // byte string) while its MEANING changed (`{grant, proof}`, answered with a
        // Mark), so under an unchanged version byte a version-1 Attach would decode
        // CLEANLY into the new variant. The byte is checked on every decode, which
        // turns that silent reinterpretation into a refusal. The stored format is
        // unaffected.
        assert_eq!(
            PROTO_VERSION, 2,
            "PROTO_VERSION moved to 2 with Attach's redefinition"
        );
        assert_eq!(
            crate::brecord::BREC_VERSION,
            2,
            "the stored record format stays 2: nothing here is an on-disk change"
        );

        // Every tag's NUMBER, pinned against the variant that carries it.
        let request_tags: [(u8, Request); 26] = [
            (
                0x01,
                Request::Publish {
                    producer_id: 0,
                    producer_seq: 0,
                    subject: String::new(),
                    body: Vec::new(),
                },
            ),
            (
                0x02,
                Request::Subscribe {
                    from_offset: 0,
                    filter: String::new(),
                },
            ),
            (
                0x03,
                Request::ForkSubscribe {
                    fork_at: 0,
                    replacement_subject: String::new(),
                    replacement_body: Vec::new(),
                    filter: String::new(),
                },
            ),
            (
                0x04,
                Request::Commit {
                    group: String::new(),
                    upto: 0,
                },
            ),
            (
                0x05,
                Request::ProcessAndProduce {
                    producer_id: 0,
                    producer_seq: 0,
                    out_subject: String::new(),
                    out_body: Vec::new(),
                    group: String::new(),
                    upto: 0,
                },
            ),
            (
                0x06,
                Request::SubscribeGroup {
                    group: String::new(),
                    filter: String::new(),
                },
            ),
            (
                0x07,
                Request::Attach {
                    grant: String::new(),
                    proof: Vec::new(),
                },
            ),
            (
                0x08,
                Request::Replicate {
                    seq: 0,
                    producer_id: 0,
                    producer_seq: 0,
                    subject: String::new(),
                    body: Vec::new(),
                    commit: None,
                    leader: None,
                },
            ),
            (
                0x09,
                Request::Last {
                    filter: String::new(),
                    after: String::new(),
                    max: 0,
                },
            ),
            (
                0x0A,
                Request::Fetch {
                    from_offset: 0,
                    filter: String::new(),
                    max: 0,
                },
            ),
            (
                0x0B,
                Request::Will {
                    producer_id: 0,
                    producer_seq: 0,
                    subject: String::new(),
                    body: Vec::new(),
                },
            ),
            (0x0C, Request::Hello),
            (0x0D, Request::Keepalive),
            (0x0E, Request::IdleMarks),
            (0x0F, Request::Budget { producer_id: 0 }),
            (
                0x10,
                Request::Retire {
                    producer_id: 0,
                    subject: String::new(),
                    offset: 0,
                    log: LogIdentity {
                        id: [0; 16],
                        generation: 0,
                    },
                },
            ),
            (0x11, Request::GapNotices),
            (0x12, Request::BrokerTimes),
            (
                0x13,
                Request::Stats {
                    filter: String::new(),
                },
            ),
            (0x14, Request::ClearGapFences),
            (0x15, Request::FenceGaps),
            (0x16, Request::BurstMarks),
            (
                0x17,
                Request::Relay {
                    producer_id: 0,
                    producer_seq: 0,
                    subject: String::new(),
                    body: Vec::new(),
                },
            ),
            (0x18, Request::OriginStamps),
            (0x19, Request::Settle),
            (
                0x1A,
                Request::FreshPublish {
                    producer_id: 0,
                    producer_seq: 0,
                    subject: String::new(),
                    body: Vec::new(),
                },
            ),
        ];
        for (tag, req) in &request_tags {
            let bytes = encode_request(req);
            assert_eq!(bytes[1], *tag, "tag number moved for {req:?}");
            assert_eq!(
                decode_request(&bytes).as_ref(),
                Some(req),
                "round trip for tag {tag:#04x}"
            );
        }

        let response_tags: [(u8, Response); 8] = [
            (
                0x81,
                Response::PublishAck {
                    offset: 0,
                    deduped: false,
                },
            ),
            (
                0x82,
                Response::Delivery {
                    offset: 0,
                    subject: String::new(),
                    body: Vec::new(),
                },
            ),
            (
                0x83,
                Response::Error {
                    code: 0,
                    msg: String::new(),
                },
            ),
            (
                0x84,
                Response::Mark {
                    next: 0,
                    head: 0,
                    resume: String::new(),
                    durable: Some(0),
                    oldest: Some(0),
                },
            ),
            (
                0x85,
                Response::Nonce {
                    nonce: Vec::new(),
                    log: None,
                    ext: NonceExt::default(),
                },
            ),
            (
                0x86,
                Response::Budget {
                    subjects: 0,
                    reserved: 0,
                    max: 0,
                },
            ),
            (
                0x87,
                Response::Gap(Gap {
                    from: 0,
                    to: 0,
                    records: None,
                }),
            ),
            (0x88, Response::Stats(WireStats::default())),
        ];
        for (tag, resp) in &response_tags {
            let bytes = encode_response(resp);
            assert_eq!(bytes[1], *tag, "tag number moved for {resp:?}");
            assert_eq!(
                decode_response(&bytes).as_ref(),
                Some(resp),
                "round trip for tag {tag:#04x}"
            );
        }

        // THE BUDGET: sweep every byte. A zero-filled body satisfies every declared
        // tag's parser (empty strings, empty byte vectors, a `None` commit), so a tag
        // decodes here IF AND ONLY IF it is declared — an undeclared byte is `None`,
        // which is what keeps an old broker's answer to a new client `Error 5,
        // "malformed request"` and nothing else.
        let mut body = vec![PROTO_VERSION, 0];
        body.extend_from_slice(&[0u8; 64]);
        let declared_requests: Vec<u8> = request_tags.iter().map(|(t, _)| *t).collect();
        let declared_responses: Vec<u8> = response_tags.iter().map(|(t, _)| *t).collect();
        let mut decodable_requests = Vec::new();
        let mut decodable_responses = Vec::new();
        for tag in 0u8..=255 {
            body[1] = tag;
            if decode_request(&body).is_some() {
                decodable_requests.push(tag);
            }
            if decode_response(&body).is_some() {
                decodable_responses.push(tag);
            }
        }
        assert_eq!(
            decodable_requests, declared_requests,
            "exactly the declared request tags decode, and no other byte does"
        );
        assert_eq!(
            decodable_responses, declared_responses,
            "exactly eight response tags decode, and no other byte does"
        );

        // And the version byte still gates every tag, response tags included: the
        // right tag under the wrong version decodes to nothing at all. The body is
        // the same zero-filled one the sweep just proved every declared tag's parser
        // accepts, so what refuses these frames is the version byte — not a body that
        // ran out early.
        body[0] = PROTO_VERSION + 1;
        for tag in &declared_requests {
            body[1] = *tag;
            assert_eq!(
                decode_request(&body),
                None,
                "request tag {tag:#04x} decoded under a wrong version byte"
            );
        }
        for tag in &declared_responses {
            body[1] = *tag;
            assert_eq!(
                decode_response(&body),
                None,
                "response tag {tag:#04x} decoded under a wrong version byte"
            );
        }
    }

    /// THE GAP NOTICE ON THE WIRE (R4 addendum A9): a known count and an unknown one each
    /// read back as sent; the body is exactly `from, to, flag, records` (25 bytes after
    /// the tag), every shorter body is malformed, a later build's trailer is skipped, and a
    /// flag this build does not know or a range that ends below its start is no notice at
    /// all. Hello's request set announces the verb by its own bit, which the retire bit
    /// does not set. NC: a decoder that reads a body cut after `to` as one whose count is
    /// unknown (an optional trailer) decodes it.
    #[test]
    fn a_gap_notice_round_trips_and_a_short_one_is_malformed() {
        for records in [Some(3), Some(0), None] {
            let g = Response::Gap(Gap {
                from: 7,
                to: 1_000_000,
                records,
            });
            let bytes = encode_response(&g);
            assert_eq!(bytes.len(), 2 + 8 + 8 + 1 + 8, "{records:?}");
            assert_eq!(decode_response(&bytes), Some(g.clone()), "{records:?}");
            for cut in 2..bytes.len() {
                assert_eq!(
                    decode_response(&bytes[..cut]),
                    None,
                    "a body cut to {cut} bytes decoded"
                );
            }
            let mut later = bytes.clone();
            later.extend_from_slice(&[0xAB; 5]);
            assert_eq!(
                decode_response(&later),
                Some(g),
                "a later trailer is skipped"
            );
        }
        let mut bad_flag = encode_response(&Response::Gap(Gap {
            from: 1,
            to: 2,
            records: Some(1),
        }));
        bad_flag[18] = 2;
        assert_eq!(decode_response(&bad_flag), None, "an unknown flag");
        let backwards = encode_response(&Response::Gap(Gap {
            from: 9,
            to: 2,
            records: None,
        }));
        assert_eq!(
            decode_response(&backwards),
            None,
            "a range that ends below its start"
        );
        let ext = |requests| NonceExt {
            requests,
            ..NonceExt::default()
        };
        assert!(ext(Some(REQUEST_GAP_NOTICES)).supports_gap_notices());
        assert!(!ext(Some(REQUEST_RETIRE)).supports_gap_notices());
        assert!(!ext(Some(REQUEST_GAP_NOTICES)).supports_retire());
        assert!(!ext(None).supports_gap_notices());
        assert!(ext(Some(REQUEST_TOLD_FETCH)).supports_told_fetch());
        assert!(!ext(Some(REQUEST_GAP_NOTICES)).supports_told_fetch());
        assert!(!ext(Some(REQUEST_TOLD_FETCH)).supports_gap_notices());
        assert!(!ext(None).supports_told_fetch());
        assert_eq!(
            Gap {
                from: 4,
                to: 9,
                records: Some(2)
            }
            .and(Gap {
                from: 6,
                to: 12,
                records: Some(1)
            }),
            Gap {
                from: 4,
                to: 12,
                records: Some(3)
            }
        );
        assert_eq!(
            Gap {
                from: 4,
                to: 9,
                records: Some(2)
            }
            .and(Gap {
                from: 6,
                to: 9,
                records: None
            })
            .records,
            None,
            "an unknown count makes the sum unknown"
        );
    }

    #[test]
    fn malformed_payload_decodes_to_none() {
        assert_eq!(decode_request(&[]), None);
        assert_eq!(decode_request(&[PROTO_VERSION, TAG_PUBLISH, 1, 2]), None);
        assert_eq!(decode_request(&[9, TAG_PUBLISH]), None); // bad version
    }

    /// A `Mark` that stops after `head` is MALFORMED, not an older broker's frame: an
    /// older broker is refused at the version byte, so tolerating the short form would
    /// only read a current peer's truncated page as `resume = ""` — "the scan reached
    /// the end of the filter's range".
    #[test]
    fn a_mark_truncated_after_head_is_malformed() {
        let full = encode_response(&Response::Mark {
            next: 4,
            head: 9,
            resume: "/f/x".to_string(),
            durable: None,
            oldest: None,
        });
        assert_eq!(
            decode_response(&full),
            Some(Response::Mark {
                next: 4,
                head: 9,
                resume: "/f/x".to_string(),
                durable: None,
                oldest: None,
            })
        );
        // The 18-byte prefix: version, tag, next, head, and nothing more.
        assert_eq!(
            decode_response(&full[..18]),
            None,
            "a short Mark is malformed"
        );
        // An older broker does not get this far: its version byte is refused.
        let mut older = full.clone();
        older[0] = PROTO_VERSION - 1;
        assert_eq!(decode_response(&older), None);
    }

    /// The `Mark` decoder of the release before `Mark.durable`, frozen here as it stood
    /// (next, head, resume — and no check of where the body ends): what an OLDER client
    /// runs on a `Mark` this build's broker sends.
    fn older_client_mark(p: &[u8]) -> Option<(u64, u64, String)> {
        let mut r = Reader { b: p };
        if r.u8()? != PROTO_VERSION || r.u8()? != TAG_MARK {
            return None;
        }
        Some((r.u64()?, r.u64()?, r.string()?))
    }

    /// `Mark.durable` is an ADDITIVE trailer both ways: an older client reads a `Mark`
    /// carrying it as the same `(next, head, resume)` (it never checked where the body
    /// ends); this build reads an older broker's `Mark`, which ends at `resume`, as
    /// `durable: None`. One to seven bytes after `resume` is a frame cut short (bytes after
    /// the eight are `oldest`'s: `a_marks_oldest_trailer_is_additive_both_ways`).
    #[test]
    fn a_marks_durable_trailer_is_additive_both_ways() {
        let with = Response::Mark {
            next: 4,
            head: 9,
            resume: "/f/x".to_string(),
            durable: Some(7),
            oldest: None,
        };
        let bytes = encode_response(&with);
        assert_eq!(
            older_client_mark(&bytes),
            Some((4, 9, "/f/x".to_string())),
            "an older client reads a new broker's Mark"
        );
        assert_eq!(decode_response(&bytes), Some(with.clone()));
        // An older broker's Mark: the same bytes without the trailer.
        let without = &bytes[..bytes.len() - 8];
        let Some(Response::Mark { durable, .. }) = decode_response(without) else {
            panic!("an older broker's Mark decodes")
        };
        assert_eq!(
            durable, None,
            "an older broker says nothing about durability"
        );
        for cut in 1..8 {
            assert_eq!(
                decode_response(&bytes[..bytes.len() - cut]),
                None,
                "a trailer cut {cut} bytes short is malformed"
            );
        }
    }

    /// `Mark.oldest` is ADDITIVE both ways, as `durable` is: an older client reads a `Mark`
    /// carrying both as the same `(next, head, resume)`, and a client of the release before
    /// `oldest` read only `durable`'s eight bytes; this build reads a `Mark` that ends after
    /// `durable` as `oldest: None`. One to seven bytes after `durable` is a frame cut short;
    /// bytes past `oldest`'s eight are a later trailer, skipped. An `oldest` with no
    /// `durable` to send writes `0` before it, which claims nothing.
    #[test]
    fn a_marks_oldest_trailer_is_additive_both_ways() {
        let with = Response::Mark {
            next: 200,
            head: 251,
            resume: String::new(),
            durable: Some(251),
            oldest: Some(151),
        };
        let bytes = encode_response(&with);
        assert_eq!(
            older_client_mark(&bytes),
            Some((200, 251, String::new())),
            "an older client reads a new broker's Mark"
        );
        assert_eq!(decode_response(&bytes), Some(with.clone()));
        let before = &bytes[..bytes.len() - 8];
        let Some(Response::Mark {
            durable, oldest, ..
        }) = decode_response(before)
        else {
            panic!("a Mark from the release before oldest decodes")
        };
        assert_eq!((durable, oldest), (Some(251), None));
        for cut in 1..8 {
            assert_eq!(
                decode_response(&bytes[..bytes.len() - cut]),
                None,
                "an oldest cut {cut} bytes short is malformed"
            );
        }
        let mut later = bytes.clone();
        later.extend_from_slice(&[0xAB; 5]);
        assert_eq!(
            decode_response(&later),
            Some(with),
            "a later trailer is skipped"
        );
        let alone = Response::Mark {
            next: 1,
            head: 1,
            resume: String::new(),
            durable: None,
            oldest: Some(1),
        };
        let Some(Response::Mark {
            durable, oldest, ..
        }) = decode_response(&encode_response(&alone))
        else {
            panic!("an oldest alone decodes")
        };
        assert_eq!(
            (durable, oldest),
            (Some(0), Some(1)),
            "durable 0 claims nothing"
        );
    }

    /// The log-identity trailers are ADDITIVE, so neither side has to be upgraded
    /// first. A frame without one is byte for byte the frame a peer that predates log
    /// identity sends, and reads as `None`. A frame with one STARTS with exactly those
    /// bytes, which is all such a peer's decoder reads (it never checked where a body
    /// ends). A body that ends INSIDE one is malformed, never "no identity"; bytes past
    /// one are left unread for the next trailer.
    #[test]
    fn identity_trailers_are_additive_in_both_directions() {
        let ident = LogIdentity {
            id: [0xab; 16],
            generation: 7,
        };
        let nonce = |log| Response::Nonce {
            nonce: vec![1; 32],
            log,
            ext: NonceExt::default(),
        };
        let mut older = vec![PROTO_VERSION, TAG_NONCE];
        older.extend_from_slice(&32u32.to_le_bytes());
        older.extend_from_slice(&[1; 32]);
        let bare = encode_response(&nonce(None));
        let with = encode_response(&nonce(Some(ident)));
        assert_eq!(bare, older, "no identity: the older peer's frame exactly");
        assert_eq!(
            with[..older.len()],
            older[..],
            "the older frame is a prefix"
        );
        assert_eq!(with.len(), older.len() + LogIdentity::WIRE_LEN);
        assert_eq!(decode_response(&bare), Some(nonce(None)));
        assert_eq!(decode_response(&with), Some(nonce(Some(ident))));
        for cut in 1..LogIdentity::WIRE_LEN {
            assert_eq!(
                decode_response(&with[..older.len() + cut]),
                None,
                "cut {cut}"
            );
        }
        // Behind the identity comes the extension block: an entry of an unknown tag is
        // skipped by its length, one cut short is a malformed frame.
        let mut longer = with.clone();
        longer.extend_from_slice(&[0x7f, 2, 0, 0xaa, 0xbb]);
        assert_eq!(decode_response(&longer), Some(nonce(Some(ident))));
        longer.push(9);
        assert_eq!(decode_response(&longer), None, "an entry cut short");

        let replicate = |leader| Request::Replicate {
            seq: 3,
            producer_id: 4,
            producer_seq: 5,
            subject: "/a/x".into(),
            body: b"b".to_vec(),
            commit: Some(("g".into(), 2)),
            leader,
        };
        let bare = encode_request(&replicate(None));
        let with = encode_request(&replicate(Some(ident)));
        assert_eq!(
            bare,
            encode_replicate(3, 4, 5, "/a/x", b"b", Some(("g", 2)), None)
        );
        assert_eq!(
            with,
            encode_replicate(3, 4, 5, "/a/x", b"b", Some(("g", 2)), Some(&ident))
        );
        assert_eq!(with[..bare.len()], bare[..], "the older frame is a prefix");
        assert_eq!(decode_request(&bare), Some(replicate(None)));
        assert_eq!(decode_request(&with), Some(replicate(Some(ident))));
        for cut in 1..LogIdentity::WIRE_LEN {
            assert_eq!(decode_request(&with[..bare.len() + cut]), None, "cut {cut}");
        }
    }

    /// The `Nonce` extension block: the served tier (0x01) and the lineage (0x02) round
    /// trip; the frame without them is byte-identical to the identity-only frame, which
    /// is a prefix of the frame with them — exactly what an OLDER client reads, stopping
    /// after the identity; an unknown tag (0x03, reserved for the retire design's
    /// request set) is skipped; a known entry whose bytes are not its layout, or a block
    /// with no identity before it, is malformed or absent.
    #[test]
    fn the_nonce_extension_block_is_additive_and_skips_unknown_tags() {
        let ident = LogIdentity {
            id: [0xcd; 16],
            generation: 3,
        };
        let ext = NonceExt {
            durability: Some(ServedInfo {
                requested: Tier::Relaxed,
                served: Tier::Relaxed,
                reason: ServedReason::None,
                horizon_ms: None,
                rules: 0,
            }),
            lineage: Some(crate::logid::step(&Lineage::default(), 3, 41)),
            retention: None,
            requests: Some(REQUEST_RETIRE),
            health: None,
            device: Some(LogDevice {
                dev: 0x0102_0304_0506_0708,
                flush_drains_device: true,
            }),
        };
        let nonce = |log, ext| Response::Nonce {
            nonce: vec![2; 32],
            log,
            ext,
        };
        let plain = encode_response(&nonce(Some(ident), NonceExt::default()));
        let full = encode_response(&nonce(Some(ident), ext.clone()));
        assert_eq!(
            full[..plain.len()],
            plain[..],
            "an older client's frame is a prefix"
        );
        assert_eq!(
            decode_response(&full),
            Some(nonce(Some(ident), ext.clone()))
        );
        assert!(ext.supports_retire());
        assert!(!NonceExt::default().supports_retire());
        // With no identity no block is sent, whatever the caller passed.
        assert_eq!(
            encode_response(&nonce(None, ext.clone())),
            encode_response(&nonce(None, NonceExt::default()))
        );
        // A future tier and reason are kept as told, not refused.
        let mut future = full.clone();
        let at = plain.len() + 3;
        future[at] = 9;
        future[at + 2] = 77;
        match decode_response(&future) {
            Some(Response::Nonce { ext, .. }) => {
                let d = ext.durability.unwrap();
                assert_eq!(
                    (d.requested, d.reason),
                    (Tier::Other(9), ServedReason::Other(77))
                );
            }
            other => panic!("{other:?}"),
        }
        // An unknown tag (0x7f) is skipped.
        let mut unknown = full.clone();
        unknown.extend_from_slice(&[0x7f, 1, 0, 0xff]);
        assert_eq!(
            decode_response(&unknown),
            Some(nonce(Some(ident), ext.clone()))
        );
        // A durability entry one byte short is malformed.
        let mut short = plain.clone();
        short.extend_from_slice(&[0x01, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(decode_response(&short), None);
        // A requests entry (tag 0x03) that is not 8 bytes is malformed.
        let mut bad_req = plain.clone();
        bad_req.extend_from_slice(&[0x03, 7, 0, 1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(decode_response(&bad_req), None);
        // The retention entry (0x05) is kept as sent, after the others.
        let with_rules = NonceExt {
            retention: Some(vec![9, 8, 7]),
            ..ext.clone()
        };
        let frame = encode_response(&nonce(Some(ident), with_rules.clone()));
        assert_eq!(frame[..full.len()], full[..], "the older block is a prefix");
        assert_eq!(frame[full.len()..], [0x05, 3, 0, 9, 8, 7]);
        assert_eq!(
            decode_response(&frame),
            Some(nonce(Some(ident), with_rules))
        );
    }

    /// The block's reader as it stood in the release before the health entry (0x04),
    /// frozen here: it knows 0x01 and 0x02 and skips every other tag by its length —
    /// what an OLDER client runs on the block this build's broker sends.
    fn older_client_ext(mut b: &[u8]) -> Option<(Option<ServedInfo>, Option<Lineage>)> {
        let (mut durability, mut lineage) = (None, None);
        while !b.is_empty() {
            let (tag, len, rest) = take_ext_entry_header(b)?;
            let body = rest.get(..len)?;
            b = rest.get(len..)?;
            match tag {
                0x01 => durability = Some(decode_served_info(body)?),
                0x02 => lineage = Some(Lineage::from_wire(body)?),
                _ => {}
            }
        }
        Some((durability, lineage))
    }

    /// The `Nonce` answer's bytes after the identity: the extension block.
    fn ext_block(frame: &[u8]) -> &[u8] {
        let mut r = Reader { b: frame };
        assert_eq!((r.u8(), r.u8()), (Some(PROTO_VERSION), Some(TAG_NONCE)));
        r.bytes().expect("the nonce");
        r.identity_trailer().expect("an identity");
        r.b
    }

    /// THE DEVICE ENTRY (0x06) IS ADDITIVE AND EXACT: it round-trips with its flag set and
    /// clear and at the extremes of `st_dev`; flag bits past bit 0 and bytes after the flags
    /// are a later build's, read as this build's entry; one cut inside its eight-byte device
    /// or before its flags is malformed. A client that predates it (the frozen reader of the
    /// release before the health entry) reads the block carrying it as the same tier and
    /// lineage, the entry skipped by its length, and refuses one whose length runs past the
    /// frame (the negative control: it walks the header). `LogDevice::settles` trusts the drain
    /// only for the log's own device, and only where the flush drains it; `supports_settle`
    /// reads bit 8 of the request set alone.
    #[test]
    fn the_device_entry_round_trips_and_is_skipped_by_a_decoder_that_predates_it() {
        let ident = LogIdentity {
            id: [0xab; 16],
            generation: 4,
        };
        let served = ServedInfo {
            requested: Tier::Ordered,
            served: Tier::Ordered,
            reason: ServedReason::None,
            horizon_ms: Some(100),
            rules: 4,
        };
        let lineage = crate::logid::step(&Lineage::default(), 4, 17);
        let frame_of = |ext: NonceExt| {
            encode_response(&Response::Nonce {
                nonce: vec![7; 32],
                log: Some(ident),
                ext,
            })
        };
        for (dev, drains) in [(0, false), (1 << 24 | 3, true), (u64::MAX, true)] {
            let device = LogDevice {
                dev,
                flush_drains_device: drains,
            };
            let ext = NonceExt {
                durability: Some(served),
                lineage: Some(lineage.clone()),
                requests: Some(REQUEST_SETTLE),
                device: Some(device),
                ..NonceExt::default()
            };
            let frame = frame_of(ext.clone());
            match decode_response(&frame) {
                Some(Response::Nonce { ext: read, .. }) => assert_eq!(read, ext),
                other => panic!("{other:?}"),
            }
            assert_eq!(
                older_client_ext(ext_block(&frame)),
                Some((Some(served), Some(lineage.clone()))),
                "an older client reads the tier and the lineage past the device"
            );
            assert_eq!(device.settles(dev), drains);
            assert!(!device.settles(dev ^ 1), "another device is never settled");
        }
        // A later build's flag bits and trailing bytes: read as this entry.
        let plain = frame_of(NonceExt::default());
        let mut later = plain.clone();
        later.extend_from_slice(&[0x06, 10, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0b1111_0001, 0xee]);
        match decode_response(&later) {
            Some(Response::Nonce { ext, .. }) => assert_eq!(
                ext.device,
                Some(LogDevice {
                    dev: 9,
                    flush_drains_device: true,
                })
            ),
            other => panic!("{other:?}"),
        }
        // Cut inside the device, or before the flags: malformed.
        for cut in [0usize, 4, 8] {
            let mut short = plain.clone();
            short.extend_from_slice(&[0x06, u8::try_from(cut).unwrap(), 0]);
            short.extend_from_slice(&[0u8; 8][..cut]);
            assert_eq!(
                decode_response(&short),
                None,
                "a device entry of {cut} bytes"
            );
        }
        // The negative control: an entry whose length runs past the frame is refused by the
        // older reader too.
        let mut past = plain.clone();
        past.extend_from_slice(&[0x06, 9, 0, 1, 2, 3]);
        assert_eq!(older_client_ext(ext_block(&past)), None);
        // The settle bit is bit 8 alone.
        let settle = NonceExt {
            requests: Some(REQUEST_SETTLE),
            ..NonceExt::default()
        };
        assert!(settle.supports_settle());
        let others = NonceExt {
            requests: Some(!REQUEST_SETTLE),
            ..NonceExt::default()
        };
        assert!(!others.supports_settle());
        assert!(!NonceExt::default().supports_settle());
    }

    /// THE HEALTH ENTRY (0x04) IS ADDITIVE: a client that predates it reads a block
    /// carrying it exactly as it read the block before — the tier and the lineage, the
    /// entry skipped by its length — whether the log is healthy or poisoned; this build
    /// reads all three. NEGATIVE CONTROL: the same older reader REFUSES a health entry
    /// cut short (its length runs past the frame), so it really walks the entry's header
    /// rather than stopping before it.
    #[test]
    fn the_health_entry_is_skipped_by_a_decoder_that_predates_it() {
        let ident = LogIdentity {
            id: [0x5a; 16],
            generation: 2,
        };
        let served = ServedInfo {
            requested: Tier::Relaxed,
            served: Tier::Strict,
            reason: ServedReason::LatchedAfterFlushFailure,
            horizon_ms: None,
            rules: 1,
        };
        let lineage = crate::logid::step(&Lineage::default(), 2, 9);
        for poisoned in [None, Some("a flush failed (injected)".to_string())] {
            let ext = NonceExt {
                durability: Some(served),
                lineage: Some(lineage.clone()),
                requests: None,
                retention: None,
                health: Some(HelloHealth {
                    poisoned: poisoned.clone(),
                    flushes: crate::store::FlushCounts {
                        barrier: 3,
                        full: 2,
                        skipped: 1,
                        failed: 1,
                    },
                }),
                device: None,
            };
            let frame = encode_response(&Response::Nonce {
                nonce: vec![7; 32],
                log: Some(ident),
                ext: ext.clone(),
            });
            assert_eq!(
                older_client_ext(ext_block(&frame)),
                Some((Some(served), Some(lineage.clone()))),
                "an older client reads the tier and the lineage, the health skipped"
            );
            match decode_response(&frame) {
                Some(Response::Nonce { ext: got, .. }) => assert_eq!(got, ext),
                other => panic!("{other:?}"),
            }
            // The control: the entry's length now runs one byte past the frame.
            let cut = &frame[..frame.len() - 1];
            assert_eq!(older_client_ext(ext_block(cut)), None, "cut short: refused");
            assert_eq!(decode_response(cut), None);
        }
    }

    /// The health entry's own layout: it round-trips healthy and poisoned (an empty
    /// reason included, which is still a poison); a reason past [`HELLO_REASON_MAX`] is
    /// cut there at a character boundary, never inside one; flag bits other than bit 0
    /// and bytes after the reason are a later build's, ignored; and a reason that is
    /// not UTF-8, or a body cut inside its fixed part or its reason, is malformed.
    #[test]
    fn the_health_entry_round_trips_and_cuts_a_long_reason_at_a_char_boundary() {
        let round = |h: &HelloHealth| {
            let mut b = Vec::new();
            h.put(&mut b);
            (HelloHealth::from_wire(&b), b)
        };
        let healthy = HelloHealth::default();
        assert_eq!(round(&healthy).0, Some(healthy.clone()));
        let empty_reason = HelloHealth {
            poisoned: Some(String::new()),
            flushes: crate::store::FlushCounts::default(),
        };
        assert_eq!(round(&empty_reason).0, Some(empty_reason.clone()));

        // 1023 ASCII bytes then a 3-byte character: the cut at 1024 would split it.
        let long = format!("{}€tail", "x".repeat(HELLO_REASON_MAX - 1));
        let (got, bytes) = round(&HelloHealth {
            poisoned: Some(long),
            flushes: crate::store::FlushCounts::default(),
        });
        let reason = got.unwrap().poisoned.unwrap();
        assert_eq!(reason, "x".repeat(HELLO_REASON_MAX - 1), "cut before the €");
        assert_eq!(bytes.len(), HEALTH_FIXED_LEN + HELLO_REASON_MAX - 1);

        let (_, mut later) = round(&healthy);
        later[0] |= 0b110;
        later.extend_from_slice(&[0xEE; 9]);
        assert_eq!(HelloHealth::from_wire(&later), Some(healthy.clone()));

        let (_, poisoned) = round(&HelloHealth {
            poisoned: Some("why".into()),
            flushes: crate::store::FlushCounts::default(),
        });
        let mut not_utf8 = poisoned.clone();
        let last = not_utf8.len() - 1;
        not_utf8[last] = 0xFF;
        assert_eq!(HelloHealth::from_wire(&not_utf8), None);
        for cut in [1, HEALTH_FIXED_LEN - 1, poisoned.len() - 1] {
            assert_eq!(HelloHealth::from_wire(&poisoned[..cut]), None, "cut {cut}");
        }
    }

    /// HELLO ADVERTISES THE RULES: a block carrying a broker's retention reads back as
    /// those rules, and one carrying none as none.
    #[cfg(feature = "retention")]
    #[test]
    fn the_nonce_extension_block_advertises_the_retention_rules() {
        let rules = crate::parse_rules(
            "prefix age=7d bytes=256MiB /f/F/pub/*/*/ev\n\
             hold age=7d bytes=64MiB read=/f/{2}/cur/{4}/node/inbox /f/F/in/>\n\
             hold last /f/F/pub/*/*/presence\n\
             default age=7d bytes=32MiB\n",
        )
        .unwrap();
        let ident = LogIdentity {
            id: [0xee; 16],
            generation: 1,
        };
        let ext = NonceExt {
            retention: Some(rules.encode()),
            ..NonceExt::default()
        };
        let frame = encode_response(&Response::Nonce {
            nonce: vec![3; 32],
            log: Some(ident),
            ext,
        });
        let Some(Response::Nonce { ext, .. }) = decode_response(&frame) else {
            panic!("the Nonce decodes")
        };
        assert_eq!(ext.retention_rules(), Some(rules));
        assert_eq!(NonceExt::default().retention_rules(), None);
    }

    /// THE HORIZON TELLS NO BOUND FROM A FLUSH AFTER EVERY BATCH. An Ordered broker with
    /// no horizon (a power loss can take every batch since the last escalation) and one
    /// with a zero horizon (a full flush after every batch) are opposite promises, and
    /// both used to read `horizon_ms = 0` — the value Strict sent too. Now none reads
    /// `None`, zero reads `Some(0)`, a sub-millisecond horizon rounds UP to `Some(1)`
    /// (never down to the every-batch promise), and a horizon on a tier other than
    /// Ordered is no horizon whatever the wire carried (the broker before Ordered sent 0
    /// for Strict and Relaxed).
    #[test]
    fn the_hello_horizon_tells_none_from_zero() {
        use std::time::Duration;
        let ident = LogIdentity {
            id: [0xcd; 16],
            generation: 0,
        };
        let told = |requested: Tier, horizon_ms: Option<u32>| {
            let ext = NonceExt {
                durability: Some(ServedInfo {
                    requested,
                    served: requested,
                    reason: ServedReason::None,
                    horizon_ms,
                    rules: 1,
                }),
                lineage: None,
                retention: None,
                requests: None,
                health: None,
                device: None,
            };
            let frame = encode_response(&Response::Nonce {
                nonce: vec![2; 32],
                log: Some(ident),
                ext,
            });
            match decode_response(&frame) {
                Some(Response::Nonce { ext, .. }) => ext.durability.unwrap().horizon_ms,
                other => panic!("{other:?}"),
            }
        };
        assert_eq!(told(Tier::Ordered, None), None, "no horizon");
        assert_eq!(told(Tier::Ordered, Some(0)), Some(0), "every batch");
        assert_eq!(told(Tier::Ordered, Some(1000)), Some(1000));
        assert_ne!(told(Tier::Ordered, None), told(Tier::Ordered, Some(0)));
        assert_eq!(told(Tier::Strict, Some(0)), None, "not Ordered: no horizon");
        assert_eq!(told(Tier::Relaxed, Some(0)), None);
        assert_eq!(ServedInfo::horizon_ms_of(Duration::ZERO), 0);
        assert_eq!(ServedInfo::horizon_ms_of(Duration::from_nanos(1)), 1);
        assert_eq!(ServedInfo::horizon_ms_of(Duration::from_micros(999)), 1);
        assert_eq!(ServedInfo::horizon_ms_of(Duration::from_millis(1000)), 1000);
        assert_eq!(ServedInfo::horizon_ms_of(Duration::from_micros(1001)), 2);
        assert_eq!(
            ServedInfo::horizon_ms_of(Duration::MAX),
            u32::MAX - 1,
            "a real horizon never reads as none"
        );
    }

    /// THE REFUSAL A PEER OF ANY VERSION READS, pinned byte by byte:
    /// `[peer][0x83][ERR_PROTOCOL][len:u32 LE][msg][PROTO_VERSION]`. Under the peer's own
    /// version byte it is the refusal layout every version keeps, so the peer's decoder
    /// reads `Error { code: 9 }`; the byte after the message, which no decoder reads, is
    /// how the peer learns which protocol this broker speaks.
    #[test]
    fn a_protocol_refusal_is_readable_by_the_peer_it_refuses() {
        for peer in [0, PROTO_VERSION - 1, PROTO_VERSION + 1, u8::MAX] {
            let refusal = encode_protocol_refusal(peer);
            assert_eq!(refusal[..3], [peer, 0x83, ERR_PROTOCOL], "peer {peer}");
            let len = u32::from_le_bytes(refusal[3..7].try_into().unwrap()) as usize;
            assert_eq!(
                refusal.len(),
                7 + len + 1,
                "peer {peer}: the message, then one byte"
            );
            assert_eq!(refusal[refusal.len() - 1], PROTO_VERSION, "peer {peer}");
            // The decoder this build has is the protocol-2 one, so the frozen layout is
            // checked through it: the same bytes under its version byte are a refusal.
            let mut restamped = refusal.clone();
            restamped[0] = PROTO_VERSION;
            assert!(
                matches!(
                    decode_response(&restamped),
                    Some(Response::Error {
                        code: ERR_PROTOCOL,
                        ..
                    })
                ),
                "peer {peer}"
            );
            // And the peer, reading it in its own protocol, learns this broker's.
            assert_eq!(
                foreign_protocol_at(peer, &refusal),
                Some(PROTO_VERSION),
                "peer {peer}"
            );
        }
    }

    /// The two ways a reply says the broker speaks another protocol — stamped with
    /// another version (all a broker that predates `ERR_PROTOCOL` can send: its
    /// "malformed request", in its own protocol), or a protocol refusal in ours naming
    /// the broker's — and everything that is not one.
    #[test]
    fn foreign_protocol_reads_a_broker_in_another_protocol() {
        let stamped = |resp: &Response, version: u8| {
            let mut p = encode_response(resp);
            p[0] = version;
            p
        };
        let malformed = Response::Error {
            code: ERR_REFUSED,
            msg: "malformed request".into(),
        };
        let mark = Response::Mark {
            next: 1,
            head: 2,
            resume: String::new(),
            durable: None,
            oldest: None,
        };
        assert_eq!(
            foreign_protocol(&stamped(&malformed, PROTO_VERSION - 1)),
            Some(PROTO_VERSION - 1)
        );
        assert_eq!(
            foreign_protocol(&stamped(&mark, PROTO_VERSION + 1)),
            Some(PROTO_VERSION + 1)
        );
        // A newer broker's refusal, stamped with ours.
        let refusal_naming = |broker: u8| {
            let mut p = vec![PROTO_VERSION, TAG_ERROR, ERR_PROTOCOL];
            put_str(&mut p, "from a newer broker");
            p.push(broker);
            p
        };
        assert_eq!(
            foreign_protocol(&refusal_naming(PROTO_VERSION + 1)),
            Some(PROTO_VERSION + 1)
        );

        let mut two_after = refusal_naming(PROTO_VERSION + 1);
        two_after.push(0);
        for (what, reply) in [
            ("a refusal in ours", encode_response(&malformed)),
            ("a mark in ours", encode_response(&mark)),
            (
                "ERR_PROTOCOL naming no version",
                encode_response(&Response::Error {
                    code: ERR_PROTOCOL,
                    msg: String::new(),
                }),
            ),
            ("one naming ours", refusal_naming(PROTO_VERSION)),
            ("two bytes after the message", two_after),
            ("nothing", Vec::new()),
        ] {
            assert_eq!(foreign_protocol(&reply), None, "{what}");
        }
    }
}
