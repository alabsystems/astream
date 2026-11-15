// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Cross-broker federation (`ROADMAP.md` & `DESIGN-aterm-fabric` Federation across brokers):
//! durable consumer-group-backed subtree mirroring ([`FederationBridge`]) with deterministic
//! `(producer_id, src_offset)` exactly-once deduplication, [`LogIdentity`] lineage continuity
//! checks, loop-preventing [`SubjectRewrite`] rules, and Chandy-Lamport consistent cuts
//! ([`FederatedCut`]) across independent per-host broker logs.

use crate::broker::IDLE_MARK_DEADLINE;
use crate::client::{
    broker_refusal, connect, AnyClient, Closer, Event, Pipelined, Transport, ACK_SEQ_BASE,
};
use crate::logid::{Lineage, LogIdentity};
use crate::proto::{Gap, ERR_ORIGIN_REFUSED, ERR_ORIGIN_UNKNOWN, ERR_SUBJECT_BOUND};
use crate::store::is_hidden_subject;
use astream_wire::{CausalCut, CausalEdge, CutViolation, Filter, Offset as WireOffset, Subject};

/// Log offset (`u64`) on a federated source or destination broker.
pub type Offset = u64;
use std::fmt;
use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

#[cfg(clean_islands)]
#[path = "federation_island.rs"]
mod federation_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{federation_commit_bound, federation_cursor_advance, federation_seq_clamp};
#[cfg(clean_islands)]
pub use federation_island::{
    federation_commit_bound, federation_cursor_advance, federation_seq_clamp,
};

contract_fn! {
    /// Verified check that a federated record's hop count lies strictly below `max_hops`
    /// (`hops < max_hops`), linked via `clean-kernel-defeq` to `federation_hop_allowed_isl`.
    #[must_use]
    pub const fn federation_hop_allowed(hops: u8, max_hops: u8) -> bool
    clauses [ensures result == (hops < max_hops)]
    {
        hops < max_hops
    }
}

/// Maximum burst of records pipelined to the destination broker in one round trip.
const FEDERATION_BATCH_CAP: usize = 256;

/// The most relayed records one [`FederationBridge::run`] keeps in hand for a destination that did
/// not take their origin ([`ERR_ORIGIN_UNKNOWN`]). Past it, or past [`HELD_BYTES`], a record is
/// kept by its offset alone, and the run reads again from there once the rest are answered.
pub const HELD_CAP: usize = 4096;

/// The most body bytes the records of [`HELD_CAP`] may take; a run always keeps the first.
pub const HELD_BYTES: usize = 16 * 1024 * 1024;

/// Wire transport for dialing a source or destination broker in [`FederationEndpoint`].
#[derive(Clone)]
pub enum FederationWire {
    /// Any standard client [`Transport`] (`Unix`, `Tcp`, `Sealed`, or `Handshake`).
    Client(Transport),
    /// Mutual Ed25519 signed-DH (`Broker::serve_tcp_identity`) with a pinned server key.
    #[cfg(feature = "identity")]
    Identity {
        /// Bridge's Ed25519 client identity keypair.
        identity: Arc<astream_aead::IdentityKeypair>,
        /// Pinned 32-byte Ed25519 public key expected from the remote broker.
        expected_server: [u8; astream_aead::ID_PUB_LEN],
    },
    /// A stream the embedder already authenticated ([`Broker::serve_stream`] at the other end).
    /// [`FederationEndpoint::endpoint`] only names the peer; `connect_timeout` is the dialer's
    /// to apply.
    ///
    /// [`Broker::serve_stream`]: crate::Broker::serve_stream
    #[cfg(feature = "stream")]
    Stream(Arc<dyn crate::stream_link::StreamDial>),
}

impl fmt::Debug for FederationWire {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FederationWire::Client(t) => write!(f, "FederationWire::Client({t:?})"),
            #[cfg(feature = "identity")]
            FederationWire::Identity { .. } => f.write_str("FederationWire::Identity(<pinned>)"),
            #[cfg(feature = "stream")]
            FederationWire::Stream(_) => f.write_str("FederationWire::Stream(<dialer>)"),
        }
    }
}

/// Connection specification (address, transport, timeouts, and optional capability keyring)
/// for one side of a [`FederationBridge`].
#[derive(Clone, Debug)]
pub struct FederationEndpoint {
    /// Socket path (`Transport::Unix`) or `host:port` TCP address.
    pub endpoint: String,
    /// Wire transport and authentication credentials.
    pub wire: FederationWire,
    /// Optional TCP/handshake dial deadline.
    pub connect_timeout: Option<Duration>,
    /// Optional per-request socket read/write deadline once connected.
    pub io_timeout: Option<Duration>,
    /// Capabilities attached immediately after connecting on guarded brokers.
    #[cfg(feature = "cap")]
    pub caps: Vec<astream_cap::Capability>,
    /// Raw `(grant, tag)` pairs (as read from `capfile`) attached on connect.
    pub grant_tags: Vec<(String, [u8; 32])>,
}

impl FederationEndpoint {
    /// Create an endpoint over a standard [`Transport`] (`Unix`, `Tcp`, `Sealed`, `Handshake`).
    #[must_use]
    pub fn new(endpoint: &str, transport: Transport) -> Self {
        Self {
            endpoint: endpoint.to_string(),
            wire: FederationWire::Client(transport),
            connect_timeout: Some(Duration::from_secs(5)),
            io_timeout: Some(Duration::from_secs(10)),
            #[cfg(feature = "cap")]
            caps: Vec::new(),
            grant_tags: Vec::new(),
        }
    }

    /// Create an endpoint over mutual Ed25519 signed-DH (`Broker::serve_tcp_identity`).
    #[cfg(feature = "identity")]
    #[must_use]
    pub fn identity(
        endpoint: &str,
        identity: Arc<astream_aead::IdentityKeypair>,
        expected_server: [u8; astream_aead::ID_PUB_LEN],
    ) -> Self {
        Self {
            endpoint: endpoint.to_string(),
            wire: FederationWire::Identity {
                identity,
                expected_server,
            },
            connect_timeout: Some(Duration::from_secs(5)),
            io_timeout: Some(Duration::from_secs(10)),
            #[cfg(feature = "cap")]
            caps: Vec::new(),
            grant_tags: Vec::new(),
        }
    }

    /// Create an endpoint over streams `dial` opens to the broker named `peer`.
    #[cfg(feature = "stream")]
    #[must_use]
    pub fn stream(peer: &str, dial: Arc<dyn crate::stream_link::StreamDial>) -> Self {
        Self {
            endpoint: peer.to_string(),
            wire: FederationWire::Stream(dial),
            connect_timeout: None,
            io_timeout: Some(Duration::from_secs(10)),
            #[cfg(feature = "cap")]
            caps: Vec::new(),
            grant_tags: Vec::new(),
        }
    }

    /// Attach a capability keyring presented on every dial/reconnect.
    #[cfg(feature = "cap")]
    #[must_use]
    pub fn with_caps(mut self, caps: Vec<astream_cap::Capability>) -> Self {
        self.caps = caps;
        self
    }

    /// Attach raw `(grant, tag)` lines (e.g. loaded from `--cap-file`) presented on every dial.
    #[must_use]
    pub fn with_grant_tags(mut self, grant_tags: Vec<(String, [u8; 32])>) -> Self {
        self.grant_tags = grant_tags;
        self
    }

    /// Override `(connect_timeout, io_timeout)`.
    #[must_use]
    pub const fn with_timeouts(
        mut self,
        connect_timeout: Option<Duration>,
        io_timeout: Option<Duration>,
    ) -> Self {
        self.connect_timeout = connect_timeout;
        self.io_timeout = io_timeout;
        self
    }

    fn dial(&self) -> io::Result<(AnyClient, Closer)> {
        #[cfg_attr(not(feature = "cap"), allow(unused_mut))]
        let (mut client, closer) = match &self.wire {
            FederationWire::Client(t) => connect(t, &self.endpoint, self.connect_timeout)?,
            #[cfg(feature = "identity")]
            FederationWire::Identity {
                identity,
                expected_server,
            } => crate::client::connect_identity(
                &self.endpoint,
                identity,
                expected_server,
                self.connect_timeout,
            )?,
            #[cfg(feature = "stream")]
            FederationWire::Stream(dialer) => {
                crate::client::connect_stream_end(crate::stream_link::dial_stream_link(dialer)?)
            }
        };
        if let Some(io_to) = self.io_timeout {
            closer.set_read_timeout(Some(io_to))?;
            closer.set_write_timeout(Some(io_to))?;
        }
        #[cfg(feature = "cap")]
        if !self.caps.is_empty() {
            let mut ring: Vec<(&str, &[u8])> = Vec::with_capacity(self.caps.len().min(64));
            for cap in &self.caps {
                ring.push((cap.filter.as_str(), cap.tag.as_slice()));
            }
            client.attach_all(ring)?;
        }
        if !self.grant_tags.is_empty() {
            let mut ring: Vec<(&str, &[u8])> = Vec::with_capacity(self.grant_tags.len().min(64));
            for (grant, tag) in &self.grant_tags {
                ring.push((grant.as_str(), tag.as_slice()));
            }
            client.attach_all(ring)?;
        }
        Ok((client, closer))
    }
}

/// Subject prefix transformation and loop-exclusion policy for [`FederationBridge`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SubjectRewrite {
    /// Leading segment prefix stripped from matched source subjects (`""` = strip nothing).
    pub strip_prefix: String,
    /// Leading segment prefix prepended on the destination broker (`""` = add nothing).
    pub add_prefix: String,
    /// Segment prefixes skipped as peer-federated echo traffic so bidirectional bridges
    /// (`Host A <-> Host B`) never re-mirror records back to their origin.
    pub exclude_prefixes: Vec<String>,
    /// Current federation hop index (`0` for direct origin -> peer mirroring).
    pub hops: u8,
    /// Maximum allowed hop count (`1` by default; `0` blocks all forwarding).
    pub max_hops: u8,
}

impl SubjectRewrite {
    /// Identity pass-through (`max_hops = 1`, no prefix rewrite, no exclusions).
    #[must_use]
    pub fn passthrough() -> Self {
        Self {
            strip_prefix: String::new(),
            add_prefix: String::new(),
            exclude_prefixes: Vec::new(),
            hops: 0,
            max_hops: 1,
        }
    }

    /// Map `<strip_prefix>/...` on the source broker to `<add_prefix>/...` on the
    /// destination broker (`max_hops = 1`).
    pub fn prefix_map(strip_prefix: &str, add_prefix: &str) -> Result<Self, String> {
        let rw = Self {
            strip_prefix: strip_prefix.to_string(),
            add_prefix: add_prefix.to_string(),
            exclude_prefixes: Vec::new(),
            hops: 0,
            max_hops: 1,
        };
        rw.validate()?;
        Ok(rw)
    }

    /// Add a segment prefix excluded from mirroring (bidirectional loop prevention).
    pub fn with_excluded_prefix(mut self, prefix: &str) -> Result<Self, String> {
        validate_prefix_shape(prefix, "exclude_prefix")?;
        self.exclude_prefixes.push(prefix.to_string());
        Ok(self)
    }

    /// Set `(hops, max_hops)` checked via [`federation_hop_allowed`].
    #[must_use]
    pub const fn with_hop_budget(mut self, hops: u8, max_hops: u8) -> Self {
        self.hops = hops;
        self.max_hops = max_hops;
        self
    }

    /// Validate all configured prefixes against `astream-wire`'s subject grammar.
    pub fn validate(&self) -> Result<(), String> {
        if !self.strip_prefix.is_empty() {
            validate_prefix_shape(&self.strip_prefix, "strip_prefix")?;
        }
        if !self.add_prefix.is_empty() {
            validate_prefix_shape(&self.add_prefix, "add_prefix")?;
        }
        for ex in &self.exclude_prefixes {
            validate_prefix_shape(ex, "exclude_prefix")?;
        }
        Ok(())
    }

    /// Rewrite `src_subject`, returning `Ok(None)` if excluded by loop-prevention rules or
    /// hop budget, `Ok(Some(dst_subject))` when eligible, or `Err` if resulting subject is invalid.
    pub fn apply(&self, src_subject: &str) -> Result<Option<String>, String> {
        if !federation_hop_allowed(self.hops, self.max_hops) {
            return Ok(None);
        }
        for ex in &self.exclude_prefixes {
            if matches_segment_prefix(src_subject, ex) {
                return Ok(None);
            }
        }
        if !self.add_prefix.is_empty() && matches_segment_prefix(src_subject, &self.add_prefix) {
            // Already carries the destination's federated prefix: never double-wrap or loop.
            return Ok(None);
        }
        let tail = if self.strip_prefix.is_empty() {
            src_subject
        } else if src_subject == self.strip_prefix {
            return Err(format!(
                "source subject {src_subject:?} equals strip_prefix {:?} with no trailing segment",
                self.strip_prefix
            ));
        } else {
            match src_subject.strip_prefix(&self.strip_prefix) {
                Some(rest) if rest.starts_with('/') => rest,
                _ => return Ok(None),
            }
        };
        let mapped = if self.add_prefix.is_empty() {
            tail.to_string()
        } else {
            format!("{}{tail}", self.add_prefix)
        };
        if Subject::new(&mapped).is_err() {
            return Err(format!(
                "rewritten subject {mapped:?} is not a valid Subject"
            ));
        }
        Ok(Some(mapped))
    }
}

fn validate_prefix_shape(prefix: &str, field: &str) -> Result<(), String> {
    if prefix.is_empty() || !prefix.starts_with('/') || prefix.ends_with('/') {
        return Err(format!(
            "{field} {prefix:?} must start with '/' and not end with '/'"
        ));
    }
    if Subject::new(prefix).is_err() {
        return Err(format!("{field} {prefix:?} is not a valid Subject prefix"));
    }
    Ok(())
}

fn matches_segment_prefix(subject: &str, prefix: &str) -> bool {
    if subject == prefix {
        return true;
    }
    match subject.strip_prefix(prefix) {
        Some(rest) => rest.starts_with('/'),
        None => false,
    }
}

/// Configuration for opening a [`FederationBridge`].
#[derive(Clone, Debug)]
pub struct FederationConfig {
    /// Source broker endpoint to mirror from.
    pub source: FederationEndpoint,
    /// Destination broker endpoint to publish onto.
    pub dest: FederationEndpoint,
    /// Durable consumer-group name on `source` (must be a valid `Subject`, e.g. `"/g/fed/host-b"`).
    pub group: String,
    /// Subscription [`Filter`] selecting records on `source` (e.g. `"/f/fleet/pub/host-a/>"`).
    pub filter: String,
    /// The filters within `filter` this bridge carries, when one group follows several: a record
    /// of `filter` is carried only where one of these matches it too, and is otherwise skipped
    /// (counted in [`FederationReport::skipped`]) exactly as a rewrite that drops it; empty carries
    /// every record of `filter`. Each must be a [`Filter`] that `filter` contains. The group still
    /// tails `filter` and commits past every record it scans, carried or not, so a union of lanes
    /// under one group is one edge whose cursor never passes a record of any of them it has not
    /// carried; two bridges on one group, one per lane, are not: either one's commit would pass the
    /// other's unsent records.
    pub carry: Vec<String>,
    /// Stable `producer_id` used on `dest` (on a guarded destination broker with a bound
    /// `rw,p=<principal>:` grant, set to `astream_cap::producer_id_of(principal)`).
    pub producer_id: u64,
    /// Subject prefix mapping and loop-prevention policy.
    pub rewrite: SubjectRewrite,
    /// RELAY rather than mirror: carry each record under its ORIGIN's `(producer_id, producer_seq)`
    /// instead of `(producer_id, src_offset)`, with its subject and its body, the origin's signed
    /// envelope, unchanged. The key is then the same
    /// on every broker, so bridges may form any graph, cycles included, each broker appends a
    /// record once, and mirrored records may be re-exported. `producer_id` goes unused. A mirror's
    /// key names one path, so a mirror on a cycle echoes forever. Relay runs by push alone
    /// ([`FederationBridge::run`]), only over owner-shaped subjects (`astream_cap::relay_owner`),
    /// and needs the `cap` feature. On guarded brokers the source takes a read grant
    /// over `filter` and a write grant over `group`, and the destination a relay grant.
    pub relay: bool,
}

/// Cross-broker provenance receipt emitted for each mirrored record, directly convertible
/// into a Chandy-Lamport [`CausalEdge<LogIdentity>`] for [`FederatedCut`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FederationLink {
    /// Source broker's [`LogIdentity`] at the time the record was read.
    pub src_log: LogIdentity,
    /// Source broker offset of the mirrored record.
    pub src_offset: Offset,
    /// Destination broker's [`LogIdentity`] at the time the record was published.
    pub dst_log: LogIdentity,
    /// Destination broker offset assigned (or deduplicated) for the mirrored record.
    pub dst_offset: Offset,
    /// `true` when `dest` already held `(producer_id, src_offset)` from an earlier attempt.
    pub deduped: bool,
    /// Rewritten subject published onto `dest`.
    pub dst_subject: String,
}

impl FederationLink {
    /// View this cross-broker mirror receipt as a directed [`CausalEdge<LogIdentity>`]
    /// (`cause: (src_log, src_offset) -> effect: (dst_log, dst_offset)`).
    #[must_use]
    pub const fn causal_edge(&self) -> CausalEdge<LogIdentity> {
        CausalEdge {
            cause: (self.src_log, WireOffset(self.src_offset)),
            effect: (self.dst_log, WireOffset(self.dst_offset)),
        }
    }
}

/// Summary returned by [`FederationBridge::sync_once`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FederationReport {
    /// Matching records fetched from `source` in this step.
    pub fetched: usize,
    /// Records published (or deduplicated) onto `dest`.
    pub mirrored: usize,
    /// Subset of `mirrored` that deduplicated against an existing record on `dest`.
    pub deduped: usize,
    /// Records skipped by loop-exclusion / hop-limit / prefix policy or outside
    /// [`FederationConfig::carry`], and, on a relay, those whose producer is not their subject's
    /// owner: no destination would take them.
    pub skipped: usize,
    /// Relayed records the destination refused for good: a bad signature, a revoked origin, a
    /// record that is not its origin's, or an origin over its subject budget there; and a record
    /// whose origin the destination did not know and the source no longer seats
    /// ([`FederationBridge::hold_while`]). Not retried; the rest of the burst still lands, so one
    /// bad record does not stop an edge.
    pub refused: usize,
    /// Relayed records the run holds back after this step, a gauge: the destination did not take
    /// their origin ([`ERR_ORIGIN_UNKNOWN`]), and the source still seats it
    /// ([`FederationBridge::hold_while`]). The first of each origin's is offered again with every
    /// later burst and mark, and the group is never committed past the lowest of them.
    pub held: usize,
    /// Highest `source` offset durably committed for `group` at the end of this step, if any: a
    /// commit is inclusive, so a restarted bridge resumes one past it. A relay's commit stays
    /// below every record it holds.
    pub committed_upto: Option<Offset>,
    /// Bridge's next `source` fetch cursor after this step.
    pub next_cursor: Offset,
    /// Provenance links (`src_log@src_offset -> dst_log@dst_offset`) produced in this step.
    pub links: Vec<FederationLink>,
    /// What retention gave up on `source` below this bridge's group, as its tail was told
    /// ([`FederationBridge::run`] only): records it will never mirror.
    pub gaps: Vec<Gap>,
}

/// Failure modes of [`FederationBridge`].
#[derive(Debug)]
pub enum FederationError {
    /// Invalid configuration (bad filter, bad group subject, bad rewrite, or self-loop).
    Config(String),
    /// Remote broker did not advertise a [`LogIdentity`] in `Hello`.
    MissingLogIdentity {
        /// `"source"` or `"dest"`.
        role: &'static str,
    },
    /// Source broker's [`LogIdentity`] changed without continuing across `cursor`
    /// (truncated below `cursor`, restored from an older backup, or replaced).
    SourceLogDiverged {
        /// Previously pinned source identity.
        expected: LogIdentity,
        /// Newly observed source identity.
        found: LogIdentity,
        /// Bridge cursor that is no longer vouched for by `found.continues(&expected)`.
        cursor: Offset,
    },
    /// Destination broker's [`LogIdentity`] changed to an incompatible log/generation.
    DestLogChanged {
        /// Previously pinned destination identity.
        expected: LogIdentity,
        /// Newly observed destination identity.
        found: LogIdentity,
    },
    /// Source offset reached the reserved `ACK_SEQ_BASE` half (`>= 2^63`).
    OffsetInReservedHalf(Offset),
    /// Rewritten subject failed validation.
    Rewrite(String),
    /// A relay held more records than one run keeps ([`HELD_CAP`], [`HELD_BYTES`]) for a
    /// destination that did not take their origin, and the destination has answered all it kept:
    /// its group is committed below `from`, so the next run reads again from there.
    HeldBack {
        /// The lowest offset held by offset alone.
        from: Offset,
    },
    /// Underlying broker or socket I/O error.
    Io(io::Error),
}

impl fmt::Display for FederationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FederationError::Config(msg) => write!(f, "federation config error: {msg}"),
            FederationError::MissingLogIdentity { role } => {
                write!(f, "federation {role} broker did not report a LogIdentity")
            }
            FederationError::SourceLogDiverged {
                expected,
                found,
                cursor,
            } => write!(
                f,
                "federation source log diverged at cursor {cursor}: expected {expected}, found {found}"
            ),
            FederationError::DestLogChanged { expected, found } => write!(
                f,
                "federation destination log identity changed: expected {expected}, found {found}"
            ),
            FederationError::OffsetInReservedHalf(off) => write!(
                f,
                "federation source offset {off} enters reserved ACK_SEQ_BASE half"
            ),
            FederationError::Rewrite(msg) => write!(f, "federation subject rewrite error: {msg}"),
            FederationError::HeldBack { from } => write!(
                f,
                "federation relay held more records than it keeps for origins its destination did not take; it reads again from {from}"
            ),
            FederationError::Io(e) => write!(f, "federation I/O error: {e}"),
        }
    }
}

impl std::error::Error for FederationError {}

/// Durable, loop-free, exactly-once cross-broker subtree bridge (`source -> dest`).
pub struct FederationBridge {
    cfg: FederationConfig,
    src_ctl: AnyClient,
    src_closer: Closer,
    dst: AnyClient,
    dst_closer: Closer,
    src_log: LogIdentity,
    dst_log: LogIdentity,
    cursor: Offset,
    closer: FederationBridgeCloser,
    liveness: Duration,
    seated: Option<Seated>,
    /// [`FederationConfig::carry`], parsed.
    carry: Vec<Filter>,
}

/// Whether the source still seats a relayed record's owner ([`FederationBridge::hold_while`]).
pub type Seated = Arc<dyn Fn(&str) -> bool + Send + Sync>;

impl FederationBridge {
    /// Validate `cfg`, dial `source` and `dest`, pin both [`LogIdentity`] values, and
    /// bootstrap `cursor` from `cfg.group`'s durable committed position on `source`.
    pub fn open(cfg: FederationConfig) -> Result<Self, FederationError> {
        if Subject::new(&cfg.group).is_err() || is_hidden_subject(&cfg.group) {
            return Err(FederationError::Config(format!(
                "group {:?} must be a valid non-reserved Subject",
                cfg.group
            )));
        }
        let Ok(filter) = Filter::new(&cfg.filter) else {
            return Err(FederationError::Config(format!(
                "filter {:?} is not a valid Filter",
                cfg.filter
            )));
        };
        let carry = carried_within(&filter, &cfg.carry)?;
        if let Err(msg) = cfg.rewrite.validate() {
            return Err(FederationError::Config(msg));
        }
        if cfg.relay {
            if !cfg!(feature = "cap") {
                return Err(FederationError::Config(
                    "a relay bridge needs astream-broker's `cap` feature".to_string(),
                ));
            }
            if !cfg.rewrite.strip_prefix.is_empty() || !cfg.rewrite.add_prefix.is_empty() {
                return Err(FederationError::Config(
                    "a relay carries a record under its own subject: it takes no prefix rewrite"
                        .to_string(),
                ));
            }
        }

        let (mut src_ctl, src_closer) = match cfg.source.dial() {
            Ok(pair) => pair,
            Err(e) => return Err(FederationError::Io(e)),
        };
        let src_log = read_client_identity(&mut src_ctl, "source")?;

        let (mut dst, dst_closer) = match cfg.dest.dial() {
            Ok(pair) => pair,
            Err(e) => return Err(FederationError::Io(e)),
        };
        let dst_log = read_client_identity(&mut dst, "dest")?;

        if src_log.id == dst_log.id && cfg.rewrite.add_prefix.is_empty() {
            return Err(FederationError::Config(
                "refusing self-federation onto the same broker LogIdentity without a loop-guarded add_prefix".to_string(),
            ));
        }

        let cursor = bootstrap_group_cursor(&cfg.source, &cfg.group, &cfg.filter)?;
        Ok(Self {
            cfg,
            src_ctl,
            src_closer,
            dst,
            dst_closer,
            src_log,
            dst_log,
            cursor,
            closer: FederationBridgeCloser::default(),
            liveness: IDLE_MARK_DEADLINE,
            seated: None,
            carry,
        })
    }

    /// Pinned [`LogIdentity`] of the source broker.
    #[must_use]
    pub const fn source_identity(&self) -> LogIdentity {
        self.src_log
    }

    /// Pinned [`LogIdentity`] of the destination broker.
    #[must_use]
    pub const fn dest_identity(&self) -> LogIdentity {
        self.dst_log
    }

    /// Current source fetch cursor (`>= group_start` at open).
    #[must_use]
    pub const fn cursor(&self) -> Offset {
        self.cursor
    }

    /// Re-dial `source` and `dest` after a transient network error, verifying that both
    /// brokers' [`LogIdentity`] values remain consistent with `self.cursor`.
    pub fn reconnect(&mut self) -> Result<(), FederationError> {
        self.src_closer.close();
        self.dst_closer.close();

        let (mut new_src, new_src_closer) = match self.cfg.source.dial() {
            Ok(pair) => pair,
            Err(e) => return Err(FederationError::Io(e)),
        };
        let found_src = read_client_identity(&mut new_src, "source")?;
        let lineage = new_src.log_lineage().cloned();
        self.verify_or_adopt_source_identity(found_src, lineage.as_ref())?;

        let (mut new_dst, new_dst_closer) = match self.cfg.dest.dial() {
            Ok(pair) => pair,
            Err(e) => return Err(FederationError::Io(e)),
        };
        let found_dst = read_client_identity(&mut new_dst, "dest")?;
        if found_dst != self.dst_log {
            return Err(FederationError::DestLogChanged {
                expected: self.dst_log,
                found: found_dst,
            });
        }

        self.src_ctl = new_src;
        self.src_closer = new_src_closer;
        self.dst = new_dst;
        self.dst_closer = new_dst_closer;
        Ok(())
    }

    fn verify_or_adopt_source_identity(
        &mut self,
        found: LogIdentity,
        lineage: Option<&Lineage>,
    ) -> Result<(), FederationError> {
        if found == self.src_log {
            return Ok(());
        }
        if let Some(lin) = lineage {
            if let Some(common) = found.continues(self.src_log, lin) {
                if self.cursor <= common {
                    self.src_log = found;
                    return Ok(());
                }
            }
        }
        Err(FederationError::SourceLogDiverged {
            expected: self.src_log,
            found,
            cursor: self.cursor,
        })
    }

    /// Whether this bridge carries a record of `subject` ([`FederationConfig::carry`]).
    fn carries(&self, subject: &str) -> bool {
        self.carry.is_empty() || self.carry.iter().any(|f| f.matches_str(subject))
    }

    /// Fetch up to `max_records` (`1..=256`) matching records from `source`, pipeline
    /// eligible rewritten publishes onto `dest` under deterministic `(producer_id, src_offset)`
    /// dedup keys, and durably commit `cfg.group` on `source` only after `dest` acknowledges
    /// the entire batch.
    pub fn sync_once(&mut self, max_records: usize) -> Result<FederationReport, FederationError> {
        if self.cfg.relay {
            return Err(FederationError::Config(
                "a relay bridge runs by push: FederationBridge::run".to_string(),
            ));
        }
        let bounded_max = max_records.clamp(1, FEDERATION_BATCH_CAP) as u32;
        let ((records, (page_next, _head)), _gap) =
            match self
                .src_ctl
                .fetch_told(self.cursor, &self.cfg.filter, bounded_max)
            {
                Ok(res) => res,
                Err(e) => return Err(FederationError::Io(e)),
            };

        let fetched = records.len();
        let max_seq = ACK_SEQ_BASE.saturating_sub(1);
        let mut staged: Vec<Staged> = Vec::with_capacity(fetched.min(FEDERATION_BATCH_CAP));
        let mut highest_src_off: Option<Offset> = None;
        let mut skipped = 0usize;

        for (src_off, src_subj, body) in records {
            if src_off >= ACK_SEQ_BASE {
                return Err(FederationError::OffsetInReservedHalf(src_off));
            }
            highest_src_off = Some(match highest_src_off {
                Some(prev) => federation_cursor_advance(prev, src_off),
                None => src_off,
            });
            if is_hidden_subject(&src_subj) || !self.carries(&src_subj) {
                skipped = skipped.saturating_add(1);
                continue;
            }
            match self.cfg.rewrite.apply(&src_subj) {
                Ok(Some(dst_subj)) => staged.push(Staged {
                    src_off,
                    producer_id: self.cfg.producer_id,
                    seq: federation_seq_clamp(src_off, max_seq),
                    subject: dst_subj,
                    body,
                }),
                Ok(None) => {
                    skipped = skipped.saturating_add(1);
                }
                Err(msg) => return Err(FederationError::Rewrite(msg)),
            }
        }

        let Answers { links, deduped, .. } = self.mirror(staged)?;

        let committed_upto = match highest_src_off {
            Some(upto) => {
                if let Err(e) = self.src_ctl.commit(&self.cfg.group, upto) {
                    return Err(FederationError::Io(e));
                }
                Some(upto)
            }
            None => None,
        };

        let next_cur = match highest_src_off {
            Some(upto) => federation_cursor_advance(page_next, upto.saturating_add(1)),
            None => page_next,
        };
        self.cursor = federation_cursor_advance(self.cursor, next_cur);

        Ok(FederationReport {
            fetched,
            mirrored: links.len(),
            deduped,
            skipped,
            refused: 0,
            held: 0,
            committed_upto,
            next_cursor: self.cursor,
            links,
            gaps: Vec::new(),
        })
    }

    /// Pipeline `staged` onto `dest` and read every ack ([`Answers`]).
    fn mirror(&mut self, staged: Vec<Staged>) -> Result<Answers, FederationError> {
        let mut answers = Answers {
            links: Vec::with_capacity(staged.len().min(FEDERATION_BATCH_CAP)),
            ..Answers::default()
        };
        if staged.is_empty() {
            return Ok(answers);
        }
        let mut pipe_ops: Vec<Pipelined<'_>> =
            Vec::with_capacity(staged.len().min(FEDERATION_BATCH_CAP));
        for rec in &staged {
            pipe_ops.push(if self.cfg.relay {
                Pipelined::Relay {
                    producer_id: rec.producer_id,
                    producer_seq: rec.seq,
                    subject: rec.subject.as_str(),
                    body: rec.body.as_slice(),
                }
            } else {
                Pipelined::Publish {
                    producer_id: rec.producer_id,
                    producer_seq: rec.seq,
                    subject: rec.subject.as_str(),
                    body: rec.body.as_slice(),
                }
            });
        }
        if let Err(e) = self.dst.send_pipelined(&pipe_ops) {
            return Err(FederationError::Io(e));
        }
        drop(pipe_ops);
        // A refusal pays its ack, so every owed ack is read before any error returns: the
        // connection stays in step, though the caller reconnects on an error anyway.
        let mut failed = None;
        for rec in staged {
            let (dst_off, deduped) = match self.dst.recv_publish_ack() {
                Ok(ack) => ack,
                Err(e) => {
                    let code = broker_refusal(&e)
                        .map(|r| r.code)
                        .filter(|_| self.cfg.relay);
                    match code {
                        Some(ERR_SUBJECT_BOUND | ERR_ORIGIN_REFUSED) => {
                            answers.refused = answers.refused.saturating_add(1);
                        }
                        Some(ERR_ORIGIN_UNKNOWN) => answers.unknown.push(rec),
                        _ => {
                            if failed.is_none() {
                                failed = Some(e);
                            }
                        }
                    }
                    if self.dst.owed_acks() == 0 {
                        break;
                    }
                    continue;
                }
            };
            if deduped {
                answers.deduped = answers.deduped.saturating_add(1);
            }
            answers.links.push(FederationLink {
                src_log: self.src_log,
                src_offset: rec.src_off,
                dst_log: self.dst_log,
                dst_offset: dst_off,
                deduped,
                dst_subject: rec.subject,
            });
        }
        match failed {
            Some(e) => Err(FederationError::Io(e)),
            None => Ok(answers),
        }
    }

    /// Pipeline `records` onto `dest` in bursts of at most `FEDERATION_BATCH_CAP`, gathering the
    /// answers.
    fn mirror_all(&mut self, records: Vec<Staged>) -> Result<Answers, FederationError> {
        let mut all = Answers::default();
        let mut it = records.into_iter();
        loop {
            let mut batch = Vec::with_capacity(FEDERATION_BATCH_CAP);
            for _ in 0..FEDERATION_BATCH_CAP {
                match it.next() {
                    Some(rec) => batch.push(rec),
                    None => break,
                }
            }
            if batch.is_empty() {
                break;
            }
            let answers = self.mirror(batch)?;
            all.links.extend(answers.links);
            all.deduped = all.deduped.saturating_add(answers.deduped);
            all.refused = all.refused.saturating_add(answers.refused);
            all.unknown.extend(answers.unknown);
        }
        Ok(all)
    }

    /// Hold a relayed record the destination answers [`ERR_ORIGIN_UNKNOWN`] while `seated` says the
    /// source still seats its owner (the subject's owner, `astream_cap::relay_owner`): the
    /// destination may yet be given that origin's key, or see its revocation lifted. Once it says
    /// no, the record is counted refused and let go, as no destination will be told to take an
    /// origin the source does not. A bridge never told holds nothing: each such record is counted
    /// refused at once, as one that is not its origin's is.
    pub fn hold_while(&mut self, seated: Seated) {
        self.seated = Some(seated);
    }

    /// Whether a record of `subject` its destination did not take is still owed to it.
    fn still_seated(&self, subject: &str) -> bool {
        let Some(seated) = self.seated.as_ref() else {
            return false;
        };
        relay_owner(subject).is_some_and(|owner| seated(owner))
    }

    /// A handle that stops [`run`](Self::run) from another thread.
    #[must_use]
    pub fn closer(&self) -> FederationBridgeCloser {
        self.closer.clone()
    }

    /// How long a [`run`](Self::run) waits for any word from its source before it calls the source
    /// lost. A source writes an idle mark every [`IDLE_MARK`](crate::broker::IDLE_MARK) with
    /// nothing else to say; a deadline shorter than its broker's idle mark ends the run of a
    /// source that is only quiet.
    pub const fn set_liveness_deadline(&mut self, deadline: Duration) {
        self.liveness = deadline;
    }

    /// Mirror until stopped, by push: park on a `subscribe_group` of `source`, so a record reaches
    /// `dest` as soon as `source` can deliver it and an idle bridge does nothing at all. Up to
    /// `max_records` (`1..=256`) go to `dest` as one pipelined burst, cut where the source says its
    /// tail caught up ([`Request::BurstMarks`]), and the group is committed once per burst, only
    /// after `dest` acknowledged all of it, through the last offset the burst scanned. A group
    /// commit is inclusive (the group resumes one past it), so a burst cut at its cap commits the
    /// offset before the cut, a burst a mark ended the one before the mark's `next`, and a
    /// restarted bridge starts its scan at the cut or at that `next`. `on_burst` sees the report
    /// of each; a burst of nothing but a retention gap is reported too, for a caller that repairs
    /// on one.
    ///
    /// A relayed record whose origin the destination does not take now ([`ERR_ORIGIN_UNKNOWN`])
    /// is held back while the source seats it ([`hold_while`](Self::hold_while)), and so is every
    /// later record of that origin, unsent behind it, so an origin's records arrive in the order
    /// they left. The first of each origin's is offered again with every later burst, and with
    /// every mark while any is held (so at least every [`IDLE_MARK`](crate::broker::IDLE_MARK) on a
    /// quiet source); once the destination takes it, the rest of that origin's go at once. The group
    /// is committed below the lowest record held, so a restarted run delivers each again, and no
    /// record is passed for a destination that was only behind (`TlaPushEdge` in the island:
    /// `NoSkip`).
    ///
    /// Returns `Ok(())` once [`FederationBridgeCloser::close`] ends it. A lost connection, or a
    /// source silent past its liveness deadline ([`IDLE_MARK_DEADLINE`] unless
    /// [`set_liveness_deadline`](Self::set_liveness_deadline) says otherwise), is an `Err`, with
    /// no retry here: the durable group and the destination's dedup make the next
    /// `run` (after [`reconnect`](Self::reconnect), when the link is back) resume exactly.
    ///
    /// [`Request::BurstMarks`]: crate::proto::Request::BurstMarks
    pub fn run(
        &mut self,
        max_records: usize,
        on_burst: &mut dyn FnMut(&FederationReport),
    ) -> Result<(), FederationError> {
        let burst_cap = max_records.clamp(1, FEDERATION_BATCH_CAP);
        let (client, closer) = match self.cfg.source.dial() {
            Ok(pair) => pair,
            Err(e) => return Err(FederationError::Io(e)),
        };
        // Parked before the first read, so a stop can end a source that stops answering at any
        // point, and that read keeps the endpoint's io timeout until the tail is open.
        if !self.closer.park(closer.clone()) {
            return Ok(());
        }
        let _released = ReleasedOnExit(self.closer.clone());
        let mut sub = match self.open_tail(client) {
            Ok(sub) => sub,
            Err(_) if self.closer.stopping() => return Ok(()),
            Err(e) => return Err(e),
        };
        // A healthy source writes at least an idle mark in this time, however quiet it is, so
        // this does no work on a bridge with nothing to carry: it only makes a source that
        // vanished without a FIN the same lost connection as one that hung up.
        if let Err(e) = closer.set_read_timeout(Some(self.liveness)) {
            return Err(FederationError::Io(e));
        }
        let mut burst = Burst::default();
        let mut held = Held::default();
        loop {
            let event = sub.recv_event();
            match event {
                Ok(Some(Event::Delivery {
                    offset,
                    subject,
                    body,
                })) => {
                    burst.take(self, offset, sub.last_origin(), subject, body)?;
                    if burst.fetched >= burst_cap {
                        let upto = burst.next;
                        self.finish_burst(&mut burst, &mut held, upto, on_burst)?;
                    }
                }
                Ok(Some(Event::Mark { next, .. })) => {
                    self.finish_burst(&mut burst, &mut held, next, on_burst)?;
                }
                Ok(Some(Event::Gap(gap))) => burst.gaps.push(gap),
                Ok(None) => {
                    if self.closer.stopping() {
                        return Ok(());
                    }
                    return Err(FederationError::Io(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "source broker closed the bridge's subscription",
                    )));
                }
                Err(_) if self.closer.stopping() => return Ok(()),
                Err(e) => return Err(FederationError::Io(e)),
            }
        }
    }

    /// The handshake of a [`run`](Self::run)'s subscription, up to its open tail.
    fn open_tail(
        &mut self,
        mut client: AnyClient,
    ) -> Result<crate::client::AnySubscription, FederationError> {
        let found = read_client_identity(&mut client, "source")?;
        let lineage = client.log_lineage().cloned();
        self.verify_or_adopt_source_identity(found, lineage.as_ref())?;
        let asked = match client.burst_marks() {
            Ok(true) if self.cfg.relay => client.origin_stamps(),
            other => other,
        };
        match asked {
            Ok(true) => {}
            Ok(false) => return Err(FederationError::Config(
                "the source broker predates this bridge's asks: run the same astream release on both ends"
                    .to_string(),
            )),
            Err(e) => return Err(FederationError::Io(e)),
        }
        match client.subscribe_group(&self.cfg.group, &self.cfg.filter) {
            Ok(sub) => Ok(sub),
            Err(e) => Err(FederationError::Io(e)),
        }
    }

    /// Offer the records `held` back and `burst`'s, commit the group on `source`, and report.
    /// `upto` is exclusive, the offset the tail scans next (the cut's [`Burst::next`] or a mark's
    /// `next`), and a burst that delivered a record makes it the run's scan and the bridge's
    /// cursor. The group then resumes at the bound [`federation_commit_bound`] takes of the scan
    /// and the lowest record still held ([`Client::commit_before`](crate::client::Client::commit_before)):
    /// the island's `TlaPushEdge.Commit`. A run commits no bound it committed before, so a tail
    /// that only scans past its own commits moves nothing. What retention gave up is reported
    /// before any commit passes it (`TlaPushEdge.Gap`), so a stop between the two loses no word of
    /// it: the next run is told again.
    fn finish_burst(
        &mut self,
        burst: &mut Burst,
        held: &mut Held,
        upto: Offset,
        on_burst: &mut dyn FnMut(&FederationReport),
    ) -> Result<(), FederationError> {
        let mut taken = std::mem::take(burst);
        if !taken.gaps.is_empty() {
            let gap_report = FederationReport {
                held: held.count.saturating_add(held.past_count),
                committed_upto: held.committed(),
                next_cursor: self.cursor,
                gaps: std::mem::take(&mut taken.gaps),
                ..FederationReport::default()
            };
            let _ = Some(()).map(|()| on_burst(&gap_report));
        }
        if taken.fetched == 0 && held.is_empty() {
            return Ok(());
        }
        let mut refused = held.let_go(|subject| self.still_seated(subject));
        // The first of each origin's held records goes again, ahead of what is new; a new record
        // of an origin held waits behind it, unsent.
        let mut probed = std::collections::BTreeSet::new();
        let mut offered = held.probes();
        for rec in &offered {
            probed.insert(rec.producer_id);
        }
        for rec in taken.staged {
            if probed.contains(&rec.producer_id) || held.queues.contains_key(&rec.producer_id) {
                held.keep(rec);
            } else {
                offered.push(rec);
            }
        }
        let mut answered = Answers::default();
        loop {
            let answers = self.mirror_all(offered)?;
            answered.links.extend(answers.links);
            answered.deduped = answered.deduped.saturating_add(answers.deduped);
            refused = refused.saturating_add(answers.refused);
            let mut still = std::collections::BTreeSet::new();
            for rec in answers.unknown {
                if self.still_seated(&rec.subject) {
                    still.insert(rec.producer_id);
                    held.keep(rec);
                } else {
                    refused = refused.saturating_add(1);
                }
            }
            // An origin whose first record the destination took now: the rest of its go too.
            offered = probed
                .difference(&still)
                .flat_map(|id| held.release(*id))
                .collect();
            probed.clear();
            if offered.is_empty() {
                break;
            }
        }
        if taken.fetched > 0 {
            held.scanned = Some(upto);
            self.cursor = federation_cursor_advance(self.cursor, upto);
        }
        if let Some(scanned) = held.scanned {
            let bound = federation_commit_bound(scanned, held.lowest());
            if held.resumes.is_none_or(|last| bound > last) {
                if let Err(e) = self.src_ctl.commit_before(&self.cfg.group, bound) {
                    return Err(FederationError::Io(e));
                }
                held.resumes = Some(bound);
            }
        }
        let burst_report = FederationReport {
            fetched: taken.fetched,
            mirrored: answered.links.len(),
            deduped: answered.deduped,
            skipped: taken.skipped,
            refused,
            held: held.count.saturating_add(held.past_count),
            committed_upto: held.committed(),
            next_cursor: self.cursor,
            links: answered.links,
            gaps: Vec::new(),
        };
        let _ = Some(()).map(|()| on_burst(&burst_report));
        match held.past {
            Some(from) if held.queues.is_empty() => Err(FederationError::HeldBack { from }),
            _ => Ok(()),
        }
    }
}

/// What [`FederationBridge::mirror`] read back from `dest`.
#[derive(Default)]
struct Answers {
    /// The records `dest` appended or already held.
    links: Vec<FederationLink>,
    /// How many of `links` it already held.
    deduped: usize,
    /// Relayed records it refused for good.
    refused: usize,
    /// Relayed records whose origin it does not take now, in the order sent.
    unknown: Vec<Staged>,
}

/// What one [`FederationBridge::run`] keeps between its bursts. It ends with the run: the next
/// run's subscription resumes at or below the lowest record held, so it delivers each again.
#[derive(Default)]
struct Held {
    /// The records the destination did not take the origin of, by origin, each in source order:
    /// the first of each is offered again, the rest wait behind it.
    queues: std::collections::BTreeMap<u64, std::collections::VecDeque<Staged>>,
    /// How many records the queues keep, at most [`HELD_CAP`].
    count: usize,
    /// How many body bytes they keep, at most [`HELD_BYTES`].
    bytes: usize,
    /// The lowest record held by its offset alone, past either bound.
    past: Option<Offset>,
    /// How many records are held by offset alone.
    past_count: usize,
    /// The offset after the last record this run's bursts delivered.
    scanned: Option<Offset>,
    /// Where this run's last commit has the group resume.
    resumes: Option<Offset>,
}

impl Held {
    fn is_empty(&self) -> bool {
        self.queues.is_empty() && self.past.is_none()
    }

    /// The inclusive commit this run made last, if it made one.
    fn committed(&self) -> Option<Offset> {
        self.resumes.and_then(|next| next.checked_sub(1))
    }

    /// Keep `rec` behind its origin's earlier records, or by its offset alone past the bounds: a
    /// run keeps its first record whatever its size, so one body over [`HELD_BYTES`] is offered
    /// again rather than read again forever.
    fn keep(&mut self, rec: Staged) {
        let fits = self.count == 0
            || (self.count < HELD_CAP && self.bytes.saturating_add(rec.body.len()) <= HELD_BYTES);
        if self.past.is_some() || !fits {
            self.past = Some(self.past.map_or(rec.src_off, |past| past.min(rec.src_off)));
            self.past_count = self.past_count.saturating_add(1);
            return;
        }
        self.count = self.count.saturating_add(1);
        self.bytes = self.bytes.saturating_add(rec.body.len());
        let queue = self.queues.entry(rec.producer_id).or_default();
        // A record offered again goes back before the ones that waited behind it.
        if queue
            .front()
            .is_some_and(|first| first.src_off < rec.src_off)
        {
            queue.push_back(rec);
        } else {
            queue.push_front(rec);
        }
    }

    /// Take the first record of each origin's queue, to offer again.
    fn probes(&mut self) -> Vec<Staged> {
        let cap = self.queues.len();
        let mut probes = if cap <= 65_536 {
            Vec::with_capacity(cap)
        } else {
            Vec::new()
        };
        for queue in self.queues.values_mut() {
            if let Some(rec) = queue.pop_front() {
                self.count = self.count.saturating_sub(1);
                self.bytes = self.bytes.saturating_sub(rec.body.len());
                probes.push(rec);
            }
        }
        self.queues.retain(|_, queue| !queue.is_empty());
        probes
    }

    /// Take every record held of origin `id`.
    fn release(&mut self, id: u64) -> std::collections::VecDeque<Staged> {
        let queue = self.queues.remove(&id).unwrap_or_default();
        for rec in &queue {
            self.count = self.count.saturating_sub(1);
            self.bytes = self.bytes.saturating_sub(rec.body.len());
        }
        queue
    }

    /// Let go of every origin's records the source no longer seats, answering how many.
    fn let_go(&mut self, seated: impl Fn(&str) -> bool) -> usize {
        let gone: Vec<u64> = self
            .queues
            .iter()
            .filter(|(_, queue)| queue.front().is_some_and(|rec| !seated(&rec.subject)))
            .map(|(id, _)| *id)
            .collect();
        gone.into_iter().map(|id| self.release(id).len()).sum()
    }

    /// The lowest offset held, by body or by offset alone: [`Offset::MAX`] when none is.
    fn lowest(&self) -> Offset {
        self.queues
            .values()
            .filter_map(|queue| queue.front().map(|rec| rec.src_off))
            .chain(self.past)
            .min()
            .unwrap_or(Offset::MAX)
    }
}

/// A record staged for `dest`.
struct Staged {
    src_off: Offset,
    /// Its key on `dest`: `(cfg.producer_id, src_off)` for a mirror, its origin's for a relay.
    producer_id: u64,
    seq: u64,
    subject: String,
    body: Vec<u8>,
}

/// What [`FederationBridge::run`] gathered since its last commit.
#[derive(Default)]
struct Burst {
    staged: Vec<Staged>,
    fetched: usize,
    skipped: usize,
    /// The offset after the last record delivered.
    next: Offset,
    gaps: Vec<Gap>,
}

impl Burst {
    fn take(
        &mut self,
        bridge: &FederationBridge,
        src_off: Offset,
        origin: Option<(u64, u64)>,
        src_subj: String,
        body: Vec<u8>,
    ) -> Result<(), FederationError> {
        if src_off >= ACK_SEQ_BASE {
            return Err(FederationError::OffsetInReservedHalf(src_off));
        }
        self.fetched = self.fetched.saturating_add(1);
        self.next = src_off.saturating_add(1);
        if is_hidden_subject(&src_subj) || !bridge.carries(&src_subj) {
            self.skipped = self.skipped.saturating_add(1);
            return Ok(());
        }
        let dst_subj = match bridge.cfg.rewrite.apply(&src_subj) {
            Ok(Some(dst_subj)) => dst_subj,
            Ok(None) => {
                self.skipped = self.skipped.saturating_add(1);
                return Ok(());
            }
            Err(msg) => return Err(FederationError::Rewrite(msg)),
        };
        let (producer_id, seq) = if bridge.cfg.relay {
            let Some((id, seq)) = origin else {
                return Err(FederationError::Config(format!(
                    "the source broker delivered offset {src_off} without its origin"
                )));
            };
            if !relay_owns(&dst_subj, id) {
                self.skipped = self.skipped.saturating_add(1);
                return Ok(());
            }
            (id, seq)
        } else {
            let seq = federation_seq_clamp(src_off, ACK_SEQ_BASE.saturating_sub(1));
            (bridge.cfg.producer_id, seq)
        };
        self.staged.push(Staged {
            src_off,
            producer_id,
            seq,
            subject: dst_subj,
            body,
        });
        Ok(())
    }
}

/// Whether a record of `subject` from producer `id` is one a relay may carry: skipped here, it is
/// not sent to a destination that could only refuse it.
#[cfg(feature = "cap")]
fn relay_owns(subject: &str, id: u64) -> bool {
    astream_cap::relay_producer_of(subject) == Some(id)
}

/// A build without `cap` opens no relay bridge ([`FederationBridge::open`]).
#[cfg(not(feature = "cap"))]
const fn relay_owns(_subject: &str, _id: u64) -> bool {
    false
}

/// The owner a relayed record's subject names.
#[cfg(feature = "cap")]
fn relay_owner(subject: &str) -> Option<&str> {
    astream_cap::relay_owner(subject)
}

/// A build without `cap` relays nothing, so it holds nothing back.
#[cfg(not(feature = "cap"))]
const fn relay_owner(_subject: &str) -> Option<&str> {
    None
}

/// Stops a [`FederationBridge::run`] from another thread: it shuts the parked subscription, and
/// `run` returns `Ok(())`. Idempotent. Clones are handles on the one bridge.
#[derive(Clone, Debug, Default)]
pub struct FederationBridgeCloser {
    state: Arc<BridgeCloserState>,
}

#[derive(Debug, Default)]
struct BridgeCloserState {
    /// The caller's [`close`](FederationBridgeCloser::close): for good.
    closed: AtomicBool,
    /// This [`FederationRunner::run`] is over, because a sibling ended. The next one starts afresh.
    run_ended: AtomicBool,
    parked: Mutex<Option<Closer>>,
}

impl FederationBridgeCloser {
    /// End the bridge's `run`, now or as soon as it dials.
    pub fn close(&self) {
        self.state.closed.store(true, Ordering::Release);
        self.shut_parked();
    }

    /// Whether [`close`](Self::close) has been called.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.state.closed.load(Ordering::Acquire)
    }

    fn shut_parked(&self) {
        let parked = self
            .state
            .parked
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(closer) = parked.as_ref() {
            closer.close();
        }
    }

    /// End this runner's run of the bridge, leaving it free to run again.
    fn end_run(&self) {
        self.state.run_ended.store(true, Ordering::Release);
        self.shut_parked();
    }

    fn begin_run(&self) {
        self.state.run_ended.store(false, Ordering::Release);
    }

    /// Whether `run` was asked to end, rather than having lost its connection.
    fn stopping(&self) -> bool {
        self.is_closed() || self.state.run_ended.load(Ordering::Acquire)
    }

    /// Hold `closer` for a later stop; `false` if that stop already came, with `closer` shut.
    /// Under the lock, so a stop meets either its flag or this closer.
    fn park(&self, closer: Closer) -> bool {
        let mut parked = self
            .state
            .parked
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if self.stopping() {
            closer.close();
            return false;
        }
        *parked = Some(closer);
        true
    }

    /// Shut what is parked and let it go. A run that ended leaves no connection behind it: the
    /// source's tail would stay parked on it, holding a thread and a connection slot, until
    /// something else ended it.
    fn release(&self) {
        let parked = self
            .state
            .parked
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take();
        if let Some(closer) = parked {
            closer.close();
        }
    }
}

/// Releases a bridge's parked connection however its `run` ends, a panic in `on_burst` included.
struct ReleasedOnExit(FederationBridgeCloser);

impl Drop for ReleasedOnExit {
    fn drop(&mut self) {
        self.0.release();
    }
}

impl Drop for FederationBridge {
    fn drop(&mut self) {
        self.src_closer.close();
        self.dst_closer.close();
        self.closer.release();
    }
}

fn read_client_identity(
    client: &mut AnyClient,
    role: &'static str,
) -> Result<LogIdentity, FederationError> {
    if let Some(id) = client.seen_log_identity() {
        return Ok(id);
    }
    match client.log_identity() {
        Ok(Some(id)) => Ok(id),
        Ok(None) => Err(FederationError::MissingLogIdentity { role }),
        Err(e) => Err(FederationError::Io(e)),
    }
}

/// [`FederationConfig::carry`] parsed, each filter one that `filter` contains: a carried filter
/// `filter` did not contain would name records the group never scans.
fn carried_within(filter: &Filter, carry: &[String]) -> Result<Vec<Filter>, FederationError> {
    carry
        .iter()
        .map(|raw| match Filter::new(raw) {
            Ok(f) if filter.contains(&f) => Ok(f),
            Ok(_) => Err(FederationError::Config(format!(
                "carry filter {raw:?} is not within filter {:?}",
                filter.as_str()
            ))),
            Err(_) => Err(FederationError::Config(format!(
                "carry filter {raw:?} is not a valid Filter"
            ))),
        })
        .collect()
}

fn bootstrap_group_cursor(
    source: &FederationEndpoint,
    group: &str,
    filter: &str,
) -> Result<Offset, FederationError> {
    let (client, closer) = match source.dial() {
        Ok(pair) => pair,
        Err(e) => return Err(FederationError::Io(e)),
    };
    let mut sub = match client.subscribe_group(group, filter) {
        Ok(s) => s,
        Err(e) => {
            closer.close();
            return Err(FederationError::Io(e));
        }
    };
    let mut resolved: Option<Offset> = None;
    let mut rounds = 0usize;
    while rounds < 16 {
        rounds = rounds.saturating_add(1);
        match sub.recv_event() {
            Ok(Some(Event::Delivery { offset, .. })) => {
                resolved = Some(offset);
                break;
            }
            Ok(Some(Event::Mark { head, .. })) => {
                resolved = Some(head);
                break;
            }
            Ok(Some(Event::Gap(_))) => {}
            Ok(None) => {
                closer.close();
                return Err(FederationError::Io(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "source broker closed subscription before catch-up mark",
                )));
            }
            Err(e) => {
                closer.close();
                return Err(FederationError::Io(e));
            }
        }
    }
    closer.close();
    match resolved {
        Some(off) => Ok(off),
        None => Err(FederationError::Io(io::Error::other(
            "exceeded gap-notice rounds while bootstrapping federation group cursor",
        ))),
    }
}

/// Cross-broker Chandy-Lamport consistent cut mapping each broker [`LogIdentity`] in a
/// federated fleet to its frontier [`Offset`].
///
/// Wraps [`astream_wire::CausalCut<LogIdentity>`] and evaluates causal consistency,
/// violation witnesses, minimal causal closure (`heal`), and lattice `join`/`meet` over
/// [`FederationLink`] receipts, plus canonical `<id>.<gen>=<offset>` text persistence.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FederatedCut {
    inner: CausalCut<LogIdentity>,
}

impl FederatedCut {
    /// An empty cross-broker cut admitting no broker logs.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            inner: CausalCut::new(),
        }
    }

    /// Number of broker logs represented in this cut.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Whether the cut tracks zero broker logs.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Query the frontier offset recorded for `log` (`None` if `log` is absent).
    #[must_use]
    pub fn frontier(&self, log: &LogIdentity) -> Option<Offset> {
        match self.inner.offset_of(log) {
            Some(off) => Some(off.0),
            None => None,
        }
    }

    /// Set `log`'s frontier to `offset`.
    pub fn insert(&mut self, log: LogIdentity, offset: Offset) {
        self.inner.set(log, WireOffset(offset));
    }

    /// Monotonically advance `log`'s frontier to `max(current, offset)`.
    pub fn advance(&mut self, log: LogIdentity, offset: Offset) {
        self.inner.advance(log, WireOffset(offset));
    }

    /// Borrow the underlying [`CausalCut<LogIdentity>`].
    #[must_use]
    pub const fn as_causal_cut(&self) -> &CausalCut<LogIdentity> {
        &self.inner
    }

    /// Decide Chandy-Lamport consistency across `links`: for every mirrored record whose
    /// `dst_offset` lies within `self.frontier(&dst_log)`, `self.frontier(&src_log)` must
    /// exist and be `>= src_offset`.
    #[must_use]
    pub fn is_consistent(&self, links: &[FederationLink]) -> bool {
        let edges = collect_edges(links);
        self.inner.is_consistent(&edges)
    }

    /// Return the first cross-broker [`CutViolation<LogIdentity>`] witnessed by `links`,
    /// or `None` if this cut is causally consistent.
    #[must_use]
    pub fn first_violation(&self, links: &[FederationLink]) -> Option<CutViolation<LogIdentity>> {
        let edges = collect_edges(links);
        self.inner.first_violation(&edges)
    }

    /// Advance lagging source broker frontiers to the minimal Chandy-Lamport consistent
    /// closure containing `self` with respect to `links`, returning the number of frontier
    /// updates performed.
    pub fn heal(&mut self, links: &[FederationLink]) -> usize {
        let edges = collect_edges(links);
        self.inner.heal(&edges)
    }

    /// Pointwise least upper bound (`max`) of two federated cuts.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            inner: self.inner.join(&other.inner),
        }
    }

    /// Pointwise greatest lower bound (`min` over shared logs) of two federated cuts.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        Self {
            inner: self.inner.meet(&other.inner),
        }
    }

    /// Whether `self` includes every broker log in `other` at an equal or greater frontier.
    #[must_use]
    pub fn dominates(&self, other: &Self) -> bool {
        self.inner.dominates(&other.inner)
    }

    /// Canonical deterministic `<32hex>.<generation>=<offset>\n` text encoding (sorted by
    /// [`LogIdentity`]), suitable for fabric control messages or sidecar persistence.
    #[must_use]
    pub fn encode_text(&self) -> String {
        let mut out = String::new();
        for (log, off) in self.inner.iter() {
            let off_val = off.0;
            out.push_str(&format!("{log}={off_val}\n"));
        }
        out
    }

    /// Decode a canonical `<32hex>.<generation>=<offset>` text cut, rejecting malformed
    /// identities, duplicate log entries, or non-integer offsets fail-closed.
    pub fn decode_text(text: &str) -> Result<Self, String> {
        const MAX_CUT_ENTRIES: usize = 4096;
        let mut cut = Self::new();
        for raw_line in text.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if cut.len() >= MAX_CUT_ENTRIES {
                return Err(format!(
                    "federated cut exceeds MAX_CUT_ENTRIES ({MAX_CUT_ENTRIES})"
                ));
            }
            let Some((id_str, off_str)) = line.split_once('=') else {
                return Err(format!(
                    "malformed federated cut line {line:?}: missing '='"
                ));
            };
            let Some(log) = LogIdentity::parse(id_str.trim()) else {
                return Err(format!(
                    "invalid LogIdentity {:?} in federated cut",
                    id_str.trim()
                ));
            };
            let off = match off_str.trim().parse::<u64>() {
                Ok(v) => v,
                Err(_) => {
                    return Err(format!(
                        "invalid offset {:?} for {log} in federated cut",
                        off_str.trim()
                    ));
                }
            };
            if cut.frontier(&log).is_some() {
                return Err(format!("duplicate LogIdentity {log} in federated cut"));
            }
            cut.insert(log, off);
        }
        Ok(cut)
    }
}

fn collect_edges(links: &[FederationLink]) -> Vec<CausalEdge<LogIdentity>> {
    const MAX_LINKS: usize = 65_536;
    let cap = links.len().min(MAX_LINKS);
    let mut out = Vec::with_capacity(cap);
    for link in links {
        out.push(link.causal_edge());
    }
    out
}

/// Maximum number of subtree rules in a single [`FederationRunner`] or `--rules-file`.
pub const MAX_FEDERATION_RULES: usize = 64;

/// Default batch size per rule in [`FederationRule`] (`128`, bounded by `256`).
pub const DEFAULT_FEDERATION_BATCH: usize = 128;

/// Declarative per-subtree federation rule parsed by [`parse_federation_rules`] and executed
/// by [`FederationRunner`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FederationRule {
    /// Durable consumer-group name on `source` (must be a valid non-reserved `Subject`).
    pub group: String,
    /// Subscription [`Filter`] selecting records on `source`.
    pub filter: String,
    /// Subject prefix transformation and loop-prevention policy.
    pub rewrite: SubjectRewrite,
    /// Optional per-rule override for `producer_id` on `dest` (`None` inherits runner default).
    pub producer_id: Option<u64>,
    /// Maximum batch size per `sync_once` tick (`1..=256`).
    pub batch_size: usize,
}

/// Parse a `<strip>=><add>` or `passthrough` rewrite specification into [`SubjectRewrite`].
pub fn parse_rewrite_spec(spec: &str) -> Result<SubjectRewrite, String> {
    if spec == "passthrough" {
        return Ok(SubjectRewrite::passthrough());
    }
    let Some((strip, add)) = spec.split_once("=>") else {
        return Err(format!(
            "rewrite {:?} must be `passthrough` or `<strip_prefix>=><add_prefix>`",
            spec
        ));
    };
    SubjectRewrite::prefix_map(strip, add)
}

/// Parse a declarative multi-link federation ruleset (`#` comments and blank lines skipped).
///
/// Line grammar (`key=value` whitespace-separated tokens):
/// `group=<subject> filter=<filter> [rewrite=passthrough|<strip>=><add>] [exclude=<p1,p2>] [hops=<cur>/<max>] [id=<u64>] [batch=<1..=256>]`
pub fn parse_federation_rules(text: &str) -> Result<Vec<FederationRule>, String> {
    let mut rules: Vec<FederationRule> = Vec::new();
    let mut line_no = 0usize;

    for raw_line in text.lines() {
        line_no = line_no.saturating_add(1);
        let trimmed = raw_line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if rules.len() >= MAX_FEDERATION_RULES {
            return Err(format!(
                "line {line_no}: exceeds MAX_FEDERATION_RULES ({MAX_FEDERATION_RULES})"
            ));
        }

        let mut group: Option<String> = None;
        let mut filter: Option<String> = None;
        let mut rewrite: Option<SubjectRewrite> = None;
        let mut excludes: Vec<String> = Vec::new();
        let mut hop_pair: Option<(u8, u8)> = None;
        let mut producer_id: Option<u64> = None;
        let mut batch_size: Option<usize> = None;

        for tok in trimmed.split_ascii_whitespace() {
            let Some((key, val)) = tok.split_once('=') else {
                return Err(format!(
                    "line {line_no}: expected `key=value` token, got {tok:?}"
                ));
            };
            if val.is_empty() && key != "rewrite" {
                return Err(format!("line {line_no}: empty value for `{key}=`"));
            }
            if key == "group" {
                if group.is_some() {
                    return Err(format!("line {line_no}: duplicate `group=`"));
                }
                if Subject::new(val).is_err() || is_hidden_subject(val) {
                    return Err(format!(
                        "line {line_no}: group {val:?} must be a valid non-reserved Subject"
                    ));
                }
                group = Some(val.to_string());
            } else if key == "filter" {
                if filter.is_some() {
                    return Err(format!("line {line_no}: duplicate `filter=`"));
                }
                if Filter::new(val).is_err() {
                    return Err(format!(
                        "line {line_no}: filter {val:?} is not a valid Filter"
                    ));
                }
                filter = Some(val.to_string());
            } else if key == "rewrite" {
                if rewrite.is_some() {
                    return Err(format!("line {line_no}: duplicate `rewrite=`"));
                }
                let parsed = match parse_rewrite_spec(val) {
                    Ok(rw) => rw,
                    Err(msg) => return Err(format!("line {line_no}: {msg}")),
                };
                rewrite = Some(parsed);
            } else if key == "exclude" {
                for item in val.split(',') {
                    if item.is_empty() {
                        return Err(format!("line {line_no}: empty prefix in `exclude={val}`"));
                    }
                    excludes.push(item.to_string());
                }
            } else if key == "hops" {
                if hop_pair.is_some() {
                    return Err(format!("line {line_no}: duplicate `hops=`"));
                }
                let Some((cur_s, max_s)) = val.split_once('/') else {
                    return Err(format!(
                        "line {line_no}: `hops={val}` must be `<cur>/<max>`"
                    ));
                };
                let Ok(cur_h) = cur_s.parse::<u8>() else {
                    return Err(format!("line {line_no}: invalid hop count {cur_s:?}"));
                };
                let Ok(max_h) = max_s.parse::<u8>() else {
                    return Err(format!("line {line_no}: invalid max_hops {max_s:?}"));
                };
                hop_pair = Some((cur_h, max_h));
            } else if key == "id" || key == "producer_id" {
                if producer_id.is_some() {
                    return Err(format!("line {line_no}: duplicate `{key}=`"));
                }
                let Ok(pid) = val.parse::<u64>() else {
                    return Err(format!(
                        "line {line_no}: `{key}={val}` expects an unsigned 64-bit integer"
                    ));
                };
                producer_id = Some(pid);
            } else if key == "batch" {
                if batch_size.is_some() {
                    return Err(format!("line {line_no}: duplicate `batch=`"));
                }
                let Ok(bsz) = val.parse::<usize>() else {
                    return Err(format!("line {line_no}: invalid `batch={val}`"));
                };
                if bsz == 0 || bsz > FEDERATION_BATCH_CAP {
                    return Err(format!(
                        "line {line_no}: `batch={bsz}` must be in 1..={FEDERATION_BATCH_CAP}"
                    ));
                }
                batch_size = Some(bsz);
            } else {
                return Err(format!("line {line_no}: unknown rule key {key:?}"));
            }
        }

        let Some(group_val) = group else {
            return Err(format!(
                "line {line_no}: missing required `group=<subject>`"
            ));
        };
        let Some(filter_val) = filter else {
            return Err(format!(
                "line {line_no}: missing required `filter=<filter>`"
            ));
        };
        for existing in &rules {
            if existing.group == group_val {
                return Err(format!(
                    "line {line_no}: duplicate consumer group {group_val:?} across rules"
                ));
            }
        }

        let mut rw = match rewrite {
            Some(r) => r,
            None => SubjectRewrite::passthrough(),
        };
        for ex in &excludes {
            rw = match rw.with_excluded_prefix(ex) {
                Ok(next) => next,
                Err(msg) => return Err(format!("line {line_no}: {msg}")),
            };
        }
        if let Some((cur_h, max_h)) = hop_pair {
            rw = rw.with_hop_budget(cur_h, max_h);
        }

        rules.push(FederationRule {
            group: group_val,
            filter: filter_val,
            rewrite: rw,
            producer_id,
            batch_size: batch_size.unwrap_or(DEFAULT_FEDERATION_BATCH),
        });
    }

    if rules.is_empty() {
        return Err("federation rules file holds no rules".to_string());
    }
    Ok(rules)
}

/// Ends a [`FederationRunner::run`] when one of its bridges ends, however it ended.
struct EndsTheRun(FederationRunnerCloser);

impl Drop for EndsTheRun {
    fn drop(&mut self) {
        for bridge in &self.0.bridges {
            bridge.end_run();
        }
    }
}

/// Thread-safe cooperative stop handle for [`FederationRunner`].
#[derive(Clone, Debug)]
pub struct FederationRunnerCloser {
    stopped: Arc<AtomicBool>,
    bridges: Vec<FederationBridgeCloser>,
}

impl FederationRunnerCloser {
    /// Signal the [`FederationRunner`] to stop before its next rule step, and end its
    /// [`run`](FederationRunner::run).
    pub fn close(&self) {
        self.stopped.store(true, Ordering::Release);
        for bridge in &self.bridges {
            bridge.close();
        }
    }

    /// Whether [`Self::close`] has been invoked.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.stopped.load(Ordering::Acquire)
    }
}

/// Multi-link cross-broker federation coordinator managing `1..=64` [`FederationBridge`]
/// instances between a source and destination [`FederationEndpoint`].
pub struct FederationRunner {
    rules: Vec<FederationRule>,
    bridges: Vec<FederationBridge>,
    src_log: LogIdentity,
    dst_log: LogIdentity,
    stopped: Arc<AtomicBool>,
}

impl FederationRunner {
    /// Validate `rules`, open a [`FederationBridge`] per rule, and verify all rules agree on
    /// the pinned `(src_log, dst_log)` [`LogIdentity`] pair.
    pub fn open(
        source: FederationEndpoint,
        dest: FederationEndpoint,
        default_producer_id: u64,
        rules: Vec<FederationRule>,
    ) -> Result<Self, FederationError> {
        if rules.is_empty() {
            return Err(FederationError::Config(
                "FederationRunner requires at least one FederationRule".to_string(),
            ));
        }
        if rules.len() > MAX_FEDERATION_RULES {
            return Err(FederationError::Config(format!(
                "FederationRunner rules ({}) exceed MAX_FEDERATION_RULES ({MAX_FEDERATION_RULES})",
                rules.len()
            )));
        }
        let mut bridges: Vec<FederationBridge> =
            Vec::with_capacity(rules.len().min(MAX_FEDERATION_RULES));
        let mut pinned_pair: Option<(LogIdentity, LogIdentity)> = None;

        for rule in &rules {
            let cfg = FederationConfig {
                source: source.clone(),
                dest: dest.clone(),
                group: rule.group.clone(),
                filter: rule.filter.clone(),
                carry: Vec::new(),
                producer_id: rule.producer_id.unwrap_or(default_producer_id),
                rewrite: rule.rewrite.clone(),
                relay: false,
            };
            let bridge = FederationBridge::open(cfg)?;
            let s_id = bridge.source_identity();
            let d_id = bridge.dest_identity();
            match pinned_pair {
                None => pinned_pair = Some((s_id, d_id)),
                Some((exp_s, exp_d)) => {
                    if s_id != exp_s {
                        return Err(FederationError::SourceLogDiverged {
                            expected: exp_s,
                            found: s_id,
                            cursor: bridge.cursor(),
                        });
                    }
                    if d_id != exp_d {
                        return Err(FederationError::DestLogChanged {
                            expected: exp_d,
                            found: d_id,
                        });
                    }
                }
            }
            bridges.push(bridge);
        }

        let Some((src_log, dst_log)) = pinned_pair else {
            return Err(FederationError::Config(
                "FederationRunner opened zero bridges".to_string(),
            ));
        };

        Ok(Self {
            rules,
            bridges,
            src_log,
            dst_log,
            stopped: Arc::new(AtomicBool::new(false)),
        })
    }

    /// Return a thread-safe handle that stops [`run`](Self::run) cleanly.
    #[must_use]
    pub fn closer(&self) -> FederationRunnerCloser {
        FederationRunnerCloser {
            stopped: Arc::clone(&self.stopped),
            bridges: self.bridges.iter().map(FederationBridge::closer).collect(),
        }
    }

    /// Whether [`FederationRunnerCloser::close`] has been signaled.
    #[must_use]
    pub fn is_stopped(&self) -> bool {
        self.stopped.load(Ordering::Acquire)
    }

    /// Pinned [`LogIdentity`] of the source broker.
    #[must_use]
    pub const fn source_identity(&self) -> LogIdentity {
        self.src_log
    }

    /// Pinned [`LogIdentity`] of the destination broker.
    #[must_use]
    pub const fn dest_identity(&self) -> LogIdentity {
        self.dst_log
    }

    /// Number of active [`FederationRule`] bridges.
    #[must_use]
    pub fn rule_count(&self) -> usize {
        self.rules.len()
    }

    /// Configured [`FederationRule`] slice.
    #[must_use]
    pub fn rules(&self) -> &[FederationRule] {
        &self.rules
    }

    /// Reconnect all underlying [`FederationBridge`] instances, verifying [`LogIdentity`]
    /// lineage continuity across every rule cursor.
    pub fn reconnect_all(&mut self) -> Result<(), FederationError> {
        for bridge in &mut self.bridges {
            bridge.reconnect()?;
            self.src_log = bridge.source_identity();
        }
        Ok(())
    }

    /// Step every configured bridge once (`rule.batch_size` records max per rule), returning
    /// `(group, report)` in rule declaration order.
    pub fn sync_all_once(&mut self) -> Result<Vec<(String, FederationReport)>, FederationError> {
        let mut out = Vec::with_capacity(self.rules.len().min(MAX_FEDERATION_RULES));
        let mut idx = 0usize;
        while idx < self.bridges.len() {
            if self.is_stopped() {
                break;
            }
            let Some(rule) = self.rules.get(idx) else {
                break;
            };
            let Some(bridge) = self.bridges.get_mut(idx) else {
                break;
            };
            let rep = bridge.sync_once(rule.batch_size)?;
            out.push((rule.group.clone(), rep));
            idx = idx.saturating_add(1);
        }
        Ok(out)
    }

    /// Drain every configured bridge for up to `max_rounds` (`1..=4096`) rounds per rule until
    /// caught up (`fetched == 0`), returning one aggregated [`FederationReport`] per rule.
    pub fn drain_until_caught_up(
        &mut self,
        max_rounds: usize,
    ) -> Result<Vec<(String, FederationReport)>, FederationError> {
        let round_cap = max_rounds.clamp(1, 4096);
        let mut out = Vec::with_capacity(self.rules.len().min(MAX_FEDERATION_RULES));
        let mut idx = 0usize;
        while idx < self.bridges.len() {
            if self.is_stopped() {
                break;
            }
            let Some(rule) = self.rules.get(idx) else {
                break;
            };
            let Some(bridge) = self.bridges.get_mut(idx) else {
                break;
            };
            let mut agg = FederationReport {
                next_cursor: bridge.cursor(),
                ..FederationReport::default()
            };
            let mut round = 0usize;
            while round < round_cap {
                if self.stopped.load(Ordering::Acquire) {
                    break;
                }
                let step = bridge.sync_once(rule.batch_size)?;
                let step_fetched = step.fetched;
                agg.fetched = agg.fetched.saturating_add(step.fetched);
                agg.mirrored = agg.mirrored.saturating_add(step.mirrored);
                agg.deduped = agg.deduped.saturating_add(step.deduped);
                agg.skipped = agg.skipped.saturating_add(step.skipped);
                if let Some(upto) = step.committed_upto {
                    agg.committed_upto = Some(match agg.committed_upto {
                        Some(prev) => federation_cursor_advance(prev, upto),
                        None => upto,
                    });
                }
                agg.next_cursor = federation_cursor_advance(agg.next_cursor, step.next_cursor);
                agg.links.extend(step.links);
                round = round.saturating_add(1);
                if step_fetched == 0 {
                    break;
                }
            }
            out.push((rule.group.clone(), agg));
            idx = idx.saturating_add(1);
        }
        Ok(out)
    }

    /// Run every bridge by push ([`FederationBridge::run`]), one thread per rule, until
    /// [`FederationRunnerCloser::close`] or the first failure, which ends the others and is
    /// returned. Each bridge's own ending ends this run, a panic in `on_burst` included, and leaves
    /// the runner free to [`reconnect_all`](Self::reconnect_all) and run again; only the closer's
    /// `close` is for good. `on_burst` sees `(group, report)`, from those threads.
    pub fn run(
        &mut self,
        on_burst: &(impl Fn(&str, &FederationReport) + Sync + ?Sized),
    ) -> Result<(), FederationError> {
        let closer = self.closer();
        for bridge in &closer.bridges {
            bridge.begin_run();
        }
        let rules = &self.rules;
        let bridges = &mut self.bridges;
        std::thread::scope(|scope| {
            let mut running = Vec::with_capacity(bridges.len().min(MAX_FEDERATION_RULES));
            for (rule, bridge) in rules.iter().zip(bridges.iter_mut()) {
                let closer = closer.clone();
                running.push(scope.spawn(move || {
                    let _ends_the_run = EndsTheRun(closer);
                    bridge.run(rule.batch_size, &mut |report| {
                        on_burst(&rule.group, report);
                    })
                }));
            }
            let mut first = Ok(());
            for thread in running {
                match thread.join() {
                    Ok(Err(e)) if first.is_ok() => first = Err(e),
                    Err(panicked) => std::panic::resume_unwind(panicked),
                    _ => {}
                }
            }
            first
        })
    }

    /// Record all [`FederationReport`] cursors and [`FederationLink`] provenance receipts into
    /// `cut`, then heal `cut` so it forms a Chandy-Lamport consistent cross-broker cut.
    pub fn record_into_cut(&self, reports: &[(String, FederationReport)], cut: &mut FederatedCut) {
        for (_group, rep) in reports {
            Self::record_report(self.src_log, rep, cut);
        }
    }

    /// [`record_into_cut`](Self::record_into_cut) for the one report of `src_log`'s bridge that
    /// a [`run`](Self::run) burst hands over.
    pub fn record_report(src_log: LogIdentity, rep: &FederationReport, cut: &mut FederatedCut) {
        if rep.next_cursor > 0 {
            cut.advance(src_log, rep.next_cursor);
        }
        for link in &rep.links {
            cut.advance(link.src_log, link.src_offset.saturating_add(1));
            cut.advance(link.dst_log, link.dst_offset.saturating_add(1));
        }
        if !rep.links.is_empty() {
            let _ = cut.heal(&rep.links);
        }
    }
}

/// Maximum federated peer endpoints tracked by [`FederationMesh`].
pub const MAX_FEDERATION_PEERS: usize = 128;

/// Maximum distinct remote regions routed by [`FederationMesh`].
pub const MAX_FEDERATION_REGIONS: usize = 64;

/// Maximum exported subject prefixes per [`PeerAdvertisement`].
pub const MAX_PEER_EXPORT_PREFIXES: usize = 16;

/// Maximum smoothed RTT sample cap (`10_000_000` us = 10 seconds) enforced via
/// [`federation_seq_clamp`].
pub const MAX_FEDERATION_RTT_US: u64 = 10_000_000;

/// Default EWMA hysteresis margin (`2_000` us = 2 ms) required before switching an
/// already-healthy regional gateway to a lower-RTT candidate.
pub const DEFAULT_ROUTE_HYSTERESIS_US: u64 = 2_000;

/// Default retained registry prefix (`"/f/fed/peers"`) used by [`FederationDirectory`]
/// for dynamic peer discovery across seed brokers.
pub const DEFAULT_PEER_REGISTRY_PREFIX: &str = "/f/fed/peers";

contract_fn! {
    /// Verified check that a candidate gateway's hysteresis-padded RTT threshold
    /// (`cand_srtt_us + hysteresis_us`) beats or ties the active gateway's `cur_rtt_us`
    /// (`switch_threshold_us <= cur_rtt_us`), linked via `clean-kernel-defeq` to
    /// `federation_route_preferred_isl`.
    #[must_use]
    pub const fn federation_route_preferred(cur_rtt_us: u64, switch_threshold_us: u64) -> bool
    clauses [ensures result == (switch_threshold_us <= cur_rtt_us)]
    {
        switch_threshold_us <= cur_rtt_us
    }
}

contract_fn! {
    /// Verified check that an observed SWIM peer incarnation meets or exceeds `min_inc`
    /// (`min_inc <= observed_inc`), linked via `clean-kernel-defeq` to
    /// `federation_incarnation_fresh_isl`.
    #[must_use]
    pub const fn federation_incarnation_fresh(observed_inc: u64, min_inc: u64) -> bool
    clauses [ensures result == (min_inc <= observed_inc)]
    {
        min_inc <= observed_inc
    }
}

/// SWIM-style membership health state advertised or observed for a peer in [`FederationMesh`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PeerHealthState {
    /// Healthy gateway eligible for primary multi-region routing.
    Alive,
    /// Probe failure or gossip suspicion; bypassed when an [`PeerHealthState::Alive`] gateway exists.
    Suspect,
    /// Graceful operator drain; bypassed immediately so traffic shifts cleanly before shutdown.
    Draining,
    /// Tombstoned at this incarnation until superseded by a strictly higher incarnation.
    Dead,
}

impl PeerHealthState {
    /// Canonical lowercase token used in [`PeerAdvertisement::encode_text`].
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            PeerHealthState::Alive => "alive",
            PeerHealthState::Suspect => "suspect",
            PeerHealthState::Draining => "draining",
            PeerHealthState::Dead => "dead",
        }
    }

    /// Parse a canonical [`PeerHealthState`] token.
    pub fn parse(token: &str) -> Result<Self, String> {
        match token {
            "alive" => Ok(PeerHealthState::Alive),
            "suspect" => Ok(PeerHealthState::Suspect),
            "draining" => Ok(PeerHealthState::Draining),
            "dead" => Ok(PeerHealthState::Dead),
            _ => Err(format!("invalid peer state {token:?}")),
        }
    }

    const fn degradation_rank(self) -> u8 {
        match self {
            PeerHealthState::Alive => 0,
            PeerHealthState::Suspect => 1,
            PeerHealthState::Draining => 2,
            PeerHealthState::Dead => 3,
        }
    }
}

/// Wire-advertisable transport kind in [`PeerAdvertisement`] (secrets and keys never travel
/// inside gossip advertisements; authenticated wire wrappers are attached locally via
/// [`FederationMeshConfig`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PeerTransportKind {
    /// Local Unix-domain socket path (`Transport::Unix`).
    Unix,
    /// TCP `host:port` endpoint (`Transport::Tcp`, or upgraded locally by mesh policy).
    Tcp,
}

impl PeerTransportKind {
    /// Canonical lowercase token used in [`PeerAdvertisement::encode_text`].
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            PeerTransportKind::Unix => "unix",
            PeerTransportKind::Tcp => "tcp",
        }
    }

    /// Parse a canonical [`PeerTransportKind`] token.
    pub fn parse(token: &str) -> Result<Self, String> {
        match token {
            "unix" => Ok(PeerTransportKind::Unix),
            "tcp" => Ok(PeerTransportKind::Tcp),
            _ => Err(format!("invalid peer transport {token:?}")),
        }
    }
}

fn validate_mesh_segment(seg: &str, field: &str) -> Result<(), String> {
    if seg.is_empty() || seg.contains('/') {
        return Err(format!(
            "{field} {seg:?} must be a non-empty single subject segment without '/'"
        ));
    }
    let probe = format!("/g/{seg}");
    if Subject::new(&probe).is_err() {
        return Err(format!(
            "{field} {seg:?} is not a valid astream Subject segment"
        ));
    }
    Ok(())
}

fn validate_endpoint_token(endpoint: &str) -> Result<(), String> {
    if endpoint.is_empty() {
        return Err("peer endpoint must not be empty".to_string());
    }
    let mut bytes = endpoint.as_bytes();
    while let &[b, ref rest @ ..] = bytes {
        if b <= b' ' || b == 0x7f {
            return Err(format!(
                "peer endpoint {endpoint:?} must not contain whitespace or ASCII control bytes"
            ));
        }
        bytes = rest;
    }
    Ok(())
}

/// Dynamic peer-discovery record published onto seed registry brokers under
/// `"{registry_prefix}/{peer_id}"` (`DEFAULT_PEER_REGISTRY_PREFIX`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeerAdvertisement {
    /// Unique single-segment peer identifier (e.g. `"us-east-gw1"`).
    pub peer_id: String,
    /// Single-segment region identifier (e.g. `"us-east"`, `"eu-west"`).
    pub region: String,
    /// Socket path (`PeerTransportKind::Unix`) or `host:port` (`PeerTransportKind::Tcp`).
    pub endpoint: String,
    /// Advertised base transport kind (credentials/keys stay out of gossip).
    pub transport_kind: PeerTransportKind,
    /// Monotone SWIM incarnation number (`0..=u64::MAX`).
    pub incarnation: u64,
    /// Advertised [`PeerHealthState`].
    pub state: PeerHealthState,
    /// Validated subject prefixes exported by this peer (`0..=MAX_PEER_EXPORT_PREFIXES`).
    pub export_prefixes: Vec<String>,
}

impl PeerAdvertisement {
    /// Construct and validate a [`PeerAdvertisement`].
    pub fn new(
        peer_id: &str,
        region: &str,
        endpoint: &str,
        transport_kind: PeerTransportKind,
        incarnation: u64,
        state: PeerHealthState,
        export_prefixes: Vec<String>,
    ) -> Result<Self, String> {
        let ad = Self {
            peer_id: peer_id.to_string(),
            region: region.to_string(),
            endpoint: endpoint.to_string(),
            transport_kind,
            incarnation,
            state,
            export_prefixes,
        };
        ad.validate()?;
        Ok(ad)
    }

    /// Validate segment grammar, endpoint safety, and exported subject prefixes.
    pub fn validate(&self) -> Result<(), String> {
        validate_mesh_segment(&self.peer_id, "peer_id")?;
        validate_mesh_segment(&self.region, "region")?;
        validate_endpoint_token(&self.endpoint)?;
        if self.export_prefixes.len() > MAX_PEER_EXPORT_PREFIXES {
            return Err(format!(
                "export_prefixes count ({}) exceeds MAX_PEER_EXPORT_PREFIXES ({MAX_PEER_EXPORT_PREFIXES})",
                self.export_prefixes.len()
            ));
        }
        let mut i = 0usize;
        while i < self.export_prefixes.len() {
            if let Some(pfx) = self.export_prefixes.get(i) {
                validate_prefix_shape(pfx, "export_prefix")?;
                let mut j = 0usize;
                while j < i {
                    if let Some(prev) = self.export_prefixes.get(j) {
                        if prev == pfx {
                            return Err(format!("duplicate export_prefix {pfx:?}"));
                        }
                    }
                    j = j.saturating_add(1);
                }
            }
            i = i.saturating_add(1);
        }
        Ok(())
    }

    /// Registry subject (`"{registry_prefix}/{peer_id}"`) under which this peer advertises.
    pub fn registry_subject(&self, registry_prefix: &str) -> Result<String, String> {
        validate_prefix_shape(registry_prefix, "registry_prefix")?;
        validate_mesh_segment(&self.peer_id, "peer_id")?;
        let subj = format!("{registry_prefix}/{}", self.peer_id);
        if Subject::new(&subj).is_err() {
            return Err(format!("invalid registry subject {subj:?}"));
        }
        Ok(subj)
    }

    /// Canonical deterministic text wire representation (`v=1 ...`) containing zero secrets.
    #[must_use]
    pub fn encode_text(&self) -> String {
        let mut exports = String::new();
        let mut idx = 0usize;
        while idx < self.export_prefixes.len() {
            if let Some(pfx) = self.export_prefixes.get(idx) {
                if idx > 0 {
                    exports.push(',');
                }
                exports.push_str(pfx);
            }
            idx = idx.saturating_add(1);
        }
        if exports.is_empty() {
            exports.push('-');
        }
        format!(
            "v=1 peer={} region={} transport={} endpoint={} incarnation={} state={} exports={exports}\n",
            self.peer_id,
            self.region,
            self.transport_kind.as_str(),
            self.endpoint,
            self.incarnation,
            self.state.as_str()
        )
    }

    /// Fail-closed parser for [`Self::encode_text`] payloads.
    pub fn decode_text(text: &str) -> Result<Self, String> {
        let trimmed = text.trim();
        if trimmed.is_empty() {
            return Err("empty peer advertisement".to_string());
        }
        let mut version_ok = false;
        let mut peer_id: Option<String> = None;
        let mut region: Option<String> = None;
        let mut transport_kind: Option<PeerTransportKind> = None;
        let mut endpoint: Option<String> = None;
        let mut incarnation: Option<u64> = None;
        let mut state: Option<PeerHealthState> = None;
        let mut exports: Option<Vec<String>> = None;

        for tok in trimmed.split_whitespace() {
            let Some((key, val)) = tok.split_once('=') else {
                return Err(format!("malformed peer advertisement token {tok:?}"));
            };
            if key == "v" {
                if val != "1" {
                    return Err(format!("unsupported peer advertisement version {val:?}"));
                }
                version_ok = true;
            } else if key == "peer" {
                if peer_id.is_some() {
                    return Err("duplicate `peer=` key".to_string());
                }
                peer_id = Some(val.to_string());
            } else if key == "region" {
                if region.is_some() {
                    return Err("duplicate `region=` key".to_string());
                }
                region = Some(val.to_string());
            } else if key == "transport" {
                if transport_kind.is_some() {
                    return Err("duplicate `transport=` key".to_string());
                }
                transport_kind = Some(PeerTransportKind::parse(val)?);
            } else if key == "endpoint" {
                if endpoint.is_some() {
                    return Err("duplicate `endpoint=` key".to_string());
                }
                endpoint = Some(val.to_string());
            } else if key == "incarnation" {
                if incarnation.is_some() {
                    return Err("duplicate `incarnation=` key".to_string());
                }
                let parsed = match val.parse::<u64>() {
                    Ok(v) => v,
                    Err(_) => return Err(format!("invalid incarnation {val:?}")),
                };
                incarnation = Some(parsed);
            } else if key == "state" {
                if state.is_some() {
                    return Err("duplicate `state=` key".to_string());
                }
                state = Some(PeerHealthState::parse(val)?);
            } else if key == "exports" {
                if exports.is_some() {
                    return Err("duplicate `exports=` key".to_string());
                }
                let mut list = Vec::new();
                if val != "-" {
                    for item in val.split(',') {
                        list.push(item.to_string());
                    }
                }
                exports = Some(list);
            } else {
                return Err(format!("unknown peer advertisement key {key:?}"));
            }
        }

        if !version_ok {
            return Err("missing required `v=1` in peer advertisement".to_string());
        }
        let Some(peer_val) = peer_id else {
            return Err("missing `peer=` in peer advertisement".to_string());
        };
        let Some(region_val) = region else {
            return Err("missing `region=` in peer advertisement".to_string());
        };
        let Some(tk_val) = transport_kind else {
            return Err("missing `transport=` in peer advertisement".to_string());
        };
        let Some(ep_val) = endpoint else {
            return Err("missing `endpoint=` in peer advertisement".to_string());
        };
        let Some(inc_val) = incarnation else {
            return Err("missing `incarnation=` in peer advertisement".to_string());
        };
        let Some(st_val) = state else {
            return Err("missing `state=` in peer advertisement".to_string());
        };
        let export_vec = match exports {
            Some(v) => v,
            None => return Err("missing `exports=` in peer advertisement".to_string()),
        };

        PeerAdvertisement::new(
            &peer_val,
            &region_val,
            &ep_val,
            tk_val,
            inc_val,
            st_val,
            export_vec,
        )
    }
}

/// Tracked gossip + RTT telemetry entry for one discovered peer in [`FederationDirectory`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeerRouteEntry {
    /// Latest accepted SWIM [`PeerAdvertisement`].
    pub ad: PeerAdvertisement,
    /// Smoothed EWMA round-trip latency in microseconds (`0` before first sample).
    pub srtt_us: u64,
    /// Monotone count of RTT observations integrated into `srtt_us`.
    pub rtt_samples: u64,
    /// Consecutive wire `Hello` probe failures (or poisoned responses).
    pub consecutive_failures: u32,
    /// Latest observed [`LogIdentity`] from wire `Hello` probes.
    pub last_log_id: Option<LogIdentity>,
    /// Whether the peer's latest `HelloHealth` reported a poisoned log.
    pub poisoned: bool,
}

impl PeerRouteEntry {
    fn from_advertisement(ad: PeerAdvertisement) -> Self {
        Self {
            ad,
            srtt_us: 0,
            rtt_samples: 0,
            consecutive_failures: 0,
            last_log_id: None,
            poisoned: false,
        }
    }

    /// Whether this peer is currently eligible to serve as a regional federation gateway.
    #[must_use]
    pub fn is_routable_for(&self, local_region: &str) -> bool {
        self.ad.region != local_region
            && self.ad.state == PeerHealthState::Alive
            && !self.poisoned
            && self.consecutive_failures == 0
            && !self.ad.export_prefixes.is_empty()
    }

    fn effective_rtt_us(&self) -> u64 {
        if self.rtt_samples == 0 {
            MAX_FEDERATION_RTT_US
        } else {
            self.srtt_us
        }
    }

    fn observe_rtt_sample(&mut self, sample_us: u64) -> u64 {
        let clamped = federation_seq_clamp(sample_us, MAX_FEDERATION_RTT_US);
        let next_srtt = if self.rtt_samples == 0 {
            clamped
        } else {
            let weighted = (self.srtt_us & 0x0FFF_FFFF_FFFF_FFFF).saturating_mul(7);
            weighted.saturating_add(clamped) >> 3
        };
        self.srtt_us = federation_seq_clamp(next_srtt, MAX_FEDERATION_RTT_US);
        self.rtt_samples =
            federation_cursor_advance(self.rtt_samples, self.rtt_samples.saturating_add(1));
        self.srtt_us
    }
}

/// Selected gateway decision for one remote region in [`FederationDirectory`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionRouteDecision {
    /// Remote region name (e.g. `"us-east"`).
    pub region: String,
    /// Chosen gateway `peer_id` in `region`.
    pub gateway_peer_id: String,
    /// Chosen gateway's advertised endpoint.
    pub endpoint: String,
    /// Chosen gateway's [`PeerTransportKind`].
    pub transport_kind: PeerTransportKind,
    /// Chosen gateway's smoothed RTT (`0` if unprobed).
    pub srtt_us: u64,
    /// Exported subject prefixes mirrored from this region.
    pub export_prefixes: Vec<String>,
}

/// SWIM incarnation-resolved dynamic peer directory and EWMA hysteresis multi-region
/// route selector (`MAX_FEDERATION_PEERS` peers, `MAX_FEDERATION_REGIONS` regions).
#[derive(Clone, Debug)]
pub struct FederationDirectory {
    local_region: String,
    hysteresis_us: u64,
    suspect_failure_threshold: u32,
    peers: Vec<PeerRouteEntry>,
    active_gateways: Vec<(String, String)>,
    route_switches: usize,
}

impl FederationDirectory {
    /// Create an empty directory for `local_region` with `hysteresis_us` EWMA damping.
    pub fn new(local_region: &str, hysteresis_us: u64) -> Result<Self, String> {
        validate_mesh_segment(local_region, "local_region")?;
        Ok(Self {
            local_region: local_region.to_string(),
            hysteresis_us: federation_seq_clamp(hysteresis_us, MAX_FEDERATION_RTT_US),
            suspect_failure_threshold: 2,
            peers: Vec::new(),
            active_gateways: Vec::new(),
            route_switches: 0,
        })
    }

    /// Override the consecutive probe-failure threshold (`>= 1`) that marks an `Alive`
    /// peer `Suspect`.
    #[must_use]
    pub const fn with_suspect_threshold(mut self, failures: u32) -> Self {
        self.suspect_failure_threshold = if failures == 0 { 1 } else { failures };
        self
    }

    /// Local region identifier.
    #[must_use]
    pub fn local_region(&self) -> &str {
        &self.local_region
    }

    /// Configured EWMA route-switch hysteresis margin in microseconds.
    #[must_use]
    pub const fn hysteresis_us(&self) -> u64 {
        self.hysteresis_us
    }

    /// Total number of primary regional gateway switches since creation.
    #[must_use]
    pub const fn route_switches(&self) -> usize {
        self.route_switches
    }

    /// Snapshot of all tracked [`PeerRouteEntry`] records.
    #[must_use]
    pub fn peers(&self) -> &[PeerRouteEntry] {
        &self.peers
    }

    /// Look up a tracked peer by `peer_id`.
    #[must_use]
    pub fn peer(&self, peer_id: &str) -> Option<&PeerRouteEntry> {
        let mut idx = 0usize;
        while idx < self.peers.len() {
            if let Some(entry) = self.peers.get(idx) {
                if entry.ad.peer_id == peer_id {
                    return Some(entry);
                }
            }
            idx = idx.saturating_add(1);
        }
        None
    }

    /// Publish `ad` as retained state under `"{registry_prefix}/{ad.peer_id}"` on a seed
    /// registry broker.
    pub fn publish_advertisement(
        registry: &FederationEndpoint,
        registry_prefix: &str,
        producer_id: u64,
        seq: u64,
        ad: &PeerAdvertisement,
    ) -> Result<(Offset, bool), FederationError> {
        if let Err(msg) = ad.validate() {
            return Err(FederationError::Config(msg));
        }
        let subject = match ad.registry_subject(registry_prefix) {
            Ok(s) => s,
            Err(msg) => return Err(FederationError::Config(msg)),
        };
        let payload = ad.encode_text();
        let (mut client, _closer) = match registry.dial() {
            Ok(pair) => pair,
            Err(e) => return Err(FederationError::Io(e)),
        };
        match client.publish(producer_id, seq, &subject, payload.as_bytes()) {
            Ok(ack) => Ok(ack),
            Err(e) => Err(FederationError::Io(e)),
        }
    }

    /// Discover all retained [`PeerAdvertisement`] records under `"{registry_prefix}/>"` from
    /// a seed registry broker via `Client::last_all`. Malformed records fail closed with
    /// [`FederationError::Config`].
    pub fn discover_from_registry(
        registry: &FederationEndpoint,
        registry_prefix: &str,
    ) -> Result<Vec<PeerAdvertisement>, FederationError> {
        if let Err(msg) = validate_prefix_shape(registry_prefix, "registry_prefix") {
            return Err(FederationError::Config(msg));
        }
        let filter = format!("{registry_prefix}/>");
        if Filter::new(&filter).is_err() {
            return Err(FederationError::Config(format!(
                "invalid registry filter {filter:?}"
            )));
        }
        let (mut client, _closer) = match registry.dial() {
            Ok(pair) => pair,
            Err(e) => return Err(FederationError::Io(e)),
        };
        let (records, _head) = match client.last_all(&filter) {
            Ok(page) => page,
            Err(e) => return Err(FederationError::Io(e)),
        };
        let mut out = Vec::with_capacity(records.len().min(MAX_FEDERATION_PEERS));
        let mut idx = 0usize;
        while idx < records.len() {
            if let Some((_off, _subj, body)) = records.get(idx) {
                let text = match std::str::from_utf8(body) {
                    Ok(s) => s,
                    Err(_) => {
                        return Err(FederationError::Config(
                            "non-UTF8 peer advertisement in registry".to_string(),
                        ))
                    }
                };
                let ad = match PeerAdvertisement::decode_text(text) {
                    Ok(a) => a,
                    Err(msg) => return Err(FederationError::Config(msg)),
                };
                out.push(ad);
            }
            idx = idx.saturating_add(1);
        }
        Ok(out)
    }

    /// Apply a [`PeerAdvertisement`] under SWIM monotone incarnation rules:
    /// - A strictly higher incarnation (`observed >= current + 1`, verified via
    ///   [`federation_incarnation_fresh`]) supersedes any prior state (allowing a live peer to
    ///   refute false `Suspect` gossip or rejoin cleanly after restart).
    /// - Equal incarnation permits only monotone health degradation
    ///   (`Alive -> Suspect -> Draining -> Dead`) and metadata refresh if nothing degrades backwards.
    /// - Lower incarnations are ignored as stale gossip (`Ok(false)`).
    pub fn apply_advertisement(&mut self, ad: PeerAdvertisement) -> Result<bool, String> {
        ad.validate()?;
        let mut idx = 0usize;
        while idx < self.peers.len() {
            if let Some(entry) = self.peers.get_mut(idx) {
                if entry.ad.peer_id == ad.peer_id {
                    if let Some(min_fresh) = entry.ad.incarnation.checked_add(1) {
                        if ad.incarnation > entry.ad.incarnation
                            && federation_incarnation_fresh(ad.incarnation, min_fresh)
                        {
                            let next_inc =
                                federation_cursor_advance(entry.ad.incarnation, ad.incarnation);
                            let mut updated = ad;
                            updated.incarnation = next_inc;
                            if updated.state == PeerHealthState::Alive {
                                entry.consecutive_failures = 0;
                            }
                            entry.ad = updated;
                            return Ok(true);
                        }
                    }
                    if ad.incarnation == entry.ad.incarnation
                        && ad.state.degradation_rank() > entry.ad.state.degradation_rank()
                    {
                        entry.ad.state = ad.state;
                        return Ok(true);
                    }
                    return Ok(false);
                }
            }
            idx = idx.saturating_add(1);
        }

        if self.peers.len() >= MAX_FEDERATION_PEERS {
            return Err(format!(
                "peer table full at MAX_FEDERATION_PEERS ({MAX_FEDERATION_PEERS})"
            ));
        }
        self.peers.push(PeerRouteEntry::from_advertisement(ad));
        Ok(true)
    }

    /// Record a deterministic or measured RTT sample (in microseconds) for `peer_id`, resetting
    /// `consecutive_failures` and `poisoned`. Returns `true` if `peer_id` is known.
    pub fn record_rtt_sample(&mut self, peer_id: &str, sample_us: u64) -> bool {
        let mut idx = 0usize;
        while idx < self.peers.len() {
            if let Some(entry) = self.peers.get_mut(idx) {
                if entry.ad.peer_id == peer_id {
                    let _ = entry.observe_rtt_sample(sample_us);
                    entry.consecutive_failures = 0;
                    entry.poisoned = false;
                    return true;
                }
            }
            idx = idx.saturating_add(1);
        }
        false
    }

    /// Record a probe failure (or poisoned log health) for `peer_id`, transitioning `Alive`
    /// to `Suspect` once `consecutive_failures >= suspect_failure_threshold`.
    pub fn record_probe_failure(&mut self, peer_id: &str, poisoned: bool) -> bool {
        let threshold = self.suspect_failure_threshold;
        let mut idx = 0usize;
        while idx < self.peers.len() {
            if let Some(entry) = self.peers.get_mut(idx) {
                if entry.ad.peer_id == peer_id {
                    entry.consecutive_failures = entry.consecutive_failures.saturating_add(1);
                    if poisoned {
                        entry.poisoned = true;
                    }
                    if entry.ad.state == PeerHealthState::Alive
                        && (poisoned || entry.consecutive_failures >= threshold)
                    {
                        entry.ad.state = PeerHealthState::Suspect;
                    }
                    return true;
                }
            }
            idx = idx.saturating_add(1);
        }
        false
    }

    fn current_gateway_for(&self, region: &str) -> Option<&str> {
        let mut idx = 0usize;
        while idx < self.active_gateways.len() {
            if let Some((reg, gw)) = self.active_gateways.get(idx) {
                if reg == region {
                    return Some(gw.as_str());
                }
            }
            idx = idx.saturating_add(1);
        }
        None
    }

    /// Recompute the optimal gateway per remote region using EWMA `srtt_us` with
    /// `hysteresis_us` stickiness (verified via [`federation_route_preferred`]), returning
    /// decisions sorted lexicographically by `region`.
    pub fn recompute_routes(&mut self) -> Vec<RegionRouteDecision> {
        let mut regions: Vec<String> = Vec::new();
        let mut i = 0usize;
        while i < self.peers.len() {
            if let Some(entry) = self.peers.get(i) {
                if entry.ad.region != self.local_region && regions.len() < MAX_FEDERATION_REGIONS {
                    let mut seen = false;
                    let mut r_idx = 0usize;
                    while r_idx < regions.len() {
                        if let Some(existing) = regions.get(r_idx) {
                            if existing == &entry.ad.region {
                                seen = true;
                                break;
                            }
                        }
                        r_idx = r_idx.saturating_add(1);
                    }
                    if !seen {
                        regions.push(entry.ad.region.clone());
                    }
                }
            }
            i = i.saturating_add(1);
        }

        // Insertion-sort `regions` lexicographically without closures or panicking indexing.
        let mut sort_i = 1usize;
        while sort_i < regions.len() {
            let mut j = sort_i;
            while j > 0 {
                let prev = j.saturating_sub(1);
                let Some((left_half, right_half)) = regions.split_at_mut_checked(j) else {
                    break;
                };
                let (Some(left), Some(right)) = (left_half.get_mut(prev), right_half.first_mut())
                else {
                    break;
                };
                if *left > *right {
                    std::mem::swap(left, right);
                } else {
                    break;
                }
                j = prev;
            }
            sort_i = sort_i.saturating_add(1);
        }

        let mut next_active: Vec<(String, String)> = Vec::new();
        let mut decisions: Vec<RegionRouteDecision> = Vec::new();

        let mut reg_i = 0usize;
        while reg_i < regions.len() {
            let Some(region) = regions.get(reg_i) else {
                break;
            };

            // Find lowest-RTT eligible candidate in `region` (tie-break by `peer_id`).
            let mut best_idx: Option<usize> = None;
            let mut p_i = 0usize;
            while p_i < self.peers.len() {
                if let Some(cand) = self.peers.get(p_i) {
                    if cand.ad.region == *region && cand.is_routable_for(&self.local_region) {
                        let take = match best_idx {
                            None => true,
                            Some(cur_best_idx) => match self.peers.get(cur_best_idx) {
                                None => true,
                                Some(cur_best) => {
                                    let c_rtt = cand.effective_rtt_us();
                                    let b_rtt = cur_best.effective_rtt_us();
                                    c_rtt < b_rtt
                                        || (c_rtt == b_rtt && cand.ad.peer_id < cur_best.ad.peer_id)
                                }
                            },
                        };
                        if take {
                            best_idx = Some(p_i);
                        }
                    }
                }
                p_i = p_i.saturating_add(1);
            }

            // Check whether `region` already had a healthy active gateway that holds within hysteresis.
            let prev_gw_id: Option<String> = match self.current_gateway_for(region) {
                Some(id) => Some(id.to_string()),
                None => None,
            };
            let mut prev_idx: Option<usize> = None;
            if let Some(ref prev_id) = prev_gw_id {
                let mut k = 0usize;
                while k < self.peers.len() {
                    if let Some(p) = self.peers.get(k) {
                        if p.ad.peer_id == *prev_id
                            && p.ad.region == *region
                            && p.is_routable_for(&self.local_region)
                        {
                            prev_idx = Some(k);
                            break;
                        }
                    }
                    k = k.saturating_add(1);
                }
            }

            let chosen_idx = match (prev_idx, best_idx) {
                (None, None) => None,
                (None, Some(b)) => Some(b),
                (Some(p), None) => Some(p),
                (Some(p), Some(b)) => {
                    if p == b {
                        Some(p)
                    } else {
                        match (self.peers.get(p), self.peers.get(b)) {
                            (Some(prev_peer), Some(best_peer)) => {
                                if prev_peer.rtt_samples > 0 && best_peer.rtt_samples > 0 {
                                    match best_peer.srtt_us.checked_add(self.hysteresis_us) {
                                        Some(thresh)
                                            if federation_route_preferred(
                                                prev_peer.srtt_us,
                                                thresh,
                                            ) =>
                                        {
                                            Some(b)
                                        }
                                        _ => Some(p),
                                    }
                                } else if prev_peer.rtt_samples == 0 && best_peer.rtt_samples > 0 {
                                    Some(b)
                                } else {
                                    Some(p)
                                }
                            }
                            _ => Some(b),
                        }
                    }
                }
            };

            if let Some(c_idx) = chosen_idx {
                if let Some(chosen) = self.peers.get(c_idx) {
                    if let Some(ref prev_id) = prev_gw_id {
                        if prev_id != &chosen.ad.peer_id {
                            self.route_switches = self.route_switches.saturating_add(1);
                        }
                    }
                    next_active.push((region.clone(), chosen.ad.peer_id.clone()));
                    decisions.push(RegionRouteDecision {
                        region: region.clone(),
                        gateway_peer_id: chosen.ad.peer_id.clone(),
                        endpoint: chosen.ad.endpoint.clone(),
                        transport_kind: chosen.ad.transport_kind,
                        srtt_us: chosen.srtt_us,
                        export_prefixes: chosen.ad.export_prefixes.clone(),
                    });
                }
            }

            reg_i = reg_i.saturating_add(1);
        }

        self.active_gateways = next_active;
        decisions
    }
}

const fn derive_mesh_producer_id(base: u64, log_id: &[u8; 16], prefix_idx: u64) -> u64 {
    let mut acc = base ^ 0x9E37_79B9_7F4A_7C15 ^ prefix_idx;
    let mut rest: &[u8] = log_id;
    while let &[b, ref tail @ ..] = rest {
        acc = (acc ^ (b as u64)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        rest = tail;
    }
    acc ^= acc >> 30;
    if acc == 0 {
        1
    } else {
        acc
    }
}

/// Configuration for [`FederationMesh`] (dynamic seed-registry discovery + automatic
/// multi-region gateway selection and loop-free inbound subtree mirroring).
#[derive(Clone, Debug)]
pub struct FederationMeshConfig {
    /// Local region identifier (e.g. `"us-west"`).
    pub local_region: String,
    /// Local broker endpoint receiving mirrored multi-region subtrees.
    pub local_endpoint: FederationEndpoint,
    /// Local region's own exported prefixes, automatically added to `exclude_prefixes` on all
    /// inbound regional bridges so bidirectional multi-region meshes never echo records back
    /// to their origin region (split-horizon loop prevention).
    pub local_export_prefixes: Vec<String>,
    /// Seed registry brokers polled via `Client::last_all` during dynamic discovery.
    pub seed_registries: Vec<FederationEndpoint>,
    /// Retained registry subject prefix (`DEFAULT_PEER_REGISTRY_PREFIX` = `"/f/fed/peers"`).
    pub registry_prefix: String,
    /// Base `producer_id` used on `local_endpoint`.
    pub base_producer_id: u64,
    /// When `true` (default), derives a deterministic non-zero `producer_id` from
    /// `(base_producer_id, source_log_identity.id, prefix_idx)` so independent gateway logs in
    /// the same region never collide `(producer_id, seq)` dedup slots while replicas sharing a
    /// `LogIdentity.id` preserve exact failover deduplication. Set `false` when `local_endpoint`
    /// uses a capability grant bound to a single fixed principal `p=<principal>`.
    pub per_source_log_producer_id: bool,
    /// EWMA hysteresis margin in microseconds (`DEFAULT_ROUTE_HYSTERESIS_US`).
    pub hysteresis_us: u64,
    /// Consecutive wire probe failures before marking an `Alive` peer `Suspect`.
    pub suspect_failure_threshold: u32,
    /// Connect/IO timeout used for live wire `Hello` RTT + `HelloHealth` probes.
    pub probe_timeout: Duration,
    /// Maximum records mirrored per regional bridge step (`1..=FEDERATION_BATCH_CAP`).
    pub batch_size: usize,
    /// Maximum federation hop budget (`1` by default).
    pub max_hops: u8,
}

impl FederationMeshConfig {
    /// Construct a default [`FederationMeshConfig`] for `(local_region, local_endpoint)`.
    #[must_use]
    pub fn new(
        local_region: &str,
        local_endpoint: FederationEndpoint,
        base_producer_id: u64,
    ) -> Self {
        Self {
            local_region: local_region.to_string(),
            local_endpoint,
            local_export_prefixes: Vec::new(),
            seed_registries: Vec::new(),
            registry_prefix: DEFAULT_PEER_REGISTRY_PREFIX.to_string(),
            base_producer_id,
            per_source_log_producer_id: true,
            hysteresis_us: DEFAULT_ROUTE_HYSTERESIS_US,
            suspect_failure_threshold: 2,
            probe_timeout: Duration::from_millis(500),
            batch_size: DEFAULT_FEDERATION_BATCH,
            max_hops: 1,
        }
    }
}

/// Summary of one [`FederationMesh::sync_once`] discovery + probing + multi-region sync tick.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FederationMeshReport {
    /// Total peers currently tracked in the mesh directory.
    pub discovered_peers: usize,
    /// Number of remote regions with an active healthy gateway selected.
    pub active_regions: usize,
    /// Cumulative gateway switches recorded by [`FederationDirectory`].
    pub route_switches: usize,
    /// Records fetched across all active regional bridges in this tick.
    pub fetched: usize,
    /// Records mirrored onto `local_endpoint` in this tick.
    pub mirrored: usize,
    /// Records deduplicated on `local_endpoint` in this tick.
    pub deduped: usize,
    /// Records skipped by split-horizon / hop-budget filters in this tick.
    pub skipped: usize,
    /// Selected `(region, gateway_peer_id)` pairs sorted by `region`.
    pub active_gateways: Vec<(String, String)>,
}

struct ActiveRegionBridge {
    region: String,
    gateway_peer_id: String,
    prefix_idx: usize,
    export_prefix: String,
    bridge: FederationBridge,
}

/// Dynamic multi-region federation coordinator combining seed-registry peer discovery,
/// wire `Hello` RTT + `HelloHealth.poisoned` probing, hysteresis-damped gateway selection,
/// automatic gateway failover, split-horizon echo suppression, and healed [`FederatedCut`]
/// tracking across regions.
pub struct FederationMesh {
    cfg: FederationMeshConfig,
    directory: FederationDirectory,
    peer_wire_overrides: Vec<(String, FederationEndpoint)>,
    bridges: Vec<ActiveRegionBridge>,
    cut: FederatedCut,
    stopped: Arc<AtomicBool>,
}

impl FederationMesh {
    /// Validate `cfg` and initialize an empty [`FederationMesh`].
    pub fn open(cfg: FederationMeshConfig) -> Result<Self, FederationError> {
        if let Err(msg) = validate_prefix_shape(&cfg.registry_prefix, "registry_prefix") {
            return Err(FederationError::Config(msg));
        }
        let mut idx = 0usize;
        while idx < cfg.local_export_prefixes.len() {
            if let Some(pfx) = cfg.local_export_prefixes.get(idx) {
                if let Err(msg) = validate_prefix_shape(pfx, "local_export_prefix") {
                    return Err(FederationError::Config(msg));
                }
            }
            idx = idx.saturating_add(1);
        }
        let dir = match FederationDirectory::new(&cfg.local_region, cfg.hysteresis_us) {
            Ok(d) => d.with_suspect_threshold(cfg.suspect_failure_threshold),
            Err(msg) => return Err(FederationError::Config(msg)),
        };
        Ok(Self {
            cfg,
            directory: dir,
            peer_wire_overrides: Vec::new(),
            bridges: Vec::new(),
            cut: FederatedCut::new(),
            stopped: Arc::new(AtomicBool::new(false)),
        })
    }

    /// Register an authenticated [`FederationEndpoint`] (e.g. Sealed, Handshake, Identity, or
    /// capability-bearing endpoint) to use whenever dialing `peer_id`, keeping secrets out of
    /// [`PeerAdvertisement`] gossip records.
    pub fn set_peer_endpoint_override(&mut self, peer_id: &str, endpoint: FederationEndpoint) {
        let mut idx = 0usize;
        while idx < self.peer_wire_overrides.len() {
            if let Some(slot) = self.peer_wire_overrides.get_mut(idx) {
                if slot.0 == peer_id {
                    slot.1 = endpoint;
                    return;
                }
            }
            idx = idx.saturating_add(1);
        }
        if self.peer_wire_overrides.len() < MAX_FEDERATION_PEERS {
            self.peer_wire_overrides
                .push((peer_id.to_string(), endpoint));
        }
    }

    /// Return a cooperative stop handle for background mesh loops.
    #[must_use]
    pub fn closer(&self) -> FederationRunnerCloser {
        FederationRunnerCloser {
            stopped: Arc::clone(&self.stopped),
            bridges: Vec::new(),
        }
    }

    /// Borrow the underlying [`FederationDirectory`].
    #[must_use]
    pub const fn directory(&self) -> &FederationDirectory {
        &self.directory
    }

    /// Mutably borrow the underlying [`FederationDirectory`] (e.g. for direct gossip injection).
    pub fn directory_mut(&mut self) -> &mut FederationDirectory {
        &mut self.directory
    }

    /// Current Chandy-Lamport consistent [`FederatedCut`] across all regional links mirrored
    /// by this mesh.
    #[must_use]
    pub const fn cut(&self) -> &FederatedCut {
        &self.cut
    }

    fn endpoint_for(&self, ad: &PeerAdvertisement) -> FederationEndpoint {
        let mut idx = 0usize;
        while idx < self.peer_wire_overrides.len() {
            if let Some((pid, ep)) = self.peer_wire_overrides.get(idx) {
                if pid == &ad.peer_id {
                    return ep.clone();
                }
            }
            idx = idx.saturating_add(1);
        }
        let transport = match ad.transport_kind {
            PeerTransportKind::Unix => Transport::Unix,
            PeerTransportKind::Tcp => Transport::Tcp,
        };
        FederationEndpoint::new(&ad.endpoint, transport)
            .with_timeouts(Some(self.cfg.probe_timeout), Some(self.cfg.probe_timeout))
    }

    /// Poll all configured `seed_registries` via `Client::last_all` and fold discovered
    /// [`PeerAdvertisement`] records into [`FederationDirectory`]. Seed registries that are
    /// temporarily unreachable are skipped as long as at least one seed succeeds (or no seeds
    /// are configured).
    pub fn refresh_discovery(&mut self) -> Result<usize, FederationError> {
        if self.cfg.seed_registries.is_empty() {
            return Ok(self.directory.peers().len());
        }
        let mut any_ok = false;
        let mut last_err: Option<FederationError> = None;
        let mut idx = 0usize;
        while idx < self.cfg.seed_registries.len() {
            if let Some(seed) = self.cfg.seed_registries.get(idx) {
                match FederationDirectory::discover_from_registry(seed, &self.cfg.registry_prefix) {
                    Ok(ads) => {
                        any_ok = true;
                        let mut a_i = 0usize;
                        while a_i < ads.len() {
                            if let Some(ad) = ads.get(a_i) {
                                if let Err(msg) = self.directory.apply_advertisement(ad.clone()) {
                                    return Err(FederationError::Config(msg));
                                }
                            }
                            a_i = a_i.saturating_add(1);
                        }
                    }
                    Err(FederationError::Config(msg)) => {
                        return Err(FederationError::Config(msg));
                    }
                    Err(e) => {
                        last_err = Some(e);
                    }
                }
            }
            idx = idx.saturating_add(1);
        }
        if !any_ok {
            if let Some(err) = last_err {
                return Err(err);
            }
        }
        Ok(self.directory.peers().len())
    }

    /// Probe every non-`Dead` remote peer over the wire with `Client::hello_identity`,
    /// recording measured EWMA `srtt_us`, [`LogIdentity`], and `HelloHealth.poisoned` status.
    pub fn probe_peers(&mut self) {
        let mut targets: Vec<PeerAdvertisement> = Vec::new();
        let mut idx = 0usize;
        while idx < self.directory.peers.len() {
            if let Some(entry) = self.directory.peers.get(idx) {
                if entry.ad.region != self.cfg.local_region
                    && entry.ad.state != PeerHealthState::Dead
                {
                    targets.push(entry.ad.clone());
                }
            }
            idx = idx.saturating_add(1);
        }

        let mut t_i = 0usize;
        while t_i < targets.len() {
            if let Some(ad) = targets.get(t_i) {
                let ep = self.endpoint_for(ad);
                let started = std::time::Instant::now();
                let mut probe_ok = false;
                let mut poisoned = false;
                let mut seen_log: Option<LogIdentity> = None;

                if let Ok((mut client, _closer)) = ep.dial() {
                    if let Ok((_nonce, log_id)) = client.hello_identity() {
                        seen_log = log_id;
                        if let Some(h) = client.broker_health() {
                            if h.poisoned.is_some() {
                                poisoned = true;
                            }
                        }
                        if !poisoned {
                            probe_ok = true;
                        }
                    }
                }

                let elapsed = started.elapsed();
                let sample_us = match u64::try_from(elapsed.as_micros()) {
                    Ok(0) => 1,
                    Ok(v) => v,
                    Err(_) => MAX_FEDERATION_RTT_US,
                };

                if probe_ok {
                    let _ = self.directory.record_rtt_sample(&ad.peer_id, sample_us);
                    let mut p_idx = 0usize;
                    while p_idx < self.directory.peers.len() {
                        if let Some(entry) = self.directory.peers.get_mut(p_idx) {
                            if entry.ad.peer_id == ad.peer_id {
                                entry.last_log_id = seen_log;
                                break;
                            }
                        }
                        p_idx = p_idx.saturating_add(1);
                    }
                } else {
                    let _ = self.directory.record_probe_failure(&ad.peer_id, poisoned);
                }
            }
            t_i = t_i.saturating_add(1);
        }
    }

    fn open_region_bridge(
        &self,
        decision: &RegionRouteDecision,
        prefix_idx: usize,
        export_prefix: &str,
    ) -> Result<ActiveRegionBridge, FederationError> {
        let ad = PeerAdvertisement {
            peer_id: decision.gateway_peer_id.clone(),
            region: decision.region.clone(),
            endpoint: decision.endpoint.clone(),
            transport_kind: decision.transport_kind,
            incarnation: 0,
            state: PeerHealthState::Alive,
            export_prefixes: decision.export_prefixes.clone(),
        };
        let mut src_ep = self.endpoint_for(&ad);
        if src_ep.io_timeout == Some(self.cfg.probe_timeout) {
            src_ep.io_timeout = self.cfg.local_endpoint.io_timeout;
        }
        let group = format!(
            "/g/mesh/{}/{}/p{prefix_idx}",
            self.cfg.local_region, decision.region
        );
        let filter = format!("{export_prefix}/>");

        let mut rw = SubjectRewrite::passthrough().with_hop_budget(0, self.cfg.max_hops);
        let mut ex_i = 0usize;
        while ex_i < self.cfg.local_export_prefixes.len() {
            if let Some(local_pfx) = self.cfg.local_export_prefixes.get(ex_i) {
                rw = match rw.with_excluded_prefix(local_pfx) {
                    Ok(next) => next,
                    Err(msg) => return Err(FederationError::Config(msg)),
                };
            }
            ex_i = ex_i.saturating_add(1);
        }

        let mut producer_id = self.cfg.base_producer_id;
        if self.cfg.per_source_log_producer_id {
            if let Some(peer_entry) = self.directory.peer(&decision.gateway_peer_id) {
                if let Some(log_id) = peer_entry.last_log_id {
                    let p_idx_u64 = u64::try_from(prefix_idx).unwrap_or(0);
                    producer_id =
                        derive_mesh_producer_id(self.cfg.base_producer_id, &log_id.id, p_idx_u64);
                }
            }
        }

        let bridge = FederationBridge::open(FederationConfig {
            source: src_ep,
            dest: self.cfg.local_endpoint.clone(),
            group,
            filter,
            carry: Vec::new(),
            producer_id,
            rewrite: rw,
            relay: false,
        })?;

        Ok(ActiveRegionBridge {
            region: decision.region.clone(),
            gateway_peer_id: decision.gateway_peer_id.clone(),
            prefix_idx,
            export_prefix: export_prefix.to_string(),
            bridge,
        })
    }

    fn reconcile_bridges(
        &mut self,
        decisions: &[RegionRouteDecision],
    ) -> Result<(), FederationError> {
        let mut old_bridges = std::mem::take(&mut self.bridges);
        let mut pool: Vec<Option<ActiveRegionBridge>> = Vec::new();
        while let Some(bridge) = old_bridges.pop() {
            pool.push(Some(bridge));
        }

        let mut next_bridges: Vec<ActiveRegionBridge> = Vec::new();
        let mut d_i = 0usize;
        while d_i < decisions.len() {
            if let Some(dec) = decisions.get(d_i) {
                let mut p_i = 0usize;
                while p_i < dec.export_prefixes.len() {
                    if let Some(export_pfx) = dec.export_prefixes.get(p_i) {
                        // Reuse existing bridge if `(region, gateway_peer_id, prefix_idx, export_prefix)` matches.
                        let mut reused: Option<ActiveRegionBridge> = None;
                        let mut b_i = 0usize;
                        while b_i < pool.len() {
                            if let Some(slot) = pool.get_mut(b_i) {
                                let matches = match slot.as_ref() {
                                    Some(b) => {
                                        b.region == dec.region
                                            && b.gateway_peer_id == dec.gateway_peer_id
                                            && b.prefix_idx == p_i
                                            && b.export_prefix == *export_pfx
                                    }
                                    None => false,
                                };
                                if matches {
                                    reused = slot.take();
                                    break;
                                }
                            }
                            b_i = b_i.saturating_add(1);
                        }
                        match reused {
                            Some(existing) => next_bridges.push(existing),
                            None => {
                                let opened = self.open_region_bridge(dec, p_i, export_pfx)?;
                                next_bridges.push(opened);
                            }
                        }
                    }
                    p_i = p_i.saturating_add(1);
                }
            }
            d_i = d_i.saturating_add(1);
        }
        self.bridges = next_bridges;
        Ok(())
    }

    /// Execute one complete dynamic mesh cycle:
    /// 1. Poll seed registries (`refresh_discovery`) and fold SWIM incarnations.
    /// 2. Probe remote peer endpoints (`probe_peers`) when `run_wire_probes` is `true`.
    /// 3. Recompute hysteresis-damped lowest-RTT regional gateways (`recompute_routes`).
    /// 4. Reconcile [`FederationBridge`] instances across active gateways, draining up to
    ///    `cfg.batch_size` records per exported prefix and healing `self.cut()`.
    pub fn sync_once(
        &mut self,
        run_wire_probes: bool,
    ) -> Result<FederationMeshReport, FederationError> {
        if self.stopped.load(Ordering::Acquire) {
            return Ok(FederationMeshReport {
                discovered_peers: self.directory.peers().len(),
                route_switches: self.directory.route_switches(),
                ..FederationMeshReport::default()
            });
        }
        let discovered = self.refresh_discovery()?;
        if run_wire_probes {
            self.probe_peers();
        }
        let decisions = self.directory.recompute_routes();
        self.reconcile_bridges(&decisions)?;

        let batch = self.cfg.batch_size.clamp(1, FEDERATION_BATCH_CAP);
        let mut all_links: Vec<FederationLink> = Vec::new();
        let mut report = FederationMeshReport {
            discovered_peers: discovered,
            active_regions: decisions.len(),
            route_switches: self.directory.route_switches(),
            fetched: 0,
            mirrored: 0,
            deduped: 0,
            skipped: 0,
            active_gateways: Vec::new(),
        };

        let mut d_i = 0usize;
        while d_i < decisions.len() {
            if let Some(dec) = decisions.get(d_i) {
                report
                    .active_gateways
                    .push((dec.region.clone(), dec.gateway_peer_id.clone()));
            }
            d_i = d_i.saturating_add(1);
        }

        let mut b_i = 0usize;
        while b_i < self.bridges.len() {
            if self.stopped.load(Ordering::Acquire) {
                break;
            }
            let step_res = match self.bridges.get_mut(b_i) {
                Some(active) => {
                    let src_id = active.bridge.source_identity();
                    let res = active.bridge.sync_once(batch);
                    (active.gateway_peer_id.clone(), src_id, res)
                }
                None => break,
            };
            let (gw_id, src_id, res) = step_res;
            match res {
                Ok(step) => {
                    report.fetched = report.fetched.saturating_add(step.fetched);
                    report.mirrored = report.mirrored.saturating_add(step.mirrored);
                    report.deduped = report.deduped.saturating_add(step.deduped);
                    report.skipped = report.skipped.saturating_add(step.skipped);
                    if step.next_cursor > 0 {
                        self.cut.advance(src_id, step.next_cursor);
                    }
                    let mut l_i = 0usize;
                    while l_i < step.links.len() {
                        if let Some(link) = step.links.get(l_i) {
                            self.cut
                                .advance(link.src_log, link.src_offset.saturating_add(1));
                            self.cut
                                .advance(link.dst_log, link.dst_offset.saturating_add(1));
                            all_links.push(link.clone());
                        }
                        l_i = l_i.saturating_add(1);
                    }
                    b_i = b_i.saturating_add(1);
                }
                Err(FederationError::Io(_)) => {
                    // Mark failed gateway suspect so the next `sync_once` fails over automatically!
                    let _ = self.directory.record_probe_failure(&gw_id, false);
                    let _ = self.directory.record_probe_failure(&gw_id, false);
                    b_i = b_i.saturating_add(1);
                }
                Err(other) => return Err(other),
            }
        }

        if !all_links.is_empty() {
            let _ = self.cut.heal(&all_links);
        }
        Ok(report)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn federation_directory_enforces_swim_incarnation_and_ewma_hysteresis() {
        let gw1 = PeerAdvertisement::new(
            "us-east-gw1",
            "us-east",
            "/tmp/gw1.sock",
            PeerTransportKind::Unix,
            1,
            PeerHealthState::Alive,
            vec!["/f/us-east".to_string()],
        )
        .expect("valid gw1 advertisement");
        let encoded = gw1.encode_text();
        let decoded = PeerAdvertisement::decode_text(&encoded).expect("round-trip decode");
        assert_eq!(decoded, gw1);

        // Fail-closed validation checks.
        assert!(PeerAdvertisement::decode_text("").is_err());
        assert!(PeerAdvertisement::decode_text("peer=a region=b").is_err());
        assert!(PeerAdvertisement::new(
            "bad/slash",
            "us-east",
            "/tmp/x",
            PeerTransportKind::Unix,
            1,
            PeerHealthState::Alive,
            vec!["/f/us-east".to_string()],
        )
        .is_err());

        let mut dir = FederationDirectory::new("us-west", 2_000).expect("valid directory");
        assert!(dir.apply_advertisement(gw1.clone()).unwrap());

        // Equal incarnation allows Alive -> Suspect degradation, but rejects stale Suspect -> Alive.
        let gw1_suspect = PeerAdvertisement::new(
            "us-east-gw1",
            "us-east",
            "/tmp/gw1.sock",
            PeerTransportKind::Unix,
            1,
            PeerHealthState::Suspect,
            vec!["/f/us-east".to_string()],
        )
        .unwrap();
        assert!(dir.apply_advertisement(gw1_suspect).unwrap());
        assert_eq!(
            dir.peer("us-east-gw1").unwrap().ad.state,
            PeerHealthState::Suspect
        );
        assert!(!dir.apply_advertisement(gw1).unwrap());

        // Strictly higher incarnation refutes Suspect back to Alive (`federation_incarnation_fresh`).
        let gw1_refuted = PeerAdvertisement::new(
            "us-east-gw1",
            "us-east",
            "/tmp/gw1.sock",
            PeerTransportKind::Unix,
            2,
            PeerHealthState::Alive,
            vec!["/f/us-east".to_string()],
        )
        .unwrap();
        assert!(dir.apply_advertisement(gw1_refuted).unwrap());
        assert_eq!(
            dir.peer("us-east-gw1").unwrap().ad.state,
            PeerHealthState::Alive
        );

        let gw2 = PeerAdvertisement::new(
            "us-east-gw2",
            "us-east",
            "/tmp/gw2.sock",
            PeerTransportKind::Unix,
            1,
            PeerHealthState::Alive,
            vec!["/f/us-east".to_string()],
        )
        .unwrap();
        assert!(dir.apply_advertisement(gw2).unwrap());

        // Establish initial route on gw1 (`10_000` us vs `12_000` us).
        assert!(dir.record_rtt_sample("us-east-gw1", 10_000));
        assert!(dir.record_rtt_sample("us-east-gw2", 12_000));
        let r0 = dir.recompute_routes();
        assert_eq!(r0.len(), 1);
        assert_eq!(r0[0].gateway_peer_id, "us-east-gw1");
        assert_eq!(dir.route_switches(), 0);

        // Candidate improves to 8_500 us (`8_500 + 2_000 = 10_500 > 10_000`): hysteresis holds gw1!
        let mut i = 0;
        while i < 32 {
            dir.record_rtt_sample("us-east-gw2", 8_500);
            i += 1;
        }
        let r1 = dir.recompute_routes();
        assert_eq!(r1[0].gateway_peer_id, "us-east-gw1");
        assert_eq!(dir.route_switches(), 0);

        // Candidate improves to 7_000 us (`srtt <= 8_000`, `cand + 2_000 <= 10_000`): switches cleanly!
        let mut j = 0;
        while j < 32 {
            dir.record_rtt_sample("us-east-gw2", 7_000);
            j += 1;
        }
        let r2 = dir.recompute_routes();
        assert_eq!(r2[0].gateway_peer_id, "us-east-gw2");
        assert_eq!(dir.route_switches(), 1);
    }
}
