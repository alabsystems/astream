// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Content-addressed Merkle-DAG session history (`docs/DESIGN-astream-term.md` §9,
//! `docs/ROADMAP.md` "Content-addressed Merkle-DAG session history").
//!
//! Each session [`Envelope`] is linked into a domain-separated SHA-256 commit chain
//! ([`MerkleChain`]) where every [`MerkleNode`] commits to its dense [`Offset`],
//! `ts_logical`, causal pointer, record payload, and up to [`MAX_MERKLE_PARENTS`]
//! (`2`) parent [`CommitHash`]es (`0` at genesis, `1` for linear history, `2` at an
//! input-branch merge point).
//!
//! ## §9 Merge Law (Pure Input Logs Only)
//!
//! Diffing two chains ([`diff_chains`]) finds their lowest common ancestor ([`lca`])
//! and partitions both timelines into the shared prefix plus each branch's divergent
//! suffix. Merging two divergent branches ([`merge_input_branches`]) enforces §9's
//! semantic boundary: **a merge is sound only when both divergent suffixes consist
//! exclusively of [`Record::In`] records**. Any [`Record::Out`], [`Record::Resize`],
//! or [`Record::Exit`] in either divergent suffix is refused fail-closed
//! ([`MerkleError::DivergentNonInput`]), because a forked output timeline cannot be
//! merged without re-driving the underlying program through the effect seam.

use crate::envelope::{CausedBy, Envelope};
use crate::log::{Log, ReadError};
use astream_digest::{ct_eq, Sha256};
use astream_term::Record;
use astream_wire::Offset;
use std::collections::BTreeMap;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "merkle_island.rs"]
mod merkle_island;
#[cfg(not(clean_islands))]
pub use crate::twins::merkle_parent_count_clamp;
#[cfg(clean_islands)]
pub use merkle_island::merkle_parent_count_clamp;

contract_fn! {
    /// Kernel-certified check that a Merkle node's envelope sequence `found_seq`
    /// equals the expected dense commit index `expected_seq`.
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `merkle_offset_matches_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn merkle_offset_matches(expected_seq: u64, found_seq: u64) -> bool
    clauses [ensures result == (expected_seq == found_seq)]
    {
        expected_seq == found_seq
    }
}

/// Maximum number of parent commits on any [`MerkleNode`] (`0` = genesis,
/// `1` = linear step, `2` = two-branch input merge).
pub const MAX_MERKLE_PARENTS: u64 = 2;

const MERKLE_NODE_DOMAIN: &[u8] = b"astream.engine.merkle.node.v1\0";
const MERKLE_EMPTY_DOMAIN: &[u8] = b"astream.engine.merkle.empty.v1\0";

const RECORD_TAG_IN: u8 = 1;
const RECORD_TAG_OUT: u8 = 2;
const RECORD_TAG_RESIZE: u8 = 3;
const RECORD_TAG_EXIT: u8 = 4;

/// A 32-byte domain-separated SHA-256 commit digest in a [`MerkleChain`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CommitHash(pub [u8; 32]);

impl CommitHash {
    /// Domain-separated root digest representing an empty session history (`0` commits).
    #[must_use]
    pub const fn empty_tree() -> Self {
        Self(Sha256::digest_slice(MERKLE_EMPTY_DOMAIN))
    }

    /// Borrow the raw 32-byte digest.
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Constant-time digest comparison (`astream_digest::ct_eq`).
    #[must_use]
    pub fn ct_eq(&self, other: &Self) -> bool {
        ct_eq(&self.0, &other.0)
    }

    /// Lowercase 64-character hexadecimal representation.
    #[must_use]
    pub fn to_hex(&self) -> String {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut out = String::new();
        for &byte in &self.0 {
            let hi = usize::from((byte >> 4) & 0x0f);
            let lo = usize::from(byte & 0x0f);
            let hc = HEX.get(hi).copied().unwrap_or(b'0') as char;
            let lc = HEX.get(lo).copied().unwrap_or(b'0') as char;
            out.push(hc);
            out.push(lc);
        }
        out
    }
}

impl std::fmt::Debug for CommitHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::from("CommitHash(");
        s.push_str(&self.to_hex());
        s.push(')');
        f.write_str(&s)
    }
}

impl std::fmt::Display for CommitHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_hex())
    }
}

/// Compute the canonical domain-separated [`CommitHash`] of `(parents, envelope)`.
///
/// Every variable-length slice is preceded by an explicit fixed-width tag and
/// 64-bit little-endian byte count, so distinct `(parents, envelope)` pairs map
/// injectively into the SHA-256 input stream.
#[must_use]
pub fn compute_node_hash(parents: &[CommitHash], env: &Envelope) -> CommitHash {
    let mut h = Sha256::new();
    h.update_slice(MERKLE_NODE_DOMAIN);
    h.update_slice(&env.seq.0.to_le_bytes());
    h.update_slice(&env.ts_logical.to_le_bytes());

    let clamped = merkle_parent_count_clamp(parents.len() as u64, MAX_MERKLE_PARENTS);
    let take_parents = usize::try_from(clamped).unwrap_or(0);
    h.update_slice(&[clamped as u8]);
    let mut p_idx = 0usize;
    while p_idx < take_parents {
        if let Some(parent) = parents.get(p_idx) {
            h.update_slice(parent.as_bytes());
        }
        p_idx = p_idx.saturating_add(1);
    }

    match env.caused_by {
        None => h.update_slice(&[0]),
        Some(CausedBy {
            partition: None,
            offset,
        }) => {
            h.update_slice(&[1]);
            h.update_slice(&offset.to_le_bytes());
            h.update_slice(&[0]);
        }
        Some(CausedBy {
            partition: Some(part),
            offset,
        }) => {
            h.update_slice(&[1]);
            h.update_slice(&offset.to_le_bytes());
            h.update_slice(&[1]);
            h.update_slice(&part.to_le_bytes());
        }
    }

    match &env.record {
        Record::In {
            bytes,
            client_id,
            client_seq,
        } => {
            h.update_slice(&[RECORD_TAG_IN]);
            h.update_slice(&client_id.to_le_bytes());
            h.update_slice(&client_seq.to_le_bytes());
            h.update_slice(&(bytes.len() as u64).to_le_bytes());
            h.update_slice(bytes);
        }
        Record::Out(bytes) => {
            h.update_slice(&[RECORD_TAG_OUT]);
            h.update_slice(&(bytes.len() as u64).to_le_bytes());
            h.update_slice(bytes);
        }
        Record::Resize { cols, rows } => {
            h.update_slice(&[RECORD_TAG_RESIZE]);
            h.update_slice(&cols.to_le_bytes());
            h.update_slice(&rows.to_le_bytes());
        }
        Record::Exit { code } => {
            h.update_slice(&[RECORD_TAG_EXIT]);
            h.update_slice(&code.to_le_bytes());
        }
    }

    CommitHash(h.finalize())
}

/// Which side of a two-branch merge violated a [`MerkleChain`] invariant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeSide {
    /// Left branch passed to [`merge_input_branches`].
    Left,
    /// Right branch passed to [`merge_input_branches`].
    Right,
}

/// Why constructing, verifying, or merging a [`MerkleChain`] failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MerkleError {
    /// Decoded or supplied envelope offset did not match the dense `0..N` commit spine.
    NonDenseOffset {
        /// Expected dense offset.
        expected: u64,
        /// Offset stamped on the envelope.
        found: u64,
    },
    /// A node declared more than [`MAX_MERKLE_PARENTS`] parents, or `> 0` parents at
    /// offset `0`, or `0` parents above offset `0`.
    InvalidParentCount {
        /// Offset of the offending node.
        at: u64,
        /// Declared parent count.
        count: usize,
    },
    /// A node's primary parent `parents[0]` did not match the preceding commit's hash.
    BrokenParentLink {
        /// Offset of the offending node.
        at: u64,
    },
    /// Recomputing a node's SHA-256 commit digest disagreed with its stored `hash`.
    HashMismatch {
        /// Offset of the tampered node.
        at: u64,
    },
    /// Stored log bytes failed [`Log::read_bytes`] decoding or ended in a torn frame.
    Decode(ReadError),
    /// [`merge_input_branches`] encountered a non-[`Record::In`] record in a divergent
    /// suffix (`docs/DESIGN-astream-term.md` §9: merge is valid only on input logs).
    DivergentNonInput {
        /// Branch holding the non-input record.
        side: MergeSide,
        /// Offset in that branch.
        offset: u64,
        /// Record kind (`"Out"`, `"Resize"`, or `"Exit"`).
        kind: &'static str,
    },
    /// Two divergent [`Record::In`] branches carried the same `(client_id, client_seq)`
    /// with different payload bytes (equivocation rather than idempotent retry).
    ConflictingInputSeq {
        /// Equivocating client identifier.
        client_id: u64,
        /// Equivocating client sequence number.
        client_seq: u64,
    },
}

impl std::fmt::Display for MerkleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            MerkleError::NonDenseOffset { expected, found } => {
                format!("merkle chain offset mismatch: expected {expected}, found {found}")
            }
            MerkleError::InvalidParentCount { at, count } => {
                format!("invalid merkle parent count {count} at offset {at}")
            }
            MerkleError::BrokenParentLink { at } => {
                format!("broken merkle parent link at offset {at}")
            }
            MerkleError::HashMismatch { at } => {
                format!("merkle commit hash mismatch at offset {at}")
            }
            MerkleError::Decode(e) => format!("merkle log decode error: {e}"),
            MerkleError::DivergentNonInput { side, offset, kind } => {
                let which = match side {
                    MergeSide::Left => "left",
                    MergeSide::Right => "right",
                };
                format!(
                    "cannot merge non-input {kind} record on {which} branch at offset {offset} (merge is valid only on input logs)"
                )
            }
            MerkleError::ConflictingInputSeq {
                client_id,
                client_seq,
            } => format!(
                "conflicting input bytes for (client_id={client_id}, client_seq={client_seq}) across merged branches"
            ),
        };
        f.write_str(&msg)
    }
}

impl std::error::Error for MerkleError {}

/// One content-addressed commit in a [`MerkleChain`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleNode {
    /// Dense session offset (`0..len`).
    pub seq: Offset,
    /// Domain-separated SHA-256 commit digest over `parents` and `envelope`.
    pub hash: CommitHash,
    /// Parent commit hashes (`[]` at offset `0`, `[prev]` for linear commits, or
    /// `[left_tip, right_tip]` at the first merged commit after [`merge_input_branches`]).
    /// Note that when merging two non-empty branches diverged from genesis (`lca == None`),
    /// the first merged commit at offset `0` carries `[left_tip, right_tip]` (`2` parents).
    pub parents: Vec<CommitHash>,
    /// Underlying session envelope.
    pub envelope: Envelope,
}

/// Content-addressed Merkle-DAG commit chain over a session's [`Envelope`] history.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleChain {
    nodes: Vec<MerkleNode>,
}

/// Tree-diff between two [`MerkleChain`] histories sharing a (possibly empty) prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleDiff {
    /// Lowest common ancestor `(offset, hash)` if the chains share at least 1 commit.
    pub lca: Option<(Offset, CommitHash)>,
    /// Number of shared prefix commits (`0` when `lca.is_none()`).
    pub shared_len: usize,
    /// Divergent suffix commits unique to the left chain (`left[shared_len..]`).
    pub left_only: Vec<MerkleNode>,
    /// Divergent suffix commits unique to the right chain (`right[shared_len..]`).
    pub right_only: Vec<MerkleNode>,
}

const fn record_kind_name(record: &Record) -> &'static str {
    match record {
        Record::In { .. } => "In",
        Record::Out(_) => "Out",
        Record::Resize { .. } => "Resize",
        Record::Exit { .. } => "Exit",
    }
}

impl MerkleChain {
    /// An empty [`MerkleChain`] with zero commits (head digest [`CommitHash::empty_tree`]).
    #[must_use]
    pub const fn empty() -> Self {
        Self { nodes: Vec::new() }
    }

    /// Build a linear hash-linked [`MerkleChain`] from a dense slice of [`Envelope`]s.
    pub fn from_envelopes(envelopes: &[Envelope]) -> Result<Self, MerkleError> {
        let mut nodes: Vec<MerkleNode> = Vec::new();
        let mut prev_hash: Option<CommitHash> = None;
        let mut expected = 0u64;

        for env in envelopes {
            if !merkle_offset_matches(expected, env.seq.0) {
                return Err(MerkleError::NonDenseOffset {
                    expected,
                    found: env.seq.0,
                });
            }
            let mut parents = Vec::new();
            if let Some(p) = prev_hash {
                parents.push(p);
            }
            let hash = compute_node_hash(&parents, env);
            prev_hash = Some(hash);
            nodes.push(MerkleNode {
                seq: env.seq,
                hash,
                parents,
                envelope: env.clone(),
            });
            expected = expected.saturating_add(1);
        }

        Ok(Self { nodes })
    }

    /// Decode framed [`Envelope`]s from stored log bytes via [`Log::read_bytes`] and
    /// construct their [`MerkleChain`]. Refuses corrupt frames, bad envelopes, offset
    /// gaps, and unrecovered torn tails. After validating the complete log, decoded
    /// envelopes move into their nodes without cloning their record bodies.
    pub fn from_log_bytes(bytes: &[u8]) -> Result<Self, MerkleError> {
        let mut reader = Log::read_bytes(bytes, Offset::ZERO);
        let mut envelopes = Vec::new();
        for item in &mut reader {
            match item {
                Ok(env) => envelopes.push(env),
                Err(e) => return Err(MerkleError::Decode(e)),
            }
        }
        if let Some(at) = reader.incomplete_at() {
            return Err(MerkleError::Decode(ReadError::Incomplete { at }));
        }
        Ok(Self::from_log_envelopes(envelopes))
    }

    /// Consume a fully validated log's records. Keeping node construction out of
    /// the decoder preserves its small rejection path as well as body ownership.
    #[inline(never)]
    fn from_log_envelopes(envelopes: Vec<Envelope>) -> Self {
        // Validate before hashing, as before, so a late malformed tail does not
        // incur hashing work for the valid prefix. Consuming the decoded values
        // transfers each body allocation instead of retaining and cloning it.
        let mut nodes: Vec<MerkleNode> = Vec::with_capacity(envelopes.len());
        let mut prev_hash: Option<CommitHash> = None;
        for env in envelopes {
            let mut parents = Vec::new();
            if let Some(prev) = prev_hash {
                parents.push(prev);
            }
            let hash = compute_node_hash(&parents, &env);
            prev_hash = Some(hash);
            nodes.push(MerkleNode {
                seq: env.seq,
                hash,
                parents,
                envelope: env,
            });
        }
        Self { nodes }
    }

    /// Number of commits in this chain.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether this chain has zero commits.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Borrow all commit nodes in offset order.
    #[must_use]
    pub fn nodes(&self) -> &[MerkleNode] {
        &self.nodes
    }

    /// Tip [`CommitHash`] (`CommitHash::empty_tree()` when empty).
    #[must_use]
    pub fn head_hash(&self) -> CommitHash {
        match self.nodes.last() {
            Some(last) => last.hash,
            None => CommitHash::empty_tree(),
        }
    }

    /// Verify every commit's dense offset, parent count, primary hash-chain link,
    /// and constant-time SHA-256 [`CommitHash`] integrity from genesis to head.
    pub fn verify(&self) -> Result<(), MerkleError> {
        let mut expected = 0u64;
        let mut prev_hash: Option<CommitHash> = None;

        for node in &self.nodes {
            if !merkle_offset_matches(expected, node.seq.0)
                || !merkle_offset_matches(expected, node.envelope.seq.0)
            {
                return Err(MerkleError::NonDenseOffset {
                    expected,
                    found: node.envelope.seq.0,
                });
            }
            let pcount = node.parents.len();
            if pcount as u64 > MAX_MERKLE_PARENTS {
                return Err(MerkleError::InvalidParentCount {
                    at: expected,
                    count: pcount,
                });
            }
            if expected == 0 {
                // Offset 0 is either a linear genesis (`0` parents) or a 2-parent merge
                // of two branches that diverged at offset 0 (`2` parents).
                if pcount == 1 {
                    return Err(MerkleError::InvalidParentCount {
                        at: 0,
                        count: pcount,
                    });
                }
            } else {
                // Every commit above offset 0 has at least 1 parent, and `parents[0]`
                // links to the preceding commit in this chain (unless it is a 2-parent
                // merge commit at `shared_len`, whose `parents` are `[left_tip, right_tip]`,
                // both descendants of `prev_hash`!).
                if pcount == 0 {
                    return Err(MerkleError::InvalidParentCount {
                        at: expected,
                        count: 0,
                    });
                }
                if pcount == 1 {
                    let (Some(first_parent), Some(prev)) = (node.parents.first(), prev_hash) else {
                        return Err(MerkleError::BrokenParentLink { at: expected });
                    };
                    if !first_parent.ct_eq(&prev) {
                        return Err(MerkleError::BrokenParentLink { at: expected });
                    }
                }
            }
            let recomputed = compute_node_hash(&node.parents, &node.envelope);
            if !recomputed.ct_eq(&node.hash) {
                return Err(MerkleError::HashMismatch { at: expected });
            }
            prev_hash = Some(node.hash);
            expected = expected.saturating_add(1);
        }
        Ok(())
    }

    /// Extract the underlying [`Envelope`] sequence, e.g. to feed into [`crate::Session`]
    /// or re-encode onto a [`Log`].
    #[must_use]
    pub fn to_envelopes(&self) -> Vec<Envelope> {
        let mut out = Vec::new();
        for node in &self.nodes {
            out.push(node.envelope.clone());
        }
        out
    }
}

#[cfg(test)]
#[path = "merkle_stream_tests.rs"]
mod merkle_stream_tests;

/// Find the lowest common ancestor `(offset, hash)` of `left` and `right` along
/// their verified hash-linked commit spines.
#[must_use]
pub fn lca(left: &MerkleChain, right: &MerkleChain) -> Option<(Offset, CommitHash)> {
    let mut idx = 0usize;
    let mut best: Option<(Offset, CommitHash)> = None;
    while let (Some(ln), Some(rn)) = (left.nodes.get(idx), right.nodes.get(idx)) {
        if !ln.hash.ct_eq(&rn.hash) {
            break;
        }
        best = Some((ln.seq, ln.hash));
        idx = idx.saturating_add(1);
    }
    best
}

/// Compute the structural tree-diff ([`MerkleDiff`]) between `left` and `right`.
#[must_use]
pub fn diff_chains(left: &MerkleChain, right: &MerkleChain) -> MerkleDiff {
    let ancestor = lca(left, right);
    let shared_len = match ancestor {
        Some((off, _)) => usize::try_from(off.0)
            .unwrap_or(usize::MAX)
            .saturating_add(1),
        None => 0,
    };
    let mut left_only = Vec::new();
    if let Some(tail) = left.nodes.get(shared_len..) {
        for n in tail {
            left_only.push(n.clone());
        }
    }
    let mut right_only = Vec::new();
    if let Some(tail) = right.nodes.get(shared_len..) {
        for n in tail {
            right_only.push(n.clone());
        }
    }
    MerkleDiff {
        lca: ancestor,
        shared_len,
        left_only,
        right_only,
    }
}

#[derive(Clone, PartialEq, Eq)]
struct PendingInput {
    ts_logical: u64,
    client_id: u64,
    client_seq: u64,
    caused_by: Option<CausedBy>,
    bytes: Vec<u8>,
}

fn collect_divergent_inputs(
    nodes: &[MerkleNode],
    side: MergeSide,
    seen: &mut BTreeMap<(u64, u64), PendingInput>,
) -> Result<(), MerkleError> {
    for node in nodes {
        match &node.envelope.record {
            Record::In {
                bytes,
                client_id,
                client_seq,
            } => {
                let key = (*client_id, *client_seq);
                if let Some(existing) = seen.get(&key) {
                    if existing.bytes != *bytes {
                        return Err(MerkleError::ConflictingInputSeq {
                            client_id: *client_id,
                            client_seq: *client_seq,
                        });
                    }
                    // Idempotent retry across branches: keep the earlier `ts_logical`.
                    if node.envelope.ts_logical < existing.ts_logical {
                        seen.insert(
                            key,
                            PendingInput {
                                ts_logical: node.envelope.ts_logical,
                                client_id: *client_id,
                                client_seq: *client_seq,
                                caused_by: node.envelope.caused_by,
                                bytes: bytes.clone(),
                            },
                        );
                    }
                } else {
                    seen.insert(
                        key,
                        PendingInput {
                            ts_logical: node.envelope.ts_logical,
                            client_id: *client_id,
                            client_seq: *client_seq,
                            caused_by: node.envelope.caused_by,
                            bytes: bytes.clone(),
                        },
                    );
                }
            }
            other => {
                return Err(MerkleError::DivergentNonInput {
                    side,
                    offset: node.seq.0,
                    kind: record_kind_name(other),
                });
            }
        }
    }
    Ok(())
}

/// Merge two verified session [`MerkleChain`] branches under §9's input-only merge law:
///
/// 1. Both chains are verified via [`MerkleChain::verify`].
/// 2. If one chain is an exact prefix of the other, its divergent suffix is checked
///    to contain only [`Record::In`] commits and the fast-forwarded chain is returned.
/// 3. Otherwise, every commit in `left_only` and `right_only` must be [`Record::In`]
///    (any `Out`, `Resize`, or `Exit` returns [`MerkleError::DivergentNonInput`]).
/// 4. Divergent [`Record::In`] commits are deduplicated by `(client_id, client_seq)`
///    (rejecting payload equivocation with [`MerkleError::ConflictingInputSeq`]),
///    canonically ordered by `(ts_logical, client_id, client_seq)`, and appended onto
///    the shared prefix with the first merged commit recording `[left.head_hash(), right.head_hash()]`
///    as its two Merkle-DAG parents.
pub fn merge_input_branches(
    left: &MerkleChain,
    right: &MerkleChain,
) -> Result<MerkleChain, MerkleError> {
    left.verify()?;
    right.verify()?;

    let diff = diff_chains(left, right);
    if diff.left_only.is_empty() && diff.right_only.is_empty() {
        return Ok(left.clone());
    }

    let mut seen: BTreeMap<(u64, u64), PendingInput> = BTreeMap::new();
    collect_divergent_inputs(&diff.left_only, MergeSide::Left, &mut seen)?;
    collect_divergent_inputs(&diff.right_only, MergeSide::Right, &mut seen)?;

    // Fast-forward when one branch adds pure `Record::In` commits onto the other.
    if diff.left_only.is_empty() {
        return Ok(right.clone());
    }
    if diff.right_only.is_empty() {
        return Ok(left.clone());
    }

    let mut ordered: Vec<PendingInput> = Vec::new();
    for item in seen.into_values() {
        ordered.push(item);
    }
    ordered.sort_by(|a, b| {
        a.ts_logical
            .cmp(&b.ts_logical)
            .then_with(|| a.client_id.cmp(&b.client_id))
            .then_with(|| a.client_seq.cmp(&b.client_seq))
    });

    let mut merged_nodes: Vec<MerkleNode> = Vec::new();
    if let Some(prefix) = left.nodes.get(..diff.shared_len) {
        for n in prefix {
            merged_nodes.push(n.clone());
        }
    }

    let left_tip = left.head_hash();
    let right_tip = right.head_hash();
    // Canonical symmetric parent ordering (`min, max`) when tips differ so
    // `merge_input_branches(left, right) == merge_input_branches(right, left)`!
    let merge_parents = if left_tip <= right_tip {
        vec![left_tip, right_tip]
    } else {
        vec![right_tip, left_tip]
    };

    let mut next_seq = diff.shared_len as u64;
    let mut prev_hash: Option<CommitHash> = merged_nodes.last().map(|n| n.hash);
    let mut is_first_merged = true;

    for inp in ordered {
        // Any same-log `caused_by` pointing into a branch-local offset at or above
        // `shared_len` is cleared unless it named the shared prefix (`< shared_len`),
        // keeping causal pointers valid on the merged offset spine.
        let caused_by = match inp.caused_by {
            Some(
                cb @ CausedBy {
                    partition: None, ..
                },
            ) if cb.offset >= diff.shared_len as u64 => None,
            other => other,
        };
        let env = Envelope {
            seq: Offset(next_seq),
            ts_logical: inp.ts_logical,
            caused_by,
            record: Record::In {
                bytes: inp.bytes,
                client_id: inp.client_id,
                client_seq: inp.client_seq,
            },
        };
        let parents = if is_first_merged {
            is_first_merged = false;
            merge_parents.clone()
        } else {
            let mut p = Vec::new();
            if let Some(ph) = prev_hash {
                p.push(ph);
            }
            p
        };
        let hash = compute_node_hash(&parents, &env);
        prev_hash = Some(hash);
        merged_nodes.push(MerkleNode {
            seq: Offset(next_seq),
            hash,
            parents,
            envelope: env,
        });
        next_seq = next_seq.saturating_add(1);
    }

    Ok(MerkleChain {
        nodes: merged_nodes,
    })
}
