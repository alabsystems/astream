// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Step-DAG durable execution (`docs/ROADMAP.md` "step-DAG workflows",
//! `docs/DESIGN-astream-term.md` §13).
//!
//! Generalizes [`crate::WorkflowJournal`] from a linear `0..total` spine to an
//! arbitrary directed acyclic graph ([`DagSpec`]) of steps with explicit parent
//! dependencies (`deps: Vec<u64>`).
//!
//! ## Guarantees
//!
//! 1. **Fail-closed static validation ([`DagSpec::new`]):** verifies dense node IDs
//!    `0..N`, rejects self-dependencies, unknown dependencies, duplicate edges, and
//!    any cycle via Kahn's deterministic lexicographic topological sort
//!    ([`DagError::Cycle`]).
//! 2. **SHA-256 dependency-set binding:** each node's canonical `(id, sorted_deps)`
//!    digest is written inside its `ADAG` v1 step frame on disk. Reopening a journal
//!    under a modified [`DagSpec`] whose edges drifted for an already-committed node
//!    fails closed with `InvalidData` (`DagFault::SpecMismatch`) rather than silently
//!    consuming stale parent outputs.
//! 3. **Crash-resumable Strict durability ([`DagJournal`]):** built over
//!    [`astream_wire::steps`] and [`crate::store`]'s Strict `fsync`-per-append log-file
//!    primitives (`open_log_file`, `append_frame`, `truncate_to`). A torn final frame
//!    from a crash mid-commit is durably truncated on [`DagJournal::open`]; a
//!    mid-journal fault or topological/spec violation is refused unless repaired
//!    explicitly via [`DagJournal::open_truncating`].

use crate::store::{self, FaultKind, LogFault, RecoverReport, Tail};
use astream_digest::{ct_eq, Sha256};
use astream_wire::steps::{self, StepEnd};
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "dag_island.rs"]
mod dag_island;
#[cfg(not(clean_islands))]
pub use crate::twins::dag_committed_advance;
#[cfg(clean_islands)]
pub use dag_island::dag_committed_advance;

contract_fn! {
    /// Kernel-certified readiness predicate: a DAG node is ready to execute iff its
    /// count of uncommitted parent dependencies `unsatisfied_deps` is `0`.
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `dag_deps_satisfied_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn dag_deps_satisfied(unsatisfied_deps: u64) -> bool
    clauses [ensures result == (unsatisfied_deps == 0)]
    {
        unsatisfied_deps == 0
    }
}

/// Four-byte magic prefix (`"ADAG"`) inside each step-DAG journal record payload.
pub const DAG_RECORD_MAGIC: [u8; 4] = *b"ADAG";
/// Format version for `ADAG` step-DAG journal records.
pub const DAG_RECORD_VERSION: u8 = 1;
/// Fixed header size of an `ADAG` v1 record: `magic(4) + version(1) + node_id(8) + dep_digest(32)`.
pub const DAG_HEADER_LEN: usize = 45;

const DAG_NODE_DIGEST_DOMAIN: &[u8] = b"astream.engine.dag.node.v1\0";

/// Declaration of one node in a [`DagSpec`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DagStep {
    /// Dense node identifier (`0..N`).
    pub id: u64,
    /// Upstream parent node IDs that must commit before `id` runs.
    pub deps: Vec<u64>,
}

impl DagStep {
    /// Construct a [`DagStep`] with `id` and `deps`.
    #[must_use]
    pub fn new(id: u64, deps: Vec<u64>) -> Self {
        Self { id, deps }
    }
}

/// Why a [`DagSpec`] failed static validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DagError {
    /// Step at slice position `expected` carried `found != expected`.
    NonDenseId {
        /// Expected dense node ID.
        expected: u64,
        /// Declared `step.id`.
        found: u64,
    },
    /// Node listed itself in `deps`.
    SelfDependency {
        /// Offending node ID.
        step: u64,
    },
    /// Node referenced a parent ID `>= steps.len()`.
    UnknownDependency {
        /// Offending node ID.
        step: u64,
        /// Out-of-range dependency ID.
        dep: u64,
    },
    /// Node listed the same parent `dep` more than once.
    DuplicateDependency {
        /// Offending node ID.
        step: u64,
        /// Repeated dependency ID.
        dep: u64,
    },
    /// Graph contains one or more directed cycles; `remaining_nodes` lists the
    /// nodes whose in-degree never reached zero under Kahn's algorithm.
    Cycle {
        /// Node IDs participating in or blocked by a cycle, in ascending ID order.
        remaining_nodes: Vec<u64>,
    },
}

impl std::fmt::Display for DagError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            DagError::NonDenseId { expected, found } => {
                format!("non-dense DAG step id: expected {expected}, found {found}")
            }
            DagError::SelfDependency { step } => {
                format!("DAG step {step} depends on itself")
            }
            DagError::UnknownDependency { step, dep } => {
                format!("DAG step {step} depends on unknown step {dep}")
            }
            DagError::DuplicateDependency { step, dep } => {
                format!("DAG step {step} lists duplicate dependency {dep}")
            }
            DagError::Cycle { remaining_nodes } => {
                format!("DAG contains a cycle involving steps {remaining_nodes:?}")
            }
        };
        f.write_str(&msg)
    }
}

impl std::error::Error for DagError {}

fn compute_node_dep_digest(id: u64, sorted_deps: &[u64]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update_slice(DAG_NODE_DIGEST_DOMAIN);
    h.update_slice(&id.to_le_bytes());
    h.update_slice(&(sorted_deps.len() as u64).to_le_bytes());
    for &dep in sorted_deps {
        h.update_slice(&dep.to_le_bytes());
    }
    h.finalize()
}

/// Kahn's lexicographic topological sort. A node enters the minimum heap once,
/// when its final parent is placed, and leaves it once. Selection costs
/// O(nodes * log(nodes) + edges), rather than restarting a scan at node zero for
/// every placement. Validation has already excluded duplicate edges and self-deps.
fn dag_topological_order(
    mut indegree: Vec<u64>,
    dependents: &[Vec<usize>],
) -> Result<Vec<u64>, DagError> {
    let n = indegree.len();
    let mut placed = vec![false; n];
    let mut ready: BinaryHeap<Reverse<usize>> = indegree
        .iter()
        .enumerate()
        .filter_map(|(node, &degree)| dag_deps_satisfied(degree).then_some(Reverse(node)))
        .collect();
    let mut topo_order = Vec::with_capacity(n);
    while let Some(Reverse(u)) = ready.pop() {
        if let Some(slot) = placed.get_mut(u) {
            *slot = true;
        }
        topo_order.push(u as u64);
        if let Some(children) = dependents.get(u) {
            for &child in children {
                if let Some(degree) = indegree.get_mut(child) {
                    if *degree > 0 {
                        *degree = degree.saturating_sub(1);
                        if dag_deps_satisfied(*degree) {
                            ready.push(Reverse(child));
                        }
                    }
                }
            }
        }
    }
    if topo_order.len() < n {
        let remaining_nodes = placed
            .iter()
            .enumerate()
            .filter_map(|(node, &is_placed)| (!is_placed).then_some(node as u64))
            .collect();
        return Err(DagError::Cycle { remaining_nodes });
    }
    Ok(topo_order)
}

/// Validated, acyclic step-DAG workflow specification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DagSpec {
    steps: Vec<DagStep>,
    topo_order: Vec<u64>,
    node_digests: Vec<[u8; 32]>,
}

impl DagSpec {
    /// Validate `steps` and precompute the deterministic lexicographic topological
    /// execution order and per-node SHA-256 dependency digests.
    pub fn new(steps: Vec<DagStep>) -> Result<Self, DagError> {
        let n = steps.len();
        let n_u64 = n as u64;

        let mut indegree: Vec<u64> = Vec::new();
        let mut dependents: Vec<Vec<usize>> = Vec::new();
        let mut node_digests: Vec<[u8; 32]> = Vec::new();

        let mut idx = 0usize;
        while idx < n {
            indegree.push(0);
            dependents.push(Vec::new());
            idx = idx.saturating_add(1);
        }

        for (pos, step) in steps.iter().enumerate() {
            let expected = pos as u64;
            if step.id != expected {
                return Err(DagError::NonDenseId {
                    expected,
                    found: step.id,
                });
            }
            let mut sorted_deps: Vec<u64> = Vec::new();
            for &dep in &step.deps {
                if dep == expected {
                    return Err(DagError::SelfDependency { step: expected });
                }
                if dep >= n_u64 {
                    return Err(DagError::UnknownDependency {
                        step: expected,
                        dep,
                    });
                }
                sorted_deps.push(dep);
            }
            sorted_deps.sort_unstable();
            let mut d_idx = 0usize;
            while d_idx.saturating_add(1) < sorted_deps.len() {
                if let (Some(&a), Some(&b)) = (
                    sorted_deps.get(d_idx),
                    sorted_deps.get(d_idx.saturating_add(1)),
                ) {
                    if a == b {
                        return Err(DagError::DuplicateDependency {
                            step: expected,
                            dep: a,
                        });
                    }
                }
                d_idx = d_idx.saturating_add(1);
            }

            if let Some(deg_slot) = indegree.get_mut(pos) {
                *deg_slot = sorted_deps.len() as u64;
            }
            for &dep in &sorted_deps {
                if let Ok(dep_usize) = usize::try_from(dep) {
                    if let Some(children) = dependents.get_mut(dep_usize) {
                        children.push(pos);
                    }
                }
            }
            node_digests.push(compute_node_dep_digest(expected, &sorted_deps));
        }

        let topo_order = dag_topological_order(indegree, &dependents)?;

        Ok(Self {
            steps,
            topo_order,
            node_digests,
        })
    }

    /// Number of nodes in the DAG.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.steps.len()
    }

    /// Borrow all [`DagStep`] declarations indexed by node ID (`0..node_count`).
    #[must_use]
    pub fn steps(&self) -> &[DagStep] {
        &self.steps
    }

    /// Deterministic lexicographic topological execution order (`0..node_count`).
    #[must_use]
    pub fn topological_order(&self) -> &[u64] {
        &self.topo_order
    }

    /// Domain-separated SHA-256 digest of `(node_id, sorted_deps)` for `node_id`.
    #[must_use]
    pub fn node_digest(&self, node_id: u64) -> Option<&[u8; 32]> {
        let idx = usize::try_from(node_id).ok()?;
        self.node_digests.get(idx)
    }

    /// Return all uncommitted node IDs (`0..node_count`) whose declared dependencies
    /// are all marked `true` in `completed`, in ascending node-ID order.
    #[must_use]
    pub fn ready_nodes(&self, completed: &[bool]) -> Vec<u64> {
        let mut ready = Vec::new();
        for (idx, step) in self.steps.iter().enumerate() {
            if completed.get(idx).copied().unwrap_or(false) {
                continue;
            }
            let mut unsatisfied = 0u64;
            for &dep in &step.deps {
                let dep_done = usize::try_from(dep)
                    .ok()
                    .and_then(|d| completed.get(d).copied())
                    .unwrap_or(false);
                if !dep_done {
                    unsatisfied = unsatisfied.saturating_add(1);
                }
            }
            if dag_deps_satisfied(unsatisfied) {
                ready.push(step.id);
            }
        }
        ready
    }
}

/// Encode an `ADAG` v1 step payload (`magic || version || node_id_le || dep_digest || output`).
#[must_use]
pub fn encode_dag_record(node_id: u64, dep_digest: &[u8; 32], output: &[u8]) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(&DAG_RECORD_MAGIC);
    buf.push(DAG_RECORD_VERSION);
    buf.extend_from_slice(&node_id.to_le_bytes());
    buf.extend_from_slice(dep_digest);
    buf.extend_from_slice(output);
    buf
}

/// Decode an `ADAG` v1 step payload into `(node_id, dep_digest, output)`.
#[must_use]
pub fn decode_dag_record(body: &[u8]) -> Option<(u64, [u8; 32], &[u8])> {
    let &[m0, m1, m2, m3, ver, n0, n1, n2, n3, n4, n5, n6, n7, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, ref output @ ..] =
        body
    else {
        return None;
    };
    if [m0, m1, m2, m3] != DAG_RECORD_MAGIC || ver != DAG_RECORD_VERSION {
        return None;
    }
    let node_id = (n0 as u64)
        | ((n1 as u64) << 8)
        | ((n2 as u64) << 16)
        | ((n3 as u64) << 24)
        | ((n4 as u64) << 32)
        | ((n5 as u64) << 40)
        | ((n6 as u64) << 48)
        | ((n7 as u64) << 56);
    let digest = [
        d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19,
        d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    ];
    Some((node_id, digest, output))
}

/// Why a committed `ADAG` journal entry failed [`DagSpec`] validation on reopen.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DagJournalFault {
    /// Step body did not carry a valid `ADAG` v1 header.
    MalformedRecord {
        /// Byte offset of the outer step frame.
        at: usize,
    },
    /// Committed `node_id` is outside `0..spec.node_count()`.
    UnknownNode {
        /// Byte offset of the outer step frame.
        at: usize,
        /// Stored `node_id`.
        node_id: u64,
    },
    /// Same `node_id` appeared twice in the journal.
    DuplicateNode {
        /// Byte offset of the duplicate outer step frame.
        at: usize,
        /// Duplicate `node_id`.
        node_id: u64,
    },
    /// Stored SHA-256 dependency digest did not match `spec.node_digest(node_id)`.
    SpecMismatch {
        /// Byte offset of the outer step frame.
        at: usize,
        /// Node whose dependency edges changed since commit.
        node_id: u64,
    },
    /// Node was committed before one of its declared parent dependencies `missing_dep`.
    TopologicalViolation {
        /// Byte offset of the outer step frame.
        at: usize,
        /// Offending child node.
        node_id: u64,
        /// Uncommitted parent dependency.
        missing_dep: u64,
    },
}

impl std::fmt::Display for DagJournalFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            DagJournalFault::MalformedRecord { at } => {
                format!("DAG journal fault at byte {at}: malformed ADAG record")
            }
            DagJournalFault::UnknownNode { at, node_id } => {
                format!("DAG journal fault at byte {at}: unknown node id {node_id}")
            }
            DagJournalFault::DuplicateNode { at, node_id } => {
                format!("DAG journal fault at byte {at}: duplicate commit for node {node_id}")
            }
            DagJournalFault::SpecMismatch { at, node_id } => {
                format!(
                    "DAG journal fault at byte {at}: dependency digest mismatch for node {node_id} (spec drifted since commit)"
                )
            }
            DagJournalFault::TopologicalViolation {
                at,
                node_id,
                missing_dep,
            } => format!(
                "DAG journal fault at byte {at}: node {node_id} committed before dependency {missing_dep}"
            ),
        };
        f.write_str(&msg)
    }
}

impl std::error::Error for DagJournalFault {}

impl DagJournalFault {
    fn into_io(self) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidData, self)
    }
}

///Compute the byte offset where each scanned step frame begins in `bytes`.
///
/// `steps::scan_steps_from` yields `body` byte ranges inside `bytes`. Each step frame
/// has `Frame::HEADER_LEN` (`9`) bytes + `steps::STEP_HEADER_LEN` (`13` = `1 + 8 + 4`)
/// bytes immediately before `body.start`, i.e. `frame_start == body.start - 22`.
const STEP_BODY_PREFIX_LEN: usize = 9 + 13;

/// Crash-resumable Strict step-DAG execution journal.
#[derive(Debug)]
pub struct DagJournal {
    file: File,
    len: u64,
    spec: DagSpec,
    outputs: Vec<Option<Vec<u8>>>,
    committed_order: Vec<u64>,
    /// Earliest topological position not yet passed by execution. Every earlier
    /// node is committed; later nodes may also be committed after recovery of an
    /// arbitrary valid order. Failed callbacks/encoding/appends leave it in place.
    next_topo: usize,
    poisoned: bool,
    recovery: RecoverReport,
}

impl DagJournal {
    /// Open (creating if absent) the step-DAG journal at `path` against `spec`,
    /// recovering the committed prefix and durably truncating any torn tail.
    ///
    /// Refuses mid-journal frame faults ([`LogFault`]) and `ADAG` spec/topological
    /// faults ([`DagJournalFault`]) without modifying the file.
    pub fn open(path: impl AsRef<Path>, spec: DagSpec) -> io::Result<Self> {
        Self::open_with(path.as_ref(), spec, false)
    }

    /// Operator repair: like [`open`](Self::open), but truncates durably at the first
    /// frame or `ADAG` fault so remaining nodes can be re-executed from that cut point.
    pub fn open_truncating(path: impl AsRef<Path>, spec: DagSpec) -> io::Result<Self> {
        Self::open_with(path.as_ref(), spec, true)
    }

    fn open_with(path: &Path, spec: DagSpec, truncate_faults: bool) -> io::Result<Self> {
        let mut file = store::open_log_file(path)?;
        let mut existing = Vec::new();
        file.read_to_end(&mut existing)?;

        let raw_scan = steps::scan_steps_from(&existing, 0);
        let wire_tail = store::tail_of(raw_scan.end.clone());
        if let Tail::Fault { at, kind } = &wire_tail {
            if !truncate_faults {
                return Err(LogFault {
                    at: *at,
                    kind: kind.clone(),
                }
                .into_io());
            }
        }

        let n = spec.node_count();
        let mut outputs: Vec<Option<Vec<u8>>> = Vec::new();
        let mut completed: Vec<bool> = Vec::new();
        let mut idx = 0usize;
        while idx < n {
            outputs.push(None);
            completed.push(false);
            idx = idx.saturating_add(1);
        }

        let mut committed_order: Vec<u64> = Vec::new();
        let mut valid_len = raw_scan.valid_len;
        let mut final_tail = wire_tail;

        for (_seq_idx, body_range) in &raw_scan.steps {
            let frame_at = body_range.start.saturating_sub(STEP_BODY_PREFIX_LEN);
            let body = existing.get(body_range.clone()).unwrap_or(&[]);
            let Some((node_id, found_digest, user_out)) = decode_dag_record(body) else {
                let fault = DagJournalFault::MalformedRecord { at: frame_at };
                if !truncate_faults {
                    return Err(fault.into_io());
                }
                valid_len = frame_at;
                final_tail = Tail::Fault {
                    at: frame_at,
                    kind: FaultKind::BadStep,
                };
                break;
            };

            let Ok(node_usize) = usize::try_from(node_id) else {
                let fault = DagJournalFault::UnknownNode {
                    at: frame_at,
                    node_id,
                };
                if !truncate_faults {
                    return Err(fault.into_io());
                }
                valid_len = frame_at;
                final_tail = Tail::Fault {
                    at: frame_at,
                    kind: FaultKind::BadStep,
                };
                break;
            };

            let Some(step_decl) = spec.steps().get(node_usize) else {
                let fault = DagJournalFault::UnknownNode {
                    at: frame_at,
                    node_id,
                };
                if !truncate_faults {
                    return Err(fault.into_io());
                }
                valid_len = frame_at;
                final_tail = Tail::Fault {
                    at: frame_at,
                    kind: FaultKind::BadStep,
                };
                break;
            };

            if completed.get(node_usize).copied().unwrap_or(false) {
                let fault = DagJournalFault::DuplicateNode {
                    at: frame_at,
                    node_id,
                };
                if !truncate_faults {
                    return Err(fault.into_io());
                }
                valid_len = frame_at;
                final_tail = Tail::Fault {
                    at: frame_at,
                    kind: FaultKind::BadStep,
                };
                break;
            }

            let Some(expected_digest) = spec.node_digest(node_id) else {
                return Err(DagJournalFault::UnknownNode {
                    at: frame_at,
                    node_id,
                }
                .into_io());
            };
            if !ct_eq(&found_digest, expected_digest) {
                let fault = DagJournalFault::SpecMismatch {
                    at: frame_at,
                    node_id,
                };
                if !truncate_faults {
                    return Err(fault.into_io());
                }
                valid_len = frame_at;
                final_tail = Tail::Fault {
                    at: frame_at,
                    kind: FaultKind::BadStep,
                };
                break;
            }

            let mut missing: Option<u64> = None;
            for &dep in &step_decl.deps {
                let dep_done = usize::try_from(dep)
                    .ok()
                    .and_then(|d| completed.get(d).copied())
                    .unwrap_or(false);
                if !dep_done {
                    missing = Some(dep);
                    break;
                }
            }
            if let Some(missing_dep) = missing {
                let fault = DagJournalFault::TopologicalViolation {
                    at: frame_at,
                    node_id,
                    missing_dep,
                };
                if !truncate_faults {
                    return Err(fault.into_io());
                }
                valid_len = frame_at;
                final_tail = Tail::Fault {
                    at: frame_at,
                    kind: FaultKind::BadStep,
                };
                break;
            }

            if let Some(c_slot) = completed.get_mut(node_usize) {
                *c_slot = true;
            }
            if let Some(o_slot) = outputs.get_mut(node_usize) {
                *o_slot = Some(user_out.to_vec());
            }
            committed_order.push(node_id);
        }

        let _ = StepEnd::Clean;
        store::truncate_to(&mut file, valid_len)?;
        let recovery = RecoverReport {
            valid_len,
            records: committed_order.len() as u64,
            torn: final_tail != Tail::Clean,
            tail: final_tail,
        };

        let mut next_topo = 0usize;
        let _ = next_dag_node(spec.topological_order(), &outputs, &mut next_topo);
        Ok(Self {
            file,
            len: valid_len as u64,
            spec,
            outputs,
            committed_order,
            next_topo,
            poisoned: false,
            recovery,
        })
    }

    /// Recovery report from opening this journal.
    #[must_use]
    pub fn recovery(&self) -> &RecoverReport {
        &self.recovery
    }

    /// Borrow the validated [`DagSpec`].
    #[must_use]
    pub fn spec(&self) -> &DagSpec {
        &self.spec
    }

    /// Number of DAG nodes durably committed so far.
    #[must_use]
    pub fn committed_count(&self) -> usize {
        self.committed_order.len()
    }

    /// Node IDs durably committed so far, in commit order.
    #[must_use]
    pub fn committed_order(&self) -> &[u64] {
        &self.committed_order
    }

    /// Whether `node_id` has already been durably committed.
    #[must_use]
    pub fn is_committed(&self, node_id: u64) -> bool {
        usize::try_from(node_id)
            .ok()
            .and_then(|idx| self.outputs.get(idx))
            .is_some_and(Option::is_some)
    }

    /// Borrow the committed output of `node_id`, if already committed.
    #[must_use]
    pub fn output(&self, node_id: u64) -> Option<&[u8]> {
        let idx = usize::try_from(node_id).ok()?;
        self.outputs.get(idx)?.as_deref()
    }

    /// Whether a write or fsync error has poisoned this handle (see
    /// [`crate::FileLog::is_poisoned`]); appends are refused until reopened.
    #[must_use]
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Uncommitted node IDs whose parent dependencies are all committed, in ascending
    /// node-ID order.
    #[must_use]
    pub fn ready_steps(&self) -> Vec<u64> {
        let mut completed = Vec::new();
        for slot in &self.outputs {
            completed.push(slot.is_some());
        }
        self.spec.ready_nodes(&completed)
    }

    /// Execute uncommitted DAG nodes in deterministic topological order until at most
    /// `target_committed` total nodes are durably committed on disk (clamped to
    /// `spec.node_count()`). Returns the total number of committed nodes after this pass.
    /// A poisoned journal refuses new execution before invoking `exec`; already-reached
    /// targets remain no-ops. Reopen the journal to recover before requesting more work.
    pub fn run_up_to<F>(&mut self, target_committed: u64, mut exec: F) -> io::Result<usize>
    where
        F: FnMut(u64, &[(u64, &[u8])]) -> Vec<u8>,
    {
        let max_nodes = self.spec.node_count() as u64;
        let clamped_target = if target_committed < max_nodes {
            target_committed
        } else {
            max_nodes
        };
        let target = dag_committed_advance(self.committed_order.len() as u64, clamped_target);
        let mut committed_nodes = self.committed_order.len() as u64;
        // A write or fsync error means this handle cannot durably append anything.
        // Refuse new execution before invoking user code or moving the cursor;
        // callers may still query an already-reached target without executing.
        if committed_nodes < target && self.poisoned {
            return Err(io::Error::other(store::Poisoned));
        }

        while committed_nodes < target {
            let Some(node_id) = next_dag_node(
                self.spec.topological_order(),
                &self.outputs,
                &mut self.next_topo,
            ) else {
                break;
            };
            let Ok(node_usize) = usize::try_from(node_id) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "DAG node id exceeds usize",
                ));
            };
            let Some(step_decl) = self.spec.steps().get(node_usize) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "DAG node missing from spec",
                ));
            };
            let Some(&dep_digest) = self.spec.node_digest(node_id) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "DAG node digest missing from spec",
                ));
            };

            let output = {
                let mut parent_inputs: Vec<(u64, &[u8])> = Vec::with_capacity(step_decl.deps.len());
                for &dep_id in &step_decl.deps {
                    let Some(dep_bytes) = usize::try_from(dep_id)
                        .ok()
                        .and_then(|d| self.outputs.get(d))
                        .and_then(|opt| opt.as_deref())
                    else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "topological order reached node with uncommitted dependency",
                        ));
                    };
                    parent_inputs.push((dep_id, dep_bytes));
                }
                exec(node_id, &parent_inputs)
            };

            let seq_idx = self.committed_order.len() as u64;
            let dag_body = encode_dag_record(node_id, &dep_digest, &output);
            let frame = steps::encode_step(seq_idx, &dag_body).map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidData, "DAG step output too large")
            })?;
            self.append(&frame)?;

            if let Some(slot) = self.outputs.get_mut(node_usize) {
                *slot = Some(output);
            }
            self.committed_order.push(node_id);
            self.next_topo = self.next_topo.saturating_add(1);
            committed_nodes =
                dag_committed_advance(committed_nodes, self.committed_order.len() as u64);
        }

        Ok(self.committed_order.len())
    }

    /// Execute all uncommitted nodes of the DAG in deterministic topological order,
    /// skipping every node already committed on disk and fsyncing each newly executed
    /// node's output before advancing.
    ///
    /// For each uncommitted `node_id`, `exec(node_id, &parent_outputs)` receives the
    /// committed `(dep_id, dep_bytes)` pairs in the exact order `step.deps` declared
    /// them. Returns all `spec.node_count()` outputs indexed by `node_id` (`0..N`).
    pub fn run<F>(&mut self, exec: F) -> io::Result<Vec<Vec<u8>>>
    where
        F: FnMut(u64, &[(u64, &[u8])]) -> Vec<u8>,
    {
        let total = self.spec.node_count() as u64;
        let _ = self.run_up_to(total, exec)?;
        let mut all_outputs: Vec<Vec<u8>> = Vec::new();
        for slot in &self.outputs {
            let Some(bytes) = slot else {
                return Err(io::Error::other("incomplete DAG outputs after run"));
            };
            all_outputs.push(bytes.clone());
        }
        Ok(all_outputs)
    }

    fn append(&mut self, frame_bytes: &[u8]) -> io::Result<()> {
        store::append_frame(&mut self.file, self.len, &mut self.poisoned, frame_bytes)?;
        self.len = self.len.saturating_add(frame_bytes.len() as u64);
        Ok(())
    }
}

/// Borrow the next uncommitted node without copying the topological order or
/// restarting its committed prefix. Across successful incremental calls, each
/// position is visited at most once (plus retry attempts at a failed node).
/// This traversal allocates nothing; the cursor itself is the only added state.
fn next_dag_node(topo: &[u64], outputs: &[Option<Vec<u8>>], cursor: &mut usize) -> Option<u64> {
    while let Some(&node) = topo.get(*cursor) {
        #[cfg(test)]
        cursor_tally::visit();
        if usize::try_from(node)
            .ok()
            .and_then(|idx| outputs.get(idx))
            .is_some_and(Option::is_some)
        {
            *cursor = cursor.saturating_add(1);
        } else {
            return Some(node);
        }
    }
    None
}

#[cfg(test)]
mod cursor_tally {
    use std::cell::Cell;

    thread_local! {
        static VISITS: Cell<usize> = const { Cell::new(0) };
    }

    pub(super) fn visit() {
        VISITS.with(|visits| visits.set(visits.get().saturating_add(1)));
    }

    pub(super) fn take() -> usize {
        VISITS.with(|visits| visits.replace(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The former scan selector, deliberately retained only as an independent
    /// schedule/cycle oracle and an equal-input manual benchmark reference.
    fn scan_topological_order(
        mut indegree: Vec<u64>,
        dependents: &[Vec<usize>],
    ) -> Result<Vec<u64>, DagError> {
        let n = indegree.len();
        // Kahn's deterministic lexicographic topological sort: at each round, pick the
        // smallest uncommitted node index `0..n` whose remaining indegree is 0.
        let mut placed: Vec<bool> = Vec::new();
        let mut p_idx = 0usize;
        while p_idx < n {
            placed.push(false);
            p_idx = p_idx.saturating_add(1);
        }

        let mut topo_order: Vec<u64> = Vec::new();
        let mut round = 0usize;
        while round < n {
            let mut chosen: Option<usize> = None;
            let mut cand = 0usize;
            while cand < n {
                let is_placed = placed.get(cand).copied().unwrap_or(true);
                let deg = indegree.get(cand).copied().unwrap_or(1);
                if !is_placed && dag_deps_satisfied(deg) {
                    chosen = Some(cand);
                    break;
                }
                cand = cand.saturating_add(1);
            }
            let Some(u) = chosen else {
                break;
            };
            if let Some(slot) = placed.get_mut(u) {
                *slot = true;
            }
            topo_order.push(u as u64);
            if let Some(children) = dependents.get(u) {
                for &child in children {
                    if let Some(deg_slot) = indegree.get_mut(child) {
                        *deg_slot = deg_slot.saturating_sub(1);
                    }
                }
            }
            round = round.saturating_add(1);
        }

        if topo_order.len() < n {
            let mut remaining_nodes = Vec::new();
            let mut c = 0usize;
            while c < n {
                if !placed.get(c).copied().unwrap_or(false) {
                    remaining_nodes.push(c as u64);
                }
                c = c.saturating_add(1);
            }
            return Err(DagError::Cycle { remaining_nodes });
        }
        Ok(topo_order)
    }

    fn graph(steps: &[DagStep]) -> (Vec<u64>, Vec<Vec<usize>>) {
        let mut dependents = vec![Vec::new(); steps.len()];
        for step in steps {
            for &parent in &step.deps {
                dependents[parent as usize].push(step.id as usize);
            }
        }
        let indegree = steps.iter().map(|step| step.deps.len() as u64).collect();
        (indegree, dependents)
    }

    #[test]
    fn heap_order_matches_scan_for_every_directed_four_node_graph() {
        for n in 0usize..=4 {
            let edge_slots = n * n.saturating_sub(1);
            for mask in 0u64..(1u64 << edge_slots) {
                let mut steps = Vec::new();
                let mut bit = 0usize;
                for node in 0..n {
                    let mut deps = Vec::new();
                    for parent in 0..n {
                        if parent == node {
                            continue;
                        }
                        if mask & (1u64 << bit) != 0 {
                            deps.push(parent as u64);
                        }
                        bit += 1;
                    }
                    // Dependency declaration order cannot change the selected order.
                    if node % 2 == 0 {
                        deps.reverse();
                    }
                    steps.push(DagStep::new(node as u64, deps));
                }
                let (indegree, dependents) = graph(&steps);
                let expected = scan_topological_order(indegree, &dependents);
                let actual = DagSpec::new(steps).map(|spec| spec.topo_order);
                assert_eq!(actual, expected, "nodes {n}, edge mask {mask:#x}");
            }
        }
    }

    #[test]
    fn newly_ready_lower_ids_preempt_larger_ready_nodes_without_reordering_parents() {
        let steps = vec![
            DagStep::new(0, vec![2]),
            DagStep::new(1, vec![2]),
            DagStep::new(2, vec![]),
            DagStep::new(3, vec![]),
            DagStep::new(4, vec![3, 1]),
        ];
        let mut reordered = steps.clone();
        reordered[4].deps.reverse();
        let spec = DagSpec::new(steps.clone()).unwrap();
        let canonical = DagSpec::new(reordered).unwrap();
        assert_eq!(spec.topological_order(), &[2, 0, 1, 3, 4]);
        assert_eq!(spec.steps(), steps.as_slice());
        assert_eq!(spec.steps()[4].deps, vec![3, 1]);
        assert_eq!(spec.node_digests, canonical.node_digests);
        assert_eq!(spec.topo_order, canonical.topo_order);
    }

    #[test]
    fn validation_error_precedence_and_blocked_cycle_nodes_are_preserved() {
        let cases = [
            (
                vec![DagStep::new(9, vec![0, 99])],
                DagError::NonDenseId {
                    expected: 0,
                    found: 9,
                },
            ),
            (
                vec![DagStep::new(0, vec![99, 0])],
                DagError::UnknownDependency { step: 0, dep: 99 },
            ),
            (
                vec![DagStep::new(0, vec![0, 99])],
                DagError::SelfDependency { step: 0 },
            ),
            (
                vec![DagStep::new(0, vec![1, 1, 99]), DagStep::new(1, vec![])],
                DagError::UnknownDependency { step: 0, dep: 99 },
            ),
            (
                vec![
                    DagStep::new(0, vec![2, 2, 1, 1]),
                    DagStep::new(1, vec![]),
                    DagStep::new(2, vec![]),
                ],
                DagError::DuplicateDependency { step: 0, dep: 1 },
            ),
            (
                vec![DagStep::new(0, vec![99]), DagStep::new(9, vec![])],
                DagError::UnknownDependency { step: 0, dep: 99 },
            ),
        ];
        for (steps, expected) in cases {
            assert_eq!(DagSpec::new(steps), Err(expected));
        }
        let blocked = vec![
            DagStep::new(0, vec![1]),
            DagStep::new(1, vec![0]),
            DagStep::new(2, vec![1]),
            DagStep::new(3, vec![]),
            DagStep::new(4, vec![5]),
            DagStep::new(5, vec![4]),
        ];
        assert_eq!(
            DagSpec::new(blocked),
            Err(DagError::Cycle {
                remaining_nodes: vec![0, 1, 2, 4, 5]
            })
        );
        let empty = DagSpec::new(Vec::new()).unwrap();
        assert_eq!(empty.node_count(), 0);
        assert!(empty.topological_order().is_empty());
    }

    /// Compare only selection, with the same prebuilt validated indegrees and
    /// outgoing edges. Neither side includes dependency validation or hashing.
    /// Run: targo --unverified test --locked --release -p astream-engine --lib
    ///      dag_selection_benchmark -- --ignored --nocapture
    #[test]
    #[ignore = "manual DAG selection scaling benchmark"]
    fn dag_selection_benchmark() {
        use std::hint::black_box;
        use std::time::Instant;

        for n in [4096usize, 8192, 16384] {
            for shape in ["independent", "ascending", "descending", "fanout", "fanin"] {
                let steps: Vec<_> = (0..n)
                    .map(|node| {
                        let deps = match shape {
                            "ascending" if node > 0 => vec![(node - 1) as u64],
                            "descending" if node + 1 < n => vec![(node + 1) as u64],
                            "fanout" if node + 1 < n => vec![(n - 1) as u64],
                            "fanin" if node == 0 => (1..n as u64).collect(),
                            _ => Vec::new(),
                        };
                        DagStep::new(node as u64, deps)
                    })
                    .collect();
                let (indegree, dependents) = graph(&steps);
                let mut heap_ns = [0u128; 3];
                let mut scan_ns = [0u128; 3];
                for run in 0..3 {
                    // Clone before timing both forms, and keep outputs alive until
                    // after their timers stop. Alternate order to reduce run bias.
                    let heap_input = indegree.clone();
                    let scan_input = indegree.clone();
                    let timed_heap = || {
                        let start = Instant::now();
                        let actual =
                            dag_topological_order(black_box(heap_input), black_box(&dependents));
                        heap_ns[run] = start.elapsed().as_nanos();
                        black_box(actual)
                    };
                    let timed_scan = || {
                        let start = Instant::now();
                        let expected =
                            scan_topological_order(black_box(scan_input), black_box(&dependents));
                        scan_ns[run] = start.elapsed().as_nanos();
                        black_box(expected)
                    };
                    let (actual, expected) = if run % 2 == 0 {
                        (timed_heap(), timed_scan())
                    } else {
                        let expected = timed_scan();
                        (timed_heap(), expected)
                    };
                    assert_eq!(actual, expected);
                }
                heap_ns.sort_unstable();
                scan_ns.sort_unstable();
                println!(
                    "DAG_SELECTION shape={shape} nodes={n} heap_ns={} scan_ns={} speedup={:.2}",
                    heap_ns[1],
                    scan_ns[1],
                    scan_ns[1] as f64 / heap_ns[1].max(1) as f64
                );
            }
        }
    }

    struct Scratch(std::path::PathBuf);

    impl Scratch {
        fn new() -> Self {
            use std::sync::atomic::{AtomicU64, Ordering};
            static NEXT: AtomicU64 = AtomicU64::new(0);
            for _ in 0..1024 {
                let path = std::env::temp_dir().join(format!(
                    "astream-dag-cursor-{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                match std::fs::create_dir(&path) {
                    Ok(()) => return Self(path),
                    Err(e) if e.kind() == io::ErrorKind::AlreadyExists => continue,
                    Err(e) => panic!("create scratch directory: {e}"),
                }
            }
            panic!("no exclusive scratch directory");
        }

        fn path(&self) -> std::path::PathBuf {
            self.0.join("dag.log")
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn cursor_spec() -> DagSpec {
        DagSpec::new(vec![
            DagStep::new(0, vec![2]),
            DagStep::new(1, vec![2]),
            DagStep::new(2, vec![]),
            DagStep::new(3, vec![]),
            DagStep::new(4, vec![3, 1]),
        ])
        .unwrap()
    }

    fn journal_output(node: u64, parents: &[(u64, &[u8])]) -> Vec<u8> {
        let mut output = vec![node as u8];
        for &(parent, bytes) in parents {
            output.push(parent as u8);
            output.extend_from_slice(bytes);
        }
        output
    }

    /// Build independently chosen valid journal histories through the public codec.
    fn journal_bytes(spec: &DagSpec, order: &[u64]) -> Vec<u8> {
        let mut outputs: Vec<Option<Vec<u8>>> = vec![None; spec.node_count()];
        let mut bytes = Vec::new();
        for (seq, &node) in order.iter().enumerate() {
            let parents: Vec<_> = spec.steps()[node as usize]
                .deps
                .iter()
                .map(|&parent| (parent, outputs[parent as usize].as_deref().unwrap()))
                .collect();
            let output = journal_output(node, &parents);
            let body = encode_dag_record(node, spec.node_digest(node).unwrap(), &output);
            bytes.extend_from_slice(&steps::encode_step(seq as u64, &body).unwrap());
            outputs[node as usize] = Some(output);
        }
        bytes
    }

    #[test]
    fn incremental_cursor_preserves_noncanonical_recovered_history_and_parent_order() {
        let scratch = Scratch::new();
        let spec = cursor_spec();
        // Valid dependencies, but not a prefix of canonical [2,0,1,3,4].
        let prefix = journal_bytes(&spec, &[3, 2, 1]);
        std::fs::write(scratch.path(), &prefix).unwrap();
        let mut journal = DagJournal::open(scratch.path(), spec.clone()).unwrap();
        assert_eq!(journal.next_topo, 1);
        assert_eq!(journal.committed_order(), &[3, 2, 1]);
        let _ = cursor_tally::take();
        let mut called = Vec::new();
        assert_eq!(
            journal
                .run_up_to(4, |node, parents| {
                    called.push(node);
                    journal_output(node, parents)
                })
                .unwrap(),
            4
        );
        assert_eq!(cursor_tally::take(), 1);
        assert_eq!(journal.next_topo, 2);
        assert_eq!(
            journal
                .run_up_to(0, |_, _| panic!("already beyond target"))
                .unwrap(),
            4
        );
        assert_eq!(cursor_tally::take(), 0);
        assert_eq!(
            journal
                .run_up_to(u64::MAX, |node, parents| {
                    called.push(node);
                    assert_eq!(node, 4);
                    assert_eq!(
                        parents.iter().map(|(id, _)| *id).collect::<Vec<_>>(),
                        vec![3, 1]
                    );
                    journal_output(node, parents)
                })
                .unwrap(),
            5
        );
        assert_eq!(cursor_tally::take(), 3); // Two recovered future nodes, then node4.
        assert_eq!(called, vec![0, 4]);
        assert_eq!(journal.committed_order(), &[3, 2, 1, 0, 4]);
        assert_eq!(
            std::fs::read(scratch.path()).unwrap(),
            journal_bytes(&spec, &[3, 2, 1, 0, 4])
        );
        drop(journal);
        let mut complete = DagJournal::open(scratch.path(), spec).unwrap();
        assert_eq!(complete.next_topo, 5);
        assert_eq!(
            complete
                .run_up_to(u64::MAX, |_, _| panic!("complete journal"))
                .unwrap(),
            5
        );
    }

    #[test]
    fn incremental_cursor_retries_the_same_node_after_callback_panic_and_encode_error() {
        use std::panic::{catch_unwind, AssertUnwindSafe};
        let scratch = Scratch::new();
        let spec = cursor_spec();
        let mut journal = DagJournal::open(scratch.path(), spec.clone()).unwrap();
        journal.run_up_to(1, journal_output).unwrap();
        let prefix = std::fs::read(scratch.path()).unwrap();
        let panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = journal.run_up_to(2, |node, _| {
                assert_eq!(node, 0);
                panic!("callback failed before append");
            });
        }));
        assert!(panic.is_err());
        assert_eq!(journal.next_topo, 1);
        assert_eq!(journal.committed_order(), &[2]);
        assert_eq!(std::fs::read(scratch.path()).unwrap(), prefix);
        let err = journal
            .run_up_to(2, |node, _| {
                assert_eq!(node, 0);
                vec![0; astream_wire::MAX_PAYLOAD_LEN]
            })
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert_eq!(journal.next_topo, 1);
        assert_eq!(journal.committed_order(), &[2]);
        assert!(!journal.is_poisoned());
        assert_eq!(std::fs::read(scratch.path()).unwrap(), prefix);
        for target in 2..=5 {
            journal.run_up_to(target, journal_output).unwrap();
        }
        assert_eq!(journal.committed_order(), spec.topological_order());
        assert_eq!(
            std::fs::read(scratch.path()).unwrap(),
            journal_bytes(&spec, spec.topological_order())
        );
    }

    #[test]
    fn failed_append_and_poison_refusal_do_not_advance_incremental_cursor() {
        let scratch = Scratch::new();
        let spec = cursor_spec();
        let mut journal = DagJournal::open(scratch.path(), spec.clone()).unwrap();
        journal.run_up_to(1, journal_output).unwrap();
        let prefix = std::fs::read(scratch.path()).unwrap();
        // The read-only replacement refuses both write and rollback. This exercises
        // the real failure/poison path without changing the durable prefix.
        journal.file = File::open(scratch.path()).unwrap();
        let mut callbacks = 0;
        let err = journal
            .run_up_to(2, |node, parents| {
                assert_eq!(node, 0);
                callbacks += 1;
                journal_output(node, parents)
            })
            .unwrap_err();
        assert!(err.to_string().contains("rollback failed"));
        assert!(journal.is_poisoned());
        assert_eq!(journal.next_topo, 1);
        assert_eq!(journal.committed_order(), &[2]);
        journal.file = store::open_log_file(&scratch.path()).unwrap();
        let _ = cursor_tally::take();
        assert_eq!(
            journal
                .run_up_to(0, |_, _| panic!("already-reached poisoned target"))
                .unwrap(),
            1
        );
        let err = journal
            .run_up_to(2, |node, parents| {
                assert_eq!(node, 0);
                callbacks += 1;
                journal_output(node, parents)
            })
            .unwrap_err();
        assert!(store::Poisoned::is(&err));
        // A known-poisoned handle must not repeat user effects that cannot commit.
        assert_eq!(callbacks, 1);
        assert_eq!(cursor_tally::take(), 0);
        assert_eq!(journal.next_topo, 1);
        assert_eq!(journal.committed_order(), &[2]);
        assert_eq!(std::fs::read(scratch.path()).unwrap(), prefix);
        drop(journal);
        let mut recovered = DagJournal::open(scratch.path(), spec.clone()).unwrap();
        assert_eq!(recovered.next_topo, 1);
        recovered.run(journal_output).unwrap();
        assert_eq!(
            std::fs::read(scratch.path()).unwrap(),
            journal_bytes(&spec, spec.topological_order())
        );
    }

    fn cursor_walk(topo: &[u64], outputs: &mut [Option<Vec<u8>>]) {
        let mut cursor = 0usize;
        for _ in 0..topo.len() {
            let node = next_dag_node(topo, outputs, &mut cursor).unwrap();
            outputs[node as usize] = Some(Vec::new());
            cursor += 1;
        }
        assert_eq!(cursor, topo.len());
    }

    fn restarting_walk(topo: &[u64], outputs: &mut [Option<Vec<u8>>]) -> (usize, usize) {
        let mut visits = 0usize;
        let mut copied_ids = 0usize;
        for _ in 0..topo.len() {
            // The former run_up_to cloned the entire order before every request.
            let order = std::hint::black_box(topo.to_vec());
            copied_ids += order.len();
            for node in order {
                visits += 1;
                if outputs[node as usize].is_none() {
                    outputs[node as usize] = Some(Vec::new());
                    break;
                }
            }
        }
        (visits, copied_ids)
    }

    #[test]
    fn incremental_traversal_visits_each_node_once_without_copying_the_order() {
        const N: usize = 4096;
        let topo: Vec<_> = (0..N as u64).rev().collect();
        let mut cursor_outputs = vec![None; N];
        let mut restarting_outputs = vec![None; N];
        let _ = cursor_tally::take();
        cursor_walk(&topo, &mut cursor_outputs);
        assert_eq!(cursor_tally::take(), N);
        let (visits, copied_ids) = restarting_walk(&topo, &mut restarting_outputs);
        assert_eq!(visits, N * (N + 1) / 2);
        assert_eq!(copied_ids, N * N);
        assert_eq!(cursor_outputs, restarting_outputs);
        assert_eq!(topo, (0..N as u64).rev().collect::<Vec<_>>());
    }

    /// CPU traversal only: outputs are marked in memory, with no encoding, callback,
    /// file writes or fsync. Both forms receive the same prebuilt order and state.
    #[test]
    #[ignore = "manual incremental DAG cursor benchmark"]
    fn dag_incremental_cursor_benchmark() {
        use std::hint::black_box;
        use std::time::Instant;
        for n in [4096usize, 8192, 16384] {
            let topo: Vec<_> = (0..n as u64).rev().collect();
            let mut cursor_ns = [0u128; 3];
            let mut restarting_ns = [0u128; 3];
            for run in 0..3 {
                let mut cursor_outputs = vec![None; n];
                let mut restarting_outputs = vec![None; n];
                let mut timed_cursor = || {
                    let start = Instant::now();
                    cursor_walk(black_box(&topo), black_box(&mut cursor_outputs));
                    cursor_ns[run] = start.elapsed().as_nanos();
                };
                let mut timed_restarting = || {
                    let start = Instant::now();
                    let work =
                        restarting_walk(black_box(&topo), black_box(&mut restarting_outputs));
                    restarting_ns[run] = start.elapsed().as_nanos();
                    work
                };
                let work = if run % 2 == 0 {
                    timed_cursor();
                    timed_restarting()
                } else {
                    let work = timed_restarting();
                    timed_cursor();
                    work
                };
                assert_eq!(cursor_outputs, restarting_outputs);
                assert_eq!(work, (n * (n + 1) / 2, n * n));
            }
            cursor_ns.sort_unstable();
            restarting_ns.sort_unstable();
            println!(
                "DAG_CURSOR nodes={n} cursor_ns={} restarting_ns={} speedup={:.2} cursor_visits={n} restarting_visits={} restarting_copied_bytes={}",
                cursor_ns[1], restarting_ns[1], restarting_ns[1] as f64 / cursor_ns[1].max(1) as f64,
                n * (n + 1) / 2, n * n * std::mem::size_of::<u64>()
            );
        }
    }
}
