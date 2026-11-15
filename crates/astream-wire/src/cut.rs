//! Chandy-Lamport consistent-cut lattice and causal-closure algebra over
//! multi-stream offset frontiers.
//!
//! [`astream-engine`](../astream_engine/index.html)'s `fleet.rs` (per-session envelope
//! logs indexed by `Partition(u64)`, whose `Cut` and `CrossEdge` delegate here) and
//! `astream-broker`'s `BrokerRecord::causal_edge_from` / `commit_causal_edge`
//! (per-subject broker streams keyed by `String` subjects and group names) coordinate
//! independent ordered streams connected by cross-stream causal edges
//! (`cause: (K, Offset) -> effect: (K, Offset)`). No aterm code calls this module:
//! aterm deleted its own consistent-cut auditor (aterm `06426ed3fa`).
//!
//! A [`CausalCut<K>`] assigns a frontier [`Offset`] to each stream `K`. By the
//! Chandy-Lamport distributed snapshot criterion (1985), a cut `C` is **causally
//! consistent** with respect to a set of cross-stream edges `E` iff every edge whose
//! effect lies inside `C` also has its cause inside `C`:
//!
//! ```text
//! ∀ ( (src, k) -> (dst, m) ) ∈ E :  m ≤ C[dst]  ⟹  k ≤ C[src]
//! ```
//!
//! Besides deciding consistency (`is_consistent`) and pinpointing the first
//! causal orphan (`first_violation`), [`CausalCut`] forms a bounded join-semilattice
//! (`join`, `meet`, `dominates`) and computes the minimal causal closure (`heal`)
//! that advances lagging source frontiers until every admitted effect's transitive
//! cause is included.

use crate::Offset;
use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "cut_island.rs"]
mod cut_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{causal_gate_frontier, heal_frontier_monotone, meet_frontier_monotone};
#[cfg(clean_islands)]
pub use cut_island::{causal_gate_frontier, heal_frontier_monotone, meet_frontier_monotone};

contract_fn! {
    /// Kernel-certified predicate deciding whether a stream frontier `upto` includes
    /// event offset `at_off` (`at_off <= upto`).
    #[must_use]
    pub const fn frontier_includes_raw(upto: u64, at_off: u64) -> bool
    clauses [ensures result == (at_off <= upto)]
    {
        at_off <= upto
    }
}

pub use frontier_includes_raw as frontier_includes;

/// 4-parameter Chandy-Lamport causal effect transition kernel: advances `eff_cur` to
/// `max(eff_cur, eff_cand)` once `cause_req <= cause_cut`, and keeps it otherwise.
///
/// Hand-written plain Rust, not compiled from Clean: it restates `causal_step_frontier_isl`,
/// the island's composition of the Clean-Origin (`I5`) [`causal_gate_frontier`] and
/// [`heal_frontier_monotone`] functions, and astream-broker's `clean_tla_protocol_surface`
/// suite holds it to that composition over a grid of boundary operands.
#[must_use]
pub const fn causal_step_frontier(
    cause_cut: u64,
    cause_req: u64,
    eff_cur: u64,
    eff_cand: u64,
) -> u64 {
    if cause_cut < cause_req {
        eff_cur
    } else if eff_cur < eff_cand {
        eff_cand
    } else {
        eff_cur
    }
}

/// A directed causal dependency from `(cause.0, cause.1)` to `(effect.0, effect.1)`:
/// the event at `cause.1` on stream `cause.0` causally preceded the event at
/// `effect.1` on stream `effect.0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CausalEdge<K> {
    /// The producing stream and the offset of the event that caused the effect.
    pub cause: (K, Offset),
    /// The receiving stream and the offset of the resulting event.
    pub effect: (K, Offset),
}

/// A witness that a [`CausalCut`] violates Chandy-Lamport consistency on `edge`:
/// the cut admits `edge.effect` (at `effect_frontier >= edge.effect.1`), but its
/// frontier on `edge.cause.0` is `cause_frontier` (`None` or `< edge.cause.1`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CutViolation<K> {
    /// The cross-stream causal edge whose effect is admitted without its cause.
    pub edge: CausalEdge<K>,
    /// The cut's current frontier on `edge.cause.0` (`None` if the stream is absent).
    pub cause_frontier: Option<Offset>,
    /// The cut's current frontier on `edge.effect.0` (always `>= edge.effect.1`).
    pub effect_frontier: Offset,
}

/// A vector frontier mapping each stream identifier `K` to the highest [`Offset`]
/// included in the cut.
///
/// A stream absent from the map admits no offsets (`includes` returns `false` even
/// for `Offset::ZERO`), matching `astream-engine::fleet::Cut`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CausalCut<K: Ord> {
    frontiers: BTreeMap<K, Offset>,
}

impl<K: Ord> Default for CausalCut<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord> CausalCut<K> {
    /// An empty cut that names no streams (admits nothing).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            frontiers: BTreeMap::new(),
        }
    }

    /// Build a cut from `(stream, offset)` pairs. To match `astream-engine::fleet::Cut`'s
    /// first-entry-wins convention when a caller passes a slice containing duplicate
    /// stream keys, only the FIRST offset for each stream `K` is kept.
    #[must_use]
    pub fn from_first_wins<I: IntoIterator<Item = (K, Offset)>>(iter: I) -> Self {
        let mut frontiers = BTreeMap::new();
        for (k, off) in iter {
            frontiers.entry(k).or_insert(off);
        }
        Self { frontiers }
    }

    /// Set the frontier for `stream` to `upto`, replacing any previous frontier.
    pub fn set(&mut self, stream: K, upto: Offset) {
        self.frontiers.insert(stream, upto);
    }

    /// Monotonically advance `stream`'s frontier to at least `upto`. Returns `true`
    /// iff the frontier moved forward (or `stream` was newly inserted).
    pub fn advance(&mut self, stream: K, upto: Offset) -> bool {
        match self.frontiers.get_mut(&stream) {
            Some(cur) => {
                let next = Offset(heal_frontier_monotone(cur.0, upto.0));
                if next == *cur {
                    false
                } else {
                    *cur = next;
                    true
                }
            }
            None => {
                self.frontiers.insert(stream, upto);
                true
            }
        }
    }

    /// The frontier offset for `stream`, if the cut names it.
    #[must_use]
    pub fn offset_of(&self, stream: &K) -> Option<Offset> {
        self.frontiers.get(stream).copied()
    }

    /// Does the cut admit `at` on `stream` (`at <= offset_of(stream)`)?
    /// A stream not named in the cut admits nothing.
    #[must_use]
    pub fn includes(&self, stream: &K, at: Offset) -> bool {
        match self.offset_of(stream) {
            Some(upto) => frontier_includes_raw(upto.0, at.0),
            None => false,
        }
    }

    /// Number of streams named in the cut.
    #[must_use]
    pub fn len(&self) -> usize {
        self.frontiers.len()
    }

    /// True if the cut names no streams.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.frontiers.is_empty()
    }

    /// Iterate over `(stream, &frontier)` pairs in ascending `K` order.
    pub fn iter(&self) -> std::collections::btree_map::Iter<'_, K, Offset> {
        self.frontiers.iter()
    }

    /// True iff `self` includes every frontier in `other` (`∀ (k, off) ∈ other,
    /// self.includes(k, off)`).
    #[must_use]
    pub fn dominates(&self, other: &Self) -> bool {
        for (k, &off) in &other.frontiers {
            if !self.includes(k, off) {
                return false;
            }
        }
        true
    }
}

impl<K: Ord + Clone> CausalCut<K> {
    /// Return the first [`CutViolation`] in `edges` where the cut admits `edge.effect`
    /// without admitting `edge.cause`, or `None` if the cut is Chandy-Lamport
    /// consistent.
    #[must_use]
    pub fn first_violation(&self, edges: &[CausalEdge<K>]) -> Option<CutViolation<K>> {
        for edge in edges {
            if let Some(effect_frontier) = self.offset_of(&edge.effect.0) {
                if frontier_includes_raw(effect_frontier.0, edge.effect.1 .0)
                    && !self.includes(&edge.cause.0, edge.cause.1)
                {
                    return Some(CutViolation {
                        edge: edge.clone(),
                        cause_frontier: self.offset_of(&edge.cause.0),
                        effect_frontier,
                    });
                }
            }
        }
        None
    }

    /// Chandy-Lamport consistency: for every edge whose effect the cut admits, it
    /// also admits the cause.
    #[must_use]
    pub fn is_consistent(&self, edges: &[CausalEdge<K>]) -> bool {
        self.first_violation(edges).is_none()
    }

    /// Advance this cut to its minimal Chandy-Lamport causal closure over `edges`:
    /// whenever an edge's effect is admitted by the cut (`effect.1 <= cut[effect.0]`)
    /// and its cause is not, advance `cut[cause.0]` to `edge.cause.1`.
    ///
    /// Closes transitive causal chains (`A -> B -> C`) in one call. Edges are indexed
    /// by effect stream and threshold; each becomes eligible only once as frontiers
    /// advance. Work is `O(E log E + E log S)` and scratch is `O(E)`, for `E` edges
    /// and `S` streams, rather than repeated full scans of all edges.
    ///
    /// Returns the total number of causal edge repairs applied (`0` if already
    /// consistent). Repairs retain the input-order, round-by-round schedule of a
    /// full-scan fixed point, including its count when several edges raise the same
    /// stream in stages.
    pub fn heal(&mut self, edges: &[CausalEdge<K>]) -> usize {
        // Most delivered bursts are already consistent or close in one scan.
        // Keep those paths allocation-free and retain their former repair order.
        let mut repairs = 0usize;
        for _ in 0..edges.len().min(2) {
            let mut changed = false;
            for edge in edges {
                if self.includes(&edge.effect.0, edge.effect.1)
                    && !self.includes(&edge.cause.0, edge.cause.1)
                {
                    self.advance(edge.cause.0.clone(), edge.cause.1);
                    repairs = repairs.saturating_add(1);
                    changed = true;
                }
            }
            if !changed {
                return repairs;
            }
        }
        // Each productive scan repairs a previously unsatisfied cause threshold,
        // so E scans suffice even when there is no following unchanged scan.
        if edges.len() <= 2 {
            return repairs;
        }
        // Descending thresholds let pop() consume the newly admitted prefix without
        // moving any remaining entries. Keys borrow the edges, never the cut.
        let mut waiting: BTreeMap<&K, Vec<(Offset, usize)>> = BTreeMap::new();
        for (idx, edge) in edges.iter().enumerate() {
            waiting
                .entry(&edge.effect.0)
                .or_default()
                .push((edge.effect.1, idx));
        }
        let mut ready = BinaryHeap::new();
        for (&stream, effects) in &mut waiting {
            effects.sort_unstable_by(|a, b| b.cmp(a));
            if let Some(frontier) = self.offset_of(stream) {
                while effects.last().is_some_and(|&(off, _)| off <= frontier) {
                    if let Some((_, idx)) = effects.pop() {
                        ready.push(Reverse((0usize, idx)));
                    }
                }
            }
        }

        while let Some(Reverse((round, idx))) = ready.pop() {
            let Some(edge) = edges.get(idx) else {
                continue;
            };
            // The effect was admitted when queued and frontiers only advance.
            // A cause admitted in the meantime needs no further work: this edge
            // can never become violated again.
            if self.includes(&edge.cause.0, edge.cause.1) {
                continue;
            }
            self.advance(edge.cause.0.clone(), edge.cause.1);
            repairs = repairs.saturating_add(1);
            if let Some(effects) = waiting.get_mut(&edge.cause.0) {
                while effects.last().is_some_and(|&(off, _)| off <= edge.cause.1) {
                    if let Some((_, next_idx)) = effects.pop() {
                        // A full scan has already visited earlier indices in this
                        // round. Later indices are repaired in the current round;
                        // earlier ones wait for the next, preserving repair counts.
                        let next_round = if next_idx <= idx {
                            round.saturating_add(1)
                        } else {
                            round
                        };
                        ready.push(Reverse((next_round, next_idx)));
                    }
                }
            }
        }
        repairs
    }

    /// Least upper bound (pointwise maximum frontier) of two cuts.
    ///
    /// By construction, the join of any two consistent cuts is also consistent:
    /// if an effect is in `A ⊔ B`, it was in `A` or `B`, so its cause was in `A`
    /// or `B`, and therefore in `A ⊔ B`.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (k, &off) in &other.frontiers {
            out.advance(k.clone(), off);
        }
        out
    }

    /// Greatest lower bound (pointwise minimum frontier over streams present in both)
    /// of two cuts.
    ///
    /// By construction, the meet of any two consistent cuts is also consistent:
    /// if an effect is in `A ⊓ B`, it was in both `A` and `B`, so its cause was in
    /// both `A` and `B`, and therefore in `A ⊓ B`.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        let mut frontiers = BTreeMap::new();
        for (k, &a) in &self.frontiers {
            if let Some(&b) = other.frontiers.get(k) {
                frontiers.insert(k.clone(), Offset(meet_frontier_monotone(a.0, b.0)));
            }
        }
        Self { frontiers }
    }

    /// Directly execute `Astream.Wire.TlaCausalCut.AdvanceEffectConsistent`: iff the
    /// causal parent `cause` (if any) is already admitted by this cut
    /// (`self.includes(cause_stream, cause_offset)`), advance `effect_stream`'s frontier to
    /// `max(frontier, effect_upto)`. With a cause the step is [`causal_step_frontier`], the
    /// hand-written kernel its own doc describes; without one it is [`Self::advance`],
    /// which takes the Clean-Origin (`I5`) [`heal_frontier_monotone`].
    /// Returns `true` iff the causal guard passed, whether or not the frontier moved.
    pub fn advance_effect_if_causal(
        &mut self,
        effect_stream: K,
        effect_upto: Offset,
        cause: Option<(&K, Offset)>,
    ) -> bool {
        if let Some((cause_stream, cause_off)) = cause {
            let Some(cause_cut) = self.offset_of(cause_stream) else {
                return false;
            };
            if !frontier_includes(cause_cut.0, cause_off.0) {
                return false;
            }
            let eff_cur = self.offset_of(&effect_stream).map_or(0, |o| o.0);
            let next_eff = causal_step_frontier(cause_cut.0, cause_off.0, eff_cur, effect_upto.0);
            self.frontiers.insert(effect_stream, Offset(next_eff));
            return true;
        }
        self.advance(effect_stream, effect_upto);
        true
    }

    /// Directly execute `Astream.Wire.TlaCausalCut.HealCut` + `AdvanceEffectConsistent`
    /// in O(1) for a single delivered causal edge: if `cause` is present and not yet
    /// admitted by `self`, heal `cause.0` to `heal_frontier_monotone(cur, cause.1)` first,
    /// then advance `effect_stream` to `effect_upto`. Returns `true` if `cause` had
    /// to be healed.
    pub fn advance_and_heal_edge(
        &mut self,
        effect_stream: K,
        effect_upto: Offset,
        cause: Option<(K, Offset)>,
    ) -> bool {
        let mut healed_cause = false;
        if let Some((cause_stream, cause_off)) = cause {
            if !self.includes(&cause_stream, cause_off) {
                self.advance(cause_stream, cause_off);
                healed_cause = true;
            }
        }
        self.advance(effect_stream, effect_upto);
        healed_cause
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn consistent_cut_admits_in_flight_and_rejects_orphaned_effect() {
        let edge = CausalEdge {
            cause: ("agent-a", Offset(5)),
            effect: ("agent-b", Offset(2)),
        };
        let mut cut = CausalCut::new();
        cut.set("agent-a", Offset(5));
        cut.set("agent-b", Offset(1));
        // In-flight (cause included, effect not yet included) is consistent.
        assert!(cut.is_consistent(&[edge]));

        // Including the effect while cause is at 4 violates consistency.
        cut.set("agent-a", Offset(4));
        cut.set("agent-b", Offset(2));
        assert!(!cut.is_consistent(&[edge]));
        let v = cut.first_violation(&[edge]).unwrap();
        assert_eq!(v.edge, edge);
        assert_eq!(v.cause_frontier, Some(Offset(4)));
        assert_eq!(v.effect_frontier, Offset(2));
    }

    #[test]
    fn heal_closes_transitive_causal_chains() {
        let edges = [
            CausalEdge {
                cause: ("planner", Offset(10)),
                effect: ("coder", Offset(4)),
            },
            CausalEdge {
                cause: ("coder", Offset(4)),
                effect: ("verifier", Offset(1)),
            },
        ];
        // Cut only names verifier at offset 1; heal must pull in coder@4 and planner@10.
        let mut cut = CausalCut::new();
        cut.set("verifier", Offset(1));
        assert!(!cut.is_consistent(&edges));

        let repairs = cut.heal(&edges);
        assert_eq!(repairs, 2);
        assert!(cut.is_consistent(&edges));
        assert_eq!(cut.offset_of(&"coder"), Some(Offset(4)));
        assert_eq!(cut.offset_of(&"planner"), Some(Offset(10)));
    }

    /// The former algorithm, retained as an independent semantic oracle. Its
    /// repair count depends on input order as well as the closure's final state.
    fn heal_by_full_scans<K: Ord + Clone>(
        cut: &mut CausalCut<K>,
        edges: &[CausalEdge<K>],
    ) -> usize {
        let mut repairs = 0usize;
        for _ in 0..edges.len() {
            let mut changed = false;
            for edge in edges {
                if cut.includes(&edge.effect.0, edge.effect.1)
                    && !cut.includes(&edge.cause.0, edge.cause.1)
                {
                    cut.advance(edge.cause.0.clone(), edge.cause.1);
                    repairs += 1;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        repairs
    }

    #[test]
    fn heal_matches_full_scan_closure_and_repair_count() {
        fn next(rng: &mut u64) -> u64 {
            *rng ^= *rng << 13;
            *rng ^= *rng >> 7;
            *rng ^= *rng << 17;
            *rng
        }
        fn offset(rng: &mut u64) -> Offset {
            match next(rng) % 8 {
                0 => Offset(0),
                1 => Offset(u64::MAX),
                _ => Offset(next(rng) % 32),
            }
        }
        for seed in 1..=2_000u64 {
            let mut rng = seed;
            let mut cut = CausalCut::new();
            for stream in 0..16 {
                if next(&mut rng) % 3 == 0 {
                    cut.set(stream, offset(&mut rng));
                }
            }
            let count = next(&mut rng) % 100;
            let mut edges = Vec::new();
            for _ in 0..count {
                edges.push(CausalEdge {
                    cause: (next(&mut rng) % 16, offset(&mut rng)),
                    effect: (next(&mut rng) % 16, offset(&mut rng)),
                });
            }
            let original = cut.clone();
            let mut expected = cut.clone();
            let expected_repairs = heal_by_full_scans(&mut expected, &edges);
            let repairs = cut.heal(&edges);
            assert_eq!(cut, expected, "closure, seed {seed}");
            assert_eq!(repairs, expected_repairs, "repair count, seed {seed}");
            assert!(cut.dominates(&original));
            assert!(cut.is_consistent(&edges));
            assert_eq!(cut.heal(&edges), 0);
            // Reversing edges changes the schedule, but never the least closure.
            edges.reverse();
            let mut reversed = original;
            reversed.heal(&edges);
            assert_eq!(reversed, cut, "edge order, seed {seed}");
        }
    }

    #[test]
    fn heal_preserves_scan_order_when_a_newly_enabled_earlier_edge_waits_a_round() {
        let edges = [
            CausalEdge {
                cause: (0, Offset(3)),
                effect: (1, Offset(1)),
            },
            CausalEdge {
                cause: (1, Offset(1)),
                effect: (2, Offset(1)),
            },
            CausalEdge {
                cause: (0, Offset(5)),
                effect: (2, Offset(1)),
            },
            CausalEdge {
                cause: (2, Offset(1)),
                effect: (3, Offset(1)),
            },
            CausalEdge {
                cause: (3, Offset(1)),
                effect: (4, Offset(1)),
            },
            CausalEdge {
                cause: (4, Offset(1)),
                effect: (5, Offset(1)),
            },
        ];
        let mut cut = CausalCut::new();
        cut.set(5, Offset(1));
        // The reverse chain exhausts the two fast scans. In the indexed phase,
        // edge 1 enables edge 0, but edge 2 must run before edge 0 in the next
        // round. A FIFO worklist would perform six repairs here.
        assert_eq!(cut.heal(&edges), 5);
        assert_eq!(cut.offset_of(&0), Some(Offset(5)));
        assert!(cut.is_consistent(&edges));
    }

    /// Count stream comparisons to bound all dependency-index/frontier lookups,
    /// rather than depending on machine-specific timing for the complexity gate.
    #[test]
    fn heal_reverse_chain_work_is_bounded_by_edges_times_log_streams() {
        use std::cell::Cell;
        thread_local! {
            static COMPARES: Cell<usize> = const { Cell::new(0) };
        }
        #[derive(Clone, Debug, PartialEq, Eq)]
        struct Key(usize);
        impl Ord for Key {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                COMPARES.with(|c| c.set(c.get().saturating_add(1)));
                self.0.cmp(&other.0)
            }
        }
        impl PartialOrd for Key {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        for n in [256usize, 1_024, 4_096] {
            let edges: Vec<_> = (0..n)
                .map(|i| CausalEdge {
                    cause: (Key(i), Offset(1)),
                    effect: (Key(i + 1), Offset(1)),
                })
                .collect();
            let mut cut = CausalCut::new();
            cut.set(Key(n), Offset(1));
            COMPARES.with(|c| c.set(0));
            assert_eq!(cut.heal(&edges), n);
            let comparisons = COMPARES.with(Cell::get);
            let bound = 32 * n * (n.ilog2() as usize + 1);
            assert!(
                comparisons <= bound,
                "{n} edges: {comparisons} comparisons > {bound}"
            );
            assert!(cut.is_consistent(&edges));
        }
    }

    /// Run explicitly to measure the adversarial reverse-chain case against the
    /// old full-scan implementation; timing is evidence, never a pass threshold.
    #[test]
    #[ignore = "manual causal-closure benchmark"]
    fn heal_reverse_chain_benchmark() {
        use std::time::Instant;
        for n in [1usize, 8, 64, 1_000, 4_000] {
            let reversed: Vec<_> = (0..n)
                .map(|i| CausalEdge {
                    cause: (i, Offset(1)),
                    effect: (i + 1, Offset(1)),
                })
                .collect();
            let mut forward = reversed.clone();
            forward.reverse();
            for (name, edges, consistent) in [
                ("consistent", &reversed, true),
                ("forward", &forward, false),
            ] {
                let mut original = CausalCut::new();
                if consistent {
                    for stream in 0..=n {
                        original.set(stream, Offset(1));
                    }
                } else {
                    original.set(n, Offset(1));
                }
                let repeats = if n <= 64 { 2_000 } else { 100 };
                // Prepare clones outside the measured sections to time healing.
                let mut old: Vec<_> = (0..repeats).map(|_| original.clone()).collect();
                let mut new = old.clone();
                let started = Instant::now();
                for cut in &mut old {
                    std::hint::black_box(heal_by_full_scans(cut, edges));
                }
                let old_time = started.elapsed();
                let started = Instant::now();
                for cut in &mut new {
                    std::hint::black_box(cut.heal(edges));
                }
                let new_time = started.elapsed();
                assert_eq!(old, new);
                eprintln!("{name} {n} edges ({repeats} repeats): full scans {old_time:?}, indexed {new_time:?}, {:.2}x", old_time.as_secs_f64() / new_time.as_secs_f64());
            }
        }
        for n in [1_000usize, 2_000, 4_000] {
            let edges: Vec<_> = (0..n)
                .map(|i| CausalEdge {
                    cause: (i, Offset(1)),
                    effect: (i + 1, Offset(1)),
                })
                .collect();
            let mut slow = CausalCut::new();
            slow.set(n, Offset(1));
            let mut fast = slow.clone();
            let started = Instant::now();
            let slow_repairs = heal_by_full_scans(&mut slow, &edges);
            let slow_time = started.elapsed();
            let started = Instant::now();
            let fast_repairs = fast.heal(&edges);
            let fast_time = started.elapsed();
            assert_eq!(fast, slow);
            assert_eq!(fast_repairs, slow_repairs);
            eprintln!(
                "{n} edges: full scans {slow_time:?}, indexed {fast_time:?}, {:.1}x",
                slow_time.as_secs_f64() / fast_time.as_secs_f64()
            );
        }
    }

    #[test]
    fn join_and_meet_preserve_consistency_and_dominance() {
        let edges = [
            CausalEdge {
                cause: (1u64, Offset(3)),
                effect: (2u64, Offset(7)),
            },
            CausalEdge {
                cause: (2u64, Offset(5)),
                effect: (3u64, Offset(2)),
            },
        ];
        let mut a = CausalCut::new();
        a.set(1, Offset(3));
        a.set(2, Offset(7));
        a.set(3, Offset(0));
        assert!(a.is_consistent(&edges));

        let mut b = CausalCut::new();
        b.set(1, Offset(1));
        b.set(2, Offset(5));
        b.set(3, Offset(2));
        assert!(b.is_consistent(&edges));

        let joined = a.join(&b);
        assert!(joined.is_consistent(&edges));
        assert!(joined.dominates(&a));
        assert!(joined.dominates(&b));
        assert_eq!(joined.offset_of(&1), Some(Offset(3)));
        assert_eq!(joined.offset_of(&2), Some(Offset(7)));
        assert_eq!(joined.offset_of(&3), Some(Offset(2)));

        let met = a.meet(&b);
        assert!(met.is_consistent(&edges));
        assert!(a.dominates(&met));
        assert!(b.dominates(&met));
        assert_eq!(met.offset_of(&1), Some(Offset(1)));
        assert_eq!(met.offset_of(&2), Some(Offset(5)));
        assert_eq!(met.offset_of(&3), Some(Offset(0)));
    }

    #[test]
    fn advance_effect_if_causal_and_heal_edge_enforce_tla_transitions() {
        let edge = CausalEdge {
            cause: ("src", Offset(10)),
            effect: ("dst", Offset(3)),
        };
        let mut cut = CausalCut::new();
        cut.set("src", Offset(9));
        assert!(!cut.advance_effect_if_causal("dst", Offset(3), Some((&"src", Offset(10)))));
        assert_eq!(cut.offset_of(&"dst"), None);

        // Healing the edge pulls src -> 10 and dst -> 3 in one atomic step.
        let healed = cut.advance_and_heal_edge("dst", Offset(3), Some(("src", Offset(10))));
        assert!(healed);
        assert!(cut.is_consistent(&[edge]));
        assert_eq!(cut.offset_of(&"src"), Some(Offset(10)));
        assert_eq!(cut.offset_of(&"dst"), Some(Offset(3)));

        // Subsequent causal advance succeeds without healing because src@10 is already admitted.
        assert!(cut.advance_effect_if_causal("dst", Offset(4), Some((&"src", Offset(10)))));
        assert_eq!(cut.offset_of(&"dst"), Some(Offset(4)));
    }

    #[test]
    fn advance_effect_if_causal_takes_the_max_and_answers_the_guard_not_the_move() {
        let mut cut = CausalCut::new();
        cut.set("src", Offset(10));
        cut.set("dst", Offset(6));
        // An admitted cause with a lower target: the guard passes, the frontier stays.
        assert!(cut.advance_effect_if_causal("dst", Offset(2), Some((&"src", Offset(10)))));
        assert_eq!(cut.offset_of(&"dst"), Some(Offset(6)));
        // An admitted cause on an absent effect stream: it is created at the target.
        assert!(cut.advance_effect_if_causal("new", Offset(5), Some((&"src", Offset(3)))));
        assert_eq!(cut.offset_of(&"new"), Some(Offset(5)));
        // A cause on a stream the cut does not hold is not admitted.
        assert!(!cut.advance_effect_if_causal("dst", Offset(9), Some((&"gone", Offset(0)))));
        assert_eq!(cut.offset_of(&"dst"), Some(Offset(6)));
        // No cause: `advance`'s max, and `true` whether or not the frontier moved.
        assert!(cut.advance_effect_if_causal("dst", Offset(4), None));
        assert_eq!(cut.offset_of(&"dst"), Some(Offset(6)));
        assert!(cut.advance_effect_if_causal("dst", Offset(8), None));
        assert_eq!(cut.offset_of(&"dst"), Some(Offset(8)));
        assert!(cut.advance_effect_if_causal("solo", Offset(1), None));
        assert_eq!(cut.offset_of(&"solo"), Some(Offset(1)));
    }
}
