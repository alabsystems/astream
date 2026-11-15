// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `subject.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `subject.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaSubjectFilter)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaSubjectFilter

    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop

    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)

    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    prefix:100 "□" => _root_.Astream.Wire.TlaSubjectFilter.Always
    infixl:45 " ⊨ " => _root_.Astream.Wire.TlaSubjectFilter.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      @Nat.rec (fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun step => hStep (b k) (b (Nat.succ k)) ih step)
            (fun stutter => Eq.mpr (congrArg I stutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    end TlaSubjectFilter
    end Wire
    end Astream

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn segment_depth_advance`) and verified by
    --    `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Monotone segment-depth progression (`max(matched_depth, candidate_depth)`).
    -- Compiled directly to `pub const fn segment_depth_advance(matched_depth: u64, candidate_depth: u64) -> u64`.
    def segment_depth_advance (matched_depth : UInt64) (candidate_depth : UInt64) : UInt64 :=
      if matched_depth < candidate_depth then candidate_depth else matched_depth

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Subject/Filter Lockstep Segment Matcher
    --    Directly over `UInt64` segment depths, `_root_.segment_depth_advance`,
    --    and `filter_depth_contains_isl`
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaSubjectFilter

    -- Island specification of `pub fn filter_depth_contains(filter_prefix_depth: u64, subject_depth: u64) -> bool`.
    def filter_depth_contains_isl (filter_prefix_depth : UInt64) (subject_depth : UInt64) : Bool :=
      decide (filter_prefix_depth <= subject_depth)

    theorem segment_depth_advance_ge_matched : forall (d : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat d) (UInt64.toNat (_root_.segment_depth_advance d cand)) :=
      fun d cand => Decidable.casesOn
        (motive := fun (dec : Decidable (LT.lt d cand)) =>
          Nat.le (UInt64.toNat d) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) dec (fun _ => d) (fun _ => cand))))
        (instDecidableUInt64Lt d cand)
        (fun _ => Nat.le.refl (UInt64.toNat d))
        (fun h => Nat.le_of_lt h)

    -- State of the lockstep segment matcher (`Filter::matches` / `Filter::contains`):
    --   status       : 0 = Matching, 1 = MatchedExact, 2 = MatchedMultiTail, 3 = Rejected
    --   filterDepth  : number of non-`>` filter segments matched so far (`UInt64`)
    --   subjectDepth : number of subject/target segments consumed so far (`UInt64`)
    structure MatchState where
      status       : Nat
      filterDepth  : UInt64
      subjectDepth : UInt64

    -- TLA+ Safety Invariant:
    -- 1. `filterDepth <= subjectDepth`: the matched non-`>` filter prefix depth never
    --    exceeds the consumed subject depth.
    -- 2. `status = 1 -> filterDepth = subjectDepth`: an exact non-`>` match holds only
    --    when both filter and subject depths are equal.
    def FilterMatchSafetyInv (s : MatchState) : Prop :=
      Nat.le (UInt64.toNat s.filterDepth) (UInt64.toNat s.subjectDepth) ∧
      (s.status = 1 → s.filterDepth = s.subjectDepth)

    def Init (s : MatchState) : Prop :=
      s.status = 0 ∧
      s.filterDepth = 0 ∧
      s.subjectDepth = 0

    -- Action 1: MatchSingleOrLiteral — both filter and subject advance together in lockstep.
    def MatchSingleOrLiteral (next_depth : UInt64) (s sNext : MatchState) : Prop :=
      s.status = 0 ∧
      sNext.status = 0 ∧
      sNext.filterDepth = _root_.segment_depth_advance s.filterDepth next_depth ∧
      sNext.subjectDepth = _root_.segment_depth_advance s.filterDepth next_depth

    -- Action 2: FinishExact — both filter and subject are exhausted at the same depth.
    def FinishExact (s sNext : MatchState) : Prop :=
      s.status = 0 ∧
      s.filterDepth = s.subjectDepth ∧
      sNext.status = 1 ∧
      sNext.filterDepth = s.filterDepth ∧
      sNext.subjectDepth = s.subjectDepth

    -- Action 3: MatchMultiTail — `>` matches 1+ trailing segments (`subjectDepth` advances).
    def MatchMultiTail (tail_depth : UInt64) (s sNext : MatchState) : Prop :=
      s.status = 0 ∧
      sNext.status = 2 ∧
      sNext.filterDepth = s.filterDepth ∧
      sNext.subjectDepth = _root_.segment_depth_advance s.subjectDepth tail_depth

    -- Action 4: RejectMismatch — segment mismatch or arity mismatch.
    def RejectMismatch (s sNext : MatchState) : Prop :=
      s.status = 0 ∧
      sNext.status = 3 ∧
      sNext.filterDepth = s.filterDepth ∧
      sNext.subjectDepth = s.subjectDepth

    def Next (s sNext : MatchState) : Prop :=
      (∃ next_depth : UInt64, MatchSingleOrLiteral next_depth s sNext) ∨
        (FinishExact s sNext ∨
          ((∃ tail_depth : UInt64, MatchMultiTail tail_depth s sNext) ∨
            RejectMismatch s sNext))

    def Spec : StateMachine MatchState :=
      StateMachine.mk Init Next

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem two_ne_one (h : 2 = 1) : False :=
      Nat.noConfusion h (fun h10 => Nat.noConfusion h10)

    theorem three_ne_one (h : 3 = 1) : False :=
      Nat.noConfusion h (fun h20 => Nat.noConfusion h20)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (Nat.le.refl (UInt64.toNat a))

    theorem init_implies_inv (s : MatchState) (hInit : Init s) : FilterMatchSafetyInv s :=
      And.intro
        (uint64_eq_le s.filterDepth s.subjectDepth (Eq.trans hInit.2.1 (Eq.symm hInit.2.2)))
        (fun hSt1 => False.elim (zero_ne_one (Eq.trans (Eq.symm hInit.1) hSt1)))

    theorem single_preserves_inv (next_depth : UInt64) (s sNext : MatchState)
        (_hInv : FilterMatchSafetyInv s) (hAct : MatchSingleOrLiteral next_depth s sNext) :
        FilterMatchSafetyInv sNext :=
      let hEq : sNext.filterDepth = sNext.subjectDepth :=
        Eq.trans hAct.2.2.1 (Eq.symm hAct.2.2.2)
      And.intro
        (uint64_eq_le sNext.filterDepth sNext.subjectDepth hEq)
        (fun hSt1 => False.elim (zero_ne_one (Eq.trans (Eq.symm hAct.2.1) hSt1)))

    theorem exact_preserves_inv (s sNext : MatchState)
        (_hInv : FilterMatchSafetyInv s) (hAct : FinishExact s sNext) :
        FilterMatchSafetyInv sNext :=
      let hEq : sNext.filterDepth = sNext.subjectDepth :=
        Eq.trans hAct.2.2.2.1 (Eq.trans hAct.2.1 (Eq.symm hAct.2.2.2.2))
      And.intro
        (uint64_eq_le sNext.filterDepth sNext.subjectDepth hEq)
        (fun _ => hEq)

    theorem multi_preserves_inv (tail_depth : UInt64) (s sNext : MatchState)
        (hInv : FilterMatchSafetyInv s) (hAct : MatchMultiTail tail_depth s sNext) :
        FilterMatchSafetyInv sNext :=
      let hFlEq : sNext.filterDepth = s.filterDepth := hAct.2.2.1
      let hSubEq : sNext.subjectDepth = _root_.segment_depth_advance s.subjectDepth tail_depth := hAct.2.2.2
      let hFlLeSub : Nat.le (UInt64.toNat sNext.filterDepth) (UInt64.toNat s.subjectDepth) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.subjectDepth)) hFlEq) hInv.1
      let hSubLeNext : Nat.le (UInt64.toNat s.subjectDepth) (UInt64.toNat sNext.subjectDepth) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat s.subjectDepth) (UInt64.toNat x)) hSubEq)
          (segment_depth_advance_ge_matched s.subjectDepth tail_depth)
      And.intro
        (Nat.le_trans hFlLeSub hSubLeNext)
        (fun hSt1 => False.elim (two_ne_one (Eq.trans (Eq.symm hAct.2.1) hSt1)))

    theorem reject_preserves_inv (s sNext : MatchState)
        (hInv : FilterMatchSafetyInv s) (hAct : RejectMismatch s sNext) :
        FilterMatchSafetyInv sNext :=
      let h1 : Nat.le (UInt64.toNat sNext.filterDepth) (UInt64.toNat s.subjectDepth) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.subjectDepth)) hAct.2.2.1) hInv.1
      let h2 : Nat.le (UInt64.toNat sNext.filterDepth) (UInt64.toNat sNext.subjectDepth) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.filterDepth) (UInt64.toNat x)) hAct.2.2.2) h1
      And.intro
        h2
        (fun hSt1 => False.elim (three_ne_one (Eq.trans (Eq.symm hAct.2.1) hSt1)))

    theorem next_preserves_inv (s sNext : MatchState)
        (hInv : FilterMatchSafetyInv s) (hNext : Next s sNext) :
        FilterMatchSafetyInv sNext :=
      Or.elim hNext
        (fun hS => Exists.elim hS (fun nd hAct => single_preserves_inv nd s sNext hInv hAct))
        (fun hR1 => Or.elim hR1
          (fun hEx => exact_preserves_inv s sNext hInv hEx)
          (fun hR2 => Or.elim hR2
            (fun hM => Exists.elim hM (fun td hAct => multi_preserves_inv td s sNext hInv hAct))
            (fun hRej => reject_preserves_inv s sNext hInv hRej)))

    -- ========================================================================
    -- 4. Top-Level Temporal Theorem: `Spec ⊨ □ (Lift FilterMatchSafetyInv)`
    -- ========================================================================
    theorem spec_satisfies_always_filter_match_safety : Spec ⊨ □ (Lift FilterMatchSafetyInv) :=
      invariantSatisfies Spec FilterMatchSafetyInv init_implies_inv next_preserves_inv

    end TlaSubjectFilter
    end Wire
    end Astream
}
