// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `fork_divergence_diff.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `fork_divergence_diff.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def fork_diff_clamp (cand_diffs : UInt64) (max_diffs : UInt64) : UInt64 :=
      if cand_diffs < max_diffs then cand_diffs else max_diffs

    def fork_diff_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Session Fork Diff Spec
    -- =======================================================================

    namespace Astream
    namespace Engine
    namespace TlaSessionForkDiff

    def Behavior (State : Type) : Type := Nat → State

    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun (k : Nat) => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (n : Nat), P (drop n b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (n : Nat), M.Next (b n) (b (Nat.add n 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (P : Formula State) (Q : Formula State) : Prop :=
      ∀ (b : Behavior State), P b → Q b

    theorem invariantAt
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s')
      (b : Behavior State)
      (hRun : Runs M b)
      (k : Nat) :
      Inv (b k) :=
      Nat.rec
        (hInit (b 0) (And.left hRun))
        (fun (j : Nat) (ih : Inv (b j)) =>
          hStep (b j) (b (Nat.add j 1)) ih (And.right hRun j))
        k

    theorem invariantSatisfies
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s') :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure ForkDiffState where
      reported_diffs : UInt64
      max_diffs : UInt64
      diff_epoch : UInt64
      prev_epoch : UInt64

    def SessionForkDiffInv (s : ForkDiffState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.reported_diffs) (UInt64.toNat s.max_diffs))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.diff_epoch))

    def Init (max_diffs : UInt64) (s : ForkDiffState) : Prop :=
      And
        (And (s.reported_diffs = 0) (s.max_diffs = max_diffs))
        (And (s.diff_epoch = 0) (s.prev_epoch = 0))

    def compareStep (cand_diffs : UInt64) (cand_epoch : UInt64) (s : ForkDiffState) : ForkDiffState :=
      ForkDiffState.mk
        (_root_.fork_diff_clamp cand_diffs s.max_diffs)
        s.max_diffs
        (_root_.fork_diff_epoch_advance s.diff_epoch cand_epoch)
        s.diff_epoch

    def Next (s : ForkDiffState) (s' : ForkDiffState) : Prop :=
      ∃ (cand_diffs : UInt64), ∃ (cand_epoch : UInt64),
        s' = compareStep cand_diffs cand_epoch s

    def Spec (max_diffs : UInt64) : StateMachine ForkDiffState :=
      StateMachine.mk (Init max_diffs) Next

    theorem diff_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.fork_diff_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.fork_diff_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_diffs : UInt64) (s : ForkDiffState)
      (hInit : Init max_diffs s) :
      SessionForkDiffInv s :=
      And.intro
        (eq_zero_le s.reported_diffs s.max_diffs (And.left (And.left hInit)))
        (eq_zero_le s.prev_epoch s.diff_epoch (And.right (And.right hInit)))

    theorem next_preserves_inv (s : ForkDiffState) (s' : ForkDiffState)
      (_hInv : SessionForkDiffInv s) (hNext : Next s s') :
      SessionForkDiffInv s' :=
      Exists.elim hNext (fun (cd : UInt64) (hRest : ∃ (ce : UInt64), s' = compareStep cd ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = compareStep cd ce s) =>
          Eq.mpr
            (congrArg (fun (st : ForkDiffState) => SessionForkDiffInv st) hEq)
            (And.intro
              (diff_clamp_le cd s.max_diffs)
              (epoch_monotone s.diff_epoch ce))))

    theorem session_fork_diff_safety_always (max_diffs : UInt64) :
      Satisfies (Runs (Spec max_diffs)) (Always (Lift SessionForkDiffInv)) :=
      invariantSatisfies (Spec max_diffs) SessionForkDiffInv (init_establishes_inv max_diffs) next_preserves_inv

    end TlaSessionForkDiff
    end Engine
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def fork_diffs_within_cap_isl (count : UInt64) (max_diffs : UInt64) : Bool :=
      decide (count <= max_diffs)
}
