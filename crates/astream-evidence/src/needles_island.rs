// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `needles.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `needles.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def needle_clamp_count (count : UInt64) (max_count : UInt64) : UInt64 :=
      if count < max_count then count else max_count

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Needle Count Invariant
    -- =======================================================================

    namespace Astream
    namespace Evidence
    namespace TlaLintNeedles

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

    structure NeedleSetState where
      count : UInt64
      max_count : UInt64

    def NeedleCountBoundedInv (s : NeedleSetState) : Prop :=
      Nat.le (UInt64.toNat s.count) (UInt64.toNat s.max_count)

    def Init (s : NeedleSetState) : Prop :=
      s.count = 0

    def addNeedleAction (proposed : UInt64) (s : NeedleSetState) : NeedleSetState :=
      NeedleSetState.mk (_root_.needle_clamp_count proposed s.max_count) s.max_count

    def Next (s : NeedleSetState) (s' : NeedleSetState) : Prop :=
      ∃ (proposed : UInt64), s' = addNeedleAction proposed s

    def Spec : StateMachine NeedleSetState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (proposed : UInt64) (max_count : UInt64),
        Nat.le (UInt64.toNat (_root_.needle_clamp_count proposed max_count)) (UInt64.toNat max_count) :=
      fun proposed max_count => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt proposed max_count)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_count) (fun _ => proposed))) (UInt64.toNat max_count))
        (instDecidableUInt64Lt proposed max_count)
        (fun _ => Nat.le.refl (UInt64.toNat max_count))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (x : UInt64) : Nat.le (UInt64.toNat 0) (UInt64.toNat x) :=
      Nat.zero_le (UInt64.toNat x)

    theorem init_establishes_inv (s : NeedleSetState) (hInit : Init s) :
      NeedleCountBoundedInv s :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.max_count)) hInit)
        (uint64_zero_le s.max_count)

    theorem next_preserves_inv (s : NeedleSetState) (s' : NeedleSetState)
      (_hInv : NeedleCountBoundedInv s) (hNext : Next s s') :
      NeedleCountBoundedInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = addNeedleAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : NeedleSetState) => NeedleCountBoundedInv st) hEq)
          (clamp_le_max proposed s.max_count))

    theorem spec_satisfies_needle_count_bounded :
      Satisfies (Runs Spec) (Always (Lift NeedleCountBoundedInv)) :=
      invariantSatisfies Spec NeedleCountBoundedInv init_establishes_inv next_preserves_inv

    end TlaLintNeedles
    end Evidence
    end Astream

    def needle_non_empty_isl (len : USize) : Bool :=
      decide (0 < len)
}
