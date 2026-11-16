// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `aspump.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `aspump.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `islands/aspump_twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def aspump_commit_offset_advance (prev : UInt64) (next : UInt64) : UInt64 :=
      if prev < next then next else prev

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Commit Offset Monotone
    -- =======================================================================

    namespace Astream
    namespace Pump
    namespace TlaAspumpBin

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

    structure AspumpCommitState where
      prev_offset : UInt64
      offset : UInt64

    def AspumpCommitMonotoneInv (s : AspumpCommitState) : Prop :=
      Nat.le (UInt64.toNat s.prev_offset) (UInt64.toNat s.offset)

    def Init (s : AspumpCommitState) : Prop :=
      s.prev_offset = s.offset

    def commitDeliveryAction (proposed : UInt64) (s : AspumpCommitState) : AspumpCommitState :=
      AspumpCommitState.mk s.offset (_root_.aspump_commit_offset_advance s.offset proposed)

    def Next (s : AspumpCommitState) (s' : AspumpCommitState) : Prop :=
      ∃ (proposed : UInt64), s' = commitDeliveryAction proposed s

    def Spec : StateMachine AspumpCommitState :=
      StateMachine.mk Init Next

    theorem advance_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.aspump_commit_offset_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : AspumpCommitState) (hInit : Init s) :
      AspumpCommitMonotoneInv s :=
      uint64_eq_le s.prev_offset s.offset hInit

    theorem next_preserves_inv (s : AspumpCommitState) (s' : AspumpCommitState)
      (_hInv : AspumpCommitMonotoneInv s) (hNext : Next s s') :
      AspumpCommitMonotoneInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = commitDeliveryAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : AspumpCommitState) => AspumpCommitMonotoneInv st) hEq)
          (advance_ge_prev s.offset proposed))

    theorem spec_satisfies_aspump_commit_monotonicity :
      Satisfies (Runs Spec) (Always (Lift AspumpCommitMonotoneInv)) :=
      invariantSatisfies Spec AspumpCommitMonotoneInv init_establishes_inv next_preserves_inv

    end TlaAspumpBin
    end Pump
    end Astream

    def aspump_dim_in_range_isl (dim : UInt16) : Bool :=
      decide (0 < dim)
}
