// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `seam.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `seam.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def seam_false_reads_advance (cur : UInt64) (next : UInt64) : UInt64 :=
      if cur < next then next else cur

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Effects.TlaLatchState)
    -- ========================================================================
    namespace Astream
    namespace Effects
    namespace TlaLatchState

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (k : Nat) (b : Behavior State) : Behavior State :=
      fun (n : Nat) => b (Nat.add k n)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (k : Nat), P (drop k b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        M.Init (b 0) ∧ ∀ (k : Nat), M.Next (b k) (b (Nat.add k 1))

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun (b : Behavior State) => P (b 0)

    def Satisfies {State : Type} (SpecF : Formula State) (PropF : Formula State) : Prop :=
      ∀ (b : Behavior State), SpecF b → PropF b

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

    structure LatchCounterState where
      prev : UInt64
      cur : UInt64

    def FalseReadsMonotoneInv (s : LatchCounterState) : Prop :=
      Nat.le (UInt64.toNat s.prev) (UInt64.toNat s.cur)

    def Init (s : LatchCounterState) : Prop :=
      s.prev = s.cur

    def pollFalseAction (proposed : UInt64) (s : LatchCounterState) : LatchCounterState :=
      LatchCounterState.mk s.cur (_root_.seam_false_reads_advance s.cur proposed)

    def Next (s : LatchCounterState) (s' : LatchCounterState) : Prop :=
      ∃ (proposed : UInt64), s' = pollFalseAction proposed s

    def Spec : StateMachine LatchCounterState :=
      StateMachine.mk Init Next

    theorem advance_ge_cur : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.seam_false_reads_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : LatchCounterState) (hInit : Init s) :
      FalseReadsMonotoneInv s :=
      uint64_eq_le s.prev s.cur hInit

    theorem next_preserves_inv (s : LatchCounterState) (s' : LatchCounterState)
      (_hInv : FalseReadsMonotoneInv s) (hNext : Next s s') :
      FalseReadsMonotoneInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = pollFalseAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : LatchCounterState) => FalseReadsMonotoneInv st) hEq)
          (advance_ge_cur s.cur proposed))

    theorem spec_satisfies_false_reads_monotonicity :
      Satisfies (Runs Spec) (Always (Lift FalseReadsMonotoneInv)) :=
      invariantSatisfies Spec FalseReadsMonotoneInv init_establishes_inv next_preserves_inv

    end TlaLatchState
    end Effects
    end Astream

    def seam_false_reads_matches_isl (recorded : UInt64) (counted : UInt64) : Bool :=
      decide (recorded = counted)
}
