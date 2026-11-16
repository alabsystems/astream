// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `gate.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `gate.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def gate_violation_advance (prev : UInt64) (next : UInt64) : UInt64 :=
      if prev < next then next else prev

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Violation Count Monotone
    -- =======================================================================

    namespace Astream
    namespace Evidence
    namespace TlaMergeGate

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

    structure GateScanState where
      prev_count : UInt64
      count : UInt64

    def GateViolationMonotoneInv (s : GateScanState) : Prop :=
      Nat.le (UInt64.toNat s.prev_count) (UInt64.toNat s.count)

    def Init (s : GateScanState) : Prop :=
      s.prev_count = s.count

    def recordViolationAction (proposed : UInt64) (s : GateScanState) : GateScanState :=
      GateScanState.mk s.count (_root_.gate_violation_advance s.count proposed)

    def Next (s : GateScanState) (s' : GateScanState) : Prop :=
      ∃ (proposed : UInt64), s' = recordViolationAction proposed s

    def Spec : StateMachine GateScanState :=
      StateMachine.mk Init Next

    theorem advance_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.gate_violation_advance cur proposed)) :=
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

    theorem init_establishes_inv (s : GateScanState) (hInit : Init s) :
      GateViolationMonotoneInv s :=
      uint64_eq_le s.prev_count s.count hInit

    theorem next_preserves_inv (s : GateScanState) (s' : GateScanState)
      (_hInv : GateViolationMonotoneInv s) (hNext : Next s s') :
      GateViolationMonotoneInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = recordViolationAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : GateScanState) => GateViolationMonotoneInv st) hEq)
          (advance_ge_prev s.count proposed))

    theorem spec_satisfies_gate_violation_monotonicity :
      Satisfies (Runs Spec) (Always (Lift GateViolationMonotoneInv)) :=
      invariantSatisfies Spec GateViolationMonotoneInv init_establishes_inv next_preserves_inv

    end TlaMergeGate
    end Evidence
    end Astream

    def gate_is_clean_isl (violations : USize) : Bool :=
      decide (violations = 0)
}
