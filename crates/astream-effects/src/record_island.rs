// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `record.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `record.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def record_mono_advance (prev : UInt64) (now : UInt64) : UInt64 :=
      if prev < now then now else prev

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Effects.TlaMonoClock)
    -- ========================================================================
    namespace Astream
    namespace Effects
    namespace TlaMonoClock

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

    structure MonoClockState where
      prev : UInt64
      now : UInt64

    def MonoClockMonotoneInv (s : MonoClockState) : Prop :=
      Nat.le (UInt64.toNat s.prev) (UInt64.toNat s.now)

    def Init (s : MonoClockState) : Prop :=
      s.prev = s.now

    def sampleMonoAction (sample : UInt64) (s : MonoClockState) : MonoClockState :=
      MonoClockState.mk s.now (_root_.record_mono_advance s.now sample)

    def Next (s : MonoClockState) (s' : MonoClockState) : Prop :=
      ∃ (sample : UInt64), s' = sampleMonoAction sample s

    def Spec : StateMachine MonoClockState :=
      StateMachine.mk Init Next

    theorem advance_ge_prev : forall (prev : UInt64) (sample : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.record_mono_advance prev sample)) :=
      fun prev sample => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev sample)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => sample))))
        (instDecidableUInt64Lt prev sample)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : MonoClockState) (hInit : Init s) :
      MonoClockMonotoneInv s :=
      uint64_eq_le s.prev s.now hInit

    theorem next_preserves_inv (s : MonoClockState) (s' : MonoClockState)
      (_hInv : MonoClockMonotoneInv s) (hNext : Next s s') :
      MonoClockMonotoneInv s' :=
      Exists.elim hNext (fun (sample : UInt64) (hEq : s' = sampleMonoAction sample s) =>
        Eq.mpr
          (congrArg (fun (st : MonoClockState) => MonoClockMonotoneInv st) hEq)
          (advance_ge_prev s.now sample))

    theorem spec_satisfies_mono_clock_monotonicity :
      Satisfies (Runs Spec) (Always (Lift MonoClockMonotoneInv)) :=
      invariantSatisfies Spec MonoClockMonotoneInv init_establishes_inv next_preserves_inv

    end TlaMonoClock
    end Effects
    end Astream

    def record_seed_non_zero_isl (seed : UInt64) : Bool :=
      decide (0 < seed)
}
