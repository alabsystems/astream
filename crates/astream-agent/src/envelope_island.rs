// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `envelope.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `envelope.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def envelope_clamp_call_cap (n : UInt64) (max_cap : UInt64) : UInt64 :=
      if n < max_cap then n else max_cap

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Prealloc Cap Invariant
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaCogEnvelope

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

    structure EnvelopeCapState where
      cap : UInt64
      max_cap : UInt64

    def EnvelopeCapBoundedInv (s : EnvelopeCapState) : Prop :=
      Nat.le (UInt64.toNat s.cap) (UInt64.toNat s.max_cap)

    def Init (s : EnvelopeCapState) : Prop :=
      s.cap = 0

    def reserveCallsAction (proposed : UInt64) (s : EnvelopeCapState) : EnvelopeCapState :=
      EnvelopeCapState.mk (_root_.envelope_clamp_call_cap proposed s.max_cap) s.max_cap

    def Next (s : EnvelopeCapState) (s' : EnvelopeCapState) : Prop :=
      ∃ (proposed : UInt64), s' = reserveCallsAction proposed s

    def Spec : StateMachine EnvelopeCapState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (proposed : UInt64) (max_cap : UInt64),
        Nat.le (UInt64.toNat (_root_.envelope_clamp_call_cap proposed max_cap)) (UInt64.toNat max_cap) :=
      fun proposed max_cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt proposed max_cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_cap) (fun _ => proposed))) (UInt64.toNat max_cap))
        (instDecidableUInt64Lt proposed max_cap)
        (fun _ => Nat.le.refl (UInt64.toNat max_cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (x : UInt64) : Nat.le (UInt64.toNat 0) (UInt64.toNat x) :=
      Nat.zero_le (UInt64.toNat x)

    theorem init_establishes_inv (s : EnvelopeCapState) (hInit : Init s) :
      EnvelopeCapBoundedInv s :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.max_cap)) hInit)
        (uint64_zero_le s.max_cap)

    theorem next_preserves_inv (s : EnvelopeCapState) (s' : EnvelopeCapState)
      (_hInv : EnvelopeCapBoundedInv s) (hNext : Next s s') :
      EnvelopeCapBoundedInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = reserveCallsAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : EnvelopeCapState) => EnvelopeCapBoundedInv st) hEq)
          (clamp_le_max proposed s.max_cap))

    theorem spec_satisfies_envelope_cap_bounded :
      Satisfies (Runs Spec) (Always (Lift EnvelopeCapBoundedInv)) :=
      invariantSatisfies Spec EnvelopeCapBoundedInv init_establishes_inv next_preserves_inv

    end TlaCogEnvelope
    end Agent
    end Astream

    def envelope_version_matches_isl (version : UInt8) (expected : UInt8) : Bool :=
      decide (version = expected)
}
