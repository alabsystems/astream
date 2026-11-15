// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `fixtures.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `fixtures.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def fixture_clamp_transcript_len (len : UInt64) (max_len : UInt64) : UInt64 :=
      if len < max_len then len else max_len

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Transcript Cap Invariant
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaFixtureTranscript

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

    structure FixtureState where
      len : UInt64
      max_len : UInt64

    def FixtureLenBoundedInv (s : FixtureState) : Prop :=
      Nat.le (UInt64.toNat s.len) (UInt64.toNat s.max_len)

    def Init (s : FixtureState) : Prop :=
      s.len = 0

    def appendFixtureAction (proposed : UInt64) (s : FixtureState) : FixtureState :=
      FixtureState.mk (_root_.fixture_clamp_transcript_len proposed s.max_len) s.max_len

    def Next (s : FixtureState) (s' : FixtureState) : Prop :=
      ∃ (proposed : UInt64), s' = appendFixtureAction proposed s

    def Spec : StateMachine FixtureState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (proposed : UInt64) (max_len : UInt64),
        Nat.le (UInt64.toNat (_root_.fixture_clamp_transcript_len proposed max_len)) (UInt64.toNat max_len) :=
      fun proposed max_len => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt proposed max_len)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_len) (fun _ => proposed))) (UInt64.toNat max_len))
        (instDecidableUInt64Lt proposed max_len)
        (fun _ => Nat.le.refl (UInt64.toNat max_len))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (x : UInt64) : Nat.le (UInt64.toNat 0) (UInt64.toNat x) :=
      Nat.zero_le (UInt64.toNat x)

    theorem init_establishes_inv (s : FixtureState) (hInit : Init s) :
      FixtureLenBoundedInv s :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.max_len)) hInit)
        (uint64_zero_le s.max_len)

    theorem next_preserves_inv (s : FixtureState) (s' : FixtureState)
      (_hInv : FixtureLenBoundedInv s) (hNext : Next s s') :
      FixtureLenBoundedInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = appendFixtureAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : FixtureState) => FixtureLenBoundedInv st) hEq)
          (clamp_le_max proposed s.max_len))

    theorem spec_satisfies_fixture_len_bounded :
      Satisfies (Runs Spec) (Always (Lift FixtureLenBoundedInv)) :=
      invariantSatisfies Spec FixtureLenBoundedInv init_establishes_inv next_preserves_inv

    end TlaFixtureTranscript
    end Agent
    end Astream

    def fixture_has_expected_len_isl (len : USize) (expected : USize) : Bool :=
      decide (len = expected)
}
