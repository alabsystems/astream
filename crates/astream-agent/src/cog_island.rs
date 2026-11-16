// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `cog.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `cog.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def cog_clamp_call_count (count : UInt64) (max_calls : UInt64) : UInt64 :=
      if count < max_calls then count else max_calls

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Call Count Invariant
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaCogRecord

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

    structure CogCallState where
      calls : UInt64
      max_calls : UInt64

    def CogCallsBoundedInv (s : CogCallState) : Prop :=
      Nat.le (UInt64.toNat s.calls) (UInt64.toNat s.max_calls)

    def Init (s : CogCallState) : Prop :=
      s.calls = 0

    def emitCallsAction (proposed : UInt64) (s : CogCallState) : CogCallState :=
      CogCallState.mk (_root_.cog_clamp_call_count proposed s.max_calls) s.max_calls

    def Next (s : CogCallState) (s' : CogCallState) : Prop :=
      ∃ (proposed : UInt64), s' = emitCallsAction proposed s

    def Spec : StateMachine CogCallState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (proposed : UInt64) (max_calls : UInt64),
        Nat.le (UInt64.toNat (_root_.cog_clamp_call_count proposed max_calls)) (UInt64.toNat max_calls) :=
      fun proposed max_calls => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt proposed max_calls)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_calls) (fun _ => proposed))) (UInt64.toNat max_calls))
        (instDecidableUInt64Lt proposed max_calls)
        (fun _ => @Nat.le.refl (UInt64.toNat max_calls))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (x : UInt64) : Nat.le (UInt64.toNat 0) (UInt64.toNat x) :=
      Nat.zero_le (UInt64.toNat x)

    theorem init_establishes_inv (s : CogCallState) (hInit : Init s) :
      CogCallsBoundedInv s :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.max_calls)) hInit)
        (uint64_zero_le s.max_calls)

    theorem next_preserves_inv (s : CogCallState) (s' : CogCallState)
      (_hInv : CogCallsBoundedInv s) (hNext : Next s s') :
      CogCallsBoundedInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = emitCallsAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : CogCallState) => CogCallsBoundedInv st) hEq)
          (clamp_le_max proposed s.max_calls))

    theorem spec_satisfies_cog_calls_bounded :
      Satisfies (Runs Spec) (Always (Lift CogCallsBoundedInv)) :=
      invariantSatisfies Spec CogCallsBoundedInv init_establishes_inv next_preserves_inv

    end TlaCogRecord
    end Agent
    end Astream

    def cog_is_end_turn_isl (stop_code : UInt8) : Bool :=
      decide (stop_code = 1)
}
