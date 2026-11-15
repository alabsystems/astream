// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `fleet.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `fleet.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def fleet_clamp_cut_len (cut_len : UInt64) (total : UInt64) : UInt64 :=
      if cut_len < total then cut_len else total

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Fleet Cut Prefix Bound
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaCogFleet

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

    structure CogFleetCutState where
      cut_len : UInt64
      total : UInt64

    def CogFleetCutBoundedInv (s : CogFleetCutState) : Prop :=
      Nat.le (UInt64.toNat s.cut_len) (UInt64.toNat s.total)

    def Init (s : CogFleetCutState) : Prop :=
      s.cut_len = 0

    def sliceCutAction (proposed : UInt64) (s : CogFleetCutState) : CogFleetCutState :=
      CogFleetCutState.mk (_root_.fleet_clamp_cut_len proposed s.total) s.total

    def Next (s : CogFleetCutState) (s' : CogFleetCutState) : Prop :=
      ∃ (proposed : UInt64), s' = sliceCutAction proposed s

    def Spec : StateMachine CogFleetCutState :=
      StateMachine.mk Init Next

    theorem clamp_le_total : forall (proposed : UInt64) (total : UInt64),
        Nat.le (UInt64.toNat (_root_.fleet_clamp_cut_len proposed total)) (UInt64.toNat total) :=
      fun proposed total => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt proposed total)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => total) (fun _ => proposed))) (UInt64.toNat total))
        (instDecidableUInt64Lt proposed total)
        (fun _ => Nat.le.refl (UInt64.toNat total))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (x : UInt64) : Nat.le (UInt64.toNat 0) (UInt64.toNat x) :=
      Nat.zero_le (UInt64.toNat x)

    theorem init_establishes_inv (s : CogFleetCutState) (hInit : Init s) :
      CogFleetCutBoundedInv s :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.total)) hInit)
        (uint64_zero_le s.total)

    theorem next_preserves_inv (s : CogFleetCutState) (s' : CogFleetCutState)
      (_hInv : CogFleetCutBoundedInv s) (hNext : Next s s') :
      CogFleetCutBoundedInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = sliceCutAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : CogFleetCutState) => CogFleetCutBoundedInv st) hEq)
          (clamp_le_total proposed s.total))

    theorem spec_satisfies_cog_fleet_cut_bounded :
      Satisfies (Runs Spec) (Always (Lift CogFleetCutBoundedInv)) :=
      invariantSatisfies Spec CogFleetCutBoundedInv init_establishes_inv next_preserves_inv

    end TlaCogFleet
    end Agent
    end Astream

    def fleet_cause_reached_isl (cause_offset : UInt64) (reached_count : UInt64) : Bool :=
      decide (cause_offset < reached_count)
}
