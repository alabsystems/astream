// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `cruise_cadence_rotator.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `cruise_cadence_rotator.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def cruise_idle_streak_clamp (cand_streak : UInt64) (max_streak : UInt64) : UInt64 :=
      if cand_streak < max_streak then cand_streak else max_streak

    def cruise_turn_advance (cur_turn : UInt64) (cand_turn : UInt64) : UInt64 :=
      if cur_turn < cand_turn then cand_turn else cur_turn

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Cruise Work Rotator Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaCruiseWorkRotator

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

    structure CruiseState where
      idle_streak : UInt64
      max_idle_streak : UInt64
      turn_seq : UInt64
      prev_turn : UInt64

    def CruiseInv (s : CruiseState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.idle_streak) (UInt64.toNat s.max_idle_streak))
        (Nat.le (UInt64.toNat s.prev_turn) (UInt64.toNat s.turn_seq))

    def Init (max_idle_streak : UInt64) (s : CruiseState) : Prop :=
      And
        (And (s.idle_streak = 0) (s.max_idle_streak = max_idle_streak))
        (And (s.turn_seq = 0) (s.prev_turn = 0))

    def cruiseStep (cand_streak : UInt64) (cand_turn : UInt64) (s : CruiseState) : CruiseState :=
      CruiseState.mk
        (_root_.cruise_idle_streak_clamp cand_streak s.max_idle_streak)
        s.max_idle_streak
        (_root_.cruise_turn_advance s.turn_seq cand_turn)
        s.turn_seq

    def Next (s : CruiseState) (s' : CruiseState) : Prop :=
      ∃ (cand_streak : UInt64), ∃ (cand_turn : UInt64),
        s' = cruiseStep cand_streak cand_turn s

    def Spec (max_idle_streak : UInt64) : StateMachine CruiseState :=
      StateMachine.mk (Init max_idle_streak) Next

    theorem streak_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.cruise_idle_streak_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem turn_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.cruise_turn_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_idle_streak : UInt64) (s : CruiseState)
      (hInit : Init max_idle_streak s) :
      CruiseInv s :=
      And.intro
        (eq_zero_le s.idle_streak s.max_idle_streak (And.left (And.left hInit)))
        (eq_zero_le s.prev_turn s.turn_seq (And.right (And.right hInit)))

    theorem next_preserves_inv (s : CruiseState) (s' : CruiseState)
      (_hInv : CruiseInv s) (hNext : Next s s') :
      CruiseInv s' :=
      Exists.elim hNext (fun (cs : UInt64) (hRest : ∃ (ct : UInt64), s' = cruiseStep cs ct s) =>
        Exists.elim hRest (fun (ct : UInt64) (hEq : s' = cruiseStep cs ct s) =>
          Eq.mpr
            (congrArg (fun (st : CruiseState) => CruiseInv st) hEq)
            (And.intro
              (streak_clamp_le cs s.max_idle_streak)
              (turn_monotone s.turn_seq ct))))

    theorem cruise_rotator_safety_always (max_idle_streak : UInt64) :
      Satisfies (Runs (Spec max_idle_streak)) (Always (Lift CruiseInv)) :=
      invariantSatisfies (Spec max_idle_streak) CruiseInv (init_establishes_inv max_idle_streak) next_preserves_inv

    end TlaCruiseWorkRotator
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def cruise_idle_within_cap_isl (idle_streak : UInt64) (max_streak : UInt64) : Bool :=
      decide (idle_streak <= max_streak)
}
