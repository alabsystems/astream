// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `syspolicyd_guard.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `syspolicyd_guard.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def syspolicy_hang_clamp (proposed_streak : UInt64) (trip_cap : UInt64) : UInt64 :=
      if proposed_streak < trip_cap then proposed_streak else trip_cap

    def syspolicy_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Syspolicyd Guard Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaSyspolicydGuard

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

    structure SyspolicydState where
      hang_streak : UInt64
      trip_cap : UInt64
      cur_epoch : UInt64
      prev_epoch : UInt64

    def SyspolicydGuardInv (s : SyspolicydState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.hang_streak) (UInt64.toNat s.trip_cap))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.cur_epoch))

    def Init (trip_cap : UInt64) (s : SyspolicydState) : Prop :=
      And
        (And (s.hang_streak = 0) (s.trip_cap = trip_cap))
        (And (s.cur_epoch = 0) (s.prev_epoch = 0))

    def stepGuard (cand_streak : UInt64) (cand_epoch : UInt64) (s : SyspolicydState) : SyspolicydState :=
      SyspolicydState.mk
        (_root_.syspolicy_hang_clamp cand_streak s.trip_cap)
        s.trip_cap
        (_root_.syspolicy_epoch_advance s.cur_epoch cand_epoch)
        s.cur_epoch

    def Next (s : SyspolicydState) (s' : SyspolicydState) : Prop :=
      ∃ (cand_streak : UInt64), ∃ (cand_epoch : UInt64),
        s' = stepGuard cand_streak cand_epoch s

    def Spec (trip_cap : UInt64) : StateMachine SyspolicydState :=
      StateMachine.mk (Init trip_cap) Next

    theorem hang_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.syspolicy_hang_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.syspolicy_epoch_advance cur cand)) :=
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

    theorem init_establishes_inv (trip_cap : UInt64) (s : SyspolicydState)
      (hInit : Init trip_cap s) :
      SyspolicydGuardInv s :=
      And.intro
        (eq_zero_le s.hang_streak s.trip_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_epoch s.cur_epoch (And.right (And.right hInit)))

    theorem next_preserves_inv (s : SyspolicydState) (s' : SyspolicydState)
      (_hInv : SyspolicydGuardInv s) (hNext : Next s s') :
      SyspolicydGuardInv s' :=
      Exists.elim hNext (fun (cs : UInt64) (hRest : ∃ (ce : UInt64), s' = stepGuard cs ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = stepGuard cs ce s) =>
          Eq.mpr
            (congrArg (fun (st : SyspolicydState) => SyspolicydGuardInv st) hEq)
            (And.intro
              (hang_clamp_le cs s.trip_cap)
              (epoch_monotone s.cur_epoch ce))))

    theorem syspolicyd_guard_safety_always (trip_cap : UInt64) :
      Satisfies (Runs (Spec trip_cap)) (Always (Lift SyspolicydGuardInv)) :=
      invariantSatisfies (Spec trip_cap) SyspolicydGuardInv (init_establishes_inv trip_cap) next_preserves_inv

    end TlaSyspolicydGuard
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def syspolicy_breaker_tripped_isl (hang_streak : UInt64) (trip_cap : UInt64) : Bool :=
      decide (trip_cap <= hang_streak)
}
