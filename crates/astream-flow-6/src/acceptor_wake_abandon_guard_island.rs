// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `broker.blocking-accept` shutdown wakeup dialing and bounded
// stranger abandonment (`Astream.Broker.TlaAcceptorWakeAbandonGuard`, Island #279).
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def acceptor_dial_clamp (dials : UInt64) (max_dials : UInt64) : UInt64 :=
      if dials < max_dials then dials else max_dials

    def acceptor_abandoned_advance (prev : UInt64) (next : UInt64) : UInt64 :=
      if prev < next then next else prev

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Acceptor Wake Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaAcceptorWakeAbandonGuard

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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next)
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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next) :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure AcceptorWakeState where
      dials : UInt64
      max_dials : UInt64
      prev_abandoned : UInt64
      abandoned : UInt64

    def AcceptorSafetyInv (s : AcceptorWakeState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.dials) (UInt64.toNat s.max_dials))
        (Nat.le (UInt64.toNat s.prev_abandoned) (UInt64.toNat s.abandoned))

    def Init (s : AcceptorWakeState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.dials) (UInt64.toNat s.max_dials))
        (s.prev_abandoned = s.abandoned)

    def dialStep (raw_dials : UInt64) (cand_abandoned : UInt64) (s : AcceptorWakeState) : AcceptorWakeState :=
      AcceptorWakeState.mk
        (_root_.acceptor_dial_clamp raw_dials s.max_dials)
        s.max_dials
        s.abandoned
        (_root_.acceptor_abandoned_advance s.abandoned cand_abandoned)

    def Next (s : AcceptorWakeState) (s_next : AcceptorWakeState) : Prop :=
      ∃ (raw_dials : UInt64), ∃ (cand_abandoned : UInt64),
        s_next = dialStep raw_dials cand_abandoned s

    def Spec : StateMachine AcceptorWakeState :=
      StateMachine.mk Init Next

    theorem dials_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.acceptor_dial_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem abandoned_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.acceptor_abandoned_advance cur proposed)) :=
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

    theorem init_establishes_inv (s : AcceptorWakeState) (hInit : Init s) :
      AcceptorSafetyInv s :=
      And.intro
        (And.left hInit)
        (uint64_eq_le s.prev_abandoned s.abandoned (And.right hInit))

    theorem next_preserves_inv (s : AcceptorWakeState) (s_next : AcceptorWakeState)
      (_hInv : AcceptorSafetyInv s) (hNext : Next s s_next) :
      AcceptorSafetyInv s_next :=
      Exists.elim hNext (fun (rd : UInt64) (hRest : ∃ (ca : UInt64), s_next = dialStep rd ca s) =>
        Exists.elim hRest (fun (ca : UInt64) (hEq : s_next = dialStep rd ca s) =>
          Eq.mpr
            (congrArg (fun (st : AcceptorWakeState) => AcceptorSafetyInv st) hEq)
            (And.intro
              (dials_le_cap rd s.max_dials)
              (abandoned_ge_prev s.abandoned ca))))

    theorem acceptor_wake_safety_always :
      Satisfies (Runs Spec) (Always (Lift AcceptorSafetyInv)) :=
      invariantSatisfies Spec AcceptorSafetyInv init_establishes_inv next_preserves_inv

    end TlaAcceptorWakeAbandonGuard
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def acceptor_should_abandon_isl (unanswered_dials : UInt64) (max_dials : UInt64) : Bool :=
      decide (max_dials ≤ unanswered_dials)
}
