// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `Durability::Ordered` escalation held-head and horizon clamping
// (`Astream.Broker.TlaOrderedEscalationHorizon`, Island #276), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def ordered_head_advance (cur : UInt64) (next_off : UInt64) : UInt64 :=
      if cur < next_off then next_off else cur

    def ordered_horizon_clamp (horizon_ms : UInt64) (max_ms : UInt64) : UInt64 :=
      if horizon_ms < max_ms then horizon_ms else max_ms

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Ordered Escalation Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaOrderedEscalationHorizon

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

    structure OrderedState where
      prev_head : UInt64
      staged_head : UInt64
      horizon_ms : UInt64
      max_horizon_ms : UInt64

    def OrderedSafetyInv (s : OrderedState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_head) (UInt64.toNat s.staged_head))
        (Nat.le (UInt64.toNat s.horizon_ms) (UInt64.toNat s.max_horizon_ms))

    def Init (s : OrderedState) : Prop :=
      And
        (s.prev_head = s.staged_head)
        (Nat.le (UInt64.toNat s.horizon_ms) (UInt64.toNat s.max_horizon_ms))

    def stageStep (batch_end : UInt64) (raw_horizon : UInt64) (s : OrderedState) : OrderedState :=
      OrderedState.mk
        s.staged_head
        (_root_.ordered_head_advance s.staged_head batch_end)
        (_root_.ordered_horizon_clamp raw_horizon s.max_horizon_ms)
        s.max_horizon_ms

    def Next (s : OrderedState) (s' : OrderedState) : Prop :=
      ∃ (batch_end : UInt64), ∃ (raw_horizon : UInt64),
        s' = stageStep batch_end raw_horizon s

    def Spec : StateMachine OrderedState :=
      StateMachine.mk Init Next

    theorem head_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.ordered_head_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem horizon_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.ordered_horizon_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : OrderedState) (hInit : Init s) :
      OrderedSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_head s.staged_head (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : OrderedState) (s' : OrderedState)
      (_hInv : OrderedSafetyInv s) (hNext : Next s s') :
      OrderedSafetyInv s' :=
      Exists.elim hNext (fun (be : UInt64) (hRest : ∃ (rh : UInt64), s' = stageStep be rh s) =>
        Exists.elim hRest (fun (rh : UInt64) (hEq : s' = stageStep be rh s) =>
          Eq.mpr
            (congrArg (fun (st : OrderedState) => OrderedSafetyInv st) hEq)
            (And.intro
              (head_ge_prev s.staged_head be)
              (horizon_le_max rh s.max_horizon_ms))))

    theorem ordered_safety_always :
      Satisfies (Runs Spec) (Always (Lift OrderedSafetyInv)) :=
      invariantSatisfies Spec OrderedSafetyInv init_establishes_inv next_preserves_inv

    end TlaOrderedEscalationHorizon
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def ordered_heads_ordered_isl (durable : UInt64) (visible : UInt64) : Bool :=
      decide (durable ≤ visible)

    def ordered_is_poisoned_isl (poisoned_flag : UInt64) : Bool :=
      decide ((0 : UInt64) < poisoned_flag)
}
