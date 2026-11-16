// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// Clean-Origin TLA+ protocol island (#255): `Astream.Agent.TlaAutopilotCruiseWheel`.
// Models `Autopilot=Cruise` 6-phase work-rotation & repetition-halt controller.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def cruise_phase_clamp (phase : UInt64) : UInt64 :=
      if phase < (5 : UInt64) then phase else (5 : UInt64)

    def cruise_empty_streak_clamp (streak : UInt64) : UInt64 :=
      if streak < (6 : UInt64) then streak else (6 : UInt64)

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & TlaAutopilotCruiseWheel Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaAutopilotCruiseWheel

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

    structure ProtocolState where
      prev_epoch : UInt64
      epoch : UInt64
      bounded_val : UInt64
      cap_val : UInt64

    def SafetyInv (s : ProtocolState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.epoch))
        (Nat.le (UInt64.toNat s.bounded_val) (UInt64.toNat s.cap_val))

    def Init (s : ProtocolState) : Prop :=
      And
        (s.prev_epoch = s.epoch)
        (Nat.le (UInt64.toNat s.bounded_val) (UInt64.toNat s.cap_val))

    def step (cand_epoch : UInt64) (raw_val : UInt64) (s : ProtocolState) : ProtocolState :=
      ProtocolState.mk
        s.epoch
        (if s.epoch < cand_epoch then cand_epoch else s.epoch)
        (if raw_val < s.cap_val then raw_val else s.cap_val)
        s.cap_val

    def Next (s : ProtocolState) (s_next : ProtocolState) : Prop :=
      ∃ (cand_epoch : UInt64), ∃ (raw_val : UInt64),
        s_next = step cand_epoch raw_val s

    def Spec : StateMachine ProtocolState :=
      StateMachine.mk Init Next

    theorem epoch_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (if cur < proposed then proposed else cur)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem val_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (if raw < cap then raw else cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : ProtocolState) (hInit : Init s) :
      SafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_epoch s.epoch (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : ProtocolState) (s_next : ProtocolState)
      (_hInv : SafetyInv s) (hNext : Next s s_next) :
      SafetyInv s_next :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (rv : UInt64), s_next = step ce rv s) =>
        Exists.elim hRest (fun (rv : UInt64) (hEq : s_next = step ce rv s) =>
          Eq.mpr
            (congrArg (fun (st : ProtocolState) => SafetyInv st) hEq)
            (And.intro
              (epoch_ge_prev s.epoch ce)
              (val_le_cap rv s.cap_val))))

    theorem safety_always :
      Satisfies (Runs Spec) (Always (Lift SafetyInv)) :=
      invariantSatisfies Spec SafetyInv init_establishes_inv next_preserves_inv

    end TlaAutopilotCruiseWheel
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def cruise_reply_not_repeated_isl (same_reply_count : UInt64) : Bool :=
      decide (same_reply_count < (2 : UInt64))
}
