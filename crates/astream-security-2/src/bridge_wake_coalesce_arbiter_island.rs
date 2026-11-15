// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `bridge_wake_coalesce_arbiter.rs`, mounted under `cfg(clean_islands)`.
clean {
    def wake_budget_used_clamp_b124 (candUsed : UInt64) (maxBudget : UInt64) : UInt64 :=
      if candUsed < maxBudget then candUsed else maxBudget

    def wake_offset_advance_b124 (curOff : UInt64) (candOff : UInt64) : UInt64 :=
      if curOff < candOff then candOff else curOff

    def wake_priority_max_b124 (curRank : UInt64) (candRank : UInt64) : UInt64 :=
      if curRank < candRank then candRank else curRank

    namespace Astream
    namespace Pump
    namespace TlaBridgeWakeCoalesceArbiter
    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop
    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)
    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      Nat.rec
        (motive := fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun hNext => hStep (b k) (b (Nat.succ k)) ih hNext)
            (fun hStutter => Eq.mpr (congrArg I hStutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        Satisfies M (Always (Lift I)) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure BridgeWakeCoalesceArbiterState where
      val_0 : UInt64
      cap_0 : UInt64
      cur_1 : UInt64
      prev_1 : UInt64
      cur_2 : UInt64
      prev_2 : UInt64

    def BridgeWakeCoalesceArbiterInv (s : BridgeWakeCoalesceArbiterState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.val_0) (UInt64.toNat s.cap_0))
        (And (Nat.le (UInt64.toNat s.prev_1) (UInt64.toNat s.cur_1)) (Nat.le (UInt64.toNat s.prev_2) (UInt64.toNat s.cur_2)))

    def Init (s : BridgeWakeCoalesceArbiterState) : Prop :=
      And
        (s.val_0 = 0)
        (And (s.prev_1 = 0) (s.prev_2 = 0))

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (c_2 : UInt64) (s : BridgeWakeCoalesceArbiterState) : BridgeWakeCoalesceArbiterState :=
      BridgeWakeCoalesceArbiterState.mk
        (_root_.wake_budget_used_clamp_b124 c_0 s.cap_0)
        s.cap_0
        (_root_.wake_offset_advance_b124 s.cur_1 c_1)
        s.cur_1
        (_root_.wake_priority_max_b124 s.cur_2 c_2)
        s.cur_2

    def Next (s : BridgeWakeCoalesceArbiterState) (s' : BridgeWakeCoalesceArbiterState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64), ∃ (c_2 : UInt64),
        s' = stepTransition c_0 c_1 c_2 s

    def Spec : StateMachine BridgeWakeCoalesceArbiterState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.wake_budget_used_clamp_b124 raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.wake_offset_advance_b124 prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_2 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.wake_priority_max_b124 prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : BridgeWakeCoalesceArbiterState) (hInit : Init s) :
      BridgeWakeCoalesceArbiterInv s :=
      And.intro
        (zero_le_u64 s.val_0 s.cap_0 (And.left hInit))
        (And.intro
          (zero_le_u64 s.prev_1 s.cur_1 (And.left (And.right hInit)))
          (zero_le_u64 s.prev_2 s.cur_2 (And.right (And.right hInit))))

    theorem next_preserves_inv (s : BridgeWakeCoalesceArbiterState) (s' : BridgeWakeCoalesceArbiterState)
      (_hInv : BridgeWakeCoalesceArbiterInv s) (hNext : Next s s') :
      BridgeWakeCoalesceArbiterInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hR1 : ∃ (c_1 : UInt64), ∃ (c_2 : UInt64), s' = stepTransition c_0 c_1 c_2 s) =>
        Exists.elim hR1 (fun (c_1 : UInt64) (hR2 : ∃ (c_2 : UInt64), s' = stepTransition c_0 c_1 c_2 s) =>
          Exists.elim hR2 (fun (c_2 : UInt64) (hEq : s' = stepTransition c_0 c_1 c_2 s) =>
            Eq.mpr
              (congrArg (fun (st : BridgeWakeCoalesceArbiterState) => BridgeWakeCoalesceArbiterInv st) hEq)
              (And.intro
                (helper_bound_0 c_0 s.cap_0)
                (And.intro
                  (helper_bound_1 s.cur_1 c_1)
                  (helper_bound_2 s.cur_2 c_2))))))

    theorem bridge_wake_coalesce_arbiter_safety_always :
      Satisfies Spec (Always (Lift BridgeWakeCoalesceArbiterInv)) :=
      invariantSatisfies Spec BridgeWakeCoalesceArbiterInv init_establishes_inv next_preserves_inv

    end TlaBridgeWakeCoalesceArbiter
    end Pump
    end Astream


    def wake_budget_has_room_b124_isl (wakesUsed : UInt64) (maxBudget : UInt64) : Bool :=
      decide (LT.lt wakesUsed maxBudget)
}
