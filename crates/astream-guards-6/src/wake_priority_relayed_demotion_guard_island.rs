// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `wake_priority_relayed_demotion_guard.rs`, mounted under `cfg(clean_islands)`.
clean {
    def wake_rank_cap_clamp_b156 (candRank : UInt64) (maxRank : UInt64) : UInt64 :=
      if candRank < maxRank then candRank else maxRank

    def wake_batch_rank_advance_b156 (curRank : UInt64) (candRank : UInt64) : UInt64 :=
      if curRank < candRank then candRank else curRank

    namespace Astream
    namespace Wire
    namespace TlaWakePriorityRelayedDemotionGuard
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

    structure WakePriorityRelayedDemotionGuardState where
      val_0 : UInt64
      cap_0 : UInt64
      cur_1 : UInt64
      prev_1 : UInt64

    def WakePriorityRelayedDemotionGuardInv (s : WakePriorityRelayedDemotionGuardState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.val_0) (UInt64.toNat s.cap_0))
        (Nat.le (UInt64.toNat s.prev_1) (UInt64.toNat s.cur_1))

    def Init (s : WakePriorityRelayedDemotionGuardState) : Prop :=
      And
        (s.val_0 = 0)
        (s.prev_1 = 0)

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (s : WakePriorityRelayedDemotionGuardState) : WakePriorityRelayedDemotionGuardState :=
      WakePriorityRelayedDemotionGuardState.mk
        (_root_.wake_rank_cap_clamp_b156 c_0 s.cap_0)
        s.cap_0
        (_root_.wake_batch_rank_advance_b156 s.cur_1 c_1)
        s.cur_1

    def Next (s : WakePriorityRelayedDemotionGuardState) (s' : WakePriorityRelayedDemotionGuardState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64),
        s' = stepTransition c_0 c_1 s

    def Spec : StateMachine WakePriorityRelayedDemotionGuardState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.wake_rank_cap_clamp_b156 raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.wake_batch_rank_advance_b156 prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : WakePriorityRelayedDemotionGuardState) (hInit : Init s) :
      WakePriorityRelayedDemotionGuardInv s :=
      And.intro
        (zero_le_u64 s.val_0 s.cap_0 (And.left hInit))
        (zero_le_u64 s.prev_1 s.cur_1 (And.right hInit))

    theorem next_preserves_inv (s : WakePriorityRelayedDemotionGuardState) (s' : WakePriorityRelayedDemotionGuardState)
      (_hInv : WakePriorityRelayedDemotionGuardInv s) (hNext : Next s s') :
      WakePriorityRelayedDemotionGuardInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hRest : ∃ (c_1 : UInt64), s' = stepTransition c_0 c_1 s) =>
        Exists.elim hRest (fun (c_1 : UInt64) (hEq : s' = stepTransition c_0 c_1 s) =>
          Eq.mpr
            (congrArg (fun (st : WakePriorityRelayedDemotionGuardState) => WakePriorityRelayedDemotionGuardInv st) hEq)
            (And.intro
              (helper_bound_0 c_0 s.cap_0)
              (helper_bound_1 s.cur_1 c_1))))

    theorem wake_priority_relayed_demotion_guard_safety_always :
      Satisfies Spec (Always (Lift WakePriorityRelayedDemotionGuardInv)) :=
      invariantSatisfies Spec WakePriorityRelayedDemotionGuardInv init_establishes_inv next_preserves_inv

    end TlaWakePriorityRelayedDemotionGuard
    end Wire
    end Astream


    def coalesced_wake_fires_b156_isl
      (batchRank : UInt64)
      (controlRank : UInt64)
      (windowUsed : UInt64)
      (windowBudget : UInt64) : Bool :=
      and (decide (0 < batchRank)) (or (decide (batchRank = controlRank)) (decide (windowUsed < windowBudget)))
}
