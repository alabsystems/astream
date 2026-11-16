// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `unlocked_batch_three_phase_commit.rs`, mounted under `cfg(clean_islands)`.
clean {
    def visible_head_promote_advance_b145 (curHead : UInt64) (candHead : UInt64) : UInt64 :=
      if curHead < candHead then candHead else curHead

    def retention_wait_count_advance_b145 (curWaits : UInt64) (candWaits : UInt64) : UInt64 :=
      if curWaits < candWaits then candWaits else curWaits

    namespace Astream
    namespace Broker
    namespace TlaUnlockedBatchThreePhaseCommit
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

    structure UnlockedBatchThreePhaseCommitState where
      cur_0 : UInt64
      prev_0 : UInt64
      cur_1 : UInt64
      prev_1 : UInt64

    def UnlockedBatchThreePhaseCommitInv (s : UnlockedBatchThreePhaseCommitState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_0) (UInt64.toNat s.cur_0))
        (Nat.le (UInt64.toNat s.prev_1) (UInt64.toNat s.cur_1))

    def Init (s : UnlockedBatchThreePhaseCommitState) : Prop :=
      And
        (s.prev_0 = 0)
        (s.prev_1 = 0)

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (s : UnlockedBatchThreePhaseCommitState) : UnlockedBatchThreePhaseCommitState :=
      UnlockedBatchThreePhaseCommitState.mk
        (_root_.visible_head_promote_advance_b145 s.cur_0 c_0)
        s.cur_0
        (_root_.retention_wait_count_advance_b145 s.cur_1 c_1)
        s.cur_1

    def Next (s : UnlockedBatchThreePhaseCommitState) (s' : UnlockedBatchThreePhaseCommitState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64),
        s' = stepTransition c_0 c_1 s

    def Spec : StateMachine UnlockedBatchThreePhaseCommitState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.visible_head_promote_advance_b145 prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.retention_wait_count_advance_b145 prev cand)) :=
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

    theorem init_establishes_inv (s : UnlockedBatchThreePhaseCommitState) (hInit : Init s) :
      UnlockedBatchThreePhaseCommitInv s :=
      And.intro
        (zero_le_u64 s.prev_0 s.cur_0 (And.left hInit))
        (zero_le_u64 s.prev_1 s.cur_1 (And.right hInit))

    theorem next_preserves_inv (s : UnlockedBatchThreePhaseCommitState) (s' : UnlockedBatchThreePhaseCommitState)
      (_hInv : UnlockedBatchThreePhaseCommitInv s) (hNext : Next s s') :
      UnlockedBatchThreePhaseCommitInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hRest : ∃ (c_1 : UInt64), s' = stepTransition c_0 c_1 s) =>
        Exists.elim hRest (fun (c_1 : UInt64) (hEq : s' = stepTransition c_0 c_1 s) =>
          Eq.mpr
            (congrArg (fun (st : UnlockedBatchThreePhaseCommitState) => UnlockedBatchThreePhaseCommitInv st) hEq)
            (And.intro
              (helper_bound_0 s.cur_0 c_0)
              (helper_bound_1 s.cur_1 c_1))))

    theorem unlocked_batch_three_phase_commit_safety_always :
      Satisfies Spec (Always (Lift UnlockedBatchThreePhaseCommitInv)) :=
      invariantSatisfies Spec UnlockedBatchThreePhaseCommitInv init_establishes_inv next_preserves_inv

    end TlaUnlockedBatchThreePhaseCommit
    end Broker
    end Astream


    def direct_log_mutation_admissible_b145_isl
      (batchInFlight : Bool) (logPoisoned : Bool) : Bool :=
      and (not batchInFlight) (not logPoisoned)
}
