// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `SubscribeGroup` / `/a/commit` monotone group watermarks and
// in-flight lease bounds (`Astream.Broker.TlaConsumerGroupLease`), mounted under
// `cfg(clean_islands)` in `subscribe_group_fair_lease.rs`. Proves
// `committedOffset <= headOffset` and `leasedCount <= maxInFlight`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def group_commit_clamp (candidate : UInt64) (head : UInt64) : UInt64 :=
      if candidate < head then candidate else head

    def group_lease_clamp (leased : UInt64) (max_in_flight : UInt64) : UInt64 :=
      if leased < max_in_flight then leased else max_in_flight

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaConsumerGroupLease

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

    -- ========================================================================
    -- 3. Consumer-Group Watermark & Lease State Machine
    -- ========================================================================

    structure GroupState where
      committedOffset : UInt64
      headOffset      : UInt64
      leasedCount     : UInt64
      maxInFlight     : UInt64

    def GroupCommitSafetyInv (s : GroupState) : Prop :=
      Nat.le (UInt64.toNat s.committedOffset) (UInt64.toNat s.headOffset) ∧
      Nat.le (UInt64.toNat s.leasedCount) (UInt64.toNat s.maxInFlight)

    def Init (maxInFlight : UInt64) (s : GroupState) : Prop :=
      s.committedOffset = (0 : UInt64) ∧
      s.headOffset = (0 : UInt64) ∧
      s.leasedCount = (0 : UInt64) ∧
      s.maxInFlight = maxInFlight

    def StepLeaseOrCommit (rawCommit newHead rawLeased : UInt64)
        (s sNext : GroupState) : Prop :=
      sNext.committedOffset = _root_.group_commit_clamp rawCommit newHead ∧
      sNext.headOffset = newHead ∧
      sNext.leasedCount = _root_.group_lease_clamp rawLeased s.maxInFlight ∧
      sNext.maxInFlight = s.maxInFlight

    def Next (s sNext : GroupState) : Prop :=
      ∃ rc : UInt64, ∃ nh : UInt64, ∃ rl : UInt64, StepLeaseOrCommit rc nh rl s sNext

    def Spec (maxInFlight : UInt64) : StateMachine GroupState :=
      StateMachine.mk (Init maxInFlight) Next

    theorem commit_clamp_le : forall (c : UInt64) (h : UInt64),
        Nat.le (UInt64.toNat (_root_.group_commit_clamp c h)) (UInt64.toNat h) :=
      fun c h => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt c h)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => h) (fun _ => c))) (UInt64.toNat h))
        (instDecidableUInt64Lt c h)
        (fun _ => Nat.le.refl (UInt64.toNat h))
        (fun hLt => Nat.le_of_lt hLt)

    theorem lease_clamp_le : forall (l : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.group_lease_clamp l cap)) (UInt64.toNat cap) :=
      fun l cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt l cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => l))) (UInt64.toNat cap))
        (instDecidableUInt64Lt l cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxInFlight : UInt64) (s : GroupState)
        (hInit : Init maxInFlight s) : GroupCommitSafetyInv s :=
      And.intro
        (zero_u64_le s.committedOffset s.headOffset hInit.1)
        (zero_u64_le s.leasedCount s.maxInFlight hInit.2.2.1)

    theorem step_preserves_inv (rc nh rl : UInt64) (s sNext : GroupState)
        (hAct : StepLeaseOrCommit rc nh rl s sNext) : GroupCommitSafetyInv sNext :=
      let hC1 : Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat nh) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat nh)) hAct.1)
          (commit_clamp_le rc nh)
      let hC2 : Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat sNext.headOffset) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat y)) hAct.2.1)
          hC1
      let hL1 : Nat.le (UInt64.toNat sNext.leasedCount) (UInt64.toNat s.maxInFlight) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxInFlight)) hAct.2.2.1)
          (lease_clamp_le rl s.maxInFlight)
      let hL2 : Nat.le (UInt64.toNat sNext.leasedCount) (UInt64.toNat sNext.maxInFlight) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.leasedCount) (UInt64.toNat y)) hAct.2.2.2)
          hL1
      And.intro hC2 hL2

    theorem next_preserves_inv (s sNext : GroupState)
        (_hInv : GroupCommitSafetyInv s) (hNext : Next s sNext) :
        GroupCommitSafetyInv sNext :=
      Exists.elim hNext (fun rc hEx1 =>
        Exists.elim hEx1 (fun nh hEx2 =>
          Exists.elim hEx2 (fun rl hAct => step_preserves_inv rc nh rl s sNext hAct)))

    theorem spec_satisfies_group_commit_safety (maxInFlight : UInt64) :
        Satisfies (Spec maxInFlight) (Always (Lift GroupCommitSafetyInv)) :=
      invariantSatisfies (Spec maxInFlight) GroupCommitSafetyInv
        (init_establishes_inv maxInFlight)
        next_preserves_inv

    end TlaConsumerGroupLease
    end Broker
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def group_commit_operand_valid_isl (upto_offset : UInt64) (visible_head : UInt64) : Bool :=
      decide (upto_offset < visible_head)
}
