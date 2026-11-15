// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for distributed multi-worker step-DAG execution over astream-broker
// (`Astream.Engine.TlaDistributedDag`), mounted under `cfg(clean_islands)` in
// `distributed.rs`. Proves monotone broker-time lease expiry progression
// (`prevExpiry <= leaseExpiry`) and canonical earliest-offset commit winner convergence
// (`winnerOffset <= maxOffset`) across worker lease acquisitions, expired-lease takeovers,
// and racing commit records.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def dist_lease_expiry_advance (cur_expiry : UInt64) (proposed_expiry : UInt64) : UInt64 :=
      if cur_expiry < proposed_expiry then proposed_expiry else cur_expiry

    def dist_winner_offset_min (cur_winner : UInt64) (candidate_offset : UInt64) : UInt64 :=
      if candidate_offset < cur_winner then candidate_offset else cur_winner

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaDistributedDag)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaDistributedDag

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun k => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun b => ∀ n : Nat, P (drop n b)
    prefix:90 "□" => _root_.Astream.Engine.TlaDistributedDag.Always

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun b => M.Init (b 0) ∧ ∀ n : Nat, M.Next (b n) (b (Nat.succ n))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun b => pred (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (P : Formula State) : Prop :=
      ∀ b : Behavior State, Runs M b → P b
    infix:50 " ⊨ " => _root_.Astream.Engine.TlaDistributedDag.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (Inv : State → Prop)
        (hInit : ∀ s : State, M.Init s → Inv s)
        (hStep : ∀ s s' : State, Inv s → M.Next s s' → Inv s')
        (b : Behavior State) (hRun : Runs M b) (n : Nat) : Inv (b n) :=
      Nat.rec
        (motive := fun k => Inv (b k))
        (hInit (b 0) hRun.1)
        (fun k ih => hStep (b k) (b (Nat.succ k)) ih (hRun.2 k))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (Inv : State → Prop)
        (hInit : ∀ s : State, M.Init s → Inv s)
        (hStep : ∀ s s' : State, Inv s → M.Next s s' → Inv s') :
        M ⊨ □ (Lift Inv) :=
      fun b hRun n =>
        let hAt : Inv (b n) := invariantAt M Inv hInit hStep b hRun n
        let hEq : Nat.add n 0 = n := Nat.add_zero n
        Eq.mpr (congrArg (fun idx => Inv (b idx)) hEq) hAt

    theorem lease_advance_ge_cur (cur prop : UInt64) :
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.dist_lease_expiry_advance cur prop)) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur prop)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => prop))))
        (instDecidableUInt64Lt cur prop)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem winner_min_le_cur (cur cand : UInt64) :
        Nat.le (UInt64.toNat (_root_.dist_winner_offset_min cur cand)) (UInt64.toNat cur) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cur)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))) (UInt64.toNat cur))
        (instDecidableUInt64Lt cand cur)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    -- ========================================================================
    -- 3. Distributed Lease & Canonical Commit State Machine & Safety Theorem
    -- ========================================================================

    structure DistDagState where
      prevExpiry   : UInt64
      leaseExpiry  : UInt64
      winnerOffset : UInt64
      maxOffset    : UInt64

    def DistDagSafetyInv (s : DistDagState) : Prop :=
      Nat.le (UInt64.toNat s.prevExpiry) (UInt64.toNat s.leaseExpiry) ∧
      Nat.le (UInt64.toNat s.winnerOffset) (UInt64.toNat s.maxOffset)

    def Init (maxOffset : UInt64) (s : DistDagState) : Prop :=
      s.prevExpiry = (0 : UInt64) ∧
      s.leaseExpiry = (0 : UInt64) ∧
      s.winnerOffset = maxOffset ∧
      s.maxOffset = maxOffset

    def AcquireOrTakeoverLease (proposedExpiry : UInt64) (s sNext : DistDagState) : Prop :=
      sNext.prevExpiry = s.leaseExpiry ∧
      sNext.leaseExpiry = _root_.dist_lease_expiry_advance s.leaseExpiry proposedExpiry ∧
      sNext.winnerOffset = s.winnerOffset ∧
      sNext.maxOffset = s.maxOffset

    def ObserveCommit (candOffset : UInt64) (s sNext : DistDagState) : Prop :=
      sNext.prevExpiry = s.prevExpiry ∧
      sNext.leaseExpiry = s.leaseExpiry ∧
      sNext.winnerOffset = _root_.dist_winner_offset_min s.winnerOffset candOffset ∧
      sNext.maxOffset = s.maxOffset

    def Next (s sNext : DistDagState) : Prop :=
      (∃ pe : UInt64, AcquireOrTakeoverLease pe s sNext) ∨
      (∃ co : UInt64, ObserveCommit co s sNext)

    def Spec (maxOffset : UInt64) : StateMachine DistDagState :=
      StateMachine.mk (Init maxOffset) Next

    theorem init_establishes_inv (maxOffset : UInt64) (s : DistDagState)
        (hInit : Init maxOffset s) : DistDagSafetyInv s :=
      let hEqExp : s.prevExpiry = s.leaseExpiry :=
        Eq.trans hInit.1 (Eq.symm hInit.2.1)
      let hL : Nat.le (UInt64.toNat s.prevExpiry) (UInt64.toNat s.leaseExpiry) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.leaseExpiry)) hEqExp)
          (Nat.le.refl (UInt64.toNat s.leaseExpiry))
      let hEqWin : s.winnerOffset = s.maxOffset :=
        Eq.trans hInit.2.2.1 (Eq.symm hInit.2.2.2)
      let hW : Nat.le (UInt64.toNat s.winnerOffset) (UInt64.toNat s.maxOffset) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxOffset)) hEqWin)
          (Nat.le.refl (UInt64.toNat s.maxOffset))
      And.intro hL hW

    theorem acquireLease_preserves_inv (pe : UInt64) (s sNext : DistDagState)
        (hInv : DistDagSafetyInv s) (hAct : AcquireOrTakeoverLease pe s sNext) :
        DistDagSafetyInv sNext :=
      let hAdv : Nat.le (UInt64.toNat s.leaseExpiry)
          (UInt64.toNat (_root_.dist_lease_expiry_advance s.leaseExpiry pe)) :=
        lease_advance_ge_cur s.leaseExpiry pe
      let hL1 : Nat.le (UInt64.toNat sNext.prevExpiry)
          (UInt64.toNat (_root_.dist_lease_expiry_advance s.leaseExpiry pe)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x)
            (UInt64.toNat (_root_.dist_lease_expiry_advance s.leaseExpiry pe))) hAct.1)
          hAdv
      let hL2 : Nat.le (UInt64.toNat sNext.prevExpiry) (UInt64.toNat sNext.leaseExpiry) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.prevExpiry) (UInt64.toNat y)) hAct.2.1)
          hL1
      let hW1 : Nat.le (UInt64.toNat sNext.winnerOffset) (UInt64.toNat s.maxOffset) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxOffset)) hAct.2.2.1)
          hInv.2
      let hW2 : Nat.le (UInt64.toNat sNext.winnerOffset) (UInt64.toNat sNext.maxOffset) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.winnerOffset) (UInt64.toNat y)) hAct.2.2.2)
          hW1
      And.intro hL2 hW2

    theorem observeCommit_preserves_inv (co : UInt64) (s sNext : DistDagState)
        (hInv : DistDagSafetyInv s) (hAct : ObserveCommit co s sNext) :
        DistDagSafetyInv sNext :=
      let hL1 : Nat.le (UInt64.toNat sNext.prevExpiry) (UInt64.toNat s.leaseExpiry) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.leaseExpiry)) hAct.1)
          hInv.1
      let hL2 : Nat.le (UInt64.toNat sNext.prevExpiry) (UInt64.toNat sNext.leaseExpiry) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.prevExpiry) (UInt64.toNat y)) hAct.2.1)
          hL1
      let hMin : Nat.le (UInt64.toNat (_root_.dist_winner_offset_min s.winnerOffset co))
          (UInt64.toNat s.maxOffset) :=
        Nat.le_trans (winner_min_le_cur s.winnerOffset co) hInv.2
      let hW1 : Nat.le (UInt64.toNat sNext.winnerOffset) (UInt64.toNat s.maxOffset) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxOffset)) hAct.2.2.1)
          hMin
      let hW2 : Nat.le (UInt64.toNat sNext.winnerOffset) (UInt64.toNat sNext.maxOffset) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.winnerOffset) (UInt64.toNat y)) hAct.2.2.2)
          hW1
      And.intro hL2 hW2

    theorem next_preserves_inv (s sNext : DistDagState)
        (hInv : DistDagSafetyInv s) (hNext : Next s sNext) :
        DistDagSafetyInv sNext :=
      Or.elim hNext
        (fun hExL =>
          Exists.elim hExL (fun pe hL => acquireLease_preserves_inv pe s sNext hInv hL))
        (fun hExC =>
          Exists.elim hExC (fun co hC => observeCommit_preserves_inv co s sNext hInv hC))

    theorem spec_satisfies_distributed_dag_safety (maxOffset : UInt64) :
        (Spec maxOffset) ⊨ □ (Lift DistDagSafetyInv) :=
      invariantSatisfies (Spec maxOffset) DistDagSafetyInv
        (init_establishes_inv maxOffset)
        next_preserves_inv

    end TlaDistributedDag
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def dist_lease_expired_isl (lease_expiry_ms : UInt64) (now_bt_ms : UInt64) : Bool :=
      decide (lease_expiry_ms ≤ now_bt_ms)
}
