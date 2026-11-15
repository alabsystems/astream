// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for replicated-cluster quorum leader election and epoch fencing
// (`Astream.Broker.TlaLeaderFailover`), mounted under `cfg(clean_islands)` in
// `failover.rs`. Proves monotone leader-generation epoch advancement
// (`prevEpoch <= adoptedEpoch`) and bounded quorum vote accounting
// (`quorumVotes <= clusterSize`) across leader promotions and stale-leader fencing.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def failover_epoch_advance (cur_epoch : UInt64) (proposed_epoch : UInt64) : UInt64 :=
      if cur_epoch < proposed_epoch then proposed_epoch else cur_epoch

    def failover_quorum_clamp (votes : UInt64) (cluster_size : UInt64) : UInt64 :=
      if votes < cluster_size then votes else cluster_size

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Broker.TlaLeaderFailover)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaLeaderFailover

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaLeaderFailover.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaLeaderFailover.Always

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
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    -- ========================================================================
    -- 3. Quorum Leader Failover & Zombie-Epoch Fencing State Machine
    -- ========================================================================

    structure FailoverState where
      prevEpoch    : UInt64
      adoptedEpoch : UInt64
      quorumVotes  : UInt64
      clusterSize  : UInt64

    def FailoverSafetyInv (s : FailoverState) : Prop :=
      Nat.le (UInt64.toNat s.prevEpoch) (UInt64.toNat s.adoptedEpoch) ∧
      Nat.le (UInt64.toNat s.quorumVotes) (UInt64.toNat s.clusterSize)

    def Init (clusterSize : UInt64) (s : FailoverState) : Prop :=
      s.prevEpoch = (0 : UInt64) ∧
      s.adoptedEpoch = (0 : UInt64) ∧
      s.quorumVotes = (0 : UInt64) ∧
      s.clusterSize = clusterSize

    def ElectAndPromote (proposedEpoch rawVotes : UInt64) (s sNext : FailoverState) : Prop :=
      sNext.prevEpoch = s.adoptedEpoch ∧
      sNext.adoptedEpoch = _root_.failover_epoch_advance s.adoptedEpoch proposedEpoch ∧
      sNext.quorumVotes = _root_.failover_quorum_clamp rawVotes s.clusterSize ∧
      sNext.clusterSize = s.clusterSize

    def FenceStaleLeader (zombieEpoch : UInt64) (s sNext : FailoverState) : Prop :=
      LT.lt zombieEpoch s.adoptedEpoch ∧
      sNext.prevEpoch = s.prevEpoch ∧
      sNext.adoptedEpoch = s.adoptedEpoch ∧
      sNext.quorumVotes = s.quorumVotes ∧
      sNext.clusterSize = s.clusterSize

    def Next (s sNext : FailoverState) : Prop :=
      (∃ pe : UInt64, ∃ rv : UInt64, ElectAndPromote pe rv s sNext) ∨
      (∃ ze : UInt64, FenceStaleLeader ze s sNext)

    def Spec (clusterSize : UInt64) : StateMachine FailoverState :=
      StateMachine.mk (Init clusterSize) Next

    theorem epoch_advance_ge_cur : forall (cur : UInt64) (prop : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.failover_epoch_advance cur prop)) :=
      fun cur prop => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur prop)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => prop))))
        (instDecidableUInt64Lt cur prop)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem quorum_clamp_le : forall (votes : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.failover_quorum_clamp votes cap)) (UInt64.toNat cap) :=
      fun votes cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt votes cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => votes))) (UInt64.toNat cap))
        (instDecidableUInt64Lt votes cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (clusterSize : UInt64) (s : FailoverState)
        (hInit : Init clusterSize s) : FailoverSafetyInv s :=
      let hEqEp : s.prevEpoch = s.adoptedEpoch :=
        Eq.trans hInit.1 (Eq.symm hInit.2.1)
      let hE : Nat.le (UInt64.toNat s.prevEpoch) (UInt64.toNat s.adoptedEpoch) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.adoptedEpoch)) hEqEp)
          (Nat.le.refl (UInt64.toNat s.adoptedEpoch))
      And.intro hE (zero_u64_le s.quorumVotes s.clusterSize hInit.2.2.1)

    theorem electAndPromote_preserves_inv (pe rv : UInt64) (s sNext : FailoverState)
        (hAct : ElectAndPromote pe rv s sNext) : FailoverSafetyInv sNext :=
      let hAdv : Nat.le (UInt64.toNat s.adoptedEpoch)
          (UInt64.toNat (_root_.failover_epoch_advance s.adoptedEpoch pe)) :=
        epoch_advance_ge_cur s.adoptedEpoch pe
      let hE1 : Nat.le (UInt64.toNat sNext.prevEpoch)
          (UInt64.toNat (_root_.failover_epoch_advance s.adoptedEpoch pe)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x)
            (UInt64.toNat (_root_.failover_epoch_advance s.adoptedEpoch pe))) hAct.1)
          hAdv
      let hE2 : Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat sNext.adoptedEpoch) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat y)) hAct.2.1)
          hE1
      let hQ1 : Nat.le (UInt64.toNat sNext.quorumVotes) (UInt64.toNat s.clusterSize) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.clusterSize)) hAct.2.2.1)
          (quorum_clamp_le rv s.clusterSize)
      let hQ2 : Nat.le (UInt64.toNat sNext.quorumVotes) (UInt64.toNat sNext.clusterSize) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.quorumVotes) (UInt64.toNat y)) hAct.2.2.2)
          hQ1
      And.intro hE2 hQ2

    theorem fenceStaleLeader_preserves_inv (ze : UInt64) (s sNext : FailoverState)
        (hInv : FailoverSafetyInv s) (hAct : FenceStaleLeader ze s sNext) :
        FailoverSafetyInv sNext :=
      let hE1 : Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat s.adoptedEpoch) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.adoptedEpoch)) hAct.2.1)
          hInv.1
      let hE2 : Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat sNext.adoptedEpoch) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat y)) hAct.2.2.1)
          hE1
      let hQ1 : Nat.le (UInt64.toNat sNext.quorumVotes) (UInt64.toNat s.clusterSize) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.clusterSize)) hAct.2.2.2.1)
          hInv.2
      let hQ2 : Nat.le (UInt64.toNat sNext.quorumVotes) (UInt64.toNat sNext.clusterSize) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.quorumVotes) (UInt64.toNat y)) hAct.2.2.2.2)
          hQ1
      And.intro hE2 hQ2

    theorem next_preserves_inv (s sNext : FailoverState)
        (hInv : FailoverSafetyInv s) (hNext : Next s sNext) :
        FailoverSafetyInv sNext :=
      Or.elim hNext
        (fun hEx1 =>
          Exists.elim hEx1 (fun pe hEx2 =>
            Exists.elim hEx2 (fun rv hEl => electAndPromote_preserves_inv pe rv s sNext hEl)))
        (fun hExF =>
          Exists.elim hExF (fun ze hFn => fenceStaleLeader_preserves_inv ze s sNext hInv hFn))

    theorem spec_satisfies_leader_failover_safety (clusterSize : UInt64) :
        (Spec clusterSize) ⊨ □ (Lift FailoverSafetyInv) :=
      invariantSatisfies (Spec clusterSize) FailoverSafetyInv
        (init_establishes_inv clusterSize)
        next_preserves_inv

    end TlaLeaderFailover
    end Broker
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def failover_fences_stale_isl (leader_gen : UInt64) (adopted_gen : UInt64) : Bool :=
      decide (leader_gen < adopted_gen)

    def failover_lease_expired_isl (now_ms : UInt64) (threshold_ms : UInt64) : Bool :=
      decide (threshold_ms ≤ now_ms)
}
