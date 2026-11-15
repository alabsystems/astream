// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for consistent-hash shard routing & live shard-split drain fencing
// (`Astream.Broker.TlaShardedRingMigration`), mounted under `cfg(clean_islands)` in
// `sharded_ring_rebalancer.rs`. Proves `targetShard <= maxShardIdx` and
// `drainedOffset <= barrierOffset` across shard routing and live migrations.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def ring_shard_idx_clamp (shard_idx : UInt64) (max_shard_idx : UInt64) : UInt64 :=
      if shard_idx < max_shard_idx then shard_idx else max_shard_idx

    def ring_drain_offset_clamp (drained_off : UInt64) (barrier_off : UInt64) : UInt64 :=
      if drained_off < barrier_off then drained_off else barrier_off

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Broker.TlaShardedRingMigration)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaShardedRingMigration

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
    -- 3. Consistent-Hash Shard Ring & Drain Barrier State Machine
    -- ========================================================================

    structure ShardMigrationState where
      targetShard   : UInt64
      maxShardIdx   : UInt64
      drainedOffset : UInt64
      barrierOffset : UInt64

    def ShardMigrationInv (s : ShardMigrationState) : Prop :=
      Nat.le (UInt64.toNat s.targetShard) (UInt64.toNat s.maxShardIdx) ∧
      Nat.le (UInt64.toNat s.drainedOffset) (UInt64.toNat s.barrierOffset)

    def Init (maxShardIdx barrierOffset : UInt64) (s : ShardMigrationState) : Prop :=
      s.targetShard = (0 : UInt64) ∧
      s.maxShardIdx = maxShardIdx ∧
      s.drainedOffset = (0 : UInt64) ∧
      s.barrierOffset = barrierOffset

    def RouteOrDrain (rawShard rawDrained : UInt64) (s sNext : ShardMigrationState) : Prop :=
      sNext.targetShard = _root_.ring_shard_idx_clamp rawShard s.maxShardIdx ∧
      sNext.maxShardIdx = s.maxShardIdx ∧
      sNext.drainedOffset = _root_.ring_drain_offset_clamp rawDrained s.barrierOffset ∧
      sNext.barrierOffset = s.barrierOffset

    def Next (s sNext : ShardMigrationState) : Prop :=
      ∃ rs : UInt64, ∃ rd : UInt64, RouteOrDrain rs rd s sNext

    def Spec (maxShardIdx barrierOffset : UInt64) : StateMachine ShardMigrationState :=
      StateMachine.mk (Init maxShardIdx barrierOffset) Next

    theorem shard_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.ring_shard_idx_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem drain_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.ring_drain_offset_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxShardIdx barrierOffset : UInt64) (s : ShardMigrationState)
        (hInit : Init maxShardIdx barrierOffset s) : ShardMigrationInv s :=
      And.intro
        (zero_u64_le s.targetShard s.maxShardIdx hInit.1)
        (zero_u64_le s.drainedOffset s.barrierOffset hInit.2.2.1)

    theorem routeOrDrain_preserves_inv (rs rd : UInt64) (s sNext : ShardMigrationState)
        (hAct : RouteOrDrain rs rd s sNext) : ShardMigrationInv sNext :=
      let hS1 : Nat.le (UInt64.toNat sNext.targetShard) (UInt64.toNat s.maxShardIdx) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxShardIdx)) hAct.1)
          (shard_clamp_le rs s.maxShardIdx)
      let hS2 : Nat.le (UInt64.toNat sNext.targetShard) (UInt64.toNat sNext.maxShardIdx) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.targetShard) (UInt64.toNat y)) hAct.2.1)
          hS1
      let hD1 : Nat.le (UInt64.toNat sNext.drainedOffset) (UInt64.toNat s.barrierOffset) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.barrierOffset)) hAct.2.2.1)
          (drain_clamp_le rd s.barrierOffset)
      let hD2 : Nat.le (UInt64.toNat sNext.drainedOffset) (UInt64.toNat sNext.barrierOffset) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.drainedOffset) (UInt64.toNat y)) hAct.2.2.2)
          hD1
      And.intro hS2 hD2

    theorem next_preserves_inv (s sNext : ShardMigrationState)
        (_hInv : ShardMigrationInv s) (hNext : Next s sNext) : ShardMigrationInv sNext :=
      Exists.elim hNext (fun rs hEx2 =>
        Exists.elim hEx2 (fun rd hAct => routeOrDrain_preserves_inv rs rd s sNext hAct))

    theorem spec_satisfies_shard_ring_migration_safety (maxShardIdx barrierOffset : UInt64) :
        Satisfies (Spec maxShardIdx barrierOffset) (Always (Lift ShardMigrationInv)) :=
      invariantSatisfies (Spec maxShardIdx barrierOffset) ShardMigrationInv
        (init_establishes_inv maxShardIdx barrierOffset)
        next_preserves_inv

    end TlaShardedRingMigration
    end Broker
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def shard_drain_complete_isl (drained_off : UInt64) (barrier_off : UInt64) : Bool :=
      decide (barrier_off ≤ drained_off)
}
