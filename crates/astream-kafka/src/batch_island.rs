// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `record_batch.rs` and `server.rs`, mounted only under
// `cfg(clean_islands)`. Every other compiler calls the plain-Rust twins in `twins.rs`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    -- Monotone Kafka partition log-end-offset advance (`max(cur_head, next_head)`).
    def kafka_batch_offset_advance (cur_head : UInt64) (next_head : UInt64) : UInt64 :=
      if cur_head < next_head then next_head else cur_head

    -- Clamp fetched RecordBatch payload bytes to the partition/request `max_bytes` budget.
    def kafka_fetch_clamp_bytes (avail : UInt64) (max_bytes : UInt64) : UInt64 :=
      if avail < max_bytes then avail else max_bytes

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Kafka.TlaRecordBatchLog)
    -- ========================================================================
    namespace Astream
    namespace Kafka
    namespace TlaRecordBatchLog

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

    prefix:100 "□" => _root_.Astream.Kafka.TlaRecordBatchLog.Always
    infixl:45 " ⊨ " => _root_.Astream.Kafka.TlaRecordBatchLog.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      @Nat.rec (fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun step => hStep (b k) (b (Nat.succ k)) ih step)
            (fun stutter => Eq.mpr (congrArg I stutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    theorem advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.kafka_batch_offset_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clamp_fetch_le_max : forall (avail : UInt64) (maxB : UInt64),
        Nat.le (UInt64.toNat (_root_.kafka_fetch_clamp_bytes avail maxB)) (UInt64.toNat maxB) :=
      fun avail maxB => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt avail maxB)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => maxB) (fun _ => avail))) (UInt64.toNat maxB))
        (instDecidableUInt64Lt avail maxB)
        (fun _ => @Nat.le.refl (UInt64.toNat maxB))
        (fun hLt => Nat.le_of_lt hLt)

    -- ========================================================================
    -- 3. TLA+ Specification: Monotone Partition High-Watermark & Bounded Fetch
    -- ========================================================================
    structure PartitionLogState where
      baseOffset     : UInt64
      highWatermark  : UInt64
      lastFetchBytes : UInt64
      maxFetchCap    : UInt64

    def PartitionLogSafetyInv (s : PartitionLogState) : Prop :=
      Nat.le (UInt64.toNat s.baseOffset) (UInt64.toNat s.highWatermark) ∧
      Nat.le (UInt64.toNat s.lastFetchBytes) (UInt64.toNat s.maxFetchCap)

    def Init (base : UInt64) (cap : UInt64) (s : PartitionLogState) : Prop :=
      s.baseOffset = base ∧
      s.highWatermark = base ∧
      s.lastFetchBytes = (0 : UInt64) ∧
      s.maxFetchCap = cap

    def AppendBatch (candHead : UInt64) (s sNext : PartitionLogState) : Prop :=
      sNext.baseOffset = s.baseOffset ∧
      sNext.highWatermark = _root_.kafka_batch_offset_advance s.highWatermark candHead ∧
      sNext.lastFetchBytes = s.lastFetchBytes ∧
      sNext.maxFetchCap = s.maxFetchCap

    def ServeFetch (availBytes : UInt64) (s sNext : PartitionLogState) : Prop :=
      sNext.baseOffset = s.baseOffset ∧
      sNext.highWatermark = s.highWatermark ∧
      sNext.lastFetchBytes = _root_.kafka_fetch_clamp_bytes availBytes s.maxFetchCap ∧
      sNext.maxFetchCap = s.maxFetchCap

    def Next (s sNext : PartitionLogState) : Prop :=
      (∃ cand : UInt64, AppendBatch cand s sNext) ∨
      (∃ avail : UInt64, ServeFetch avail s sNext)

    def Spec (base : UInt64) (cap : UInt64) : StateMachine PartitionLogState :=
      StateMachine.mk (Init base cap) Next

    theorem init_establishes_inv (base : UInt64) (cap : UInt64) (s : PartitionLogState)
        (hInit : Init base cap s) : PartitionLogSafetyInv s :=
      let hEqHw : s.baseOffset = s.highWatermark := Eq.trans hInit.1 (Eq.symm hInit.2.1)
      let hBaseLeHw : Nat.le (UInt64.toNat s.baseOffset) (UInt64.toNat s.highWatermark) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.highWatermark)) hEqHw)
          (@Nat.le.refl (UInt64.toNat s.highWatermark))
      let hZeroLe : Nat.le (UInt64.toNat (0 : UInt64)) (UInt64.toNat s.maxFetchCap) :=
        Nat.zero_le (UInt64.toNat s.maxFetchCap)
      let hFetchLe : Nat.le (UInt64.toNat s.lastFetchBytes) (UInt64.toNat s.maxFetchCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxFetchCap)) hInit.2.2.1)
          hZeroLe
      And.intro hBaseLeHw hFetchLe

    theorem appendBatch_preserves_inv (cand : UInt64) (s sNext : PartitionLogState)
        (hInv : PartitionLogSafetyInv s) (hAct : AppendBatch cand s sNext) :
        PartitionLogSafetyInv sNext :=
      let hBaseEq : sNext.baseOffset = s.baseOffset := hAct.1
      let hHwEq : sNext.highWatermark = _root_.kafka_batch_offset_advance s.highWatermark cand := hAct.2.1
      let hFetchEq : sNext.lastFetchBytes = s.lastFetchBytes := hAct.2.2.1
      let hCapEq : sNext.maxFetchCap = s.maxFetchCap := hAct.2.2.2
      let hStepHw : Nat.le (UInt64.toNat s.baseOffset) (UInt64.toNat (_root_.kafka_batch_offset_advance s.highWatermark cand)) :=
        Nat.le_trans hInv.1 (advance_ge_cur s.highWatermark cand)
      let hHw1 : Nat.le (UInt64.toNat s.baseOffset) (UInt64.toNat sNext.highWatermark) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.baseOffset) (UInt64.toNat y)) hHwEq) hStepHw
      let hHwNext : Nat.le (UInt64.toNat sNext.baseOffset) (UInt64.toNat sNext.highWatermark) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.highWatermark)) hBaseEq) hHw1
      let hF1 : Nat.le (UInt64.toNat sNext.lastFetchBytes) (UInt64.toNat s.maxFetchCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxFetchCap)) hFetchEq) hInv.2
      let hFetchNext : Nat.le (UInt64.toNat sNext.lastFetchBytes) (UInt64.toNat sNext.maxFetchCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.lastFetchBytes) (UInt64.toNat y)) hCapEq) hF1
      And.intro hHwNext hFetchNext

    theorem serveFetch_preserves_inv (avail : UInt64) (s sNext : PartitionLogState)
        (hInv : PartitionLogSafetyInv s) (hAct : ServeFetch avail s sNext) :
        PartitionLogSafetyInv sNext :=
      let hBaseEq : sNext.baseOffset = s.baseOffset := hAct.1
      let hHwEq : sNext.highWatermark = s.highWatermark := hAct.2.1
      let hFetchEq : sNext.lastFetchBytes = _root_.kafka_fetch_clamp_bytes avail s.maxFetchCap := hAct.2.2.1
      let hCapEq : sNext.maxFetchCap = s.maxFetchCap := hAct.2.2.2
      let hHw1 : Nat.le (UInt64.toNat s.baseOffset) (UInt64.toNat sNext.highWatermark) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.baseOffset) (UInt64.toNat y)) hHwEq) hInv.1
      let hHwNext : Nat.le (UInt64.toNat sNext.baseOffset) (UInt64.toNat sNext.highWatermark) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.highWatermark)) hBaseEq) hHw1
      let hF1 : Nat.le (UInt64.toNat sNext.lastFetchBytes) (UInt64.toNat s.maxFetchCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxFetchCap)) hFetchEq)
          (clamp_fetch_le_max avail s.maxFetchCap)
      let hFetchNext : Nat.le (UInt64.toNat sNext.lastFetchBytes) (UInt64.toNat sNext.maxFetchCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.lastFetchBytes) (UInt64.toNat y)) hCapEq) hF1
      And.intro hHwNext hFetchNext

    theorem next_preserves_inv (s sNext : PartitionLogState)
        (hInv : PartitionLogSafetyInv s) (hNext : Next s sNext) :
        PartitionLogSafetyInv sNext :=
      Or.elim hNext
        (fun hApp => Exists.elim hApp (fun cand hA => appendBatch_preserves_inv cand s sNext hInv hA))
        (fun hFet => Exists.elim hFet (fun avail hF => serveFetch_preserves_inv avail s sNext hInv hF))

    theorem spec_satisfies_partition_log_safety (base : UInt64) (cap : UInt64) :
        (Spec base cap) ⊨ □ (Lift PartitionLogSafetyInv) :=
      invariantSatisfies (Spec base cap) PartitionLogSafetyInv
        (init_establishes_inv base cap)
        next_preserves_inv

    end TlaRecordBatchLog
    end Kafka
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def record_batch_magic_v2_isl (magic : UInt8) : Bool :=
      decide (magic = (2 : UInt8))
}
