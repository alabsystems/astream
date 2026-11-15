// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for DEC Mode `?2026` synchronized-output frame budgeting & fail-open
// timeouts (`Astream.Term.TlaSynchronizedFrameBudget`), mounted under `cfg(clean_islands)`
// in `vt_synchronized_frame_budget.rs`. Proves `bufferedBytes <= maxSyncBytes` and
// `elapsedMs <= maxHoldMs`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def sync_bytes_clamp_b82 (buffered : UInt64) (max_bytes : UInt64) : UInt64 :=
      if buffered < max_bytes then buffered else max_bytes

    def sync_elapsed_clamp (elapsed : UInt64) (max_ms : UInt64) : UInt64 :=
      if elapsed < max_ms then elapsed else max_ms

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaSynchronizedFrameBudget

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

    structure SyncBudgetState where
      bufferedBytes : UInt64
      maxSyncBytes  : UInt64
      elapsedMs     : UInt64
      maxHoldMs     : UInt64

    def SyncBudgetSafetyInv (s : SyncBudgetState) : Prop :=
      Nat.le (UInt64.toNat s.bufferedBytes) (UInt64.toNat s.maxSyncBytes) ∧
      Nat.le (UInt64.toNat s.elapsedMs) (UInt64.toNat s.maxHoldMs)

    def Init (maxBytes maxMs : UInt64) (s : SyncBudgetState) : Prop :=
      s.bufferedBytes = (0 : UInt64) ∧
      s.maxSyncBytes = maxBytes ∧
      s.elapsedMs = (0 : UInt64) ∧
      s.maxHoldMs = maxMs

    def StepChunkOrFlush (rawBytes rawElapsed : UInt64) (s sNext : SyncBudgetState) : Prop :=
      sNext.bufferedBytes = _root_.sync_bytes_clamp_b82 rawBytes s.maxSyncBytes ∧
      sNext.maxSyncBytes = s.maxSyncBytes ∧
      sNext.elapsedMs = _root_.sync_elapsed_clamp rawElapsed s.maxHoldMs ∧
      sNext.maxHoldMs = s.maxHoldMs

    def Next (s sNext : SyncBudgetState) : Prop :=
      ∃ rb : UInt64, ∃ re : UInt64, StepChunkOrFlush rb re s sNext

    def Spec (maxBytes maxMs : UInt64) : StateMachine SyncBudgetState :=
      StateMachine.mk (Init maxBytes maxMs) Next

    theorem bytes_clamp_le : forall (b : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sync_bytes_clamp_b82 b cap)) (UInt64.toNat cap) :=
      fun b cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt b cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => b))) (UInt64.toNat cap))
        (instDecidableUInt64Lt b cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem elapsed_clamp_le : forall (e : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sync_elapsed_clamp e cap)) (UInt64.toNat cap) :=
      fun e cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt e cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => e))) (UInt64.toNat cap))
        (instDecidableUInt64Lt e cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxBytes maxMs : UInt64) (s : SyncBudgetState)
        (hInit : Init maxBytes maxMs s) : SyncBudgetSafetyInv s :=
      And.intro
        (zero_u64_le s.bufferedBytes s.maxSyncBytes hInit.1)
        (zero_u64_le s.elapsedMs s.maxHoldMs hInit.2.2.1)

    theorem step_preserves_inv (rb re : UInt64) (s sNext : SyncBudgetState)
        (hAct : StepChunkOrFlush rb re s sNext) : SyncBudgetSafetyInv sNext :=
      let hB1 : Nat.le (UInt64.toNat sNext.bufferedBytes) (UInt64.toNat s.maxSyncBytes) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxSyncBytes)) hAct.1)
          (bytes_clamp_le rb s.maxSyncBytes)
      let hB2 : Nat.le (UInt64.toNat sNext.bufferedBytes) (UInt64.toNat sNext.maxSyncBytes) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.bufferedBytes) (UInt64.toNat y)) hAct.2.1)
          hB1
      let hE1 : Nat.le (UInt64.toNat sNext.elapsedMs) (UInt64.toNat s.maxHoldMs) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxHoldMs)) hAct.2.2.1)
          (elapsed_clamp_le re s.maxHoldMs)
      let hE2 : Nat.le (UInt64.toNat sNext.elapsedMs) (UInt64.toNat sNext.maxHoldMs) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.elapsedMs) (UInt64.toNat y)) hAct.2.2.2)
          hE1
      And.intro hB2 hE2

    theorem next_preserves_inv (s sNext : SyncBudgetState)
        (_hInv : SyncBudgetSafetyInv s) (hNext : Next s sNext) :
        SyncBudgetSafetyInv sNext :=
      Exists.elim hNext (fun rb hEx =>
        Exists.elim hEx (fun re hAct => step_preserves_inv rb re s sNext hAct))

    theorem spec_satisfies_sync_budget_safety (maxBytes maxMs : UInt64) :
        Satisfies (Spec maxBytes maxMs) (Always (Lift SyncBudgetSafetyInv)) :=
      invariantSatisfies (Spec maxBytes maxMs) SyncBudgetSafetyInv
        (init_establishes_inv maxBytes maxMs)
        next_preserves_inv

    end TlaSynchronizedFrameBudget
    end Term
    end Astream

    -- ========================================================================
    -- 3. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def sync_frame_within_budget_isl (buffered_bytes : UInt64) (max_sync_bytes : UInt64) : Bool :=
      decide (buffered_bytes ≤ max_sync_bytes)
}
