// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for macOS `syspolicyd=stuck` deadlock detection and spawn retry
// circuit-breaking (`Astream.Host.TlaSyspolicydDetector`), mounted under
// `cfg(clean_islands)` in `syspolicyd_deadlock.rs`. Proves
// `stalledNonApple <= stallThresholdCap` and `retryAttempts <= maxRetries`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def syspolicy_stall_clamp (stalled_count : UInt64) (threshold_cap : UInt64) : UInt64 :=
      if stalled_count < threshold_cap then stalled_count else threshold_cap

    def syspolicy_retry_clamp (retry_attempts : UInt64) (max_retries : UInt64) : UInt64 :=
      if retry_attempts < max_retries then retry_attempts else max_retries

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Host.TlaSyspolicydDetector)
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaSyspolicydDetector

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Host.TlaSyspolicydDetector.Satisfies M F
    prefix:75 "□" => _root_.Astream.Host.TlaSyspolicydDetector.Always

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
    -- 3. macOS `syspolicyd=stuck` Detector & Circuit-Breaker State Machine
    -- ========================================================================

    structure SyspolicyState where
      stalledNonApple   : UInt64
      stallThresholdCap : UInt64
      retryAttempts     : UInt64
      maxRetries        : UInt64

    def SyspolicyInv (s : SyspolicyState) : Prop :=
      Nat.le (UInt64.toNat s.stalledNonApple) (UInt64.toNat s.stallThresholdCap) ∧
      Nat.le (UInt64.toNat s.retryAttempts) (UInt64.toNat s.maxRetries)

    def Init (stallThresholdCap maxRetries : UInt64) (s : SyspolicyState) : Prop :=
      s.stalledNonApple = (0 : UInt64) ∧
      s.stallThresholdCap = stallThresholdCap ∧
      s.retryAttempts = (0 : UInt64) ∧
      s.maxRetries = maxRetries

    def RecordSpawnOutcome (rawStalls rawRetries : UInt64) (s sNext : SyspolicyState) : Prop :=
      sNext.stalledNonApple = _root_.syspolicy_stall_clamp rawStalls s.stallThresholdCap ∧
      sNext.stallThresholdCap = s.stallThresholdCap ∧
      sNext.retryAttempts = _root_.syspolicy_retry_clamp rawRetries s.maxRetries ∧
      sNext.maxRetries = s.maxRetries

    def Next (s sNext : SyspolicyState) : Prop :=
      ∃ rs : UInt64, ∃ rr : UInt64, RecordSpawnOutcome rs rr s sNext

    def Spec (stallThresholdCap maxRetries : UInt64) : StateMachine SyspolicyState :=
      StateMachine.mk (Init stallThresholdCap maxRetries) Next

    theorem stall_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.syspolicy_stall_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem retry_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.syspolicy_retry_clamp cand cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (stallThresholdCap maxRetries : UInt64) (s : SyspolicyState)
        (hInit : Init stallThresholdCap maxRetries s) : SyspolicyInv s :=
      And.intro
        (zero_u64_le s.stalledNonApple s.stallThresholdCap hInit.1)
        (zero_u64_le s.retryAttempts s.maxRetries hInit.2.2.1)

    theorem recordSpawnOutcome_preserves_inv (rs rr : UInt64) (s sNext : SyspolicyState)
        (hAct : RecordSpawnOutcome rs rr s sNext) : SyspolicyInv sNext :=
      let hS1 : Nat.le (UInt64.toNat sNext.stalledNonApple) (UInt64.toNat s.stallThresholdCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.stallThresholdCap)) hAct.1)
          (stall_clamp_le rs s.stallThresholdCap)
      let hS2 : Nat.le (UInt64.toNat sNext.stalledNonApple) (UInt64.toNat sNext.stallThresholdCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.stalledNonApple) (UInt64.toNat y)) hAct.2.1)
          hS1
      let hR1 : Nat.le (UInt64.toNat sNext.retryAttempts) (UInt64.toNat s.maxRetries) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRetries)) hAct.2.2.1)
          (retry_clamp_le rr s.maxRetries)
      let hR2 : Nat.le (UInt64.toNat sNext.retryAttempts) (UInt64.toNat sNext.maxRetries) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.retryAttempts) (UInt64.toNat y)) hAct.2.2.2)
          hR1
      And.intro hS2 hR2

    theorem next_preserves_inv (s sNext : SyspolicyState)
        (_hInv : SyspolicyInv s) (hNext : Next s sNext) : SyspolicyInv sNext :=
      Exists.elim hNext (fun rs hEx2 =>
        Exists.elim hEx2 (fun rr hAct => recordSpawnOutcome_preserves_inv rs rr s sNext hAct))

    theorem spec_satisfies_syspolicyd_detector_safety (stallThresholdCap maxRetries : UInt64) :
        (Spec stallThresholdCap maxRetries) ⊨ □ (Lift SyspolicyInv) :=
      invariantSatisfies (Spec stallThresholdCap maxRetries) SyspolicyInv
        (init_establishes_inv stallThresholdCap maxRetries)
        next_preserves_inv

    end TlaSyspolicydDetector
    end Host
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def syspolicy_is_deadlocked_isl (stalled_count : UInt64) (threshold : UInt64) : Bool :=
      decide (threshold ≤ stalled_count)
}
