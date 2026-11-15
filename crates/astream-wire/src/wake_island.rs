// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for per-recipient fabric wake coalescing & window-budget enforcement
// (`Astream.Wire.TlaWakeBudget`), mounted under `cfg(clean_islands)` in `wake.rs`
// (`DESIGN-aterm-fabric.md` §5.6, T9).
// Proves that `wake_rank_max` and `wake_charge_clamp` maintain:
// 1. `usedWakes <= maxBudget` (wakes never exceed the configured window budget),
// 2. `emittedInBatch <= 1` (at most one wake event per pending batch), and
// 3. `batchRank <= maxRank` (coalesced priority stays bounded by `control`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def wake_rank_max (cur_rank : UInt64) (cand_rank : UInt64) : UInt64 :=
      if cur_rank < cand_rank then cand_rank else cur_rank

    def wake_charge_clamp (used : UInt64) (budget : UInt64) : UInt64 :=
      if used < budget then used else budget

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaWakeBudget)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaWakeBudget

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Wire.TlaWakeBudget.Satisfies M F
    prefix:75 "□" => _root_.Astream.Wire.TlaWakeBudget.Always

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
    -- 3. Per-Recipient Wake Coalescing & Window Budget State Machine
    -- ========================================================================

    theorem wake_charge_clamp_le_budget (used budget : UInt64) :
        Nat.le (UInt64.toNat (_root_.wake_charge_clamp used budget)) (UInt64.toNat budget) :=
      @Decidable.casesOn (LT.lt used budget)
        (fun (d : Decidable (LT.lt used budget)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt used budget) d used budget)) (UInt64.toNat budget))
        (instDecidableUInt64Lt used budget)
        (fun _ => Nat.le_refl (UInt64.toNat budget))
        (fun hLt => Nat.le_of_lt hLt)

    theorem wake_rank_max_lub (cur cand cap : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat cap))
        (hCand : Nat.le (UInt64.toNat cand) (UInt64.toNat cap)) :
        Nat.le (UInt64.toNat (_root_.wake_rank_max cur cand)) (UInt64.toNat cap) :=
      @Decidable.casesOn (LT.lt cur cand)
        (fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur cand) d cand cur)) (UInt64.toNat cap))
        (instDecidableUInt64Lt cur cand)
        (fun _ => hCur)
        (fun _ => hCand)

    structure WakeState where
      usedWakes      : UInt64
      maxBudget      : UInt64
      batchRank      : UInt64
      maxRank        : UInt64
      emittedInBatch : Nat

    def WakeBudgetSafetyInv (s : WakeState) : Prop :=
      Nat.le (UInt64.toNat s.usedWakes) (UInt64.toNat s.maxBudget) ∧
      Nat.le (UInt64.toNat s.batchRank) (UInt64.toNat s.maxRank) ∧
      Nat.le s.emittedInBatch 1

    def Init (budget maxRank : UInt64) (s : WakeState) : Prop :=
      s.usedWakes = (0 : UInt64) ∧
      s.maxBudget = budget ∧
      s.batchRank = (0 : UInt64) ∧
      s.maxRank = maxRank ∧
      s.emittedInBatch = 0

    def ObserveDelivery (candRank : UInt64) (s sNext : WakeState) : Prop :=
      Nat.le (UInt64.toNat candRank) (UInt64.toNat s.maxRank) ∧
      sNext.usedWakes = s.usedWakes ∧
      sNext.maxBudget = s.maxBudget ∧
      sNext.batchRank = _root_.wake_rank_max s.batchRank candRank ∧
      sNext.maxRank = s.maxRank ∧
      sNext.emittedInBatch = s.emittedInBatch

    def EmitWake (nextUsed : UInt64) (s sNext : WakeState) : Prop :=
      s.emittedInBatch = 0 ∧
      sNext.usedWakes = _root_.wake_charge_clamp nextUsed s.maxBudget ∧
      sNext.maxBudget = s.maxBudget ∧
      sNext.batchRank = s.batchRank ∧
      sNext.maxRank = s.maxRank ∧
      sNext.emittedInBatch = 1

    def ResetBatch (retainedUsed : UInt64) (s sNext : WakeState) : Prop :=
      sNext.usedWakes = _root_.wake_charge_clamp retainedUsed s.maxBudget ∧
      sNext.maxBudget = s.maxBudget ∧
      sNext.batchRank = (0 : UInt64) ∧
      sNext.maxRank = s.maxRank ∧
      sNext.emittedInBatch = 0

    def Next (s sNext : WakeState) : Prop :=
      (∃ cr : UInt64, ObserveDelivery cr s sNext) ∨
      ((∃ nu : UInt64, EmitWake nu s sNext) ∨
       (∃ ru : UInt64, ResetBatch ru s sNext))

    def Spec (budget maxRank : UInt64) : StateMachine WakeState :=
      StateMachine.mk (Init budget maxRank) Next

    theorem init_establishes_inv (budget maxRank : UInt64) (s : WakeState)
        (hInit : Init budget maxRank s) : WakeBudgetSafetyInv s :=
      let hUsed0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.maxBudget) :=
        Nat.zero_le (UInt64.toNat s.maxBudget)
      let hUsed : Nat.le (UInt64.toNat s.usedWakes) (UInt64.toNat s.maxBudget) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxBudget)) hInit.1) hUsed0
      let hRank0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.maxRank) :=
        Nat.zero_le (UInt64.toNat s.maxRank)
      let hRank : Nat.le (UInt64.toNat s.batchRank) (UInt64.toNat s.maxRank) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRank)) hInit.2.2.1) hRank0
      let hEmit : Nat.le s.emittedInBatch 1 :=
        Eq.mpr (congrArg (fun x => Nat.le x 1) hInit.2.2.2.2) (Nat.zero_le 1)
      And.intro hUsed (And.intro hRank hEmit)

    theorem observeDelivery_preserves_inv (cr : UInt64) (s sNext : WakeState)
        (hInv : WakeBudgetSafetyInv s) (hAct : ObserveDelivery cr s sNext) :
        WakeBudgetSafetyInv sNext :=
      let hUsed1 : Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat s.maxBudget) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxBudget)) hAct.2.1) hInv.1
      let hUsed : Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat sNext.maxBudget) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat y)) hAct.2.2.1) hUsed1
      let hLub : Nat.le (UInt64.toNat (_root_.wake_rank_max s.batchRank cr)) (UInt64.toNat s.maxRank) :=
        wake_rank_max_lub s.batchRank cr s.maxRank hInv.2.1 hAct.1
      let hRank1 : Nat.le (UInt64.toNat sNext.batchRank) (UInt64.toNat s.maxRank) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRank)) hAct.2.2.2.1) hLub
      let hRank : Nat.le (UInt64.toNat sNext.batchRank) (UInt64.toNat sNext.maxRank) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.batchRank) (UInt64.toNat y)) hAct.2.2.2.2.1) hRank1
      let hEmit : Nat.le sNext.emittedInBatch 1 :=
        Eq.mpr (congrArg (fun x => Nat.le x 1) hAct.2.2.2.2.2) hInv.2.2
      And.intro hUsed (And.intro hRank hEmit)

    theorem emitWake_preserves_inv (nu : UInt64) (s sNext : WakeState)
        (hInv : WakeBudgetSafetyInv s) (hAct : EmitWake nu s sNext) :
        WakeBudgetSafetyInv sNext :=
      let hClamp : Nat.le (UInt64.toNat (_root_.wake_charge_clamp nu s.maxBudget)) (UInt64.toNat s.maxBudget) :=
        wake_charge_clamp_le_budget nu s.maxBudget
      let hUsed1 : Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat s.maxBudget) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxBudget)) hAct.2.1) hClamp
      let hUsed : Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat sNext.maxBudget) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat y)) hAct.2.2.1) hUsed1
      let hRank1 : Nat.le (UInt64.toNat sNext.batchRank) (UInt64.toNat s.maxRank) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRank)) hAct.2.2.2.1) hInv.2.1
      let hRank : Nat.le (UInt64.toNat sNext.batchRank) (UInt64.toNat sNext.maxRank) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.batchRank) (UInt64.toNat y)) hAct.2.2.2.2.1) hRank1
      let hEmit : Nat.le sNext.emittedInBatch 1 :=
        Eq.mpr (congrArg (fun x => Nat.le x 1) hAct.2.2.2.2.2) (Nat.le_refl 1)
      And.intro hUsed (And.intro hRank hEmit)

    theorem resetBatch_preserves_inv (ru : UInt64) (s sNext : WakeState)
        (hAct : ResetBatch ru s sNext) : WakeBudgetSafetyInv sNext :=
      let hClamp : Nat.le (UInt64.toNat (_root_.wake_charge_clamp ru s.maxBudget)) (UInt64.toNat s.maxBudget) :=
        wake_charge_clamp_le_budget ru s.maxBudget
      let hUsed1 : Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat s.maxBudget) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxBudget)) hAct.1) hClamp
      let hUsed : Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat sNext.maxBudget) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.usedWakes) (UInt64.toNat y)) hAct.2.1) hUsed1
      let hRank0 : Nat.le (UInt64.toNat 0) (UInt64.toNat sNext.maxRank) :=
        Nat.zero_le (UInt64.toNat sNext.maxRank)
      let hRank : Nat.le (UInt64.toNat sNext.batchRank) (UInt64.toNat sNext.maxRank) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.maxRank)) hAct.2.2.1) hRank0
      let hEmit : Nat.le sNext.emittedInBatch 1 :=
        Eq.mpr (congrArg (fun x => Nat.le x 1) hAct.2.2.2.2) (Nat.zero_le 1)
      And.intro hUsed (And.intro hRank hEmit)

    theorem next_preserves_inv (s sNext : WakeState)
        (hInv : WakeBudgetSafetyInv s) (hNext : Next s sNext) :
        WakeBudgetSafetyInv sNext :=
      Or.elim hNext
        (fun hObs =>
          Exists.elim hObs (fun cr hO => observeDelivery_preserves_inv cr s sNext hInv hO))
        (fun hRest =>
          Or.elim hRest
            (fun hEm =>
              Exists.elim hEm (fun nu hE => emitWake_preserves_inv nu s sNext hInv hE))
            (fun hRs =>
              Exists.elim hRs (fun ru hR => resetBatch_preserves_inv ru s sNext hR)))

    theorem spec_satisfies_wake_budget_safety (budget maxRank : UInt64) :
        (Spec budget maxRank) ⊨ □ (Lift WakeBudgetSafetyInv) :=
      invariantSatisfies (Spec budget maxRank) WakeBudgetSafetyInv
        (init_establishes_inv budget maxRank)
        next_preserves_inv

    end TlaWakeBudget
    end Wire
    end Astream

    def wake_within_budget_isl (used : UInt64) (budget : UInt64) : Bool :=
      decide (used < budget)
}
