// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for PTY window-size (`TIOCSWINSZ`) drag-resize debouncing
// (`Astream.Host.TlaWinsizeDebounce`), mounted under `cfg(clean_islands)` in
// `pty_winsize_debounce.rs`. Proves monotone delivery epoch progression
// (`prevEpoch <= curEpoch`) and bounded grid dimensions (`cols <= maxDim ∧ rows <= maxDim`)
// across rapid GUI window-resize coalescing and timer-driven flushes.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def winsize_debounce_dim_clamp (raw_dim : UInt64) (max_dim : UInt64) : UInt64 :=
      if raw_dim < max_dim then raw_dim else max_dim

    def winsize_debounce_epoch_advance (cur_epoch : UInt64) (next_epoch : UInt64) : UInt64 :=
      if cur_epoch < next_epoch then next_epoch else cur_epoch

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Host.TlaWinsizeDebounce)
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaWinsizeDebounce

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Host.TlaWinsizeDebounce.Satisfies M F
    prefix:75 "□" => _root_.Astream.Host.TlaWinsizeDebounce.Always

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
    -- 3. PTY Winsize Debounce State Machine & Safety Theorem
    -- ========================================================================

    structure WinsizeState where
      prevEpoch : UInt64
      curEpoch  : UInt64
      cols      : UInt64
      rows      : UInt64
      maxDim    : UInt64

    def WinsizeSafetyInv (s : WinsizeState) : Prop :=
      Nat.le (UInt64.toNat s.prevEpoch) (UInt64.toNat s.curEpoch) ∧
      Nat.le (UInt64.toNat s.cols) (UInt64.toNat s.maxDim) ∧
      Nat.le (UInt64.toNat s.rows) (UInt64.toNat s.maxDim)

    def Init (maxDim : UInt64) (s : WinsizeState) : Prop :=
      s.prevEpoch = (0 : UInt64) ∧
      s.curEpoch = (0 : UInt64) ∧
      s.cols = (0 : UInt64) ∧
      s.rows = (0 : UInt64) ∧
      s.maxDim = maxDim

    def StageOrFlushWinsize (rawCols rawRows nextEpoch : UInt64) (s sNext : WinsizeState) : Prop :=
      sNext.prevEpoch = s.curEpoch ∧
      sNext.curEpoch = _root_.winsize_debounce_epoch_advance s.curEpoch nextEpoch ∧
      sNext.cols = _root_.winsize_debounce_dim_clamp rawCols s.maxDim ∧
      sNext.rows = _root_.winsize_debounce_dim_clamp rawRows s.maxDim ∧
      sNext.maxDim = s.maxDim

    def Next (s sNext : WinsizeState) : Prop :=
      ∃ rc : UInt64, ∃ rr : UInt64, ∃ ne : UInt64, StageOrFlushWinsize rc rr ne s sNext

    def Spec (maxDim : UInt64) : StateMachine WinsizeState :=
      StateMachine.mk (Init maxDim) Next

    theorem dim_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.winsize_debounce_dim_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_adv_ge : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.winsize_debounce_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_u64_le (x y : UInt64) (hEq : x = y) :
        Nat.le (UInt64.toNat x) (UInt64.toNat y) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat y)) hEq)
        (Nat.le.refl (UInt64.toNat y))

    theorem init_establishes_inv (maxDim : UInt64) (s : WinsizeState)
        (hInit : Init maxDim s) : WinsizeSafetyInv s :=
      And.intro
        (eq_u64_le s.prevEpoch s.curEpoch (Eq.trans hInit.1 (Eq.symm hInit.2.1)))
        (And.intro
          (zero_u64_le s.cols s.maxDim hInit.2.2.1)
          (zero_u64_le s.rows s.maxDim hInit.2.2.2.1))

    theorem step_preserves_inv (rc rr ne : UInt64) (s sNext : WinsizeState)
        (hAct : StageOrFlushWinsize rc rr ne s sNext) : WinsizeSafetyInv sNext :=
      let hE1 : Nat.le (UInt64.toNat s.curEpoch) (UInt64.toNat sNext.curEpoch) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat s.curEpoch) (UInt64.toNat y)) hAct.2.1)
          (epoch_adv_ge s.curEpoch ne)
      let hE2 : Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat sNext.curEpoch) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.curEpoch)) hAct.1)
          hE1
      let hC1 : Nat.le (UInt64.toNat sNext.cols) (UInt64.toNat s.maxDim) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxDim)) hAct.2.2.1)
          (dim_clamp_le rc s.maxDim)
      let hC2 : Nat.le (UInt64.toNat sNext.cols) (UInt64.toNat sNext.maxDim) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.cols) (UInt64.toNat y)) hAct.2.2.2.2)
          hC1
      let hR1 : Nat.le (UInt64.toNat sNext.rows) (UInt64.toNat s.maxDim) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxDim)) hAct.2.2.2.1)
          (dim_clamp_le rr s.maxDim)
      let hR2 : Nat.le (UInt64.toNat sNext.rows) (UInt64.toNat sNext.maxDim) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.rows) (UInt64.toNat y)) hAct.2.2.2.2)
          hR1
      And.intro hE2 (And.intro hC2 hR2)

    theorem next_preserves_inv (s sNext : WinsizeState)
        (_hInv : WinsizeSafetyInv s) (hNext : Next s sNext) :
        WinsizeSafetyInv sNext :=
      Exists.elim hNext (fun rc hEx2 =>
        Exists.elim hEx2 (fun rr hEx3 =>
          Exists.elim hEx3 (fun ne hS => step_preserves_inv rc rr ne s sNext hS)))

    theorem spec_satisfies_winsize_debounce_safety (maxDim : UInt64) :
        (Spec maxDim) ⊨ □ (Lift WinsizeSafetyInv) :=
      invariantSatisfies (Spec maxDim) WinsizeSafetyInv
        (init_establishes_inv maxDim)
        next_preserves_inv

    end TlaWinsizeDebounce
    end Host
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def winsize_debounce_ready_isl (elapsed_ms : UInt64) (window_ms : UInt64) : Bool :=
      decide (window_ms ≤ elapsed_ms)
}
