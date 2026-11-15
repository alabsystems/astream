// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for DECLRMM (`?69`) + DECAWM pending-wrap canonicalization
// (`Astream.Term.TlaMarginWrapArbiter`), mounted under `cfg(clean_islands)` in
// `margin_wrap_arbiter.rs`. Proves `cursorCol <= screenCols` and `marginWrapFlag <= 1`
// so `Screen::serialize()` injectivity holds across edge wraps and DECSLRM right-margin wraps.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def wrap_col_clamp (col : UInt64) (screen_cols : UInt64) : UInt64 :=
      if col < screen_cols then col else screen_cols

    def wrap_margin_flag (col : UInt64) (last_col : UInt64) : UInt64 :=
      if col < last_col then (1 : UInt64) else (0 : UInt64)

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaMarginWrapArbiter

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaMarginWrapArbiter.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaMarginWrapArbiter.Always

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
    -- 3. Canonical Edge-Wrap vs Margin-Wrap State Machine
    -- ========================================================================

    structure WrapState where
      cursorCol      : UInt64
      marginWrapFlag : UInt64
      screenCols     : UInt64

    def CanonicalWrapInv (s : WrapState) : Prop :=
      Nat.le (UInt64.toNat s.cursorCol) (UInt64.toNat s.screenCols) ∧
      Nat.le (UInt64.toNat s.marginWrapFlag) (UInt64.toNat (1 : UInt64))

    def Init (screenCols : UInt64) (s : WrapState) : Prop :=
      s.cursorCol = (0 : UInt64) ∧
      s.marginWrapFlag = (0 : UInt64) ∧
      s.screenCols = screenCols

    def SetCanonicalWrap (rawCol lastCol : UInt64) (s sNext : WrapState) : Prop :=
      sNext.cursorCol = _root_.wrap_col_clamp rawCol s.screenCols ∧
      sNext.marginWrapFlag = _root_.wrap_margin_flag rawCol lastCol ∧
      sNext.screenCols = s.screenCols

    def Next (s sNext : WrapState) : Prop :=
      ∃ rc : UInt64, ∃ lc : UInt64, SetCanonicalWrap rc lc s sNext

    def Spec (screenCols : UInt64) : StateMachine WrapState :=
      StateMachine.mk (Init screenCols) Next

    theorem col_clamp_le : forall (c : UInt64) (cols : UInt64),
        Nat.le (UInt64.toNat (_root_.wrap_col_clamp c cols)) (UInt64.toNat cols) :=
      fun c cols => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt c cols)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cols) (fun _ => c))) (UInt64.toNat cols))
        (instDecidableUInt64Lt c cols)
        (fun _ => Nat.le.refl (UInt64.toNat cols))
        (fun hLt => Nat.le_of_lt hLt)

    theorem margin_flag_le_one : forall (c : UInt64) (lc : UInt64),
        Nat.le (UInt64.toNat (_root_.wrap_margin_flag c lc)) (UInt64.toNat (1 : UInt64)) :=
      fun c lc => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt c lc)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => (0 : UInt64)) (fun _ => (1 : UInt64))))
            (UInt64.toNat (1 : UInt64)))
        (instDecidableUInt64Lt c lc)
        (fun _ => Nat.zero_le (UInt64.toNat (1 : UInt64)))
        (fun _ => Nat.le.refl (UInt64.toNat (1 : UInt64)))

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (screenCols : UInt64) (s : WrapState)
        (hInit : Init screenCols s) : CanonicalWrapInv s :=
      And.intro
        (zero_u64_le s.cursorCol s.screenCols hInit.1)
        (zero_u64_le s.marginWrapFlag (1 : UInt64) hInit.2.1)

    theorem setWrap_preserves_inv (rc lc : UInt64) (s sNext : WrapState)
        (hAct : SetCanonicalWrap rc lc s sNext) : CanonicalWrapInv sNext :=
      let hC1 : Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat s.screenCols) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.screenCols)) hAct.1)
          (col_clamp_le rc s.screenCols)
      let hC2 : Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat sNext.screenCols) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat y)) hAct.2.2)
          hC1
      let hM : Nat.le (UInt64.toNat sNext.marginWrapFlag) (UInt64.toNat (1 : UInt64)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (1 : UInt64))) hAct.2.1)
          (margin_flag_le_one rc lc)
      And.intro hC2 hM

    theorem next_preserves_inv (s sNext : WrapState)
        (_hInv : CanonicalWrapInv s) (hNext : Next s sNext) :
        CanonicalWrapInv sNext :=
      Exists.elim hNext (fun rc hEx =>
        Exists.elim hEx (fun lc hAct => setWrap_preserves_inv rc lc s sNext hAct))

    theorem spec_satisfies_canonical_wrap (screenCols : UInt64) :
        (Spec screenCols) ⊨ □ (Lift CanonicalWrapInv) :=
      invariantSatisfies (Spec screenCols) CanonicalWrapInv
        (init_establishes_inv screenCols)
        next_preserves_inv

    end TlaMarginWrapArbiter
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def wrap_at_edge_isl (cursor_col : UInt64) (screen_cols : UInt64) : Bool :=
      decide (screen_cols ≤ cursor_col)
}
