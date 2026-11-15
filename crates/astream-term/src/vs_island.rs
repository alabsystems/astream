// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for UCD 16.0 VS16/VS15 variation-selector cell presentation width
// (`Astream.Term.TlaVariationWidth`), mounted under `cfg(clean_islands)` in `screen.rs`.
// Proves that `vs_width_clamp` and `vs_cursor_advance_clamp` maintain bounded cell width
// (`cellWidth <= maxWidth`), bounded cursor column (`cursorCol <= lineEnd`), and spacer
// consistency (`hasSpacer = true -> cellWidth = maxWidth`) across base printing, VS16
// emoji widening, and VS15 text narrowing transitions.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def vs_width_clamp (proposed_width : UInt64) (max_width : UInt64) : UInt64 :=
      if proposed_width < max_width then proposed_width else max_width

    def vs_cursor_advance_clamp (next_col : UInt64) (line_end : UInt64) : UInt64 :=
      if next_col < line_end then next_col else line_end

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaVariationWidth)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaVariationWidth

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaVariationWidth.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaVariationWidth.Always

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
    -- 3. UCD 16.0 VS16/VS15 Variation Presentation State Machine & Safety Theorem
    -- ========================================================================

    structure VariationWidthState where
      cellWidth : UInt64
      maxWidth  : UInt64
      cursorCol : UInt64
      lineEnd   : UInt64
      hasSpacer : Bool

    def VariationSafetyInv (s : VariationWidthState) : Prop :=
      Nat.le (UInt64.toNat s.cellWidth) (UInt64.toNat s.maxWidth) ∧
      Nat.le (UInt64.toNat s.cursorCol) (UInt64.toNat s.lineEnd) ∧
      (s.hasSpacer = true → s.cellWidth = s.maxWidth)

    def Init (maxWidth lineEnd : UInt64) (s : VariationWidthState) : Prop :=
      s.cellWidth = (0 : UInt64) ∧
      s.maxWidth = maxWidth ∧
      s.cursorCol = (0 : UInt64) ∧
      s.lineEnd = lineEnd ∧
      s.hasSpacer = false

    def PrintBaseNarrow (candWidth nextCol : UInt64) (s sNext : VariationWidthState) : Prop :=
      sNext.cellWidth = _root_.vs_width_clamp candWidth s.maxWidth ∧
      sNext.maxWidth = s.maxWidth ∧
      sNext.cursorCol = _root_.vs_cursor_advance_clamp nextCol s.lineEnd ∧
      sNext.lineEnd = s.lineEnd ∧
      sNext.hasSpacer = false

    def WidenVs16 (nextCol : UInt64) (s sNext : VariationWidthState) : Prop :=
      sNext.cellWidth = s.maxWidth ∧
      sNext.maxWidth = s.maxWidth ∧
      sNext.cursorCol = _root_.vs_cursor_advance_clamp nextCol s.lineEnd ∧
      sNext.lineEnd = s.lineEnd ∧
      sNext.hasSpacer = true

    def NarrowVs15 (narrowWidth : UInt64) (s sNext : VariationWidthState) : Prop :=
      sNext.cellWidth = _root_.vs_width_clamp narrowWidth s.maxWidth ∧
      sNext.maxWidth = s.maxWidth ∧
      sNext.cursorCol = s.cursorCol ∧
      sNext.lineEnd = s.lineEnd ∧
      sNext.hasSpacer = false

    def Next (s sNext : VariationWidthState) : Prop :=
      (∃ cw : UInt64, ∃ nc : UInt64, PrintBaseNarrow cw nc s sNext) ∨
      ((∃ nc : UInt64, WidenVs16 nc s sNext) ∨
       (∃ nw : UInt64, NarrowVs15 nw s sNext))

    def Spec (maxWidth lineEnd : UInt64) : StateMachine VariationWidthState :=
      StateMachine.mk (Init maxWidth lineEnd) Next

    theorem false_ne_true (h : false = true) : False :=
      Bool.noConfusion h

    theorem width_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.vs_width_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem cursor_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.vs_cursor_advance_clamp cand cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (maxWidth lineEnd : UInt64) (s : VariationWidthState)
        (hInit : Init maxWidth lineEnd s) : VariationSafetyInv s :=
      And.intro
        (zero_u64_le s.cellWidth s.maxWidth hInit.1)
        (And.intro
          (zero_u64_le s.cursorCol s.lineEnd hInit.2.2.1)
          (fun hTrue =>
            False.elim (false_ne_true (Eq.trans (Eq.symm hInit.2.2.2.2) hTrue))))

    theorem printBaseNarrow_preserves_inv (cw nc : UInt64) (s sNext : VariationWidthState)
        (hAct : PrintBaseNarrow cw nc s sNext) : VariationSafetyInv sNext :=
      let hW1 : Nat.le (UInt64.toNat sNext.cellWidth) (UInt64.toNat s.maxWidth) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxWidth)) hAct.1)
          (width_clamp_le cw s.maxWidth)
      let hW2 : Nat.le (UInt64.toNat sNext.cellWidth) (UInt64.toNat sNext.maxWidth) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.cellWidth) (UInt64.toNat y)) hAct.2.1)
          hW1
      let hC1 : Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat s.lineEnd) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.lineEnd)) hAct.2.2.1)
          (cursor_clamp_le nc s.lineEnd)
      let hC2 : Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat sNext.lineEnd) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat y)) hAct.2.2.2.1)
          hC1
      And.intro hW2
        (And.intro hC2
          (fun hTrue =>
            False.elim (false_ne_true (Eq.trans (Eq.symm hAct.2.2.2.2) hTrue))))

    theorem widenVs16_preserves_inv (nc : UInt64) (s sNext : VariationWidthState)
        (hAct : WidenVs16 nc s sNext) : VariationSafetyInv sNext :=
      let hEqMax : sNext.cellWidth = sNext.maxWidth :=
        Eq.trans hAct.1 (Eq.symm hAct.2.1)
      let hW : Nat.le (UInt64.toNat sNext.cellWidth) (UInt64.toNat sNext.maxWidth) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.maxWidth)) hEqMax)
          (Nat.le.refl (UInt64.toNat sNext.maxWidth))
      let hC1 : Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat s.lineEnd) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.lineEnd)) hAct.2.2.1)
          (cursor_clamp_le nc s.lineEnd)
      let hC2 : Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat sNext.lineEnd) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat y)) hAct.2.2.2.1)
          hC1
      And.intro hW (And.intro hC2 (fun _ => hEqMax))

    theorem narrowVs15_preserves_inv (nw : UInt64) (s sNext : VariationWidthState)
        (hInv : VariationSafetyInv s) (hAct : NarrowVs15 nw s sNext) :
        VariationSafetyInv sNext :=
      let hW1 : Nat.le (UInt64.toNat sNext.cellWidth) (UInt64.toNat s.maxWidth) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxWidth)) hAct.1)
          (width_clamp_le nw s.maxWidth)
      let hW2 : Nat.le (UInt64.toNat sNext.cellWidth) (UInt64.toNat sNext.maxWidth) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.cellWidth) (UInt64.toNat y)) hAct.2.1)
          hW1
      let hC1 : Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat s.lineEnd) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.lineEnd)) hAct.2.2.1)
          hInv.2.1
      let hC2 : Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat sNext.lineEnd) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.cursorCol) (UInt64.toNat y)) hAct.2.2.2.1)
          hC1
      And.intro hW2
        (And.intro hC2
          (fun hTrue =>
            False.elim (false_ne_true (Eq.trans (Eq.symm hAct.2.2.2.2) hTrue))))

    theorem next_preserves_inv (s sNext : VariationWidthState)
        (hInv : VariationSafetyInv s) (hNext : Next s sNext) :
        VariationSafetyInv sNext :=
      Or.elim hNext
        (fun hEx1 =>
          Exists.elim hEx1 (fun cw hEx2 =>
            Exists.elim hEx2 (fun nc hP => printBaseNarrow_preserves_inv cw nc s sNext hP)))
        (fun hRest =>
          Or.elim hRest
            (fun hExW =>
              Exists.elim hExW (fun nc hW => widenVs16_preserves_inv nc s sNext hW))
            (fun hExN =>
              Exists.elim hExN (fun nw hN => narrowVs15_preserves_inv nw s sNext hInv hN)))

    theorem spec_satisfies_variation_width_safety (maxWidth lineEnd : UInt64) :
        (Spec maxWidth lineEnd) ⊨ □ (Lift VariationSafetyInv) :=
      invariantSatisfies (Spec maxWidth lineEnd) VariationSafetyInv
        (init_establishes_inv maxWidth lineEnd)
        next_preserves_inv

    end TlaVariationWidth
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def vs_width_valid_isl (width : UInt64) (max_width : UInt64) : Bool :=
      decide (width ≤ max_width)
}
