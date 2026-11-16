// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for SGR sub-parameter underline styles and underline RGB colors
// (`Astream.Term.TlaUnderlineStyle`), mounted under `cfg(clean_islands)` in
// `sgr_underline_style.rs`. Proves bounded underline style code (`styleCode <= maxStyle`)
// and bounded 8-bit underline RGB channel values (`colorChan <= maxChan`) across
// `CSI 4:<style> m`, `CSI 58:2::<r>:<g>:<b> m`, and `CSI 24 / 59 m` reset transitions.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def underline_style_clamp (raw_style : UInt64) (max_style : UInt64) : UInt64 :=
      if raw_style < max_style then raw_style else max_style

    def underline_rgb_clamp (raw_chan : UInt64) (max_chan : UInt64) : UInt64 :=
      if raw_chan < max_chan then raw_chan else max_chan

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaUnderlineStyle)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaUnderlineStyle

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaUnderlineStyle.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaUnderlineStyle.Always

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
    -- 3. Underline Style & RGB Pen State Machine & Safety Theorem
    -- ========================================================================

    structure UnderlinePenState where
      styleCode : UInt64
      maxStyle  : UInt64
      colorChan : UInt64
      maxChan   : UInt64

    def UnderlineSafetyInv (s : UnderlinePenState) : Prop :=
      Nat.le (UInt64.toNat s.styleCode) (UInt64.toNat s.maxStyle) ∧
      Nat.le (UInt64.toNat s.colorChan) (UInt64.toNat s.maxChan)

    def Init (maxStyle maxChan : UInt64) (s : UnderlinePenState) : Prop :=
      s.styleCode = (0 : UInt64) ∧
      s.maxStyle = maxStyle ∧
      s.colorChan = (0 : UInt64) ∧
      s.maxChan = maxChan

    def SetUnderlinePen (candStyle candChan : UInt64) (s sNext : UnderlinePenState) : Prop :=
      sNext.styleCode = _root_.underline_style_clamp candStyle s.maxStyle ∧
      sNext.maxStyle = s.maxStyle ∧
      sNext.colorChan = _root_.underline_rgb_clamp candChan s.maxChan ∧
      sNext.maxChan = s.maxChan

    def ResetUnderlinePen (s sNext : UnderlinePenState) : Prop :=
      sNext.styleCode = (0 : UInt64) ∧
      sNext.maxStyle = s.maxStyle ∧
      sNext.colorChan = (0 : UInt64) ∧
      sNext.maxChan = s.maxChan

    def Next (s sNext : UnderlinePenState) : Prop :=
      (∃ cs : UInt64, ∃ cc : UInt64, SetUnderlinePen cs cc s sNext) ∨
      ResetUnderlinePen s sNext

    def Spec (maxStyle maxChan : UInt64) : StateMachine UnderlinePenState :=
      StateMachine.mk (Init maxStyle maxChan) Next

    theorem style_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.underline_style_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem chan_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.underline_rgb_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxStyle maxChan : UInt64) (s : UnderlinePenState)
        (hInit : Init maxStyle maxChan s) : UnderlineSafetyInv s :=
      And.intro
        (zero_u64_le s.styleCode s.maxStyle hInit.1)
        (zero_u64_le s.colorChan s.maxChan hInit.2.2.1)

    theorem setPen_preserves_inv (cs cc : UInt64) (s sNext : UnderlinePenState)
        (hAct : SetUnderlinePen cs cc s sNext) : UnderlineSafetyInv sNext :=
      let hS1 : Nat.le (UInt64.toNat sNext.styleCode) (UInt64.toNat s.maxStyle) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxStyle)) hAct.1)
          (style_clamp_le cs s.maxStyle)
      let hS2 : Nat.le (UInt64.toNat sNext.styleCode) (UInt64.toNat sNext.maxStyle) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.styleCode) (UInt64.toNat y)) hAct.2.1)
          hS1
      let hC1 : Nat.le (UInt64.toNat sNext.colorChan) (UInt64.toNat s.maxChan) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxChan)) hAct.2.2.1)
          (chan_clamp_le cc s.maxChan)
      let hC2 : Nat.le (UInt64.toNat sNext.colorChan) (UInt64.toNat sNext.maxChan) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.colorChan) (UInt64.toNat y)) hAct.2.2.2)
          hC1
      And.intro hS2 hC2

    theorem resetPen_preserves_inv (s sNext : UnderlinePenState)
        (hAct : ResetUnderlinePen s sNext) : UnderlineSafetyInv sNext :=
      And.intro
        (zero_u64_le sNext.styleCode sNext.maxStyle hAct.1)
        (zero_u64_le sNext.colorChan sNext.maxChan hAct.2.2.1)

    theorem next_preserves_inv (s sNext : UnderlinePenState)
        (_hInv : UnderlineSafetyInv s) (hNext : Next s sNext) :
        UnderlineSafetyInv sNext :=
      Or.elim hNext
        (fun hEx1 =>
          Exists.elim hEx1 (fun cs hEx2 =>
            Exists.elim hEx2 (fun cc hS => setPen_preserves_inv cs cc s sNext hS)))
        (fun hR => resetPen_preserves_inv s sNext hR)

    theorem spec_satisfies_underline_style_safety (maxStyle maxChan : UInt64) :
        (Spec maxStyle maxChan) ⊨ □ (Lift UnderlineSafetyInv) :=
      invariantSatisfies (Spec maxStyle maxChan) UnderlineSafetyInv
        (init_establishes_inv maxStyle maxChan)
        next_preserves_inv

    end TlaUnderlineStyle
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def underline_style_valid_isl (style : UInt64) (max_style : UInt64) : Bool :=
      decide (style ≤ max_style)
}
