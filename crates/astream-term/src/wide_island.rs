// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for East Asian Wide / Emoji double-width cell bounds (`wcwidth == 2`)
// and right-margin spacer column clamping (`screen.rs`), mounted under `cfg(clean_islands)`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def wide_cell_width_clamp (width : UInt64) (max_width : UInt64) : UInt64 :=
      if width < max_width then width else max_width

    def wide_spacer_col_clamp (next_col : UInt64) (line_end : UInt64) : UInt64 :=
      if next_col < line_end then next_col else line_end

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaWideCell)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaWideCell

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (k : Nat) (b : Behavior State) : Behavior State :=
      fun (n : Nat) => b (Nat.add k n)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (k : Nat), P (drop k b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (k : Nat), M.Next (b k) (b (Nat.add k 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (SpecF : Formula State) (PropF : Formula State) : Prop :=
      ∀ (b : Behavior State), SpecF b → PropF b

    theorem invariantAt
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s')
      (b : Behavior State)
      (hRun : Runs M b)
      (k : Nat) :
      Inv (b k) :=
      Nat.rec
        (hInit (b 0) (And.left hRun))
        (fun (j : Nat) (ih : Inv (b j)) =>
          hStep (b j) (b (Nat.add j 1)) ih (And.right hRun j))
        k

    theorem invariantSatisfies
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s') :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    -- ========================================================================
    -- 3. Double-Width Cell Width & Spacer Column Coherence Safety Theorems
    -- ========================================================================

    structure WideCellState where
      cell_width : UInt64
      max_width : UInt64
      spacer_col : UInt64
      line_end : UInt64

    def WidePairCoherenceInv (s : WideCellState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.cell_width) (UInt64.toNat s.max_width))
        (Nat.le (UInt64.toNat s.spacer_col) (UInt64.toNat s.line_end))

    def Init (s : WideCellState) : Prop :=
      And (s.cell_width = (0 : UInt64)) (s.spacer_col = (0 : UInt64))

    def paintWideCellAction
      (raw_w : UInt64)
      (max_w : UInt64)
      (raw_next : UInt64)
      (end_col : UInt64)
      (_s : WideCellState) : WideCellState :=
      WideCellState.mk
        (_root_.wide_cell_width_clamp raw_w max_w)
        max_w
        (_root_.wide_spacer_col_clamp raw_next end_col)
        end_col

    def Next (s : WideCellState) (s' : WideCellState) : Prop :=
      ∃ (raw_w : UInt64),
        ∃ (max_w : UInt64),
          ∃ (raw_next : UInt64),
            ∃ (end_col : UInt64),
              s' = paintWideCellAction raw_w max_w raw_next end_col s

    def Spec : StateMachine WideCellState :=
      StateMachine.mk Init Next

    theorem width_clamp_le_max : forall (w : UInt64) (mw : UInt64),
        Nat.le (UInt64.toNat (_root_.wide_cell_width_clamp w mw)) (UInt64.toNat mw) :=
      fun w mw => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt w mw)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => mw) (fun _ => w))) (UInt64.toNat mw))
        (instDecidableUInt64Lt w mw)
        (fun _ => Nat.le.refl (UInt64.toNat mw))
        (fun hLt => Nat.le_of_lt hLt)

    theorem spacer_clamp_le_end : forall (nc : UInt64) (ec : UInt64),
        Nat.le (UInt64.toNat (_root_.wide_spacer_col_clamp nc ec)) (UInt64.toNat ec) :=
      fun nc ec => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt nc ec)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => ec) (fun _ => nc))) (UInt64.toNat ec))
        (instDecidableUInt64Lt nc ec)
        (fun _ => Nat.le.refl (UInt64.toNat ec))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : WideCellState) (hInit : Init s) :
      WidePairCoherenceInv s :=
      And.intro
        (uint64_zero_le s.cell_width s.max_width (And.left hInit))
        (uint64_zero_le s.spacer_col s.line_end (And.right hInit))

    theorem next_preserves_inv (s : WideCellState) (s' : WideCellState)
      (_hInv : WidePairCoherenceInv s) (hNext : Next s s') :
      WidePairCoherenceInv s' :=
      Exists.elim hNext (fun (rw : UInt64) (h1 : ∃ (mw : UInt64), ∃ (rn : UInt64), ∃ (ec : UInt64), s' = paintWideCellAction rw mw rn ec s) =>
        Exists.elim h1 (fun (mw : UInt64) (h2 : ∃ (rn : UInt64), ∃ (ec : UInt64), s' = paintWideCellAction rw mw rn ec s) =>
          Exists.elim h2 (fun (rn : UInt64) (h3 : ∃ (ec : UInt64), s' = paintWideCellAction rw mw rn ec s) =>
            Exists.elim h3 (fun (ec : UInt64) (hEq : s' = paintWideCellAction rw mw rn ec s) =>
              Eq.mpr
                (congrArg (fun (st : WideCellState) => WidePairCoherenceInv st) hEq)
                (And.intro
                  (width_clamp_le_max rw mw)
                  (spacer_clamp_le_end rn ec))))))

    theorem spec_satisfies_wide_cell_coherence :
      Satisfies (Runs Spec) (Always (Lift WidePairCoherenceInv)) :=
      invariantSatisfies Spec WidePairCoherenceInv init_establishes_inv next_preserves_inv

    end TlaWideCell
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def cell_width_is_valid_isl (w : UInt8) : Bool :=
      decide (w ≤ 2)
}
