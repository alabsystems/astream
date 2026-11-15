// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for soft-wrap terminal grid reflow (`Astream.Term.TlaGridReflow`),
// mounted under `cfg(clean_islands)` in `screen.rs`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def reflow_col_clamp (col : UInt64) (max_col : UInt64) : UInt64 :=
      if col < max_col then col else max_col

    def reflow_row_clamp (row : UInt64) (max_row : UInt64) : UInt64 :=
      if row < max_row then row else max_row

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Grid Reflow Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaGridReflow

    def Behavior (State : Type) : Type := Nat → State

    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun (k : Nat) => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (n : Nat), P (drop n b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (n : Nat), M.Next (b n) (b (Nat.add n 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (P : Formula State) (Q : Formula State) : Prop :=
      ∀ (b : Behavior State), P b → Q b

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

    structure ReflowState where
      cur_col : UInt64
      max_col : UInt64
      cur_row : UInt64
      max_row : UInt64

    def ReflowBoundsInv (s : ReflowState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.cur_col) (UInt64.toNat s.max_col))
        (Nat.le (UInt64.toNat s.cur_row) (UInt64.toNat s.max_row))

    def Init (s : ReflowState) : Prop :=
      And
        (s.cur_col = 0)
        (s.cur_row = 0)

    def resizeReflowStep (raw_col : UInt64) (new_max_col : UInt64) (raw_row : UInt64) (new_max_row : UInt64) : ReflowState :=
      ReflowState.mk
        (_root_.reflow_col_clamp raw_col new_max_col)
        new_max_col
        (_root_.reflow_row_clamp raw_row new_max_row)
        new_max_row

    def Next (_s : ReflowState) (s' : ReflowState) : Prop :=
      ∃ (raw_col : UInt64), ∃ (new_max_col : UInt64), ∃ (raw_row : UInt64), ∃ (new_max_row : UInt64),
        s' = resizeReflowStep raw_col new_max_col raw_row new_max_row

    def Spec : StateMachine ReflowState :=
      StateMachine.mk Init Next

    theorem col_clamp_le : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.reflow_col_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem row_clamp_le : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.reflow_row_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : ReflowState) (hInit : Init s) :
      ReflowBoundsInv s :=
      And.intro
        (zero_le_cap s.cur_col s.max_col (And.left hInit))
        (zero_le_cap s.cur_row s.max_row (And.right hInit))

    theorem next_preserves_inv (s : ReflowState) (s' : ReflowState)
      (_hInv : ReflowBoundsInv s) (hNext : Next s s') :
      ReflowBoundsInv s' :=
      Exists.elim hNext (fun (rc : UInt64) (h1 : ∃ (mc : UInt64), ∃ (rr : UInt64), ∃ (mr : UInt64), s' = resizeReflowStep rc mc rr mr) =>
        Exists.elim h1 (fun (mc : UInt64) (h2 : ∃ (rr : UInt64), ∃ (mr : UInt64), s' = resizeReflowStep rc mc rr mr) =>
          Exists.elim h2 (fun (rr : UInt64) (h3 : ∃ (mr : UInt64), s' = resizeReflowStep rc mc rr mr) =>
            Exists.elim h3 (fun (mr : UInt64) (hEq : s' = resizeReflowStep rc mc rr mr) =>
              Eq.mpr
                (congrArg (fun (st : ReflowState) => ReflowBoundsInv st) hEq)
                (And.intro
                  (col_clamp_le rc mc)
                  (row_clamp_le rr mr))))))

    theorem reflow_bounds_always :
      Satisfies (Runs Spec) (Always (Lift ReflowBoundsInv)) :=
      invariantSatisfies Spec ReflowBoundsInv init_establishes_inv next_preserves_inv

    end TlaGridReflow
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def reflow_cursor_in_grid_isl (col : UInt16) (cols : UInt16) : Bool :=
      decide (col < cols)
}
