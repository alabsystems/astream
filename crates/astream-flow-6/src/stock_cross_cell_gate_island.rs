// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `scripts/stock-check.sh` 3-valued exit-code verdict aggregation
// (`Astream.Evidence.TlaStockCrossCellGate`, Island #280), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def stock_exit_code_escalate (cur_code : UInt64) (row_code : UInt64) : UInt64 :=
      if cur_code < row_code then row_code else cur_code

    def stock_cell_count_clamp (cells : UInt64) (max_cells : UInt64) : UInt64 :=
      if cells < max_cells then cells else max_cells

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Stock Cross-Cell Gate Spec
    -- =======================================================================

    namespace Astream
    namespace Evidence
    namespace TlaStockCrossCellGate

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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next)
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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next) :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure StockGateState where
      prev_code : UInt64
      exit_code : UInt64
      cells_checked : UInt64
      max_cells : UInt64

    def StockGateSafetyInv (s : StockGateState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_code) (UInt64.toNat s.exit_code))
        (Nat.le (UInt64.toNat s.cells_checked) (UInt64.toNat s.max_cells))

    def Init (s : StockGateState) : Prop :=
      And
        (s.prev_code = s.exit_code)
        (Nat.le (UInt64.toNat s.cells_checked) (UInt64.toNat s.max_cells))

    def recordCellStep (row_code : UInt64) (raw_cells : UInt64) (s : StockGateState) : StockGateState :=
      StockGateState.mk
        s.exit_code
        (_root_.stock_exit_code_escalate s.exit_code row_code)
        (_root_.stock_cell_count_clamp raw_cells s.max_cells)
        s.max_cells

    def Next (s : StockGateState) (s_next : StockGateState) : Prop :=
      ∃ (row_code : UInt64), ∃ (raw_cells : UInt64),
        s_next = recordCellStep row_code raw_cells s

    def Spec : StateMachine StockGateState :=
      StateMachine.mk Init Next

    theorem code_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.stock_exit_code_escalate cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem cells_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.stock_cell_count_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : StockGateState) (hInit : Init s) :
      StockGateSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_code s.exit_code (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : StockGateState) (s_next : StockGateState)
      (_hInv : StockGateSafetyInv s) (hNext : Next s s_next) :
      StockGateSafetyInv s_next :=
      Exists.elim hNext (fun (rc : UInt64) (hRest : ∃ (rw : UInt64), s_next = recordCellStep rc rw s) =>
        Exists.elim hRest (fun (rw : UInt64) (hEq : s_next = recordCellStep rc rw s) =>
          Eq.mpr
            (congrArg (fun (st : StockGateState) => StockGateSafetyInv st) hEq)
            (And.intro
              (code_ge_prev s.exit_code rc)
              (cells_le_cap rw s.max_cells))))

    theorem stock_gate_safety_always :
      Satisfies (Runs Spec) (Always (Lift StockGateSafetyInv)) :=
      invariantSatisfies Spec StockGateSafetyInv init_establishes_inv next_preserves_inv

    end TlaStockCrossCellGate
    end Evidence
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def stock_cells_all_checked_isl (cells_checked : UInt64) (expected_cells : UInt64) : Bool :=
      decide (cells_checked = expected_cells)
}
