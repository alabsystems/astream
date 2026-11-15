// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `wasm.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `wasm.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def wasm_fuel_advance (spent : UInt64) (next_spent : UInt64) : UInt64 :=
      if spent < next_spent then next_spent else spent

    def wasm_mem_clamp (addr_end : UInt64) (mem_cap : UInt64) : UInt64 :=
      if addr_end < mem_cap then addr_end else mem_cap

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Deterministic Wasm Spec
    -- =======================================================================

    namespace Astream
    namespace Effects
    namespace TlaWasmSandbox

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

    structure WasmVmState where
      prev_spent : UInt64
      spent_fuel : UInt64
      mem_used : UInt64
      mem_cap : UInt64

    def WasmSandboxInv (s : WasmVmState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_spent) (UInt64.toNat s.spent_fuel))
        (Nat.le (UInt64.toNat s.mem_used) (UInt64.toNat s.mem_cap))

    def Init (s : WasmVmState) : Prop :=
      And
        (s.prev_spent = s.spent_fuel)
        (Nat.le (UInt64.toNat s.mem_used) (UInt64.toNat s.mem_cap))

    def execOpStep (proposed_spent : UInt64) (raw_mem : UInt64) (s : WasmVmState) : WasmVmState :=
      WasmVmState.mk
        s.spent_fuel
        (_root_.wasm_fuel_advance s.spent_fuel proposed_spent)
        (_root_.wasm_mem_clamp raw_mem s.mem_cap)
        s.mem_cap

    def Next (s : WasmVmState) (s' : WasmVmState) : Prop :=
      ∃ (proposed_spent : UInt64), ∃ (raw_mem : UInt64),
        s' = execOpStep proposed_spent raw_mem s

    def Spec : StateMachine WasmVmState :=
      StateMachine.mk Init Next

    theorem fuel_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.wasm_fuel_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem mem_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.wasm_mem_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : WasmVmState) (hInit : Init s) :
      WasmSandboxInv s :=
      And.intro
        (uint64_eq_le s.prev_spent s.spent_fuel (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : WasmVmState) (s' : WasmVmState)
      (_hInv : WasmSandboxInv s) (hNext : Next s s') :
      WasmSandboxInv s' :=
      Exists.elim hNext (fun (ps : UInt64) (hRest : ∃ (rm : UInt64), s' = execOpStep ps rm s) =>
        Exists.elim hRest (fun (rm : UInt64) (hEq : s' = execOpStep ps rm s) =>
          Eq.mpr
            (congrArg (fun (st : WasmVmState) => WasmSandboxInv st) hEq)
            (And.intro
              (fuel_ge_prev s.spent_fuel ps)
              (mem_le_cap rm s.mem_cap))))

    theorem wasm_sandbox_safety_always :
      Satisfies (Runs Spec) (Always (Lift WasmSandboxInv)) :=
      invariantSatisfies Spec WasmSandboxInv init_establishes_inv next_preserves_inv

    end TlaWasmSandbox
    end Effects
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def wasm_fuel_remaining_isl (spent : UInt64) (limit : UInt64) : Bool :=
      decide (spent < limit)
}
