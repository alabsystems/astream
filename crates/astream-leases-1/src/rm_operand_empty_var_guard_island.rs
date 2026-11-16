// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `rm` operand unguarded `$VAR` fail-safe verification
// (`Astream.Agent.TlaRmOperandEmptyVarGuard`, Island #282), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def rm_operand_count_clamp (operands : UInt64) (max_operands : UInt64) : UInt64 :=
      if operands < max_operands then operands else max_operands

    def rm_unguarded_hits_advance (prev_hits : UInt64) (next_hits : UInt64) : UInt64 :=
      if prev_hits < next_hits then next_hits else prev_hits

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Rm Operand Guard Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaRmOperandEmptyVarGuard

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

    structure RmGuardState where
      operands : UInt64
      max_operands : UInt64
      prev_hits : UInt64
      unguarded_hits : UInt64

    def RmGuardSafetyInv (s : RmGuardState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.operands) (UInt64.toNat s.max_operands))
        (Nat.le (UInt64.toNat s.prev_hits) (UInt64.toNat s.unguarded_hits))

    def Init (s : RmGuardState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.operands) (UInt64.toNat s.max_operands))
        (s.prev_hits = s.unguarded_hits)

    def scanRmStep (raw_ops : UInt64) (cand_hits : UInt64) (s : RmGuardState) : RmGuardState :=
      RmGuardState.mk
        (_root_.rm_operand_count_clamp raw_ops s.max_operands)
        s.max_operands
        s.unguarded_hits
        (_root_.rm_unguarded_hits_advance s.unguarded_hits cand_hits)

    def Next (s : RmGuardState) (s_next : RmGuardState) : Prop :=
      ∃ (raw_ops : UInt64), ∃ (cand_hits : UInt64),
        s_next = scanRmStep raw_ops cand_hits s

    def Spec : StateMachine RmGuardState :=
      StateMachine.mk Init Next

    theorem ops_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.rm_operand_count_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem hits_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.rm_unguarded_hits_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : RmGuardState) (hInit : Init s) :
      RmGuardSafetyInv s :=
      And.intro
        (And.left hInit)
        (uint64_eq_le s.prev_hits s.unguarded_hits (And.right hInit))

    theorem next_preserves_inv (s : RmGuardState) (s_next : RmGuardState)
      (_hInv : RmGuardSafetyInv s) (hNext : Next s s_next) :
      RmGuardSafetyInv s_next :=
      Exists.elim hNext (fun (ro : UInt64) (hRest : ∃ (ch : UInt64), s_next = scanRmStep ro ch s) =>
        Exists.elim hRest (fun (ch : UInt64) (hEq : s_next = scanRmStep ro ch s) =>
          Eq.mpr
            (congrArg (fun (st : RmGuardState) => RmGuardSafetyInv st) hEq)
            (And.intro
              (ops_le_cap ro s.max_operands)
              (hits_ge_prev s.unguarded_hits ch))))

    theorem rm_guard_safety_always :
      Satisfies (Runs Spec) (Always (Lift RmGuardSafetyInv)) :=
      invariantSatisfies Spec RmGuardSafetyInv init_establishes_inv next_preserves_inv

    end TlaRmOperandEmptyVarGuard
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def rm_zero_unguarded_count_isl (unguarded_count : UInt64) : Bool :=
      decide (unguarded_count ≤ (0 : UInt64))
}
