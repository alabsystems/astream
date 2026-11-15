// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `events.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `events.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def event_advance_offset_monotone (cur_offset : UInt64) (next_offset : UInt64) : UInt64 :=
      if cur_offset < next_offset then next_offset else cur_offset

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaEventClassifier)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaEventClassifier

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
    -- 3. EventClassifier Offset Monotonicity State Machine & Safety Theorem
    -- ========================================================================

    structure ClassifierState where
      cur_offset : UInt64
      prev_offset : UInt64

    def ClassifierOffsetMonotoneInv (s : ClassifierState) : Prop :=
      Nat.le (UInt64.toNat s.prev_offset) (UInt64.toNat s.cur_offset)

    def Init (s : ClassifierState) : Prop :=
      And (s.cur_offset = (0 : UInt64)) (s.prev_offset = (0 : UInt64))

    def pushAction (next_offset : UInt64) (s : ClassifierState) : ClassifierState :=
      ClassifierState.mk
        (_root_.event_advance_offset_monotone s.cur_offset next_offset)
        s.cur_offset

    def Next (s : ClassifierState) (s' : ClassifierState) : Prop :=
      ∃ (next_offset : UInt64), s' = pushAction next_offset s

    def Spec : StateMachine ClassifierState :=
      StateMachine.mk Init Next

    theorem advance_ge_cur : forall (cur_offset : UInt64) (next_offset : UInt64),
        Nat.le (UInt64.toNat cur_offset) (UInt64.toNat (_root_.event_advance_offset_monotone cur_offset next_offset)) :=
      fun cur_offset next_offset => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur_offset next_offset)) =>
          Nat.le (UInt64.toNat cur_offset)
            (UInt64.toNat (Decidable.casesOn
              (motive := fun _ => UInt64) d (fun _ => cur_offset) (fun _ => next_offset))))
        (instDecidableUInt64Lt cur_offset next_offset)
        (fun _ => Nat.le.refl (UInt64.toNat cur_offset))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (Nat.le.refl (UInt64.toNat a))

    theorem init_establishes_inv (s : ClassifierState) (hInit : Init s) :
      ClassifierOffsetMonotoneInv s :=
      uint64_eq_le
        s.prev_offset
        s.cur_offset
        (Eq.trans (And.right hInit) (Eq.symm (And.left hInit)))

    theorem next_preserves_inv (s : ClassifierState) (s' : ClassifierState)
      (_hInv : ClassifierOffsetMonotoneInv s) (hNext : Next s s') :
      ClassifierOffsetMonotoneInv s' :=
      Exists.elim hNext (fun (next_offset : UInt64) (hEq : s' = pushAction next_offset s) =>
        Eq.mpr
          (congrArg (fun (st : ClassifierState) => ClassifierOffsetMonotoneInv st) hEq)
          (advance_ge_cur s.cur_offset next_offset))

    theorem spec_satisfies_classifier_offset_monotonicity :
      Satisfies (Runs Spec) (Always (Lift ClassifierOffsetMonotoneInv)) :=
      invariantSatisfies Spec ClassifierOffsetMonotoneInv init_establishes_inv next_preserves_inv

    end TlaEventClassifier
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def event_carry_within_bound_isl (len : UInt64) (max_carry : UInt64) : Bool :=
      decide (len ≤ max_carry)
}
