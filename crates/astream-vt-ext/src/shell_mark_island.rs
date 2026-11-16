// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `shell_mark.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `shell_mark.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def shell_offset_advance (cur_off : UInt64) (next_off : UInt64) : UInt64 :=
      if cur_off < next_off then next_off else cur_off

    def shell_exit_clamp (raw_exit : UInt64) (max_exit : UInt64) : UInt64 :=
      if raw_exit < max_exit then raw_exit else max_exit

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & OSC 133 Shell Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaShellIntegration

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

    structure ShellMarkState where
      start_off : UInt64
      end_off : UInt64
      exit_code : UInt64
      max_exit : UInt64

    def ShellMarkInv (s : ShellMarkState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.start_off) (UInt64.toNat s.end_off))
        (Nat.le (UInt64.toNat s.exit_code) (UInt64.toNat s.max_exit))

    def Init (s : ShellMarkState) : Prop :=
      And
        (s.start_off = s.end_off)
        (Nat.le (UInt64.toNat s.exit_code) (UInt64.toNat s.max_exit))

    def markTransition (proposed_end : UInt64) (raw_exit : UInt64) (s : ShellMarkState) : ShellMarkState :=
      ShellMarkState.mk
        s.end_off
        (_root_.shell_offset_advance s.end_off proposed_end)
        (_root_.shell_exit_clamp raw_exit s.max_exit)
        s.max_exit

    def Next (s : ShellMarkState) (s' : ShellMarkState) : Prop :=
      ∃ (proposed_end : UInt64), ∃ (raw_exit : UInt64),
        s' = markTransition proposed_end raw_exit s

    def Spec : StateMachine ShellMarkState :=
      StateMachine.mk Init Next

    theorem end_ge_start : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.shell_offset_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem exit_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.shell_exit_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : ShellMarkState) (hInit : Init s) :
      ShellMarkInv s :=
      And.intro
        (uint64_eq_le s.start_off s.end_off (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : ShellMarkState) (s' : ShellMarkState)
      (_hInv : ShellMarkInv s) (hNext : Next s s') :
      ShellMarkInv s' :=
      Exists.elim hNext (fun (pe : UInt64) (hRest : ∃ (re : UInt64), s' = markTransition pe re s) =>
        Exists.elim hRest (fun (re : UInt64) (hEq : s' = markTransition pe re s) =>
          Eq.mpr
            (congrArg (fun (st : ShellMarkState) => ShellMarkInv st) hEq)
            (And.intro
              (end_ge_start s.end_off pe)
              (exit_le_max re s.max_exit))))

    theorem shell_mark_safety_always :
      Satisfies (Runs Spec) (Always (Lift ShellMarkInv)) :=
      invariantSatisfies Spec ShellMarkInv init_establishes_inv next_preserves_inv

    end TlaShellIntegration
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def shell_span_ordered_isl (start_off : UInt64) (end_off : UInt64) : Bool :=
      decide (start_off ≤ end_off)
}
