// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `osc133_shell_prompt.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `osc133_shell_prompt.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def osc133_exit_clamp (cand_exit : UInt64) (max_exit : UInt64) : UInt64 :=
      if cand_exit < max_exit then cand_exit else max_exit

    def osc133_cmd_seq_advance (cur_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_seq < cand_seq then cand_seq else cur_seq

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & OSC 133 Shell Prompt Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaOsc133ShellIntegration

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

    structure Osc133State where
      exit_code : UInt64
      max_exit : UInt64
      cmd_seq : UInt64
      prev_seq : UInt64

    def Osc133Inv (s : Osc133State) : Prop :=
      And
        (Nat.le (UInt64.toNat s.exit_code) (UInt64.toNat s.max_exit))
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.cmd_seq))

    def Init (max_exit : UInt64) (s : Osc133State) : Prop :=
      And
        (And (s.exit_code = 0) (s.max_exit = max_exit))
        (And (s.cmd_seq = 0) (s.prev_seq = 0))

    def osc133Step (cand_exit : UInt64) (cand_seq : UInt64) (s : Osc133State) : Osc133State :=
      Osc133State.mk
        (_root_.osc133_exit_clamp cand_exit s.max_exit)
        s.max_exit
        (_root_.osc133_cmd_seq_advance s.cmd_seq cand_seq)
        s.cmd_seq

    def Next (s : Osc133State) (s' : Osc133State) : Prop :=
      ∃ (cand_exit : UInt64), ∃ (cand_seq : UInt64),
        s' = osc133Step cand_exit cand_seq s

    def Spec (max_exit : UInt64) : StateMachine Osc133State :=
      StateMachine.mk (Init max_exit) Next

    theorem exit_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc133_exit_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem cmd_seq_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.osc133_cmd_seq_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_exit : UInt64) (s : Osc133State)
      (hInit : Init max_exit s) :
      Osc133Inv s :=
      And.intro
        (eq_zero_le s.exit_code s.max_exit (And.left (And.left hInit)))
        (eq_zero_le s.prev_seq s.cmd_seq (And.right (And.right hInit)))

    theorem next_preserves_inv (s : Osc133State) (s' : Osc133State)
      (_hInv : Osc133Inv s) (hNext : Next s s') :
      Osc133Inv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (cs : UInt64), s' = osc133Step ce cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = osc133Step ce cs s) =>
          Eq.mpr
            (congrArg (fun (st : Osc133State) => Osc133Inv st) hEq)
            (And.intro
              (exit_clamp_le ce s.max_exit)
              (cmd_seq_monotone s.cmd_seq cs))))

    theorem osc133_shell_integration_safety_always (max_exit : UInt64) :
      Satisfies (Runs (Spec max_exit)) (Always (Lift Osc133Inv)) :=
      invariantSatisfies (Spec max_exit) Osc133Inv (init_establishes_inv max_exit) next_preserves_inv

    end TlaOsc133ShellIntegration
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def osc133_exit_within_max_isl (exit_code : UInt64) (max_exit : UInt64) : Bool :=
      decide (exit_code <= max_exit)
}
