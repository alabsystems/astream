// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `tool_output_spill.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `tool_output_spill.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def spill_inline_clamp (cand_bytes : UInt64) (max_inline : UInt64) : UInt64 :=
      if cand_bytes < max_inline then cand_bytes else max_inline

    def spill_step_advance (cur_step : UInt64) (cand_step : UInt64) : UInt64 :=
      if cur_step < cand_step then cand_step else cur_step

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Tool Output Spiller Spec
    -- =======================================================================

    namespace Astream
    namespace Live
    namespace TlaToolOutputSpiller

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

    structure SpillerState where
      inline_bytes : UInt64
      max_inline : UInt64
      spill_step : UInt64
      prev_step : UInt64

    def ToolOutputSpillerInv (s : SpillerState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.inline_bytes) (UInt64.toNat s.max_inline))
        (Nat.le (UInt64.toNat s.prev_step) (UInt64.toNat s.spill_step))

    def Init (max_inline : UInt64) (s : SpillerState) : Prop :=
      And
        (And (s.inline_bytes = 0) (s.max_inline = max_inline))
        (And (s.spill_step = 0) (s.prev_step = 0))

    def spillAction (cand_bytes : UInt64) (cand_step : UInt64) (s : SpillerState) : SpillerState :=
      SpillerState.mk
        (_root_.spill_inline_clamp cand_bytes s.max_inline)
        s.max_inline
        (_root_.spill_step_advance s.spill_step cand_step)
        s.spill_step

    def Next (s : SpillerState) (s' : SpillerState) : Prop :=
      ∃ (cand_bytes : UInt64), ∃ (cand_step : UInt64),
        s' = spillAction cand_bytes cand_step s

    def Spec (max_inline : UInt64) : StateMachine SpillerState :=
      StateMachine.mk (Init max_inline) Next

    theorem inline_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.spill_inline_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem step_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.spill_step_advance cur cand)) :=
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

    theorem init_establishes_inv (max_inline : UInt64) (s : SpillerState)
      (hInit : Init max_inline s) :
      ToolOutputSpillerInv s :=
      And.intro
        (eq_zero_le s.inline_bytes s.max_inline (And.left (And.left hInit)))
        (eq_zero_le s.prev_step s.spill_step (And.right (And.right hInit)))

    theorem next_preserves_inv (s : SpillerState) (s' : SpillerState)
      (_hInv : ToolOutputSpillerInv s) (hNext : Next s s') :
      ToolOutputSpillerInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (cs : UInt64), s' = spillAction cb cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = spillAction cb cs s) =>
          Eq.mpr
            (congrArg (fun (st : SpillerState) => ToolOutputSpillerInv st) hEq)
            (And.intro
              (inline_clamp_le cb s.max_inline)
              (step_monotone s.spill_step cs))))

    theorem tool_output_spiller_safety_always (max_inline : UInt64) :
      Satisfies (Runs (Spec max_inline)) (Always (Lift ToolOutputSpillerInv)) :=
      invariantSatisfies (Spec max_inline) ToolOutputSpillerInv (init_establishes_inv max_inline) next_preserves_inv

    end TlaToolOutputSpiller
    end Live
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def spill_inline_within_cap_isl (inline_len : UInt64) (max_inline : UInt64) : Bool :=
      decide (inline_len <= max_inline)
}
