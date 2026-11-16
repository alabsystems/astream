// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `effect_budget.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `effect_budget.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def effect_bytes_clamp (cand_bytes : UInt64) (byte_cap : UInt64) : UInt64 :=
      if cand_bytes < byte_cap then cand_bytes else byte_cap

    def effect_seq_advance (cur_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_seq < cand_seq then cand_seq else cur_seq

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Seam Effect Budget Spec
    -- =======================================================================

    namespace Astream
    namespace Effects
    namespace TlaSeamEffectBudget

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

    structure SeamBudgetState where
      accounted_bytes : UInt64
      byte_cap : UInt64
      effect_seq : UInt64
      prev_seq : UInt64

    def SeamEffectBudgetInv (s : SeamBudgetState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.accounted_bytes) (UInt64.toNat s.byte_cap))
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.effect_seq))

    def Init (byte_cap : UInt64) (s : SeamBudgetState) : Prop :=
      And
        (And (s.accounted_bytes = 0) (s.byte_cap = byte_cap))
        (And (s.effect_seq = 0) (s.prev_seq = 0))

    def admitStep (cand_bytes : UInt64) (cand_seq : UInt64) (s : SeamBudgetState) : SeamBudgetState :=
      SeamBudgetState.mk
        (_root_.effect_bytes_clamp cand_bytes s.byte_cap)
        s.byte_cap
        (_root_.effect_seq_advance s.effect_seq cand_seq)
        s.effect_seq

    def Next (s : SeamBudgetState) (s' : SeamBudgetState) : Prop :=
      ∃ (cand_bytes : UInt64), ∃ (cand_seq : UInt64),
        s' = admitStep cand_bytes cand_seq s

    def Spec (byte_cap : UInt64) : StateMachine SeamBudgetState :=
      StateMachine.mk (Init byte_cap) Next

    theorem bytes_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.effect_bytes_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem seq_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.effect_seq_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (byte_cap : UInt64) (s : SeamBudgetState)
      (hInit : Init byte_cap s) :
      SeamEffectBudgetInv s :=
      And.intro
        (eq_zero_le s.accounted_bytes s.byte_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_seq s.effect_seq (And.right (And.right hInit)))

    theorem next_preserves_inv (s : SeamBudgetState) (s' : SeamBudgetState)
      (_hInv : SeamEffectBudgetInv s) (hNext : Next s s') :
      SeamEffectBudgetInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (cs : UInt64), s' = admitStep cb cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = admitStep cb cs s) =>
          Eq.mpr
            (congrArg (fun (st : SeamBudgetState) => SeamEffectBudgetInv st) hEq)
            (And.intro
              (bytes_clamp_le cb s.byte_cap)
              (seq_monotone s.effect_seq cs))))

    theorem seam_effect_budget_safety_always (byte_cap : UInt64) :
      Satisfies (Runs (Spec byte_cap)) (Always (Lift SeamEffectBudgetInv)) :=
      invariantSatisfies (Spec byte_cap) SeamEffectBudgetInv (init_establishes_inv byte_cap) next_preserves_inv

    end TlaSeamEffectBudget
    end Effects
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def effect_bytes_within_cap_isl (used_bytes : UInt64) (byte_cap : UInt64) : Bool :=
      decide (used_bytes <= byte_cap)
}
