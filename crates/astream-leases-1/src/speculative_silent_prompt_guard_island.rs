// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `SpeculativeTerminal` password/passphrase silent-prompt suppression
// (`Astream.Term.TlaSpeculativeSilentPromptGuard`, Island #286), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def silent_tail_len_clamp (tail_len : UInt64) (max_tail : UInt64) : UInt64 :=
      if tail_len < max_tail then tail_len else max_tail

    def silent_suppressed_advance (prev : UInt64) (next : UInt64) : UInt64 :=
      if prev < next then next else prev

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Silent Prompt Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaSpeculativeSilentPromptGuard

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

    structure SilentPromptState where
      tail_len : UInt64
      max_tail : UInt64
      prev_suppressed : UInt64
      suppressed : UInt64

    def SilentSafetyInv (s : SilentPromptState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.tail_len) (UInt64.toNat s.max_tail))
        (Nat.le (UInt64.toNat s.prev_suppressed) (UInt64.toNat s.suppressed))

    def Init (s : SilentPromptState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.tail_len) (UInt64.toNat s.max_tail))
        (s.prev_suppressed = s.suppressed)

    def keystrokeStep (raw_tail : UInt64) (cand_suppressed : UInt64) (s : SilentPromptState) : SilentPromptState :=
      SilentPromptState.mk
        (_root_.silent_tail_len_clamp raw_tail s.max_tail)
        s.max_tail
        s.suppressed
        (_root_.silent_suppressed_advance s.suppressed cand_suppressed)

    def Next (s : SilentPromptState) (s_next : SilentPromptState) : Prop :=
      ∃ (raw_tail : UInt64), ∃ (cand_suppressed : UInt64),
        s_next = keystrokeStep raw_tail cand_suppressed s

    def Spec : StateMachine SilentPromptState :=
      StateMachine.mk Init Next

    theorem tail_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.silent_tail_len_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem supp_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.silent_suppressed_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : SilentPromptState) (hInit : Init s) :
      SilentSafetyInv s :=
      And.intro
        (And.left hInit)
        (uint64_eq_le s.prev_suppressed s.suppressed (And.right hInit))

    theorem next_preserves_inv (s : SilentPromptState) (s_next : SilentPromptState)
      (_hInv : SilentSafetyInv s) (hNext : Next s s_next) :
      SilentSafetyInv s_next :=
      Exists.elim hNext (fun (rt : UInt64) (hRest : ∃ (cs : UInt64), s_next = keystrokeStep rt cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s_next = keystrokeStep rt cs s) =>
          Eq.mpr
            (congrArg (fun (st : SilentPromptState) => SilentSafetyInv st) hEq)
            (And.intro
              (tail_le_cap rt s.max_tail)
              (supp_ge_prev s.suppressed cs))))

    theorem silent_prompt_safety_always :
      Satisfies (Runs Spec) (Always (Lift SilentSafetyInv)) :=
      invariantSatisfies Spec SilentSafetyInv init_establishes_inv next_preserves_inv

    end TlaSpeculativeSilentPromptGuard
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def silent_echo_permitted_isl (latched_silent : UInt64) : Bool :=
      decide (latched_silent = (0 : UInt64))
}
