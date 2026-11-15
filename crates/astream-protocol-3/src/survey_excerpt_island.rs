// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `survey_excerpt.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `survey_excerpt.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def survey_clamp_bytes (req_bytes : UInt64) (max_bytes : UInt64) : UInt64 :=
      if req_bytes < max_bytes then req_bytes else max_bytes

    def survey_clamp_lines (req_lines : UInt64) (max_lines : UInt64) : UInt64 :=
      if req_lines < max_lines then req_lines else max_lines

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Survey Excerpt Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaSurveyExcerpt

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

    structure SurveyExcerptState where
      emitted_bytes : UInt64
      max_bytes : UInt64
      emitted_lines : UInt64
      max_lines : UInt64

    def SurveyExcerptInv (s : SurveyExcerptState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.emitted_bytes) (UInt64.toNat s.max_bytes))
        (Nat.le (UInt64.toNat s.emitted_lines) (UInt64.toNat s.max_lines))

    def Init (s : SurveyExcerptState) : Prop :=
      And (s.emitted_bytes = 0) (s.emitted_lines = 0)

    def sampleExcerptStep (cand_bytes : UInt64) (cand_lines : UInt64) (s : SurveyExcerptState) : SurveyExcerptState :=
      SurveyExcerptState.mk
        (_root_.survey_clamp_bytes cand_bytes s.max_bytes)
        s.max_bytes
        (_root_.survey_clamp_lines cand_lines s.max_lines)
        s.max_lines

    def Next (s : SurveyExcerptState) (s' : SurveyExcerptState) : Prop :=
      ∃ (cand_bytes : UInt64), ∃ (cand_lines : UInt64),
        s' = sampleExcerptStep cand_bytes cand_lines s

    def Spec : StateMachine SurveyExcerptState :=
      StateMachine.mk Init Next

    theorem clamp_bytes_le : forall (req : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.survey_clamp_bytes req cap)) (UInt64.toNat cap) :=
      fun req cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt req cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => req))) (UInt64.toNat cap))
        (instDecidableUInt64Lt req cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clamp_lines_le : forall (req : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.survey_clamp_lines req cap)) (UInt64.toNat cap) :=
      fun req cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt req cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => req))) (UInt64.toNat cap))
        (instDecidableUInt64Lt req cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : SurveyExcerptState) (hInit : Init s) :
      SurveyExcerptInv s :=
      And.intro
        (zero_le_cap s.emitted_bytes s.max_bytes (And.left hInit))
        (zero_le_cap s.emitted_lines s.max_lines (And.right hInit))

    theorem next_preserves_inv (s : SurveyExcerptState) (s' : SurveyExcerptState)
      (_hInv : SurveyExcerptInv s) (hNext : Next s s') :
      SurveyExcerptInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (cl : UInt64), s' = sampleExcerptStep cb cl s) =>
        Exists.elim hRest (fun (cl : UInt64) (hEq : s' = sampleExcerptStep cb cl s) =>
          Eq.mpr
            (congrArg (fun (st : SurveyExcerptState) => SurveyExcerptInv st) hEq)
            (And.intro
              (clamp_bytes_le cb s.max_bytes)
              (clamp_lines_le cl s.max_lines))))

    theorem survey_excerpt_safety_always :
      Satisfies (Runs Spec) (Always (Lift SurveyExcerptInv)) :=
      invariantSatisfies Spec SurveyExcerptInv init_establishes_inv next_preserves_inv

    end TlaSurveyExcerpt
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def survey_is_stalled_isl (unchanged_ticks : UInt64) (threshold : UInt64) : Bool :=
      decide (threshold ≤ unchanged_ticks)
}
