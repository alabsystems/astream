// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `context_compact.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `context_compact.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def ctx_tokens_clamp (retained_tokens : UInt64) (window_budget : UInt64) : UInt64 :=
      if retained_tokens < window_budget then retained_tokens else window_budget

    def ctx_compact_gen_advance (prev_gen : UInt64) (cand_gen : UInt64) : UInt64 :=
      if prev_gen < cand_gen then cand_gen else prev_gen

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Context Compactor Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaContextCompactor

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

    structure ContextCompactState where
      retained_tokens : UInt64
      window_budget : UInt64
      compact_gen : UInt64
      prev_gen : UInt64

    def ContextCompactInv (s : ContextCompactState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.retained_tokens) (UInt64.toNat s.window_budget))
        (Nat.le (UInt64.toNat s.prev_gen) (UInt64.toNat s.compact_gen))

    def Init (s : ContextCompactState) : Prop :=
      And
        (s.retained_tokens = 0)
        (And (s.compact_gen = 0) (s.prev_gen = 0))

    def ctxStep (raw_tokens : UInt64) (cand_gen : UInt64) (s : ContextCompactState) : ContextCompactState :=
      ContextCompactState.mk
        (_root_.ctx_tokens_clamp raw_tokens s.window_budget)
        s.window_budget
        (_root_.ctx_compact_gen_advance s.compact_gen cand_gen)
        s.compact_gen

    def Next (s : ContextCompactState) (s' : ContextCompactState) : Prop :=
      ∃ (raw_tokens : UInt64), ∃ (cand_gen : UInt64),
        s' = ctxStep raw_tokens cand_gen s

    def Spec : StateMachine ContextCompactState :=
      StateMachine.mk Init Next

    theorem tokens_le_budget : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.ctx_tokens_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem gen_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.ctx_compact_gen_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : ContextCompactState) (hInit : Init s) :
      ContextCompactInv s :=
      And.intro
        (zero_le_cap s.retained_tokens s.window_budget (And.left hInit))
        (eq_zero_le
          s.prev_gen
          s.compact_gen
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : ContextCompactState) (s' : ContextCompactState)
      (_hInv : ContextCompactInv s) (hNext : Next s s') :
      ContextCompactInv s' :=
      Exists.elim hNext (fun (rt : UInt64) (hRest : ∃ (cg : UInt64), s' = ctxStep rt cg s) =>
        Exists.elim hRest (fun (cg : UInt64) (hEq : s' = ctxStep rt cg s) =>
          Eq.mpr
            (congrArg (fun (st : ContextCompactState) => ContextCompactInv st) hEq)
            (And.intro
              (tokens_le_budget rt s.window_budget)
              (gen_monotone s.compact_gen cg))))

    theorem context_compactor_safety_always :
      Satisfies (Runs Spec) (Always (Lift ContextCompactInv)) :=
      invariantSatisfies Spec ContextCompactInv init_establishes_inv next_preserves_inv

    end TlaContextCompactor
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def ctx_needs_compact_isl (used_tokens : UInt64) (trigger_watermark : UInt64) : Bool :=
      decide (trigger_watermark ≤ used_tokens)
}
