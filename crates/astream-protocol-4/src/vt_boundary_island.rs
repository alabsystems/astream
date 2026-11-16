// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `vt_boundary.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `vt_boundary.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def vt_holdback_clamp (tail_len : UInt64) (max_hold : UInt64) : UInt64 :=
      if tail_len < max_hold then tail_len else max_hold

    def vt_emitted_advance (prev_emitted : UInt64) (cand_emitted : UInt64) : UInt64 :=
      if prev_emitted < cand_emitted then cand_emitted else prev_emitted

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & VT Split-Boundary Spec
    -- =======================================================================

    namespace Astream
    namespace Pump
    namespace TlaVtFrameBoundary

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

    structure VtBoundaryState where
      emitted_bytes : UInt64
      prev_emitted : UInt64
      held_bytes : UInt64
      max_hold : UInt64

    def VtBoundaryInv (s : VtBoundaryState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_emitted) (UInt64.toNat s.emitted_bytes))
        (Nat.le (UInt64.toNat s.held_bytes) (UInt64.toNat s.max_hold))

    def Init (s : VtBoundaryState) : Prop :=
      And
        (s.held_bytes = 0)
        (And (s.emitted_bytes = 0) (s.prev_emitted = 0))

    def splitChunkStep (cand_emitted : UInt64) (raw_hold : UInt64) (s : VtBoundaryState) : VtBoundaryState :=
      VtBoundaryState.mk
        (_root_.vt_emitted_advance s.emitted_bytes cand_emitted)
        s.emitted_bytes
        (_root_.vt_holdback_clamp raw_hold s.max_hold)
        s.max_hold

    def Next (s : VtBoundaryState) (s' : VtBoundaryState) : Prop :=
      ∃ (cand_emitted : UInt64), ∃ (raw_hold : UInt64),
        s' = splitChunkStep cand_emitted raw_hold s

    def Spec : StateMachine VtBoundaryState :=
      StateMachine.mk Init Next

    theorem emitted_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.vt_emitted_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem hold_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.vt_holdback_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
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

    theorem init_establishes_inv (s : VtBoundaryState) (hInit : Init s) :
      VtBoundaryInv s :=
      And.intro
        (eq_zero_le
          s.prev_emitted
          s.emitted_bytes
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.held_bytes s.max_hold (And.left hInit))

    theorem next_preserves_inv (s : VtBoundaryState) (s' : VtBoundaryState)
      (_hInv : VtBoundaryInv s) (hNext : Next s s') :
      VtBoundaryInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (rh : UInt64), s' = splitChunkStep ce rh s) =>
        Exists.elim hRest (fun (rh : UInt64) (hEq : s' = splitChunkStep ce rh s) =>
          Eq.mpr
            (congrArg (fun (st : VtBoundaryState) => VtBoundaryInv st) hEq)
            (And.intro
              (emitted_monotone s.emitted_bytes ce)
              (hold_le_max rh s.max_hold))))

    theorem vt_boundary_safety_always :
      Satisfies (Runs Spec) (Always (Lift VtBoundaryInv)) :=
      invariantSatisfies Spec VtBoundaryInv init_establishes_inv next_preserves_inv

    end TlaVtFrameBoundary
    end Pump
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def vt_holdback_within_cap_isl (held : UInt64) (max_hold : UInt64) : Bool :=
      decide (held ≤ max_hold)
}
