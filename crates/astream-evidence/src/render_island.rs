// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `render.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `render.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def render_clamp_span_start (begin_pos : UInt64) (end_pos : UInt64) : UInt64 :=
      if begin_pos < end_pos then begin_pos else end_pos

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Marker Span Ordering
    -- =======================================================================

    namespace Astream
    namespace Evidence
    namespace TlaEvidenceRender

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

    structure MarkerSpanState where
      begin_pos : UInt64
      end_pos : UInt64

    def MarkerSpanOrderedInv (s : MarkerSpanState) : Prop :=
      Nat.le (UInt64.toNat s.begin_pos) (UInt64.toNat s.end_pos)

    def Init (s : MarkerSpanState) : Prop :=
      s.begin_pos = 0

    def locateSpanAction (proposed_begin : UInt64) (s : MarkerSpanState) : MarkerSpanState :=
      MarkerSpanState.mk (_root_.render_clamp_span_start proposed_begin s.end_pos) s.end_pos

    def Next (s : MarkerSpanState) (s' : MarkerSpanState) : Prop :=
      ∃ (proposed_begin : UInt64), s' = locateSpanAction proposed_begin s

    def Spec : StateMachine MarkerSpanState :=
      StateMachine.mk Init Next

    theorem clamp_le_end : forall (proposed_begin : UInt64) (end_pos : UInt64),
        Nat.le (UInt64.toNat (_root_.render_clamp_span_start proposed_begin end_pos)) (UInt64.toNat end_pos) :=
      fun proposed_begin end_pos => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt proposed_begin end_pos)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => end_pos) (fun _ => proposed_begin))) (UInt64.toNat end_pos))
        (instDecidableUInt64Lt proposed_begin end_pos)
        (fun _ => @Nat.le.refl (UInt64.toNat end_pos))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (x : UInt64) : Nat.le (UInt64.toNat 0) (UInt64.toNat x) :=
      Nat.zero_le (UInt64.toNat x)

    theorem init_establishes_inv (s : MarkerSpanState) (hInit : Init s) :
      MarkerSpanOrderedInv s :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.end_pos)) hInit)
        (uint64_zero_le s.end_pos)

    theorem next_preserves_inv (s : MarkerSpanState) (s' : MarkerSpanState)
      (_hInv : MarkerSpanOrderedInv s) (hNext : Next s s') :
      MarkerSpanOrderedInv s' :=
      Exists.elim hNext (fun (proposed_begin : UInt64) (hEq : s' = locateSpanAction proposed_begin s) =>
        Eq.mpr
          (congrArg (fun (st : MarkerSpanState) => MarkerSpanOrderedInv st) hEq)
          (clamp_le_end proposed_begin s.end_pos))

    theorem spec_satisfies_marker_span_ordered :
      Satisfies (Runs Spec) (Always (Lift MarkerSpanOrderedInv)) :=
      invariantSatisfies Spec MarkerSpanOrderedInv init_establishes_inv next_preserves_inv

    end TlaEvidenceRender
    end Evidence
    end Astream

    def render_markers_ordered_isl (begin_pos : USize) (end_pos : USize) : Bool :=
      decide (begin_pos ≤ end_pos)
}
