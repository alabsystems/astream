// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `provenance.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `provenance.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def provenance_seq_advance (cur_seq : UInt64) (next_seq : UInt64) : UInt64 :=
      if cur_seq < next_seq then next_seq else cur_seq

    def provenance_skew_clamp (skew_ms : UInt64) (max_skew_ms : UInt64) : UInt64 :=
      if skew_ms < max_skew_ms then skew_ms else max_skew_ms

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Input Provenance Spec
    -- =======================================================================

    namespace Astream
    namespace Cap
    namespace TlaInputProvenance

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

    structure ProvenanceState where
      prev_seq : UInt64
      cur_seq : UInt64
      skew_ms : UInt64
      max_skew_ms : UInt64

    def ProvenanceInv (s : ProvenanceState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.cur_seq))
        (Nat.le (UInt64.toNat s.skew_ms) (UInt64.toNat s.max_skew_ms))

    def Init (s : ProvenanceState) : Prop :=
      And
        (s.prev_seq = s.cur_seq)
        (Nat.le (UInt64.toNat s.skew_ms) (UInt64.toNat s.max_skew_ms))

    def admitInputStep (proposed_seq : UInt64) (raw_skew : UInt64) (s : ProvenanceState) : ProvenanceState :=
      ProvenanceState.mk
        s.cur_seq
        (_root_.provenance_seq_advance s.cur_seq proposed_seq)
        (_root_.provenance_skew_clamp raw_skew s.max_skew_ms)
        s.max_skew_ms

    def Next (s : ProvenanceState) (s' : ProvenanceState) : Prop :=
      ∃ (proposed_seq : UInt64), ∃ (raw_skew : UInt64),
        s' = admitInputStep proposed_seq raw_skew s

    def Spec : StateMachine ProvenanceState :=
      StateMachine.mk Init Next

    theorem seq_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.provenance_seq_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem skew_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.provenance_skew_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : ProvenanceState) (hInit : Init s) :
      ProvenanceInv s :=
      And.intro
        (uint64_eq_le s.prev_seq s.cur_seq (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : ProvenanceState) (s' : ProvenanceState)
      (_hInv : ProvenanceInv s) (hNext : Next s s') :
      ProvenanceInv s' :=
      Exists.elim hNext (fun (ps : UInt64) (hRest : ∃ (rs : UInt64), s' = admitInputStep ps rs s) =>
        Exists.elim hRest (fun (rs : UInt64) (hEq : s' = admitInputStep ps rs s) =>
          Eq.mpr
            (congrArg (fun (st : ProvenanceState) => ProvenanceInv st) hEq)
            (And.intro
              (seq_ge_prev s.cur_seq ps)
              (skew_le_max rs s.max_skew_ms))))

    theorem input_provenance_safety_always :
      Satisfies (Runs Spec) (Always (Lift ProvenanceInv)) :=
      invariantSatisfies Spec ProvenanceInv init_establishes_inv next_preserves_inv

    end TlaInputProvenance
    end Cap
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def provenance_seq_fresh_isl (last_seq : UInt64) (seq : UInt64) : Bool :=
      decide (last_seq < seq)
}
