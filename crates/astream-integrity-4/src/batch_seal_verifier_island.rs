// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `batch_seal_verifier.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `batch_seal_verifier.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def batch_seal_seen_clamp (cand_seen : UInt64) (expected_count : UInt64) : UInt64 :=
      if cand_seen < expected_count then cand_seen else expected_count

    def batch_seal_offset_advance (cur_off : UInt64) (cand_off : UInt64) : UInt64 :=
      if cur_off < cand_off then cand_off else cur_off

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Batch Seal Verifier Spec
    -- =======================================================================

    namespace Astream
    namespace Wire
    namespace TlaBatchSealVerifier

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

    structure SealVerifierState where
      seen_records : UInt64
      expected_records : UInt64
      sealed_offset : UInt64
      prev_offset : UInt64

    def SealVerifierInv (s : SealVerifierState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.seen_records) (UInt64.toNat s.expected_records))
        (Nat.le (UInt64.toNat s.prev_offset) (UInt64.toNat s.sealed_offset))

    def Init (expected_records : UInt64) (s : SealVerifierState) : Prop :=
      And
        (And (s.seen_records = 0) (s.expected_records = expected_records))
        (And (s.sealed_offset = 0) (s.prev_offset = 0))

    def sealStep (cand_seen : UInt64) (cand_off : UInt64) (s : SealVerifierState) : SealVerifierState :=
      SealVerifierState.mk
        (_root_.batch_seal_seen_clamp cand_seen s.expected_records)
        s.expected_records
        (_root_.batch_seal_offset_advance s.sealed_offset cand_off)
        s.sealed_offset

    def Next (s : SealVerifierState) (s' : SealVerifierState) : Prop :=
      ∃ (cand_seen : UInt64), ∃ (cand_off : UInt64),
        s' = sealStep cand_seen cand_off s

    def Spec (expected_records : UInt64) : StateMachine SealVerifierState :=
      StateMachine.mk (Init expected_records) Next

    theorem seen_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.batch_seal_seen_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem seal_offset_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.batch_seal_offset_advance cur cand)) :=
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

    theorem init_establishes_inv (expected_records : UInt64) (s : SealVerifierState)
      (hInit : Init expected_records s) :
      SealVerifierInv s :=
      And.intro
        (eq_zero_le s.seen_records s.expected_records (And.left (And.left hInit)))
        (eq_zero_le s.prev_offset s.sealed_offset (And.right (And.right hInit)))

    theorem next_preserves_inv (s : SealVerifierState) (s' : SealVerifierState)
      (_hInv : SealVerifierInv s) (hNext : Next s s') :
      SealVerifierInv s' :=
      Exists.elim hNext (fun (cs : UInt64) (hRest : ∃ (co : UInt64), s' = sealStep cs co s) =>
        Exists.elim hRest (fun (co : UInt64) (hEq : s' = sealStep cs co s) =>
          Eq.mpr
            (congrArg (fun (st : SealVerifierState) => SealVerifierInv st) hEq)
            (And.intro
              (seen_clamp_le cs s.expected_records)
              (seal_offset_monotone s.sealed_offset co))))

    theorem batch_seal_verifier_safety_always (expected_records : UInt64) :
      Satisfies (Runs (Spec expected_records)) (Always (Lift SealVerifierInv)) :=
      invariantSatisfies (Spec expected_records) SealVerifierInv (init_establishes_inv expected_records) next_preserves_inv

    end TlaBatchSealVerifier
    end Wire
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def batch_seal_seen_within_expected_isl (seen : UInt64) (expected : UInt64) : Bool :=
      decide (seen <= expected)
}
