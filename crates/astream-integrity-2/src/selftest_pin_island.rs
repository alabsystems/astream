// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `selftest_pin.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `selftest_pin.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def pin_excerpt_clamp (cand_len : UInt64) (max_excerpt : UInt64) : UInt64 :=
      if cand_len < max_excerpt then cand_len else max_excerpt

    def pin_verified_advance (cur_verified : UInt64) (cand_verified : UInt64) : UInt64 :=
      if cur_verified < cand_verified then cand_verified else cur_verified

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Selftest Digest Pin Spec
    -- =======================================================================

    namespace Astream
    namespace Evidence
    namespace TlaSelftestDigestPin

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

    structure SelftestPinState where
      excerpt_bytes : UInt64
      max_excerpt : UInt64
      verified_claims : UInt64
      prev_verified : UInt64

    def SelftestDigestPinInv (s : SelftestPinState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.excerpt_bytes) (UInt64.toNat s.max_excerpt))
        (Nat.le (UInt64.toNat s.prev_verified) (UInt64.toNat s.verified_claims))

    def Init (max_excerpt : UInt64) (s : SelftestPinState) : Prop :=
      And
        (And (s.excerpt_bytes = 0) (s.max_excerpt = max_excerpt))
        (And (s.verified_claims = 0) (s.prev_verified = 0))

    def verifyPinStep (cand_excerpt : UInt64) (cand_verified : UInt64) (s : SelftestPinState) : SelftestPinState :=
      SelftestPinState.mk
        (_root_.pin_excerpt_clamp cand_excerpt s.max_excerpt)
        s.max_excerpt
        (_root_.pin_verified_advance s.verified_claims cand_verified)
        s.verified_claims

    def Next (s : SelftestPinState) (s' : SelftestPinState) : Prop :=
      ∃ (cand_excerpt : UInt64), ∃ (cand_verified : UInt64),
        s' = verifyPinStep cand_excerpt cand_verified s

    def Spec (max_excerpt : UInt64) : StateMachine SelftestPinState :=
      StateMachine.mk (Init max_excerpt) Next

    theorem excerpt_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.pin_excerpt_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem verified_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.pin_verified_advance cur cand)) :=
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

    theorem init_establishes_inv (max_excerpt : UInt64) (s : SelftestPinState)
      (hInit : Init max_excerpt s) :
      SelftestDigestPinInv s :=
      And.intro
        (eq_zero_le s.excerpt_bytes s.max_excerpt (And.left (And.left hInit)))
        (eq_zero_le s.prev_verified s.verified_claims (And.right (And.right hInit)))

    theorem next_preserves_inv (s : SelftestPinState) (s' : SelftestPinState)
      (_hInv : SelftestDigestPinInv s) (hNext : Next s s') :
      SelftestDigestPinInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (cv : UInt64), s' = verifyPinStep ce cv s) =>
        Exists.elim hRest (fun (cv : UInt64) (hEq : s' = verifyPinStep ce cv s) =>
          Eq.mpr
            (congrArg (fun (st : SelftestPinState) => SelftestDigestPinInv st) hEq)
            (And.intro
              (excerpt_clamp_le ce s.max_excerpt)
              (verified_monotone s.verified_claims cv))))

    theorem selftest_digest_pin_safety_always (max_excerpt : UInt64) :
      Satisfies (Runs (Spec max_excerpt)) (Always (Lift SelftestDigestPinInv)) :=
      invariantSatisfies (Spec max_excerpt) SelftestDigestPinInv (init_establishes_inv max_excerpt) next_preserves_inv

    end TlaSelftestDigestPin
    end Evidence
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def pin_excerpt_within_cap_isl (excerpt_len : UInt64) (max_excerpt : UInt64) : Bool :=
      decide (excerpt_len <= max_excerpt)
}
