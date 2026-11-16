// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `hyperlink.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `hyperlink.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def osc8_uri_clamp (uri_len : UInt64) (max_uri : UInt64) : UInt64 :=
      if uri_len < max_uri then uri_len else max_uri

    def osc8_id_clamp (id_len : UInt64) (max_id : UInt64) : UInt64 :=
      if id_len < max_id then id_len else max_id

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & OSC 8 Hyperlink Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaOscHyperlink

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

    structure Osc8State where
      uri_len : UInt64
      max_uri : UInt64
      id_len : UInt64
      max_id : UInt64

    def Osc8BoundsInv (s : Osc8State) : Prop :=
      And
        (Nat.le (UInt64.toNat s.uri_len) (UInt64.toNat s.max_uri))
        (Nat.le (UInt64.toNat s.id_len) (UInt64.toNat s.max_id))

    def Init (s : Osc8State) : Prop :=
      And
        (s.uri_len = 0)
        (s.id_len = 0)

    def setLinkStep (raw_uri : UInt64) (raw_id : UInt64) (s : Osc8State) : Osc8State :=
      Osc8State.mk
        (_root_.osc8_uri_clamp raw_uri s.max_uri)
        s.max_uri
        (_root_.osc8_id_clamp raw_id s.max_id)
        s.max_id

    def Next (s : Osc8State) (s' : Osc8State) : Prop :=
      ∃ (raw_uri : UInt64), ∃ (raw_id : UInt64),
        s' = setLinkStep raw_uri raw_id s

    def Spec : StateMachine Osc8State :=
      StateMachine.mk Init Next

    theorem uri_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc8_uri_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem id_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc8_id_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : Osc8State) (hInit : Init s) :
      Osc8BoundsInv s :=
      And.intro
        (zero_le_cap s.uri_len s.max_uri (And.left hInit))
        (zero_le_cap s.id_len s.max_id (And.right hInit))

    theorem next_preserves_inv (s : Osc8State) (s' : Osc8State)
      (_hInv : Osc8BoundsInv s) (hNext : Next s s') :
      Osc8BoundsInv s' :=
      Exists.elim hNext (fun (raw_uri : UInt64) (hRest : ∃ (raw_id : UInt64), s' = setLinkStep raw_uri raw_id s) =>
        Exists.elim hRest (fun (raw_id : UInt64) (hEq : s' = setLinkStep raw_uri raw_id s) =>
          Eq.mpr
            (congrArg (fun (st : Osc8State) => Osc8BoundsInv st) hEq)
            (And.intro
              (uri_le_max raw_uri s.max_uri)
              (id_le_max raw_id s.max_id))))

    theorem osc8_bounds_always :
      Satisfies (Runs Spec) (Always (Lift Osc8BoundsInv)) :=
      invariantSatisfies Spec Osc8BoundsInv init_establishes_inv next_preserves_inv

    end TlaOscHyperlink
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def osc8_within_cap_isl (len : USize) (cap : USize) : Bool :=
      decide (len ≤ cap)
}
