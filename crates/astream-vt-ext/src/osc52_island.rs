// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `osc52.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `osc52.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def osc52_bytes_clamp (decoded_len : UInt64) (max_bytes : UInt64) : UInt64 :=
      if decoded_len < max_bytes then decoded_len else max_bytes

    def osc52_target_mask_clamp (mask : UInt64) (max_mask : UInt64) : UInt64 :=
      if mask < max_mask then mask else max_mask

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & OSC 52 Clipboard Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaClipboardOsc52

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

    structure Osc52State where
      decoded_bytes : UInt64
      max_bytes : UInt64
      target_mask : UInt64
      max_mask : UInt64

    def Osc52Inv (s : Osc52State) : Prop :=
      And
        (Nat.le (UInt64.toNat s.decoded_bytes) (UInt64.toNat s.max_bytes))
        (Nat.le (UInt64.toNat s.target_mask) (UInt64.toNat s.max_mask))

    def Init (s : Osc52State) : Prop :=
      And
        (s.decoded_bytes = 0)
        (s.target_mask = 0)

    def osc52Step (raw_bytes : UInt64) (raw_mask : UInt64) (s : Osc52State) : Osc52State :=
      Osc52State.mk
        (_root_.osc52_bytes_clamp raw_bytes s.max_bytes)
        s.max_bytes
        (_root_.osc52_target_mask_clamp raw_mask s.max_mask)
        s.max_mask

    def Next (s : Osc52State) (s' : Osc52State) : Prop :=
      ∃ (raw_bytes : UInt64), ∃ (raw_mask : UInt64),
        s' = osc52Step raw_bytes raw_mask s

    def Spec : StateMachine Osc52State :=
      StateMachine.mk Init Next

    theorem bytes_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc52_bytes_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem mask_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc52_target_mask_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : Osc52State) (hInit : Init s) :
      Osc52Inv s :=
      And.intro
        (zero_le_cap s.decoded_bytes s.max_bytes (And.left hInit))
        (zero_le_cap s.target_mask s.max_mask (And.right hInit))

    theorem next_preserves_inv (s : Osc52State) (s' : Osc52State)
      (_hInv : Osc52Inv s) (hNext : Next s s') :
      Osc52Inv s' :=
      Exists.elim hNext (fun (rb : UInt64) (hRest : ∃ (rm : UInt64), s' = osc52Step rb rm s) =>
        Exists.elim hRest (fun (rm : UInt64) (hEq : s' = osc52Step rb rm s) =>
          Eq.mpr
            (congrArg (fun (st : Osc52State) => Osc52Inv st) hEq)
            (And.intro
              (bytes_le_max rb s.max_bytes)
              (mask_le_max rm s.max_mask))))

    theorem osc52_safety_always :
      Satisfies (Runs Spec) (Always (Lift Osc52Inv)) :=
      invariantSatisfies Spec Osc52Inv init_establishes_inv next_preserves_inv

    end TlaClipboardOsc52
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def osc52_payload_within_cap_isl (len : USize) (max_len : USize) : Bool :=
      decide (len ≤ max_len)
}
