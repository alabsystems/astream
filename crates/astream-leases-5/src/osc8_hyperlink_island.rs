// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for bounded OSC 8 terminal hyperlink interning & URI length clamping
// (`Astream.Term.TlaOsc8Hyperlink`), mounted under `cfg(clean_islands)` in
// `osc8_hyperlink.rs`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def osc8_link_uri_clamp (uri_len : UInt64) (max_uri_len : UInt64) : UInt64 :=
      if uri_len < max_uri_len then uri_len else max_uri_len

    def osc8_link_slot_clamp (slots : UInt64) (max_slots : UInt64) : UInt64 :=
      if slots < max_slots then slots else max_slots

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaOsc8Hyperlink)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaOsc8Hyperlink

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

    theorem uri_clamp_le : forall (u : UInt64) (m : UInt64),
        Nat.le (UInt64.toNat (_root_.osc8_link_uri_clamp u m)) (UInt64.toNat m) :=
      fun u m => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt u m)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => m) (fun _ => u))) (UInt64.toNat m))
        (instDecidableUInt64Lt u m)
        (fun _ => @Nat.le.refl (UInt64.toNat m))
        (fun hLt => Nat.le_of_lt hLt)

    theorem slot_clamp_le : forall (c : UInt64) (m : UInt64),
        Nat.le (UInt64.toNat (_root_.osc8_link_slot_clamp c m)) (UInt64.toNat m) :=
      fun c m => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt c m)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => m) (fun _ => c))) (UInt64.toNat m))
        (instDecidableUInt64Lt c m)
        (fun _ => @Nat.le.refl (UInt64.toNat m))
        (fun hLt => Nat.le_of_lt hLt)

    structure Osc8State where
      uriBytes : UInt64
      maxUri : UInt64
      slots : UInt64
      maxSlots : UInt64

    def Osc8SafetyInv (s : Osc8State) : Prop :=
      And
        (Nat.le (UInt64.toNat s.uriBytes) (UInt64.toNat s.maxUri))
        (Nat.le (UInt64.toNat s.slots) (UInt64.toNat s.maxSlots))

    def Init (s : Osc8State) : Prop :=
      Osc8SafetyInv s

    def internStep (ru : UInt64) (cs : UInt64) (s : Osc8State) : Osc8State :=
      Osc8State.mk
        (_root_.osc8_link_uri_clamp ru s.maxUri)
        s.maxUri
        (_root_.osc8_link_slot_clamp cs s.maxSlots)
        s.maxSlots

    def Next (s : Osc8State) (s' : Osc8State) : Prop :=
      ∃ (ru : UInt64), ∃ (cs : UInt64), s' = internStep ru cs s

    def Spec : StateMachine Osc8State :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : Osc8State) (hInit : Init s) :
      Osc8SafetyInv s :=
      hInit

    theorem next_preserves_inv (s : Osc8State) (s' : Osc8State)
      (_hInv : Osc8SafetyInv s) (hNext : Next s s') :
      Osc8SafetyInv s' :=
      Exists.elim hNext (fun (ru : UInt64) (hRest : ∃ (cs : UInt64), s' = internStep ru cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = internStep ru cs s) =>
          Eq.mpr
            (congrArg (fun (st : Osc8State) => Osc8SafetyInv st) hEq)
            (And.intro
              (uri_clamp_le ru s.maxUri)
              (slot_clamp_le cs s.maxSlots))))

    theorem spec_satisfies_osc8_hyperlink_safety :
      Satisfies (Runs Spec) (Always (Lift Osc8SafetyInv)) :=
      invariantSatisfies Spec Osc8SafetyInv init_establishes_inv next_preserves_inv

    end TlaOsc8Hyperlink
    end Term
    end Astream

    def osc8_link_uri_within_cap_isl (uri_len : USize) (max_len : USize) : Bool :=
      decide (uri_len ≤ max_len)
}
