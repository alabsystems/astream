// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `needs_you.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `needs_you.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def needs_you_items_clamp (items : UInt64) (max_items : UInt64) : UInt64 :=
      if items < max_items then items else max_items

    def needs_you_len_clamp (item_len : UInt64) (max_len : UInt64) : UInt64 :=
      if item_len < max_len then item_len else max_len

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & NEEDS YOU Ledger Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaNeedsYouLedger

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

    structure NeedsYouState where
      active_items : UInt64
      max_items : UInt64
      item_len : UInt64
      max_len : UInt64

    def NeedsYouInv (s : NeedsYouState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.active_items) (UInt64.toNat s.max_items))
        (Nat.le (UInt64.toNat s.item_len) (UInt64.toNat s.max_len))

    def Init (s : NeedsYouState) : Prop :=
      And
        (s.active_items = 0)
        (s.item_len = 0)

    def needsYouStep (raw_items : UInt64) (raw_len : UInt64) (s : NeedsYouState) : NeedsYouState :=
      NeedsYouState.mk
        (_root_.needs_you_items_clamp raw_items s.max_items)
        s.max_items
        (_root_.needs_you_len_clamp raw_len s.max_len)
        s.max_len

    def Next (s : NeedsYouState) (s' : NeedsYouState) : Prop :=
      ∃ (raw_items : UInt64), ∃ (raw_len : UInt64),
        s' = needsYouStep raw_items raw_len s

    def Spec : StateMachine NeedsYouState :=
      StateMachine.mk Init Next

    theorem items_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.needs_you_items_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem len_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.needs_you_len_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : NeedsYouState) (hInit : Init s) :
      NeedsYouInv s :=
      And.intro
        (zero_le_cap s.active_items s.max_items (And.left hInit))
        (zero_le_cap s.item_len s.max_len (And.right hInit))

    theorem next_preserves_inv (s : NeedsYouState) (s' : NeedsYouState)
      (_hInv : NeedsYouInv s) (hNext : Next s s') :
      NeedsYouInv s' :=
      Exists.elim hNext (fun (ri : UInt64) (hRest : ∃ (rl : UInt64), s' = needsYouStep ri rl s) =>
        Exists.elim hRest (fun (rl : UInt64) (hEq : s' = needsYouStep ri rl s) =>
          Eq.mpr
            (congrArg (fun (st : NeedsYouState) => NeedsYouInv st) hEq)
            (And.intro
              (items_le_max ri s.max_items)
              (len_le_max rl s.max_len))))

    theorem needs_you_safety_always :
      Satisfies (Runs Spec) (Always (Lift NeedsYouInv)) :=
      invariantSatisfies Spec NeedsYouInv init_establishes_inv next_preserves_inv

    end TlaNeedsYouLedger
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def needs_you_banner_active_isl (active_items : USize) : Bool :=
      decide (0 < active_items)
}
