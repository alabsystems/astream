// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `kitty_kbd.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `kitty_kbd.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def kitty_stack_depth_clamp (depth : UInt64) (max_depth : UInt64) : UInt64 :=
      if depth < max_depth then depth else max_depth

    def kitty_flags_mask (raw_flags : UInt64) (allowed_mask : UInt64) : UInt64 :=
      if raw_flags < allowed_mask then raw_flags else allowed_mask

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Kitty Keyboard Stack Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaKittyKeyboard

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

    structure KittyState where
      depth : UInt64
      max_depth : UInt64
      flags : UInt64
      max_flags : UInt64

    def KittyBoundsInv (s : KittyState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.depth) (UInt64.toNat s.max_depth))
        (Nat.le (UInt64.toNat s.flags) (UInt64.toNat s.max_flags))

    def Init (s : KittyState) : Prop :=
      And
        (s.depth = 0)
        (s.flags = 0)

    def updateStackStep (raw_depth : UInt64) (raw_flags : UInt64) (s : KittyState) : KittyState :=
      KittyState.mk
        (_root_.kitty_stack_depth_clamp raw_depth s.max_depth)
        s.max_depth
        (_root_.kitty_flags_mask raw_flags s.max_flags)
        s.max_flags

    def Next (s : KittyState) (s' : KittyState) : Prop :=
      ∃ (raw_depth : UInt64), ∃ (raw_flags : UInt64),
        s' = updateStackStep raw_depth raw_flags s

    def Spec : StateMachine KittyState :=
      StateMachine.mk Init Next

    theorem depth_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kitty_stack_depth_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem flags_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kitty_flags_mask raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : KittyState) (hInit : Init s) :
      KittyBoundsInv s :=
      And.intro
        (zero_le_cap s.depth s.max_depth (And.left hInit))
        (zero_le_cap s.flags s.max_flags (And.right hInit))

    theorem next_preserves_inv (s : KittyState) (s' : KittyState)
      (_hInv : KittyBoundsInv s) (hNext : Next s s') :
      KittyBoundsInv s' :=
      Exists.elim hNext (fun (rd : UInt64) (hRest : ∃ (rf : UInt64), s' = updateStackStep rd rf s) =>
        Exists.elim hRest (fun (rf : UInt64) (hEq : s' = updateStackStep rd rf s) =>
          Eq.mpr
            (congrArg (fun (st : KittyState) => KittyBoundsInv st) hEq)
            (And.intro
              (depth_le_max rd s.max_depth)
              (flags_le_max rf s.max_flags))))

    theorem kitty_bounds_always :
      Satisfies (Runs Spec) (Always (Lift KittyBoundsInv)) :=
      invariantSatisfies Spec KittyBoundsInv init_establishes_inv next_preserves_inv

    end TlaKittyKeyboard
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def kitty_depth_within_cap_isl (depth : USize) (cap : USize) : Bool :=
      decide (depth ≤ cap)
}
