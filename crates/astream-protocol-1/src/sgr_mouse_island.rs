// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `sgr_mouse.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `sgr_mouse.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def sgr_mouse_coord_clamp (coord_zero : UInt64) (max_zero : UInt64) : UInt64 :=
      if coord_zero < max_zero then coord_zero else max_zero

    def sgr_mouse_coalesce_clamp (batch_count : UInt64) (max_batch : UInt64) : UInt64 :=
      if batch_count < max_batch then batch_count else max_batch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & DEC ?1006 SGR Mouse Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaSgrMouseFocus

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

    structure SgrMouseState where
      col_zero : UInt64
      max_col_zero : UInt64
      coalesced : UInt64
      max_coalesce : UInt64

    def SgrMouseInv (s : SgrMouseState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.col_zero) (UInt64.toNat s.max_col_zero))
        (Nat.le (UInt64.toNat s.coalesced) (UInt64.toNat s.max_coalesce))

    def Init (s : SgrMouseState) : Prop :=
      And (s.col_zero = 0) (s.coalesced = 0)

    def mouseStep (raw_col : UInt64) (raw_batch : UInt64) (s : SgrMouseState) : SgrMouseState :=
      SgrMouseState.mk
        (_root_.sgr_mouse_coord_clamp raw_col s.max_col_zero)
        s.max_col_zero
        (_root_.sgr_mouse_coalesce_clamp raw_batch s.max_coalesce)
        s.max_coalesce

    def Next (s : SgrMouseState) (s' : SgrMouseState) : Prop :=
      ∃ (raw_col : UInt64), ∃ (raw_batch : UInt64),
        s' = mouseStep raw_col raw_batch s

    def Spec : StateMachine SgrMouseState :=
      StateMachine.mk Init Next

    theorem coord_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sgr_mouse_coord_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem coalesce_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sgr_mouse_coalesce_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : SgrMouseState) (hInit : Init s) :
      SgrMouseInv s :=
      And.intro
        (zero_le_cap s.col_zero s.max_col_zero (And.left hInit))
        (zero_le_cap s.coalesced s.max_coalesce (And.right hInit))

    theorem next_preserves_inv (s : SgrMouseState) (s' : SgrMouseState)
      (_hInv : SgrMouseInv s) (hNext : Next s s') :
      SgrMouseInv s' :=
      Exists.elim hNext (fun (rc : UInt64) (hRest : ∃ (rb : UInt64), s' = mouseStep rc rb s) =>
        Exists.elim hRest (fun (rb : UInt64) (hEq : s' = mouseStep rc rb s) =>
          Eq.mpr
            (congrArg (fun (st : SgrMouseState) => SgrMouseInv st) hEq)
            (And.intro
              (coord_le_max rc s.max_col_zero)
              (coalesce_le_max rb s.max_coalesce))))

    theorem sgr_mouse_safety_always :
      Satisfies (Runs Spec) (Always (Lift SgrMouseInv)) :=
      invariantSatisfies Spec SgrMouseInv init_establishes_inv next_preserves_inv

    end TlaSgrMouseFocus
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def sgr_mouse_motion_bit_set_isl (motion_bit : UInt32) : Bool :=
      decide ((0 : UInt32) < motion_bit)
}
