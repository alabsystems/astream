// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `alt_screen.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `alt_screen.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def alt_cursor_row_clamp (saved_row : UInt64) (max_row : UInt64) : UInt64 :=
      if saved_row < max_row then saved_row else max_row

    def alt_cursor_col_clamp (saved_col : UInt64) (max_col : UInt64) : UInt64 :=
      if saved_col < max_col then saved_col else max_col

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & DEC ?1049 Alt-Screen Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaAltScreenGuard

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

    structure AltScreenState where
      restored_row : UInt64
      max_row : UInt64
      restored_col : UInt64
      max_col : UInt64

    def AltScreenInv (s : AltScreenState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.restored_row) (UInt64.toNat s.max_row))
        (Nat.le (UInt64.toNat s.restored_col) (UInt64.toNat s.max_col))

    def Init (s : AltScreenState) : Prop :=
      And (s.restored_row = 0) (s.restored_col = 0)

    def altStep (raw_row : UInt64) (raw_col : UInt64) (s : AltScreenState) : AltScreenState :=
      AltScreenState.mk
        (_root_.alt_cursor_row_clamp raw_row s.max_row)
        s.max_row
        (_root_.alt_cursor_col_clamp raw_col s.max_col)
        s.max_col

    def Next (s : AltScreenState) (s' : AltScreenState) : Prop :=
      ∃ (raw_row : UInt64), ∃ (raw_col : UInt64),
        s' = altStep raw_row raw_col s

    def Spec : StateMachine AltScreenState :=
      StateMachine.mk Init Next

    theorem row_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.alt_cursor_row_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem col_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.alt_cursor_col_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : AltScreenState) (hInit : Init s) :
      AltScreenInv s :=
      And.intro
        (zero_le_cap s.restored_row s.max_row (And.left hInit))
        (zero_le_cap s.restored_col s.max_col (And.right hInit))

    theorem next_preserves_inv (s : AltScreenState) (s' : AltScreenState)
      (_hInv : AltScreenInv s) (hNext : Next s s') :
      AltScreenInv s' :=
      Exists.elim hNext (fun (rr : UInt64) (hRest : ∃ (rc : UInt64), s' = altStep rr rc s) =>
        Exists.elim hRest (fun (rc : UInt64) (hEq : s' = altStep rr rc s) =>
          Eq.mpr
            (congrArg (fun (st : AltScreenState) => AltScreenInv st) hEq)
            (And.intro
              (row_le_max rr s.max_row)
              (col_le_max rc s.max_col))))

    theorem alt_screen_safety_always :
      Satisfies (Runs Spec) (Always (Lift AltScreenInv)) :=
      invariantSatisfies Spec AltScreenInv init_establishes_inv next_preserves_inv

    end TlaAltScreenGuard
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def alt_needs_teardown_isl (in_alt_screen : Bool) (child_exited : Bool) : Bool :=
      and in_alt_screen child_exited
}
