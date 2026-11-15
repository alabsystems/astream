// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `screen.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `screen.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def screen_clamp_dim (dim : UInt64) (max_dim : UInt64) : UInt64 :=
      if dim < max_dim then dim else max_dim

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaScreenDim)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaScreenDim

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (k : Nat) (b : Behavior State) : Behavior State :=
      fun (n : Nat) => b (Nat.add k n)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (k : Nat), P (drop k b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (k : Nat), M.Next (b k) (b (Nat.add k 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (SpecF : Formula State) (PropF : Formula State) : Prop :=
      ∀ (b : Behavior State), SpecF b → PropF b

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

    -- ========================================================================
    -- 3. Screen Grid Dimension Clamping State Machine & Safety Theorem
    -- ========================================================================

    structure GridDimState where
      dim : UInt64
      max_dim : UInt64

    def GridDimBoundedInv (s : GridDimState) : Prop :=
      Nat.le (UInt64.toNat s.dim) (UInt64.toNat s.max_dim)

    def Init (s : GridDimState) : Prop :=
      s.dim = (0 : UInt64)

    def resizeDimAction (requested : UInt64) (max_dim : UInt64) (_s : GridDimState) : GridDimState :=
      GridDimState.mk (_root_.screen_clamp_dim requested max_dim) max_dim

    def Next (s : GridDimState) (s' : GridDimState) : Prop :=
      ∃ (requested : UInt64), ∃ (max_dim : UInt64), s' = resizeDimAction requested max_dim s

    def Spec : StateMachine GridDimState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (requested : UInt64) (max_dim : UInt64),
        Nat.le (UInt64.toNat (_root_.screen_clamp_dim requested max_dim)) (UInt64.toNat max_dim) :=
      fun requested max_dim => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt requested max_dim)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_dim) (fun _ => requested))) (UInt64.toNat max_dim))
        (instDecidableUInt64Lt requested max_dim)
        (fun _ => Nat.le.refl (UInt64.toNat max_dim))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : GridDimState) (hInit : Init s) :
      GridDimBoundedInv s :=
      uint64_zero_le s.dim s.max_dim hInit

    theorem next_preserves_inv (s : GridDimState) (s' : GridDimState)
      (_hInv : GridDimBoundedInv s) (hNext : Next s s') :
      GridDimBoundedInv s' :=
      Exists.elim hNext (fun (requested : UInt64) (hEx : ∃ (max_dim : UInt64), s' = resizeDimAction requested max_dim s) =>
        Exists.elim hEx (fun (max_dim : UInt64) (hEq : s' = resizeDimAction requested max_dim s) =>
          Eq.mpr
            (congrArg (fun (st : GridDimState) => GridDimBoundedInv st) hEq)
            (clamp_le_max requested max_dim)))

    theorem spec_satisfies_grid_dim_bounded :
      Satisfies (Runs Spec) (Always (Lift GridDimBoundedInv)) :=
      invariantSatisfies Spec GridDimBoundedInv init_establishes_inv next_preserves_inv

    end TlaScreenDim
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def screen_coord_in_bounds_isl (coord : UInt16) (dim : UInt16) : Bool :=
      decide (coord < dim)
}
