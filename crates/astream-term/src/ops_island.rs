// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `ops.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `ops.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def op_clamp_scroll_top (top : UInt64) (bottom : UInt64) : UInt64 :=
      if top < bottom then top else bottom

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaScreenOp)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaScreenOp

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
    -- 3. DECSTBM Scroll-Region Bounds State Machine & Safety Theorem
    -- ========================================================================

    structure RegionState where
      top : UInt64
      bottom : UInt64

    def ScrollRegionValidInv (s : RegionState) : Prop :=
      Nat.le (UInt64.toNat s.top) (UInt64.toNat s.bottom)

    def Init (s : RegionState) : Prop :=
      s.top = (0 : UInt64)

    def setRegionAction (top : UInt64) (bottom : UInt64) (_s : RegionState) : RegionState :=
      RegionState.mk (_root_.op_clamp_scroll_top top bottom) bottom

    def Next (s : RegionState) (s' : RegionState) : Prop :=
      ∃ (top : UInt64), ∃ (bottom : UInt64), s' = setRegionAction top bottom s

    def Spec : StateMachine RegionState :=
      StateMachine.mk Init Next

    theorem clamp_le_bottom : forall (top : UInt64) (bottom : UInt64),
        Nat.le (UInt64.toNat (_root_.op_clamp_scroll_top top bottom)) (UInt64.toNat bottom) :=
      fun top bottom => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt top bottom)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => bottom) (fun _ => top))) (UInt64.toNat bottom))
        (instDecidableUInt64Lt top bottom)
        (fun _ => Nat.le.refl (UInt64.toNat bottom))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : RegionState) (hInit : Init s) :
      ScrollRegionValidInv s :=
      uint64_zero_le s.top s.bottom hInit

    theorem next_preserves_inv (s : RegionState) (s' : RegionState)
      (_hInv : ScrollRegionValidInv s) (hNext : Next s s') :
      ScrollRegionValidInv s' :=
      Exists.elim hNext (fun (top : UInt64) (hEx : ∃ (bottom : UInt64), s' = setRegionAction top bottom s) =>
        Exists.elim hEx (fun (bottom : UInt64) (hEq : s' = setRegionAction top bottom s) =>
          Eq.mpr
            (congrArg (fun (st : RegionState) => ScrollRegionValidInv st) hEq)
            (clamp_le_bottom top bottom)))

    theorem spec_satisfies_scroll_region_validity :
      Satisfies (Runs Spec) (Always (Lift ScrollRegionValidInv)) :=
      invariantSatisfies Spec ScrollRegionValidInv init_establishes_inv next_preserves_inv

    end TlaScreenOp
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def op_scroll_region_nonempty_isl (top : UInt16) (bottom : UInt16) : Bool :=
      decide (top ≤ bottom)
}
