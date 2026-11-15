// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `perceive.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `perceive.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def perceive_clamp_take_count (requested : UInt64) (total : UInt64) : UInt64 :=
      if requested < total then requested else total

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaPerceive)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaPerceive

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
    -- 3. Frame Prefix Query Bounds State Machine & Safety Theorem
    -- ========================================================================

    structure FrameQueryState where
      take_count : UInt64
      total_records : UInt64

    def FrameTakeBoundedInv (s : FrameQueryState) : Prop :=
      Nat.le (UInt64.toNat s.take_count) (UInt64.toNat s.total_records)

    def Init (s : FrameQueryState) : Prop :=
      s.take_count = (0 : UInt64)

    def queryFrameAction (requested : UInt64) (total : UInt64) (_s : FrameQueryState) : FrameQueryState :=
      FrameQueryState.mk (_root_.perceive_clamp_take_count requested total) total

    def Next (s : FrameQueryState) (s' : FrameQueryState) : Prop :=
      ∃ (requested : UInt64), ∃ (total : UInt64), s' = queryFrameAction requested total s

    def Spec : StateMachine FrameQueryState :=
      StateMachine.mk Init Next

    theorem clamp_le_total : forall (requested : UInt64) (total : UInt64),
        Nat.le (UInt64.toNat (_root_.perceive_clamp_take_count requested total)) (UInt64.toNat total) :=
      fun requested total => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt requested total)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => total) (fun _ => requested))) (UInt64.toNat total))
        (instDecidableUInt64Lt requested total)
        (fun _ => Nat.le.refl (UInt64.toNat total))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : FrameQueryState) (hInit : Init s) :
      FrameTakeBoundedInv s :=
      uint64_zero_le s.take_count s.total_records hInit

    theorem next_preserves_inv (s : FrameQueryState) (s' : FrameQueryState)
      (_hInv : FrameTakeBoundedInv s) (hNext : Next s s') :
      FrameTakeBoundedInv s' :=
      Exists.elim hNext (fun (requested : UInt64) (hEx : ∃ (total : UInt64), s' = queryFrameAction requested total s) =>
        Exists.elim hEx (fun (total : UInt64) (hEq : s' = queryFrameAction requested total s) =>
          Eq.mpr
            (congrArg (fun (st : FrameQueryState) => FrameTakeBoundedInv st) hEq)
            (clamp_le_total requested total)))

    theorem spec_satisfies_frame_take_bounded :
      Satisfies (Runs Spec) (Always (Lift FrameTakeBoundedInv)) :=
      invariantSatisfies Spec FrameTakeBoundedInv init_establishes_inv next_preserves_inv

    end TlaPerceive
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def perceive_row_in_bounds_isl (row : UInt16) (rows : UInt16) : Bool :=
      decide (row < rows)
}
