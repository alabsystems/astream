// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `render.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `render.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def render_clamp_end_offset (to_off : UInt64) (max_off : UInt64) : UInt64 :=
      if to_off < max_off then to_off else max_off

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaAnimationRange)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaAnimationRange

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
    -- 3. Animation End-Offset Clamping State Machine & Safety Theorem
    -- ========================================================================

    structure AnimState where
      end_off : UInt64
      max_off : UInt64

    def AnimEndBoundedInv (s : AnimState) : Prop :=
      Nat.le (UInt64.toNat s.end_off) (UInt64.toNat s.max_off)

    def Init (s : AnimState) : Prop :=
      s.end_off = (0 : UInt64)

    def scrubAction (to_off : UInt64) (max_off : UInt64) (_s : AnimState) : AnimState :=
      AnimState.mk (_root_.render_clamp_end_offset to_off max_off) max_off

    def Next (s : AnimState) (s' : AnimState) : Prop :=
      ∃ (to_off : UInt64), ∃ (max_off : UInt64), s' = scrubAction to_off max_off s

    def Spec : StateMachine AnimState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (to_off : UInt64) (max_off : UInt64),
        Nat.le (UInt64.toNat (_root_.render_clamp_end_offset to_off max_off)) (UInt64.toNat max_off) :=
      fun to_off max_off => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt to_off max_off)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_off) (fun _ => to_off))) (UInt64.toNat max_off))
        (instDecidableUInt64Lt to_off max_off)
        (fun _ => Nat.le.refl (UInt64.toNat max_off))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : AnimState) (hInit : Init s) :
      AnimEndBoundedInv s :=
      uint64_zero_le s.end_off s.max_off hInit

    theorem next_preserves_inv (s : AnimState) (s' : AnimState)
      (_hInv : AnimEndBoundedInv s) (hNext : Next s s') :
      AnimEndBoundedInv s' :=
      Exists.elim hNext (fun (to_off : UInt64) (hEx : ∃ (max_off : UInt64), s' = scrubAction to_off max_off s) =>
        Exists.elim hEx (fun (max_off : UInt64) (hEq : s' = scrubAction to_off max_off s) =>
          Eq.mpr
            (congrArg (fun (st : AnimState) => AnimEndBoundedInv st) hEq)
            (clamp_le_max to_off max_off)))

    theorem spec_satisfies_anim_end_bounded :
      Satisfies (Runs Spec) (Always (Lift AnimEndBoundedInv)) :=
      invariantSatisfies Spec AnimEndBoundedInv init_establishes_inv next_preserves_inv

    end TlaAnimationRange
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def render_frame_changed_isl (prev_hash : UInt64) (cur_hash : UInt64) : Bool :=
      decide (prev_hash ≠ cur_hash)
}
