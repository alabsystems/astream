// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `keyed.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `keyed.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def keyed_clamp_cutoff (seen : UInt64) (tape_len : UInt64) : UInt64 :=
      if seen < tape_len then seen else tape_len

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Effects.TlaKeyedView)
    -- ========================================================================
    namespace Astream
    namespace Effects
    namespace TlaKeyedView

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
        M.Init (b 0) ∧ ∀ (k : Nat), M.Next (b k) (b (Nat.add k 1))

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun (b : Behavior State) => P (b 0)

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

    structure LookupState where
      cutoff : UInt64
      tape_len : UInt64

    def KeyedCutoffBoundedInv (s : LookupState) : Prop :=
      Nat.le (UInt64.toNat s.cutoff) (UInt64.toNat s.tape_len)

    def Init (s : LookupState) : Prop :=
      s.cutoff = (0 : UInt64)

    def lookupAction (requested : UInt64) (tape_len : UInt64) (_s : LookupState) : LookupState :=
      LookupState.mk (_root_.keyed_clamp_cutoff requested tape_len) tape_len

    def Next (s : LookupState) (s' : LookupState) : Prop :=
      ∃ (requested : UInt64), ∃ (tape_len : UInt64), s' = lookupAction requested tape_len s

    def Spec : StateMachine LookupState :=
      StateMachine.mk Init Next

    theorem clamp_le_len : forall (requested : UInt64) (tape_len : UInt64),
        Nat.le (UInt64.toNat (_root_.keyed_clamp_cutoff requested tape_len)) (UInt64.toNat tape_len) :=
      fun requested tape_len => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt requested tape_len)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => tape_len) (fun _ => requested))) (UInt64.toNat tape_len))
        (instDecidableUInt64Lt requested tape_len)
        (fun _ => Nat.le.refl (UInt64.toNat tape_len))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : LookupState) (hInit : Init s) :
      KeyedCutoffBoundedInv s :=
      uint64_zero_le s.cutoff s.tape_len hInit

    theorem next_preserves_inv (s : LookupState) (s' : LookupState)
      (_hInv : KeyedCutoffBoundedInv s) (hNext : Next s s') :
      KeyedCutoffBoundedInv s' :=
      Exists.elim hNext (fun (requested : UInt64) (hEx : ∃ (tape_len : UInt64), s' = lookupAction requested tape_len s) =>
        Exists.elim hEx (fun (tape_len : UInt64) (hEq : s' = lookupAction requested tape_len s) =>
          Eq.mpr
            (congrArg (fun (st : LookupState) => KeyedCutoffBoundedInv st) hEq)
            (clamp_le_len requested tape_len)))

    theorem spec_satisfies_keyed_cutoff_bounded :
      Satisfies (Runs Spec) (Always (Lift KeyedCutoffBoundedInv)) :=
      invariantSatisfies Spec KeyedCutoffBoundedInv init_establishes_inv next_preserves_inv

    end TlaKeyedView
    end Effects
    end Astream

    def keyed_hit_within_cutoff_isl (pos : USize) (seen : USize) : Bool :=
      decide (pos < seen)
}
