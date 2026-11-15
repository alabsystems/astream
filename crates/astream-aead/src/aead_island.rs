// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `lib.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `lib.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- =======================================================================

    def aead_clamp_sealed_len (overhead : UInt64) (sealed_len : UInt64) : UInt64 :=
      if overhead < sealed_len then sealed_len else overhead

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Sealed Box Invariant
    -- =======================================================================

    namespace Astream
    namespace Aead
    namespace TlaSealedBox

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

    structure SealedBoxState where
      sealed_len : UInt64
      overhead : UInt64

    def SealedBoxOverheadInv (s : SealedBoxState) : Prop :=
      Nat.le (UInt64.toNat s.overhead) (UInt64.toNat s.sealed_len)

    def Init (s : SealedBoxState) : Prop :=
      s.overhead = s.sealed_len

    def sealAction (proposed_len : UInt64) (s : SealedBoxState) : SealedBoxState :=
      SealedBoxState.mk (_root_.aead_clamp_sealed_len s.overhead proposed_len) s.overhead

    def Next (s : SealedBoxState) (s' : SealedBoxState) : Prop :=
      ∃ (proposed_len : UInt64), s' = sealAction proposed_len s

    def Spec : StateMachine SealedBoxState :=
      StateMachine.mk Init Next

    theorem clamp_ge_overhead : forall (overhead : UInt64) (proposed_len : UInt64),
        Nat.le (UInt64.toNat overhead) (UInt64.toNat (_root_.aead_clamp_sealed_len overhead proposed_len)) :=
      fun overhead proposed_len => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt overhead proposed_len)) =>
          Nat.le (UInt64.toNat overhead) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => overhead) (fun _ => proposed_len))))
        (instDecidableUInt64Lt overhead proposed_len)
        (fun _ => Nat.le.refl (UInt64.toNat overhead))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : SealedBoxState) (hInit : Init s) :
      SealedBoxOverheadInv s :=
      uint64_eq_le s.overhead s.sealed_len hInit

    theorem next_preserves_inv (s : SealedBoxState) (s' : SealedBoxState)
      (_hInv : SealedBoxOverheadInv s) (hNext : Next s s') :
      SealedBoxOverheadInv s' :=
      Exists.elim hNext (fun (proposed_len : UInt64) (hEq : s' = sealAction proposed_len s) =>
        Eq.mpr
          (congrArg (fun (st : SealedBoxState) => SealedBoxOverheadInv st) hEq)
          (clamp_ge_overhead s.overhead proposed_len))

    theorem spec_satisfies_sealed_box_overhead :
      Satisfies (Runs Spec) (Always (Lift SealedBoxOverheadInv)) :=
      invariantSatisfies Spec SealedBoxOverheadInv init_establishes_inv next_preserves_inv

    end TlaSealedBox
    end Aead
    end Astream

    def aead_sealed_has_overhead_isl (sealed_len : USize) (overhead : USize) : Bool :=
      decide (overhead ≤ sealed_len)
}
