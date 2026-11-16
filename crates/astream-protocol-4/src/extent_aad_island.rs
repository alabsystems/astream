// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `extent_aad.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `extent_aad.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def extent_offset_advance (cur_off : UInt64) (cand_off : UInt64) : UInt64 :=
      if cur_off < cand_off then cand_off else cur_off

    def extent_gen_advance (cur_gen : UInt64) (cand_gen : UInt64) : UInt64 :=
      if cur_gen < cand_gen then cand_gen else cur_gen

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & At-Rest Extent AAD Spec
    -- =======================================================================

    namespace Astream
    namespace Aead
    namespace TlaAtRestExtentAad

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

    structure ExtentAadState where
      sealed_off : UInt64
      prev_off : UInt64
      sealed_gen : UInt64
      prev_gen : UInt64

    def ExtentAadInv (s : ExtentAadState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_off) (UInt64.toNat s.sealed_off))
        (Nat.le (UInt64.toNat s.prev_gen) (UInt64.toNat s.sealed_gen))

    def Init (s : ExtentAadState) : Prop :=
      And
        (And (s.sealed_off = 0) (s.prev_off = 0))
        (And (s.sealed_gen = 0) (s.prev_gen = 0))

    def sealExtentStep (cand_off : UInt64) (cand_gen : UInt64) (s : ExtentAadState) : ExtentAadState :=
      ExtentAadState.mk
        (_root_.extent_offset_advance s.sealed_off cand_off)
        s.sealed_off
        (_root_.extent_gen_advance s.sealed_gen cand_gen)
        s.sealed_gen

    def Next (s : ExtentAadState) (s' : ExtentAadState) : Prop :=
      ∃ (cand_off : UInt64), ∃ (cand_gen : UInt64),
        s' = sealExtentStep cand_off cand_gen s

    def Spec : StateMachine ExtentAadState :=
      StateMachine.mk Init Next

    theorem off_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.extent_offset_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem gen_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.extent_gen_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : ExtentAadState) (hInit : Init s) :
      ExtentAadInv s :=
      And.intro
        (eq_zero_le
          s.prev_off
          s.sealed_off
          (And.right (And.left hInit))
          (And.left (And.left hInit)))
        (eq_zero_le
          s.prev_gen
          s.sealed_gen
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : ExtentAadState) (s' : ExtentAadState)
      (_hInv : ExtentAadInv s) (hNext : Next s s') :
      ExtentAadInv s' :=
      Exists.elim hNext (fun (co : UInt64) (hRest : ∃ (cg : UInt64), s' = sealExtentStep co cg s) =>
        Exists.elim hRest (fun (cg : UInt64) (hEq : s' = sealExtentStep co cg s) =>
          Eq.mpr
            (congrArg (fun (st : ExtentAadState) => ExtentAadInv st) hEq)
            (And.intro
              (off_monotone s.sealed_off co)
              (gen_monotone s.sealed_gen cg))))

    theorem extent_aad_safety_always :
      Satisfies (Runs Spec) (Always (Lift ExtentAadInv)) :=
      invariantSatisfies Spec ExtentAadInv init_establishes_inv next_preserves_inv

    end TlaAtRestExtentAad
    end Aead
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def extent_offset_strictly_next_isl (prev_off : UInt64) (cand_off : UInt64) : Bool :=
      decide (prev_off < cand_off)
}
