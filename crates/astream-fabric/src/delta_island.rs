// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `delta.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `delta.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def delta_out_advance (cur_out : UInt64) (next_out : UInt64) : UInt64 :=
      if cur_out < next_out then next_out else cur_out

    def delta_target_clamp (target_len : UInt64) (max_target : UInt64) : UInt64 :=
      if target_len < max_target then target_len else max_target

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Snapshot Delta Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaSnapshotDelta

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

    structure DeltaState where
      prev_out : UInt64
      out_pos : UInt64
      target_len : UInt64
      max_target : UInt64

    def DeltaSafetyInv (s : DeltaState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_out) (UInt64.toNat s.out_pos))
        (Nat.le (UInt64.toNat s.target_len) (UInt64.toNat s.max_target))

    def Init (s : DeltaState) : Prop :=
      And
        (s.prev_out = s.out_pos)
        (Nat.le (UInt64.toNat s.target_len) (UInt64.toNat s.max_target))

    def applyHunkStep (proposed_out : UInt64) (raw_target : UInt64) (s : DeltaState) : DeltaState :=
      DeltaState.mk
        s.out_pos
        (_root_.delta_out_advance s.out_pos proposed_out)
        (_root_.delta_target_clamp raw_target s.max_target)
        s.max_target

    def Next (s : DeltaState) (s' : DeltaState) : Prop :=
      ∃ (proposed_out : UInt64), ∃ (raw_target : UInt64),
        s' = applyHunkStep proposed_out raw_target s

    def Spec : StateMachine DeltaState :=
      StateMachine.mk Init Next

    theorem out_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.delta_out_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem target_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.delta_target_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : DeltaState) (hInit : Init s) :
      DeltaSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_out s.out_pos (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : DeltaState) (s' : DeltaState)
      (_hInv : DeltaSafetyInv s) (hNext : Next s s') :
      DeltaSafetyInv s' :=
      Exists.elim hNext (fun (po : UInt64) (hRest : ∃ (rt : UInt64), s' = applyHunkStep po rt s) =>
        Exists.elim hRest (fun (rt : UInt64) (hEq : s' = applyHunkStep po rt s) =>
          Eq.mpr
            (congrArg (fun (st : DeltaState) => DeltaSafetyInv st) hEq)
            (And.intro
              (out_ge_prev s.out_pos po)
              (target_le_max rt s.max_target))))

    theorem delta_safety_always :
      Satisfies (Runs Spec) (Always (Lift DeltaSafetyInv)) :=
      invariantSatisfies Spec DeltaSafetyInv init_establishes_inv next_preserves_inv

    end TlaSnapshotDelta
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def delta_slice_in_bounds_isl (end_off : USize) (buf_len : USize) : Bool :=
      decide (end_off ≤ buf_len)
}
