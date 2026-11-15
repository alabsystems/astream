// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `key_rotation.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `key_rotation.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def key_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    def key_grace_clamp_ms (req_grace : UInt64) (max_grace : UInt64) : UInt64 :=
      if req_grace < max_grace then req_grace else max_grace

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Key-Rotation Ring Spec
    -- =======================================================================

    namespace Astream
    namespace Cap
    namespace TlaCapKeyRotation

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

    structure KeyRotationState where
      active_epoch : UInt64
      prev_epoch : UInt64
      grace_ms : UInt64
      max_grace_ms : UInt64

    def KeyRotationInv (s : KeyRotationState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.active_epoch))
        (Nat.le (UInt64.toNat s.grace_ms) (UInt64.toNat s.max_grace_ms))

    def Init (s : KeyRotationState) : Prop :=
      And
        (s.grace_ms = 0)
        (And (s.active_epoch = 0) (s.prev_epoch = 0))

    def rotateKeyStep (cand_epoch : UInt64) (req_grace : UInt64) (s : KeyRotationState) : KeyRotationState :=
      KeyRotationState.mk
        (_root_.key_epoch_advance s.active_epoch cand_epoch)
        s.active_epoch
        (_root_.key_grace_clamp_ms req_grace s.max_grace_ms)
        s.max_grace_ms

    def Next (s : KeyRotationState) (s' : KeyRotationState) : Prop :=
      ∃ (cand_epoch : UInt64), ∃ (req_grace : UInt64),
        s' = rotateKeyStep cand_epoch req_grace s

    def Spec : StateMachine KeyRotationState :=
      StateMachine.mk Init Next

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.key_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem grace_le_max : forall (req : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.key_grace_clamp_ms req cap)) (UInt64.toNat cap) :=
      fun req cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt req cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => req))) (UInt64.toNat cap))
        (instDecidableUInt64Lt req cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : KeyRotationState) (hInit : Init s) :
      KeyRotationInv s :=
      And.intro
        (eq_zero_le
          s.prev_epoch
          s.active_epoch
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.grace_ms s.max_grace_ms (And.left hInit))

    theorem next_preserves_inv (s : KeyRotationState) (s' : KeyRotationState)
      (_hInv : KeyRotationInv s) (hNext : Next s s') :
      KeyRotationInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (rg : UInt64), s' = rotateKeyStep ce rg s) =>
        Exists.elim hRest (fun (rg : UInt64) (hEq : s' = rotateKeyStep ce rg s) =>
          Eq.mpr
            (congrArg (fun (st : KeyRotationState) => KeyRotationInv st) hEq)
            (And.intro
              (epoch_monotone s.active_epoch ce)
              (grace_le_max rg s.max_grace_ms))))

    theorem key_rotation_safety_always :
      Satisfies (Runs Spec) (Always (Lift KeyRotationInv)) :=
      invariantSatisfies Spec KeyRotationInv init_establishes_inv next_preserves_inv

    end TlaCapKeyRotation
    end Cap
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def retiring_grace_active_isl (now_ms : UInt64) (retire_at_ms : UInt64) : Bool :=
      decide (now_ms < retire_at_ms)
}
