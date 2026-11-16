// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `agy_quota_rotator.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `agy_quota_rotator.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def agy_rotator_bps_clamp (cand_bps : UInt64) (max_bps : UInt64) : UInt64 :=
      if cand_bps < max_bps then cand_bps else max_bps

    def rotation_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Quota Pool Rotator Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaQuotaPoolRotator

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

    structure QuotaRotatorState where
      effective_bps : UInt64
      max_bps : UInt64
      rotation_epoch : UInt64
      prev_epoch : UInt64

    def QuotaRotatorInv (s : QuotaRotatorState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.effective_bps) (UInt64.toNat s.max_bps))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.rotation_epoch))

    def Init (max_bps : UInt64) (s : QuotaRotatorState) : Prop :=
      And
        (And (s.effective_bps = 0) (s.max_bps = max_bps))
        (And (s.rotation_epoch = 0) (s.prev_epoch = 0))

    def rotatorStep (cand_bps : UInt64) (cand_epoch : UInt64) (s : QuotaRotatorState) : QuotaRotatorState :=
      QuotaRotatorState.mk
        (_root_.agy_rotator_bps_clamp cand_bps s.max_bps)
        s.max_bps
        (_root_.rotation_epoch_advance s.rotation_epoch cand_epoch)
        s.rotation_epoch

    def Next (s : QuotaRotatorState) (s' : QuotaRotatorState) : Prop :=
      ∃ (cand_bps : UInt64), ∃ (cand_epoch : UInt64),
        s' = rotatorStep cand_bps cand_epoch s

    def Spec (max_bps : UInt64) : StateMachine QuotaRotatorState :=
      StateMachine.mk (Init max_bps) Next

    theorem bps_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.agy_rotator_bps_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem rot_epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.rotation_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_bps : UInt64) (s : QuotaRotatorState)
      (hInit : Init max_bps s) :
      QuotaRotatorInv s :=
      And.intro
        (eq_zero_le s.effective_bps s.max_bps (And.left (And.left hInit)))
        (eq_zero_le s.prev_epoch s.rotation_epoch (And.right (And.right hInit)))

    theorem next_preserves_inv (s : QuotaRotatorState) (s' : QuotaRotatorState)
      (_hInv : QuotaRotatorInv s) (hNext : Next s s') :
      QuotaRotatorInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (ce : UInt64), s' = rotatorStep cb ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = rotatorStep cb ce s) =>
          Eq.mpr
            (congrArg (fun (st : QuotaRotatorState) => QuotaRotatorInv st) hEq)
            (And.intro
              (bps_clamp_le cb s.max_bps)
              (rot_epoch_monotone s.rotation_epoch ce))))

    theorem quota_rotator_safety_always (max_bps : UInt64) :
      Satisfies (Runs (Spec max_bps)) (Always (Lift QuotaRotatorInv)) :=
      invariantSatisfies (Spec max_bps) QuotaRotatorInv (init_establishes_inv max_bps) next_preserves_inv

    end TlaQuotaPoolRotator
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def quota_bps_within_max_isl (bps : UInt64) (max_bps : UInt64) : Bool :=
      decide (bps <= max_bps)
}
