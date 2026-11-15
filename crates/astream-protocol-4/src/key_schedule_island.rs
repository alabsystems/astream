// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `key_schedule.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `key_schedule.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def hkdf_okm_clamp (req_len : UInt64) (max_okm : UInt64) : UInt64 :=
      if req_len < max_okm then req_len else max_okm

    def hkdf_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & HKDF Key-Schedule Spec
    -- =======================================================================

    namespace Astream
    namespace Digest
    namespace TlaHkdfKeySchedule

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

    structure KeyScheduleState where
      epoch : UInt64
      prev_epoch : UInt64
      okm_len : UInt64
      max_okm : UInt64

    def KeyScheduleInv (s : KeyScheduleState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.epoch))
        (Nat.le (UInt64.toNat s.okm_len) (UInt64.toNat s.max_okm))

    def Init (s : KeyScheduleState) : Prop :=
      And
        (s.okm_len = 0)
        (And (s.epoch = 0) (s.prev_epoch = 0))

    def deriveStep (cand_epoch : UInt64) (req_len : UInt64) (s : KeyScheduleState) : KeyScheduleState :=
      KeyScheduleState.mk
        (_root_.hkdf_epoch_advance s.epoch cand_epoch)
        s.epoch
        (_root_.hkdf_okm_clamp req_len s.max_okm)
        s.max_okm

    def Next (s : KeyScheduleState) (s' : KeyScheduleState) : Prop :=
      ∃ (cand_epoch : UInt64), ∃ (req_len : UInt64),
        s' = deriveStep cand_epoch req_len s

    def Spec : StateMachine KeyScheduleState :=
      StateMachine.mk Init Next

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.hkdf_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem okm_le_max : forall (req : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.hkdf_okm_clamp req cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : KeyScheduleState) (hInit : Init s) :
      KeyScheduleInv s :=
      And.intro
        (eq_zero_le
          s.prev_epoch
          s.epoch
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.okm_len s.max_okm (And.left hInit))

    theorem next_preserves_inv (s : KeyScheduleState) (s' : KeyScheduleState)
      (_hInv : KeyScheduleInv s) (hNext : Next s s') :
      KeyScheduleInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (rl : UInt64), s' = deriveStep ce rl s) =>
        Exists.elim hRest (fun (rl : UInt64) (hEq : s' = deriveStep ce rl s) =>
          Eq.mpr
            (congrArg (fun (st : KeyScheduleState) => KeyScheduleInv st) hEq)
            (And.intro
              (epoch_monotone s.epoch ce)
              (okm_le_max rl s.max_okm))))

    theorem hkdf_schedule_safety_always :
      Satisfies (Runs Spec) (Always (Lift KeyScheduleInv)) :=
      invariantSatisfies Spec KeyScheduleInv init_establishes_inv next_preserves_inv

    end TlaHkdfKeySchedule
    end Digest
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def hkdf_len_valid_isl (okm_len : UInt64) (max_okm : UInt64) : Bool :=
      decide (okm_len ≤ max_okm)
}
