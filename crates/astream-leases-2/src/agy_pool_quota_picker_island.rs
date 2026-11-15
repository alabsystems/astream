// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `aterm harness agy pick` multi-pool quota headroom & fallback selection
// (`Astream.Agent.TlaAgyPoolQuotaPicker`, Island #289), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def agy_picker_bp_clamp (quota_bp : UInt64) (max_bp : UInt64) : UInt64 :=
      if quota_bp < max_bp then quota_bp else max_bp

    def agy_picker_headroom_bp (five_hour_bp : UInt64) (weekly_bp : UInt64) : UInt64 :=
      if five_hour_bp < weekly_bp then five_hour_bp else weekly_bp

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Agy Pool Quota Picker Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaAgyPoolQuotaPicker
    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop
    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)
    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      Nat.rec
        (motive := fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun hNext => hStep (b k) (b (Nat.succ k)) ih hNext)
            (fun hStutter => Eq.mpr (congrArg I hStutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        Satisfies M (Always (Lift I)) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure AgyPoolQuotaPickerState where
      val_0 : UInt64
      cap_0 : UInt64
      val_1 : UInt64
      cap_1 : UInt64

    def AgyPoolQuotaPickerInv (s : AgyPoolQuotaPickerState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.val_0) (UInt64.toNat s.cap_0))
        (Nat.le (UInt64.toNat s.val_1) (UInt64.toNat s.cap_1))

    def Init (s : AgyPoolQuotaPickerState) : Prop :=
      And
        (s.val_0 = 0)
        (s.val_1 = 0)

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (s : AgyPoolQuotaPickerState) : AgyPoolQuotaPickerState :=
      AgyPoolQuotaPickerState.mk
        (_root_.agy_picker_bp_clamp c_0 s.cap_0)
        s.cap_0
        (_root_.agy_picker_headroom_bp c_1 s.cap_1)
        s.cap_1

    def Next (s : AgyPoolQuotaPickerState) (s' : AgyPoolQuotaPickerState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64),
        s' = stepTransition c_0 c_1 s

    def Spec : StateMachine AgyPoolQuotaPickerState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.agy_picker_bp_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.agy_picker_headroom_bp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : AgyPoolQuotaPickerState) (hInit : Init s) :
      AgyPoolQuotaPickerInv s :=
      And.intro
        (zero_le_u64 s.val_0 s.cap_0 (And.left hInit))
        (zero_le_u64 s.val_1 s.cap_1 (And.right hInit))

    theorem next_preserves_inv (s : AgyPoolQuotaPickerState) (s' : AgyPoolQuotaPickerState)
      (_hInv : AgyPoolQuotaPickerInv s) (hNext : Next s s') :
      AgyPoolQuotaPickerInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hRest : ∃ (c_1 : UInt64), s' = stepTransition c_0 c_1 s) =>
        Exists.elim hRest (fun (c_1 : UInt64) (hEq : s' = stepTransition c_0 c_1 s) =>
          Eq.mpr
            (congrArg (fun (st : AgyPoolQuotaPickerState) => AgyPoolQuotaPickerInv st) hEq)
            (And.intro
              (helper_bound_0 c_0 s.cap_0)
              (helper_bound_1 c_1 s.cap_1))))

    theorem agy_pool_quota_picker_safety_always :
      Satisfies Spec (Always (Lift AgyPoolQuotaPickerInv)) :=
      invariantSatisfies Spec AgyPoolQuotaPickerInv init_establishes_inv next_preserves_inv

    end TlaAgyPoolQuotaPicker
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- =======================================================================

    def agy_picker_healthy_isl (headroom_bp : UInt64) (low_floor_bp : UInt64) : Bool :=
      decide (low_floor_bp ≤ headroom_bp)
}
