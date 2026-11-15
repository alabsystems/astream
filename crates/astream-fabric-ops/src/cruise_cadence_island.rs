// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `cruise_cadence.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `cruise_cadence.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def cruise_rung_clamp (rung : UInt64) (max_rung : UInt64) : UInt64 :=
      if rung < max_rung then rung else max_rung

    def cruise_no_work_clamp (streak : UInt64) (max_streak : UInt64) : UInt64 :=
      if streak < max_streak then streak else max_streak

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Autopilot Cruise Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaCruiseCadence

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

    structure CruiseCadenceState where
      rung_idx : UInt64
      max_rung : UInt64
      no_work_streak : UInt64
      max_streak : UInt64

    def CruiseCadenceInv (s : CruiseCadenceState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.rung_idx) (UInt64.toNat s.max_rung))
        (Nat.le (UInt64.toNat s.no_work_streak) (UInt64.toNat s.max_streak))

    def Init (s : CruiseCadenceState) : Prop :=
      And
        (s.rung_idx = 0)
        (s.no_work_streak = 0)

    def cadenceStep (raw_rung : UInt64) (raw_streak : UInt64) (s : CruiseCadenceState) : CruiseCadenceState :=
      CruiseCadenceState.mk
        (_root_.cruise_rung_clamp raw_rung s.max_rung)
        s.max_rung
        (_root_.cruise_no_work_clamp raw_streak s.max_streak)
        s.max_streak

    def Next (s : CruiseCadenceState) (s' : CruiseCadenceState) : Prop :=
      ∃ (raw_rung : UInt64), ∃ (raw_streak : UInt64),
        s' = cadenceStep raw_rung raw_streak s

    def Spec : StateMachine CruiseCadenceState :=
      StateMachine.mk Init Next

    theorem rung_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.cruise_rung_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem streak_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.cruise_no_work_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : CruiseCadenceState) (hInit : Init s) :
      CruiseCadenceInv s :=
      And.intro
        (zero_le_cap s.rung_idx s.max_rung (And.left hInit))
        (zero_le_cap s.no_work_streak s.max_streak (And.right hInit))

    theorem next_preserves_inv (s : CruiseCadenceState) (s' : CruiseCadenceState)
      (_hInv : CruiseCadenceInv s) (hNext : Next s s') :
      CruiseCadenceInv s' :=
      Exists.elim hNext (fun (rr : UInt64) (hRest : ∃ (rs : UInt64), s' = cadenceStep rr rs s) =>
        Exists.elim hRest (fun (rs : UInt64) (hEq : s' = cadenceStep rr rs s) =>
          Eq.mpr
            (congrArg (fun (st : CruiseCadenceState) => CruiseCadenceInv st) hEq)
            (And.intro
              (rung_le_max rr s.max_rung)
              (streak_le_max rs s.max_streak))))

    theorem cruise_cadence_safety_always :
      Satisfies Spec (Always (Lift CruiseCadenceInv)) :=
      invariantSatisfies Spec CruiseCadenceInv init_establishes_inv next_preserves_inv

    end TlaCruiseCadence
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def cruise_should_park_isl (same_reply_twice : Bool) (streak : UInt64) (limit : UInt64) : Bool :=
      or same_reply_twice (decide (limit ≤ streak))
}
