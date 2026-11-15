// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `backoff.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `backoff.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def backoff_delay_clamp (proposed_ms : UInt64) (max_ms : UInt64) : UInt64 :=
      if proposed_ms < max_ms then proposed_ms else max_ms

    def backoff_attempt_advance (cur_attempt : UInt64) (next_attempt : UInt64) : UInt64 :=
      if cur_attempt < next_attempt then next_attempt else cur_attempt

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Adaptive Backoff Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaAdaptiveBackoff

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

    structure BackoffState where
      prev_attempt : UInt64
      attempt : UInt64
      delay_ms : UInt64
      max_ms : UInt64

    def BackoffSafetyInv (s : BackoffState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_attempt) (UInt64.toNat s.attempt))
        (Nat.le (UInt64.toNat s.delay_ms) (UInt64.toNat s.max_ms))

    def Init (s : BackoffState) : Prop :=
      And
        (s.prev_attempt = s.attempt)
        (Nat.le (UInt64.toNat s.delay_ms) (UInt64.toNat s.max_ms))

    def retryStep (proposed_attempt : UInt64) (raw_delay : UInt64) (s : BackoffState) : BackoffState :=
      BackoffState.mk
        s.attempt
        (_root_.backoff_attempt_advance s.attempt proposed_attempt)
        (_root_.backoff_delay_clamp raw_delay s.max_ms)
        s.max_ms

    def Next (s : BackoffState) (s' : BackoffState) : Prop :=
      ∃ (proposed_attempt : UInt64), ∃ (raw_delay : UInt64),
        s' = retryStep proposed_attempt raw_delay s

    def Spec : StateMachine BackoffState :=
      StateMachine.mk Init Next

    theorem attempt_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.backoff_attempt_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem delay_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.backoff_delay_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : BackoffState) (hInit : Init s) :
      BackoffSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_attempt s.attempt (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : BackoffState) (s' : BackoffState)
      (_hInv : BackoffSafetyInv s) (hNext : Next s s') :
      BackoffSafetyInv s' :=
      Exists.elim hNext (fun (pa : UInt64) (hRest : ∃ (rd : UInt64), s' = retryStep pa rd s) =>
        Exists.elim hRest (fun (rd : UInt64) (hEq : s' = retryStep pa rd s) =>
          Eq.mpr
            (congrArg (fun (st : BackoffState) => BackoffSafetyInv st) hEq)
            (And.intro
              (attempt_ge_prev s.attempt pa)
              (delay_le_max rd s.max_ms))))

    theorem backoff_safety_always :
      Satisfies Spec (Always (Lift BackoffSafetyInv)) :=
      invariantSatisfies Spec BackoffSafetyInv init_establishes_inv next_preserves_inv

    end TlaAdaptiveBackoff
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def backoff_delay_in_range_isl (delay_ms : UInt64) (max_ms : UInt64) : Bool :=
      decide (delay_ms ≤ max_ms)
}
