// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `subscriber_wakeup_coalesce.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `subscriber_wakeup_coalesce.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def sub_wake_backlog_clamp (cand_backlog : UInt64) (batch_target : UInt64) : UInt64 :=
      if cand_backlog < batch_target then cand_backlog else batch_target

    def sub_wake_hw_advance (cur_hw : UInt64) (cand_hw : UInt64) : UInt64 :=
      if cur_hw < cand_hw then cand_hw else cur_hw

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Subscriber Wake Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaSubscriberWakeCoalesce

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

    structure SubWakeState where
      clamped_backlog : UInt64
      batch_target : UInt64
      notified_hw : UInt64
      prev_hw : UInt64

    def SubscriberWakeInv (s : SubWakeState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.clamped_backlog) (UInt64.toNat s.batch_target))
        (Nat.le (UInt64.toNat s.prev_hw) (UInt64.toNat s.notified_hw))

    def Init (batch_target : UInt64) (s : SubWakeState) : Prop :=
      And
        (And (s.clamped_backlog = 0) (s.batch_target = batch_target))
        (And (s.notified_hw = 0) (s.prev_hw = 0))

    def wakeStep (cand_backlog : UInt64) (cand_hw : UInt64) (s : SubWakeState) : SubWakeState :=
      SubWakeState.mk
        (_root_.sub_wake_backlog_clamp cand_backlog s.batch_target)
        s.batch_target
        (_root_.sub_wake_hw_advance s.notified_hw cand_hw)
        s.notified_hw

    def Next (s : SubWakeState) (s' : SubWakeState) : Prop :=
      ∃ (cand_backlog : UInt64), ∃ (cand_hw : UInt64),
        s' = wakeStep cand_backlog cand_hw s

    def Spec (batch_target : UInt64) : StateMachine SubWakeState :=
      StateMachine.mk (Init batch_target) Next

    theorem backlog_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sub_wake_backlog_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem hw_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.sub_wake_hw_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (batch_target : UInt64) (s : SubWakeState)
      (hInit : Init batch_target s) :
      SubscriberWakeInv s :=
      And.intro
        (eq_zero_le s.clamped_backlog s.batch_target (And.left (And.left hInit)))
        (eq_zero_le s.prev_hw s.notified_hw (And.right (And.right hInit)))

    theorem next_preserves_inv (s : SubWakeState) (s' : SubWakeState)
      (_hInv : SubscriberWakeInv s) (hNext : Next s s') :
      SubscriberWakeInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (ch : UInt64), s' = wakeStep cb ch s) =>
        Exists.elim hRest (fun (ch : UInt64) (hEq : s' = wakeStep cb ch s) =>
          Eq.mpr
            (congrArg (fun (st : SubWakeState) => SubscriberWakeInv st) hEq)
            (And.intro
              (backlog_clamp_le cb s.batch_target)
              (hw_monotone s.notified_hw ch))))

    theorem subscriber_wake_coalesce_safety_always (batch_target : UInt64) :
      Satisfies (Spec batch_target) (Always (Lift SubscriberWakeInv)) :=
      invariantSatisfies (Spec batch_target) SubscriberWakeInv (init_establishes_inv batch_target) next_preserves_inv

    end TlaSubscriberWakeCoalesce
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def sub_already_has_unconsumed_wake_isl (acked_cursor : UInt64) (notified_hw : UInt64) : Bool :=
      decide (acked_cursor < notified_hw)
}
