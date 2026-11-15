// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `tail_credit.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `tail_credit.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def tail_inflight_clamp (inflight : UInt64) (max_credit : UInt64) : UInt64 :=
      if inflight < max_credit then inflight else max_credit

    def tail_pending_hw_advance (prev_hw : UInt64) (cand_hw : UInt64) : UInt64 :=
      if prev_hw < cand_hw then cand_hw else prev_hw

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Tail Credit Scheduler Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaTailCreditScheduler

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

    structure TailCreditState where
      inflight : UInt64
      max_credit : UInt64
      pending_hw : UInt64
      prev_hw : UInt64

    def TailCreditInv (s : TailCreditState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.inflight) (UInt64.toNat s.max_credit))
        (Nat.le (UInt64.toNat s.prev_hw) (UInt64.toNat s.pending_hw))

    def Init (s : TailCreditState) : Prop :=
      And
        (s.inflight = 0)
        (And (s.pending_hw = 0) (s.prev_hw = 0))

    def tailCreditStep (raw_if : UInt64) (cand_hw : UInt64) (s : TailCreditState) : TailCreditState :=
      TailCreditState.mk
        (_root_.tail_inflight_clamp raw_if s.max_credit)
        s.max_credit
        (_root_.tail_pending_hw_advance s.pending_hw cand_hw)
        s.pending_hw

    def Next (s : TailCreditState) (s' : TailCreditState) : Prop :=
      ∃ (raw_if : UInt64), ∃ (cand_hw : UInt64),
        s' = tailCreditStep raw_if cand_hw s

    def Spec : StateMachine TailCreditState :=
      StateMachine.mk Init Next

    theorem inflight_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.tail_inflight_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem hw_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.tail_pending_hw_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
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

    theorem init_establishes_inv (s : TailCreditState) (hInit : Init s) :
      TailCreditInv s :=
      And.intro
        (zero_le_cap s.inflight s.max_credit (And.left hInit))
        (eq_zero_le
          s.prev_hw
          s.pending_hw
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : TailCreditState) (s' : TailCreditState)
      (_hInv : TailCreditInv s) (hNext : Next s s') :
      TailCreditInv s' :=
      Exists.elim hNext (fun (ri : UInt64) (hRest : ∃ (ch : UInt64), s' = tailCreditStep ri ch s) =>
        Exists.elim hRest (fun (ch : UInt64) (hEq : s' = tailCreditStep ri ch s) =>
          Eq.mpr
            (congrArg (fun (st : TailCreditState) => TailCreditInv st) hEq)
            (And.intro
              (inflight_le_max ri s.max_credit)
              (hw_monotone s.pending_hw ch))))

    theorem tail_credit_safety_always :
      Satisfies Spec (Always (Lift TailCreditInv)) :=
      invariantSatisfies Spec TailCreditInv init_establishes_inv next_preserves_inv

    end TlaTailCreditScheduler
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def tail_can_dispatch_isl (inflight : UInt64) (max_credit : UInt64) (cursor : UInt64) (hw : UInt64) : Bool :=
      and (decide (inflight < max_credit)) (decide (cursor < hw))
}
