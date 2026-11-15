// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `broker.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `broker.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def broker_batch_clamp (queued : UInt64) (max_batch : UInt64) : UInt64 :=
      if queued < max_batch then queued else max_batch

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaBrokerRuntime)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaBrokerRuntime

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaBrokerRuntime.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaBrokerRuntime.Always

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
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure BrokerBatchState where
      batchLen : UInt64
      maxBatch : UInt64

    def BrokerBatchBoundedInv (s : BrokerBatchState) : Prop :=
      Nat.le (UInt64.toNat s.batchLen) (UInt64.toNat s.maxBatch)

    def Init (s : BrokerBatchState) : Prop :=
      s.batchLen = 0 ∧ s.maxBatch = 4096

    def drainQueueAction (queued : UInt64) (s sNext : BrokerBatchState) : Prop :=
      sNext.maxBatch = s.maxBatch ∧
      sNext.batchLen = _root_.broker_batch_clamp queued s.maxBatch

    def Next (s sNext : BrokerBatchState) : Prop :=
      ∃ queued : UInt64, drainQueueAction queued s sNext

    def Spec : StateMachine BrokerBatchState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (queued : UInt64) (max_batch : UInt64),
        Nat.le (UInt64.toNat (_root_.broker_batch_clamp queued max_batch)) (UInt64.toNat max_batch) :=
      fun queued max_batch => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt queued max_batch)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_batch) (fun _ => queued))) (UInt64.toNat max_batch))
        (instDecidableUInt64Lt queued max_batch)
        (fun _ => Nat.le.refl (UInt64.toNat max_batch))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a b : UInt64) (hZero : a = 0) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : BrokerBatchState) (hInit : Init s) :
        BrokerBatchBoundedInv s :=
      uint64_zero_le s.batchLen s.maxBatch hInit.1

    theorem next_preserves_inv (s sNext : BrokerBatchState)
        (_hInv : BrokerBatchBoundedInv s) (hNext : Next s sNext) :
        BrokerBatchBoundedInv sNext :=
      Exists.elim hNext (fun queued hAct =>
        let hClamp : Nat.le (UInt64.toNat (_root_.broker_batch_clamp queued s.maxBatch)) (UInt64.toNat s.maxBatch) :=
          clamp_le_max queued s.maxBatch
        let hEqLen : sNext.batchLen = _root_.broker_batch_clamp queued s.maxBatch := hAct.2
        let hEqMax : sNext.maxBatch = s.maxBatch := hAct.1
        Eq.mpr
          (congrArg (fun (m : UInt64) => Nat.le (UInt64.toNat sNext.batchLen) (UInt64.toNat m)) hEqMax)
          (Eq.mpr
            (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.maxBatch)) hEqLen)
            hClamp))

    theorem spec_satisfies_broker_batch_bounded :
        Spec ⊨ □ (Lift BrokerBatchBoundedInv) :=
      invariantSatisfies Spec BrokerBatchBoundedInv init_establishes_inv next_preserves_inv

    end TlaBrokerRuntime
    end Broker
    end Astream

    def broker_wake_attempts_within_cap_isl (unanswered : UInt32) : Bool :=
      decide (unanswered ≤ 10)
}
