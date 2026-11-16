// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for WAN/TCP keepalive scheduling and half-open connection deadline
// enforcement (`Astream.Wire.TlaKeepaliveDeadline`), mounted under `cfg(clean_islands)` in
// `keepalive_probe_budget.rs`. Proves `pingIntervalMs <= deadlineMs` and
// `unansweredPings <= maxMissedPings`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def keepalive_interval_clamp (interval_ms : UInt64) (deadline_ms : UInt64) : UInt64 :=
      if interval_ms < deadline_ms then interval_ms else deadline_ms

    def keepalive_missed_clamp (missed : UInt64) (max_missed : UInt64) : UInt64 :=
      if missed < max_missed then missed else max_missed

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaKeepaliveDeadline)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaKeepaliveDeadline

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Wire.TlaKeepaliveDeadline.Satisfies M F
    prefix:75 "□" => _root_.Astream.Wire.TlaKeepaliveDeadline.Always

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

    -- ========================================================================
    -- 3. WAN Keepalive Interval & Half-Open Deadline State Machine
    -- ========================================================================

    structure KeepaliveState where
      pingIntervalMs  : UInt64
      deadlineMs      : UInt64
      unansweredPings : UInt64
      maxMissedPings  : UInt64

    def KeepaliveInv (s : KeepaliveState) : Prop :=
      Nat.le (UInt64.toNat s.pingIntervalMs) (UInt64.toNat s.deadlineMs) ∧
      Nat.le (UInt64.toNat s.unansweredPings) (UInt64.toNat s.maxMissedPings)

    def Init (deadlineMs maxMissedPings : UInt64) (s : KeepaliveState) : Prop :=
      s.pingIntervalMs = (0 : UInt64) ∧
      s.deadlineMs = deadlineMs ∧
      s.unansweredPings = (0 : UInt64) ∧
      s.maxMissedPings = maxMissedPings

    def StepKeepalive (candInterval candMissed : UInt64) (s sNext : KeepaliveState) : Prop :=
      sNext.pingIntervalMs = _root_.keepalive_interval_clamp candInterval s.deadlineMs ∧
      sNext.deadlineMs = s.deadlineMs ∧
      sNext.unansweredPings = _root_.keepalive_missed_clamp candMissed s.maxMissedPings ∧
      sNext.maxMissedPings = s.maxMissedPings

    def Next (s sNext : KeepaliveState) : Prop :=
      ∃ ci : UInt64, ∃ cm : UInt64, StepKeepalive ci cm s sNext

    def Spec (deadlineMs maxMissedPings : UInt64) : StateMachine KeepaliveState :=
      StateMachine.mk (Init deadlineMs maxMissedPings) Next

    theorem int_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.keepalive_interval_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem missed_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.keepalive_missed_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (deadlineMs maxMissedPings : UInt64) (s : KeepaliveState)
        (hInit : Init deadlineMs maxMissedPings s) : KeepaliveInv s :=
      And.intro
        (zero_u64_le s.pingIntervalMs s.deadlineMs hInit.1)
        (zero_u64_le s.unansweredPings s.maxMissedPings hInit.2.2.1)

    theorem stepKeepalive_preserves_inv (ci cm : UInt64) (s sNext : KeepaliveState)
        (hAct : StepKeepalive ci cm s sNext) : KeepaliveInv sNext :=
      let hI1 : Nat.le (UInt64.toNat sNext.pingIntervalMs) (UInt64.toNat s.deadlineMs) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.deadlineMs)) hAct.1)
          (int_clamp_le ci s.deadlineMs)
      let hI2 : Nat.le (UInt64.toNat sNext.pingIntervalMs) (UInt64.toNat sNext.deadlineMs) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.pingIntervalMs) (UInt64.toNat y)) hAct.2.1)
          hI1
      let hM1 : Nat.le (UInt64.toNat sNext.unansweredPings) (UInt64.toNat s.maxMissedPings) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxMissedPings)) hAct.2.2.1)
          (missed_clamp_le cm s.maxMissedPings)
      let hM2 : Nat.le (UInt64.toNat sNext.unansweredPings) (UInt64.toNat sNext.maxMissedPings) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.unansweredPings) (UInt64.toNat y)) hAct.2.2.2)
          hM1
      And.intro hI2 hM2

    theorem next_preserves_inv (s sNext : KeepaliveState)
        (_hInv : KeepaliveInv s) (hNext : Next s sNext) : KeepaliveInv sNext :=
      Exists.elim hNext (fun ci hEx2 =>
        Exists.elim hEx2 (fun cm hAct => stepKeepalive_preserves_inv ci cm s sNext hAct))

    theorem spec_satisfies_keepalive_deadline_safety (deadlineMs maxMissedPings : UInt64) :
        (Spec deadlineMs maxMissedPings) ⊨ □ (Lift KeepaliveInv) :=
      invariantSatisfies (Spec deadlineMs maxMissedPings) KeepaliveInv
        (init_establishes_inv deadlineMs maxMissedPings)
        next_preserves_inv

    end TlaKeepaliveDeadline
    end Wire
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def keepalive_peer_expired_isl (idle_ms : UInt64) (deadline_ms : UInt64) : Bool :=
      decide (deadline_ms ≤ idle_ms)
}
