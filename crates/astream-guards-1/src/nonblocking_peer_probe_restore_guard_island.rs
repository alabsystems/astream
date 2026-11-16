// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `nonblocking_peer_probe_restore_guard.rs`, mounted under `cfg(clean_islands)`.
clean {
    def probe_clock_advance_b146 (curMs : UInt64) (candMs : UInt64) : UInt64 :=
      if curMs < candMs then candMs else curMs

    def peer_probes_count_advance_b146 (curProbes : UInt64) (candProbes : UInt64) : UInt64 :=
      if curProbes < candProbes then candProbes else curProbes

    namespace Astream
    namespace Broker
    namespace TlaNonblockingPeerProbeRestoreGuard
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

    structure NonblockingPeerProbeRestoreGuardState where
      cur_0 : UInt64
      prev_0 : UInt64
      cur_1 : UInt64
      prev_1 : UInt64

    def NonblockingPeerProbeRestoreGuardInv (s : NonblockingPeerProbeRestoreGuardState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_0) (UInt64.toNat s.cur_0))
        (Nat.le (UInt64.toNat s.prev_1) (UInt64.toNat s.cur_1))

    def Init (s : NonblockingPeerProbeRestoreGuardState) : Prop :=
      And
        (s.prev_0 = 0)
        (s.prev_1 = 0)

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (s : NonblockingPeerProbeRestoreGuardState) : NonblockingPeerProbeRestoreGuardState :=
      NonblockingPeerProbeRestoreGuardState.mk
        (_root_.probe_clock_advance_b146 s.cur_0 c_0)
        s.cur_0
        (_root_.peer_probes_count_advance_b146 s.cur_1 c_1)
        s.cur_1

    def Next (s : NonblockingPeerProbeRestoreGuardState) (s' : NonblockingPeerProbeRestoreGuardState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64),
        s' = stepTransition c_0 c_1 s

    def Spec : StateMachine NonblockingPeerProbeRestoreGuardState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.probe_clock_advance_b146 prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.peer_probes_count_advance_b146 prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : NonblockingPeerProbeRestoreGuardState) (hInit : Init s) :
      NonblockingPeerProbeRestoreGuardInv s :=
      And.intro
        (zero_le_u64 s.prev_0 s.cur_0 (And.left hInit))
        (zero_le_u64 s.prev_1 s.cur_1 (And.right hInit))

    theorem next_preserves_inv (s : NonblockingPeerProbeRestoreGuardState) (s' : NonblockingPeerProbeRestoreGuardState)
      (_hInv : NonblockingPeerProbeRestoreGuardInv s) (hNext : Next s s') :
      NonblockingPeerProbeRestoreGuardInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hRest : ∃ (c_1 : UInt64), s' = stepTransition c_0 c_1 s) =>
        Exists.elim hRest (fun (c_1 : UInt64) (hEq : s' = stepTransition c_0 c_1 s) =>
          Eq.mpr
            (congrArg (fun (st : NonblockingPeerProbeRestoreGuardState) => NonblockingPeerProbeRestoreGuardInv st) hEq)
            (And.intro
              (helper_bound_0 s.cur_0 c_0)
              (helper_bound_1 s.cur_1 c_1))))

    theorem nonblocking_peer_probe_restore_guard_safety_always :
      Satisfies Spec (Always (Lift NonblockingPeerProbeRestoreGuardInv)) :=
      invariantSatisfies Spec NonblockingPeerProbeRestoreGuardInv init_establishes_inv next_preserves_inv

    end TlaNonblockingPeerProbeRestoreGuard
    end Broker
    end Astream


    def probe_due_and_restored_blocking_b146_isl
      (elapsedSinceLastProbeMs : UInt64)
      (pollIntervalMs : UInt64)
      (restoredBlocking : Bool) : Bool :=
      and (decide (LE.le pollIntervalMs elapsedSinceLastProbeMs)) restoredBlocking
}
