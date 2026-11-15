// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `pty_drain_pending_max_backstop.rs`, mounted under `cfg(clean_islands)`.
clean {
    def pending_drain_bytes_clamp_b144 (candBytes : UInt64) (pendingMaxBytes : UInt64) : UInt64 :=
      if candBytes < pendingMaxBytes then candBytes else pendingMaxBytes

    def committed_in_count_advance_b144 (curIns : UInt64) (candIns : UInt64) : UInt64 :=
      if curIns < candIns then candIns else curIns

    namespace Astream
    namespace Host
    namespace TlaPtyDrainPendingMaxBackstop
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

    structure PtyDrainPendingMaxBackstopState where
      val_0 : UInt64
      cap_0 : UInt64
      cur_1 : UInt64
      prev_1 : UInt64

    def PtyDrainPendingMaxBackstopInv (s : PtyDrainPendingMaxBackstopState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.val_0) (UInt64.toNat s.cap_0))
        (Nat.le (UInt64.toNat s.prev_1) (UInt64.toNat s.cur_1))

    def Init (s : PtyDrainPendingMaxBackstopState) : Prop :=
      And
        (s.val_0 = 0)
        (s.prev_1 = 0)

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (s : PtyDrainPendingMaxBackstopState) : PtyDrainPendingMaxBackstopState :=
      PtyDrainPendingMaxBackstopState.mk
        (_root_.pending_drain_bytes_clamp_b144 c_0 s.cap_0)
        s.cap_0
        (_root_.committed_in_count_advance_b144 s.cur_1 c_1)
        s.cur_1

    def Next (s : PtyDrainPendingMaxBackstopState) (s' : PtyDrainPendingMaxBackstopState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64),
        s' = stepTransition c_0 c_1 s

    def Spec : StateMachine PtyDrainPendingMaxBackstopState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.pending_drain_bytes_clamp_b144 raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.committed_in_count_advance_b144 prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : PtyDrainPendingMaxBackstopState) (hInit : Init s) :
      PtyDrainPendingMaxBackstopInv s :=
      And.intro
        (zero_le_u64 s.val_0 s.cap_0 (And.left hInit))
        (zero_le_u64 s.prev_1 s.cur_1 (And.right hInit))

    theorem next_preserves_inv (s : PtyDrainPendingMaxBackstopState) (s' : PtyDrainPendingMaxBackstopState)
      (_hInv : PtyDrainPendingMaxBackstopInv s) (hNext : Next s s') :
      PtyDrainPendingMaxBackstopInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hRest : ∃ (c_1 : UInt64), s' = stepTransition c_0 c_1 s) =>
        Exists.elim hRest (fun (c_1 : UInt64) (hEq : s' = stepTransition c_0 c_1 s) =>
          Eq.mpr
            (congrArg (fun (st : PtyDrainPendingMaxBackstopState) => PtyDrainPendingMaxBackstopInv st) hEq)
            (And.intro
              (helper_bound_0 c_0 s.cap_0)
              (helper_bound_1 s.cur_1 c_1))))

    theorem pty_drain_pending_max_backstop_safety_always :
      Satisfies Spec (Always (Lift PtyDrainPendingMaxBackstopInv)) :=
      invariantSatisfies Spec PtyDrainPendingMaxBackstopInv init_establishes_inv next_preserves_inv

    end TlaPtyDrainPendingMaxBackstop
    end Host
    end Astream


    def pty_proposal_admissible_b144_isl
      (holderValid : Bool)
      (payloadLen : UInt64)
      (maxFramePayload : UInt64)
      (pendingOutBytes : UInt64)
      (pendingMaxBytes : UInt64) : Bool :=
      and holderValid
        (and (decide (LE.le payloadLen maxFramePayload))
          (decide (LT.lt pendingOutBytes pendingMaxBytes)))
}
