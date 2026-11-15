// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `ordinary_publish_seq_ceiling_guard.rs`, mounted under `cfg(clean_islands)`.
clean {
    def ordinary_seq_clamp_b127 (candSeq : UInt64) (maxOrdSeq : UInt64) : UInt64 :=
      if candSeq < maxOrdSeq then candSeq else maxOrdSeq

    def ordinary_will_hw_advance_b127 (curHw : UInt64) (candSeq : UInt64) : UInt64 :=
      if curHw < candSeq then candSeq else curHw

    namespace Astream
    namespace Broker
    namespace TlaOrdinaryPublishSeqCeilingGuard
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

    structure OrdinaryPublishSeqCeilingGuardState where
      val_0 : UInt64
      cap_0 : UInt64
      cur_1 : UInt64
      prev_1 : UInt64

    def OrdinaryPublishSeqCeilingGuardInv (s : OrdinaryPublishSeqCeilingGuardState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.val_0) (UInt64.toNat s.cap_0))
        (Nat.le (UInt64.toNat s.prev_1) (UInt64.toNat s.cur_1))

    def Init (s : OrdinaryPublishSeqCeilingGuardState) : Prop :=
      And
        (s.val_0 = 0)
        (s.prev_1 = 0)

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (s : OrdinaryPublishSeqCeilingGuardState) : OrdinaryPublishSeqCeilingGuardState :=
      OrdinaryPublishSeqCeilingGuardState.mk
        (_root_.ordinary_seq_clamp_b127 c_0 s.cap_0)
        s.cap_0
        (_root_.ordinary_will_hw_advance_b127 s.cur_1 c_1)
        s.cur_1

    def Next (s : OrdinaryPublishSeqCeilingGuardState) (s' : OrdinaryPublishSeqCeilingGuardState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64),
        s' = stepTransition c_0 c_1 s

    def Spec : StateMachine OrdinaryPublishSeqCeilingGuardState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.ordinary_seq_clamp_b127 raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.ordinary_will_hw_advance_b127 prev cand)) :=
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

    theorem init_establishes_inv (s : OrdinaryPublishSeqCeilingGuardState) (hInit : Init s) :
      OrdinaryPublishSeqCeilingGuardInv s :=
      And.intro
        (zero_le_u64 s.val_0 s.cap_0 (And.left hInit))
        (zero_le_u64 s.prev_1 s.cur_1 (And.right hInit))

    theorem next_preserves_inv (s : OrdinaryPublishSeqCeilingGuardState) (s' : OrdinaryPublishSeqCeilingGuardState)
      (_hInv : OrdinaryPublishSeqCeilingGuardInv s) (hNext : Next s s') :
      OrdinaryPublishSeqCeilingGuardInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hRest : ∃ (c_1 : UInt64), s' = stepTransition c_0 c_1 s) =>
        Exists.elim hRest (fun (c_1 : UInt64) (hEq : s' = stepTransition c_0 c_1 s) =>
          Eq.mpr
            (congrArg (fun (st : OrdinaryPublishSeqCeilingGuardState) => OrdinaryPublishSeqCeilingGuardInv st) hEq)
            (And.intro
              (helper_bound_0 c_0 s.cap_0)
              (helper_bound_1 s.cur_1 c_1))))

    theorem ordinary_publish_seq_ceiling_guard_safety_always :
      Satisfies Spec (Always (Lift OrdinaryPublishSeqCeilingGuardInv)) :=
      invariantSatisfies Spec OrdinaryPublishSeqCeilingGuardInv init_establishes_inv next_preserves_inv

    end TlaOrdinaryPublishSeqCeilingGuard
    end Broker
    end Astream


    def ordinary_seq_in_lower_half_b127_isl (seq : UInt64) (ackBase : UInt64) : Bool :=
      decide (LT.lt seq ackBase)
}
