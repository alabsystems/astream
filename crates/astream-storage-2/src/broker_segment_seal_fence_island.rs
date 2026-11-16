// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `broker_segment_seal_fence.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `broker_segment_seal_fence.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def seg_hw_advance (curHw : UInt64) (candHw : UInt64) : UInt64 :=
      if curHw < candHw then candHw else curHw
    def seg_watermark_clamp (candMark : UInt64) (ceiling : UInt64) : UInt64 :=
      if candMark < ceiling then candMark else ceiling
    def seg_hot_bytes_clamp (candBytes : UInt64) (maxSegBytes : UInt64) : UInt64 :=
      if candBytes < maxSegBytes then candBytes else maxSegBytes

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Protocol Safety Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaBrokerSegmentSealFence
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

    structure BrokerSegmentSealFenceState where
      cur_0 : UInt64
      prev_0 : UInt64
      val_1 : UInt64
      cap_1 : UInt64
      val_2 : UInt64
      cap_2 : UInt64

    def BrokerSegmentSealFenceInv (s : BrokerSegmentSealFenceState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_0) (UInt64.toNat s.cur_0))
        (And (Nat.le (UInt64.toNat s.val_1) (UInt64.toNat s.cap_1)) (Nat.le (UInt64.toNat s.val_2) (UInt64.toNat s.cap_2)))

    def Init (s : BrokerSegmentSealFenceState) : Prop :=
      And
        (s.prev_0 = 0)
        (And (s.val_1 = 0) (s.val_2 = 0))

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (c_2 : UInt64) (s : BrokerSegmentSealFenceState) : BrokerSegmentSealFenceState :=
      BrokerSegmentSealFenceState.mk
        (_root_.seg_hw_advance s.cur_0 c_0)
        s.cur_0
        (_root_.seg_watermark_clamp c_1 s.cap_1)
        s.cap_1
        (_root_.seg_hot_bytes_clamp c_2 s.cap_2)
        s.cap_2

    def Next (s : BrokerSegmentSealFenceState) (s' : BrokerSegmentSealFenceState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64), ∃ (c_2 : UInt64),
        s' = stepTransition c_0 c_1 c_2 s

    def Spec : StateMachine BrokerSegmentSealFenceState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.seg_hw_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.seg_watermark_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_2 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.seg_hot_bytes_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : BrokerSegmentSealFenceState) (hInit : Init s) :
      BrokerSegmentSealFenceInv s :=
      And.intro
        (zero_le_u64 s.prev_0 s.cur_0 (And.left hInit))
        (And.intro
          (zero_le_u64 s.val_1 s.cap_1 (And.left (And.right hInit)))
          (zero_le_u64 s.val_2 s.cap_2 (And.right (And.right hInit))))

    theorem next_preserves_inv (s : BrokerSegmentSealFenceState) (s' : BrokerSegmentSealFenceState)
      (_hInv : BrokerSegmentSealFenceInv s) (hNext : Next s s') :
      BrokerSegmentSealFenceInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hR1 : ∃ (c_1 : UInt64), ∃ (c_2 : UInt64), s' = stepTransition c_0 c_1 c_2 s) =>
        Exists.elim hR1 (fun (c_1 : UInt64) (hR2 : ∃ (c_2 : UInt64), s' = stepTransition c_0 c_1 c_2 s) =>
          Exists.elim hR2 (fun (c_2 : UInt64) (hEq : s' = stepTransition c_0 c_1 c_2 s) =>
            Eq.mpr
              (congrArg (fun (st : BrokerSegmentSealFenceState) => BrokerSegmentSealFenceInv st) hEq)
              (And.intro
                (helper_bound_0 s.cur_0 c_0)
                (And.intro
                  (helper_bound_1 c_1 s.cap_1)
                  (helper_bound_2 c_2 s.cap_2))))))

    theorem broker_segment_seal_fence_safety_always :
      Satisfies Spec (Always (Lift BrokerSegmentSealFenceInv)) :=
      invariantSatisfies Spec BrokerSegmentSealFenceInv init_establishes_inv next_preserves_inv

    end TlaBrokerSegmentSealFence
    end Broker
    end Astream
}
