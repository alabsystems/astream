// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `replicated_quorum_ack.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `replicated_quorum_ack.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def quorum_followers_clamp (req_followers : UInt64) (total_followers : UInt64) : UInt64 :=
      if req_followers < total_followers then req_followers else total_followers

    def quorum_hw_advance (cur_qhw : UInt64) (cand_qhw : UInt64) : UInt64 :=
      if cur_qhw < cand_qhw then cand_qhw else cur_qhw

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Quorum Ack Tracker Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaQuorumAckTracker
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

    structure QuorumAckState where
      needed_followers : UInt64
      total_followers : UInt64
      committed_qhw : UInt64
      prev_qhw : UInt64

    def QuorumAckTrackerInv (s : QuorumAckState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.needed_followers) (UInt64.toNat s.total_followers))
        (Nat.le (UInt64.toNat s.prev_qhw) (UInt64.toNat s.committed_qhw))

    def Init (total_followers : UInt64) (s : QuorumAckState) : Prop :=
      And
        (And (s.needed_followers = 0) (s.total_followers = total_followers))
        (And (s.committed_qhw = 0) (s.prev_qhw = 0))

    def ackStep (req_followers : UInt64) (cand_qhw : UInt64) (s : QuorumAckState) : QuorumAckState :=
      QuorumAckState.mk
        (_root_.quorum_followers_clamp req_followers s.total_followers)
        s.total_followers
        (_root_.quorum_hw_advance s.committed_qhw cand_qhw)
        s.committed_qhw

    def Next (s : QuorumAckState) (s' : QuorumAckState) : Prop :=
      ∃ (req_followers : UInt64), ∃ (cand_qhw : UInt64),
        s' = ackStep req_followers cand_qhw s

    def Spec (total_followers : UInt64) : StateMachine QuorumAckState :=
      StateMachine.mk (Init total_followers) Next

    theorem followers_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.quorum_followers_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem qhw_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.quorum_hw_advance cur cand)) :=
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

    theorem init_establishes_inv (total_followers : UInt64) (s : QuorumAckState)
      (hInit : Init total_followers s) :
      QuorumAckTrackerInv s :=
      And.intro
        (eq_zero_le s.needed_followers s.total_followers (And.left (And.left hInit)))
        (eq_zero_le s.prev_qhw s.committed_qhw (And.right (And.right hInit)))

    theorem next_preserves_inv (s : QuorumAckState) (s' : QuorumAckState)
      (_hInv : QuorumAckTrackerInv s) (hNext : Next s s') :
      QuorumAckTrackerInv s' :=
      Exists.elim hNext (fun (rf : UInt64) (hRest : ∃ (cq : UInt64), s' = ackStep rf cq s) =>
        Exists.elim hRest (fun (cq : UInt64) (hEq : s' = ackStep rf cq s) =>
          Eq.mpr
            (congrArg (fun (st : QuorumAckState) => QuorumAckTrackerInv st) hEq)
            (And.intro
              (followers_clamp_le rf s.total_followers)
              (qhw_monotone s.committed_qhw cq))))

    theorem quorum_ack_tracker_safety_always (total_followers : UInt64) :
      Satisfies (Spec total_followers) (Always (Lift QuorumAckTrackerInv)) :=
      invariantSatisfies (Spec total_followers) QuorumAckTrackerInv (init_establishes_inv total_followers) next_preserves_inv

    end TlaQuorumAckTracker
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def quorum_followers_within_total_isl (needed : UInt64) (total : UInt64) : Bool :=
      decide (needed <= total)
}
