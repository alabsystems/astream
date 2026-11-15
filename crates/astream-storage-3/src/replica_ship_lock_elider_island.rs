// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `replica_ship_lock_elider.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `replica_ship_lock_elider.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
clean {
    def replica_staged_advance (curStaged : UInt64) (candStaged : UInt64) : UInt64 :=
      if curStaged < candStaged then candStaged else curStaged

    def replica_quorum_clamp (candQuorum : UInt64) (stagedHw : UInt64) : UInt64 :=
      if candQuorum < stagedHw then candQuorum else stagedHw

    namespace Astream
    namespace Broker
    namespace TlaReplicaShipLockElider
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

    structure ReplicaShipLockEliderState where
      cur_0 : UInt64
      prev_0 : UInt64
      val_1 : UInt64
      cap_1 : UInt64

    def ReplicaShipLockEliderInv (s : ReplicaShipLockEliderState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_0) (UInt64.toNat s.cur_0))
        (Nat.le (UInt64.toNat s.val_1) (UInt64.toNat s.cap_1))

    def Init (s : ReplicaShipLockEliderState) : Prop :=
      And
        (s.prev_0 = 0)
        (s.val_1 = 0)

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (s : ReplicaShipLockEliderState) : ReplicaShipLockEliderState :=
      ReplicaShipLockEliderState.mk
        (_root_.replica_staged_advance s.cur_0 c_0)
        s.cur_0
        (_root_.replica_quorum_clamp c_1 s.cap_1)
        s.cap_1

    def Next (s : ReplicaShipLockEliderState) (s' : ReplicaShipLockEliderState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64),
        s' = stepTransition c_0 c_1 s

    def Spec : StateMachine ReplicaShipLockEliderState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.replica_staged_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.replica_quorum_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : ReplicaShipLockEliderState) (hInit : Init s) :
      ReplicaShipLockEliderInv s :=
      And.intro
        (zero_le_u64 s.prev_0 s.cur_0 (And.left hInit))
        (zero_le_u64 s.val_1 s.cap_1 (And.right hInit))

    theorem next_preserves_inv (s : ReplicaShipLockEliderState) (s' : ReplicaShipLockEliderState)
      (_hInv : ReplicaShipLockEliderInv s) (hNext : Next s s') :
      ReplicaShipLockEliderInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hRest : ∃ (c_1 : UInt64), s' = stepTransition c_0 c_1 s) =>
        Exists.elim hRest (fun (c_1 : UInt64) (hEq : s' = stepTransition c_0 c_1 s) =>
          Eq.mpr
            (congrArg (fun (st : ReplicaShipLockEliderState) => ReplicaShipLockEliderInv st) hEq)
            (And.intro
              (helper_bound_0 s.cur_0 c_0)
              (helper_bound_1 c_1 s.cap_1))))

    theorem replica_ship_lock_elider_safety_always :
      Satisfies Spec (Always (Lift ReplicaShipLockEliderInv)) :=
      invariantSatisfies Spec ReplicaShipLockEliderInv init_establishes_inv next_preserves_inv

    end TlaReplicaShipLockElider
    end Broker
    end Astream


    def replica_offset_quorum_durable_isl (targetOffset : UInt64) (quorumAckedHw : UInt64) : Bool :=
      decide (targetOffset < quorumAckedHw)
}
