// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for WAN speculative-echo password/mode suppression and unconfirmed
// keystroke bounding (`Astream.Term.TlaMoshPasswordFence`), mounted under
// `cfg(clean_islands)` in `speculative_echo_fence.rs`. Proves
// `unconfirmedKeys <= maxUnconfirmed` and `confirmedEpoch <= issuedEpoch`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def echo_unconfirmed_clamp (proposed_keys : UInt64) (max_keys : UInt64) : UInt64 :=
      if proposed_keys < max_keys then proposed_keys else max_keys

    def echo_epoch_advance (cur_epoch : UInt64) (proposed_epoch : UInt64) : UInt64 :=
      if cur_epoch < proposed_epoch then proposed_epoch else cur_epoch

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaMoshPasswordFence)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaMoshPasswordFence

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaMoshPasswordFence.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaMoshPasswordFence.Always

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
    -- 3. Speculative Echo Password/Mode Fence State Machine
    -- ========================================================================

    structure EchoFenceState where
      unconfirmedKeys : UInt64
      maxUnconfirmed  : UInt64
      confirmedEpoch  : UInt64
      issuedEpoch     : UInt64

    def EchoFenceInv (s : EchoFenceState) : Prop :=
      Nat.le (UInt64.toNat s.unconfirmedKeys) (UInt64.toNat s.maxUnconfirmed) ∧
      Nat.le (UInt64.toNat s.confirmedEpoch) (UInt64.toNat s.issuedEpoch)

    def Init (maxUnconfirmed : UInt64) (s : EchoFenceState) : Prop :=
      s.unconfirmedKeys = (0 : UInt64) ∧
      s.maxUnconfirmed = maxUnconfirmed ∧
      s.confirmedEpoch = (0 : UInt64) ∧
      s.issuedEpoch = (0 : UInt64)

    def PredictKey (nextKeys propIssued : UInt64) (s sNext : EchoFenceState) : Prop :=
      sNext.unconfirmedKeys = _root_.echo_unconfirmed_clamp nextKeys s.maxUnconfirmed ∧
      sNext.maxUnconfirmed = s.maxUnconfirmed ∧
      sNext.confirmedEpoch = s.confirmedEpoch ∧
      sNext.issuedEpoch = _root_.echo_epoch_advance s.issuedEpoch propIssued

    def FenceReset (s sNext : EchoFenceState) : Prop :=
      sNext.unconfirmedKeys = (0 : UInt64) ∧
      sNext.maxUnconfirmed = s.maxUnconfirmed ∧
      sNext.confirmedEpoch = s.issuedEpoch ∧
      sNext.issuedEpoch = s.issuedEpoch

    def Next (s sNext : EchoFenceState) : Prop :=
      (∃ nk : UInt64, ∃ pi : UInt64, PredictKey nk pi s sNext) ∨
      FenceReset s sNext

    def Spec (maxUnconfirmed : UInt64) : StateMachine EchoFenceState :=
      StateMachine.mk (Init maxUnconfirmed) Next

    theorem keys_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.echo_unconfirmed_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_adv_ge : forall (cur : UInt64) (prop : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.echo_epoch_advance cur prop)) :=
      fun cur prop => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur prop)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => prop))))
        (instDecidableUInt64Lt cur prop)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxUnconfirmed : UInt64) (s : EchoFenceState)
        (hInit : Init maxUnconfirmed s) : EchoFenceInv s :=
      let hEq : s.confirmedEpoch = s.issuedEpoch := Eq.trans hInit.2.2.1 (Eq.symm hInit.2.2.2)
      let hE : Nat.le (UInt64.toNat s.confirmedEpoch) (UInt64.toNat s.issuedEpoch) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.issuedEpoch)) hEq)
          (Nat.le.refl (UInt64.toNat s.issuedEpoch))
      And.intro (zero_u64_le s.unconfirmedKeys s.maxUnconfirmed hInit.1) hE

    theorem predictKey_preserves_inv (nk pi : UInt64) (s sNext : EchoFenceState)
        (hInv : EchoFenceInv s) (hAct : PredictKey nk pi s sNext) : EchoFenceInv sNext :=
      let hK1 : Nat.le (UInt64.toNat sNext.unconfirmedKeys) (UInt64.toNat s.maxUnconfirmed) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxUnconfirmed)) hAct.1)
          (keys_clamp_le nk s.maxUnconfirmed)
      let hK2 : Nat.le (UInt64.toNat sNext.unconfirmedKeys) (UInt64.toNat sNext.maxUnconfirmed) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.unconfirmedKeys) (UInt64.toNat y)) hAct.2.1)
          hK1
      let hAdv : Nat.le (UInt64.toNat s.confirmedEpoch)
          (UInt64.toNat (_root_.echo_epoch_advance s.issuedEpoch pi)) :=
        Nat.le_trans hInv.2 (epoch_adv_ge s.issuedEpoch pi)
      let hE1 : Nat.le (UInt64.toNat sNext.confirmedEpoch)
          (UInt64.toNat (_root_.echo_epoch_advance s.issuedEpoch pi)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x)
            (UInt64.toNat (_root_.echo_epoch_advance s.issuedEpoch pi))) hAct.2.2.1)
          hAdv
      let hE2 : Nat.le (UInt64.toNat sNext.confirmedEpoch) (UInt64.toNat sNext.issuedEpoch) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.confirmedEpoch) (UInt64.toNat y)) hAct.2.2.2)
          hE1
      And.intro hK2 hE2

    theorem fenceReset_preserves_inv (s sNext : EchoFenceState)
        (hAct : FenceReset s sNext) : EchoFenceInv sNext :=
      let hEq : sNext.confirmedEpoch = sNext.issuedEpoch :=
        Eq.trans hAct.2.2.1 (Eq.symm hAct.2.2.2)
      let hE : Nat.le (UInt64.toNat sNext.confirmedEpoch) (UInt64.toNat sNext.issuedEpoch) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.issuedEpoch)) hEq)
          (Nat.le.refl (UInt64.toNat sNext.issuedEpoch))
      And.intro (zero_u64_le sNext.unconfirmedKeys sNext.maxUnconfirmed hAct.1) hE

    theorem next_preserves_inv (s sNext : EchoFenceState)
        (hInv : EchoFenceInv s) (hNext : Next s sNext) : EchoFenceInv sNext :=
      Or.elim hNext
        (fun hEx1 => Exists.elim hEx1 (fun nk hEx2 =>
          Exists.elim hEx2 (fun pi hP => predictKey_preserves_inv nk pi s sNext hInv hP)))
        (fun hR => fenceReset_preserves_inv s sNext hR)

    theorem spec_satisfies_mosh_password_fence_safety (maxUnconfirmed : UInt64) :
        (Spec maxUnconfirmed) ⊨ □ (Lift EchoFenceInv) :=
      invariantSatisfies (Spec maxUnconfirmed) EchoFenceInv
        (init_establishes_inv maxUnconfirmed)
        next_preserves_inv

    end TlaMoshPasswordFence
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def echo_has_key_budget_isl (unconfirmed : UInt64) (max_keys : UInt64) : Bool :=
      decide (unconfirmed < max_keys)
}
