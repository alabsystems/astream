// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for directional 96-bit AEAD stream-frame nonce ratcheting and
// rekey-epoch monotonicity (`Astream.Aead.TlaStreamNonceRatchet`), mounted under
// `cfg(clean_islands)` in `aead_nonce_ratchet.rs`. Proves `prevEpoch <= curEpoch` and
// `frameSeq <= epochCap` across frame seals and key-rotation epoch ratchets.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def nonce_epoch_advance (cur_epoch : UInt64) (proposed_epoch : UInt64) : UInt64 :=
      if cur_epoch < proposed_epoch then proposed_epoch else cur_epoch

    def nonce_seq_clamp (proposed_seq : UInt64) (epoch_cap : UInt64) : UInt64 :=
      if proposed_seq < epoch_cap then proposed_seq else epoch_cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Aead.TlaStreamNonceRatchet)
    -- ========================================================================
    namespace Astream
    namespace Aead
    namespace TlaStreamNonceRatchet

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Aead.TlaStreamNonceRatchet.Satisfies M F
    prefix:75 "□" => _root_.Astream.Aead.TlaStreamNonceRatchet.Always

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
    -- 3. Directional AEAD Stream Nonce Ratchet State Machine
    -- ========================================================================

    structure NonceRatchetState where
      prevEpoch : UInt64
      curEpoch  : UInt64
      frameSeq  : UInt64
      epochCap  : UInt64

    def NonceRatchetInv (s : NonceRatchetState) : Prop :=
      Nat.le (UInt64.toNat s.prevEpoch) (UInt64.toNat s.curEpoch) ∧
      Nat.le (UInt64.toNat s.frameSeq) (UInt64.toNat s.epochCap)

    def Init (epochCap : UInt64) (s : NonceRatchetState) : Prop :=
      s.prevEpoch = (0 : UInt64) ∧
      s.curEpoch = (0 : UInt64) ∧
      s.frameSeq = (0 : UInt64) ∧
      s.epochCap = epochCap

    def SealFrame (nextSeq : UInt64) (s sNext : NonceRatchetState) : Prop :=
      sNext.prevEpoch = s.prevEpoch ∧
      sNext.curEpoch = s.curEpoch ∧
      sNext.frameSeq = _root_.nonce_seq_clamp nextSeq s.epochCap ∧
      sNext.epochCap = s.epochCap

    def RatchetEpoch (proposedEpoch : UInt64) (s sNext : NonceRatchetState) : Prop :=
      sNext.prevEpoch = s.curEpoch ∧
      sNext.curEpoch = _root_.nonce_epoch_advance s.curEpoch proposedEpoch ∧
      sNext.frameSeq = (0 : UInt64) ∧
      sNext.epochCap = s.epochCap

    def Next (s sNext : NonceRatchetState) : Prop :=
      (∃ ns : UInt64, SealFrame ns s sNext) ∨
      (∃ pe : UInt64, RatchetEpoch pe s sNext)

    def Spec (epochCap : UInt64) : StateMachine NonceRatchetState :=
      StateMachine.mk (Init epochCap) Next

    theorem epoch_adv_ge : forall (cur : UInt64) (prop : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.nonce_epoch_advance cur prop)) :=
      fun cur prop => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur prop)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => prop))))
        (instDecidableUInt64Lt cur prop)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem seq_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.nonce_seq_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (epochCap : UInt64) (s : NonceRatchetState)
        (hInit : Init epochCap s) : NonceRatchetInv s :=
      let hEq : s.prevEpoch = s.curEpoch := Eq.trans hInit.1 (Eq.symm hInit.2.1)
      let hE : Nat.le (UInt64.toNat s.prevEpoch) (UInt64.toNat s.curEpoch) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.curEpoch)) hEq)
          (Nat.le.refl (UInt64.toNat s.curEpoch))
      And.intro hE (zero_u64_le s.frameSeq s.epochCap hInit.2.2.1)

    theorem sealFrame_preserves_inv (ns : UInt64) (s sNext : NonceRatchetState)
        (hInv : NonceRatchetInv s) (hAct : SealFrame ns s sNext) : NonceRatchetInv sNext :=
      let hE1 : Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat s.curEpoch) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.curEpoch)) hAct.1)
          hInv.1
      let hE2 : Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat sNext.curEpoch) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat y)) hAct.2.1)
          hE1
      let hS1 : Nat.le (UInt64.toNat sNext.frameSeq) (UInt64.toNat s.epochCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.epochCap)) hAct.2.2.1)
          (seq_clamp_le ns s.epochCap)
      let hS2 : Nat.le (UInt64.toNat sNext.frameSeq) (UInt64.toNat sNext.epochCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.frameSeq) (UInt64.toNat y)) hAct.2.2.2)
          hS1
      And.intro hE2 hS2

    theorem ratchetEpoch_preserves_inv (pe : UInt64) (s sNext : NonceRatchetState)
        (hAct : RatchetEpoch pe s sNext) : NonceRatchetInv sNext :=
      let hAdv : Nat.le (UInt64.toNat s.curEpoch)
          (UInt64.toNat (_root_.nonce_epoch_advance s.curEpoch pe)) :=
        epoch_adv_ge s.curEpoch pe
      let hE1 : Nat.le (UInt64.toNat sNext.prevEpoch)
          (UInt64.toNat (_root_.nonce_epoch_advance s.curEpoch pe)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x)
            (UInt64.toNat (_root_.nonce_epoch_advance s.curEpoch pe))) hAct.1)
          hAdv
      let hE2 : Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat sNext.curEpoch) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.prevEpoch) (UInt64.toNat y)) hAct.2.1)
          hE1
      let hS : Nat.le (UInt64.toNat sNext.frameSeq) (UInt64.toNat sNext.epochCap) :=
        zero_u64_le sNext.frameSeq sNext.epochCap hAct.2.2.1
      And.intro hE2 hS

    theorem next_preserves_inv (s sNext : NonceRatchetState)
        (hInv : NonceRatchetInv s) (hNext : Next s sNext) : NonceRatchetInv sNext :=
      Or.elim hNext
        (fun hExS => Exists.elim hExS (fun ns hS => sealFrame_preserves_inv ns s sNext hInv hS))
        (fun hExR => Exists.elim hExR (fun pe hR => ratchetEpoch_preserves_inv pe s sNext hR))

    theorem spec_satisfies_nonce_ratchet_safety (epochCap : UInt64) :
        (Spec epochCap) ⊨ □ (Lift NonceRatchetInv) :=
      invariantSatisfies (Spec epochCap) NonceRatchetInv
        (init_establishes_inv epochCap)
        next_preserves_inv

    end TlaStreamNonceRatchet
    end Aead
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def nonce_seq_has_room_isl (seq : UInt64) (epoch_cap : UInt64) : Bool :=
      decide (seq < epoch_cap)
}
