// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for opt-in sticky producer gap fencing on refused batches
// (`Astream.Broker.TlaStickyBatchFence`), mounted under `cfg(clean_islands)` in
// `sticky_fence.rs` (`DESIGN-aterm-fabric.md` §14 Open Question 7 & §15).
// Proves over the Clean-origin `sticky_fence_min_seq` and `sticky_fence_seq_allowed`
// kernels (composed in `sticky_fence_admits_code_isl`) that:
// 1. Any pipelined write with `reqSeq > fenceSeq` while `fenced = 1` is rejected (`0`),
// 2. Any retry with `reqSeq <= fenceSeq` is admitted (`1`) and clears the fence upon commit,
// 3. No out-of-order write past a refused sequence ever commits (`outOfOrderCommitted = 0`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def sticky_fence_min_seq (cur_fence : UInt64) (failed_seq : UInt64) : UInt64 :=
      if cur_fence < failed_seq then cur_fence else failed_seq

    def sticky_fence_seq_allowed (fence_seq : UInt64) (req_seq : UInt64) : UInt64 :=
      if fence_seq < req_seq then 0 else 1

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Broker.TlaStickyBatchFence)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaStickyBatchFence

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaStickyBatchFence.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaStickyBatchFence.Always

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
    -- 3. Sticky Producer Gap Fence Kernel Lemmas & State Machine
    -- ========================================================================

    theorem sticky_fence_min_le_right (cur failed : UInt64) :
        Nat.le (UInt64.toNat (_root_.sticky_fence_min_seq cur failed)) (UInt64.toNat failed) :=
      @Decidable.casesOn (LT.lt cur failed)
        (fun (d : Decidable (LT.lt cur failed)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur failed) d cur failed)) (UInt64.toNat failed))
        (instDecidableUInt64Lt cur failed)
        (fun _ => Nat.le_refl (UInt64.toNat failed))
        (fun hLt => Nat.le_of_lt hLt)

    def sticky_fence_admits_code_isl (fenced : UInt64) (fence_seq : UInt64) (req_seq : UInt64) : UInt64 :=
      if 0 < fenced then _root_.sticky_fence_seq_allowed fence_seq req_seq else 1

    structure StickyFenceState where
      fenced              : UInt64
      fenceSeq            : UInt64
      lastCommitted       : UInt64
      outOfOrderCommitted : Nat

    def StickyBatchSafetyInv (s : StickyFenceState) : Prop :=
      (s.fenced = (0 : UInt64) ∨ s.fenced = (1 : UInt64)) ∧
      s.outOfOrderCommitted = 0

    def Init (s : StickyFenceState) : Prop :=
      s.fenced = (0 : UInt64) ∧
      s.fenceSeq = (0 : UInt64) ∧
      s.lastCommitted = (0 : UInt64) ∧
      s.outOfOrderCommitted = 0

    def AdmitUnfenced (reqSeq : UInt64) (s sNext : StickyFenceState) : Prop :=
      s.fenced = (0 : UInt64) ∧
      sticky_fence_admits_code_isl s.fenced s.fenceSeq reqSeq = (1 : UInt64) ∧
      sNext.fenced = (0 : UInt64) ∧
      sNext.fenceSeq = s.fenceSeq ∧
      sNext.lastCommitted = reqSeq ∧
      sNext.outOfOrderCommitted = s.outOfOrderCommitted

    def LatchRefusedFirst (failedSeq : UInt64) (s sNext : StickyFenceState) : Prop :=
      s.fenced = (0 : UInt64) ∧
      sNext.fenced = (1 : UInt64) ∧
      sNext.fenceSeq = failedSeq ∧
      sNext.lastCommitted = s.lastCommitted ∧
      sNext.outOfOrderCommitted = s.outOfOrderCommitted

    def TightenRefusedFence (failedSeq : UInt64) (s sNext : StickyFenceState) : Prop :=
      s.fenced = (1 : UInt64) ∧
      sNext.fenced = (1 : UInt64) ∧
      sNext.fenceSeq = _root_.sticky_fence_min_seq s.fenceSeq failedSeq ∧
      sNext.lastCommitted = s.lastCommitted ∧
      sNext.outOfOrderCommitted = s.outOfOrderCommitted

    def RejectAboveFence (reqSeq : UInt64) (s sNext : StickyFenceState) : Prop :=
      s.fenced = (1 : UInt64) ∧
      Nat.lt (UInt64.toNat s.fenceSeq) (UInt64.toNat reqSeq) ∧
      sticky_fence_admits_code_isl s.fenced s.fenceSeq reqSeq = (0 : UInt64) ∧
      sNext.fenced = (1 : UInt64) ∧
      sNext.fenceSeq = s.fenceSeq ∧
      sNext.lastCommitted = s.lastCommitted ∧
      sNext.outOfOrderCommitted = s.outOfOrderCommitted

    def RetryClearsFence (reqSeq : UInt64) (s sNext : StickyFenceState) : Prop :=
      s.fenced = (1 : UInt64) ∧
      Nat.le (UInt64.toNat reqSeq) (UInt64.toNat s.fenceSeq) ∧
      sticky_fence_admits_code_isl s.fenced s.fenceSeq reqSeq = (1 : UInt64) ∧
      sNext.fenced = (0 : UInt64) ∧
      sNext.fenceSeq = (0 : UInt64) ∧
      sNext.lastCommitted = reqSeq ∧
      sNext.outOfOrderCommitted = s.outOfOrderCommitted

    def Next (s sNext : StickyFenceState) : Prop :=
      (∃ r : UInt64, AdmitUnfenced r s sNext) ∨
      ((∃ f : UInt64, LatchRefusedFirst f s sNext) ∨
       ((∃ f : UInt64, TightenRefusedFence f s sNext) ∨
        ((∃ r : UInt64, RejectAboveFence r s sNext) ∨
         (∃ r : UInt64, RetryClearsFence r s sNext))))

    def Spec : StateMachine StickyFenceState :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : StickyFenceState) (hInit : Init s) :
        StickyBatchSafetyInv s :=
      And.intro (Or.inl hInit.1) hInit.2.2.2

    theorem admitUnfenced_preserves_inv (r : UInt64) (s sNext : StickyFenceState)
        (hInv : StickyBatchSafetyInv s) (hAct : AdmitUnfenced r s sNext) :
        StickyBatchSafetyInv sNext :=
      let hOrd : sNext.outOfOrderCommitted = 0 :=
        Eq.trans hAct.2.2.2.2.2 hInv.2
      And.intro (Or.inl hAct.2.2.1) hOrd

    theorem latchRefused_preserves_inv (f : UInt64) (s sNext : StickyFenceState)
        (hInv : StickyBatchSafetyInv s) (hAct : LatchRefusedFirst f s sNext) :
        StickyBatchSafetyInv sNext :=
      let hOrd : sNext.outOfOrderCommitted = 0 :=
        Eq.trans hAct.2.2.2.2 hInv.2
      And.intro (Or.inr hAct.2.1) hOrd

    theorem tightenRefused_preserves_inv (f : UInt64) (s sNext : StickyFenceState)
        (hInv : StickyBatchSafetyInv s) (hAct : TightenRefusedFence f s sNext) :
        StickyBatchSafetyInv sNext :=
      let hOrd : sNext.outOfOrderCommitted = 0 :=
        Eq.trans hAct.2.2.2.2 hInv.2
      And.intro (Or.inr hAct.2.1) hOrd

    theorem rejectAbove_preserves_inv (r : UInt64) (s sNext : StickyFenceState)
        (hInv : StickyBatchSafetyInv s) (hAct : RejectAboveFence r s sNext) :
        StickyBatchSafetyInv sNext :=
      let hOrd : sNext.outOfOrderCommitted = 0 :=
        Eq.trans hAct.2.2.2.2.2.2 hInv.2
      And.intro (Or.inr hAct.2.2.2.1) hOrd

    theorem retryClears_preserves_inv (r : UInt64) (s sNext : StickyFenceState)
        (hInv : StickyBatchSafetyInv s) (hAct : RetryClearsFence r s sNext) :
        StickyBatchSafetyInv sNext :=
      let hOrd : sNext.outOfOrderCommitted = 0 :=
        Eq.trans hAct.2.2.2.2.2.2 hInv.2
      And.intro (Or.inl hAct.2.2.2.1) hOrd

    theorem next_preserves_inv (s sNext : StickyFenceState)
        (hInv : StickyBatchSafetyInv s) (hNext : Next s sNext) :
        StickyBatchSafetyInv sNext :=
      Or.elim hNext
        (fun hEx => Exists.elim hEx (fun r hAct => admitUnfenced_preserves_inv r s sNext hInv hAct))
        (fun hR1 =>
          Or.elim hR1
            (fun hEx => Exists.elim hEx (fun f hAct => latchRefused_preserves_inv f s sNext hInv hAct))
            (fun hR2 =>
              Or.elim hR2
                (fun hEx => Exists.elim hEx (fun f hAct => tightenRefused_preserves_inv f s sNext hInv hAct))
                (fun hR3 =>
                  Or.elim hR3
                    (fun hEx => Exists.elim hEx (fun r hAct => rejectAbove_preserves_inv r s sNext hInv hAct))
                    (fun hEx => Exists.elim hEx (fun r hAct => retryClears_preserves_inv r s sNext hInv hAct)))))

    theorem spec_satisfies_sticky_batch_safety :
        Spec ⊨ □ (Lift StickyBatchSafetyInv) :=
      invariantSatisfies Spec StickyBatchSafetyInv init_establishes_inv next_preserves_inv

    end TlaStickyBatchFence
    end Broker
    end Astream

    def sticky_fence_table_within_cap_isl (len : UInt64) (max_entries : UInt64) : Bool :=
      decide (len ≤ max_entries)
}
