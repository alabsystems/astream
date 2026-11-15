// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for fine-grained per-byte PTY write->echo causal attribution across
// overlapping in-flight inputs (`Astream.Term.TlaOverlapEcho`), mounted under
// `cfg(clean_islands)` in `predict.rs` (`docs/ROADMAP.md` line 179).
// Proves that `echo_queue_len_clamp` and `echo_matched_advance` maintain:
// 1. `queuedBytes <= maxQueueCap` (bounded in-flight memory across bursts), and
// 2. `prevRetiredOff <= lastRetiredOff` (monotone causal in-offset retirement across
//    split and coalesced PTY echo chunks).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def echo_queue_len_clamp (proposed_len : UInt64) (cap : UInt64) : UInt64 :=
      if proposed_len < cap then proposed_len else cap

    def echo_matched_advance (cur_off : UInt64) (cand_off : UInt64) : UInt64 :=
      if cur_off < cand_off then cand_off else cur_off

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaOverlapEcho)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaOverlapEcho

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaOverlapEcho.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaOverlapEcho.Always

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

    theorem echo_queue_len_clamp_le_cap (len cap : UInt64) :
        Nat.le (UInt64.toNat (_root_.echo_queue_len_clamp len cap)) (UInt64.toNat cap) :=
      @Decidable.casesOn (LT.lt len cap)
        (fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt len cap) d len cap)) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => Nat.le_refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem echo_matched_advance_ge_cur (cur cand : UInt64) :
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.echo_matched_advance cur cand)) :=
      @Decidable.casesOn (LT.lt cur cand)
        (fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (@ite UInt64 (LT.lt cur cand) d cand cur)))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le_refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    structure OverlapEchoState where
      queuedBytes    : UInt64
      maxQueueCap    : UInt64
      floorRetired   : UInt64
      lastRetiredOff : UInt64

    def OverlapEchoSafetyInv (s : OverlapEchoState) : Prop :=
      Nat.le (UInt64.toNat s.queuedBytes) (UInt64.toNat s.maxQueueCap) ∧
      Nat.le (UInt64.toNat s.floorRetired) (UInt64.toNat s.lastRetiredOff)

    def Init (cap floorOff : UInt64) (s : OverlapEchoState) : Prop :=
      s.queuedBytes = (0 : UInt64) ∧
      s.maxQueueCap = cap ∧
      s.floorRetired = floorOff ∧
      s.lastRetiredOff = floorOff

    def EnqueueInputBytes (nextLen : UInt64) (s sNext : OverlapEchoState) : Prop :=
      sNext.queuedBytes = _root_.echo_queue_len_clamp nextLen s.maxQueueCap ∧
      sNext.maxQueueCap = s.maxQueueCap ∧
      sNext.floorRetired = s.floorRetired ∧
      sNext.lastRetiredOff = s.lastRetiredOff

    def AttributeEchoChunk (remLen candOff : UInt64) (s sNext : OverlapEchoState) : Prop :=
      sNext.queuedBytes = _root_.echo_queue_len_clamp remLen s.maxQueueCap ∧
      sNext.maxQueueCap = s.maxQueueCap ∧
      sNext.floorRetired = s.floorRetired ∧
      sNext.lastRetiredOff = _root_.echo_matched_advance s.lastRetiredOff candOff

    def Next (s sNext : OverlapEchoState) : Prop :=
      (∃ nl : UInt64, EnqueueInputBytes nl s sNext) ∨
      (∃ rl : UInt64, ∃ co : UInt64, AttributeEchoChunk rl co s sNext)

    def Spec (cap floorOff : UInt64) : StateMachine OverlapEchoState :=
      StateMachine.mk (Init cap floorOff) Next

    theorem init_establishes_inv (cap floorOff : UInt64) (s : OverlapEchoState)
        (hInit : Init cap floorOff s) : OverlapEchoSafetyInv s :=
      let hQ0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.maxQueueCap) :=
        Nat.zero_le (UInt64.toNat s.maxQueueCap)
      let hQ : Nat.le (UInt64.toNat s.queuedBytes) (UInt64.toNat s.maxQueueCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxQueueCap)) hInit.1) hQ0
      let hEqOff : s.floorRetired = s.lastRetiredOff :=
        Eq.trans hInit.2.2.1 (Eq.symm hInit.2.2.2)
      let hR : Nat.le (UInt64.toNat s.floorRetired) (UInt64.toNat s.lastRetiredOff) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.lastRetiredOff)) hEqOff)
          (Nat.le_refl (UInt64.toNat s.lastRetiredOff))
      And.intro hQ hR

    theorem enqueue_preserves_inv (nl : UInt64) (s sNext : OverlapEchoState)
        (hInv : OverlapEchoSafetyInv s) (hAct : EnqueueInputBytes nl s sNext) :
        OverlapEchoSafetyInv sNext :=
      let hClamp : Nat.le (UInt64.toNat (_root_.echo_queue_len_clamp nl s.maxQueueCap)) (UInt64.toNat s.maxQueueCap) :=
        echo_queue_len_clamp_le_cap nl s.maxQueueCap
      let hQ1 : Nat.le (UInt64.toNat sNext.queuedBytes) (UInt64.toNat s.maxQueueCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxQueueCap)) hAct.1) hClamp
      let hQ : Nat.le (UInt64.toNat sNext.queuedBytes) (UInt64.toNat sNext.maxQueueCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.queuedBytes) (UInt64.toNat y)) hAct.2.1) hQ1
      let hR1 : Nat.le (UInt64.toNat sNext.floorRetired) (UInt64.toNat s.lastRetiredOff) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.lastRetiredOff)) hAct.2.2.1) hInv.2
      let hR : Nat.le (UInt64.toNat sNext.floorRetired) (UInt64.toNat sNext.lastRetiredOff) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.floorRetired) (UInt64.toNat y)) hAct.2.2.2) hR1
      And.intro hQ hR

    theorem attribute_preserves_inv (rl co : UInt64) (s sNext : OverlapEchoState)
        (hInv : OverlapEchoSafetyInv s) (hAct : AttributeEchoChunk rl co s sNext) :
        OverlapEchoSafetyInv sNext :=
      let hClamp : Nat.le (UInt64.toNat (_root_.echo_queue_len_clamp rl s.maxQueueCap)) (UInt64.toNat s.maxQueueCap) :=
        echo_queue_len_clamp_le_cap rl s.maxQueueCap
      let hQ1 : Nat.le (UInt64.toNat sNext.queuedBytes) (UInt64.toNat s.maxQueueCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxQueueCap)) hAct.1) hClamp
      let hQ : Nat.le (UInt64.toNat sNext.queuedBytes) (UInt64.toNat sNext.maxQueueCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.queuedBytes) (UInt64.toNat y)) hAct.2.1) hQ1
      let hAdv : Nat.le (UInt64.toNat s.lastRetiredOff) (UInt64.toNat (_root_.echo_matched_advance s.lastRetiredOff co)) :=
        echo_matched_advance_ge_cur s.lastRetiredOff co
      let hTrans : Nat.le (UInt64.toNat s.floorRetired) (UInt64.toNat (_root_.echo_matched_advance s.lastRetiredOff co)) :=
        Nat.le_trans hInv.2 hAdv
      let hR1 : Nat.le (UInt64.toNat sNext.floorRetired) (UInt64.toNat (_root_.echo_matched_advance s.lastRetiredOff co)) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (_root_.echo_matched_advance s.lastRetiredOff co))) hAct.2.2.1) hTrans
      let hR : Nat.le (UInt64.toNat sNext.floorRetired) (UInt64.toNat sNext.lastRetiredOff) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.floorRetired) (UInt64.toNat y)) hAct.2.2.2) hR1
      And.intro hQ hR

    theorem next_preserves_inv (s sNext : OverlapEchoState)
        (hInv : OverlapEchoSafetyInv s) (hNext : Next s sNext) :
        OverlapEchoSafetyInv sNext :=
      Or.elim hNext
        (fun hEnq =>
          Exists.elim hEnq (fun nl hE => enqueue_preserves_inv nl s sNext hInv hE))
        (fun hAtt =>
          Exists.elim hAtt (fun rl hEx =>
            Exists.elim hEx (fun co hA => attribute_preserves_inv rl co s sNext hInv hA)))

    theorem spec_satisfies_overlap_echo_safety (cap floorOff : UInt64) :
        (Spec cap floorOff) ⊨ □ (Lift OverlapEchoSafetyInv) :=
      invariantSatisfies (Spec cap floorOff) OverlapEchoSafetyInv
        (init_establishes_inv cap floorOff)
        next_preserves_inv

    end TlaOverlapEcho
    end Term
    end Astream

    def echo_queue_within_cap_isl (queued : USize) (cap : USize) : Bool :=
      decide (queued ≤ cap)
}
