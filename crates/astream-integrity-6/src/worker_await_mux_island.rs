// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `aterm ctl await task @<sid>:<rev>` multi-worker revision-watermarked
// task multiplexing (`Astream.Agent.TlaWorkerAwaitMux`), mounted under `cfg(clean_islands)`
// in `worker_await_mux.rs`. Proves monotone revision progression (`seenRev <= latestRev`)
// and bounded watched-slot occupancy (`watchedCount <= maxWatched`) across worker spawns,
// revision updates, and terminal-state wakeups.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def worker_rev_advance (cur_rev : UInt64) (proposed_rev : UInt64) : UInt64 :=
      if cur_rev < proposed_rev then proposed_rev else cur_rev

    def worker_watch_count_clamp (count : UInt64) (max_watched : UInt64) : UInt64 :=
      if count < max_watched then count else max_watched

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Agent.TlaWorkerAwaitMux)
    -- ========================================================================
    namespace Astream
    namespace Agent
    namespace TlaWorkerAwaitMux

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Agent.TlaWorkerAwaitMux.Satisfies M F
    prefix:75 "□" => _root_.Astream.Agent.TlaWorkerAwaitMux.Always

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
    -- 3. Multi-Worker Revision Watermark Multiplexer State Machine
    -- ========================================================================

    structure WorkerMuxState where
      seenRev      : UInt64
      latestRev    : UInt64
      watchedCount : UInt64
      maxWatched   : UInt64

    def WorkerMuxInv (s : WorkerMuxState) : Prop :=
      Nat.le (UInt64.toNat s.seenRev) (UInt64.toNat s.latestRev) ∧
      Nat.le (UInt64.toNat s.watchedCount) (UInt64.toNat s.maxWatched)

    def Init (maxWatched : UInt64) (s : WorkerMuxState) : Prop :=
      s.seenRev = (0 : UInt64) ∧
      s.latestRev = (0 : UInt64) ∧
      s.watchedCount = (0 : UInt64) ∧
      s.maxWatched = maxWatched

    def ObserveWorkerTransition (proposedRev newCount : UInt64) (s sNext : WorkerMuxState) : Prop :=
      sNext.seenRev = s.seenRev ∧
      sNext.latestRev = _root_.worker_rev_advance s.latestRev proposedRev ∧
      sNext.watchedCount = _root_.worker_watch_count_clamp newCount s.maxWatched ∧
      sNext.maxWatched = s.maxWatched

    def AcknowledgeWakeup (s sNext : WorkerMuxState) : Prop :=
      sNext.seenRev = s.latestRev ∧
      sNext.latestRev = s.latestRev ∧
      sNext.watchedCount = s.watchedCount ∧
      sNext.maxWatched = s.maxWatched

    def Next (s sNext : WorkerMuxState) : Prop :=
      (∃ pr : UInt64, ∃ nc : UInt64, ObserveWorkerTransition pr nc s sNext) ∨
      AcknowledgeWakeup s sNext

    def Spec (maxWatched : UInt64) : StateMachine WorkerMuxState :=
      StateMachine.mk (Init maxWatched) Next

    theorem rev_adv_ge : forall (cur : UInt64) (prop : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.worker_rev_advance cur prop)) :=
      fun cur prop => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur prop)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => prop))))
        (instDecidableUInt64Lt cur prop)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem watch_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.worker_watch_count_clamp cand cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (maxWatched : UInt64) (s : WorkerMuxState)
        (hInit : Init maxWatched s) : WorkerMuxInv s :=
      let hEq : s.seenRev = s.latestRev := Eq.trans hInit.1 (Eq.symm hInit.2.1)
      let hR : Nat.le (UInt64.toNat s.seenRev) (UInt64.toNat s.latestRev) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.latestRev)) hEq)
          (Nat.le.refl (UInt64.toNat s.latestRev))
      And.intro hR (zero_u64_le s.watchedCount s.maxWatched hInit.2.2.1)

    theorem observeTransition_preserves_inv (pr nc : UInt64) (s sNext : WorkerMuxState)
        (hInv : WorkerMuxInv s) (hAct : ObserveWorkerTransition pr nc s sNext) :
        WorkerMuxInv sNext :=
      let hAdv : Nat.le (UInt64.toNat s.seenRev)
          (UInt64.toNat (_root_.worker_rev_advance s.latestRev pr)) :=
        Nat.le_trans hInv.1 (rev_adv_ge s.latestRev pr)
      let hR1 : Nat.le (UInt64.toNat sNext.seenRev)
          (UInt64.toNat (_root_.worker_rev_advance s.latestRev pr)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x)
            (UInt64.toNat (_root_.worker_rev_advance s.latestRev pr))) hAct.1)
          hAdv
      let hR2 : Nat.le (UInt64.toNat sNext.seenRev) (UInt64.toNat sNext.latestRev) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.seenRev) (UInt64.toNat y)) hAct.2.1)
          hR1
      let hW1 : Nat.le (UInt64.toNat sNext.watchedCount) (UInt64.toNat s.maxWatched) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxWatched)) hAct.2.2.1)
          (watch_clamp_le nc s.maxWatched)
      let hW2 : Nat.le (UInt64.toNat sNext.watchedCount) (UInt64.toNat sNext.maxWatched) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.watchedCount) (UInt64.toNat y)) hAct.2.2.2)
          hW1
      And.intro hR2 hW2

    theorem ackWakeup_preserves_inv (s sNext : WorkerMuxState)
        (hInv : WorkerMuxInv s) (hAct : AcknowledgeWakeup s sNext) : WorkerMuxInv sNext :=
      let hEq : sNext.seenRev = sNext.latestRev :=
        Eq.trans hAct.1 (Eq.symm hAct.2.1)
      let hR : Nat.le (UInt64.toNat sNext.seenRev) (UInt64.toNat sNext.latestRev) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.latestRev)) hEq)
          (Nat.le.refl (UInt64.toNat sNext.latestRev))
      let hW1 : Nat.le (UInt64.toNat sNext.watchedCount) (UInt64.toNat s.maxWatched) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxWatched)) hAct.2.2.1)
          hInv.2
      let hW2 : Nat.le (UInt64.toNat sNext.watchedCount) (UInt64.toNat sNext.maxWatched) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.watchedCount) (UInt64.toNat y)) hAct.2.2.2)
          hW1
      And.intro hR hW2

    theorem next_preserves_inv (s sNext : WorkerMuxState)
        (hInv : WorkerMuxInv s) (hNext : Next s sNext) : WorkerMuxInv sNext :=
      Or.elim hNext
        (fun hEx1 => Exists.elim hEx1 (fun pr hEx2 =>
          Exists.elim hEx2 (fun nc hO => observeTransition_preserves_inv pr nc s sNext hInv hO)))
        (fun hAck => ackWakeup_preserves_inv s sNext hInv hAck)

    theorem spec_satisfies_worker_await_mux_safety (maxWatched : UInt64) :
        (Spec maxWatched) ⊨ □ (Lift WorkerMuxInv) :=
      invariantSatisfies (Spec maxWatched) WorkerMuxInv
        (init_establishes_inv maxWatched)
        next_preserves_inv

    end TlaWorkerAwaitMux
    end Agent
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def worker_rev_is_unseen_isl (seen_rev : UInt64) (latest_rev : UInt64) : Bool :=
      decide (seen_rev < latest_rev)
}
