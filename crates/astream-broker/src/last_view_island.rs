// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for checked last-value retirement history (`Astream.Broker.TlaLastView`),
// mounted under `cfg(clean_islands)` in `last_view.rs` (`docs/ROADMAP.md` "Last-value
// retirement-history lifetime").
//
// Models `RetireHistory` (`available`, `published`, partial-prefix maintenance quantum
// `PRUNE_WORK = 64`) and an owned `LastView` cursor (`pinned`, `pinnedVis`, `captureAvail`,
// `capturePub`) over Clean-origin (`clean_origin_mir` I5) transition functions:
// 1. `last_view_available_advance`: monotone advance of the store's earliest unpruned
//    retirement floor (`max(cur_avail, vis_head)`),
// 2. `last_view_prune_clamp`: bounded partial-prefix maintenance work (`min(steps, max_work)`),
// 3. `last_view_not_before_avail` and `last_view_not_above_pub` (composed in
//    `last_view_window_admits_code_isl`): checked `[avail, pubHead]` view admission
//    (`TooOld` below `avail`, `NotPublished` above `pubHead`).
//
// Proves `spec_satisfies_last_view_safety` (`Spec ⊨ □ (Lift LastViewSafetyInv)`):
// - Every admitted `LastView` satisfies `captureAvail <= pinnedVis <= capturePub` at capture,
// - Owner publications (`AdvancePublished`) advance `avail` monotonically (`captureAvail <= avail`)
//   without revoking live views (`pinnedVis` stays intact while the store detaches its own prefix),
// - Partial-prefix maintenance never exceeds `PRUNE_WORK = 64` steps per publication.
// Out of the model: long-lived views and returned `Arc<BrokerRecord>` handles retain their
// explicit memory cost until read or dropped (`Link::drop` iterative chain destructor).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def last_view_available_advance (cur_avail : UInt64) (vis_head : UInt64) : UInt64 :=
      if cur_avail < vis_head then vis_head else cur_avail

    def last_view_prune_clamp (steps : UInt64) (max_work : UInt64) : UInt64 :=
      if steps < max_work then steps else max_work

    def last_view_not_before_avail (avail : UInt64) (req_vis : UInt64) : UInt64 :=
      if req_vis < avail then 0 else 1

    def last_view_not_above_pub (pub_head : UInt64) (req_vis : UInt64) : UInt64 :=
      if pub_head < req_vis then 0 else 1

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Broker.TlaLastView)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaLastView

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaLastView.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaLastView.Always

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
    -- 3. Retirement-History Kernel Lemmas & State Machine
    -- ========================================================================

    theorem zero_is_not_one (h : (0 : UInt64) = 1) : False :=
      absurd h (by decide)

    theorem avail_advance_ge_cur : forall (cur : UInt64) (vis : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.last_view_available_advance cur vis)) :=
      fun cur vis => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur vis)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => vis))))
        (instDecidableUInt64Lt cur vis)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem avail_advance_ge_vis : forall (cur : UInt64) (vis : UInt64),
        Nat.le (UInt64.toNat vis) (UInt64.toNat (_root_.last_view_available_advance cur vis)) :=
      fun cur vis => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur vis)) =>
          Nat.le (UInt64.toNat vis) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => vis))))
        (instDecidableUInt64Lt cur vis)
        (fun hNotLt => Nat.le_of_not_lt hNotLt)
        (fun _ => Nat.le.refl (UInt64.toNat vis))

    theorem prune_clamp_le_quantum : forall (steps : UInt64) (max_work : UInt64),
        Nat.le (UInt64.toNat (_root_.last_view_prune_clamp steps max_work)) (UInt64.toNat max_work) :=
      fun steps max_work => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt steps max_work)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_work) (fun _ => steps))) (UInt64.toNat max_work))
        (instDecidableUInt64Lt steps max_work)
        (fun _ => Nat.le.refl (UInt64.toNat max_work))
        (fun hLt => Nat.le_of_lt hLt)

    theorem admitted_ge_avail (avail req : UInt64)
        (h : _root_.last_view_not_before_avail avail req = 1) :
        Nat.le (UInt64.toNat avail) (UInt64.toNat req) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt req avail)) =>
          (Decidable.casesOn (motive := fun _ => UInt64) d (fun _ => 1) (fun _ => 0)) = 1 →
            Nat.le (UInt64.toNat avail) (UInt64.toNat req))
        (instDecidableUInt64Lt req avail)
        (fun hNotLt _ => Nat.le_of_not_lt hNotLt)
        (fun _ hZero => False.elim (zero_is_not_one hZero))
        h

    theorem admitted_le_pub (pub_head req : UInt64)
        (h : _root_.last_view_not_above_pub pub_head req = 1) :
        Nat.le (UInt64.toNat req) (UInt64.toNat pub_head) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt pub_head req)) =>
          (Decidable.casesOn (motive := fun _ => UInt64) d (fun _ => 1) (fun _ => 0)) = 1 →
            Nat.le (UInt64.toNat req) (UInt64.toNat pub_head))
        (instDecidableUInt64Lt pub_head req)
        (fun hNotLt _ => Nat.le_of_not_lt hNotLt)
        (fun _ hZero => False.elim (zero_is_not_one hZero))
        h

    def last_view_window_admits_code_isl (avail : UInt64) (pub_head : UInt64) (req_vis : UInt64) : UInt64 :=
      if 0 < _root_.last_view_not_before_avail avail req_vis then
        _root_.last_view_not_above_pub pub_head req_vis
      else
        0

    theorem window_admits_ge_avail (avail pub_head req : UInt64)
        (h : last_view_window_admits_code_isl avail pub_head req = 1) :
        Nat.le (UInt64.toNat avail) (UInt64.toNat req) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt (0 : UInt64) (_root_.last_view_not_before_avail avail req))) =>
          (Decidable.casesOn (motive := fun _ => UInt64) d
            (fun _ => 0)
            (fun _ => _root_.last_view_not_above_pub pub_head req)) = 1 →
          Nat.le (UInt64.toNat avail) (UInt64.toNat req))
        (instDecidableUInt64Lt 0 (_root_.last_view_not_before_avail avail req))
        (fun _ hZero => False.elim (zero_is_not_one hZero))
        (fun hPos _ =>
          Decidable.casesOn
            (motive := fun (d2 : Decidable (LT.lt req avail)) =>
              LT.lt (0 : UInt64) (Decidable.casesOn (motive := fun _ => UInt64) d2 (fun _ => 1) (fun _ => 0)) →
              Nat.le (UInt64.toNat avail) (UInt64.toNat req))
            (instDecidableUInt64Lt req avail)
            (fun hNotLt _ => Nat.le_of_not_lt hNotLt)
            (fun _ hLtZero => False.elim (Nat.lt_irrefl (UInt64.toNat (0 : UInt64)) hLtZero))
            hPos)
        h

    theorem window_admits_le_pub (avail pub_head req : UInt64)
        (h : last_view_window_admits_code_isl avail pub_head req = 1) :
        Nat.le (UInt64.toNat req) (UInt64.toNat pub_head) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt (0 : UInt64) (_root_.last_view_not_before_avail avail req))) =>
          (Decidable.casesOn (motive := fun _ => UInt64) d
            (fun _ => 0)
            (fun _ => _root_.last_view_not_above_pub pub_head req)) = 1 →
          Nat.le (UInt64.toNat req) (UInt64.toNat pub_head))
        (instDecidableUInt64Lt 0 (_root_.last_view_not_before_avail avail req))
        (fun _ hZero => False.elim (zero_is_not_one hZero))
        (fun _ hAbove => admitted_le_pub pub_head req hAbove)
        h

    structure LastViewHistoryState where
      avail          : UInt64
      pubHead        : UInt64
      pinned         : UInt64
      pinnedVis      : UInt64
      captureAvail   : UInt64
      capturePub     : UInt64
      lastPruneSteps : UInt64

    def LastViewBounds (s : LastViewHistoryState) : Prop :=
      Nat.le (UInt64.toNat s.captureAvail) (UInt64.toNat s.pinnedVis) ∧
      (Nat.le (UInt64.toNat s.pinnedVis) (UInt64.toNat s.capturePub) ∧
       Nat.le (UInt64.toNat s.captureAvail) (UInt64.toNat s.avail))

    def LastViewSafetyInv (s : LastViewHistoryState) : Prop :=
      (s.pinned = (0 : UInt64) ∨ (s.pinned = (1 : UInt64) ∧ LastViewBounds s)) ∧
      Nat.le (UInt64.toNat s.lastPruneSteps) (UInt64.toNat (64 : UInt64))

    def Init (s : LastViewHistoryState) : Prop :=
      s.pubHead = s.avail ∧
      s.pinned = (0 : UInt64) ∧
      s.lastPruneSteps = (0 : UInt64)

    -- Private broker constructor sets a lower initial quorum head before handing the log out.
    def StartLowerQuorum (qHead : UInt64) (s sNext : LastViewHistoryState) : Prop :=
      s.pinned = (0 : UInt64) ∧
      sNext.avail = s.avail ∧
      sNext.pubHead = qHead ∧
      sNext.pinned = (0 : UInt64) ∧
      sNext.pinnedVis = s.pinnedVis ∧
      sNext.captureAvail = s.captureAvail ∧
      sNext.capturePub = s.capturePub ∧
      sNext.lastPruneSteps = s.lastPruneSteps

    -- Owner publication advances `pubHead` monotonically, raises `avail` to `max(avail, vis)`,
    -- and bounds partial-prefix trimming to `PRUNE_WORK = 64` without revoking live views.
    def AdvancePublished (vis rawSteps : UInt64) (s sNext : LastViewHistoryState) : Prop :=
      _root_.last_view_not_before_avail s.pubHead vis = (1 : UInt64) ∧
      sNext.avail = _root_.last_view_available_advance s.avail vis ∧
      sNext.pubHead = vis ∧
      sNext.pinned = s.pinned ∧
      sNext.pinnedVis = s.pinnedVis ∧
      sNext.captureAvail = s.captureAvail ∧
      sNext.capturePub = s.capturePub ∧
      sNext.lastPruneSteps = _root_.last_view_prune_clamp rawSteps (64 : UInt64)

    -- Capturing a checked `LastView` requires `reqVis` inside `[avail, pubHead]`.
    def CaptureView (reqVis : UInt64) (s sNext : LastViewHistoryState) : Prop :=
      last_view_window_admits_code_isl s.avail s.pubHead reqVis = (1 : UInt64) ∧
      sNext.avail = s.avail ∧
      sNext.pubHead = s.pubHead ∧
      sNext.pinned = (1 : UInt64) ∧
      sNext.pinnedVis = reqVis ∧
      sNext.captureAvail = s.avail ∧
      sNext.capturePub = s.pubHead ∧
      sNext.lastPruneSteps = s.lastPruneSteps

    -- Dropping a live `LastView` releases its forward-cursor ownership.
    def ReleaseView (s sNext : LastViewHistoryState) : Prop :=
      sNext.avail = s.avail ∧
      sNext.pubHead = s.pubHead ∧
      sNext.pinned = (0 : UInt64) ∧
      sNext.pinnedVis = s.pinnedVis ∧
      sNext.captureAvail = s.captureAvail ∧
      sNext.capturePub = s.capturePub ∧
      sNext.lastPruneSteps = s.lastPruneSteps

    def Next (s sNext : LastViewHistoryState) : Prop :=
      (∃ q : UInt64, StartLowerQuorum q s sNext) ∨
      ((∃ vis : UInt64, ∃ steps : UInt64, AdvancePublished vis steps s sNext) ∨
       ((∃ req : UInt64, CaptureView req s sNext) ∨
        ReleaseView s sNext))

    def Spec : StateMachine LastViewHistoryState :=
      StateMachine.mk Init Next

    theorem zero_le_64 : Nat.le (UInt64.toNat (0 : UInt64)) (UInt64.toNat (64 : UInt64)) :=
      by decide

    theorem init_establishes_inv (s : LastViewHistoryState) (hInit : Init s) :
        LastViewSafetyInv s :=
      let hPrune : Nat.le (UInt64.toNat s.lastPruneSteps) (UInt64.toNat (64 : UInt64)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (64 : UInt64))) hInit.2.2)
          zero_le_64
      And.intro (Or.inl hInit.2.1) hPrune

    theorem startLower_preserves_inv (q : UInt64) (s sNext : LastViewHistoryState)
        (hInv : LastViewSafetyInv s) (hAct : StartLowerQuorum q s sNext) :
        LastViewSafetyInv sNext :=
      let hPrune : Nat.le (UInt64.toNat sNext.lastPruneSteps) (UInt64.toNat (64 : UInt64)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (64 : UInt64))) hAct.2.2.2.2.2.2.2)
          hInv.2
      And.intro (Or.inl hAct.2.2.2.1) hPrune

    theorem advance_preserves_bounds (vis rawSteps : UInt64) (s sNext : LastViewHistoryState)
        (hB : LastViewBounds s) (hAct : AdvancePublished vis rawSteps s sNext) :
        LastViewBounds sNext :=
      let hLow : Nat.le (UInt64.toNat sNext.captureAvail) (UInt64.toNat sNext.pinnedVis) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.pinnedVis)) hAct.2.2.2.2.2.1)
          (Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat s.captureAvail) (UInt64.toNat x)) hAct.2.2.2.2.1)
            hB.1)
      let hHigh : Nat.le (UInt64.toNat sNext.pinnedVis) (UInt64.toNat sNext.capturePub) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.capturePub)) hAct.2.2.2.2.1)
          (Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat s.pinnedVis) (UInt64.toNat x)) hAct.2.2.2.2.2.2.1)
            hB.2.1)
      let hStepAvail : Nat.le (UInt64.toNat s.captureAvail) (UInt64.toNat sNext.avail) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat s.captureAvail) (UInt64.toNat x)) hAct.2.1)
          (Nat.le_trans hB.2.2 (avail_advance_ge_cur s.avail vis))
      let hMonoAvail : Nat.le (UInt64.toNat sNext.captureAvail) (UInt64.toNat sNext.avail) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.avail)) hAct.2.2.2.2.2.1)
          hStepAvail
      And.intro hLow (And.intro hHigh hMonoAvail)

    theorem advance_preserves_inv (vis rawSteps : UInt64) (s sNext : LastViewHistoryState)
        (hInv : LastViewSafetyInv s) (hAct : AdvancePublished vis rawSteps s sNext) :
        LastViewSafetyInv sNext :=
      let hPin : sNext.pinned = (0 : UInt64) ∨ (sNext.pinned = (1 : UInt64) ∧ LastViewBounds sNext) :=
        Or.elim hInv.1
          (fun hZero => Or.inl (Eq.trans hAct.2.2.2.1 hZero))
          (fun hOne =>
            Or.inr (And.intro
              (Eq.trans hAct.2.2.2.1 hOne.1)
              (advance_preserves_bounds vis rawSteps s sNext hOne.2 hAct)))
      let hPrune : Nat.le (UInt64.toNat sNext.lastPruneSteps) (UInt64.toNat (64 : UInt64)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (64 : UInt64))) hAct.2.2.2.2.2.2.2)
          (prune_clamp_le_quantum rawSteps (64 : UInt64))
      And.intro hPin hPrune

    theorem capture_preserves_inv (req : UInt64) (s sNext : LastViewHistoryState)
        (hInv : LastViewSafetyInv s) (hAct : CaptureView req s sNext) :
        LastViewSafetyInv sNext :=
      let hGeAvail : Nat.le (UInt64.toNat s.avail) (UInt64.toNat req) :=
        window_admits_ge_avail s.avail s.pubHead req hAct.1
      let hLePub : Nat.le (UInt64.toNat req) (UInt64.toNat s.pubHead) :=
        window_admits_le_pub s.avail s.pubHead req hAct.1
      let hLow : Nat.le (UInt64.toNat sNext.captureAvail) (UInt64.toNat sNext.pinnedVis) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.pinnedVis)) hAct.2.2.2.2.2.1)
          (Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat s.avail) (UInt64.toNat x)) hAct.2.2.2.2.1)
            hGeAvail)
      let hHigh : Nat.le (UInt64.toNat sNext.pinnedVis) (UInt64.toNat sNext.capturePub) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.capturePub)) hAct.2.2.2.2.1)
          (Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat req) (UInt64.toNat x)) hAct.2.2.2.2.2.2.1)
            hLePub)
      let hMonoAvail : Nat.le (UInt64.toNat sNext.captureAvail) (UInt64.toNat sNext.avail) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.avail)) hAct.2.2.2.2.2.1)
          (Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat s.avail) (UInt64.toNat x)) hAct.2.1)
            (Nat.le.refl (UInt64.toNat s.avail)))
      let hPrune : Nat.le (UInt64.toNat sNext.lastPruneSteps) (UInt64.toNat (64 : UInt64)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (64 : UInt64))) hAct.2.2.2.2.2.2.2)
          hInv.2
      And.intro
        (Or.inr (And.intro hAct.2.2.2.1 (And.intro hLow (And.intro hHigh hMonoAvail))))
        hPrune

    theorem release_preserves_inv (s sNext : LastViewHistoryState)
        (hInv : LastViewSafetyInv s) (hAct : ReleaseView s sNext) :
        LastViewSafetyInv sNext :=
      let hPrune : Nat.le (UInt64.toNat sNext.lastPruneSteps) (UInt64.toNat (64 : UInt64)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (64 : UInt64))) hAct.2.2.2.2.2.2)
          hInv.2
      And.intro (Or.inl hAct.2.2.1) hPrune

    theorem next_preserves_inv (s sNext : LastViewHistoryState)
        (hInv : LastViewSafetyInv s) (hNext : Next s sNext) :
        LastViewSafetyInv sNext :=
      Or.elim hNext
        (fun hEx => Exists.elim hEx (fun q hAct => startLower_preserves_inv q s sNext hInv hAct))
        (fun hR1 =>
          Or.elim hR1
            (fun hEx =>
              Exists.elim hEx (fun vis hEx2 =>
                Exists.elim hEx2 (fun steps hAct =>
                  advance_preserves_inv vis steps s sNext hInv hAct)))
            (fun hR2 =>
              Or.elim hR2
                (fun hEx => Exists.elim hEx (fun req hAct => capture_preserves_inv req s sNext hInv hAct))
                (fun hAct => release_preserves_inv s sNext hInv hAct)))

    theorem spec_satisfies_last_view_safety :
        Spec ⊨ □ (Lift LastViewSafetyInv) :=
      invariantSatisfies Spec LastViewSafetyInv init_establishes_inv next_preserves_inv

    end TlaLastView
    end Broker
    end Astream

    def last_view_prune_within_quantum_isl (steps : UInt64) (max_work : UInt64) : Bool :=
      decide (steps ≤ max_work)
}
