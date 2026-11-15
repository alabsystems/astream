// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for multi-lane coalesced refill planning & cost-bounded handoff
// (`Astream.Broker.TlaSharedRefill`), mounted under `cfg(clean_islands)` in `refill.rs`
// (`aterm-link` `SPECS.md` critic item B09 `inbox-delivery-accounting`).
// Proves over `refill_join_cursor_max` and `refill_debt_clamp` that:
// 1. `inboxOldest <= sharedCursor` (the shared refill never starts or regresses below
//    the node inbox's retention floor — refuting `Mutant::RefillJoinBelowTheOldest`),
// 2. `activeDebt <= maxSlack` (while reading together, excess unowed cost never exceeds
//    `REFILL_SPLIT_SLACK`; exceeding it transitions cleanly to `HandedOn` per-lane reads),
// 3. `phase <= 2` across all transitions (`PerLaneBelowOldest -> SharedTogether -> HandedOn`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def refill_join_cursor_max (lane_from : UInt64) (inbox_oldest : UInt64) : UInt64 :=
      if inbox_oldest < lane_from then lane_from else inbox_oldest

    def refill_debt_clamp (debt : UInt64) (slack : UInt64) : UInt64 :=
      if debt < slack then debt else slack

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Broker.TlaSharedRefill)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaSharedRefill

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaSharedRefill.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaSharedRefill.Always

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
    -- 3. Multi-Lane Coalesced Refill Kernel Lemmas & State Machine
    -- ========================================================================

    theorem refill_join_ge_oldest (laneFrom oldest : UInt64) :
        Nat.le (UInt64.toNat oldest) (UInt64.toNat (_root_.refill_join_cursor_max laneFrom oldest)) :=
      @Decidable.casesOn (LT.lt oldest laneFrom)
        (fun (d : Decidable (LT.lt oldest laneFrom)) =>
          Nat.le (UInt64.toNat oldest) (UInt64.toNat (@ite UInt64 (LT.lt oldest laneFrom) d laneFrom oldest)))
        (instDecidableUInt64Lt oldest laneFrom)
        (fun _ => Nat.le_refl (UInt64.toNat oldest))
        (fun hLt => Nat.le_of_lt hLt)

    theorem refill_debt_clamp_le_slack (debt slack : UInt64) :
        Nat.le (UInt64.toNat (_root_.refill_debt_clamp debt slack)) (UInt64.toNat slack) :=
      @Decidable.casesOn (LT.lt debt slack)
        (fun (d : Decidable (LT.lt debt slack)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt debt slack) d debt slack)) (UInt64.toNat slack))
        (instDecidableUInt64Lt debt slack)
        (fun _ => Nat.le_refl (UInt64.toNat slack))
        (fun hLt => Nat.le_of_lt hLt)

    structure SharedRefillState where
      phase        : Nat
      inboxOldest  : UInt64
      sharedCursor : UInt64
      activeDebt   : UInt64
      maxSlack     : UInt64

    def SharedRefillSafetyInv (s : SharedRefillState) : Prop :=
      Nat.le (UInt64.toNat s.inboxOldest) (UInt64.toNat s.sharedCursor) ∧
      Nat.le (UInt64.toNat s.activeDebt) (UInt64.toNat s.maxSlack) ∧
      Nat.le s.phase 2

    def Init (oldest minFrom slack : UInt64) (s : SharedRefillState) : Prop :=
      s.phase = 0 ∧
      s.inboxOldest = oldest ∧
      s.sharedCursor = _root_.refill_join_cursor_max minFrom oldest ∧
      s.activeDebt = (0 : UInt64) ∧
      s.maxSlack = slack

    def BeginSharedRead (s sNext : SharedRefillState) : Prop :=
      s.phase = 0 ∧
      sNext.phase = 1 ∧
      sNext.inboxOldest = s.inboxOldest ∧
      sNext.sharedCursor = s.sharedCursor ∧
      sNext.activeDebt = (0 : UInt64) ∧
      sNext.maxSlack = s.maxSlack

    def AdvanceSharedPage (nextCur rawDebt : UInt64) (s sNext : SharedRefillState) : Prop :=
      s.phase = 1 ∧
      Nat.le (UInt64.toNat s.sharedCursor) (UInt64.toNat nextCur) ∧
      Nat.le (UInt64.toNat rawDebt) (UInt64.toNat s.maxSlack) ∧
      sNext.phase = 1 ∧
      sNext.inboxOldest = s.inboxOldest ∧
      sNext.sharedCursor = nextCur ∧
      sNext.activeDebt = _root_.refill_debt_clamp rawDebt s.maxSlack ∧
      sNext.maxSlack = s.maxSlack

    def HandOnToPerLane (nextCur : UInt64) (s sNext : SharedRefillState) : Prop :=
      s.phase = 1 ∧
      Nat.le (UInt64.toNat s.sharedCursor) (UInt64.toNat nextCur) ∧
      sNext.phase = 2 ∧
      sNext.inboxOldest = s.inboxOldest ∧
      sNext.sharedCursor = nextCur ∧
      sNext.activeDebt = s.activeDebt ∧
      sNext.maxSlack = s.maxSlack

    def Next (s sNext : SharedRefillState) : Prop :=
      BeginSharedRead s sNext ∨
      ((∃ nc : UInt64, ∃ rd : UInt64, AdvanceSharedPage nc rd s sNext) ∨
       (∃ nc : UInt64, HandOnToPerLane nc s sNext))

    def Spec (oldest minFrom slack : UInt64) : StateMachine SharedRefillState :=
      StateMachine.mk (Init oldest minFrom slack) Next

    theorem init_establishes_inv (oldest minFrom slack : UInt64) (s : SharedRefillState)
        (hInit : Init oldest minFrom slack s) : SharedRefillSafetyInv s :=
      let hJoin : Nat.le (UInt64.toNat oldest) (UInt64.toNat (_root_.refill_join_cursor_max minFrom oldest)) :=
        refill_join_ge_oldest minFrom oldest
      let hCur1 : Nat.le (UInt64.toNat oldest) (UInt64.toNat s.sharedCursor) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat oldest) (UInt64.toNat c)) hInit.2.2.1) hJoin
      let hCur : Nat.le (UInt64.toNat s.inboxOldest) (UInt64.toNat s.sharedCursor) :=
        Eq.mpr (congrArg (fun o => Nat.le (UInt64.toNat o) (UInt64.toNat s.sharedCursor)) hInit.2.1) hCur1
      let hDebt0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.maxSlack) :=
        Nat.zero_le (UInt64.toNat s.maxSlack)
      let hDebt : Nat.le (UInt64.toNat s.activeDebt) (UInt64.toNat s.maxSlack) :=
        Eq.mpr (congrArg (fun d => Nat.le (UInt64.toNat d) (UInt64.toNat s.maxSlack)) hInit.2.2.2.1) hDebt0
      let hPh : Nat.le s.phase 2 :=
        Eq.mpr (congrArg (fun p => Nat.le p 2) hInit.1) (Nat.zero_le 2)
      And.intro hCur (And.intro hDebt hPh)

    theorem beginShared_preserves_inv (s sNext : SharedRefillState)
        (hInv : SharedRefillSafetyInv s) (hAct : BeginSharedRead s sNext) :
        SharedRefillSafetyInv sNext :=
      let hCur1 : Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat s.sharedCursor) :=
        Eq.mpr (congrArg (fun o => Nat.le (UInt64.toNat o) (UInt64.toNat s.sharedCursor)) hAct.2.2.1) hInv.1
      let hCur : Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat sNext.sharedCursor) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat c)) hAct.2.2.2.1) hCur1
      let hDebt0 : Nat.le (UInt64.toNat 0) (UInt64.toNat sNext.maxSlack) :=
        Nat.zero_le (UInt64.toNat sNext.maxSlack)
      let hDebt : Nat.le (UInt64.toNat sNext.activeDebt) (UInt64.toNat sNext.maxSlack) :=
        Eq.mpr (congrArg (fun d => Nat.le (UInt64.toNat d) (UInt64.toNat sNext.maxSlack)) hAct.2.2.2.2.1) hDebt0
      let h12 : Nat.le 1 2 := @Nat.le.step 1 1 (Nat.le_refl 1)
      let hPh : Nat.le sNext.phase 2 :=
        Eq.mpr (congrArg (fun p => Nat.le p 2) hAct.2.1) h12
      And.intro hCur (And.intro hDebt hPh)

    theorem advancePage_preserves_inv (nc rd : UInt64) (s sNext : SharedRefillState)
        (hInv : SharedRefillSafetyInv s) (hAct : AdvanceSharedPage nc rd s sNext) :
        SharedRefillSafetyInv sNext :=
      let hMono : Nat.le (UInt64.toNat s.inboxOldest) (UInt64.toNat nc) :=
        Nat.le_trans hInv.1 hAct.2.1
      let hCur1 : Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat nc) :=
        Eq.mpr (congrArg (fun o => Nat.le (UInt64.toNat o) (UInt64.toNat nc)) hAct.2.2.2.2.1) hMono
      let hCur : Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat sNext.sharedCursor) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat c)) hAct.2.2.2.2.2.1) hCur1
      let hClamp : Nat.le (UInt64.toNat (_root_.refill_debt_clamp rd s.maxSlack)) (UInt64.toNat s.maxSlack) :=
        refill_debt_clamp_le_slack rd s.maxSlack
      let hDebt1 : Nat.le (UInt64.toNat sNext.activeDebt) (UInt64.toNat s.maxSlack) :=
        Eq.mpr (congrArg (fun d => Nat.le (UInt64.toNat d) (UInt64.toNat s.maxSlack)) hAct.2.2.2.2.2.2.1) hClamp
      let hDebt : Nat.le (UInt64.toNat sNext.activeDebt) (UInt64.toNat sNext.maxSlack) :=
        Eq.mpr (congrArg (fun m => Nat.le (UInt64.toNat sNext.activeDebt) (UInt64.toNat m)) hAct.2.2.2.2.2.2.2) hDebt1
      let h12 : Nat.le 1 2 := @Nat.le.step 1 1 (Nat.le_refl 1)
      let hPh : Nat.le sNext.phase 2 :=
        Eq.mpr (congrArg (fun p => Nat.le p 2) hAct.2.2.2.1) h12
      And.intro hCur (And.intro hDebt hPh)

    theorem handOn_preserves_inv (nc : UInt64) (s sNext : SharedRefillState)
        (hInv : SharedRefillSafetyInv s) (hAct : HandOnToPerLane nc s sNext) :
        SharedRefillSafetyInv sNext :=
      let hMono : Nat.le (UInt64.toNat s.inboxOldest) (UInt64.toNat nc) :=
        Nat.le_trans hInv.1 hAct.2.1
      let hCur1 : Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat nc) :=
        Eq.mpr (congrArg (fun o => Nat.le (UInt64.toNat o) (UInt64.toNat nc)) hAct.2.2.2.1) hMono
      let hCur : Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat sNext.sharedCursor) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat sNext.inboxOldest) (UInt64.toNat c)) hAct.2.2.2.2.1) hCur1
      let hDebt1 : Nat.le (UInt64.toNat sNext.activeDebt) (UInt64.toNat s.maxSlack) :=
        Eq.mpr (congrArg (fun d => Nat.le (UInt64.toNat d) (UInt64.toNat s.maxSlack)) hAct.2.2.2.2.2.1) hInv.2.1
      let hDebt : Nat.le (UInt64.toNat sNext.activeDebt) (UInt64.toNat sNext.maxSlack) :=
        Eq.mpr (congrArg (fun m => Nat.le (UInt64.toNat sNext.activeDebt) (UInt64.toNat m)) hAct.2.2.2.2.2.2) hDebt1
      let hPh : Nat.le sNext.phase 2 :=
        Eq.mpr (congrArg (fun p => Nat.le p 2) hAct.2.2.1) (Nat.le_refl 2)
      And.intro hCur (And.intro hDebt hPh)

    theorem next_preserves_inv (s sNext : SharedRefillState)
        (hInv : SharedRefillSafetyInv s) (hNext : Next s sNext) :
        SharedRefillSafetyInv sNext :=
      Or.elim hNext
        (fun hAct => beginShared_preserves_inv s sNext hInv hAct)
        (fun hRest =>
          Or.elim hRest
            (fun hEx =>
              Exists.elim hEx (fun nc hEx2 =>
                Exists.elim hEx2 (fun rd hAct => advancePage_preserves_inv nc rd s sNext hInv hAct)))
            (fun hEx => Exists.elim hEx (fun nc hAct => handOn_preserves_inv nc s sNext hInv hAct)))

    theorem spec_satisfies_shared_refill_safety (oldest minFrom slack : UInt64) :
        (Spec oldest minFrom slack) ⊨ □ (Lift SharedRefillSafetyInv) :=
      invariantSatisfies (Spec oldest minFrom slack) SharedRefillSafetyInv
        (init_establishes_inv oldest minFrom slack) next_preserves_inv

    end TlaSharedRefill
    end Broker
    end Astream

    def refill_cursor_at_least_oldest_isl (cursor : UInt64) (inbox_oldest : UInt64) : Bool :=
      decide (inbox_oldest ≤ cursor)
}
