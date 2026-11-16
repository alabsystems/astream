// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `lib.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `lib.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn pump_offset_monotone`) and verified by `Faithful`.
    -- ========================================================================

    -- Monotone pump delivery & commit offset advance (`max(cur_off, deliv_off)`).
    def pump_offset_monotone (cur_off : UInt64) (deliv_off : UInt64) : UInt64 :=
      if cur_off < deliv_off then deliv_off else cur_off

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Pump.TlaPumpCursor)
    -- ========================================================================
    namespace Astream
    namespace Pump
    namespace TlaPumpCursor

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

    prefix:100 "□" => _root_.Astream.Pump.TlaPumpCursor.Always
    infixl:45 " ⊨ " => _root_.Astream.Pump.TlaPumpCursor.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      @Nat.rec (fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun step => hStep (b k) (b (Nat.succ k)) ih step)
            (fun stutter => Eq.mpr (congrArg I stutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    theorem pump_offset_ge_cur : forall (cur_off : UInt64) (deliv_off : UInt64),
        Nat.le (UInt64.toNat cur_off) (UInt64.toNat (_root_.pump_offset_monotone cur_off deliv_off)) :=
      fun cur deliv => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur deliv)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => deliv))))
        (instDecidableUInt64Lt cur deliv)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem pump_offset_lub (cur req bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hReq : Nat.le (UInt64.toNat req) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.pump_offset_monotone cur req)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur req)
        (fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur req) d req cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur req)
        (fun _ => hCur)
        (fun _ => hReq)

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Drive-Pipe Pump Cursor & Resume Agreement
    -- ========================================================================
    -- State of a pump cursor over a broker stream:
    --   hasDelivery     : 0 = None yet, 1 = Delivered at least one record
    --   lastOffset      : broker offset of the most recent delivery (`UInt64`)
    --   nextOffset      : offset a restarted pump attaches from (`lastOffset + 1`)
    --   hasCommitted    : 0 = Uncommitted, 1 = Committed at least once
    --   committedOffset : durable group cursor (`upto` inclusive, `UInt64`)
    structure PumpCursorState where
      hasDelivery     : Nat
      lastOffset      : UInt64
      nextOffset      : Nat
      hasCommitted    : Nat
      committedOffset : UInt64

    -- TLA+ Safety Invariant:
    -- 1. Once a delivery has arrived (`hasDelivery = 1`), `nextOffset = lastOffset + 1`.
    -- 2. Any committed group cursor (`hasCommitted = 1`) requires a prior delivery
    --    (`hasDelivery = 1`) and never exceeds `lastOffset` (`committedOffset <= lastOffset`).
    def PumpCursorSafetyInv (s : PumpCursorState) : Prop :=
      (s.hasDelivery = 1 → s.nextOffset = Nat.succ (UInt64.toNat s.lastOffset)) ∧
      (s.hasCommitted = 1 →
        (s.hasDelivery = 1 ∧ Nat.le (UInt64.toNat s.committedOffset) (UInt64.toNat s.lastOffset)))

    def Init (fromOffset : Nat) (s : PumpCursorState) : Prop :=
      s.hasDelivery = 0 ∧
      s.lastOffset = 0 ∧
      s.nextOffset = fromOffset ∧
      s.hasCommitted = 0 ∧
      s.committedOffset = 0

    -- Action 1: Deliver — receive record at `off` and advance `lastOffset` via
    -- Clean-origin `_root_.pump_offset_monotone`.
    def Deliver (off : UInt64) (s sNext : PumpCursorState) : Prop :=
      sNext.hasDelivery = 1 ∧
      sNext.lastOffset = _root_.pump_offset_monotone s.lastOffset off ∧
      sNext.nextOffset = Nat.succ (UInt64.toNat (_root_.pump_offset_monotone s.lastOffset off)) ∧
      sNext.hasCommitted = s.hasCommitted ∧
      sNext.committedOffset = s.committedOffset

    -- Action 2: CommitCursor — commit durable cursor through `lastOffset` via
    -- Clean-origin `_root_.pump_offset_monotone`.
    def CommitCursor (s sNext : PumpCursorState) : Prop :=
      s.hasDelivery = 1 ∧
      Nat.le (UInt64.toNat s.committedOffset) (UInt64.toNat s.lastOffset) ∧
      sNext.hasDelivery = 1 ∧
      sNext.lastOffset = s.lastOffset ∧
      sNext.nextOffset = s.nextOffset ∧
      sNext.hasCommitted = 1 ∧
      sNext.committedOffset = _root_.pump_offset_monotone s.committedOffset s.lastOffset

    def Next (s sNext : PumpCursorState) : Prop :=
      (∃ off : UInt64, Deliver off s sNext) ∨
        CommitCursor s sNext

    def Spec (fromOffset : Nat) : StateMachine PumpCursorState :=
      StateMachine.mk (Init fromOffset) Next

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (fromOffset : Nat) (s : PumpCursorState)
        (hInit : Init fromOffset s) : PumpCursorSafetyInv s :=
      And.intro
        (fun hDel1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.1) hDel1
          False.elim (zero_ne_one h01))
        (fun hCom1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2.2.1) hCom1
          False.elim (zero_ne_one h01))

    theorem deliver_preserves_inv (off : UInt64) (s sNext : PumpCursorState)
        (hInv : PumpCursorSafetyInv s) (hAct : Deliver off s sNext) :
        PumpCursorSafetyInv sNext :=
      let hMono : Nat.le (UInt64.toNat s.lastOffset) (UInt64.toNat (_root_.pump_offset_monotone s.lastOffset off)) :=
        pump_offset_ge_cur s.lastOffset off
      let hDelNext : sNext.hasDelivery = 1 := hAct.1
      let hLastNext : sNext.lastOffset = _root_.pump_offset_monotone s.lastOffset off := hAct.2.1
      let hNextOff : sNext.nextOffset = Nat.succ (UInt64.toNat (_root_.pump_offset_monotone s.lastOffset off)) := hAct.2.2.1
      let hComEq : sNext.hasCommitted = s.hasCommitted := hAct.2.2.2.1
      let hComOffEq : sNext.committedOffset = s.committedOffset := hAct.2.2.2.2
      And.intro
        (fun _ =>
          Eq.trans hNextOff (congrArg (fun x => Nat.succ (UInt64.toNat x)) (Eq.symm hLastNext)))
        (fun hComNext =>
          let hComOld : s.hasCommitted = 1 := Eq.trans (Eq.symm hComEq) hComNext
          let hPre := hInv.2 hComOld
          let hLeOld : Nat.le (UInt64.toNat s.committedOffset) (UInt64.toNat (_root_.pump_offset_monotone s.lastOffset off)) :=
            Nat.le_trans hPre.2 hMono
          let hLe1 : Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat (_root_.pump_offset_monotone s.lastOffset off)) :=
            Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (_root_.pump_offset_monotone s.lastOffset off))) hComOffEq) hLeOld
          let hLeNext : Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat sNext.lastOffset) :=
            Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat y)) hLastNext) hLe1
          And.intro hDelNext hLeNext)

    theorem commitCursor_preserves_inv (s sNext : PumpCursorState)
        (hInv : PumpCursorSafetyInv s) (hAct : CommitCursor s sNext) :
        PumpCursorSafetyInv sNext :=
      let hDelOld : s.hasDelivery = 1 := hAct.1
      let hComLeLast : Nat.le (UInt64.toNat s.committedOffset) (UInt64.toNat s.lastOffset) := hAct.2.1
      let hDelNext : sNext.hasDelivery = 1 := hAct.2.2.1
      let hLastEq : sNext.lastOffset = s.lastOffset := hAct.2.2.2.1
      let hNextEq : sNext.nextOffset = s.nextOffset := hAct.2.2.2.2.1
      let hComOffEq : sNext.committedOffset = _root_.pump_offset_monotone s.committedOffset s.lastOffset := hAct.2.2.2.2.2.2
      let hRefl : Nat.le (UInt64.toNat s.lastOffset) (UInt64.toNat s.lastOffset) :=
        Nat.le_refl (UInt64.toNat s.lastOffset)
      let hLub : Nat.le (UInt64.toNat (_root_.pump_offset_monotone s.committedOffset s.lastOffset)) (UInt64.toNat s.lastOffset) :=
        pump_offset_lub s.committedOffset s.lastOffset s.lastOffset hComLeLast hRefl
      let hLe1 : Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat s.lastOffset) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.lastOffset)) hComOffEq) hLub
      let hLeNext : Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat sNext.lastOffset) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedOffset) (UInt64.toNat y)) hLastEq) hLe1
      And.intro
        (fun _ =>
          let hNextOld : s.nextOffset = Nat.succ (UInt64.toNat s.lastOffset) := hInv.1 hDelOld
          Eq.trans hNextEq (Eq.trans hNextOld (congrArg (fun x => Nat.succ (UInt64.toNat x)) (Eq.symm hLastEq))))
        (fun _ => And.intro hDelNext hLeNext)

    theorem next_preserves_inv (s sNext : PumpCursorState)
        (hInv : PumpCursorSafetyInv s) (hNext : Next s sNext) :
        PumpCursorSafetyInv sNext :=
      Or.elim hNext
        (fun hEx =>
          Exists.elim hEx (fun off hDel =>
            deliver_preserves_inv off s sNext hInv hDel))
        (fun hCom => commitCursor_preserves_inv s sNext hInv hCom)

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec fromOffset) ⊨ □ (Lift PumpCursorSafetyInv)`
    theorem spec_satisfies_pump_cursor_safety (fromOffset : Nat) :
        (Spec fromOffset) ⊨ □ (Lift PumpCursorSafetyInv) :=
      invariantSatisfies (Spec fromOffset) PumpCursorSafetyInv
        (init_establishes_inv fromOffset)
        next_preserves_inv

    end TlaPumpCursor
    end Pump
    end Astream

    def cursor_already_committed_isl (committed : UInt64) (upto : UInt64) : Bool :=
      decide (upto ≤ committed)
}
