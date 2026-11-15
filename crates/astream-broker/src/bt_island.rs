// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for broker-stamped monotone wall time (`REQUIREMENTS` R3), mounted under
// `cfg(clean_islands)` in `store.rs`. Proves that `broker_bt_advance` preserves monotone
// `bt` stamps (`prevBt <= curBt`) even when the host wall clock steps backward (`wallMs < curBt`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def broker_bt_advance (prev_bt : UInt64) (wall_ms : UInt64) : UInt64 :=
      if prev_bt < wall_ms then wall_ms else prev_bt

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaMonotoneBrokerTime)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaMonotoneBrokerTime

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaMonotoneBrokerTime.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaMonotoneBrokerTime.Always

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

    structure BtClockState where
      prevBt : UInt64
      curBt  : UInt64

    def MonotoneBtInv (s : BtClockState) : Prop :=
      Nat.le (UInt64.toNat s.prevBt) (UInt64.toNat s.curBt)

    def Init (s : BtClockState) : Prop :=
      s.prevBt = s.curBt

    def stampRecordAction (wallMs : UInt64) (s sNext : BtClockState) : Prop :=
      sNext.prevBt = s.curBt ∧
      sNext.curBt = _root_.broker_bt_advance s.curBt wallMs

    def Next (s sNext : BtClockState) : Prop :=
      ∃ wallMs : UInt64, stampRecordAction wallMs s sNext

    def Spec : StateMachine BtClockState :=
      StateMachine.mk Init Next

    theorem bt_advance_ge_prev : forall (prev : UInt64) (wall : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.broker_bt_advance prev wall)) :=
      fun prev wall => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev wall)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => wall))))
        (instDecidableUInt64Lt prev wall)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : BtClockState) (hInit : Init s) :
        MonotoneBtInv s :=
      uint64_eq_le s.prevBt s.curBt hInit

    theorem next_preserves_inv (s sNext : BtClockState)
        (_hInv : MonotoneBtInv s) (hNext : Next s sNext) :
        MonotoneBtInv sNext :=
      Exists.elim hNext (fun wallMs hAct =>
        let hAdv : Nat.le (UInt64.toNat s.curBt) (UInt64.toNat (_root_.broker_bt_advance s.curBt wallMs)) :=
          bt_advance_ge_prev s.curBt wallMs
        let hEqPrev : sNext.prevBt = s.curBt := hAct.1
        let hEqCur : sNext.curBt = _root_.broker_bt_advance s.curBt wallMs := hAct.2
        Eq.mpr
          (congrArg (fun (p : UInt64) => Nat.le (UInt64.toNat p) (UInt64.toNat sNext.curBt)) hEqPrev)
          (Eq.mpr
            (congrArg (fun (c : UInt64) => Nat.le (UInt64.toNat s.curBt) (UInt64.toNat c)) hEqCur)
            hAdv))

    theorem spec_satisfies_monotone_broker_time :
        Spec ⊨ □ (Lift MonotoneBtInv) :=
      invariantSatisfies Spec MonotoneBtInv init_establishes_inv next_preserves_inv

    end TlaMonotoneBrokerTime
    end Broker
    end Astream

    def bt_is_monotone_isl (prev_bt : UInt64) (next_bt : UInt64) : Bool :=
      decide (prev_bt ≤ next_bt)
}
