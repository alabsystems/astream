// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `bin/asb.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `bin/asb.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `bin/islands/asb_twins.rs` of the
// function it compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def asb_drain_count_advance (cur : UInt64) (next : UInt64) : UInt64 :=
      if cur < next then next else cur

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaAsbCli)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaAsbCli

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaAsbCli.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaAsbCli.Always

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

    structure AsbDrainState where
      prevCount : UInt64
      curCount  : UInt64

    def AsbDrainMonotoneInv (s : AsbDrainState) : Prop :=
      Nat.le (UInt64.toNat s.prevCount) (UInt64.toNat s.curCount)

    def Init (s : AsbDrainState) : Prop :=
      s.prevCount = s.curCount

    def stepDrainAction (cand : UInt64) (s sNext : AsbDrainState) : Prop :=
      sNext.prevCount = s.curCount ∧
      sNext.curCount = _root_.asb_drain_count_advance s.curCount cand

    def Next (s sNext : AsbDrainState) : Prop :=
      ∃ cand : UInt64, stepDrainAction cand s sNext

    def Spec : StateMachine AsbDrainState :=
      StateMachine.mk Init Next

    theorem advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.asb_drain_count_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : AsbDrainState) (hInit : Init s) :
        AsbDrainMonotoneInv s :=
      uint64_eq_le s.prevCount s.curCount hInit

    theorem next_preserves_inv (s sNext : AsbDrainState)
        (_hInv : AsbDrainMonotoneInv s) (hNext : Next s sNext) :
        AsbDrainMonotoneInv sNext :=
      Exists.elim hNext (fun cand hAct =>
        let hAdv : Nat.le (UInt64.toNat s.curCount) (UInt64.toNat (_root_.asb_drain_count_advance s.curCount cand)) :=
          advance_ge_cur s.curCount cand
        let hEqPrev : sNext.prevCount = s.curCount := hAct.1
        let hEqCur : sNext.curCount = _root_.asb_drain_count_advance s.curCount cand := hAct.2
        Eq.mpr
          (congrArg (fun (p : UInt64) => Nat.le (UInt64.toNat p) (UInt64.toNat sNext.curCount)) hEqPrev)
          (Eq.mpr
            (congrArg (fun (c : UInt64) => Nat.le (UInt64.toNat s.curCount) (UInt64.toNat c)) hEqCur)
            hAdv))

    theorem spec_satisfies_asb_drain_monotonicity :
        Spec ⊨ □ (Lift AsbDrainMonotoneInv) :=
      invariantSatisfies Spec AsbDrainMonotoneInv init_establishes_inv next_preserves_inv

    end TlaAsbCli
    end Broker
    end Astream

    def asb_exit_code_valid_isl (code : UInt8) : Bool :=
      decide (code ≤ 2)
}
