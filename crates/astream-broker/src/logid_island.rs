// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `logid.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `logid.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def logid_generation_advance (cur_gen : UInt64) (next_gen : UInt64) : UInt64 :=
      if cur_gen < next_gen then next_gen else cur_gen

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaLogIdentity)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaLogIdentity

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaLogIdentity.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaLogIdentity.Always

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

    structure LogidGenState where
      prevGen : UInt64
      curGen  : UInt64

    def LogidGenMonotoneInv (s : LogidGenState) : Prop :=
      Nat.le (UInt64.toNat s.prevGen) (UInt64.toNat s.curGen)

    def Init (s : LogidGenState) : Prop :=
      s.prevGen = s.curGen

    def bumpGenAction (cand : UInt64) (s sNext : LogidGenState) : Prop :=
      sNext.prevGen = s.curGen ∧
      sNext.curGen = _root_.logid_generation_advance s.curGen cand

    def Next (s sNext : LogidGenState) : Prop :=
      ∃ cand : UInt64, bumpGenAction cand s sNext

    def Spec : StateMachine LogidGenState :=
      StateMachine.mk Init Next

    theorem advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.logid_generation_advance cur cand)) :=
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

    theorem init_establishes_inv (s : LogidGenState) (hInit : Init s) :
        LogidGenMonotoneInv s :=
      uint64_eq_le s.prevGen s.curGen hInit

    theorem next_preserves_inv (s sNext : LogidGenState)
        (_hInv : LogidGenMonotoneInv s) (hNext : Next s sNext) :
        LogidGenMonotoneInv sNext :=
      Exists.elim hNext (fun cand hAct =>
        let hAdv : Nat.le (UInt64.toNat s.curGen) (UInt64.toNat (_root_.logid_generation_advance s.curGen cand)) :=
          advance_ge_cur s.curGen cand
        let hEqPrev : sNext.prevGen = s.curGen := hAct.1
        let hEqCur : sNext.curGen = _root_.logid_generation_advance s.curGen cand := hAct.2
        Eq.mpr
          (congrArg (fun (p : UInt64) => Nat.le (UInt64.toNat p) (UInt64.toNat sNext.curGen)) hEqPrev)
          (Eq.mpr
            (congrArg (fun (c : UInt64) => Nat.le (UInt64.toNat s.curGen) (UInt64.toNat c)) hEqCur)
            hAdv))

    theorem spec_satisfies_logid_generation_monotonicity :
        Spec ⊨ □ (Lift LogidGenMonotoneInv) :=
      invariantSatisfies Spec LogidGenMonotoneInv init_establishes_inv next_preserves_inv

    end TlaLogIdentity
    end Broker
    end Astream

    def logid_lineage_within_cap_isl (entries : USize) : Bool :=
      decide (entries ≤ 8)
}
