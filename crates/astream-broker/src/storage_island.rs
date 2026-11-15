// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `storage.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `storage.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def storage_len_advance (cur_len : UInt64) (next_len : UInt64) : UInt64 :=
      if cur_len < next_len then next_len else cur_len

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaStorageSeam)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaStorageSeam

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaStorageSeam.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaStorageSeam.Always

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

    structure StorageLenState where
      prevLen : UInt64
      curLen  : UInt64

    def StorageLenMonotoneInv (s : StorageLenState) : Prop :=
      Nat.le (UInt64.toNat s.prevLen) (UInt64.toNat s.curLen)

    def Init (s : StorageLenState) : Prop :=
      s.prevLen = s.curLen

    def appendBytesAction (cand : UInt64) (s sNext : StorageLenState) : Prop :=
      sNext.prevLen = s.curLen ∧
      sNext.curLen = _root_.storage_len_advance s.curLen cand

    def Next (s sNext : StorageLenState) : Prop :=
      ∃ cand : UInt64, appendBytesAction cand s sNext

    def Spec : StateMachine StorageLenState :=
      StateMachine.mk Init Next

    theorem advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.storage_len_advance cur cand)) :=
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

    theorem init_establishes_inv (s : StorageLenState) (hInit : Init s) :
        StorageLenMonotoneInv s :=
      uint64_eq_le s.prevLen s.curLen hInit

    theorem next_preserves_inv (s sNext : StorageLenState)
        (_hInv : StorageLenMonotoneInv s) (hNext : Next s sNext) :
        StorageLenMonotoneInv sNext :=
      Exists.elim hNext (fun cand hAct =>
        let hAdv : Nat.le (UInt64.toNat s.curLen) (UInt64.toNat (_root_.storage_len_advance s.curLen cand)) :=
          advance_ge_cur s.curLen cand
        let hEqPrev : sNext.prevLen = s.curLen := hAct.1
        let hEqCur : sNext.curLen = _root_.storage_len_advance s.curLen cand := hAct.2
        Eq.mpr
          (congrArg (fun (p : UInt64) => Nat.le (UInt64.toNat p) (UInt64.toNat sNext.curLen)) hEqPrev)
          (Eq.mpr
            (congrArg (fun (c : UInt64) => Nat.le (UInt64.toNat s.curLen) (UInt64.toNat c)) hEqCur)
            hAdv))

    theorem spec_satisfies_storage_append_monotonicity :
        Spec ⊨ □ (Lift StorageLenMonotoneInv) :=
      invariantSatisfies Spec StorageLenMonotoneInv init_establishes_inv next_preserves_inv

    end TlaStorageSeam
    end Broker
    end Astream

    def storage_truncate_within_len_isl (target : UInt64) (current : UInt64) : Bool :=
      decide (target ≤ current)
}
