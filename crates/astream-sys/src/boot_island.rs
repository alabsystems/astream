// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `lib.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `lib.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def boot_nibble_advance (cur : UInt64) (cand : UInt64) : UInt64 :=
      if cur < cand then cand else cur

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Sys.TlaBootSession)
    -- ========================================================================
    namespace Astream
    namespace Sys
    namespace TlaBootSession

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

    prefix:100 "□" => _root_.Astream.Sys.TlaBootSession.Always
    infixl:45 " ⊨ " => _root_.Astream.Sys.TlaBootSession.Satisfies

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

    structure BootScanState where
      nibbles     : UInt64
      prevNibbles : UInt64

    def BootNibbleMonotoneInv (s : BootScanState) : Prop :=
      Nat.le (UInt64.toNat s.prevNibbles) (UInt64.toNat s.nibbles)

    def Init (s : BootScanState) : Prop :=
      s.nibbles = 0 ∧ s.prevNibbles = 0

    def scanDigitAction (cand : UInt64) (s sNext : BootScanState) : Prop :=
      sNext.prevNibbles = s.nibbles ∧
      sNext.nibbles = _root_.boot_nibble_advance s.nibbles cand

    def Next (s sNext : BootScanState) : Prop :=
      ∃ cand : UInt64, scanDigitAction cand s sNext

    def Spec : StateMachine BootScanState :=
      StateMachine.mk Init Next

    theorem advance_ge_cur (cur cand : UInt64) :
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.boot_nibble_advance cur cand)) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur)
            (UInt64.toNat (@ite UInt64 (LT.lt cur cand) d cand cur)))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : BootScanState) (hInit : Init s) :
        BootNibbleMonotoneInv s :=
      uint64_eq_le s.prevNibbles s.nibbles (Eq.trans hInit.2 (Eq.symm hInit.1))

    theorem next_preserves_inv (s sNext : BootScanState)
        (_hInv : BootNibbleMonotoneInv s) (hNext : Next s sNext) :
        BootNibbleMonotoneInv sNext :=
      Exists.elim hNext (fun cand hAct =>
        let hPrev : Nat.le (UInt64.toNat sNext.prevNibbles) (UInt64.toNat s.nibbles) :=
          uint64_eq_le sNext.prevNibbles s.nibbles hAct.1
        let hAdv : Nat.le (UInt64.toNat s.nibbles) (UInt64.toNat (_root_.boot_nibble_advance s.nibbles cand)) :=
          advance_ge_cur s.nibbles cand
        let hStep : Nat.le (UInt64.toNat (_root_.boot_nibble_advance s.nibbles cand)) (UInt64.toNat sNext.nibbles) :=
          uint64_eq_le (_root_.boot_nibble_advance s.nibbles cand) sNext.nibbles (Eq.symm hAct.2)
        Nat.le_trans hPrev (Nat.le_trans hAdv hStep))

    theorem spec_satisfies_boot_nibble_monotonicity :
        Spec ⊨ □ (Lift BootNibbleMonotoneInv) :=
      invariantSatisfies Spec BootNibbleMonotoneInv init_establishes_inv next_preserves_inv

    end TlaBootSession
    end Sys
    end Astream

    def boot_nibble_count_valid_isl (nibbles : USize) : Bool :=
      decide (nibbles = 32)
}
