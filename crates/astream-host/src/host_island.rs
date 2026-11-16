// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `host.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `host.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def pty_reap_state_advance (cur : UInt64) (settled : UInt64) : UInt64 :=
      if cur < settled then settled else cur

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Host.TlaPtyLifecycle)
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaPtyLifecycle

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

    prefix:100 "□" => _root_.Astream.Host.TlaPtyLifecycle.Always
    infixl:45 " ⊨ " => _root_.Astream.Host.TlaPtyLifecycle.Satisfies

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

    structure PtyLifecycleState where
      reapState     : UInt64
      prevReapState : UInt64

    def PtyReapMonotoneInv (s : PtyLifecycleState) : Prop :=
      Nat.le (UInt64.toNat s.prevReapState) (UInt64.toNat s.reapState)

    def Init (s : PtyLifecycleState) : Prop :=
      s.reapState = 0 ∧ s.prevReapState = 0

    def settleAction (settled : UInt64) (s sNext : PtyLifecycleState) : Prop :=
      sNext.prevReapState = s.reapState ∧
      sNext.reapState = _root_.pty_reap_state_advance s.reapState settled

    def Next (s sNext : PtyLifecycleState) : Prop :=
      ∃ settled : UInt64, settleAction settled s sNext

    def Spec : StateMachine PtyLifecycleState :=
      StateMachine.mk Init Next

    theorem advance_ge_cur (cur settled : UInt64) :
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.pty_reap_state_advance cur settled)) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur settled)) =>
          Nat.le (UInt64.toNat cur)
            (UInt64.toNat (@ite UInt64 (LT.lt cur settled) d settled cur)))
        (instDecidableUInt64Lt cur settled)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : PtyLifecycleState) (hInit : Init s) :
        PtyReapMonotoneInv s :=
      uint64_eq_le s.prevReapState s.reapState (Eq.trans hInit.2 (Eq.symm hInit.1))

    theorem next_preserves_inv (s sNext : PtyLifecycleState)
        (_hInv : PtyReapMonotoneInv s) (hNext : Next s sNext) :
        PtyReapMonotoneInv sNext :=
      Exists.elim hNext (fun settled hAct =>
        let hPrev : Nat.le (UInt64.toNat sNext.prevReapState) (UInt64.toNat s.reapState) :=
          uint64_eq_le sNext.prevReapState s.reapState hAct.1
        let hAdv : Nat.le (UInt64.toNat s.reapState) (UInt64.toNat (_root_.pty_reap_state_advance s.reapState settled)) :=
          advance_ge_cur s.reapState settled
        let hStep : Nat.le (UInt64.toNat (_root_.pty_reap_state_advance s.reapState settled)) (UInt64.toNat sNext.reapState) :=
          uint64_eq_le (_root_.pty_reap_state_advance s.reapState settled) sNext.reapState (Eq.symm hAct.2)
        Nat.le_trans hPrev (Nat.le_trans hAdv hStep))

    theorem spec_satisfies_pty_reap_monotonicity :
        Spec ⊨ □ (Lift PtyReapMonotoneInv) :=
      invariantSatisfies Spec PtyReapMonotoneInv init_establishes_inv next_preserves_inv

    end TlaPtyLifecycle
    end Host
    end Astream

    def pty_chunk_non_empty_isl (n : USize) : Bool :=
      decide (0 < n)
}
