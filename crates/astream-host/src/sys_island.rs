// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `sys.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `sys.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def sys_stdio_fd_floor (min_fd : UInt64) (fd : UInt64) : UInt64 :=
      if min_fd < fd then fd else min_fd

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Host.TlaPtySys)
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaPtySys

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

    prefix:100 "□" => _root_.Astream.Host.TlaPtySys.Always
    infixl:45 " ⊨ " => _root_.Astream.Host.TlaPtySys.Satisfies

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

    structure FdFloorState where
      curFd : UInt64
      minFd : UInt64

    def StdioFdFloorInv (s : FdFloorState) : Prop :=
      Nat.le (UInt64.toNat s.minFd) (UInt64.toNat s.curFd)

    def Init (s : FdFloorState) : Prop :=
      s.curFd = 3 ∧ s.minFd = 3

    def moveAboveStdioAction (rawFd : UInt64) (s sNext : FdFloorState) : Prop :=
      sNext.minFd = s.minFd ∧
      sNext.curFd = _root_.sys_stdio_fd_floor s.minFd rawFd

    def Next (s sNext : FdFloorState) : Prop :=
      ∃ rawFd : UInt64, moveAboveStdioAction rawFd s sNext

    def Spec : StateMachine FdFloorState :=
      StateMachine.mk Init Next

    theorem floor_ge_min (min_fd fd : UInt64) :
        Nat.le (UInt64.toNat min_fd) (UInt64.toNat (_root_.sys_stdio_fd_floor min_fd fd)) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt min_fd fd)) =>
          Nat.le (UInt64.toNat min_fd)
            (UInt64.toNat (@ite UInt64 (LT.lt min_fd fd) d fd min_fd)))
        (instDecidableUInt64Lt min_fd fd)
        (fun _ => @Nat.le.refl (UInt64.toNat min_fd))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : FdFloorState) (hInit : Init s) :
        StdioFdFloorInv s :=
      uint64_eq_le s.minFd s.curFd (Eq.trans hInit.2 (Eq.symm hInit.1))

    theorem next_preserves_inv (s sNext : FdFloorState)
        (_hInv : StdioFdFloorInv s) (hNext : Next s sNext) :
        StdioFdFloorInv sNext :=
      Exists.elim hNext (fun rawFd hAct =>
        let hMin : Nat.le (UInt64.toNat sNext.minFd) (UInt64.toNat s.minFd) :=
          uint64_eq_le sNext.minFd s.minFd hAct.1
        let hFl : Nat.le (UInt64.toNat s.minFd) (UInt64.toNat (_root_.sys_stdio_fd_floor s.minFd rawFd)) :=
          floor_ge_min s.minFd rawFd
        let hCur : Nat.le (UInt64.toNat (_root_.sys_stdio_fd_floor s.minFd rawFd)) (UInt64.toNat sNext.curFd) :=
          uint64_eq_le (_root_.sys_stdio_fd_floor s.minFd rawFd) sNext.curFd (Eq.symm hAct.2)
        Nat.le_trans hMin (Nat.le_trans hFl hCur))

    theorem spec_satisfies_stdio_fd_floor :
        Spec ⊨ □ (Lift StdioFdFloorInv) :=
      invariantSatisfies Spec StdioFdFloorInv init_establishes_inv next_preserves_inv

    end TlaPtySys
    end Host
    end Astream

    def sys_exec_status_complete_isl (got : USize) : Bool :=
      decide (got = 4)
}
