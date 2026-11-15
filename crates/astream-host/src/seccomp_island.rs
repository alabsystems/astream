// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `seccomp.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `seccomp.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    -- ========================================================================

    -- Monotone replay tape cursor advance: never moves backward.
    def seccomp_tape_advance (cur : UInt64) (cand : UInt64) : UInt64 :=
      if cur < cand then cand else cur

    -- Bounded tracee read-buffer length clamp (`min(len, cap)`).
    def seccomp_buf_clamp (len : UInt64) (cap : UInt64) : UInt64 :=
      if len < cap then len else cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Host.TlaSeccompFilter)
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaSeccompFilter

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

    prefix:100 "□" => _root_.Astream.Host.TlaSeccompFilter.Always
    infixl:45 " ⊨ " => _root_.Astream.Host.TlaSeccompFilter.Satisfies

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

    def seccomp_tape_within_len_isl (cursor : UInt64) (tape_len : UInt64) : Bool :=
      decide (cursor ≤ tape_len)

    theorem seccomp_tape_advance_ge_cur : forall (cur cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.seccomp_tape_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem seccomp_buf_clamp_le_cap : forall (len cap : UInt64),
        Nat.le (UInt64.toNat (_root_.seccomp_buf_clamp len cap)) (UInt64.toNat cap) :=
      fun len cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => len))) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun h => Nat.le_of_lt h)

    -- ========================================================================
    -- 3. TLA+ State Machine: Seccomp-BPF Neutralized Replay Safety
    -- ========================================================================
    structure SeccompReplayState where
      cursor        : UInt64
      tapeLen       : UInt64
      injectedBytes : UInt64
      bufCap        : UInt64
      kernelRan     : UInt64

    -- Safety Invariant:
    -- 1. Tape cursor never exceeds `tapeLen`.
    -- 2. Injected payload bytes never exceed tracee buffer capacity `bufCap`.
    -- 3. Intercepted replay syscalls are neutralized (`kernelRan = 0`).
    def SeccompReplaySafetyInv (s : SeccompReplayState) : Prop :=
      Nat.le (UInt64.toNat s.cursor) (UInt64.toNat s.tapeLen) ∧
      Nat.le (UInt64.toNat s.injectedBytes) (UInt64.toNat s.bufCap) ∧
      s.kernelRan = 0

    def Init (s : SeccompReplayState) : Prop :=
      s.cursor = 0 ∧ s.injectedBytes = 0 ∧ s.kernelRan = 0

    def NeutralizeAndInject (nextCursor : UInt64) (rawBytes : UInt64)
        (s sNext : SeccompReplayState) : Prop :=
      sNext.tapeLen = s.tapeLen ∧
      sNext.bufCap = s.bufCap ∧
      sNext.cursor = _root_.seccomp_buf_clamp (_root_.seccomp_tape_advance s.cursor nextCursor) s.tapeLen ∧
      sNext.injectedBytes = _root_.seccomp_buf_clamp rawBytes s.bufCap ∧
      sNext.kernelRan = 0

    def Next (s sNext : SeccompReplayState) : Prop :=
      ∃ nextCursor rawBytes, NeutralizeAndInject nextCursor rawBytes s sNext

    def Spec : StateMachine SeccompReplayState :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : SeccompReplayState) (hInit : Init s) :
        SeccompReplaySafetyInv s :=
      let hZeroCur : Nat.le (UInt64.toNat 0) (UInt64.toNat s.tapeLen) :=
        Nat.zero_le (UInt64.toNat s.tapeLen)
      let hCurLe : Nat.le (UInt64.toNat s.cursor) (UInt64.toNat s.tapeLen) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.tapeLen)) hInit.1) hZeroCur
      let hZeroBytes : Nat.le (UInt64.toNat 0) (UInt64.toNat s.bufCap) :=
        Nat.zero_le (UInt64.toNat s.bufCap)
      let hBytesLe : Nat.le (UInt64.toNat s.injectedBytes) (UInt64.toNat s.bufCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.bufCap)) hInit.2.1) hZeroBytes
      And.intro hCurLe (And.intro hBytesLe hInit.2.2)

    theorem neutralize_preserves_inv (nextCursor rawBytes : UInt64)
        (s sNext : SeccompReplayState)
        (_hInv : SeccompReplaySafetyInv s)
        (hStep : NeutralizeAndInject nextCursor rawBytes s sNext) :
        SeccompReplaySafetyInv sNext :=
      let hCurBounded : Nat.le
          (UInt64.toNat (_root_.seccomp_buf_clamp (_root_.seccomp_tape_advance s.cursor nextCursor) s.tapeLen))
          (UInt64.toNat s.tapeLen) :=
        seccomp_buf_clamp_le_cap (_root_.seccomp_tape_advance s.cursor nextCursor) s.tapeLen
      let hCurSNext : Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat s.tapeLen) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.tapeLen)) hStep.2.2.1) hCurBounded
      let hCurFinal : Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat sNext.tapeLen) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat x)) hStep.1) hCurSNext
      let hBytesBounded : Nat.le
          (UInt64.toNat (_root_.seccomp_buf_clamp rawBytes s.bufCap))
          (UInt64.toNat s.bufCap) :=
        seccomp_buf_clamp_le_cap rawBytes s.bufCap
      let hBytesSNext : Nat.le (UInt64.toNat sNext.injectedBytes) (UInt64.toNat s.bufCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.bufCap)) hStep.2.2.2.1) hBytesBounded
      let hBytesFinal : Nat.le (UInt64.toNat sNext.injectedBytes) (UInt64.toNat sNext.bufCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.injectedBytes) (UInt64.toNat x)) hStep.2.1) hBytesSNext
      And.intro hCurFinal (And.intro hBytesFinal hStep.2.2.2.2)

    theorem next_preserves_inv (s sNext : SeccompReplayState)
        (hInv : SeccompReplaySafetyInv s) (hNext : Next s sNext) :
        SeccompReplaySafetyInv sNext :=
      Exists.elim hNext (fun nextCursor h1 =>
        Exists.elim h1 (fun rawBytes h2 =>
          neutralize_preserves_inv nextCursor rawBytes s sNext hInv h2))

    theorem spec_satisfies_seccomp_replay_safety :
        Spec ⊨ □ (Lift SeccompReplaySafetyInv) :=
      invariantSatisfies Spec SeccompReplaySafetyInv init_establishes_inv next_preserves_inv

    end TlaSeccompFilter
    end Host
    end Astream
}
