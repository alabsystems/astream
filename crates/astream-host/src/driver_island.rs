// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `driver.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `driver.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from these Clean kernel definitions into Rust MIR
    --    (`pub const fn pty_pending_clamp` and
    --     `pub const fn pty_drain_cap_select`) and verified by `Faithful`.
    -- ========================================================================

    -- Clamp a pending PTY drain length to `cap` (`PENDING_MAX = 8 MiB`).
    def pty_pending_clamp (len : UInt64) (cap : UInt64) : UInt64 :=
      if len < cap then len else cap

    -- 4-parameter Clean-origin PTY drain cap selector:
    -- selects `reject_val` (`0`) when `cap < proposed_total`, else `admit_val`.
    def pty_drain_cap_select (cap : UInt64) (proposed_total : UInt64) (reject_val : UInt64) (admit_val : UInt64) : UInt64 :=
      if cap < proposed_total then reject_val else admit_val

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Host.TlaPtyDriver)
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaPtyDriver

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

    prefix:100 "□" => _root_.Astream.Host.TlaPtyDriver.Always
    infixl:45 " ⊨ " => _root_.Astream.Host.TlaPtyDriver.Satisfies

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

    theorem pty_pending_clamp_le_cap : forall (len cap : UInt64),
        Nat.le (UInt64.toNat (_root_.pty_pending_clamp len cap)) (UInt64.toNat cap) :=
      fun len cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => len))) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun h => Nat.le_of_lt h)

    def pty_admit_drain_chunk_isl (proposed_total cap chunk_len : UInt64) : UInt64 :=
      _root_.pty_drain_cap_select cap proposed_total 0 (_root_.pty_drain_cap_select 0 chunk_len 1 0)

    theorem pty_admit_drain_binary (proposed_total cap chunk_len : UInt64) :
        pty_admit_drain_chunk_isl proposed_total cap chunk_len = 0 ∨
        pty_admit_drain_chunk_isl proposed_total cap chunk_len = 1 :=
      @Decidable.casesOn (LT.lt cap proposed_total)
        (fun (d1 : Decidable (LT.lt cap proposed_total)) =>
          @ite UInt64 (LT.lt cap proposed_total) d1 0 (_root_.pty_drain_cap_select 0 chunk_len 1 0) = 0 ∨
          @ite UInt64 (LT.lt cap proposed_total) d1 0 (_root_.pty_drain_cap_select 0 chunk_len 1 0) = 1)
        (instDecidableUInt64Lt cap proposed_total)
        (fun _ =>
          @Decidable.casesOn (LT.lt 0 chunk_len)
            (fun (d2 : Decidable (LT.lt 0 chunk_len)) =>
              @ite UInt64 (LT.lt 0 chunk_len) d2 1 0 = 0 ∨
              @ite UInt64 (LT.lt 0 chunk_len) d2 1 0 = 1)
            (instDecidableUInt64Lt 0 chunk_len)
            (fun _ => Or.inl (Eq.refl 0))
            (fun _ => Or.inr (Eq.refl 1)))
        (fun _ => Or.inl (Eq.refl 0))

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: PTY Concurrent Drain & At-Most-Once Input
    -- ========================================================================
    structure PtyDriverState where
      pendingLen  : UInt64
      pendingCap  : UInt64
      lastAdmit   : UInt64

    -- TLA+ Safety Invariant:
    -- 1. Committed pending drain occupancy never exceeds `pendingCap` (`8 MiB`).
    -- 2. Every drain-chunk admission decision is binary (`0` rejected, `1` admitted).
    def PtyDriverSafetyInv (s : PtyDriverState) : Prop :=
      Nat.le (UInt64.toNat s.pendingLen) (UInt64.toNat s.pendingCap) ∧
      (s.lastAdmit = 0 ∨ s.lastAdmit = 1)

    def Init (cap : UInt64) (s : PtyDriverState) : Prop :=
      s.pendingLen = 0 ∧
      s.pendingCap = cap ∧
      s.lastAdmit = 0

    def DrainChunk (proposedTotal chunkLen : UInt64) (s sNext : PtyDriverState) : Prop :=
      sNext.pendingLen = _root_.pty_pending_clamp proposedTotal s.pendingCap ∧
      sNext.pendingCap = s.pendingCap ∧
      sNext.lastAdmit = pty_admit_drain_chunk_isl proposedTotal s.pendingCap chunkLen

    def ConsumePending (s sNext : PtyDriverState) : Prop :=
      sNext.pendingLen = 0 ∧
      sNext.pendingCap = s.pendingCap ∧
      sNext.lastAdmit = s.lastAdmit

    def Next (s sNext : PtyDriverState) : Prop :=
      (∃ proposedTotal : UInt64, ∃ chunkLen : UInt64, DrainChunk proposedTotal chunkLen s sNext) ∨
      ConsumePending s sNext

    def Spec (cap : UInt64) : StateMachine PtyDriverState :=
      StateMachine.mk (Init cap) Next

    theorem init_establishes_inv (cap : UInt64) (s : PtyDriverState)
        (hInit : Init cap s) : PtyDriverSafetyInv s :=
      let hZeroLe : Nat.le (UInt64.toNat 0) (UInt64.toNat s.pendingCap) :=
        Nat.zero_le (UInt64.toNat s.pendingCap)
      let hLenLe : Nat.le (UInt64.toNat s.pendingLen) (UInt64.toNat s.pendingCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.pendingCap)) hInit.1) hZeroLe
      And.intro hLenLe (Or.inl hInit.2.2)

    theorem drainChunk_preserves_inv (proposedTotal chunkLen : UInt64) (s sNext : PtyDriverState)
        (_hInv : PtyDriverSafetyInv s) (hAct : DrainChunk proposedTotal chunkLen s sNext) :
        PtyDriverSafetyInv sNext :=
      let hLenEq : sNext.pendingLen = _root_.pty_pending_clamp proposedTotal s.pendingCap := hAct.1
      let hCapEq : sNext.pendingCap = s.pendingCap := hAct.2.1
      let hAdmEq : sNext.lastAdmit = pty_admit_drain_chunk_isl proposedTotal s.pendingCap chunkLen := hAct.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.pendingLen) (UInt64.toNat s.pendingCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.pendingCap)) hLenEq)
          (pty_pending_clamp_le_cap proposedTotal s.pendingCap)
      let hLeNext : Nat.le (UInt64.toNat sNext.pendingLen) (UInt64.toNat sNext.pendingCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.pendingLen) (UInt64.toNat y)) hCapEq) hLe1
      let hBin := pty_admit_drain_binary proposedTotal s.pendingCap chunkLen
      let hAdmNext : sNext.lastAdmit = 0 ∨ sNext.lastAdmit = 1 :=
        Or.elim hBin
          (fun h0 => Or.inl (Eq.trans hAdmEq h0))
          (fun h1 => Or.inr (Eq.trans hAdmEq h1))
      And.intro hLeNext hAdmNext

    theorem consumePending_preserves_inv (s sNext : PtyDriverState)
        (hInv : PtyDriverSafetyInv s) (hAct : ConsumePending s sNext) :
        PtyDriverSafetyInv sNext :=
      let hLenEq : sNext.pendingLen = 0 := hAct.1
      let hAdmEq : sNext.lastAdmit = s.lastAdmit := hAct.2.2
      let hZeroLe : Nat.le (UInt64.toNat 0) (UInt64.toNat sNext.pendingCap) :=
        Nat.zero_le (UInt64.toNat sNext.pendingCap)
      let hLeNext : Nat.le (UInt64.toNat sNext.pendingLen) (UInt64.toNat sNext.pendingCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.pendingCap)) hLenEq) hZeroLe
      let hAdmNext : sNext.lastAdmit = 0 ∨ sNext.lastAdmit = 1 :=
        Or.elim hInv.2
          (fun h0 => Or.inl (Eq.trans hAdmEq h0))
          (fun h1 => Or.inr (Eq.trans hAdmEq h1))
      And.intro hLeNext hAdmNext

    theorem next_preserves_inv (s sNext : PtyDriverState)
        (hInv : PtyDriverSafetyInv s) (hNext : Next s sNext) :
        PtyDriverSafetyInv sNext :=
      Or.elim hNext
        (fun hEx => Exists.elim hEx (fun pt hEx2 => Exists.elim hEx2 (fun cl hDr =>
          drainChunk_preserves_inv pt cl s sNext hInv hDr)))
        (fun hCon => consumePending_preserves_inv s sNext hInv hCon)

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec cap) ⊨ □ (Lift PtyDriverSafetyInv)`
    theorem spec_satisfies_pty_driver_safety (cap : UInt64) :
        (Spec cap) ⊨ □ (Lift PtyDriverSafetyInv) :=
      invariantSatisfies (Spec cap) PtyDriverSafetyInv
        (init_establishes_inv cap)
        next_preserves_inv

    end TlaPtyDriver
    end Host
    end Astream

    def pending_within_cap_isl (pending_len : UInt64) (cap : UInt64) : Bool :=
      decide (pending_len ≤ cap)
}
