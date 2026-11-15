// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for DEC `?2026` Synchronized Output atomic frame latching
// (`Astream.Term.TlaSyncOutput`), mounted under `cfg(clean_islands)` in `events.rs`.
// Proves that `sync_bytes_clamp` and `sync_hold_ticks_clamp` maintain bounded byte
// accumulation (`syncBytes <= byteCap`), bounded debounce hold ticks (`holdTicks <= tickCap`),
// and clean debt reset (`latched = false -> syncBytes = 0 /\ holdTicks = 0`) across all
// `?2026h` / chunk-feed / hold-tick / `?2026l`-or-reset transitions.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def sync_bytes_clamp (proposed_bytes : UInt64) (byte_cap : UInt64) : UInt64 :=
      if proposed_bytes < byte_cap then proposed_bytes else byte_cap

    def sync_hold_ticks_clamp (proposed_ticks : UInt64) (tick_cap : UInt64) : UInt64 :=
      if proposed_ticks < tick_cap then proposed_ticks else tick_cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaSyncOutput)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaSyncOutput

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaSyncOutput.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaSyncOutput.Always

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

    -- ========================================================================
    -- 3. DEC `?2026` Synchronized Output Latch State Machine & Safety Theorem
    -- ========================================================================

    structure SyncOutputState where
      latched   : Bool
      syncBytes : UInt64
      byteCap   : UInt64
      holdTicks : UInt64
      tickCap   : UInt64

    def SyncOutputSafetyInv (s : SyncOutputState) : Prop :=
      Nat.le (UInt64.toNat s.syncBytes) (UInt64.toNat s.byteCap) ∧
      Nat.le (UInt64.toNat s.holdTicks) (UInt64.toNat s.tickCap) ∧
      (s.latched = false → s.syncBytes = (0 : UInt64) ∧ s.holdTicks = (0 : UInt64))

    def Init (byteCap tickCap : UInt64) (s : SyncOutputState) : Prop :=
      s.latched = false ∧
      s.syncBytes = (0 : UInt64) ∧
      s.byteCap = byteCap ∧
      s.holdTicks = (0 : UInt64) ∧
      s.tickCap = tickCap

    def BeginSync (s sNext : SyncOutputState) : Prop :=
      sNext.latched = true ∧
      sNext.syncBytes = (0 : UInt64) ∧
      sNext.byteCap = s.byteCap ∧
      sNext.holdTicks = (0 : UInt64) ∧
      sNext.tickCap = s.tickCap

    def FeedSyncChunk (candBytes : UInt64) (s sNext : SyncOutputState) : Prop :=
      s.latched = true ∧
      sNext.latched = true ∧
      sNext.syncBytes = _root_.sync_bytes_clamp candBytes s.byteCap ∧
      sNext.byteCap = s.byteCap ∧
      sNext.holdTicks = s.holdTicks ∧
      sNext.tickCap = s.tickCap

    def HoldTick (candTicks : UInt64) (s sNext : SyncOutputState) : Prop :=
      s.latched = true ∧
      sNext.latched = true ∧
      sNext.syncBytes = s.syncBytes ∧
      sNext.byteCap = s.byteCap ∧
      sNext.holdTicks = _root_.sync_hold_ticks_clamp candTicks s.tickCap ∧
      sNext.tickCap = s.tickCap

    def EndSyncOrReset (s sNext : SyncOutputState) : Prop :=
      sNext.latched = false ∧
      sNext.syncBytes = (0 : UInt64) ∧
      sNext.byteCap = s.byteCap ∧
      sNext.holdTicks = (0 : UInt64) ∧
      sNext.tickCap = s.tickCap

    def Next (s sNext : SyncOutputState) : Prop :=
      BeginSync s sNext ∨
      ((∃ cb : UInt64, FeedSyncChunk cb s sNext) ∨
       ((∃ ct : UInt64, HoldTick ct s sNext) ∨
        EndSyncOrReset s sNext))

    def Spec (byteCap tickCap : UInt64) : StateMachine SyncOutputState :=
      StateMachine.mk (Init byteCap tickCap) Next

    theorem true_ne_false (h : true = false) : False :=
      Bool.noConfusion h

    theorem bytes_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sync_bytes_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem ticks_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sync_hold_ticks_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (byteCap tickCap : UInt64) (s : SyncOutputState)
        (hInit : Init byteCap tickCap s) : SyncOutputSafetyInv s :=
      And.intro
        (zero_u64_le s.syncBytes s.byteCap hInit.2.1)
        (And.intro
          (zero_u64_le s.holdTicks s.tickCap hInit.2.2.2.1)
          (fun _ => And.intro hInit.2.1 hInit.2.2.2.1))

    theorem beginSync_preserves_inv (s sNext : SyncOutputState)
        (hAct : BeginSync s sNext) : SyncOutputSafetyInv sNext :=
      And.intro
        (zero_u64_le sNext.syncBytes sNext.byteCap hAct.2.1)
        (And.intro
          (zero_u64_le sNext.holdTicks sNext.tickCap hAct.2.2.2.1)
          (fun hFalse =>
            False.elim (true_ne_false (Eq.trans (Eq.symm hAct.1) hFalse))))

    theorem feedSyncChunk_preserves_inv (cb : UInt64) (s sNext : SyncOutputState)
        (hInv : SyncOutputSafetyInv s) (hAct : FeedSyncChunk cb s sNext) :
        SyncOutputSafetyInv sNext :=
      let hBytesEq : sNext.syncBytes = _root_.sync_bytes_clamp cb s.byteCap := hAct.2.2.1
      let hBCapEq : sNext.byteCap = s.byteCap := hAct.2.2.2.1
      let hTicksEq : sNext.holdTicks = s.holdTicks := hAct.2.2.2.2.1
      let hTCapEq : sNext.tickCap = s.tickCap := hAct.2.2.2.2.2
      let hB1 : Nat.le (UInt64.toNat sNext.syncBytes) (UInt64.toNat s.byteCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.byteCap)) hBytesEq)
          (bytes_clamp_le cb s.byteCap)
      let hB2 : Nat.le (UInt64.toNat sNext.syncBytes) (UInt64.toNat sNext.byteCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.syncBytes) (UInt64.toNat y)) hBCapEq)
          hB1
      let hT1 : Nat.le (UInt64.toNat sNext.holdTicks) (UInt64.toNat s.tickCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.tickCap)) hTicksEq)
          hInv.2.1
      let hT2 : Nat.le (UInt64.toNat sNext.holdTicks) (UInt64.toNat sNext.tickCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.holdTicks) (UInt64.toNat y)) hTCapEq)
          hT1
      And.intro hB2
        (And.intro hT2
          (fun hFalse =>
            False.elim (true_ne_false (Eq.trans (Eq.symm hAct.2.1) hFalse))))

    theorem holdTick_preserves_inv (ct : UInt64) (s sNext : SyncOutputState)
        (hInv : SyncOutputSafetyInv s) (hAct : HoldTick ct s sNext) :
        SyncOutputSafetyInv sNext :=
      let hBytesEq : sNext.syncBytes = s.syncBytes := hAct.2.2.1
      let hBCapEq : sNext.byteCap = s.byteCap := hAct.2.2.2.1
      let hTicksEq : sNext.holdTicks = _root_.sync_hold_ticks_clamp ct s.tickCap := hAct.2.2.2.2.1
      let hTCapEq : sNext.tickCap = s.tickCap := hAct.2.2.2.2.2
      let hB1 : Nat.le (UInt64.toNat sNext.syncBytes) (UInt64.toNat s.byteCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.byteCap)) hBytesEq)
          hInv.1
      let hB2 : Nat.le (UInt64.toNat sNext.syncBytes) (UInt64.toNat sNext.byteCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.syncBytes) (UInt64.toNat y)) hBCapEq)
          hB1
      let hT1 : Nat.le (UInt64.toNat sNext.holdTicks) (UInt64.toNat s.tickCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.tickCap)) hTicksEq)
          (ticks_clamp_le ct s.tickCap)
      let hT2 : Nat.le (UInt64.toNat sNext.holdTicks) (UInt64.toNat sNext.tickCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.holdTicks) (UInt64.toNat y)) hTCapEq)
          hT1
      And.intro hB2
        (And.intro hT2
          (fun hFalse =>
            False.elim (true_ne_false (Eq.trans (Eq.symm hAct.2.1) hFalse))))

    theorem endSyncOrReset_preserves_inv (s sNext : SyncOutputState)
        (hAct : EndSyncOrReset s sNext) : SyncOutputSafetyInv sNext :=
      And.intro
        (zero_u64_le sNext.syncBytes sNext.byteCap hAct.2.1)
        (And.intro
          (zero_u64_le sNext.holdTicks sNext.tickCap hAct.2.2.2.1)
          (fun _ => And.intro hAct.2.1 hAct.2.2.2.1))

    theorem next_preserves_inv (s sNext : SyncOutputState)
        (hInv : SyncOutputSafetyInv s) (hNext : Next s sNext) :
        SyncOutputSafetyInv sNext :=
      Or.elim hNext
        (fun hBeg => beginSync_preserves_inv s sNext hBeg)
        (fun hRest1 =>
          Or.elim hRest1
            (fun hFeed =>
              Exists.elim hFeed (fun cb hF => feedSyncChunk_preserves_inv cb s sNext hInv hF))
            (fun hRest2 =>
              Or.elim hRest2
                (fun hTick =>
                  Exists.elim hTick (fun ct hT => holdTick_preserves_inv ct s sNext hInv hT))
                (fun hEnd => endSyncOrReset_preserves_inv s sNext hEnd)))

    theorem spec_satisfies_sync_output_safety (byteCap tickCap : UInt64) :
        (Spec byteCap tickCap) ⊨ □ (Lift SyncOutputSafetyInv) :=
      invariantSatisfies (Spec byteCap tickCap) SyncOutputSafetyInv
        (init_establishes_inv byteCap tickCap)
        next_preserves_inv

    end TlaSyncOutput
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def sync_within_budget_isl (sync_bytes : UInt64) (byte_cap : UInt64) : Bool :=
      decide (sync_bytes < byte_cap)
}
