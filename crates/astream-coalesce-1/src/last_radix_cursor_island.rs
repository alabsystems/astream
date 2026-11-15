// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for pinned-head paginated `Last` snapshot scanning
// (`Astream.Broker.TlaLastSnapshotCursor`), mounted under `cfg(clean_islands)` in
// `last_radix_cursor.rs`. Proves `scannedEntries <= scanBudget` and
// `emittedMaxOffset <= pinnedHead` across multi-round `Last` scans.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def last_scan_entries_clamp (scanned : UInt64) (scan_budget : UInt64) : UInt64 :=
      if scanned < scan_budget then scanned else scan_budget

    def last_emitted_offset_clamp (candidate_off : UInt64) (pinned_head : UInt64) : UInt64 :=
      if candidate_off < pinned_head then candidate_off else pinned_head

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Broker.TlaLastSnapshotCursor)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaLastSnapshotCursor

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
        Satisfies M (Always (Lift I)) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    -- ========================================================================
    -- 3. Pinned-Head `Last` Snapshot Cursor State Machine
    -- ========================================================================

    structure LastCursorState where
      scannedEntries   : UInt64
      scanBudget       : UInt64
      emittedMaxOffset : UInt64
      pinnedHead       : UInt64

    def LastCursorInv (s : LastCursorState) : Prop :=
      Nat.le (UInt64.toNat s.scannedEntries) (UInt64.toNat s.scanBudget) ∧
      Nat.le (UInt64.toNat s.emittedMaxOffset) (UInt64.toNat s.pinnedHead)

    def Init (scanBudget pinnedHead : UInt64) (s : LastCursorState) : Prop :=
      s.scannedEntries = (0 : UInt64) ∧
      s.scanBudget = scanBudget ∧
      s.emittedMaxOffset = (0 : UInt64) ∧
      s.pinnedHead = pinnedHead

    def ScanRound (rawScanned rawOff : UInt64) (s sNext : LastCursorState) : Prop :=
      sNext.scannedEntries = _root_.last_scan_entries_clamp rawScanned s.scanBudget ∧
      sNext.scanBudget = s.scanBudget ∧
      sNext.emittedMaxOffset = _root_.last_emitted_offset_clamp rawOff s.pinnedHead ∧
      sNext.pinnedHead = s.pinnedHead

    def Next (s sNext : LastCursorState) : Prop :=
      ∃ rs : UInt64, ∃ ro : UInt64, ScanRound rs ro s sNext

    def Spec (scanBudget pinnedHead : UInt64) : StateMachine LastCursorState :=
      StateMachine.mk (Init scanBudget pinnedHead) Next

    theorem scan_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.last_scan_entries_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem off_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.last_emitted_offset_clamp cand cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (scanBudget pinnedHead : UInt64) (s : LastCursorState)
        (hInit : Init scanBudget pinnedHead s) : LastCursorInv s :=
      And.intro
        (zero_u64_le s.scannedEntries s.scanBudget hInit.1)
        (zero_u64_le s.emittedMaxOffset s.pinnedHead hInit.2.2.1)

    theorem scanRound_preserves_inv (rs ro : UInt64) (s sNext : LastCursorState)
        (hAct : ScanRound rs ro s sNext) : LastCursorInv sNext :=
      let hS1 : Nat.le (UInt64.toNat sNext.scannedEntries) (UInt64.toNat s.scanBudget) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.scanBudget)) hAct.1)
          (scan_clamp_le rs s.scanBudget)
      let hS2 : Nat.le (UInt64.toNat sNext.scannedEntries) (UInt64.toNat sNext.scanBudget) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.scannedEntries) (UInt64.toNat y)) hAct.2.1)
          hS1
      let hO1 : Nat.le (UInt64.toNat sNext.emittedMaxOffset) (UInt64.toNat s.pinnedHead) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.pinnedHead)) hAct.2.2.1)
          (off_clamp_le ro s.pinnedHead)
      let hO2 : Nat.le (UInt64.toNat sNext.emittedMaxOffset) (UInt64.toNat sNext.pinnedHead) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.emittedMaxOffset) (UInt64.toNat y)) hAct.2.2.2)
          hO1
      And.intro hS2 hO2

    theorem next_preserves_inv (s sNext : LastCursorState)
        (_hInv : LastCursorInv s) (hNext : Next s sNext) : LastCursorInv sNext :=
      Exists.elim hNext (fun rs hEx2 =>
        Exists.elim hEx2 (fun ro hAct => scanRound_preserves_inv rs ro s sNext hAct))

    theorem spec_satisfies_last_snapshot_cursor_safety (scanBudget pinnedHead : UInt64) :
        Satisfies (Spec scanBudget pinnedHead) (Always (Lift LastCursorInv)) :=
      invariantSatisfies (Spec scanBudget pinnedHead) LastCursorInv
        (init_establishes_inv scanBudget pinnedHead)
        next_preserves_inv

    end TlaLastSnapshotCursor
    end Broker
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def last_row_visible_at_pin_isl (row_offset : UInt64) (pinned_head : UInt64) : Bool :=
      decide (row_offset < pinned_head)
}
