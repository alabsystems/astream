// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for Kafka RecordBatch v2 varint header-block budget enforcement
// (`Astream.Kafka.TlaRecordHeaderBudget`), mounted under `cfg(clean_islands)` in
// `kafka_record_header_guard.rs`. Proves `headerCount <= maxHeaders` and
// `headerBytes <= maxHeaderBytes`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def kafka_hdr_count_clamp (proposed_count : UInt64) (max_headers : UInt64) : UInt64 :=
      if proposed_count < max_headers then proposed_count else max_headers

    def kafka_hdr_bytes_clamp (proposed_bytes : UInt64) (max_bytes : UInt64) : UInt64 :=
      if proposed_bytes < max_bytes then proposed_bytes else max_bytes

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Kafka.TlaRecordHeaderBudget)
    -- ========================================================================
    namespace Astream
    namespace Kafka
    namespace TlaRecordHeaderBudget

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Kafka.TlaRecordHeaderBudget.Satisfies M F
    prefix:75 "□" => _root_.Astream.Kafka.TlaRecordHeaderBudget.Always

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
    -- 3. Kafka Record Header Budget State Machine
    -- ========================================================================

    structure HeaderBudgetState where
      headerCount    : UInt64
      maxHeaders     : UInt64
      headerBytes    : UInt64
      maxHeaderBytes : UInt64

    def HeaderBudgetInv (s : HeaderBudgetState) : Prop :=
      Nat.le (UInt64.toNat s.headerCount) (UInt64.toNat s.maxHeaders) ∧
      Nat.le (UInt64.toNat s.headerBytes) (UInt64.toNat s.maxHeaderBytes)

    def Init (maxHeaders maxHeaderBytes : UInt64) (s : HeaderBudgetState) : Prop :=
      s.headerCount = (0 : UInt64) ∧
      s.maxHeaders = maxHeaders ∧
      s.headerBytes = (0 : UInt64) ∧
      s.maxHeaderBytes = maxHeaderBytes

    def AppendHeader (propCount propBytes : UInt64) (s sNext : HeaderBudgetState) : Prop :=
      sNext.headerCount = _root_.kafka_hdr_count_clamp propCount s.maxHeaders ∧
      sNext.maxHeaders = s.maxHeaders ∧
      sNext.headerBytes = _root_.kafka_hdr_bytes_clamp propBytes s.maxHeaderBytes ∧
      sNext.maxHeaderBytes = s.maxHeaderBytes

    def Next (s sNext : HeaderBudgetState) : Prop :=
      ∃ pc : UInt64, ∃ pb : UInt64, AppendHeader pc pb s sNext

    def Spec (maxHeaders maxHeaderBytes : UInt64) : StateMachine HeaderBudgetState :=
      StateMachine.mk (Init maxHeaders maxHeaderBytes) Next

    theorem count_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kafka_hdr_count_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem bytes_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kafka_hdr_bytes_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxHeaders maxHeaderBytes : UInt64) (s : HeaderBudgetState)
        (hInit : Init maxHeaders maxHeaderBytes s) : HeaderBudgetInv s :=
      And.intro
        (zero_u64_le s.headerCount s.maxHeaders hInit.1)
        (zero_u64_le s.headerBytes s.maxHeaderBytes hInit.2.2.1)

    theorem appendHeader_preserves_inv (pc pb : UInt64) (s sNext : HeaderBudgetState)
        (hAct : AppendHeader pc pb s sNext) : HeaderBudgetInv sNext :=
      let hC1 : Nat.le (UInt64.toNat sNext.headerCount) (UInt64.toNat s.maxHeaders) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxHeaders)) hAct.1)
          (count_clamp_le pc s.maxHeaders)
      let hC2 : Nat.le (UInt64.toNat sNext.headerCount) (UInt64.toNat sNext.maxHeaders) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.headerCount) (UInt64.toNat y)) hAct.2.1)
          hC1
      let hB1 : Nat.le (UInt64.toNat sNext.headerBytes) (UInt64.toNat s.maxHeaderBytes) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxHeaderBytes)) hAct.2.2.1)
          (bytes_clamp_le pb s.maxHeaderBytes)
      let hB2 : Nat.le (UInt64.toNat sNext.headerBytes) (UInt64.toNat sNext.maxHeaderBytes) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.headerBytes) (UInt64.toNat y)) hAct.2.2.2)
          hB1
      And.intro hC2 hB2

    theorem next_preserves_inv (s sNext : HeaderBudgetState)
        (_hInv : HeaderBudgetInv s) (hNext : Next s sNext) : HeaderBudgetInv sNext :=
      Exists.elim hNext (fun pc hEx2 =>
        Exists.elim hEx2 (fun pb hAct => appendHeader_preserves_inv pc pb s sNext hAct))

    theorem spec_satisfies_kafka_header_budget_safety (maxHeaders maxHeaderBytes : UInt64) :
        (Spec maxHeaders maxHeaderBytes) ⊨ □ (Lift HeaderBudgetInv) :=
      invariantSatisfies (Spec maxHeaders maxHeaderBytes) HeaderBudgetInv
        (init_establishes_inv maxHeaders maxHeaderBytes)
        next_preserves_inv

    end TlaRecordHeaderBudget
    end Kafka
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def kafka_hdr_fits_budget_isl (used : UInt64) (cap : UInt64) : Bool :=
      decide (used ≤ cap)
}
