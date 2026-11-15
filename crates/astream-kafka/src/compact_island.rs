// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for KIP-482 compact framing and bounded RecordBatch v2 decompression
// (`compress.rs`, `record_batch.rs`, `lib.rs`), mounted only under `cfg(clean_islands)`.
// Every other compiler calls the plain-Rust twins in `twins.rs`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    -- Clamp a KIP-482 compact string/array length against a hard protocol ceiling.
    def kafka_compact_len_clamp (len : UInt64) (cap : UInt64) : UInt64 :=
      if len < cap then len else cap

    -- Clamp a RecordBatch v2 decompressed payload budget against `MAX_KAFKA_FRAME_LEN`.
    def kafka_decompress_cap_clamp (decoded_len : UInt64) (max_cap : UInt64) : UInt64 :=
      if decoded_len < max_cap then decoded_len else max_cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Kafka.TlaCompactFraming)
    -- ========================================================================
    namespace Astream
    namespace Kafka
    namespace TlaCompactFraming

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

    prefix:100 "□" => _root_.Astream.Kafka.TlaCompactFraming.Always
    infixl:45 " ⊨ " => _root_.Astream.Kafka.TlaCompactFraming.Satisfies

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

    theorem clamp_compact_le_cap : forall (len : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kafka_compact_len_clamp len cap)) (UInt64.toNat cap) :=
      fun len cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => len))) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clamp_decompress_le_cap : forall (decLen : UInt64) (maxCap : UInt64),
        Nat.le (UInt64.toNat (_root_.kafka_decompress_cap_clamp decLen maxCap)) (UInt64.toNat maxCap) :=
      fun decLen maxCap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt decLen maxCap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => maxCap) (fun _ => decLen))) (UInt64.toNat maxCap))
        (instDecidableUInt64Lt decLen maxCap)
        (fun _ => Nat.le.refl (UInt64.toNat maxCap))
        (fun hLt => Nat.le_of_lt hLt)

    -- ========================================================================
    -- 3. TLA+ Specification: Bounded KIP-482 Compact Framing & Decompression
    -- ========================================================================
    structure CompactFrameState where
      compactLen      : UInt64
      maxCompactCap   : UInt64
      decompressedLen : UInt64
      maxDecompressCap : UInt64

    def CompactFrameSafetyInv (s : CompactFrameState) : Prop :=
      Nat.le (UInt64.toNat s.compactLen) (UInt64.toNat s.maxCompactCap) ∧
      Nat.le (UInt64.toNat s.decompressedLen) (UInt64.toNat s.maxDecompressCap)

    def Init (maxComp : UInt64) (maxDec : UInt64) (s : CompactFrameState) : Prop :=
      s.compactLen = (0 : UInt64) ∧
      s.maxCompactCap = maxComp ∧
      s.decompressedLen = (0 : UInt64) ∧
      s.maxDecompressCap = maxDec

    def DecodeCompactItem (candLen : UInt64) (s sNext : CompactFrameState) : Prop :=
      sNext.compactLen = _root_.kafka_compact_len_clamp candLen s.maxCompactCap ∧
      sNext.maxCompactCap = s.maxCompactCap ∧
      sNext.decompressedLen = s.decompressedLen ∧
      sNext.maxDecompressCap = s.maxDecompressCap

    def DecompressBatchPayload (candBytes : UInt64) (s sNext : CompactFrameState) : Prop :=
      sNext.compactLen = s.compactLen ∧
      sNext.maxCompactCap = s.maxCompactCap ∧
      sNext.decompressedLen = _root_.kafka_decompress_cap_clamp candBytes s.maxDecompressCap ∧
      sNext.maxDecompressCap = s.maxDecompressCap

    def Next (s sNext : CompactFrameState) : Prop :=
      (∃ cand : UInt64, DecodeCompactItem cand s sNext) ∨
      (∃ candB : UInt64, DecompressBatchPayload candB s sNext)

    def Spec (maxComp : UInt64) (maxDec : UInt64) : StateMachine CompactFrameState :=
      StateMachine.mk (Init maxComp maxDec) Next

    theorem init_establishes_inv (maxComp : UInt64) (maxDec : UInt64) (s : CompactFrameState)
        (hInit : Init maxComp maxDec s) : CompactFrameSafetyInv s :=
      let hZ1 : Nat.le (UInt64.toNat (0 : UInt64)) (UInt64.toNat s.maxCompactCap) :=
        Nat.zero_le (UInt64.toNat s.maxCompactCap)
      let hCompLe : Nat.le (UInt64.toNat s.compactLen) (UInt64.toNat s.maxCompactCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxCompactCap)) hInit.1)
          hZ1
      let hZ2 : Nat.le (UInt64.toNat (0 : UInt64)) (UInt64.toNat s.maxDecompressCap) :=
        Nat.zero_le (UInt64.toNat s.maxDecompressCap)
      let hDecLe : Nat.le (UInt64.toNat s.decompressedLen) (UInt64.toNat s.maxDecompressCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxDecompressCap)) hInit.2.2.1)
          hZ2
      And.intro hCompLe hDecLe

    theorem decodeCompact_preserves_inv (cand : UInt64) (s sNext : CompactFrameState)
        (hInv : CompactFrameSafetyInv s) (hAct : DecodeCompactItem cand s sNext) :
        CompactFrameSafetyInv sNext :=
      let hCompEq : sNext.compactLen = _root_.kafka_compact_len_clamp cand s.maxCompactCap := hAct.1
      let hCapEq : sNext.maxCompactCap = s.maxCompactCap := hAct.2.1
      let hDecEq : sNext.decompressedLen = s.decompressedLen := hAct.2.2.1
      let hMaxDEq : sNext.maxDecompressCap = s.maxDecompressCap := hAct.2.2.2
      let hC1 : Nat.le (UInt64.toNat sNext.compactLen) (UInt64.toNat s.maxCompactCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxCompactCap)) hCompEq)
          (clamp_compact_le_cap cand s.maxCompactCap)
      let hCompNext : Nat.le (UInt64.toNat sNext.compactLen) (UInt64.toNat sNext.maxCompactCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.compactLen) (UInt64.toNat y)) hCapEq) hC1
      let hD1 : Nat.le (UInt64.toNat sNext.decompressedLen) (UInt64.toNat s.maxDecompressCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxDecompressCap)) hDecEq) hInv.2
      let hDecNext : Nat.le (UInt64.toNat sNext.decompressedLen) (UInt64.toNat sNext.maxDecompressCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.decompressedLen) (UInt64.toNat y)) hMaxDEq) hD1
      And.intro hCompNext hDecNext

    theorem decompressBatch_preserves_inv (candB : UInt64) (s sNext : CompactFrameState)
        (hInv : CompactFrameSafetyInv s) (hAct : DecompressBatchPayload candB s sNext) :
        CompactFrameSafetyInv sNext :=
      let hCompEq : sNext.compactLen = s.compactLen := hAct.1
      let hCapEq : sNext.maxCompactCap = s.maxCompactCap := hAct.2.1
      let hDecEq : sNext.decompressedLen = _root_.kafka_decompress_cap_clamp candB s.maxDecompressCap := hAct.2.2.1
      let hMaxDEq : sNext.maxDecompressCap = s.maxDecompressCap := hAct.2.2.2
      let hC1 : Nat.le (UInt64.toNat sNext.compactLen) (UInt64.toNat s.maxCompactCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxCompactCap)) hCompEq) hInv.1
      let hCompNext : Nat.le (UInt64.toNat sNext.compactLen) (UInt64.toNat sNext.maxCompactCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.compactLen) (UInt64.toNat y)) hCapEq) hC1
      let hD1 : Nat.le (UInt64.toNat sNext.decompressedLen) (UInt64.toNat s.maxDecompressCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxDecompressCap)) hDecEq)
          (clamp_decompress_le_cap candB s.maxDecompressCap)
      let hDecNext : Nat.le (UInt64.toNat sNext.decompressedLen) (UInt64.toNat sNext.maxDecompressCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.decompressedLen) (UInt64.toNat y)) hMaxDEq) hD1
      And.intro hCompNext hDecNext

    theorem next_preserves_inv (s sNext : CompactFrameState)
        (hInv : CompactFrameSafetyInv s) (hNext : Next s sNext) :
        CompactFrameSafetyInv sNext :=
      Or.elim hNext
        (fun hC => Exists.elim hC (fun cand hA => decodeCompact_preserves_inv cand s sNext hInv hA))
        (fun hD => Exists.elim hD (fun candB hB => decompressBatch_preserves_inv candB s sNext hInv hB))

    theorem spec_satisfies_compact_frame_safety (maxComp : UInt64) (maxDec : UInt64) :
        (Spec maxComp maxDec) ⊨ □ (Lift CompactFrameSafetyInv) :=
      invariantSatisfies (Spec maxComp maxDec) CompactFrameSafetyInv
        (init_establishes_inv maxComp maxDec)
        next_preserves_inv

    end TlaCompactFraming
    end Kafka
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def compression_codec_in_spec_range_isl (codec : UInt8) : Bool :=
      decide (codec ≤ (4 : UInt8))
}
