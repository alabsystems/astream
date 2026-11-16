// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for streaming O(log N)-space RFC 6962 SHA-256 Merkle Mountain Range
// accumulation (`Astream.Digest.TlaMerkleMountainRange`), mounted under `cfg(clean_islands)`
// in `digest_merkle_accumulator.rs`. Proves `activePeaks <= maxPeaks` and
// `prevLeaves <= leafCount` across streaming leaf appends.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def mmr_peaks_clamp (active_peaks : UInt64) (max_peaks : UInt64) : UInt64 :=
      if active_peaks < max_peaks then active_peaks else max_peaks

    def mmr_leaves_advance (prev_leaves : UInt64) (next_leaves : UInt64) : UInt64 :=
      if prev_leaves < next_leaves then next_leaves else prev_leaves

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Digest.TlaMerkleMountainRange)
    -- ========================================================================
    namespace Astream
    namespace Digest
    namespace TlaMerkleMountainRange

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Digest.TlaMerkleMountainRange.Satisfies M F
    prefix:75 "□" => _root_.Astream.Digest.TlaMerkleMountainRange.Always

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
    -- 3. Merkle Mountain Range Accumulator State Machine
    -- ========================================================================

    structure MmrState where
      activePeaks : UInt64
      maxPeaks    : UInt64
      prevLeaves  : UInt64
      leafCount   : UInt64

    def MmrSafetyInv (s : MmrState) : Prop :=
      Nat.le (UInt64.toNat s.activePeaks) (UInt64.toNat s.maxPeaks) ∧
      Nat.le (UInt64.toNat s.prevLeaves) (UInt64.toNat s.leafCount)

    def Init (maxPeaks : UInt64) (s : MmrState) : Prop :=
      s.activePeaks = (0 : UInt64) ∧
      s.maxPeaks = maxPeaks ∧
      s.prevLeaves = (0 : UInt64) ∧
      s.leafCount = (0 : UInt64)

    def AppendLeaf (rawPeaks nextLeaves : UInt64) (s sNext : MmrState) : Prop :=
      sNext.activePeaks = _root_.mmr_peaks_clamp rawPeaks s.maxPeaks ∧
      sNext.maxPeaks = s.maxPeaks ∧
      sNext.prevLeaves = s.leafCount ∧
      sNext.leafCount = _root_.mmr_leaves_advance s.leafCount nextLeaves

    def Next (s sNext : MmrState) : Prop :=
      ∃ rp : UInt64, ∃ nl : UInt64, AppendLeaf rp nl s sNext

    def Spec (maxPeaks : UInt64) : StateMachine MmrState :=
      StateMachine.mk (Init maxPeaks) Next

    theorem peaks_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.mmr_peaks_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem leaves_adv_ge : forall (cur : UInt64) (prop : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.mmr_leaves_advance cur prop)) :=
      fun cur prop => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur prop)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => prop))))
        (instDecidableUInt64Lt cur prop)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxPeaks : UInt64) (s : MmrState)
        (hInit : Init maxPeaks s) : MmrSafetyInv s :=
      let hEq : s.prevLeaves = s.leafCount := Eq.trans hInit.2.2.1 (Eq.symm hInit.2.2.2)
      let hL : Nat.le (UInt64.toNat s.prevLeaves) (UInt64.toNat s.leafCount) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.leafCount)) hEq)
          (@Nat.le.refl (UInt64.toNat s.leafCount))
      And.intro (zero_u64_le s.activePeaks s.maxPeaks hInit.1) hL

    theorem appendLeaf_preserves_inv (rp nl : UInt64) (s sNext : MmrState)
        (hAct : AppendLeaf rp nl s sNext) : MmrSafetyInv sNext :=
      let hP1 : Nat.le (UInt64.toNat sNext.activePeaks) (UInt64.toNat s.maxPeaks) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxPeaks)) hAct.1)
          (peaks_clamp_le rp s.maxPeaks)
      let hP2 : Nat.le (UInt64.toNat sNext.activePeaks) (UInt64.toNat sNext.maxPeaks) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.activePeaks) (UInt64.toNat y)) hAct.2.1)
          hP1
      let hAdv : Nat.le (UInt64.toNat s.leafCount)
          (UInt64.toNat (_root_.mmr_leaves_advance s.leafCount nl)) :=
        leaves_adv_ge s.leafCount nl
      let hL1 : Nat.le (UInt64.toNat sNext.prevLeaves)
          (UInt64.toNat (_root_.mmr_leaves_advance s.leafCount nl)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x)
            (UInt64.toNat (_root_.mmr_leaves_advance s.leafCount nl))) hAct.2.2.1)
          hAdv
      let hL2 : Nat.le (UInt64.toNat sNext.prevLeaves) (UInt64.toNat sNext.leafCount) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.prevLeaves) (UInt64.toNat y)) hAct.2.2.2)
          hL1
      And.intro hP2 hL2

    theorem next_preserves_inv (s sNext : MmrState)
        (_hInv : MmrSafetyInv s) (hNext : Next s sNext) : MmrSafetyInv sNext :=
      Exists.elim hNext (fun rp hEx2 =>
        Exists.elim hEx2 (fun nl hAct => appendLeaf_preserves_inv rp nl s sNext hAct))

    theorem spec_satisfies_mmr_accumulator_safety (maxPeaks : UInt64) :
        (Spec maxPeaks) ⊨ □ (Lift MmrSafetyInv) :=
      invariantSatisfies (Spec maxPeaks) MmrSafetyInv
        (init_establishes_inv maxPeaks)
        next_preserves_inv

    end TlaMerkleMountainRange
    end Digest
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def mmr_height_in_bounds_isl (height : UInt64) (max_peaks : UInt64) : Bool :=
      decide (height < max_peaks)
}
