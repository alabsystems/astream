// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `OSC 52` clipboard write-only filtering and bounded Base64 decode
// budgeting (`Astream.Term.TlaOsc52ClipboardBudget`), mounted under `cfg(clean_islands)`
// in `osc52_clipboard_budget.rs`. Proves `decodedBytes <= maxClipboardBytes` and
// `encodedBytes <= maxWireBytes`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def osc52_decoded_clamp (decoded_bytes : UInt64) (max_decoded : UInt64) : UInt64 :=
      if decoded_bytes < max_decoded then decoded_bytes else max_decoded

    def osc52_wire_clamp (encoded_bytes : UInt64) (max_wire : UInt64) : UInt64 :=
      if encoded_bytes < max_wire then encoded_bytes else max_wire

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaOsc52ClipboardBudget)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaOsc52ClipboardBudget

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaOsc52ClipboardBudget.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaOsc52ClipboardBudget.Always

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
    -- 3. `OSC 52` Clipboard Security & Byte-Budget State Machine
    -- ========================================================================

    structure Osc52State where
      decodedBytes      : UInt64
      maxClipboardBytes : UInt64
      encodedBytes      : UInt64
      maxWireBytes      : UInt64

    def Osc52Inv (s : Osc52State) : Prop :=
      Nat.le (UInt64.toNat s.decodedBytes) (UInt64.toNat s.maxClipboardBytes) ∧
      Nat.le (UInt64.toNat s.encodedBytes) (UInt64.toNat s.maxWireBytes)

    def Init (maxClipboardBytes maxWireBytes : UInt64) (s : Osc52State) : Prop :=
      s.decodedBytes = (0 : UInt64) ∧
      s.maxClipboardBytes = maxClipboardBytes ∧
      s.encodedBytes = (0 : UInt64) ∧
      s.maxWireBytes = maxWireBytes

    def AcceptOsc52Payload (rawDecoded rawEncoded : UInt64) (s sNext : Osc52State) : Prop :=
      sNext.decodedBytes = _root_.osc52_decoded_clamp rawDecoded s.maxClipboardBytes ∧
      sNext.maxClipboardBytes = s.maxClipboardBytes ∧
      sNext.encodedBytes = _root_.osc52_wire_clamp rawEncoded s.maxWireBytes ∧
      sNext.maxWireBytes = s.maxWireBytes

    def Next (s sNext : Osc52State) : Prop :=
      ∃ rd : UInt64, ∃ re : UInt64, AcceptOsc52Payload rd re s sNext

    def Spec (maxClipboardBytes maxWireBytes : UInt64) : StateMachine Osc52State :=
      StateMachine.mk (Init maxClipboardBytes maxWireBytes) Next

    theorem dec_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc52_decoded_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem wire_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc52_wire_clamp cand cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (maxClipboardBytes maxWireBytes : UInt64) (s : Osc52State)
        (hInit : Init maxClipboardBytes maxWireBytes s) : Osc52Inv s :=
      And.intro
        (zero_u64_le s.decodedBytes s.maxClipboardBytes hInit.1)
        (zero_u64_le s.encodedBytes s.maxWireBytes hInit.2.2.1)

    theorem acceptOsc52Payload_preserves_inv (rd re : UInt64) (s sNext : Osc52State)
        (hAct : AcceptOsc52Payload rd re s sNext) : Osc52Inv sNext :=
      let hD1 : Nat.le (UInt64.toNat sNext.decodedBytes) (UInt64.toNat s.maxClipboardBytes) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxClipboardBytes)) hAct.1)
          (dec_clamp_le rd s.maxClipboardBytes)
      let hD2 : Nat.le (UInt64.toNat sNext.decodedBytes) (UInt64.toNat sNext.maxClipboardBytes) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.decodedBytes) (UInt64.toNat y)) hAct.2.1)
          hD1
      let hW1 : Nat.le (UInt64.toNat sNext.encodedBytes) (UInt64.toNat s.maxWireBytes) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxWireBytes)) hAct.2.2.1)
          (wire_clamp_le re s.maxWireBytes)
      let hW2 : Nat.le (UInt64.toNat sNext.encodedBytes) (UInt64.toNat sNext.maxWireBytes) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.encodedBytes) (UInt64.toNat y)) hAct.2.2.2)
          hW1
      And.intro hD2 hW2

    theorem next_preserves_inv (s sNext : Osc52State)
        (_hInv : Osc52Inv s) (hNext : Next s sNext) : Osc52Inv sNext :=
      Exists.elim hNext (fun rd hEx2 =>
        Exists.elim hEx2 (fun re hAct => acceptOsc52Payload_preserves_inv rd re s sNext hAct))

    theorem spec_satisfies_osc52_clipboard_budget_safety (maxClipboardBytes maxWireBytes : UInt64) :
        (Spec maxClipboardBytes maxWireBytes) ⊨ □ (Lift Osc52Inv) :=
      invariantSatisfies (Spec maxClipboardBytes maxWireBytes) Osc52Inv
        (init_establishes_inv maxClipboardBytes maxWireBytes)
        next_preserves_inv

    end TlaOsc52ClipboardBudget
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def osc52_within_budget_isl (byte_len : UInt64) (budget : UInt64) : Bool :=
      decide (byte_len ≤ budget)
}
