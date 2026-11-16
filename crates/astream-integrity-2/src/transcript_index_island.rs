// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `transcript_index.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `transcript_index.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def transcript_field_clamp (cand_len : UInt64) (preview_cap : UInt64) : UInt64 :=
      if cand_len < preview_cap then cand_len else preview_cap

    def transcript_step_advance (cur_step : UInt64) (cand_step : UInt64) : UInt64 :=
      if cur_step < cand_step then cand_step else cur_step

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Transcript Index Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaDualTranscriptIndex

    def Behavior (State : Type) : Type := Nat → State

    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun (k : Nat) => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (n : Nat), P (drop n b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (n : Nat), M.Next (b n) (b (Nat.add n 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (P : Formula State) (Q : Formula State) : Prop :=
      ∀ (b : Behavior State), P b → Q b

    theorem invariantAt
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s')
      (b : Behavior State)
      (hRun : Runs M b)
      (k : Nat) :
      Inv (b k) :=
      Nat.rec
        (hInit (b 0) (And.left hRun))
        (fun (j : Nat) (ih : Inv (b j)) =>
          hStep (b j) (b (Nat.add j 1)) ih (And.right hRun j))
        k

    theorem invariantSatisfies
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s') :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure TranscriptIndexState where
      preview_bytes : UInt64
      preview_cap : UInt64
      step_idx : UInt64
      prev_step : UInt64

    def DualTranscriptIndexInv (s : TranscriptIndexState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.preview_bytes) (UInt64.toNat s.preview_cap))
        (Nat.le (UInt64.toNat s.prev_step) (UInt64.toNat s.step_idx))

    def Init (preview_cap : UInt64) (s : TranscriptIndexState) : Prop :=
      And
        (And (s.preview_bytes = 0) (s.preview_cap = preview_cap))
        (And (s.step_idx = 0) (s.prev_step = 0))

    def indexStep (cand_len : UInt64) (cand_step : UInt64) (s : TranscriptIndexState) : TranscriptIndexState :=
      TranscriptIndexState.mk
        (_root_.transcript_field_clamp cand_len s.preview_cap)
        s.preview_cap
        (_root_.transcript_step_advance s.step_idx cand_step)
        s.step_idx

    def Next (s : TranscriptIndexState) (s' : TranscriptIndexState) : Prop :=
      ∃ (cand_len : UInt64), ∃ (cand_step : UInt64),
        s' = indexStep cand_len cand_step s

    def Spec (preview_cap : UInt64) : StateMachine TranscriptIndexState :=
      StateMachine.mk (Init preview_cap) Next

    theorem field_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.transcript_field_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem step_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.transcript_step_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (preview_cap : UInt64) (s : TranscriptIndexState)
      (hInit : Init preview_cap s) :
      DualTranscriptIndexInv s :=
      And.intro
        (eq_zero_le s.preview_bytes s.preview_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_step s.step_idx (And.right (And.right hInit)))

    theorem next_preserves_inv (s : TranscriptIndexState) (s' : TranscriptIndexState)
      (_hInv : DualTranscriptIndexInv s) (hNext : Next s s') :
      DualTranscriptIndexInv s' :=
      Exists.elim hNext (fun (cl : UInt64) (hRest : ∃ (cs : UInt64), s' = indexStep cl cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = indexStep cl cs s) =>
          Eq.mpr
            (congrArg (fun (st : TranscriptIndexState) => DualTranscriptIndexInv st) hEq)
            (And.intro
              (field_clamp_le cl s.preview_cap)
              (step_monotone s.step_idx cs))))

    theorem dual_transcript_index_safety_always (preview_cap : UInt64) :
      Satisfies (Runs (Spec preview_cap)) (Always (Lift DualTranscriptIndexInv)) :=
      invariantSatisfies (Spec preview_cap) DualTranscriptIndexInv (init_establishes_inv preview_cap) next_preserves_inv

    end TlaDualTranscriptIndex
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def transcript_preview_within_cap_isl (preview_len : UInt64) (preview_cap : UInt64) : Bool :=
      decide (preview_len <= preview_cap)
}
