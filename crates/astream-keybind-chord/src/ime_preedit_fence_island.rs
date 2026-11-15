// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `ime_preedit_fence.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `ime_preedit_fence.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def kc_ime_clamp (raw : UInt64) (cap : UInt64) : UInt64 :=
      if raw < cap then raw else cap

    def kc_comp_advance (prev : UInt64) (cand : UInt64) : UInt64 :=
      if prev < cand then cand else prev

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Protocol Safety Spec
    -- =======================================================================

    namespace Astream
    namespace KeyChord
    namespace TlaImePreeditFence
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

    structure ImePreeditFenceState where
      bounded_val : UInt64
      max_cap : UInt64
      watermark : UInt64
      prev_watermark : UInt64

    def ImePreeditFenceInv (s : ImePreeditFenceState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.bounded_val) (UInt64.toNat s.max_cap))
        (Nat.le (UInt64.toNat s.prev_watermark) (UInt64.toNat s.watermark))

    def Init (s : ImePreeditFenceState) : Prop :=
      And
        (s.bounded_val = 0)
        (And (s.watermark = 0) (s.prev_watermark = 0))

    def stepTransition (raw_val : UInt64) (cand_wm : UInt64) (s : ImePreeditFenceState) : ImePreeditFenceState :=
      ImePreeditFenceState.mk
        (_root_.kc_ime_clamp raw_val s.max_cap)
        s.max_cap
        (_root_.kc_comp_advance s.watermark cand_wm)
        s.watermark

    def Next (s : ImePreeditFenceState) (s' : ImePreeditFenceState) : Prop :=
      ∃ (raw_val : UInt64), ∃ (cand_wm : UInt64),
        s' = stepTransition raw_val cand_wm s

    def Spec : StateMachine ImePreeditFenceState :=
      StateMachine.mk Init Next

    theorem clamp_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kc_ime_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem watermark_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.kc_comp_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (_hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : ImePreeditFenceState) (hInit : Init s) :
      ImePreeditFenceInv s :=
      And.intro
        (zero_le_cap s.bounded_val s.max_cap (And.left hInit))
        (eq_zero_le
          s.prev_watermark
          s.watermark
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : ImePreeditFenceState) (s' : ImePreeditFenceState)
      (_hInv : ImePreeditFenceInv s) (hNext : Next s s') :
      ImePreeditFenceInv s' :=
      Exists.elim hNext (fun (rv : UInt64) (hRest : ∃ (cw : UInt64), s' = stepTransition rv cw s) =>
        Exists.elim hRest (fun (cw : UInt64) (hEq : s' = stepTransition rv cw s) =>
          Eq.mpr
            (congrArg (fun (st : ImePreeditFenceState) => ImePreeditFenceInv st) hEq)
            (And.intro
              (clamp_le_cap rv s.max_cap)
              (watermark_monotone s.watermark cw))))

    theorem ime_preedit_fence_safety_always :
      Satisfies Spec (Always (Lift ImePreeditFenceInv)) :=
      invariantSatisfies Spec ImePreeditFenceInv init_establishes_inv next_preserves_inv

    end TlaImePreeditFence
    end KeyChord
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def kc_passthrough_ready_isl (observed : UInt64) (threshold : UInt64) : Bool :=
      decide (threshold ≤ observed)
}
