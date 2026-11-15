// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `will_compaction.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `will_compaction.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def anchor_copy_clamp (proposed_copies : UInt64) (copy_cap : UInt64) : UInt64 :=
      if proposed_copies < copy_cap then proposed_copies else copy_cap

    def retain_base_advance (cur_base : UInt64) (cand_base : UInt64) : UInt64 :=
      if cur_base < cand_base then cand_base else cur_base

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Anchor Rollover Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaWillBindCompaction

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

    structure WillCompactionState where
      copied_anchors : UInt64
      copy_cap : UInt64
      base_offset : UInt64
      prev_base : UInt64

    def WillCompactionInv (s : WillCompactionState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.copied_anchors) (UInt64.toNat s.copy_cap))
        (Nat.le (UInt64.toNat s.prev_base) (UInt64.toNat s.base_offset))

    def Init (copy_cap : UInt64) (s : WillCompactionState) : Prop :=
      And
        (And (s.copied_anchors = 0) (s.copy_cap = copy_cap))
        (And (s.base_offset = 0) (s.prev_base = 0))

    def rolloverStep (cand_copies : UInt64) (cand_base : UInt64) (s : WillCompactionState) : WillCompactionState :=
      WillCompactionState.mk
        (_root_.anchor_copy_clamp cand_copies s.copy_cap)
        s.copy_cap
        (_root_.retain_base_advance s.base_offset cand_base)
        s.base_offset

    def Next (s : WillCompactionState) (s' : WillCompactionState) : Prop :=
      ∃ (cand_copies : UInt64), ∃ (cand_base : UInt64),
        s' = rolloverStep cand_copies cand_base s

    def Spec (copy_cap : UInt64) : StateMachine WillCompactionState :=
      StateMachine.mk (Init copy_cap) Next

    theorem copy_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.anchor_copy_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem base_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.retain_base_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (copy_cap : UInt64) (s : WillCompactionState)
      (hInit : Init copy_cap s) :
      WillCompactionInv s :=
      And.intro
        (eq_zero_le s.copied_anchors s.copy_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_base s.base_offset (And.right (And.right hInit)))

    theorem next_preserves_inv (s : WillCompactionState) (s' : WillCompactionState)
      (_hInv : WillCompactionInv s) (hNext : Next s s') :
      WillCompactionInv s' :=
      Exists.elim hNext (fun (cc : UInt64) (hRest : ∃ (cb : UInt64), s' = rolloverStep cc cb s) =>
        Exists.elim hRest (fun (cb : UInt64) (hEq : s' = rolloverStep cc cb s) =>
          Eq.mpr
            (congrArg (fun (st : WillCompactionState) => WillCompactionInv st) hEq)
            (And.intro
              (copy_clamp_le cc s.copy_cap)
              (base_monotone s.base_offset cb))))

    theorem will_bind_compaction_safety_always (copy_cap : UInt64) :
      Satisfies (Spec copy_cap) (Always (Lift WillCompactionInv)) :=
      invariantSatisfies (Spec copy_cap) WillCompactionInv (init_establishes_inv copy_cap) next_preserves_inv

    end TlaWillBindCompaction
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def anchor_pinned_below_cut_isl (anchor_offset : UInt64) (cut_offset : UInt64) : Bool :=
      decide (anchor_offset < cut_offset)
}
