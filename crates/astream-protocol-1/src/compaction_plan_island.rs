// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `compaction_plan.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `compaction_plan.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def compact_base_advance (prev_base : UInt64) (cand_base : UInt64) : UInt64 :=
      if prev_base < cand_base then cand_base else prev_base

    def compact_floor_clamp (requested_before : UInt64) (safe_ceiling : UInt64) : UInt64 :=
      if requested_before < safe_ceiling then requested_before else safe_ceiling

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & /a/bind+/a/will Compaction
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaBindWillCompaction

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

    structure CompactionPlanState where
      base_offset : UInt64
      prev_base : UInt64
      planned_cut : UInt64
      safe_ceiling : UInt64

    def CompactionPlanInv (s : CompactionPlanState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_base) (UInt64.toNat s.base_offset))
        (Nat.le (UInt64.toNat s.planned_cut) (UInt64.toNat s.safe_ceiling))

    def Init (s : CompactionPlanState) : Prop :=
      And
        (s.planned_cut = 0)
        (And (s.base_offset = 0) (s.prev_base = 0))

    def compactStep (cand_base : UInt64) (req_cut : UInt64) (s : CompactionPlanState) : CompactionPlanState :=
      CompactionPlanState.mk
        (_root_.compact_base_advance s.base_offset cand_base)
        s.base_offset
        (_root_.compact_floor_clamp req_cut s.safe_ceiling)
        s.safe_ceiling

    def Next (s : CompactionPlanState) (s' : CompactionPlanState) : Prop :=
      ∃ (cand_base : UInt64), ∃ (req_cut : UInt64),
        s' = compactStep cand_base req_cut s

    def Spec : StateMachine CompactionPlanState :=
      StateMachine.mk Init Next

    theorem base_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.compact_base_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem cut_le_ceiling : forall (req : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.compact_floor_clamp req cap)) (UInt64.toNat cap) :=
      fun req cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt req cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => req))) (UInt64.toNat cap))
        (instDecidableUInt64Lt req cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : CompactionPlanState) (hInit : Init s) :
      CompactionPlanInv s :=
      And.intro
        (eq_zero_le
          s.prev_base
          s.base_offset
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.planned_cut s.safe_ceiling (And.left hInit))

    theorem next_preserves_inv (s : CompactionPlanState) (s' : CompactionPlanState)
      (_hInv : CompactionPlanInv s) (hNext : Next s s') :
      CompactionPlanInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (rc : UInt64), s' = compactStep cb rc s) =>
        Exists.elim hRest (fun (rc : UInt64) (hEq : s' = compactStep cb rc s) =>
          Eq.mpr
            (congrArg (fun (st : CompactionPlanState) => CompactionPlanInv st) hEq)
            (And.intro
              (base_monotone s.base_offset cb)
              (cut_le_ceiling rc s.safe_ceiling))))

    theorem compaction_plan_safety_always :
      Satisfies Spec (Always (Lift CompactionPlanInv)) :=
      invariantSatisfies Spec CompactionPlanInv init_establishes_inv next_preserves_inv

    end TlaBindWillCompaction
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def compact_entry_is_pinned_isl (active : Bool) (offset : UInt64) (cut : UInt64) : Bool :=
      and active (decide (offset < cut))
}
