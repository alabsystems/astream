// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `wal_prealloc_arena.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `wal_prealloc_arena.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def wal_logical_clamp (cand_logical : UInt64) (reserved_bytes : UInt64) : UInt64 :=
      if cand_logical < reserved_bytes then cand_logical else reserved_bytes

    def wal_reserved_advance (cur_reserved : UInt64) (cand_reserved : UInt64) : UInt64 :=
      if cur_reserved < cand_reserved then cand_reserved else cur_reserved

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & WAL Extent Planner Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaWalExtentPlanner
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

    structure WalExtentState where
      logical_len : UInt64
      reserved_bytes : UInt64
      prev_reserved : UInt64

    def WalExtentInv (s : WalExtentState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.logical_len) (UInt64.toNat s.reserved_bytes))
        (Nat.le (UInt64.toNat s.prev_reserved) (UInt64.toNat s.reserved_bytes))

    def Init (init_reserved : UInt64) (s : WalExtentState) : Prop :=
      And
        (And (s.logical_len = 0) (s.reserved_bytes = init_reserved))
        (s.prev_reserved = 0)

    def extentStep (cand_logical : UInt64) (cand_reserved : UInt64) (s : WalExtentState) : WalExtentState :=
      let next_res := _root_.wal_reserved_advance s.reserved_bytes cand_reserved
      WalExtentState.mk
        (_root_.wal_logical_clamp cand_logical next_res)
        next_res
        s.reserved_bytes

    def Next (s : WalExtentState) (s' : WalExtentState) : Prop :=
      ∃ (cand_logical : UInt64), ∃ (cand_reserved : UInt64),
        s' = extentStep cand_logical cand_reserved s

    def Spec (init_reserved : UInt64) : StateMachine WalExtentState :=
      StateMachine.mk (Init init_reserved) Next

    theorem logical_clamp_le : forall (cand : UInt64) (res : UInt64),
        Nat.le (UInt64.toNat (_root_.wal_logical_clamp cand res)) (UInt64.toNat res) :=
      fun cand res => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand res)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => res) (fun _ => cand))) (UInt64.toNat res))
        (instDecidableUInt64Lt cand res)
        (fun _ => @Nat.le.refl (UInt64.toNat res))
        (fun hLt => Nat.le_of_lt hLt)

    theorem reserved_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.wal_reserved_advance cur cand)) :=
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

    theorem init_establishes_inv (init_reserved : UInt64) (s : WalExtentState)
      (hInit : Init init_reserved s) :
      WalExtentInv s :=
      And.intro
        (eq_zero_le s.logical_len s.reserved_bytes (And.left (And.left hInit)))
        (eq_zero_le s.prev_reserved s.reserved_bytes (And.right hInit))

    theorem next_preserves_inv (s : WalExtentState) (s' : WalExtentState)
      (_hInv : WalExtentInv s) (hNext : Next s s') :
      WalExtentInv s' :=
      Exists.elim hNext (fun (cl : UInt64) (hRest : ∃ (cr : UInt64), s' = extentStep cl cr s) =>
        Exists.elim hRest (fun (cr : UInt64) (hEq : s' = extentStep cl cr s) =>
          Eq.mpr
            (congrArg (fun (st : WalExtentState) => WalExtentInv st) hEq)
            (And.intro
              (logical_clamp_le cl (_root_.wal_reserved_advance s.reserved_bytes cr))
              (reserved_monotone s.reserved_bytes cr))))

    theorem wal_extent_planner_safety_always (init_reserved : UInt64) :
      Satisfies (Spec init_reserved) (Always (Lift WalExtentInv)) :=
      invariantSatisfies (Spec init_reserved) WalExtentInv (init_establishes_inv init_reserved) next_preserves_inv

    end TlaWalExtentPlanner
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def wal_logical_within_reserved_isl (logical_len : UInt64) (reserved_bytes : UInt64) : Bool :=
      decide (logical_len <= reserved_bytes)
}
