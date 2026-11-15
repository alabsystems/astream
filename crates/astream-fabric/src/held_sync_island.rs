// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `held_sync.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `held_sync.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def held_sync_base_advance (replica_base : UInt64) (leader_base : UInt64) : UInt64 :=
      if replica_base < leader_base then leader_base else replica_base

    def held_sync_order_ok_code (low : UInt64) (high : UInt64) : UInt64 :=
      if high < low then 0 else 1

    def held_sync_gate_select (admissible : UInt64) (keep_val : UInt64) (next_val : UInt64) : UInt64 :=
      if admissible < 1 then keep_val else next_val

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Held-Replica Sync Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaHeldReplicaSync

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

    def held_sync_admissible_code_isl (id_ok : UInt64) (replica_base : UInt64) (leader_base : UInt64) (replica_head : UInt64) : UInt64 :=
      _root_.held_sync_gate_select id_ok (0 : UInt64)
        (_root_.held_sync_gate_select
          (_root_.held_sync_order_ok_code replica_base leader_base)
          (0 : UInt64)
          (_root_.held_sync_order_ok_code leader_base replica_head))

    def held_sync_next_base_isl (admissible : UInt64) (replica_base : UInt64) (leader_base : UInt64) : UInt64 :=
      _root_.held_sync_gate_select admissible replica_base
        (_root_.held_sync_base_advance replica_base leader_base)

    structure HeldSyncState where
      prev_base : UInt64
      replica_base : UInt64

    def HeldSyncMonotoneInv (s : HeldSyncState) : Prop :=
      Nat.le (UInt64.toNat s.prev_base) (UInt64.toNat s.replica_base)

    def Init (s : HeldSyncState) : Prop :=
      s.prev_base = s.replica_base

    def syncStepAction (id_ok : UInt64) (leader_base : UInt64) (replica_head : UInt64) (s : HeldSyncState) : HeldSyncState :=
      HeldSyncState.mk
        s.replica_base
        (held_sync_next_base_isl (held_sync_admissible_code_isl id_ok s.replica_base leader_base replica_head) s.replica_base leader_base)

    def Next (s : HeldSyncState) (s' : HeldSyncState) : Prop :=
      ∃ (id_ok : UInt64), ∃ (leader_base : UInt64), ∃ (replica_head : UInt64),
        s' = syncStepAction id_ok leader_base replica_head s

    def Spec : StateMachine HeldSyncState :=
      StateMachine.mk Init Next

    theorem next_base_ge_prev : forall (adm : UInt64) (rep_base : UInt64) (ldr_base : UInt64),
        Nat.le (UInt64.toNat rep_base) (UInt64.toNat (held_sync_next_base_isl adm rep_base ldr_base)) :=
      fun adm rep_base ldr_base => Decidable.casesOn
        (motive := fun (d0 : Decidable (LT.lt adm 1)) =>
          Nat.le (UInt64.toNat rep_base) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d0
            (fun _ => _root_.held_sync_base_advance rep_base ldr_base)
            (fun _ => rep_base))))
        (instDecidableUInt64Lt adm 1)
        (fun _ => Decidable.casesOn
          (motive := fun (d1 : Decidable (LT.lt rep_base ldr_base)) =>
            Nat.le (UInt64.toNat rep_base) (UInt64.toNat (Decidable.casesOn
              (motive := fun _ => UInt64) d1
              (fun _ => rep_base)
              (fun _ => ldr_base))))
          (instDecidableUInt64Lt rep_base ldr_base)
          (fun _ => Nat.le.refl (UInt64.toNat rep_base))
          (fun hLt => Nat.le_of_lt hLt))
        (fun _ => Nat.le.refl (UInt64.toNat rep_base))

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : HeldSyncState) (hInit : Init s) :
      HeldSyncMonotoneInv s :=
      uint64_eq_le s.prev_base s.replica_base hInit

    theorem next_preserves_inv (s : HeldSyncState) (s' : HeldSyncState)
      (_hInv : HeldSyncMonotoneInv s) (hNext : Next s s') :
      HeldSyncMonotoneInv s' :=
      Exists.elim hNext (fun (id_ok : UInt64) (h1 : ∃ (leader_base : UInt64), ∃ (replica_head : UInt64), s' = syncStepAction id_ok leader_base replica_head s) =>
        Exists.elim h1 (fun (leader_base : UInt64) (h2 : ∃ (replica_head : UInt64), s' = syncStepAction id_ok leader_base replica_head s) =>
          Exists.elim h2 (fun (replica_head : UInt64) (hEq : s' = syncStepAction id_ok leader_base replica_head s) =>
            Eq.mpr
              (congrArg (fun (st : HeldSyncState) => HeldSyncMonotoneInv st) hEq)
              (next_base_ge_prev (held_sync_admissible_code_isl id_ok s.replica_base leader_base replica_head) s.replica_base leader_base))))

    theorem held_sync_monotone_always :
      Satisfies Spec (Always (Lift HeldSyncMonotoneInv)) :=
      invariantSatisfies Spec HeldSyncMonotoneInv init_establishes_inv next_preserves_inv

    end TlaHeldReplicaSync
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def held_sync_code_is_admissible_isl (code : UInt64) : Bool :=
      decide (code = 1)
}
