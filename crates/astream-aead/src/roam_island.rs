// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `roam.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `roam.rs` mounts this file under `cfg(clean_islands)`,
// which build.rs sets when the compiler answers that it is Trust. Every other compiler calls
// the plain-Rust twins in `twins.rs` of the functions it compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    -- ========================================================================
    def roam_amp_budget_clamp (tx_cand : UInt64) (budget_cap : UInt64) : UInt64 :=
      if tx_cand < budget_cap then tx_cand else budget_cap

    def roam_epoch_advance (prev : UInt64) (cand : UInt64) : UInt64 :=
      if prev < cand then cand else prev

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Aead.TlaRoamMigration)
    -- ========================================================================
    namespace Astream
    namespace Aead
    namespace TlaRoamMigration

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

    structure RoamMigrationState where
      unval_tx : UInt64
      unval_budget : UInt64
      epoch : UInt64
      prev_epoch : UInt64
      acked_offset : UInt64
      sent_offset : UInt64

    def RoamMigrationInv (s : RoamMigrationState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.unval_tx) (UInt64.toNat s.unval_budget))
        (And
          (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.epoch))
          (Nat.le (UInt64.toNat s.acked_offset) (UInt64.toNat s.sent_offset)))

    def Init (s : RoamMigrationState) : Prop :=
      And
        (s.unval_tx = 0)
        (And
          (s.epoch = 0)
          (And
            (s.prev_epoch = 0)
            (And (s.acked_offset = 0) (s.sent_offset = 0))))

    def stepTransition (tx_cand : UInt64) (cand_ep : UInt64) (ack_cand : UInt64) (send_cand : UInt64)
        (s : RoamMigrationState) : RoamMigrationState :=
      RoamMigrationState.mk
        (_root_.roam_amp_budget_clamp tx_cand s.unval_budget)
        s.unval_budget
        (_root_.roam_epoch_advance s.epoch cand_ep)
        s.epoch
        (_root_.roam_amp_budget_clamp ack_cand (_root_.roam_epoch_advance s.sent_offset send_cand))
        (_root_.roam_epoch_advance s.sent_offset send_cand)

    def Next (s : RoamMigrationState) (s' : RoamMigrationState) : Prop :=
      ∃ (tx_cand : UInt64), ∃ (cand_ep : UInt64), ∃ (ack_cand : UInt64), ∃ (send_cand : UInt64),
        s' = stepTransition tx_cand cand_ep ack_cand send_cand s

    def Spec : StateMachine RoamMigrationState :=
      StateMachine.mk Init Next

    theorem clamp_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.roam_amp_budget_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.roam_epoch_advance prev cand)) :=
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

    theorem init_establishes_inv (s : RoamMigrationState) (hInit : Init s) :
        RoamMigrationInv s :=
      And.intro
        (zero_le_cap s.unval_tx s.unval_budget (And.left hInit))
        (And.intro
          (eq_zero_le
            s.prev_epoch
            s.epoch
            (And.left (And.right (And.right hInit)))
            (And.left (And.right hInit)))
          (eq_zero_le
            s.acked_offset
            s.sent_offset
            (And.left (And.right (And.right (And.right hInit))))
            (And.right (And.right (And.right (And.right hInit))))))

    theorem next_preserves_inv (s : RoamMigrationState) (s' : RoamMigrationState)
        (_hInv : RoamMigrationInv s) (hNext : Next s s') :
        RoamMigrationInv s' :=
      Exists.elim hNext (fun (txc : UInt64) (h1 : ∃ (ce : UInt64), ∃ (ac : UInt64), ∃ (sc : UInt64), s' = stepTransition txc ce ac sc s) =>
        Exists.elim h1 (fun (ce : UInt64) (h2 : ∃ (ac : UInt64), ∃ (sc : UInt64), s' = stepTransition txc ce ac sc s) =>
          Exists.elim h2 (fun (ac : UInt64) (h3 : ∃ (sc : UInt64), s' = stepTransition txc ce ac sc s) =>
            Exists.elim h3 (fun (sc : UInt64) (hEq : s' = stepTransition txc ce ac sc s) =>
              Eq.mpr
                (congrArg (fun (st : RoamMigrationState) => RoamMigrationInv st) hEq)
                (And.intro
                  (clamp_le_cap txc s.unval_budget)
                  (And.intro
                    (epoch_monotone s.epoch ce)
                    (clamp_le_cap ac (_root_.roam_epoch_advance s.sent_offset sc))))))))

    theorem roam_migration_safety_always :
        Satisfies Spec (Always (Lift RoamMigrationInv)) :=
      invariantSatisfies Spec RoamMigrationInv init_establishes_inv next_preserves_inv

    end TlaRoamMigration
    end Aead
    end Astream

    -- ========================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- ========================================================================
    def roam_amp_allows_send_isl (tx_after : UInt64) (budget_cap : UInt64) : Bool :=
      decide (tx_after ≤ budget_cap)

    def roam_contig_offset_matches_isl (frame_offset : UInt64) (recv_cursor : UInt64) : Bool :=
      decide (frame_offset = recv_cursor)
}
