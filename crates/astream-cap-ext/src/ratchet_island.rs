// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `ratchet.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `ratchet.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def ratchet_epoch_advance (prev_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if prev_epoch < cand_epoch then cand_epoch else prev_epoch

    def ratchet_frame_seq_clamp (seq_in_epoch : UInt64) (interval : UInt64) : UInt64 :=
      if seq_in_epoch < interval then seq_in_epoch else interval

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Symmetric Ratchet Spec
    -- =======================================================================

    namespace Astream
    namespace Aead
    namespace TlaRekeyRatchet

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

    structure RekeyRatchetState where
      epoch : UInt64
      prev_epoch : UInt64
      frames_in_epoch : UInt64
      rekey_interval : UInt64

    def RekeyRatchetInv (s : RekeyRatchetState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.epoch))
        (Nat.le (UInt64.toNat s.frames_in_epoch) (UInt64.toNat s.rekey_interval))

    def Init (s : RekeyRatchetState) : Prop :=
      And
        (s.frames_in_epoch = 0)
        (And (s.epoch = 0) (s.prev_epoch = 0))

    def ratchetStep (cand_epoch : UInt64) (raw_frames : UInt64) (s : RekeyRatchetState) : RekeyRatchetState :=
      RekeyRatchetState.mk
        (_root_.ratchet_epoch_advance s.epoch cand_epoch)
        s.epoch
        (_root_.ratchet_frame_seq_clamp raw_frames s.rekey_interval)
        s.rekey_interval

    def Next (s : RekeyRatchetState) (s' : RekeyRatchetState) : Prop :=
      ∃ (cand_epoch : UInt64), ∃ (raw_frames : UInt64),
        s' = ratchetStep cand_epoch raw_frames s

    def Spec : StateMachine RekeyRatchetState :=
      StateMachine.mk Init Next

    theorem epoch_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.ratchet_epoch_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem frames_le_interval : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.ratchet_frame_seq_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
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

    theorem init_establishes_inv (s : RekeyRatchetState) (hInit : Init s) :
      RekeyRatchetInv s :=
      And.intro
        (eq_zero_le
          s.prev_epoch
          s.epoch
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.frames_in_epoch s.rekey_interval (And.left hInit))

    theorem next_preserves_inv (s : RekeyRatchetState) (s' : RekeyRatchetState)
      (_hInv : RekeyRatchetInv s) (hNext : Next s s') :
      RekeyRatchetInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (rf : UInt64), s' = ratchetStep ce rf s) =>
        Exists.elim hRest (fun (rf : UInt64) (hEq : s' = ratchetStep ce rf s) =>
          Eq.mpr
            (congrArg (fun (st : RekeyRatchetState) => RekeyRatchetInv st) hEq)
            (And.intro
              (epoch_monotone s.epoch ce)
              (frames_le_interval rf s.rekey_interval))))

    theorem rekey_ratchet_safety_always :
      Satisfies (Runs Spec) (Always (Lift RekeyRatchetInv)) :=
      invariantSatisfies Spec RekeyRatchetInv init_establishes_inv next_preserves_inv

    end TlaRekeyRatchet
    end Aead
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def ratchet_rekey_due_isl (frames_in_epoch : UInt64) (rekey_interval : UInt64) : Bool :=
      decide (rekey_interval ≤ frames_in_epoch)
}
