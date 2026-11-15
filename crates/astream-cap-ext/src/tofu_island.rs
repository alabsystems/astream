// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `tofu.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `tofu.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def tofu_entries_clamp (entries : UInt64) (max_entries : UInt64) : UInt64 :=
      if entries < max_entries then entries else max_entries

    def tofu_epoch_advance (prev_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if prev_epoch < cand_epoch then cand_epoch else prev_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & §8.6 TOFU Pin Store Spec
    -- =======================================================================

    namespace Astream
    namespace Cap
    namespace TlaTofuPinStore

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

    structure TofuPinState where
      entry_count : UInt64
      max_entries : UInt64
      rotation_epoch : UInt64
      prev_epoch : UInt64

    def TofuPinInv (s : TofuPinState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.entry_count) (UInt64.toNat s.max_entries))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.rotation_epoch))

    def Init (s : TofuPinState) : Prop :=
      And
        (s.entry_count = 0)
        (And (s.rotation_epoch = 0) (s.prev_epoch = 0))

    def tofuStep (raw_entries : UInt64) (cand_epoch : UInt64) (s : TofuPinState) : TofuPinState :=
      TofuPinState.mk
        (_root_.tofu_entries_clamp raw_entries s.max_entries)
        s.max_entries
        (_root_.tofu_epoch_advance s.rotation_epoch cand_epoch)
        s.rotation_epoch

    def Next (s : TofuPinState) (s' : TofuPinState) : Prop :=
      ∃ (raw_entries : UInt64), ∃ (cand_epoch : UInt64),
        s' = tofuStep raw_entries cand_epoch s

    def Spec : StateMachine TofuPinState :=
      StateMachine.mk Init Next

    theorem entries_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.tofu_entries_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.tofu_epoch_advance prev cand)) :=
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

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : TofuPinState) (hInit : Init s) :
      TofuPinInv s :=
      And.intro
        (zero_le_cap s.entry_count s.max_entries (And.left hInit))
        (eq_zero_le
          s.prev_epoch
          s.rotation_epoch
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : TofuPinState) (s' : TofuPinState)
      (_hInv : TofuPinInv s) (hNext : Next s s') :
      TofuPinInv s' :=
      Exists.elim hNext (fun (re : UInt64) (hRest : ∃ (ce : UInt64), s' = tofuStep re ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = tofuStep re ce s) =>
          Eq.mpr
            (congrArg (fun (st : TofuPinState) => TofuPinInv st) hEq)
            (And.intro
              (entries_le_max re s.max_entries)
              (epoch_monotone s.rotation_epoch ce))))

    theorem tofu_pin_safety_always :
      Satisfies (Runs Spec) (Always (Lift TofuPinInv)) :=
      invariantSatisfies Spec TofuPinInv init_establishes_inv next_preserves_inv

    end TlaTofuPinStore
    end Cap
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def tofu_table_within_cap_isl (entries : USize) (max_entries : USize) : Bool :=
      decide (entries ≤ max_entries)
}
