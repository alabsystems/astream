// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for SIGHUP-driven capability/principal revocation reload fencing
// (`Astream.Cap.TlaPrincipalRevocationSighup`, Island #285), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def revoc_sighup_gen_advance (cur_gen : UInt64) (observed_gen : UInt64) : UInt64 :=
      if cur_gen < observed_gen then observed_gen else cur_gen

    def revoc_entry_count_clamp (entries : UInt64) (max_entries : UInt64) : UInt64 :=
      if entries < max_entries then entries else max_entries

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & SIGHUP Revocation Spec
    -- =======================================================================

    namespace Astream
    namespace Cap
    namespace TlaPrincipalRevocationSighup

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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next)
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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next) :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure RevocReloadState where
      prev_gen : UInt64
      loaded_gen : UInt64
      entries : UInt64
      max_entries : UInt64

    def RevocSafetyInv (s : RevocReloadState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_gen) (UInt64.toNat s.loaded_gen))
        (Nat.le (UInt64.toNat s.entries) (UInt64.toNat s.max_entries))

    def Init (s : RevocReloadState) : Prop :=
      And
        (s.prev_gen = s.loaded_gen)
        (Nat.le (UInt64.toNat s.entries) (UInt64.toNat s.max_entries))

    def reloadStep (sig_gen : UInt64) (raw_entries : UInt64) (s : RevocReloadState) : RevocReloadState :=
      RevocReloadState.mk
        s.loaded_gen
        (_root_.revoc_sighup_gen_advance s.loaded_gen sig_gen)
        (_root_.revoc_entry_count_clamp raw_entries s.max_entries)
        s.max_entries

    def Next (s : RevocReloadState) (s_next : RevocReloadState) : Prop :=
      ∃ (sig_gen : UInt64), ∃ (raw_entries : UInt64),
        s_next = reloadStep sig_gen raw_entries s

    def Spec : StateMachine RevocReloadState :=
      StateMachine.mk Init Next

    theorem gen_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.revoc_sighup_gen_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem entries_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.revoc_entry_count_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : RevocReloadState) (hInit : Init s) :
      RevocSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_gen s.loaded_gen (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : RevocReloadState) (s_next : RevocReloadState)
      (_hInv : RevocSafetyInv s) (hNext : Next s s_next) :
      RevocSafetyInv s_next :=
      Exists.elim hNext (fun (sg : UInt64) (hRest : ∃ (re : UInt64), s_next = reloadStep sg re s) =>
        Exists.elim hRest (fun (re : UInt64) (hEq : s_next = reloadStep sg re s) =>
          Eq.mpr
            (congrArg (fun (st : RevocReloadState) => RevocSafetyInv st) hEq)
            (And.intro
              (gen_ge_prev s.loaded_gen sg)
              (entries_le_cap re s.max_entries))))

    theorem revoc_reload_safety_always :
      Satisfies (Runs Spec) (Always (Lift RevocSafetyInv)) :=
      invariantSatisfies Spec RevocSafetyInv init_establishes_inv next_preserves_inv

    end TlaPrincipalRevocationSighup
    end Cap
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def revoc_reload_needed_isl (loaded_gen : UInt64) (sighup_gen : UInt64) : Bool :=
      decide (loaded_gen < sighup_gen)
}
