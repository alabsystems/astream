// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `env_strip.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `env_strip.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def env_entry_count_clamp (count : UInt64) (max_entries : UInt64) : UInt64 :=
      if count < max_entries then count else max_entries

    def env_stripped_advance (prev_stripped : UInt64) (cand_stripped : UInt64) : UInt64 :=
      if prev_stripped < cand_stripped then cand_stripped else prev_stripped

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & aterm Env Strip Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaEnvStripPolicy

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

    structure EnvStripState where
      retained_entries : UInt64
      max_entries : UInt64
      stripped_total : UInt64
      prev_stripped : UInt64

    def EnvStripInv (s : EnvStripState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.retained_entries) (UInt64.toNat s.max_entries))
        (Nat.le (UInt64.toNat s.prev_stripped) (UInt64.toNat s.stripped_total))

    def Init (s : EnvStripState) : Prop :=
      And
        (s.retained_entries = 0)
        (And (s.stripped_total = 0) (s.prev_stripped = 0))

    def envStep (raw_entries : UInt64) (cand_stripped : UInt64) (s : EnvStripState) : EnvStripState :=
      EnvStripState.mk
        (_root_.env_entry_count_clamp raw_entries s.max_entries)
        s.max_entries
        (_root_.env_stripped_advance s.stripped_total cand_stripped)
        s.stripped_total

    def Next (s : EnvStripState) (s' : EnvStripState) : Prop :=
      ∃ (raw_entries : UInt64), ∃ (cand_stripped : UInt64),
        s' = envStep raw_entries cand_stripped s

    def Spec : StateMachine EnvStripState :=
      StateMachine.mk Init Next

    theorem entries_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.env_entry_count_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem stripped_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.env_stripped_advance prev cand)) :=
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

    theorem init_establishes_inv (s : EnvStripState) (hInit : Init s) :
      EnvStripInv s :=
      And.intro
        (zero_le_cap s.retained_entries s.max_entries (And.left hInit))
        (eq_zero_le
          s.prev_stripped
          s.stripped_total
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : EnvStripState) (s' : EnvStripState)
      (_hInv : EnvStripInv s) (hNext : Next s s') :
      EnvStripInv s' :=
      Exists.elim hNext (fun (re : UInt64) (hRest : ∃ (cs : UInt64), s' = envStep re cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = envStep re cs s) =>
          Eq.mpr
            (congrArg (fun (st : EnvStripState) => EnvStripInv st) hEq)
            (And.intro
              (entries_le_max re s.max_entries)
              (stripped_monotone s.stripped_total cs))))

    theorem env_strip_safety_always :
      Satisfies (Runs Spec) (Always (Lift EnvStripInv)) :=
      invariantSatisfies Spec EnvStripInv init_establishes_inv next_preserves_inv

    end TlaEnvStripPolicy
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def env_pair_fits_budget_isl (pair_len : USize) (max_pair_bytes : USize) : Bool :=
      decide (pair_len ≤ max_pair_bytes)
}
