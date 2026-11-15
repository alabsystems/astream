// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `osc7_cwd.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `osc7_cwd.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def osc7_path_clamp (cand_len : UInt64) (max_path_bytes : UInt64) : UInt64 :=
      if cand_len < max_path_bytes then cand_len else max_path_bytes

    def osc7_seq_advance (cur_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_seq < cand_seq then cand_seq else cur_seq

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & OSC 7 Working Dir Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaOsc7WorkingDir

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

    structure Osc7State where
      cwd_bytes : UInt64
      max_path_bytes : UInt64
      cwd_seq : UInt64
      prev_seq : UInt64

    def Osc7WorkingDirInv (s : Osc7State) : Prop :=
      And
        (Nat.le (UInt64.toNat s.cwd_bytes) (UInt64.toNat s.max_path_bytes))
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.cwd_seq))

    def Init (max_path_bytes : UInt64) (s : Osc7State) : Prop :=
      And
        (And (s.cwd_bytes = 0) (s.max_path_bytes = max_path_bytes))
        (And (s.cwd_seq = 0) (s.prev_seq = 0))

    def cwdUpdateStep (cand_len : UInt64) (cand_seq : UInt64) (s : Osc7State) : Osc7State :=
      Osc7State.mk
        (_root_.osc7_path_clamp cand_len s.max_path_bytes)
        s.max_path_bytes
        (_root_.osc7_seq_advance s.cwd_seq cand_seq)
        s.cwd_seq

    def Next (s : Osc7State) (s' : Osc7State) : Prop :=
      ∃ (cand_len : UInt64), ∃ (cand_seq : UInt64),
        s' = cwdUpdateStep cand_len cand_seq s

    def Spec (max_path_bytes : UInt64) : StateMachine Osc7State :=
      StateMachine.mk (Init max_path_bytes) Next

    theorem path_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc7_path_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem seq_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.osc7_seq_advance cur cand)) :=
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

    theorem init_establishes_inv (max_path_bytes : UInt64) (s : Osc7State)
      (hInit : Init max_path_bytes s) :
      Osc7WorkingDirInv s :=
      And.intro
        (eq_zero_le s.cwd_bytes s.max_path_bytes (And.left (And.left hInit)))
        (eq_zero_le s.prev_seq s.cwd_seq (And.right (And.right hInit)))

    theorem next_preserves_inv (s : Osc7State) (s' : Osc7State)
      (_hInv : Osc7WorkingDirInv s) (hNext : Next s s') :
      Osc7WorkingDirInv s' :=
      Exists.elim hNext (fun (cl : UInt64) (hRest : ∃ (cs : UInt64), s' = cwdUpdateStep cl cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = cwdUpdateStep cl cs s) =>
          Eq.mpr
            (congrArg (fun (st : Osc7State) => Osc7WorkingDirInv st) hEq)
            (And.intro
              (path_clamp_le cl s.max_path_bytes)
              (seq_monotone s.cwd_seq cs))))

    theorem osc7_working_dir_safety_always (max_path_bytes : UInt64) :
      Satisfies (Runs (Spec max_path_bytes)) (Always (Lift Osc7WorkingDirInv)) :=
      invariantSatisfies (Spec max_path_bytes) Osc7WorkingDirInv (init_establishes_inv max_path_bytes) next_preserves_inv

    end TlaOsc7WorkingDir
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def osc7_path_within_cap_isl (path_len : UInt64) (max_path_bytes : UInt64) : Bool :=
      decide (path_len <= max_path_bytes)
}
