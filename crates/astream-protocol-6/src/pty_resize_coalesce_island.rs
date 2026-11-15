// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `pty_resize_coalesce.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `pty_resize_coalesce.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def winsize_dim_clamp (cand_dim : UInt64) (max_dim : UInt64) : UInt64 :=
      if cand_dim < max_dim then cand_dim else max_dim

    def winsize_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Winsize Coalescer Spec
    -- =======================================================================

    namespace Astream
    namespace Pump
    namespace TlaWinsizeCoalescer

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

    structure WinsizeState where
      cols : UInt64
      rows : UInt64
      max_dim : UInt64
      emit_epoch : UInt64
      prev_epoch : UInt64

    def WinsizeCoalescerInv (s : WinsizeState) : Prop :=
      And
        (And
          (Nat.le (UInt64.toNat s.cols) (UInt64.toNat s.max_dim))
          (Nat.le (UInt64.toNat s.rows) (UInt64.toNat s.max_dim)))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.emit_epoch))

    def Init (max_dim : UInt64) (s : WinsizeState) : Prop :=
      And
        (And (s.cols = 0) (And (s.rows = 0) (s.max_dim = max_dim)))
        (And (s.emit_epoch = 0) (s.prev_epoch = 0))

    def resizeStep (cand_cols : UInt64) (cand_rows : UInt64) (cand_epoch : UInt64) (s : WinsizeState) : WinsizeState :=
      WinsizeState.mk
        (_root_.winsize_dim_clamp cand_cols s.max_dim)
        (_root_.winsize_dim_clamp cand_rows s.max_dim)
        s.max_dim
        (_root_.winsize_epoch_advance s.emit_epoch cand_epoch)
        s.emit_epoch

    def Next (s : WinsizeState) (s' : WinsizeState) : Prop :=
      ∃ (cc : UInt64), ∃ (cr : UInt64), ∃ (ce : UInt64),
        s' = resizeStep cc cr ce s

    def Spec (max_dim : UInt64) : StateMachine WinsizeState :=
      StateMachine.mk (Init max_dim) Next

    theorem dim_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.winsize_dim_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.winsize_epoch_advance cur cand)) :=
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

    theorem init_establishes_inv (max_dim : UInt64) (s : WinsizeState)
      (hInit : Init max_dim s) :
      WinsizeCoalescerInv s :=
      let hLeft := And.left hInit
      let hRight := And.right hInit
      And.intro
        (And.intro
          (eq_zero_le s.cols s.max_dim (And.left hLeft))
          (eq_zero_le s.rows s.max_dim (And.left (And.right hLeft))))
        (eq_zero_le s.prev_epoch s.emit_epoch (And.right hRight))

    theorem next_preserves_inv (s : WinsizeState) (s' : WinsizeState)
      (_hInv : WinsizeCoalescerInv s) (hNext : Next s s') :
      WinsizeCoalescerInv s' :=
      Exists.elim hNext (fun (cc : UInt64) (hR1 : ∃ (cr : UInt64), ∃ (ce : UInt64), s' = resizeStep cc cr ce s) =>
        Exists.elim hR1 (fun (cr : UInt64) (hR2 : ∃ (ce : UInt64), s' = resizeStep cc cr ce s) =>
          Exists.elim hR2 (fun (ce : UInt64) (hEq : s' = resizeStep cc cr ce s) =>
            Eq.mpr
              (congrArg (fun (st : WinsizeState) => WinsizeCoalescerInv st) hEq)
              (And.intro
                (And.intro
                  (dim_clamp_le cc s.max_dim)
                  (dim_clamp_le cr s.max_dim))
                (epoch_monotone s.emit_epoch ce)))))

    theorem winsize_coalescer_safety_always (max_dim : UInt64) :
      Satisfies (Runs (Spec max_dim)) (Always (Lift WinsizeCoalescerInv)) :=
      invariantSatisfies (Spec max_dim) WinsizeCoalescerInv (init_establishes_inv max_dim) next_preserves_inv

    end TlaWinsizeCoalescer
    end Pump
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def winsize_dim_within_cap_isl (dim : UInt64) (max_dim : UInt64) : Bool :=
      decide (dim <= max_dim)
}
