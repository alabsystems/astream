// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `effect_replay_cursor.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `effect_replay_cursor.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def replay_cursor_clamp (cand_cursor : UInt64) (tape_len : UInt64) : UInt64 :=
      if cand_cursor < tape_len then cand_cursor else tape_len

    def replay_cursor_advance (cur_cursor : UInt64) (cand_cursor : UInt64) : UInt64 :=
      if cur_cursor < cand_cursor then cand_cursor else cur_cursor

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Effect Replay Cursor Spec
    -- =======================================================================

    namespace Astream
    namespace Effects
    namespace TlaEffectReplayCursor

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

    structure ReplayCursorState where
      cursor : UInt64
      tape_len : UInt64
      prev_cursor : UInt64

    def ReplayCursorInv (s : ReplayCursorState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.cursor) (UInt64.toNat s.tape_len))
        (Nat.le (UInt64.toNat s.prev_cursor) (UInt64.toNat s.cursor))

    def Init (tape_len : UInt64) (s : ReplayCursorState) : Prop :=
      And
        (And (s.cursor = 0) (s.tape_len = tape_len))
        (s.prev_cursor = 0)

    def cursorStep (cand_cursor : UInt64) (s : ReplayCursorState) : ReplayCursorState :=
      ReplayCursorState.mk
        (_root_.replay_cursor_clamp
          (_root_.replay_cursor_advance s.cursor cand_cursor)
          s.tape_len)
        s.tape_len
        s.cursor

    def Next (s : ReplayCursorState) (s' : ReplayCursorState) : Prop :=
      ∃ (cand_cursor : UInt64),
        s' = cursorStep cand_cursor s

    def Spec (tape_len : UInt64) : StateMachine ReplayCursorState :=
      StateMachine.mk (Init tape_len) Next

    theorem clamp_le_len : forall (cand : UInt64) (len : UInt64),
        Nat.le (UInt64.toNat (_root_.replay_cursor_clamp cand len)) (UInt64.toNat len) :=
      fun cand len => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand len)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => len) (fun _ => cand))) (UInt64.toNat len))
        (instDecidableUInt64Lt cand len)
        (fun _ => @Nat.le.refl (UInt64.toNat len))
        (fun hLt => Nat.le_of_lt hLt)

    theorem advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.replay_cursor_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clamp_advance_ge_cur (cur : UInt64) (cand : UInt64) (len : UInt64)
      (hCurLe : Nat.le (UInt64.toNat cur) (UInt64.toNat len)) :
      Nat.le
        (UInt64.toNat cur)
        (UInt64.toNat (_root_.replay_cursor_clamp (_root_.replay_cursor_advance cur cand) len)) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt (_root_.replay_cursor_advance cur cand) len)) =>
          Nat.le
            (UInt64.toNat cur)
            (UInt64.toNat (Decidable.casesOn
              (motive := fun _ => UInt64)
              d
              (fun _ => len)
              (fun _ => _root_.replay_cursor_advance cur cand))))
        (instDecidableUInt64Lt (_root_.replay_cursor_advance cur cand) len)
        (fun _ => hCurLe)
        (fun _ => advance_ge_cur cur cand)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (tape_len : UInt64) (s : ReplayCursorState)
      (hInit : Init tape_len s) :
      ReplayCursorInv s :=
      And.intro
        (eq_zero_le s.cursor s.tape_len (And.left (And.left hInit)))
        (eq_zero_le s.prev_cursor s.cursor (And.right hInit))

    theorem next_preserves_inv (s : ReplayCursorState) (s' : ReplayCursorState)
      (hInv : ReplayCursorInv s) (hNext : Next s s') :
      ReplayCursorInv s' :=
      Exists.elim hNext (fun (cc : UInt64) (hEq : s' = cursorStep cc s) =>
        Eq.mpr
          (congrArg (fun (st : ReplayCursorState) => ReplayCursorInv st) hEq)
          (And.intro
            (clamp_le_len (_root_.replay_cursor_advance s.cursor cc) s.tape_len)
            (clamp_advance_ge_cur s.cursor cc s.tape_len (And.left hInv))))

    theorem replay_cursor_safety_always (tape_len : UInt64) :
      Satisfies (Runs (Spec tape_len)) (Always (Lift ReplayCursorInv)) :=
      invariantSatisfies (Spec tape_len) ReplayCursorInv (init_establishes_inv tape_len) next_preserves_inv

    end TlaEffectReplayCursor
    end Effects
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def replay_cursor_within_tape_isl (cursor : UInt64) (tape_len : UInt64) : Bool :=
      decide (cursor <= tape_len)
}
