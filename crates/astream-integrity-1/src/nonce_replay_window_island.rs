// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `nonce_replay_window.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `nonce_replay_window.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def replay_reject_clamp (cand_rejects : UInt64) (reject_cap : UInt64) : UInt64 :=
      if cand_rejects < reject_cap then cand_rejects else reject_cap

    def replay_hi_advance (cur_hi : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_hi < cand_seq then cand_seq else cur_hi

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Anti-Replay Window Spec
    -- =======================================================================

    namespace Astream
    namespace Aead
    namespace TlaAntiReplayWindow

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

    structure ReplayWindowState where
      reject_count : UInt64
      reject_cap : UInt64
      window_hi : UInt64
      prev_hi : UInt64

    def AntiReplayWindowInv (s : ReplayWindowState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.reject_count) (UInt64.toNat s.reject_cap))
        (Nat.le (UInt64.toNat s.prev_hi) (UInt64.toNat s.window_hi))

    def Init (reject_cap : UInt64) (s : ReplayWindowState) : Prop :=
      And
        (And (s.reject_count = 0) (s.reject_cap = reject_cap))
        (And (s.window_hi = 0) (s.prev_hi = 0))

    def windowStep (cand_rejects : UInt64) (cand_seq : UInt64) (s : ReplayWindowState) : ReplayWindowState :=
      ReplayWindowState.mk
        (_root_.replay_reject_clamp cand_rejects s.reject_cap)
        s.reject_cap
        (_root_.replay_hi_advance s.window_hi cand_seq)
        s.window_hi

    def Next (s : ReplayWindowState) (s' : ReplayWindowState) : Prop :=
      ∃ (cand_rejects : UInt64), ∃ (cand_seq : UInt64),
        s' = windowStep cand_rejects cand_seq s

    def Spec (reject_cap : UInt64) : StateMachine ReplayWindowState :=
      StateMachine.mk (Init reject_cap) Next

    theorem reject_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.replay_reject_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem hi_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.replay_hi_advance cur cand)) :=
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

    theorem init_establishes_inv (reject_cap : UInt64) (s : ReplayWindowState)
      (hInit : Init reject_cap s) :
      AntiReplayWindowInv s :=
      And.intro
        (eq_zero_le s.reject_count s.reject_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_hi s.window_hi (And.right (And.right hInit)))

    theorem next_preserves_inv (s : ReplayWindowState) (s' : ReplayWindowState)
      (_hInv : AntiReplayWindowInv s) (hNext : Next s s') :
      AntiReplayWindowInv s' :=
      Exists.elim hNext (fun (cr : UInt64) (hRest : ∃ (cs : UInt64), s' = windowStep cr cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = windowStep cr cs s) =>
          Eq.mpr
            (congrArg (fun (st : ReplayWindowState) => AntiReplayWindowInv st) hEq)
            (And.intro
              (reject_clamp_le cr s.reject_cap)
              (hi_monotone s.window_hi cs))))

    theorem anti_replay_window_safety_always (reject_cap : UInt64) :
      Satisfies (Runs (Spec reject_cap)) (Always (Lift AntiReplayWindowInv)) :=
      invariantSatisfies (Spec reject_cap) AntiReplayWindowInv (init_establishes_inv reject_cap) next_preserves_inv

    end TlaAntiReplayWindow
    end Aead
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def replay_rejects_within_cap_isl (rejects : UInt64) (reject_cap : UInt64) : Bool :=
      decide (rejects <= reject_cap)
}
