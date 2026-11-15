// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `privacy_gate.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `privacy_gate.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def privacy_blocked_advance (prev_blocked : UInt64) (cand_blocked : UInt64) : UInt64 :=
      if prev_blocked < cand_blocked then cand_blocked else prev_blocked

    def privacy_path_depth_clamp (depth : UInt64) (max_depth : UInt64) : UInt64 :=
      if depth < max_depth then depth else max_depth

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & macOS TCC Privacy Gate
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaMacPrivacyGate

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

    structure PrivacyGateState where
      blocked_count : UInt64
      prev_blocked : UInt64
      scanned_depth : UInt64
      max_depth : UInt64

    def PrivacyGateInv (s : PrivacyGateState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_blocked) (UInt64.toNat s.blocked_count))
        (Nat.le (UInt64.toNat s.scanned_depth) (UInt64.toNat s.max_depth))

    def Init (s : PrivacyGateState) : Prop :=
      And
        (s.scanned_depth = 0)
        (And (s.blocked_count = 0) (s.prev_blocked = 0))

    def checkPathStep (cand_blocked : UInt64) (raw_depth : UInt64) (s : PrivacyGateState) : PrivacyGateState :=
      PrivacyGateState.mk
        (_root_.privacy_blocked_advance s.blocked_count cand_blocked)
        s.blocked_count
        (_root_.privacy_path_depth_clamp raw_depth s.max_depth)
        s.max_depth

    def Next (s : PrivacyGateState) (s' : PrivacyGateState) : Prop :=
      ∃ (cand_blocked : UInt64), ∃ (raw_depth : UInt64),
        s' = checkPathStep cand_blocked raw_depth s

    def Spec : StateMachine PrivacyGateState :=
      StateMachine.mk Init Next

    theorem blocked_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.privacy_blocked_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem depth_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.privacy_path_depth_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
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

    theorem init_establishes_inv (s : PrivacyGateState) (hInit : Init s) :
      PrivacyGateInv s :=
      And.intro
        (eq_zero_le
          s.prev_blocked
          s.blocked_count
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.scanned_depth s.max_depth (And.left hInit))

    theorem next_preserves_inv (s : PrivacyGateState) (s' : PrivacyGateState)
      (_hInv : PrivacyGateInv s) (hNext : Next s s') :
      PrivacyGateInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (rd : UInt64), s' = checkPathStep cb rd s) =>
        Exists.elim hRest (fun (rd : UInt64) (hEq : s' = checkPathStep cb rd s) =>
          Eq.mpr
            (congrArg (fun (st : PrivacyGateState) => PrivacyGateInv st) hEq)
            (And.intro
              (blocked_monotone s.blocked_count cb)
              (depth_le_max rd s.max_depth))))

    theorem privacy_gate_safety_always :
      Satisfies (Runs Spec) (Always (Lift PrivacyGateInv)) :=
      invariantSatisfies Spec PrivacyGateInv init_establishes_inv next_preserves_inv

    end TlaMacPrivacyGate
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def privacy_fda_granted_flag_isl (fda_flag : UInt64) : Bool :=
      decide ((0 : UInt64) < fda_flag)
}
