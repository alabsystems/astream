// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `aterm` `Autopilot=Land` termination and person-reply parking
// (`Astream.Agent.TlaAutopilotLandVerifier`, Island #275), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def land_dirty_bits_clamp (bits : UInt64) (cap : UInt64) : UInt64 :=
      if bits < cap then bits else cap

    def land_reply_elapsed_clamp (elapsed_ms : UInt64) (window_ms : UInt64) : UInt64 :=
      if elapsed_ms < window_ms then elapsed_ms else window_ms

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Land Verifier Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaAutopilotLandVerifier

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

    structure LandState where
      dirty_mask : UInt64
      mask_cap : UInt64
      elapsed_ms : UInt64
      window_ms : UInt64

    def LandSafetyInv (s : LandState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.dirty_mask) (UInt64.toNat s.mask_cap))
        (Nat.le (UInt64.toNat s.elapsed_ms) (UInt64.toNat s.window_ms))

    def Init (s : LandState) : Prop :=
      LandSafetyInv s

    def observeStep (raw_bits : UInt64) (raw_elapsed : UInt64) (s : LandState) : LandState :=
      LandState.mk
        (_root_.land_dirty_bits_clamp raw_bits s.mask_cap)
        s.mask_cap
        (_root_.land_reply_elapsed_clamp raw_elapsed s.window_ms)
        s.window_ms

    def Next (s : LandState) (s' : LandState) : Prop :=
      ∃ (raw_bits : UInt64), ∃ (raw_elapsed : UInt64),
        s' = observeStep raw_bits raw_elapsed s

    def Spec : StateMachine LandState :=
      StateMachine.mk Init Next

    theorem clamp_bits_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.land_dirty_bits_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clamp_elapsed_le_window : forall (raw : UInt64) (win : UInt64),
        Nat.le (UInt64.toNat (_root_.land_reply_elapsed_clamp raw win)) (UInt64.toNat win) :=
      fun raw win => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw win)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => win) (fun _ => raw))) (UInt64.toNat win))
        (instDecidableUInt64Lt raw win)
        (fun _ => @Nat.le.refl (UInt64.toNat win))
        (fun hLt => Nat.le_of_lt hLt)

    theorem init_establishes_inv (s : LandState) (hInit : Init s) :
      LandSafetyInv s := hInit

    theorem next_preserves_inv (s : LandState) (s' : LandState)
      (_hInv : LandSafetyInv s) (hNext : Next s s') :
      LandSafetyInv s' :=
      Exists.elim hNext (fun (rb : UInt64) (hRest : ∃ (re : UInt64), s' = observeStep rb re s) =>
        Exists.elim hRest (fun (re : UInt64) (hEq : s' = observeStep rb re s) =>
          Eq.mpr
            (congrArg (fun (st : LandState) => LandSafetyInv st) hEq)
            (And.intro
              (clamp_bits_le_cap rb s.mask_cap)
              (clamp_elapsed_le_window re s.window_ms))))

    theorem land_safety_always :
      Satisfies (Runs Spec) (Always (Lift LandSafetyInv)) :=
      invariantSatisfies Spec LandSafetyInv init_establishes_inv next_preserves_inv

    end TlaAutopilotLandVerifier
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def land_git_all_clean_isl (dirty_mask : UInt64) : Bool :=
      decide (dirty_mask = (0 : UInt64))

    def land_person_window_open_isl (elapsed_ms : UInt64) (window_ms : UInt64) : Bool :=
      decide (elapsed_ms ≤ window_ms)
}
