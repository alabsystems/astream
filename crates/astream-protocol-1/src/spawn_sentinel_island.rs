// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `spawn_sentinel.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `spawn_sentinel.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def spawn_hang_streak_clamp (streak : UInt64) (threshold : UInt64) : UInt64 :=
      if streak < threshold then streak else threshold

    def spawn_incident_advance (prev_incidents : UInt64) (cand_incidents : UInt64) : UInt64 :=
      if prev_incidents < cand_incidents then cand_incidents else prev_incidents

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & syspolicyd Sentinel Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaSpawnHealthSentinel

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

    structure SpawnSentinelState where
      hang_streak : UInt64
      stuck_threshold : UInt64
      incidents : UInt64
      prev_incidents : UInt64

    def SpawnSentinelInv (s : SpawnSentinelState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.hang_streak) (UInt64.toNat s.stuck_threshold))
        (Nat.le (UInt64.toNat s.prev_incidents) (UInt64.toNat s.incidents))

    def Init (s : SpawnSentinelState) : Prop :=
      And
        (s.hang_streak = 0)
        (And (s.incidents = 0) (s.prev_incidents = 0))

    def sentinelStep (raw_streak : UInt64) (cand_inc : UInt64) (s : SpawnSentinelState) : SpawnSentinelState :=
      SpawnSentinelState.mk
        (_root_.spawn_hang_streak_clamp raw_streak s.stuck_threshold)
        s.stuck_threshold
        (_root_.spawn_incident_advance s.incidents cand_inc)
        s.incidents

    def Next (s : SpawnSentinelState) (s' : SpawnSentinelState) : Prop :=
      ∃ (raw_streak : UInt64), ∃ (cand_inc : UInt64),
        s' = sentinelStep raw_streak cand_inc s

    def Spec : StateMachine SpawnSentinelState :=
      StateMachine.mk Init Next

    theorem streak_le_threshold : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.spawn_hang_streak_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem incidents_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.spawn_incident_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
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

    theorem init_establishes_inv (s : SpawnSentinelState) (hInit : Init s) :
      SpawnSentinelInv s :=
      And.intro
        (zero_le_cap s.hang_streak s.stuck_threshold (And.left hInit))
        (eq_zero_le
          s.prev_incidents
          s.incidents
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : SpawnSentinelState) (s' : SpawnSentinelState)
      (_hInv : SpawnSentinelInv s) (hNext : Next s s') :
      SpawnSentinelInv s' :=
      Exists.elim hNext (fun (rs : UInt64) (hRest : ∃ (ci : UInt64), s' = sentinelStep rs ci s) =>
        Exists.elim hRest (fun (ci : UInt64) (hEq : s' = sentinelStep rs ci s) =>
          Eq.mpr
            (congrArg (fun (st : SpawnSentinelState) => SpawnSentinelInv st) hEq)
            (And.intro
              (streak_le_threshold rs s.stuck_threshold)
              (incidents_monotone s.incidents ci))))

    theorem spawn_sentinel_safety_always :
      Satisfies (Runs Spec) (Always (Lift SpawnSentinelInv)) :=
      invariantSatisfies Spec SpawnSentinelInv init_establishes_inv next_preserves_inv

    end TlaSpawnHealthSentinel
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def syspolicyd_is_stuck_isl (hang_streak : UInt64) (threshold : UInt64) (apple_probe_ok : Bool) : Bool :=
      and apple_probe_ok (decide (threshold ≤ hang_streak))
}
