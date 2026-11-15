// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `<log>.health` sidecar staleness and parked-tail invariant
// verification (`Astream.Broker.TlaHealthSidecarFreshness`), mounted under
// `cfg(clean_islands)` in `health_sidecar_freshener.rs`. Proves
// `parkedTails <= attachedConns` and `sampleAgeMs <= maxStaleMs`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def health_parked_clamp (parked_tails : UInt64) (attached_conns : UInt64) : UInt64 :=
      if parked_tails < attached_conns then parked_tails else attached_conns

    def health_age_clamp (age_ms : UInt64) (max_stale_ms : UInt64) : UInt64 :=
      if age_ms < max_stale_ms then age_ms else max_stale_ms

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Broker.TlaHealthSidecarFreshness)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaHealthSidecarFreshness

    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop
    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)
    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      Nat.rec
        (motive := fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun hNext => hStep (b k) (b (Nat.succ k)) ih hNext)
            (fun hStutter => Eq.mpr (congrArg I hStutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        Satisfies M (Always (Lift I)) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaHealthSidecarFreshness.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaHealthSidecarFreshness.Always

    -- ========================================================================
    -- 3. `<log>.health` Sidecar Freshness & Connection Gauge State Machine
    -- ========================================================================

    structure HealthSidecarState where
      parkedTails   : UInt64
      attachedConns : UInt64
      sampleAgeMs   : UInt64
      maxStaleMs    : UInt64

    def HealthSidecarInv (s : HealthSidecarState) : Prop :=
      Nat.le (UInt64.toNat s.parkedTails) (UInt64.toNat s.attachedConns) ∧
      Nat.le (UInt64.toNat s.sampleAgeMs) (UInt64.toNat s.maxStaleMs)

    def Init (maxStaleMs : UInt64) (s : HealthSidecarState) : Prop :=
      s.parkedTails = (0 : UInt64) ∧
      s.attachedConns = (0 : UInt64) ∧
      s.sampleAgeMs = (0 : UInt64) ∧
      s.maxStaleMs = maxStaleMs

    def SampleHealth (rawParked nextAttached rawAge : UInt64)
        (s sNext : HealthSidecarState) : Prop :=
      sNext.parkedTails = _root_.health_parked_clamp rawParked nextAttached ∧
      sNext.attachedConns = nextAttached ∧
      sNext.sampleAgeMs = _root_.health_age_clamp rawAge s.maxStaleMs ∧
      sNext.maxStaleMs = s.maxStaleMs

    def Next (s sNext : HealthSidecarState) : Prop :=
      ∃ rp : UInt64, ∃ na : UInt64, ∃ ra : UInt64, SampleHealth rp na ra s sNext

    def Spec (maxStaleMs : UInt64) : StateMachine HealthSidecarState :=
      StateMachine.mk (Init maxStaleMs) Next

    theorem parked_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.health_parked_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem age_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.health_age_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxStaleMs : UInt64) (s : HealthSidecarState)
        (hInit : Init maxStaleMs s) : HealthSidecarInv s :=
      And.intro
        (zero_u64_le s.parkedTails s.attachedConns hInit.1)
        (zero_u64_le s.sampleAgeMs s.maxStaleMs hInit.2.2.1)

    theorem sampleHealth_preserves_inv (rp na ra : UInt64) (s sNext : HealthSidecarState)
        (hAct : SampleHealth rp na ra s sNext) : HealthSidecarInv sNext :=
      let hP1 : Nat.le (UInt64.toNat sNext.parkedTails) (UInt64.toNat na) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat na)) hAct.1)
          (parked_clamp_le rp na)
      let hP2 : Nat.le (UInt64.toNat sNext.parkedTails) (UInt64.toNat sNext.attachedConns) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.parkedTails) (UInt64.toNat y)) hAct.2.1)
          hP1
      let hA1 : Nat.le (UInt64.toNat sNext.sampleAgeMs) (UInt64.toNat s.maxStaleMs) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxStaleMs)) hAct.2.2.1)
          (age_clamp_le ra s.maxStaleMs)
      let hA2 : Nat.le (UInt64.toNat sNext.sampleAgeMs) (UInt64.toNat sNext.maxStaleMs) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.sampleAgeMs) (UInt64.toNat y)) hAct.2.2.2)
          hA1
      And.intro hP2 hA2

    theorem next_preserves_inv (s sNext : HealthSidecarState)
        (_hInv : HealthSidecarInv s) (hNext : Next s sNext) : HealthSidecarInv sNext :=
      Exists.elim hNext (fun rp hEx2 =>
        Exists.elim hEx2 (fun na hEx3 =>
          Exists.elim hEx3 (fun ra hAct => sampleHealth_preserves_inv rp na ra s sNext hAct)))

    theorem spec_satisfies_health_sidecar_freshness_safety (maxStaleMs : UInt64) :
        (Spec maxStaleMs) ⊨ □ (Lift HealthSidecarInv) :=
      invariantSatisfies (Spec maxStaleMs) HealthSidecarInv
        (init_establishes_inv maxStaleMs)
        next_preserves_inv

    end TlaHealthSidecarFreshness
    end Broker
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def health_snapshot_fresh_isl (age_ms : UInt64) (fresh_horizon_ms : UInt64) : Bool :=
      decide (age_ms ≤ fresh_horizon_ms)
}
