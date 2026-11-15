// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `sync.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `sync.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn sync_clamp_parent_count`) and verified by
    --    `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Clamp a candidate count (`len`) to an upper bound (`cap`), i.e. `min(len, cap)`.
    -- Compiled directly to `pub const fn sync_clamp_parent_count(len: u64, cap: u64) -> u64`.
    def sync_clamp_parent_count (len : UInt64) (cap : UInt64) : UInt64 :=
      if len < cap then len else cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaAppSync)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaAppSync

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

    prefix:100 "□" => _root_.Astream.Wire.TlaAppSync.Always
    infixl:45 " ⊨ " => _root_.Astream.Wire.TlaAppSync.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      @Nat.rec (fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun step => hStep (b k) (b (Nat.succ k)) ih step)
            (fun stutter => Eq.mpr (congrArg I stutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Bounded Causal Index & Equivocation
    --    Quarantine Projection (`Index::insert`, `forks`, `project_excluding`)
    -- ========================================================================

    theorem sync_clamp_le_cap : forall (len : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sync_clamp_parent_count len cap)) (UInt64.toNat cap) :=
      fun len cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => len))) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun h => Nat.le_of_lt h)

    -- State of a bounded causal sync index and its set-recomputed projection:
    --   retained       : retained verified headers in `Index` (`<= cap`)
    --   projected      : causal-ready headers emitted in `Projection.ordered` (`<= retained`)
    --   quarantined    : `0` = honest actor, `1` = actor equivocated in `forks()`
    --   actorProjected : headers of that actor emitted in `Projection.ordered`
    structure SyncState where
      retained       : UInt64
      projected      : UInt64
      quarantined    : Nat
      actorProjected : UInt64

    -- TLA+ Safety Invariant:
    -- 1. `retained <= cap`: bounded index never exceeds configured capacity.
    -- 2. `projected <= retained`: projection never emits more records than retained.
    -- 3. `quarantined = 1 -> actorProjected = 0`: once an actor equivocates,
    --    set-recomputation withdraws all of its records from `ordered` regardless
    --    of arrival order.
    def AppSyncSafetyInv (cap : UInt64) (s : SyncState) : Prop :=
      Nat.le (UInt64.toNat s.retained) (UInt64.toNat cap) ∧
      (Nat.le (UInt64.toNat s.projected) (UInt64.toNat s.retained) ∧
        (s.quarantined = 1 → s.actorProjected = 0))

    def Init (s : SyncState) : Prop :=
      s.retained = 0 ∧
      s.projected = 0 ∧
      s.quarantined = 0 ∧
      s.actorProjected = 0

    -- Action 1: InsertHeader — retain a shaped, non-colliding header within `cap`
    -- and recompute the projection within the new retained count (`quarantined` preserved).
    def InsertHeader (cap : UInt64) (cand_ret : UInt64) (cand_proj : UInt64) (s sNext : SyncState) : Prop :=
      sNext.retained = _root_.sync_clamp_parent_count cand_ret cap ∧
      sNext.projected = _root_.sync_clamp_parent_count cand_proj (_root_.sync_clamp_parent_count cand_ret cap) ∧
      sNext.quarantined = s.quarantined ∧
      sNext.actorProjected = s.actorProjected

    -- Action 2: ProjectHonestActor — project causal-ready records while `quarantined = 0`.
    def ProjectHonestActor (cand_proj : UInt64) (cand_actor_proj : UInt64) (s sNext : SyncState) : Prop :=
      s.quarantined = 0 ∧
      sNext.retained = s.retained ∧
      sNext.projected = _root_.sync_clamp_parent_count cand_proj s.retained ∧
      sNext.quarantined = 0 ∧
      sNext.actorProjected = _root_.sync_clamp_parent_count cand_actor_proj s.retained

    -- Action 3: QuarantineEquivocator — `forks()` witnesses conflicting dense-sequence
    -- claims for the actor; `project_excluding` quarantines the actor (`quarantined = 1`)
    -- and withdraws every record of that actor (`actorProjected = 0`).
    def QuarantineEquivocator (honest_proj : UInt64) (s sNext : SyncState) : Prop :=
      sNext.retained = s.retained ∧
      sNext.projected = _root_.sync_clamp_parent_count honest_proj s.retained ∧
      sNext.quarantined = 1 ∧
      sNext.actorProjected = 0

    def Next (cap : UInt64) (s sNext : SyncState) : Prop :=
      (∃ cand_ret : UInt64, ∃ cand_proj : UInt64, InsertHeader cap cand_ret cand_proj s sNext) ∨
        ((∃ cand_proj : UInt64, ∃ cand_actor : UInt64, ProjectHonestActor cand_proj cand_actor s sNext) ∨
          (∃ honest_proj : UInt64, QuarantineEquivocator honest_proj s sNext))

    def Spec (cap : UInt64) : StateMachine SyncState :=
      StateMachine.mk Init (Next cap)

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem uint64_zero_le (a b : UInt64) (hZero : a = 0) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (cap : UInt64) (s : SyncState) (hInit : Init s) :
        AppSyncSafetyInv cap s :=
      And.intro
        (uint64_zero_le s.retained cap hInit.1)
        (And.intro
          (uint64_zero_le s.projected s.retained hInit.2.1)
          (fun hQ1 =>
            let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2.1) hQ1
            False.elim (zero_ne_one h01)))

    theorem insert_preserves_inv (cap : UInt64) (cand_ret : UInt64) (cand_proj : UInt64)
        (s sNext : SyncState) (hInv : AppSyncSafetyInv cap s)
        (hAct : InsertHeader cap cand_ret cand_proj s sNext) : AppSyncSafetyInv cap sNext :=
      let hRetEq : sNext.retained = _root_.sync_clamp_parent_count cand_ret cap := hAct.1
      let hProjEq : sNext.projected = _root_.sync_clamp_parent_count cand_proj (_root_.sync_clamp_parent_count cand_ret cap) := hAct.2.1
      let hQuarEq : sNext.quarantined = s.quarantined := hAct.2.2.1
      let hActProjEq : sNext.actorProjected = s.actorProjected := hAct.2.2.2
      let hRetCap : Nat.le (UInt64.toNat sNext.retained) (UInt64.toNat cap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hRetEq)
          (sync_clamp_le_cap cand_ret cap)
      let hProjNewRet : Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat (_root_.sync_clamp_parent_count cand_ret cap)) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (_root_.sync_clamp_parent_count cand_ret cap))) hProjEq)
          (sync_clamp_le_cap cand_proj (_root_.sync_clamp_parent_count cand_ret cap))
      let hProjRet : Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat sNext.retained) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat y)) hRetEq)
          hProjNewRet
      And.intro
        hRetCap
        (And.intro
          hProjRet
          (fun hQ1 =>
            let hOldQ1 : s.quarantined = 1 := Eq.trans (Eq.symm hQuarEq) hQ1
            let hOldZero : s.actorProjected = 0 := hInv.2.2 hOldQ1
            Eq.trans hActProjEq hOldZero))

    theorem projectHonest_preserves_inv (cap : UInt64) (cand_proj : UInt64) (cand_actor : UInt64)
        (s sNext : SyncState) (hInv : AppSyncSafetyInv cap s)
        (hAct : ProjectHonestActor cand_proj cand_actor s sNext) : AppSyncSafetyInv cap sNext :=
      let hRetEq : sNext.retained = s.retained := hAct.2.1
      let hProjEq : sNext.projected = _root_.sync_clamp_parent_count cand_proj s.retained := hAct.2.2.1
      let hQuarZ : sNext.quarantined = 0 := hAct.2.2.2.1
      let hRetCap : Nat.le (UInt64.toNat sNext.retained) (UInt64.toNat cap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hRetEq) hInv.1
      let hProjOldRet : Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat s.retained) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.retained)) hProjEq)
          (sync_clamp_le_cap cand_proj s.retained)
      let hProjRet : Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat sNext.retained) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat y)) hRetEq)
          hProjOldRet
      And.intro
        hRetCap
        (And.intro
          hProjRet
          (fun hQ1 =>
            let h01 : 0 = 1 := Eq.trans (Eq.symm hQuarZ) hQ1
            False.elim (zero_ne_one h01)))

    theorem quarantine_preserves_inv (cap : UInt64) (honest_proj : UInt64)
        (s sNext : SyncState) (hInv : AppSyncSafetyInv cap s)
        (hAct : QuarantineEquivocator honest_proj s sNext) : AppSyncSafetyInv cap sNext :=
      let hRetEq : sNext.retained = s.retained := hAct.1
      let hProjEq : sNext.projected = _root_.sync_clamp_parent_count honest_proj s.retained := hAct.2.1
      let hActZ : sNext.actorProjected = 0 := hAct.2.2.2
      let hRetCap : Nat.le (UInt64.toNat sNext.retained) (UInt64.toNat cap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hRetEq) hInv.1
      let hProjOldRet : Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat s.retained) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.retained)) hProjEq)
          (sync_clamp_le_cap honest_proj s.retained)
      let hProjRet : Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat sNext.retained) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.projected) (UInt64.toNat y)) hRetEq)
          hProjOldRet
      And.intro
        hRetCap
        (And.intro
          hProjRet
          (fun _ => hActZ))

    theorem next_preserves_inv (cap : UInt64) (s sNext : SyncState)
        (hInv : AppSyncSafetyInv cap s) (hNext : Next cap s sNext) :
        AppSyncSafetyInv cap sNext :=
      Or.elim hNext
        (fun hIns =>
          Exists.elim hIns (fun cand_ret hIns2 =>
            Exists.elim hIns2 (fun cand_proj hAct =>
              insert_preserves_inv cap cand_ret cand_proj s sNext hInv hAct)))
        (fun hRest =>
          Or.elim hRest
            (fun hHon =>
              Exists.elim hHon (fun cand_proj hHon2 =>
                Exists.elim hHon2 (fun cand_actor hAct =>
                  projectHonest_preserves_inv cap cand_proj cand_actor s sNext hInv hAct)))
            (fun hQuar =>
              Exists.elim hQuar (fun honest_proj hAct =>
                quarantine_preserves_inv cap honest_proj s sNext hInv hAct)))

    theorem spec_satisfies_app_sync_safety (cap : UInt64) :
        (Spec cap) ⊨ □ (Lift (AppSyncSafetyInv cap)) :=
      invariantSatisfies (Spec cap) (AppSyncSafetyInv cap)
        (init_establishes_inv cap)
        (next_preserves_inv cap)

    end TlaAppSync
    end Wire
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def sync_within_capacity_isl (retained : UInt64) (capacity : UInt64) : Bool :=
      decide (retained < capacity)

    def clamp_le_unfulfilled_isl (v : UInt64) (hi : UInt64) : UInt64 :=
      if hi < v then hi else v

    def sync_sequence_follows_prop (previous : UInt64) (next : UInt64) : Prop :=
      previous < 18446744073709551615 ∧ UInt64.toNat next = Nat.succ (UInt64.toNat previous)

    def sync_discharge_isl (unfulfilled : Nat) : Nat :=
      Nat.pred unfulfilled
}
