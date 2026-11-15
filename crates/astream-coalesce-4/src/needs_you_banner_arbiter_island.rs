// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `aterm` `NEEDS YOU:` menu-bar/window-border escalation parsing,
// `NEEDS YOU: nothing` clear semantics, and self-restart rejection
// (`Astream.Agent.TlaNeedsYouArbiter`), mounted under `cfg(clean_islands)` in
// `needs_you_banner_arbiter.rs`. Proves `activeItems <= maxItemsCap` and
// `bannerBytes <= maxBannerBytes`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def arbiter_needs_you_items_clamp (items : UInt64) (max_items : UInt64) : UInt64 :=
      if items < max_items then items else max_items

    def arbiter_needs_you_bytes_clamp (bytes : UInt64) (max_bytes : UInt64) : UInt64 :=
      if bytes < max_bytes then bytes else max_bytes

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Agent.TlaNeedsYouArbiter)
    -- ========================================================================
    namespace Astream
    namespace Agent
    namespace TlaNeedsYouArbiter

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Agent.TlaNeedsYouArbiter.Satisfies M F
    prefix:75 "□" => _root_.Astream.Agent.TlaNeedsYouArbiter.Always

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
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    -- ========================================================================
    -- 3. `NEEDS YOU:` Menu-Bar & Border Escalation Arbiter State Machine
    -- ========================================================================

    structure NeedsYouState where
      activeItems    : UInt64
      maxItemsCap    : UInt64
      bannerBytes    : UInt64
      maxBannerBytes : UInt64

    def NeedsYouInv (s : NeedsYouState) : Prop :=
      Nat.le (UInt64.toNat s.activeItems) (UInt64.toNat s.maxItemsCap) ∧
      Nat.le (UInt64.toNat s.bannerBytes) (UInt64.toNat s.maxBannerBytes)

    def Init (maxItemsCap maxBannerBytes : UInt64) (s : NeedsYouState) : Prop :=
      s.activeItems = (0 : UInt64) ∧
      s.maxItemsCap = maxItemsCap ∧
      s.bannerBytes = (0 : UInt64) ∧
      s.maxBannerBytes = maxBannerBytes

    def ApplyReportLine (rawItems rawBytes : UInt64) (s sNext : NeedsYouState) : Prop :=
      sNext.activeItems = _root_.arbiter_needs_you_items_clamp rawItems s.maxItemsCap ∧
      sNext.maxItemsCap = s.maxItemsCap ∧
      sNext.bannerBytes = _root_.arbiter_needs_you_bytes_clamp rawBytes s.maxBannerBytes ∧
      sNext.maxBannerBytes = s.maxBannerBytes

    def Next (s sNext : NeedsYouState) : Prop :=
      ∃ ri : UInt64, ∃ rb : UInt64, ApplyReportLine ri rb s sNext

    def Spec (maxItemsCap maxBannerBytes : UInt64) : StateMachine NeedsYouState :=
      StateMachine.mk (Init maxItemsCap maxBannerBytes) Next

    theorem items_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.arbiter_needs_you_items_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem bytes_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.arbiter_needs_you_bytes_clamp cand cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (maxItemsCap maxBannerBytes : UInt64) (s : NeedsYouState)
        (hInit : Init maxItemsCap maxBannerBytes s) : NeedsYouInv s :=
      And.intro
        (zero_u64_le s.activeItems s.maxItemsCap hInit.1)
        (zero_u64_le s.bannerBytes s.maxBannerBytes hInit.2.2.1)

    theorem applyReportLine_preserves_inv (ri rb : UInt64) (s sNext : NeedsYouState)
        (hAct : ApplyReportLine ri rb s sNext) : NeedsYouInv sNext :=
      let hI1 : Nat.le (UInt64.toNat sNext.activeItems) (UInt64.toNat s.maxItemsCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxItemsCap)) hAct.1)
          (items_clamp_le ri s.maxItemsCap)
      let hI2 : Nat.le (UInt64.toNat sNext.activeItems) (UInt64.toNat sNext.maxItemsCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.activeItems) (UInt64.toNat y)) hAct.2.1)
          hI1
      let hB1 : Nat.le (UInt64.toNat sNext.bannerBytes) (UInt64.toNat s.maxBannerBytes) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxBannerBytes)) hAct.2.2.1)
          (bytes_clamp_le rb s.maxBannerBytes)
      let hB2 : Nat.le (UInt64.toNat sNext.bannerBytes) (UInt64.toNat sNext.maxBannerBytes) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.bannerBytes) (UInt64.toNat y)) hAct.2.2.2)
          hB1
      And.intro hI2 hB2

    theorem next_preserves_inv (s sNext : NeedsYouState)
        (_hInv : NeedsYouInv s) (hNext : Next s sNext) : NeedsYouInv sNext :=
      Exists.elim hNext (fun ri hEx2 =>
        Exists.elim hEx2 (fun rb hAct => applyReportLine_preserves_inv ri rb s sNext hAct))

    theorem spec_satisfies_needs_you_arbiter_safety (maxItemsCap maxBannerBytes : UInt64) :
        (Spec maxItemsCap maxBannerBytes) ⊨ □ (Lift NeedsYouInv) :=
      invariantSatisfies (Spec maxItemsCap maxBannerBytes) NeedsYouInv
        (init_establishes_inv maxItemsCap maxBannerBytes)
        next_preserves_inv

    end TlaNeedsYouArbiter
    end Agent
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def needs_you_banner_clear_isl (active_items : UInt64) : Bool :=
      decide (active_items ≤ (0 : UInt64))
}
