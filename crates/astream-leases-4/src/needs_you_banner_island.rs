// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `NEEDS YOU:` operator-escalation banner accounting
// (`Astream.Agent.TlaNeedsYouBanner`), mounted under `cfg(clean_islands)` in
// `needs_you_banner.rs`. Proves monotone update sequence progression (`prevSeq <= curSeq`),
// bounded active escalation item count (`activeItems <= maxItems`), and banner-clear safety
// (`bannerVisible = false -> activeItems = 0`) across `NEEDS YOU: <item>` raises and
// `NEEDS YOU: nothing` clears.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def needs_you_count_clamp (active_items : UInt64) (max_items : UInt64) : UInt64 :=
      if active_items < max_items then active_items else max_items

    def needs_you_seq_advance (cur_seq : UInt64) (next_seq : UInt64) : UInt64 :=
      if cur_seq < next_seq then next_seq else cur_seq

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Agent.TlaNeedsYouBanner)
    -- ========================================================================
    namespace Astream
    namespace Agent
    namespace TlaNeedsYouBanner

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Agent.TlaNeedsYouBanner.Satisfies M F
    prefix:75 "□" => _root_.Astream.Agent.TlaNeedsYouBanner.Always

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
    -- 3. NEEDS YOU Banner State Machine & Safety Theorem
    -- ========================================================================

    structure BannerState where
      prevSeq       : UInt64
      curSeq        : UInt64
      activeItems   : UInt64
      maxItems      : UInt64
      bannerVisible : Bool

    def NeedsYouSafetyInv (s : BannerState) : Prop :=
      Nat.le (UInt64.toNat s.prevSeq) (UInt64.toNat s.curSeq) ∧
      Nat.le (UInt64.toNat s.activeItems) (UInt64.toNat s.maxItems) ∧
      (s.bannerVisible = false → s.activeItems = (0 : UInt64))

    def Init (maxItems : UInt64) (s : BannerState) : Prop :=
      s.prevSeq = (0 : UInt64) ∧
      s.curSeq = (0 : UInt64) ∧
      s.activeItems = (0 : UInt64) ∧
      s.maxItems = maxItems ∧
      s.bannerVisible = false

    def RaiseItems (rawCount nextSeq : UInt64) (s sNext : BannerState) : Prop :=
      sNext.prevSeq = s.curSeq ∧
      sNext.curSeq = _root_.needs_you_seq_advance s.curSeq nextSeq ∧
      sNext.activeItems = _root_.needs_you_count_clamp rawCount s.maxItems ∧
      sNext.maxItems = s.maxItems ∧
      sNext.bannerVisible = true

    def ClearNothing (nextSeq : UInt64) (s sNext : BannerState) : Prop :=
      sNext.prevSeq = s.curSeq ∧
      sNext.curSeq = _root_.needs_you_seq_advance s.curSeq nextSeq ∧
      sNext.activeItems = (0 : UInt64) ∧
      sNext.maxItems = s.maxItems ∧
      sNext.bannerVisible = false

    def Next (s sNext : BannerState) : Prop :=
      (∃ rc : UInt64, ∃ ns : UInt64, RaiseItems rc ns s sNext) ∨
      (∃ ns : UInt64, ClearNothing ns s sNext)

    def Spec (maxItems : UInt64) : StateMachine BannerState :=
      StateMachine.mk (Init maxItems) Next

    theorem true_ne_false (h : true = false) : False :=
      Bool.noConfusion h

    theorem clamp_le_cap : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.needs_you_count_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.needs_you_seq_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_u64_le (x y : UInt64) (hEq : x = y) :
        Nat.le (UInt64.toNat x) (UInt64.toNat y) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat y)) hEq)
        (@Nat.le.refl (UInt64.toNat y))

    theorem init_establishes_inv (maxItems : UInt64) (s : BannerState)
        (hInit : Init maxItems s) : NeedsYouSafetyInv s :=
      And.intro
        (eq_u64_le s.prevSeq s.curSeq (Eq.trans hInit.1 (Eq.symm hInit.2.1)))
        (And.intro
          (zero_u64_le s.activeItems s.maxItems hInit.2.2.1)
          (fun _ => hInit.2.2.1))

    theorem raise_preserves_inv (rc ns : UInt64) (s sNext : BannerState)
        (hAct : RaiseItems rc ns s sNext) : NeedsYouSafetyInv sNext :=
      let hS1 : Nat.le (UInt64.toNat s.curSeq) (UInt64.toNat sNext.curSeq) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat s.curSeq) (UInt64.toNat y)) hAct.2.1)
          (advance_ge_cur s.curSeq ns)
      let hS2 : Nat.le (UInt64.toNat sNext.prevSeq) (UInt64.toNat sNext.curSeq) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.curSeq)) hAct.1)
          hS1
      let hC1 : Nat.le (UInt64.toNat sNext.activeItems) (UInt64.toNat s.maxItems) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxItems)) hAct.2.2.1)
          (clamp_le_cap rc s.maxItems)
      let hC2 : Nat.le (UInt64.toNat sNext.activeItems) (UInt64.toNat sNext.maxItems) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.activeItems) (UInt64.toNat y)) hAct.2.2.2.1)
          hC1
      And.intro hS2
        (And.intro hC2
          (fun hFalse =>
            False.elim (true_ne_false (Eq.trans (Eq.symm hAct.2.2.2.2) hFalse))))

    theorem clear_preserves_inv (ns : UInt64) (s sNext : BannerState)
        (hAct : ClearNothing ns s sNext) : NeedsYouSafetyInv sNext :=
      let hS1 : Nat.le (UInt64.toNat s.curSeq) (UInt64.toNat sNext.curSeq) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat s.curSeq) (UInt64.toNat y)) hAct.2.1)
          (advance_ge_cur s.curSeq ns)
      let hS2 : Nat.le (UInt64.toNat sNext.prevSeq) (UInt64.toNat sNext.curSeq) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.curSeq)) hAct.1)
          hS1
      let hC : Nat.le (UInt64.toNat sNext.activeItems) (UInt64.toNat sNext.maxItems) :=
        zero_u64_le sNext.activeItems sNext.maxItems hAct.2.2.1
      And.intro hS2 (And.intro hC (fun _ => hAct.2.2.1))

    theorem next_preserves_inv (s sNext : BannerState)
        (_hInv : NeedsYouSafetyInv s) (hNext : Next s sNext) :
        NeedsYouSafetyInv sNext :=
      Or.elim hNext
        (fun hEx1 =>
          Exists.elim hEx1 (fun rc hEx2 =>
            Exists.elim hEx2 (fun ns hR => raise_preserves_inv rc ns s sNext hR)))
        (fun hExC =>
          Exists.elim hExC (fun ns hC => clear_preserves_inv ns s sNext hC))

    theorem spec_satisfies_needs_you_banner_safety (maxItems : UInt64) :
        (Spec maxItems) ⊨ □ (Lift NeedsYouSafetyInv) :=
      invariantSatisfies (Spec maxItems) NeedsYouSafetyInv
        (init_establishes_inv maxItems)
        next_preserves_inv

    end TlaNeedsYouBanner
    end Agent
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def needs_you_is_cleared_isl (active_items : UInt64) : Bool :=
      decide (active_items = 0)
}
