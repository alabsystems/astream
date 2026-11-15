// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for hermetic shadow / counterfactual policy evaluation over
// recorded effect tapes (`Astream.Effects.TlaShadowReplay`), mounted under
// `cfg(clean_islands)` in `shadow.rs` (matching `aterm-agent` `Shadow::code` and
// `taint` propagation).
// Proves over `shadow_taint_latch` and `shadow_exit_code` that:
// 1. `taint <= 1` across every shadow row transition,
// 2. `exitCode <= 3` (`0` = identical, `1` = differs, `3` = unknown), and
// 3. `exitCode = shadow_exit_code differsCount unknownCount` is maintained across
//    every decision observation.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def shadow_nonzero_bit (val : UInt64) (code : UInt64) : UInt64 :=
      if val < 1 then 0 else code

    def shadow_code_select (primary_count : UInt64) (primary_code : UInt64) (fallback_code : UInt64) : UInt64 :=
      if primary_count < 1 then fallback_code else primary_code

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Effects.TlaShadowReplay)
    -- ========================================================================
    namespace Astream
    namespace Effects
    namespace TlaShadowReplay

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Effects.TlaShadowReplay.Satisfies M F
    prefix:75 "□" => _root_.Astream.Effects.TlaShadowReplay.Always

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
    -- 3. Shadow Evaluation State Machine & Exit-Code Bounds (100% Term-Mode)
    -- ========================================================================

    def shadow_taint_latch_isl (cur_taint : UInt64) (row_differed : UInt64) : UInt64 :=
      shadow_code_select cur_taint (1 : UInt64)
        (shadow_nonzero_bit row_differed (1 : UInt64))

    def shadow_exit_code_isl (differs_count : UInt64) (unknown_count : UInt64) : UInt64 :=
      shadow_code_select differs_count (1 : UInt64)
        (shadow_nonzero_bit unknown_count (3 : UInt64))

    theorem shadow_taint_bounded (t d : UInt64) :
        Nat.le (UInt64.toNat (shadow_taint_latch_isl t d)) 1 :=
      @Decidable.casesOn (LT.lt t (1 : UInt64))
        (fun (dt : Decidable (LT.lt t (1 : UInt64))) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt t (1 : UInt64)) dt
            (shadow_nonzero_bit d (1 : UInt64)) (1 : UInt64))) 1)
        (instDecidableUInt64Lt t (1 : UInt64))
        (fun _ => Nat.le_refl 1)
        (fun _ =>
          @Decidable.casesOn (LT.lt d (1 : UInt64))
            (fun (dd : Decidable (LT.lt d (1 : UInt64))) =>
              Nat.le (UInt64.toNat (@ite UInt64 (LT.lt d (1 : UInt64)) dd (0 : UInt64) (1 : UInt64))) 1)
            (instDecidableUInt64Lt d (1 : UInt64))
            (fun _ => Nat.le_refl 1)
            (fun _ => Nat.zero_le 1))

    theorem shadow_exit_bounded (d u : UInt64) :
        Nat.le (UInt64.toNat (shadow_exit_code_isl d u)) 3 :=
      @Decidable.casesOn (LT.lt d (1 : UInt64))
        (fun (dd : Decidable (LT.lt d (1 : UInt64))) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt d (1 : UInt64)) dd
            (shadow_nonzero_bit u (3 : UInt64)) (1 : UInt64))) 3)
        (instDecidableUInt64Lt d (1 : UInt64))
        (fun _ => @Nat.le.step 1 2 (@Nat.le.step 1 1 (Nat.le_refl 1)))
        (fun _ =>
          @Decidable.casesOn (LT.lt u (1 : UInt64))
            (fun (du : Decidable (LT.lt u (1 : UInt64))) =>
              Nat.le (UInt64.toNat (@ite UInt64 (LT.lt u (1 : UInt64)) du (0 : UInt64) (3 : UInt64))) 3)
            (instDecidableUInt64Lt u (1 : UInt64))
            (fun _ => Nat.le_refl 3)
            (fun _ => Nat.zero_le 3))

    structure ShadowState where
      differsCount : UInt64
      unknownCount : UInt64
      taint        : UInt64
      exitCode     : UInt64

    def ShadowSafetyInv (s : ShadowState) : Prop :=
      Nat.le (UInt64.toNat s.taint) 1 ∧
      Nat.le (UInt64.toNat s.exitCode) 3 ∧
      s.exitCode = shadow_exit_code_isl s.differsCount s.unknownCount

    def Init (s : ShadowState) : Prop :=
      s.differsCount = (0 : UInt64) ∧
      s.unknownCount = (0 : UInt64) ∧
      s.taint = (0 : UInt64) ∧
      s.exitCode = shadow_exit_code_isl (0 : UInt64) (0 : UInt64)

    def ObserveDecision (nextDiff nextUnk rowDiff : UInt64) (s sNext : ShadowState) : Prop :=
      sNext.differsCount = nextDiff ∧
      sNext.unknownCount = nextUnk ∧
      sNext.taint = shadow_taint_latch_isl s.taint rowDiff ∧
      sNext.exitCode = shadow_exit_code_isl nextDiff nextUnk

    def Next (s sNext : ShadowState) : Prop :=
      ∃ nd : UInt64, ∃ nu : UInt64, ∃ rd : UInt64, ObserveDecision nd nu rd s sNext

    def Spec : StateMachine ShadowState :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : ShadowState) (hInit : Init s) :
        ShadowSafetyInv s :=
      let hT0 : Nat.le (UInt64.toNat 0) 1 := Nat.zero_le 1
      let hT : Nat.le (UInt64.toNat s.taint) 1 :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) 1) hInit.2.2.1) hT0
      let hCodeBnd0 : Nat.le (UInt64.toNat (shadow_exit_code_isl 0 0)) 3 :=
        shadow_exit_bounded (0 : UInt64) (0 : UInt64)
      let hCodeBnd : Nat.le (UInt64.toNat s.exitCode) 3 :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) 3) hInit.2.2.2) hCodeBnd0
      let hEx1 : s.exitCode = shadow_exit_code_isl s.differsCount (0 : UInt64) :=
        Eq.mpr (congrArg (fun d => s.exitCode = shadow_exit_code_isl d (0 : UInt64)) hInit.1) hInit.2.2.2
      let hEx : s.exitCode = shadow_exit_code_isl s.differsCount s.unknownCount :=
        Eq.mpr (congrArg (fun u => s.exitCode = shadow_exit_code_isl s.differsCount u) hInit.2.1) hEx1
      And.intro hT (And.intro hCodeBnd hEx)

    theorem observe_preserves_inv (nd nu rd : UInt64) (s sNext : ShadowState)
        (_hInv : ShadowSafetyInv s) (hAct : ObserveDecision nd nu rd s sNext) :
        ShadowSafetyInv sNext :=
      let hBnd : Nat.le (UInt64.toNat (shadow_taint_latch_isl s.taint rd)) 1 :=
        shadow_taint_bounded s.taint rd
      let hT : Nat.le (UInt64.toNat sNext.taint) 1 :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) 1) hAct.2.2.1) hBnd
      let hCodeBnd0 : Nat.le (UInt64.toNat (shadow_exit_code_isl nd nu)) 3 :=
        shadow_exit_bounded nd nu
      let hCodeBnd : Nat.le (UInt64.toNat sNext.exitCode) 3 :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) 3) hAct.2.2.2) hCodeBnd0
      let hEx1 : sNext.exitCode = shadow_exit_code_isl sNext.differsCount nu :=
        Eq.mpr (congrArg (fun d => sNext.exitCode = shadow_exit_code_isl d nu) hAct.1) hAct.2.2.2
      let hEx : sNext.exitCode = shadow_exit_code_isl sNext.differsCount sNext.unknownCount :=
        Eq.mpr (congrArg (fun u => sNext.exitCode = shadow_exit_code_isl sNext.differsCount u) hAct.2.1) hEx1
      And.intro hT (And.intro hCodeBnd hEx)

    theorem next_preserves_inv (s sNext : ShadowState)
        (hInv : ShadowSafetyInv s) (hNext : Next s sNext) :
        ShadowSafetyInv sNext :=
      Exists.elim hNext (fun nd hEx2 =>
        Exists.elim hEx2 (fun nu hEx3 =>
          Exists.elim hEx3 (fun rd hAct => observe_preserves_inv nd nu rd s sNext hInv hAct)))

    theorem spec_satisfies_shadow_replay_safety :
        Spec ⊨ □ (Lift ShadowSafetyInv) :=
      invariantSatisfies Spec ShadowSafetyInv init_establishes_inv next_preserves_inv

    end TlaShadowReplay
    end Effects
    end Astream

    def shadow_code_in_range_isl (code : UInt64) : Bool :=
      decide (code ≤ 3)
}
