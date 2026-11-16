// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for offline bearer-attenuated Macaroon capability chains
// (`Astream.Cap.TlaMacaroonAttenuation`), mounted under `cfg(clean_islands)` in
// `macaroon_depth_attenuator.rs`. Proves `chainDepth <= maxDepth` (`<= 8`) and monotone
// deadline narrowing (`childExpiryMs <= parentExpiryMs`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def macaroon_depth_clamp (depth : UInt64) (max_depth : UInt64) : UInt64 :=
      if depth < max_depth then depth else max_depth

    def macaroon_expiry_narrow (child_exp : UInt64) (parent_exp : UInt64) : UInt64 :=
      if child_exp < parent_exp then child_exp else parent_exp

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel
    -- ========================================================================
    namespace Astream
    namespace Cap
    namespace TlaMacaroonAttenuation

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Cap.TlaMacaroonAttenuation.Satisfies M F
    prefix:75 "□" => _root_.Astream.Cap.TlaMacaroonAttenuation.Always

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
    -- 3. Offline Macaroon Delegation Narrowing State Machine
    -- ========================================================================

    structure MacaroonState where
      chainDepth     : UInt64
      maxDepth       : UInt64
      childExpiryMs  : UInt64
      parentExpiryMs : UInt64

    def MacaroonNarrowingInv (s : MacaroonState) : Prop :=
      Nat.le (UInt64.toNat s.chainDepth) (UInt64.toNat s.maxDepth) ∧
      Nat.le (UInt64.toNat s.childExpiryMs) (UInt64.toNat s.parentExpiryMs)

    def Init (maxDepth rootExpiry : UInt64) (s : MacaroonState) : Prop :=
      s.chainDepth = (0 : UInt64) ∧
      s.maxDepth = maxDepth ∧
      s.childExpiryMs = rootExpiry ∧
      s.parentExpiryMs = rootExpiry

    def AttenuateLink (rawDepth reqChildExp : UInt64) (s sNext : MacaroonState) : Prop :=
      sNext.chainDepth = _root_.macaroon_depth_clamp rawDepth s.maxDepth ∧
      sNext.maxDepth = s.maxDepth ∧
      sNext.childExpiryMs = _root_.macaroon_expiry_narrow reqChildExp s.childExpiryMs ∧
      sNext.parentExpiryMs = s.childExpiryMs

    def Next (s sNext : MacaroonState) : Prop :=
      ∃ rd : UInt64, ∃ ce : UInt64, AttenuateLink rd ce s sNext

    def Spec (maxDepth rootExpiry : UInt64) : StateMachine MacaroonState :=
      StateMachine.mk (Init maxDepth rootExpiry) Next

    theorem depth_clamp_le : forall (d : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.macaroon_depth_clamp d cap)) (UInt64.toNat cap) :=
      fun d cap => Decidable.casesOn
        (motive := fun (dec : Decidable (LT.lt d cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) dec (fun _ => cap) (fun _ => d))) (UInt64.toNat cap))
        (instDecidableUInt64Lt d cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem expiry_narrow_le : forall (ce : UInt64) (pe : UInt64),
        Nat.le (UInt64.toNat (_root_.macaroon_expiry_narrow ce pe)) (UInt64.toNat pe) :=
      fun ce pe => Decidable.casesOn
        (motive := fun (dec : Decidable (LT.lt ce pe)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) dec (fun _ => pe) (fun _ => ce))) (UInt64.toNat pe))
        (instDecidableUInt64Lt ce pe)
        (fun _ => @Nat.le.refl (UInt64.toNat pe))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxDepth rootExpiry : UInt64) (s : MacaroonState)
        (hInit : Init maxDepth rootExpiry s) : MacaroonNarrowingInv s :=
      let hEqExp : s.childExpiryMs = s.parentExpiryMs :=
        Eq.trans hInit.2.2.1 (Eq.symm hInit.2.2.2)
      let hE : Nat.le (UInt64.toNat s.childExpiryMs) (UInt64.toNat s.parentExpiryMs) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.parentExpiryMs)) hEqExp)
          (@Nat.le.refl (UInt64.toNat s.parentExpiryMs))
      And.intro (zero_u64_le s.chainDepth s.maxDepth hInit.1) hE

    theorem attenuate_preserves_inv (rd ce : UInt64) (s sNext : MacaroonState)
        (hAct : AttenuateLink rd ce s sNext) : MacaroonNarrowingInv sNext :=
      let hD1 : Nat.le (UInt64.toNat sNext.chainDepth) (UInt64.toNat s.maxDepth) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxDepth)) hAct.1)
          (depth_clamp_le rd s.maxDepth)
      let hD2 : Nat.le (UInt64.toNat sNext.chainDepth) (UInt64.toNat sNext.maxDepth) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.chainDepth) (UInt64.toNat y)) hAct.2.1)
          hD1
      let hE1 : Nat.le (UInt64.toNat sNext.childExpiryMs) (UInt64.toNat s.childExpiryMs) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.childExpiryMs)) hAct.2.2.1)
          (expiry_narrow_le ce s.childExpiryMs)
      let hE2 : Nat.le (UInt64.toNat sNext.childExpiryMs) (UInt64.toNat sNext.parentExpiryMs) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.childExpiryMs) (UInt64.toNat y)) hAct.2.2.2)
          hE1
      And.intro hD2 hE2

    theorem next_preserves_inv (s sNext : MacaroonState)
        (_hInv : MacaroonNarrowingInv s) (hNext : Next s sNext) :
        MacaroonNarrowingInv sNext :=
      Exists.elim hNext (fun rd hEx =>
        Exists.elim hEx (fun ce hAct => attenuate_preserves_inv rd ce s sNext hAct))

    theorem spec_satisfies_macaroon_narrowing (maxDepth rootExpiry : UInt64) :
        (Spec maxDepth rootExpiry) ⊨ □ (Lift MacaroonNarrowingInv) :=
      invariantSatisfies (Spec maxDepth rootExpiry) MacaroonNarrowingInv
        (init_establishes_inv maxDepth rootExpiry)
        next_preserves_inv

    end TlaMacaroonAttenuation
    end Cap
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def macaroon_expiry_within_parent_isl (child_exp : UInt64) (parent_exp : UInt64) : Bool :=
      decide (child_exp ≤ parent_exp)
}
