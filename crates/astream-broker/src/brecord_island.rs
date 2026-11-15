// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `brecord.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `brecord.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def brecord_clamp_body_len (len : UInt64) (max_len : UInt64) : UInt64 :=
      if len < max_len then len else max_len

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaRecordSkin)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaRecordSkin

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaRecordSkin.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaRecordSkin.Always

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

    structure BrecordState where
      bodyLen    : UInt64
      maxBodyLen : UInt64

    def BrecordBodyBoundedInv (s : BrecordState) : Prop :=
      Nat.le (UInt64.toNat s.bodyLen) (UInt64.toNat s.maxBodyLen)

    def Init (s : BrecordState) : Prop :=
      s.bodyLen = 0 ∧ s.maxBodyLen = 16777216

    def encodeRecordAction (rawLen : UInt64) (s sNext : BrecordState) : Prop :=
      sNext.maxBodyLen = s.maxBodyLen ∧
      sNext.bodyLen = _root_.brecord_clamp_body_len rawLen s.maxBodyLen

    def Next (s sNext : BrecordState) : Prop :=
      ∃ rawLen : UInt64, encodeRecordAction rawLen s sNext

    def Spec : StateMachine BrecordState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (len : UInt64) (max_len : UInt64),
        Nat.le (UInt64.toNat (_root_.brecord_clamp_body_len len max_len)) (UInt64.toNat max_len) :=
      fun len max_len => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len max_len)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_len) (fun _ => len))) (UInt64.toNat max_len))
        (instDecidableUInt64Lt len max_len)
        (fun _ => Nat.le.refl (UInt64.toNat max_len))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a b : UInt64) (hZero : a = 0) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : BrecordState) (hInit : Init s) :
        BrecordBodyBoundedInv s :=
      uint64_zero_le s.bodyLen s.maxBodyLen hInit.1

    theorem next_preserves_inv (s sNext : BrecordState)
        (_hInv : BrecordBodyBoundedInv s) (hNext : Next s sNext) :
        BrecordBodyBoundedInv sNext :=
      Exists.elim hNext (fun rawLen hAct =>
        let hClamp : Nat.le (UInt64.toNat (_root_.brecord_clamp_body_len rawLen s.maxBodyLen)) (UInt64.toNat s.maxBodyLen) :=
          clamp_le_max rawLen s.maxBodyLen
        let hEqBody : sNext.bodyLen = _root_.brecord_clamp_body_len rawLen s.maxBodyLen := hAct.2
        let hEqMax : sNext.maxBodyLen = s.maxBodyLen := hAct.1
        Eq.mpr
          (congrArg (fun (m : UInt64) => Nat.le (UInt64.toNat sNext.bodyLen) (UInt64.toNat m)) hEqMax)
          (Eq.mpr
            (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.maxBodyLen)) hEqBody)
            hClamp))

    theorem spec_satisfies_brecord_body_bounded :
        Spec ⊨ □ (Lift BrecordBodyBoundedInv) :=
      invariantSatisfies Spec BrecordBodyBoundedInv init_establishes_inv next_preserves_inv

    end TlaRecordSkin
    end Broker
    end Astream

    def brecord_version_current_isl (ver : UInt8) : Bool :=
      decide (ver = 2)
}
