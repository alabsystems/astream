// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `lib.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `lib.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from these Clean kernel definitions into Rust MIR
    --    (`pub const fn kafka_clamp_str_len` and
    --     `pub const fn kafka_negotiate_error_code`) and verified by `Faithful`.
    -- ========================================================================

    -- Clamp a string byte length to the Kafka v0 STRING cap (`i16::MAX = 32767`).
    def kafka_clamp_str_len (len : UInt64) (cap : UInt64) : UInt64 :=
      if len < cap then len else cap

    -- Multi-condition Kafka ApiVersions bootstrap version-negotiation kernel:
    -- returns `none_code (0)` when `req_ver <= max_ver`, else `unsupported_code (35)`
    -- so a flexible v3+ client downgrades to v0 using the v0-shaped response body.
    def kafka_negotiate_error_code (req_ver : UInt64) (max_ver : UInt64) (unsupported_code : UInt64) (none_code : UInt64) : UInt64 :=
      if max_ver < req_ver then unsupported_code else none_code

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Kafka.TlaKafkaWireCodec)
    -- ========================================================================
    namespace Astream
    namespace Kafka
    namespace TlaKafkaWireCodec

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

    prefix:100 "□" => _root_.Astream.Kafka.TlaKafkaWireCodec.Always
    infixl:45 " ⊨ " => _root_.Astream.Kafka.TlaKafkaWireCodec.Satisfies

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

    theorem kafka_clamp_str_len_le_cap : forall (len : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kafka_clamp_str_len len cap)) (UInt64.toNat cap) :=
      fun len cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => len))) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun h => Nat.le_of_lt h)

    theorem kafka_negotiate_binary (req_ver max_ver unsupported_code : UInt64) :
        _root_.kafka_negotiate_error_code req_ver max_ver unsupported_code 0 = 0 ∨
        _root_.kafka_negotiate_error_code req_ver max_ver unsupported_code 0 = unsupported_code :=
      @Decidable.casesOn (LT.lt max_ver req_ver)
        (fun (d : Decidable (LT.lt max_ver req_ver)) =>
          @ite UInt64 (LT.lt max_ver req_ver) d unsupported_code 0 = 0 ∨
          @ite UInt64 (LT.lt max_ver req_ver) d unsupported_code 0 = unsupported_code)
        (instDecidableUInt64Lt max_ver req_ver)
        (fun _ => Or.inl (Eq.refl 0))
        (fun _ => Or.inr (Eq.refl unsupported_code))

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Kafka Wire Handshake & String Clamping
    -- ========================================================================
    structure KafkaHandshakeState where
      maxVersion      : UInt64
      strLenCap       : UInt64
      unsupportedCode : UInt64
      lastClampedLen  : UInt64
      lastErrCode     : UInt64

    -- TLA+ Safety Invariant:
    -- 1. Every clamped wire string length fits within `strLenCap` (`i16::MAX`).
    -- 2. Every negotiated ApiVersions error code is either `0` (`NONE`) or
    --    `unsupportedCode` (`UNSUPPORTED_VERSION = 35`).
    def KafkaHandshakeSafetyInv (s : KafkaHandshakeState) : Prop :=
      Nat.le (UInt64.toNat s.lastClampedLen) (UInt64.toNat s.strLenCap) ∧
      (s.lastErrCode = 0 ∨ s.lastErrCode = s.unsupportedCode)

    def Init (maxVer cap unsup : UInt64) (s : KafkaHandshakeState) : Prop :=
      s.maxVersion = maxVer ∧
      s.strLenCap = cap ∧
      s.unsupportedCode = unsup ∧
      s.lastClampedLen = 0 ∧
      s.lastErrCode = 0

    def EncodeString (rawLen : UInt64) (s sNext : KafkaHandshakeState) : Prop :=
      sNext.maxVersion = s.maxVersion ∧
      sNext.strLenCap = s.strLenCap ∧
      sNext.unsupportedCode = s.unsupportedCode ∧
      sNext.lastClampedLen = _root_.kafka_clamp_str_len rawLen s.strLenCap ∧
      sNext.lastErrCode = s.lastErrCode

    def NegotiateApiVersions (reqVer : UInt64) (s sNext : KafkaHandshakeState) : Prop :=
      sNext.maxVersion = s.maxVersion ∧
      sNext.strLenCap = s.strLenCap ∧
      sNext.unsupportedCode = s.unsupportedCode ∧
      sNext.lastClampedLen = s.lastClampedLen ∧
      sNext.lastErrCode = _root_.kafka_negotiate_error_code reqVer s.maxVersion s.unsupportedCode 0

    def Next (s sNext : KafkaHandshakeState) : Prop :=
      (∃ rawLen : UInt64, EncodeString rawLen s sNext) ∨
      (∃ reqVer : UInt64, NegotiateApiVersions reqVer s sNext)

    def Spec (maxVer cap unsup : UInt64) : StateMachine KafkaHandshakeState :=
      StateMachine.mk (Init maxVer cap unsup) Next

    theorem init_establishes_inv (maxVer cap unsup : UInt64) (s : KafkaHandshakeState)
        (hInit : Init maxVer cap unsup s) : KafkaHandshakeSafetyInv s :=
      let hZeroLe : Nat.le (UInt64.toNat 0) (UInt64.toNat s.strLenCap) :=
        Nat.zero_le (UInt64.toNat s.strLenCap)
      let hClampLe : Nat.le (UInt64.toNat s.lastClampedLen) (UInt64.toNat s.strLenCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.strLenCap)) hInit.2.2.2.1) hZeroLe
      And.intro hClampLe (Or.inl hInit.2.2.2.2)

    theorem encodeString_preserves_inv (rawLen : UInt64) (s sNext : KafkaHandshakeState)
        (hInv : KafkaHandshakeSafetyInv s) (hAct : EncodeString rawLen s sNext) :
        KafkaHandshakeSafetyInv sNext :=
      let hCapEq : sNext.strLenCap = s.strLenCap := hAct.2.1
      let hUnsupEq : sNext.unsupportedCode = s.unsupportedCode := hAct.2.2.1
      let hClampEq : sNext.lastClampedLen = _root_.kafka_clamp_str_len rawLen s.strLenCap := hAct.2.2.2.1
      let hErrEq : sNext.lastErrCode = s.lastErrCode := hAct.2.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.lastClampedLen) (UInt64.toNat s.strLenCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.strLenCap)) hClampEq)
          (kafka_clamp_str_len_le_cap rawLen s.strLenCap)
      let hLeNext : Nat.le (UInt64.toNat sNext.lastClampedLen) (UInt64.toNat sNext.strLenCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.lastClampedLen) (UInt64.toNat y)) hCapEq) hLe1
      let hErrNext : sNext.lastErrCode = 0 ∨ sNext.lastErrCode = sNext.unsupportedCode :=
        Or.elim hInv.2
          (fun h0 => Or.inl (Eq.trans hErrEq h0))
          (fun hU => Or.inr (Eq.trans hErrEq (Eq.trans hU (Eq.symm hUnsupEq))))
      And.intro hLeNext hErrNext

    theorem negotiate_preserves_inv (reqVer : UInt64) (s sNext : KafkaHandshakeState)
        (hInv : KafkaHandshakeSafetyInv s) (hAct : NegotiateApiVersions reqVer s sNext) :
        KafkaHandshakeSafetyInv sNext :=
      let hCapEq : sNext.strLenCap = s.strLenCap := hAct.2.1
      let hUnsupEq : sNext.unsupportedCode = s.unsupportedCode := hAct.2.2.1
      let hClampEq : sNext.lastClampedLen = s.lastClampedLen := hAct.2.2.2.1
      let hErrEq : sNext.lastErrCode = _root_.kafka_negotiate_error_code reqVer s.maxVersion s.unsupportedCode 0 := hAct.2.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.lastClampedLen) (UInt64.toNat s.strLenCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.strLenCap)) hClampEq) hInv.1
      let hLeNext : Nat.le (UInt64.toNat sNext.lastClampedLen) (UInt64.toNat sNext.strLenCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.lastClampedLen) (UInt64.toNat y)) hCapEq) hLe1
      let hBin := kafka_negotiate_binary reqVer s.maxVersion s.unsupportedCode
      let hErrNext : sNext.lastErrCode = 0 ∨ sNext.lastErrCode = sNext.unsupportedCode :=
        Or.elim hBin
          (fun h0 => Or.inl (Eq.trans hErrEq h0))
          (fun hU => Or.inr (Eq.trans hErrEq (Eq.trans hU (Eq.symm hUnsupEq))))
      And.intro hLeNext hErrNext

    theorem next_preserves_inv (s sNext : KafkaHandshakeState)
        (hInv : KafkaHandshakeSafetyInv s) (hNext : Next s sNext) :
        KafkaHandshakeSafetyInv sNext :=
      Or.elim hNext
        (fun hEx => Exists.elim hEx (fun rawLen hEnc => encodeString_preserves_inv rawLen s sNext hInv hEnc))
        (fun hEx => Exists.elim hEx (fun reqVer hNeg => negotiate_preserves_inv reqVer s sNext hInv hNeg))

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec maxVer cap unsup) ⊨ □ (Lift KafkaHandshakeSafetyInv)`
    theorem spec_satisfies_kafka_handshake_safety (maxVer cap unsup : UInt64) :
        (Spec maxVer cap unsup) ⊨ □ (Lift KafkaHandshakeSafetyInv) :=
      invariantSatisfies (Spec maxVer cap unsup) KafkaHandshakeSafetyInv
        (init_establishes_inv maxVer cap unsup)
        next_preserves_inv

    end TlaKafkaWireCodec
    end Kafka
    end Astream

    def version_within_max_isl (req_ver : UInt64) (max_ver : UInt64) : Bool :=
      decide (req_ver ≤ max_ver)
}
