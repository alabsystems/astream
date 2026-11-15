// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `frame.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `frame.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaFrameCodec)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaFrameCodec

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

    prefix:100 "□" => _root_.Astream.Wire.TlaFrameCodec.Always
    infixl:45 " ⊨ " => _root_.Astream.Wire.TlaFrameCodec.Satisfies

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

    end TlaFrameCodec
    end Wire
    end Astream

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn frame_clamp_payload_len`) and verified by
    --    `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Clamps a frame payload length `len` to the policy ceiling `cap` (`min(len, cap)`).
    -- Compiled directly to `pub const fn frame_clamp_payload_len(len: u64, cap: u64) -> u64`.
    def frame_clamp_payload_len (len : UInt64) (cap : UInt64) : UInt64 :=
      if len < cap then len else cap

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Bounded-Buffering Wire Frame Codec
    --    Directly over `UInt64` lengths, `_root_.frame_clamp_payload_len`, and
    --    `payload_within_cap_isl`
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaFrameCodec

    -- Island specification of `pub fn payload_within_cap(len: u64, cap: u64) -> bool`.
    def payload_within_cap_isl (len : UInt64) (cap : UInt64) : Bool :=
      decide (len <= cap)

    -- Upper-bound guarantee of the Clean-origin `_root_.frame_clamp_payload_len`:
    -- `frame_clamp_payload_len len cap <= cap`.
    theorem frame_clamp_payload_len_le_cap : forall (len : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.frame_clamp_payload_len len cap)) (UInt64.toNat cap) :=
      fun len cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => len))) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun h => Nat.le_of_lt h)

    theorem bool_false_ne_true (h : false = true) : False :=
      Bool.noConfusion h

    theorem payload_within_cap_isl_true_le (len cap : UInt64) :
        payload_within_cap_isl len cap = true → Nat.le (UInt64.toNat len) (UInt64.toNat cap) :=
      @Decidable.casesOn (LE.le len cap)
        (fun (d : Decidable (LE.le len cap)) =>
          @Decidable.decide (LE.le len cap) d = true → Nat.le (UInt64.toNat len) (UInt64.toNat cap))
        (instDecidableUInt64Le len cap)
        (fun _ hEq => False.elim (bool_false_ne_true hEq))
        (fun hLe _ => hLe)

    -- State of the streaming frame decoder:
    --   status       : 0 = NeedMoreHeader, 1 = WaitingPayload, 2 = Decoded, 3 = RejectedTooLarge
    --   committedLen : payload length the decoder has committed to buffer (`UInt64`)
    --   maxCap       : policy ceiling (`MAX_PAYLOAD_LEN = 16 MiB`, `UInt64`)
    structure CodecState where
      status       : Nat
      committedLen : UInt64
      maxCap       : UInt64

    -- TLA+ Bounded-Buffering Safety Invariant:
    -- 1. The decoder NEVER commits to buffering a payload length above `maxCap`.
    -- 2. Whenever an oversized header is rejected (`status = 3`), `committedLen = 0`.
    def FrameCodecSafetyInv (s : CodecState) : Prop :=
      Nat.le (UInt64.toNat s.committedLen) (UInt64.toNat s.maxCap) ∧
      (s.status = 3 → s.committedLen = 0)

    def Init (cap : UInt64) (s : CodecState) : Prop :=
      s.status = 0 ∧
      s.committedLen = 0 ∧
      s.maxCap = cap

    -- Action 1: CommitHeaderWithinCap — header parsed with `len <= maxCap`;
    -- decoder commits to buffering `frame_clamp_payload_len hdr_len s.maxCap`.
    def CommitHeaderWithinCap (hdr_len : UInt64) (s sNext : CodecState) : Prop :=
      s.status = 0 ∧
      payload_within_cap_isl hdr_len s.maxCap = true ∧
      sNext.status = 1 ∧
      sNext.committedLen = _root_.frame_clamp_payload_len hdr_len s.maxCap ∧
      sNext.maxCap = s.maxCap

    -- Action 2: RejectOversizeHeader — header advertises `hdr_len > maxCap`;
    -- rejected outright with `committedLen = 0` (never buffered toward).
    def RejectOversizeHeader (hdr_len : UInt64) (s sNext : CodecState) : Prop :=
      s.status = 0 ∧
      payload_within_cap_isl hdr_len s.maxCap = false ∧
      sNext.status = 3 ∧
      sNext.committedLen = 0 ∧
      sNext.maxCap = s.maxCap

    -- Action 3: CompleteFrame — full payload arrived and CRC verified.
    def CompleteFrame (s sNext : CodecState) : Prop :=
      s.status = 1 ∧
      sNext.status = 2 ∧
      sNext.committedLen = s.committedLen ∧
      sNext.maxCap = s.maxCap

    -- Action 4: ResetDecoder — advance input window past consumed frame.
    def ResetDecoder (s sNext : CodecState) : Prop :=
      sNext.status = 0 ∧
      sNext.committedLen = 0 ∧
      sNext.maxCap = s.maxCap

    def Next (s sNext : CodecState) : Prop :=
      (∃ hdr_len : UInt64, CommitHeaderWithinCap hdr_len s sNext) ∨
        ((∃ hdr_len : UInt64, RejectOversizeHeader hdr_len s sNext) ∨
          (CompleteFrame s sNext ∨ ResetDecoder s sNext))

    def Spec (cap : UInt64) : StateMachine CodecState :=
      StateMachine.mk (Init cap) Next

    theorem zero_ne_three (h : 0 = 3) : False :=
      Nat.noConfusion h

    theorem one_ne_three (h : 1 = 3) : False :=
      Nat.noConfusion h (fun h02 => Nat.noConfusion h02)

    theorem two_ne_three (h : 2 = 3) : False :=
      Nat.noConfusion h (fun h12 => Nat.noConfusion h12 (fun h01 => Nat.noConfusion h01))

    theorem uint64_zero_le (cap : UInt64) (c : UInt64) (hZero : c = 0) :
        Nat.le (UInt64.toNat c) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (cap : UInt64) (s : CodecState)
        (hInit : Init cap s) : FrameCodecSafetyInv s :=
      And.intro
        (uint64_zero_le s.maxCap s.committedLen hInit.2.1)
        (fun hSt3 =>
          let h03 : 0 = 3 := Eq.trans (Eq.symm hInit.1) hSt3
          False.elim (zero_ne_three h03))

    theorem commitHeader_preserves_inv (hdr_len : UInt64) (s sNext : CodecState)
        (hAct : CommitHeaderWithinCap hdr_len s sNext) : FrameCodecSafetyInv sNext :=
      let hClamp : Nat.le (UInt64.toNat (_root_.frame_clamp_payload_len hdr_len s.maxCap)) (UInt64.toNat s.maxCap) :=
        frame_clamp_payload_len_le_cap hdr_len s.maxCap
      let hComm : sNext.committedLen = _root_.frame_clamp_payload_len hdr_len s.maxCap := hAct.2.2.2.1
      let hCap : sNext.maxCap = s.maxCap := hAct.2.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.committedLen) (UInt64.toNat s.maxCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxCap)) hComm) hClamp
      let hLe2 : Nat.le (UInt64.toNat sNext.committedLen) (UInt64.toNat sNext.maxCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedLen) (UInt64.toNat y)) hCap) hLe1
      And.intro
        hLe2
        (fun hSt3 =>
          let h13 : 1 = 3 := Eq.trans (Eq.symm hAct.2.2.1) hSt3
          False.elim (one_ne_three h13))

    theorem rejectOversize_preserves_inv (hdr_len : UInt64) (s sNext : CodecState)
        (hAct : RejectOversizeHeader hdr_len s sNext) : FrameCodecSafetyInv sNext :=
      And.intro
        (uint64_zero_le sNext.maxCap sNext.committedLen hAct.2.2.2.1)
        (fun _ => hAct.2.2.2.1)

    theorem completeFrame_preserves_inv (s sNext : CodecState)
        (hInv : FrameCodecSafetyInv s) (hAct : CompleteFrame s sNext) : FrameCodecSafetyInv sNext :=
      let hComm : sNext.committedLen = s.committedLen := hAct.2.2.1
      let hCap : sNext.maxCap = s.maxCap := hAct.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.committedLen) (UInt64.toNat s.maxCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxCap)) hComm) hInv.1
      let hLe2 : Nat.le (UInt64.toNat sNext.committedLen) (UInt64.toNat sNext.maxCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedLen) (UInt64.toNat y)) hCap) hLe1
      And.intro
        hLe2
        (fun hSt3 =>
          let h23 : 2 = 3 := Eq.trans (Eq.symm hAct.2.1) hSt3
          False.elim (two_ne_three h23))

    theorem resetDecoder_preserves_inv (s sNext : CodecState)
        (hAct : ResetDecoder s sNext) : FrameCodecSafetyInv sNext :=
      And.intro
        (uint64_zero_le sNext.maxCap sNext.committedLen hAct.2.1)
        (fun hSt3 =>
          let h03 : 0 = 3 := Eq.trans (Eq.symm hAct.1) hSt3
          False.elim (zero_ne_three h03))

    theorem next_preserves_inv (s sNext : CodecState)
        (hInv : FrameCodecSafetyInv s) (hNext : Next s sNext) : FrameCodecSafetyInv sNext :=
      Or.elim hNext
        (fun hCommit => Exists.elim hCommit (fun hdr_len hAct => commitHeader_preserves_inv hdr_len s sNext hAct))
        (fun hRest1 =>
          Or.elim hRest1
            (fun hReject => Exists.elim hReject (fun hdr_len hAct => rejectOversize_preserves_inv hdr_len s sNext hAct))
            (fun hRest2 =>
              Or.elim hRest2
                (fun hComp => completeFrame_preserves_inv s sNext hInv hComp)
                (fun hReset => resetDecoder_preserves_inv s sNext hReset)))

    theorem spec_satisfies_frame_codec_safety (cap : UInt64) :
        (Spec cap) ⊨ □ (Lift FrameCodecSafetyInv) :=
      invariantSatisfies (Spec cap) FrameCodecSafetyInv
        (init_establishes_inv cap)
        next_preserves_inv

    end TlaFrameCodec
    end Wire
    end Astream
}
