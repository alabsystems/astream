// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `lib.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `lib.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Trust.Temporal)
    -- ========================================================================
    namespace Trust
    namespace Temporal

    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop

    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)

    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    def Eventually {State : Type} (F : Formula State) : Formula State :=
      fun b => ∃ n, F (drop b n)

    def LeadsTo {State : Type} (F G : Formula State) : Formula State :=
      Always (fun b => F b → Eventually G b)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    prefix:100 "□" => _root_.Trust.Temporal.Always
    prefix:100 "◇" => _root_.Trust.Temporal.Eventually
    infixl:50 " ~> " => _root_.Trust.Temporal.LeadsTo
    infixl:45 " ⊨ " => _root_.Trust.Temporal.Satisfies

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

    end Temporal
    end Trust

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from these Clean kernel definitions into Rust MIR
    --    (`pub const fn ...`) and verified by `trust_clean_origin::Faithful`.
    -- ========================================================================

    -- Monotone authorization clock advance (`max(cur_ms, sample_ms)`).
    def cap_clock_advance_monotone (cur_ms : UInt64) (sample_ms : UInt64) : UInt64 :=
      if cur_ms < sample_ms then sample_ms else cur_ms

    -- Tightest expiry across a Macaroon attenuation hop (`min(parent_exp, child_exp)`).
    def attenuate_expiry_min (parent_exp : UInt64) (child_exp : UInt64) : UInt64 :=
      if parent_exp < child_exp then parent_exp else child_exp

    -- 3-parameter Macaroon live-clock expiry gate (`clean_origin_mir` I5):
    -- collapses to `zero_val` if `exp <= now_ms`, and otherwise returns `exp`.
    def live_expiry_or_zero (exp : UInt64) (now_ms : UInt64) (zero_val : UInt64) : UInt64 :=
      if exp <= now_ms then zero_val else exp

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Capability Auth, Expiry & Revocation
    -- ========================================================================
    namespace Astream
    namespace Cap
    namespace TlaCapabilityProtocol

    open Trust.Temporal

    def attenuate_bounded_expiry_isl (now_ms parent_exp child_exp : UInt64) : UInt64 :=
      _root_.live_expiry_or_zero (_root_.attenuate_expiry_min parent_exp child_exp) now_ms 0

    theorem cap_clock_advance_ge_cur : forall (cur_ms : UInt64) (sample_ms : UInt64),
        Nat.le (UInt64.toNat cur_ms) (UInt64.toNat (_root_.cap_clock_advance_monotone cur_ms sample_ms)) :=
      fun cur sample => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur sample)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => sample))))
        (instDecidableUInt64Lt cur sample)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem attenuate_expiry_le_parent (parent_exp child_exp : UInt64) :
        _root_.attenuate_expiry_min parent_exp child_exp <= parent_exp := by
      unfold _root_.attenuate_expiry_min
      split <;> omega

    theorem attenuate_bounded_expiry_le_parent : forall (now_ms parent_exp child_exp : UInt64),
        Nat.le (UInt64.toNat (attenuate_bounded_expiry_isl now_ms parent_exp child_exp)) (UInt64.toNat parent_exp) :=
      fun now_ms parent_exp child_exp => Decidable.casesOn
        (motive := fun (d : Decidable (LE.le (_root_.attenuate_expiry_min parent_exp child_exp) now_ms)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d
            (fun _ => _root_.attenuate_expiry_min parent_exp child_exp)
            (fun _ => 0))) (UInt64.toNat parent_exp))
        (instDecidableUInt64Le (_root_.attenuate_expiry_min parent_exp child_exp) now_ms)
        (fun _ => attenuate_expiry_le_parent parent_exp child_exp)
        (fun _ => Nat.zero_le (UInt64.toNat parent_exp))

    theorem attenuate_expiry_le_child : forall (parent_exp : UInt64) (child_exp : UInt64),
        Nat.le (UInt64.toNat (_root_.attenuate_expiry_min parent_exp child_exp)) (UInt64.toNat child_exp) :=
      fun p c => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt p c)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => c) (fun _ => p))) (UInt64.toNat c))
        (instDecidableUInt64Lt p c)
        (fun _ => Nat.le.refl (UInt64.toNat c))
        (fun h => Nat.le_of_lt h)

    -- TLA+ state variables for a guarded broker connection:
    --   nonceIssued : 0 = no challenge nonce, 1 = fresh Hello/Nonce issued
    --   attached    : 0 = unattached, 1 = capability attached with PoP
    --   sessionMode : effective mode (0 = ReadOnly, 1 = ReadWrite)
    --   sessionPid  : bound producer_id for this session
    --   revoked     : 0 = active, 1 = principal revoked by operator
    --   nowMs       : monotone clock in unix milliseconds (`UInt64`)
    --   capMode     : HMAC-sealed capability mode (0 = ReadOnly, 1 = ReadWrite)
    --   capPid      : HMAC-sealed capability producer_id
    --   capExpMs    : HMAC-sealed capability expiry timestamp (`UInt64`)
    structure CapSessionState where
      nonceIssued : Nat
      attached    : Nat
      sessionMode : Nat
      sessionPid  : Nat
      revoked     : Nat
      nowMs       : UInt64
      capMode     : Nat
      capPid      : Nat
      capExpMs    : UInt64

    -- TLA+ Safety Invariant:
    -- Whenever a connection is attached (`attached = 1`), a fresh connection
    -- nonce was issued (`nonceIssued = 1`), the principal is not revoked
    -- (`revoked = 0`), and the connection's mode and producer_id equal the
    -- capability's HMAC-sealed grant (`sessionMode = capMode ∧ sessionPid = capPid`).
    def CapAuthSafetyInv (s : CapSessionState) : Prop :=
      s.attached = 1 →
        (s.nonceIssued = 1 ∧
         s.revoked = 0 ∧
         s.sessionMode = s.capMode ∧
         s.sessionPid = s.capPid)

    def Init (cMode cPid : Nat) (cExp t0 : UInt64) (s : CapSessionState) : Prop :=
      s.nonceIssued = 0 ∧
      s.attached = 0 ∧
      s.sessionMode = 0 ∧
      s.sessionPid = 0 ∧
      s.revoked = 0 ∧
      s.nowMs = t0 ∧
      s.capMode = cMode ∧
      s.capPid = cPid ∧
      s.capExpMs = cExp

    -- Action 1: IssueNonce — broker issues fresh 32-byte connection nonce on Hello.
    def IssueNonce (s sNext : CapSessionState) : Prop :=
      sNext.nonceIssued = 1 ∧
      sNext.attached = s.attached ∧
      sNext.sessionMode = s.sessionMode ∧
      sNext.sessionPid = s.sessionPid ∧
      sNext.revoked = s.revoked ∧
      sNext.nowMs = s.nowMs ∧
      sNext.capMode = s.capMode ∧
      sNext.capPid = s.capPid ∧
      sNext.capExpMs = s.capExpMs

    -- Action 2: AttachWithProof — client presents valid HMAC(tag, nonce || grant)
    -- while `nonceIssued = 1`, `revoked = 0`, and `nowMs < capExpMs`.
    def AttachWithProof (s sNext : CapSessionState) : Prop :=
      s.nonceIssued = 1 ∧
      s.revoked = 0 ∧
      Nat.lt (UInt64.toNat s.nowMs) (UInt64.toNat s.capExpMs) ∧
      sNext.nonceIssued = s.nonceIssued ∧
      sNext.attached = 1 ∧
      sNext.sessionMode = s.capMode ∧
      sNext.sessionPid = s.capPid ∧
      sNext.revoked = s.revoked ∧
      sNext.nowMs = s.nowMs ∧
      sNext.capMode = s.capMode ∧
      sNext.capPid = s.capPid ∧
      sNext.capExpMs = s.capExpMs

    -- Action 3: TickClock — monotone clock progression directly via Clean-origin
    -- `_root_.cap_clock_advance_monotone`.
    def TickClock (sampleMs : UInt64) (s sNext : CapSessionState) : Prop :=
      sNext.nowMs = _root_.cap_clock_advance_monotone s.nowMs sampleMs ∧
      sNext.nonceIssued = s.nonceIssued ∧
      sNext.attached = s.attached ∧
      sNext.sessionMode = s.sessionMode ∧
      sNext.sessionPid = s.sessionPid ∧
      sNext.revoked = s.revoked ∧
      sNext.capMode = s.capMode ∧
      sNext.capPid = s.capPid ∧
      sNext.capExpMs = s.capExpMs

    -- Action 4: RevokeIdentity — live identity revocation (`R6`) immediately
    -- detaches the session (`attached' = 0`, `sessionMode' = 0`, `revoked' = 1`).
    def RevokeIdentity (s sNext : CapSessionState) : Prop :=
      sNext.revoked = 1 ∧
      sNext.attached = 0 ∧
      sNext.sessionMode = 0 ∧
      sNext.nonceIssued = s.nonceIssued ∧
      sNext.sessionPid = s.sessionPid ∧
      sNext.nowMs = s.nowMs ∧
      sNext.capMode = s.capMode ∧
      sNext.capPid = s.capPid ∧
      sNext.capExpMs = s.capExpMs

    def Next (s sNext : CapSessionState) : Prop :=
      IssueNonce s sNext ∨
        (AttachWithProof s sNext ∨
          ((∃ sampleMs : UInt64, TickClock sampleMs s sNext) ∨ RevokeIdentity s sNext))

    def Spec (cMode cPid : Nat) (cExp t0 : UInt64) : StateMachine CapSessionState :=
      StateMachine.mk (Init cMode cPid cExp t0) Next

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (cMode cPid : Nat) (cExp t0 : UInt64) (s : CapSessionState)
        (hInit : Init cMode cPid cExp t0 s) : CapAuthSafetyInv s :=
      fun hAtt =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.1) hAtt
        False.elim (zero_ne_one h01)

    theorem issueNonce_preserves_inv (s sNext : CapSessionState)
        (hInv : CapAuthSafetyInv s) (hAct : IssueNonce s sNext) :
        CapAuthSafetyInv sNext :=
      fun hAttNext =>
        let hAtt : s.attached = 1 := Eq.trans (Eq.symm hAct.2.1) hAttNext
        let hPre := hInv hAtt
        And.intro hAct.1
          (And.intro
            (Eq.trans hAct.2.2.2.2.1 hPre.2.1)
            (And.intro
              (Eq.trans hAct.2.2.1 (Eq.trans hPre.2.2.1 (Eq.symm hAct.2.2.2.2.2.2.1)))
              (Eq.trans hAct.2.2.2.1 (Eq.trans hPre.2.2.2 (Eq.symm hAct.2.2.2.2.2.2.2.1)))))

    theorem attach_preserves_inv (s sNext : CapSessionState)
        (hAct : AttachWithProof s sNext) :
        CapAuthSafetyInv sNext :=
      fun _ =>
        And.intro
          (Eq.trans hAct.2.2.2.1 hAct.1)
          (And.intro
            (Eq.trans hAct.2.2.2.2.2.2.2.1 hAct.2.1)
            (And.intro
              (Eq.trans hAct.2.2.2.2.2.1 (Eq.symm hAct.2.2.2.2.2.2.2.2.2.1))
              (Eq.trans hAct.2.2.2.2.2.2.1 (Eq.symm hAct.2.2.2.2.2.2.2.2.2.2.1))))

    theorem tickClock_preserves_inv (sampleMs : UInt64) (s sNext : CapSessionState)
        (hInv : CapAuthSafetyInv s) (hAct : TickClock sampleMs s sNext) :
        CapAuthSafetyInv sNext :=
      fun hAttNext =>
        let hAtt : s.attached = 1 := Eq.trans (Eq.symm hAct.2.2.1) hAttNext
        let hPre := hInv hAtt
        And.intro
          (Eq.trans hAct.2.1 hPre.1)
          (And.intro
            (Eq.trans hAct.2.2.2.2.2.1 hPre.2.1)
            (And.intro
              (Eq.trans hAct.2.2.2.1 (Eq.trans hPre.2.2.1 (Eq.symm hAct.2.2.2.2.2.2.1)))
              (Eq.trans hAct.2.2.2.2.1 (Eq.trans hPre.2.2.2 (Eq.symm hAct.2.2.2.2.2.2.2.1)))))

    theorem revoke_preserves_inv (s sNext : CapSessionState)
        (hAct : RevokeIdentity s sNext) :
        CapAuthSafetyInv sNext :=
      fun hAttNext =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.1) hAttNext
        False.elim (zero_ne_one h01)

    theorem next_preserves_inv (s sNext : CapSessionState)
        (hInv : CapAuthSafetyInv s) (hNext : Next s sNext) :
        CapAuthSafetyInv sNext :=
      Or.elim hNext
        (fun hIss => issueNonce_preserves_inv s sNext hInv hIss)
        (fun hR1 =>
          Or.elim hR1
            (fun hAtt => attach_preserves_inv s sNext hAtt)
            (fun hR2 =>
              Or.elim hR2
                (fun hEx =>
                  Exists.elim hEx (fun sampleMs hTick =>
                    tickClock_preserves_inv sampleMs s sNext hInv hTick))
                (fun hRev => revoke_preserves_inv s sNext hRev)))

    -- Full TLA+ Temporal Safety Theorem:
    --   `Spec cMode cPid cExp t0 ⊨ □ (Lift CapAuthSafetyInv)`
    theorem spec_satisfies_cap_auth_safety (cMode cPid : Nat) (cExp t0 : UInt64) :
        (Spec cMode cPid cExp t0) ⊨ □ (Lift CapAuthSafetyInv) :=
      invariantSatisfies (Spec cMode cPid cExp t0) CapAuthSafetyInv
        (init_establishes_inv cMode cPid cExp t0)
        next_preserves_inv

    -- Irrevocability of capability expiry under a monotone clock:
    -- once `exp <= now1` and `now1 <= now2`, the capability remains expired (`exp <= now2`).
    theorem expiry_monotone_irrevocable (exp now1 now2 : Nat)
        (hExpired : Nat.le exp now1) (hClock : Nat.le now1 now2) :
        Nat.le exp now2 :=
      Nat.le_trans hExpired hClock

    -- Attenuation soundness: if an attenuated child capability has tighter expiry
    -- `expChild <= expParent`, then whenever the parent is expired (`expParent <= now`),
    -- the child is also expired (`expChild <= now`).
    theorem attenuation_expiry_sound (expParent expChild now : Nat)
        (hTighter : Nat.le expChild expParent) (hParentExp : Nat.le expParent now) :
        Nat.le expChild now :=
      Nat.le_trans hTighter hParentExp

    -- Attenuation transitivity across multi-hop delegation chains:
    -- if `c <= b` and `b <= a`, then `c <= a`.
    theorem attenuation_mode_trans (a b c : Nat)
        (hCB : Nat.le c b) (hBA : Nat.le b a) :
        Nat.le c a :=
      Nat.le_trans hCB hBA

    -- Offline Macaroon capability descriptor (mode, bound principal id, expiry).
    structure MacaroonCap where
      mode  : Nat
      pid   : Nat
      expMs : Nat

    -- Monotone attenuation relation across a single Macaroon hop (`via=`).
    def ValidAttenuation (parent child : MacaroonCap) : Prop :=
      Nat.le child.mode parent.mode ∧
      (parent.pid = 0 ∨ child.pid = parent.pid) ∧
      Nat.le child.expMs parent.expMs

    theorem validAttenuation_refl (c : MacaroonCap) : ValidAttenuation c c :=
      And.intro (Nat.le_refl c.mode)
        (And.intro (Or.inr rfl) (Nat.le_refl c.expMs))

    -- Multi-hop Macaroon chain transitivity: any chain of valid offline
    -- attenuations `root -> mid -> leaf` is a valid attenuation `root -> leaf`.
    theorem validAttenuation_trans (root mid leaf : MacaroonCap)
        (h1 : ValidAttenuation root mid) (h2 : ValidAttenuation mid leaf) :
        ValidAttenuation root leaf :=
      And.intro
        (Nat.le_trans h2.1 h1.1)
        (And.intro
          (Or.elim h1.2.1
            (fun hRootUnbound => Or.inl hRootUnbound)
            (fun hMidEqRoot =>
              Or.elim h2.2.1
                (fun hMidUnbound => Or.inl (Eq.trans (Eq.symm hMidEqRoot) hMidUnbound))
                (fun hLeafEqMid => Or.inr (Eq.trans hLeafEqMid hMidEqRoot))))
          (Nat.le_trans h2.2.2 h1.2.2))

    end TlaCapabilityProtocol
    end Cap
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    -- Half-open expiry check: a grant with `expires_at = Some(exp)` is expired
    -- iff `exp <= now_ms`.
    def grant_expired_isl (exp : UInt64) (now_ms : UInt64) : Bool :=
      decide (exp <= now_ms)

    -- Principal producer-id equality check: a principal-bound grant authorizes
    -- publishing as `actual` iff `expected = actual`.
    def pid_matches_isl (expected : UInt64) (actual : UInt64) : Bool :=
      decide (expected = actual)

    -- Expiry attenuation check: a child expiry `child_exp` is within a parent
    -- expiry `parent_exp` iff `child_exp <= parent_exp`.
    def expiry_attenuates_isl (child_exp : UInt64) (parent_exp : UInt64) : Bool :=
      decide (child_exp <= parent_exp)

    -- Macaroon chain depth check: `depth < max_depth`.
    def depth_within_limit_isl (depth : UInt64) (max_depth : UInt64) : Bool :=
      decide (depth < max_depth)
}
