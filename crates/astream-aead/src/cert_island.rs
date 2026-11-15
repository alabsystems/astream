// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `cert.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `cert.rs` mounts this file under `cfg(clean_islands)`,
// which build.rs sets when the compiler answers that it is Trust. Every other compiler calls
// the plain-Rust twins in `twins.rs` of the functions it compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    -- ========================================================================
    def cert_validity_clamp (raw : UInt64) (cap : UInt64) : UInt64 :=
      if raw < cap then raw else cap

    def cert_epoch_advance (prev : UInt64) (cand : UInt64) : UInt64 :=
      if prev < cand then cand else prev

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Aead.TlaCertAuthority)
    -- ========================================================================
    namespace Astream
    namespace Aead
    namespace TlaCertAuthority

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

    structure CertAuthorityState where
      bounded_span : UInt64
      max_cap : UInt64
      epoch : UInt64
      prev_epoch : UInt64

    def CertAuthorityInv (s : CertAuthorityState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.bounded_span) (UInt64.toNat s.max_cap))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.epoch))

    def Init (s : CertAuthorityState) : Prop :=
      And
        (s.bounded_span = 0)
        (And (s.epoch = 0) (s.prev_epoch = 0))

    def stepTransition (raw_span : UInt64) (cand_ep : UInt64) (s : CertAuthorityState) : CertAuthorityState :=
      CertAuthorityState.mk
        (_root_.cert_validity_clamp raw_span s.max_cap)
        s.max_cap
        (_root_.cert_epoch_advance s.epoch cand_ep)
        s.epoch

    def Next (s : CertAuthorityState) (s' : CertAuthorityState) : Prop :=
      ∃ (raw_span : UInt64), ∃ (cand_ep : UInt64),
        s' = stepTransition raw_span cand_ep s

    def Spec : StateMachine CertAuthorityState :=
      StateMachine.mk Init Next

    theorem clamp_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.cert_validity_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.cert_epoch_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
        Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (_hB : b = 0) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : CertAuthorityState) (hInit : Init s) :
        CertAuthorityInv s :=
      And.intro
        (zero_le_cap s.bounded_span s.max_cap (And.left hInit))
        (eq_zero_le
          s.prev_epoch
          s.epoch
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : CertAuthorityState) (s' : CertAuthorityState)
        (_hInv : CertAuthorityInv s) (hNext : Next s s') :
        CertAuthorityInv s' :=
      Exists.elim hNext (fun (rs : UInt64) (hRest : ∃ (ce : UInt64), s' = stepTransition rs ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = stepTransition rs ce s) =>
          Eq.mpr
            (congrArg (fun (st : CertAuthorityState) => CertAuthorityInv st) hEq)
            (And.intro
              (clamp_le_cap rs s.max_cap)
              (epoch_monotone s.epoch ce))))

    theorem cert_authority_safety_always :
        Satisfies Spec (Always (Lift CertAuthorityInv)) :=
      invariantSatisfies Spec CertAuthorityInv init_establishes_inv next_preserves_inv

    end TlaCertAuthority
    end Aead
    end Astream

    -- ========================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- ========================================================================
    def cert_horizon_reached_isl (observed : UInt64) (threshold : UInt64) : Bool :=
      decide (threshold ≤ observed)

    def cert_wire_version_valid_isl (ver : UInt8) : Bool :=
      decide (ver = 1)
}
