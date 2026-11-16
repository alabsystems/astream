// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `transport.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `transport.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def kafka_listener_nonzero_bit (val : UInt64) (one_val : UInt64) : UInt64 :=
      if val < 1 then 0 else one_val

    def kafka_listener_req_select (required : UInt64) (present_bit : UInt64) : UInt64 :=
      if required < 1 then 1 else present_bit

    def kafka_listener_level_advance (cur_level : UInt64) (proposed_level : UInt64) : UInt64 :=
      if cur_level < proposed_level then proposed_level else cur_level

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Sealed Listener Spec
    -- =======================================================================

    namespace Astream
    namespace Kafka
    namespace TlaSealedListener

    def Behavior (State : Type) : Type := Nat → State

    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun (k : Nat) => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (n : Nat), P (drop n b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (n : Nat), M.Next (b n) (b (Nat.add n 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (P : Formula State) (Q : Formula State) : Prop :=
      ∀ (b : Behavior State), P b → Q b

    theorem invariantAt
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s')
      (b : Behavior State)
      (hRun : Runs M b)
      (k : Nat) :
      Inv (b k) :=
      Nat.rec
        (hInit (b 0) (And.left hRun))
        (fun (j : Nat) (ih : Inv (b j)) =>
          hStep (b j) (b (Nat.add j 1)) ih (And.right hRun j))
        k

    theorem invariantSatisfies
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s') :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    -- Security level lattice:
    --   0 = Plaintext
    --   1 = SealedPSK
    --   2 = ForwardSecretHandshake / RoamUdp
    --   3 = MutualIdentityEd25519
    --   4 = CertifiedCaSigma
    def kafka_listener_gate_code_isl (require_encrypted : UInt64) (is_encrypted : UInt64) (require_sasl : UInt64) (sasl_authed : UInt64) : UInt64 :=
      let enc_ok := _root_.kafka_listener_req_select require_encrypted (_root_.kafka_listener_nonzero_bit is_encrypted (1 : UInt64))
      let sasl_ok := _root_.kafka_listener_req_select require_sasl (_root_.kafka_listener_nonzero_bit sasl_authed (1 : UInt64))
      _root_.kafka_listener_nonzero_bit enc_ok sasl_ok

    structure ListenerState where
      prev_level : UInt64
      level : UInt64

    def ListenerMonotoneInv (s : ListenerState) : Prop :=
      Nat.le (UInt64.toNat s.prev_level) (UInt64.toNat s.level)

    def Init (s : ListenerState) : Prop :=
      s.prev_level = s.level

    def upgradeAction (proposed_level : UInt64) (s : ListenerState) : ListenerState :=
      ListenerState.mk
        s.level
        (_root_.kafka_listener_level_advance s.level proposed_level)

    def Next (s : ListenerState) (s' : ListenerState) : Prop :=
      ∃ (proposed_level : UInt64), s' = upgradeAction proposed_level s

    def Spec : StateMachine ListenerState :=
      StateMachine.mk Init Next

    theorem level_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.kafka_listener_level_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : ListenerState) (hInit : Init s) :
      ListenerMonotoneInv s :=
      uint64_eq_le s.prev_level s.level hInit

    theorem next_preserves_inv (s : ListenerState) (s' : ListenerState)
      (_hInv : ListenerMonotoneInv s) (hNext : Next s s') :
      ListenerMonotoneInv s' :=
      Exists.elim hNext (fun (proposed_level : UInt64) (hEq : s' = upgradeAction proposed_level s) =>
        Eq.mpr
          (congrArg (fun (st : ListenerState) => ListenerMonotoneInv st) hEq)
          (level_ge_prev s.level proposed_level))

    theorem listener_monotone_always :
      Satisfies (Runs Spec) (Always (Lift ListenerMonotoneInv)) :=
      invariantSatisfies Spec ListenerMonotoneInv init_establishes_inv next_preserves_inv

    end TlaSealedListener
    end Kafka
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def kafka_listener_code_allows_isl (code : UInt64) : Bool :=
      decide (code = 1)
}
