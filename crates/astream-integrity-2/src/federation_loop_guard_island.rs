// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `federation_loop_guard.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `federation_loop_guard.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def fed_hop_clamp (cand_hops : UInt64) (max_hops : UInt64) : UInt64 :=
      if cand_hops < max_hops then cand_hops else max_hops

    def fed_seq_advance (cur_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_seq < cand_seq then cand_seq else cur_seq

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Federation Hop Guard Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaFederationHopGuard
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

    structure FederationHopState where
      hop_count : UInt64
      max_hops : UInt64
      forward_seq : UInt64
      prev_seq : UInt64

    def FederationHopGuardInv (s : FederationHopState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.hop_count) (UInt64.toNat s.max_hops))
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.forward_seq))

    def Init (max_hops : UInt64) (s : FederationHopState) : Prop :=
      And
        (And (s.hop_count = 0) (s.max_hops = max_hops))
        (And (s.forward_seq = 0) (s.prev_seq = 0))

    def forwardStep (cand_hops : UInt64) (cand_seq : UInt64) (s : FederationHopState) : FederationHopState :=
      FederationHopState.mk
        (_root_.fed_hop_clamp cand_hops s.max_hops)
        s.max_hops
        (_root_.fed_seq_advance s.forward_seq cand_seq)
        s.forward_seq

    def Next (s : FederationHopState) (s' : FederationHopState) : Prop :=
      ∃ (cand_hops : UInt64), ∃ (cand_seq : UInt64),
        s' = forwardStep cand_hops cand_seq s

    def Spec (max_hops : UInt64) : StateMachine FederationHopState :=
      StateMachine.mk (Init max_hops) Next

    theorem hop_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.fed_hop_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem seq_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.fed_seq_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_hops : UInt64) (s : FederationHopState)
      (hInit : Init max_hops s) :
      FederationHopGuardInv s :=
      And.intro
        (eq_zero_le s.hop_count s.max_hops (And.left (And.left hInit)))
        (eq_zero_le s.prev_seq s.forward_seq (And.right (And.right hInit)))

    theorem next_preserves_inv (s : FederationHopState) (s' : FederationHopState)
      (_hInv : FederationHopGuardInv s) (hNext : Next s s') :
      FederationHopGuardInv s' :=
      Exists.elim hNext (fun (ch : UInt64) (hRest : ∃ (cs : UInt64), s' = forwardStep ch cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = forwardStep ch cs s) =>
          Eq.mpr
            (congrArg (fun (st : FederationHopState) => FederationHopGuardInv st) hEq)
            (And.intro
              (hop_clamp_le ch s.max_hops)
              (seq_monotone s.forward_seq cs))))

    theorem federation_hop_guard_safety_always (max_hops : UInt64) :
      Satisfies (Spec max_hops) (Always (Lift FederationHopGuardInv)) :=
      invariantSatisfies (Spec max_hops) FederationHopGuardInv (init_establishes_inv max_hops) next_preserves_inv

    end TlaFederationHopGuard
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def fed_hops_within_cap_isl (hops : UInt64) (max_hops : UInt64) : Bool :=
      decide (hops <= max_hops)
}
