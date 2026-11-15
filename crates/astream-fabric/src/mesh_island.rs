// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `mesh.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `mesh.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def mesh_hop_below_max_code (hop : UInt64) (max_hops : UInt64) : UInt64 :=
      if hop < max_hops then 1 else 0

    def mesh_origin_gate_code (not_self_origin : UInt64) (hop_ok : UInt64) : UInt64 :=
      if not_self_origin < 1 then 0 else hop_ok

    def mesh_hop_clamp (hop : UInt64) (max_hops : UInt64) : UInt64 :=
      if hop < max_hops then hop else max_hops

    def mesh_epoch_advance (cur_epoch : UInt64) (proposed_epoch : UInt64) : UInt64 :=
      if cur_epoch < proposed_epoch then proposed_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Federation Mesh Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaFederationMesh

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

    def mesh_route_admissible_code_isl (not_self_origin : UInt64) (hop : UInt64) (max_hops : UInt64) : UInt64 :=
      _root_.mesh_origin_gate_code not_self_origin (_root_.mesh_hop_below_max_code hop max_hops)

    structure MeshPeerState where
      prev_epoch : UInt64
      epoch : UInt64
      hop : UInt64
      max_hops : UInt64

    def MeshSafetyInv (s : MeshPeerState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.epoch))
        (Nat.le (UInt64.toNat s.hop) (UInt64.toNat s.max_hops))

    def Init (s : MeshPeerState) : Prop :=
      And
        (s.prev_epoch = s.epoch)
        (Nat.le (UInt64.toNat s.hop) (UInt64.toNat s.max_hops))

    def announceStep (proposed_epoch : UInt64) (raw_hop : UInt64) (s : MeshPeerState) : MeshPeerState :=
      MeshPeerState.mk
        s.epoch
        (_root_.mesh_epoch_advance s.epoch proposed_epoch)
        (_root_.mesh_hop_clamp raw_hop s.max_hops)
        s.max_hops

    def Next (s : MeshPeerState) (s' : MeshPeerState) : Prop :=
      ∃ (proposed_epoch : UInt64), ∃ (raw_hop : UInt64),
        s' = announceStep proposed_epoch raw_hop s

    def Spec : StateMachine MeshPeerState :=
      StateMachine.mk Init Next

    theorem epoch_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.mesh_epoch_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem hop_le_max : forall (raw_hop : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.mesh_hop_clamp raw_hop cap)) (UInt64.toNat cap) :=
      fun raw_hop cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw_hop cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw_hop))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw_hop cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : MeshPeerState) (hInit : Init s) :
      MeshSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_epoch s.epoch (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : MeshPeerState) (s' : MeshPeerState)
      (_hInv : MeshSafetyInv s) (hNext : Next s s') :
      MeshSafetyInv s' :=
      Exists.elim hNext (fun (proposed_epoch : UInt64) (hRest : ∃ (raw_hop : UInt64), s' = announceStep proposed_epoch raw_hop s) =>
        Exists.elim hRest (fun (raw_hop : UInt64) (hEq : s' = announceStep proposed_epoch raw_hop s) =>
          Eq.mpr
            (congrArg (fun (st : MeshPeerState) => MeshSafetyInv st) hEq)
            (And.intro
              (epoch_ge_prev s.epoch proposed_epoch)
              (hop_le_max raw_hop s.max_hops))))

    theorem mesh_safety_always :
      Satisfies Spec (Always (Lift MeshSafetyInv)) :=
      invariantSatisfies Spec MeshSafetyInv init_establishes_inv next_preserves_inv

    end TlaFederationMesh
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def mesh_code_is_admissible_isl (code : UInt64) : Bool :=
      decide (code = 1)
}
