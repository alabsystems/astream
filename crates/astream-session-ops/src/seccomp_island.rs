// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `seccomp.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `seccomp.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def bpf_pc_advance (cur_pc : UInt64) (proposed_pc : UInt64) : UInt64 :=
      if cur_pc < proposed_pc then proposed_pc else cur_pc

    def bpf_insn_clamp (insn_count : UInt64) (max_insns : UInt64) : UInt64 :=
      if insn_count < max_insns then insn_count else max_insns

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Sandbox BPF Filter Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaSandboxFilter

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

    structure BpfVmState where
      prev_pc : UInt64
      pc : UInt64
      prog_len : UInt64
      max_insns : UInt64

    def BpfFilterSafetyInv (s : BpfVmState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_pc) (UInt64.toNat s.pc))
        (Nat.le (UInt64.toNat s.prog_len) (UInt64.toNat s.max_insns))

    def Init (s : BpfVmState) : Prop :=
      And
        (s.prev_pc = s.pc)
        (Nat.le (UInt64.toNat s.prog_len) (UInt64.toNat s.max_insns))

    def stepInsn (target_pc : UInt64) (raw_len : UInt64) (s : BpfVmState) : BpfVmState :=
      BpfVmState.mk
        s.pc
        (_root_.bpf_pc_advance s.pc target_pc)
        (_root_.bpf_insn_clamp raw_len s.max_insns)
        s.max_insns

    def Next (s : BpfVmState) (s' : BpfVmState) : Prop :=
      ∃ (target_pc : UInt64), ∃ (raw_len : UInt64),
        s' = stepInsn target_pc raw_len s

    def Spec : StateMachine BpfVmState :=
      StateMachine.mk Init Next

    theorem pc_ge_prev : forall (cur : UInt64) (target : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.bpf_pc_advance cur target)) :=
      fun cur target => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur target)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => target))))
        (instDecidableUInt64Lt cur target)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem len_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.bpf_insn_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : BpfVmState) (hInit : Init s) :
      BpfFilterSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_pc s.pc (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : BpfVmState) (s' : BpfVmState)
      (_hInv : BpfFilterSafetyInv s) (hNext : Next s s') :
      BpfFilterSafetyInv s' :=
      Exists.elim hNext (fun (tpc : UInt64) (hRest : ∃ (rlen : UInt64), s' = stepInsn tpc rlen s) =>
        Exists.elim hRest (fun (rlen : UInt64) (hEq : s' = stepInsn tpc rlen s) =>
          Eq.mpr
            (congrArg (fun (st : BpfVmState) => BpfFilterSafetyInv st) hEq)
            (And.intro
              (pc_ge_prev s.pc tpc)
              (len_le_max rlen s.max_insns))))

    theorem bpf_filter_safety_always :
      Satisfies (Runs Spec) (Always (Lift BpfFilterSafetyInv)) :=
      invariantSatisfies Spec BpfFilterSafetyInv init_establishes_inv next_preserves_inv

    end TlaSandboxFilter
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def bpf_target_in_bounds_isl (target_pc : USize) (prog_len : USize) : Bool :=
      decide (target_pc < prog_len)
}
