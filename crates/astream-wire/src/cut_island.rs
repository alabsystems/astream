// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `cut.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `cut.rs` mounts this file under
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

    -- TLA+ transition system with stutter-permissive `Init /\ [][Next]_vars`
    -- semantics (`Runs`).
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

    -- Constructive TLA+ inductive-invariant rule:
    --   Init => I  /\  (I /\ [Next]_vars => I')  |-  Spec => []I
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
    -- 2. Clean-Origin Transition Functions (compiled directly to Rust MIR by
    --    `trustc` via `clean_origin_mir` + `Faithful` kernel gate, and called
    --    directly by `CausalCut::advance`, `CausalCut::heal`, and
    --    `CausalCut::meet` below — zero duplicate Rust fn definitions!)
    -- ========================================================================

    -- Minimal causal-closure frontier advance (`max(cur, req)`).
    def heal_frontier_monotone (cur : UInt64) (req : UInt64) : UInt64 :=
      if cur < req then req else cur

    -- Pointwise meet (`min(a, b)`), used by `CausalCut::meet`.
    def meet_frontier_monotone (a : UInt64) (b : UInt64) : UInt64 :=
      if a < b then a else b

    -- 4-parameter Clean-Origin (`I5`) Chandy-Lamport causal gate (`select.le` over 4 parameters):
    -- selects `eff_healed` iff `cause_req <= cause_cut`, else preserves `eff_cur`.
    def causal_gate_frontier (cause_req : UInt64) (cause_cut : UInt64) (eff_healed : UInt64) (eff_cur : UInt64) : UInt64 :=
      if cause_req <= cause_cut then eff_healed else eff_cur

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Chandy-Lamport Causal Cut & Lattice
    --    Directly over the Clean-Origin `UInt64` transition functions!
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaCausalCut

    open Trust.Temporal

    -- Whether a stream frontier `upto` includes offset `at_off` (`at_off <= upto`).
    def frontier_includes_isl (upto : UInt64) (at_off : UInt64) : Bool :=
      decide (at_off <= upto)

    -- Compound 4-parameter Chandy-Lamport step kernel composing `causal_gate_frontier`
    -- and `heal_frontier_monotone`.
    def causal_step_frontier_isl (cause_cut : UInt64) (cause_req : UInt64) (eff_cur : UInt64) (eff_cand : UInt64) : UInt64 :=
      _root_.causal_gate_frontier cause_req cause_cut (_root_.heal_frontier_monotone eff_cur eff_cand) eff_cur

    -- Term proof that `heal_frontier_monotone cur req >= cur` (monotonicity of `advance`/`heal`).
    theorem heal_frontier_ge_cur : forall (cur : UInt64) (req : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.heal_frontier_monotone cur req)) :=
      fun cur req => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => req))))
        (instDecidableUInt64Lt cur req)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    -- Term proof that the 4-parameter `causal_step_frontier_isl` is monotone (`>= eff_cur`).
    theorem causal_step_frontier_ge_cur : forall (cause_cut : UInt64) (cause_req : UInt64) (eff_cur : UInt64) (eff_cand : UInt64),
        Nat.le (UInt64.toNat eff_cur) (UInt64.toNat (causal_step_frontier_isl cause_cut cause_req eff_cur eff_cand)) :=
      fun cause_cut cause_req eff_cur eff_cand => Decidable.casesOn
        (motive := fun (d : Decidable (LE.le cause_req cause_cut)) =>
          Nat.le (UInt64.toNat eff_cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d
            (fun _ => eff_cur)
            (fun _ => _root_.heal_frontier_monotone eff_cur eff_cand))))
        (instDecidableUInt64Le cause_req cause_cut)
        (fun _ => Nat.le.refl (UInt64.toNat eff_cur))
        (fun _ => heal_frontier_ge_cur eff_cur eff_cand)

    -- Tactic proof that `heal_frontier_monotone cur req >= req` (healing satisfies the causal edge).
    theorem heal_frontier_ge_req (cur req : UInt64) :
        req <= _root_.heal_frontier_monotone cur req := by
      unfold _root_.heal_frontier_monotone
      split <;> omega

    -- Tactic proof that `meet_frontier_monotone a b <= a` (glb lower-bounds left operand).
    theorem meet_frontier_le_left (a b : UInt64) :
        _root_.meet_frontier_monotone a b <= a := by
      unfold _root_.meet_frontier_monotone
      split <;> omega

    -- Term proof that `meet_frontier_monotone a b <= b` (glb lower-bounds right operand).
    theorem meet_frontier_le_right : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat (_root_.meet_frontier_monotone a b)) (UInt64.toNat b) :=
      fun a b => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt a b)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => b) (fun _ => a))) (UInt64.toNat b))
        (instDecidableUInt64Lt a b)
        (fun _ => Nat.le.refl (UInt64.toNat b))
        (fun h => Nat.le_of_lt h)

    -- Tactic proof that `meet_frontier_monotone a b` is the greatest lower bound:
    -- `c <= a -> c <= b -> c <= meet_frontier_monotone a b`.
    theorem meet_frontier_glb (c a b : UInt64)
        (hA : Nat.le (UInt64.toNat c) (UInt64.toNat a))
        (hB : Nat.le (UInt64.toNat c) (UInt64.toNat b)) :
        Nat.le (UInt64.toNat c) (UInt64.toNat (_root_.meet_frontier_monotone a b)) :=
      @Decidable.casesOn (LT.lt a b)
        (fun (d : Decidable (LT.lt a b)) =>
          Nat.le (UInt64.toNat c)
            (UInt64.toNat (@ite UInt64 (LT.lt a b) d a b)))
        (instDecidableUInt64Lt a b)
        (fun _ => hB)
        (fun _ => hA)

    -- State variables of the 2-stream Chandy-Lamport causal cut protocol over `UInt64`:
    --   causeFrontier  : current cut frontier on source stream `C[src]`
    --   effectFrontier : current cut frontier on destination stream `C[dst]`
    --   causeOffset    : offset of causal parent event `k` on `src`
    --   effectOffset   : offset of caused effect event `m` on `dst`
    structure CutState where
      causeFrontier  : UInt64
      effectFrontier : UInt64
      causeOffset    : UInt64
      effectOffset   : UInt64

    -- Chandy-Lamport safety invariant over `UInt64` offsets:
    --   effectOffset <= effectFrontier  =>  causeOffset <= causeFrontier
    def ChandyLamportInv (s : CutState) : Prop :=
      Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat s.effectFrontier) →
        Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat s.causeFrontier)

    -- TLA+ Init predicate: cut begins in any consistent initial state (e.g. when
    -- `causeFrontier` already covers `causeOffset`, or before `effectOffset` is admitted).
    def Init (s : CutState) : Prop :=
      ChandyLamportInv s

    -- TLA+ Action 1: AdvanceCause — advancing the source stream frontier via the
    -- Clean-origin `heal_frontier_monotone` transition (`CausalCut::advance`).
    def AdvanceCause (req : UInt64) (s sNext : CutState) : Prop :=
      sNext.causeFrontier = _root_.heal_frontier_monotone s.causeFrontier req ∧
      sNext.effectFrontier = s.effectFrontier ∧
      sNext.causeOffset = s.causeOffset ∧
      sNext.effectOffset = s.effectOffset

    -- TLA+ Action 2: AdvanceEffectConsistent — advancing the destination stream
    -- frontier via `heal_frontier_monotone` when the causal parent is admitted in `causeFrontier`.
    def AdvanceEffectConsistent (req : UInt64) (s sNext : CutState) : Prop :=
      sNext.effectFrontier = _root_.heal_frontier_monotone s.effectFrontier req ∧
      (Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat sNext.effectFrontier) →
        Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat s.causeFrontier)) ∧
      sNext.causeFrontier = s.causeFrontier ∧
      sNext.causeOffset = s.causeOffset ∧
      sNext.effectOffset = s.effectOffset

    -- TLA+ Action 3: HealCut — advancing `causeFrontier` via the Clean-origin
    -- `heal_frontier_monotone s.causeFrontier s.causeOffset` transition (`CausalCut::heal`).
    def HealCut (s sNext : CutState) : Prop :=
      sNext.causeFrontier = _root_.heal_frontier_monotone s.causeFrontier s.causeOffset ∧
      sNext.effectFrontier = s.effectFrontier ∧
      sNext.causeOffset = s.causeOffset ∧
      sNext.effectOffset = s.effectOffset

    -- TLA+ Action 4: MeetCut — taking the greatest-lower-bound meet (`CausalCut::meet`)
    -- with another consistent cut `(otherCause, otherEffect)` via the Clean-origin
    -- `_root_.meet_frontier_monotone` function.
    def MeetCut (otherCause otherEffect : UInt64) (s sNext : CutState) : Prop :=
      (Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat otherEffect) →
        Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat otherCause)) ∧
      sNext.causeFrontier = _root_.meet_frontier_monotone s.causeFrontier otherCause ∧
      sNext.effectFrontier = _root_.meet_frontier_monotone s.effectFrontier otherEffect ∧
      sNext.causeOffset = s.causeOffset ∧
      sNext.effectOffset = s.effectOffset

    -- TLA+ Next relation: disjunction of concrete Clean-origin Rust transition functions.
    def Next (s sNext : CutState) : Prop :=
      (∃ req : UInt64, AdvanceCause req s sNext) ∨
        ((∃ req : UInt64, AdvanceEffectConsistent req s sNext) ∨
          (HealCut s sNext ∨ (∃ oc : UInt64, ∃ oe : UInt64, MeetCut oc oe s sNext)))

    def Spec : StateMachine CutState :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : CutState) (hInit : Init s) :
        ChandyLamportInv s :=
      hInit

    -- Proof of `AdvanceCause` preservation directly invokes `heal_frontier_ge_cur` on
    -- `heal_frontier_monotone s.causeFrontier req`!
    theorem advanceCause_preserves_inv (req : UInt64) (s sNext : CutState)
        (hInv : ChandyLamportInv s) (hAct : AdvanceCause req s sNext) :
        ChandyLamportInv sNext :=
      fun hEffNext =>
        let hEff : Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat s.effectFrontier) :=
          Eq.mp (congrArg (fun y => Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat y)) hAct.2.1)
            (Eq.mp (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.effectFrontier)) hAct.2.2.2) hEffNext)
        let hCause : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat s.causeFrontier) := hInv hEff
        let hMono : Nat.le (UInt64.toNat s.causeFrontier) (UInt64.toNat (_root_.heal_frontier_monotone s.causeFrontier req)) :=
          heal_frontier_ge_cur s.causeFrontier req
        let hMonoNext : Nat.le (UInt64.toNat s.causeFrontier) (UInt64.toNat sNext.causeFrontier) :=
          Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.causeFrontier) (UInt64.toNat y)) hAct.1) hMono
        let hCauseNext : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat sNext.causeFrontier) :=
          Nat.le_trans hCause hMonoNext
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.causeFrontier)) hAct.2.2.1) hCauseNext

    theorem advanceEffect_preserves_inv (req : UInt64) (s sNext : CutState)
        (hAct : AdvanceEffectConsistent req s sNext) :
        ChandyLamportInv sNext :=
      fun hEffNext =>
        let hEff : Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat sNext.effectFrontier) :=
          Eq.mp (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.effectFrontier)) hAct.2.2.2.2) hEffNext
        let hCause : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat s.causeFrontier) := hAct.2.1 hEff
        let hCauseNext : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat sNext.causeFrontier) :=
          Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat y)) hAct.2.2.1) hCause
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.causeFrontier)) hAct.2.2.2.1) hCauseNext

    -- Proof of `HealCut` directly invokes `heal_frontier_ge_req` on
    -- `heal_frontier_monotone s.causeFrontier s.causeOffset`, establishing Chandy-Lamport
    -- consistency unconditionally even from an inconsistent pre-state!
    theorem healCut_establishes_inv (s sNext : CutState) (hAct : HealCut s sNext) :
        ChandyLamportInv sNext :=
      fun _ =>
        let hHealed : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat (_root_.heal_frontier_monotone s.causeFrontier s.causeOffset)) :=
          heal_frontier_ge_req s.causeFrontier s.causeOffset
        let hHealedNext : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat sNext.causeFrontier) :=
          Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat y)) hAct.1) hHealed
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.causeFrontier)) hAct.2.2.1) hHealedNext

    -- Proof of `MeetCut` preservation directly invokes `meet_frontier_le_left`,
    -- `meet_frontier_le_right`, and `meet_frontier_glb` on `_root_.meet_frontier_monotone`!
    theorem meetCut_preserves_inv (oc oe : UInt64) (s sNext : CutState)
        (hInv : ChandyLamportInv s) (hAct : MeetCut oc oe s sNext) :
        ChandyLamportInv sNext :=
      fun hEffNext =>
        let hEff1 : Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat sNext.effectFrontier) :=
          Eq.mp (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.effectFrontier)) hAct.2.2.2.2) hEffNext
        let hEffMeet : Nat.le (UInt64.toNat s.effectOffset)
            (UInt64.toNat (_root_.meet_frontier_monotone s.effectFrontier oe)) :=
          Eq.mp (congrArg (fun y => Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat y)) hAct.2.2.1) hEff1
        let hEffLeft : Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat s.effectFrontier) :=
          Nat.le_trans hEffMeet (meet_frontier_le_left s.effectFrontier oe)
        let hEffRight : Nat.le (UInt64.toNat s.effectOffset) (UInt64.toNat oe) :=
          Nat.le_trans hEffMeet (meet_frontier_le_right s.effectFrontier oe)
        let hCauseLeft : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat s.causeFrontier) :=
          hInv hEffLeft
        let hCauseRight : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat oc) :=
          hAct.1 hEffRight
        let hCauseMeet : Nat.le (UInt64.toNat s.causeOffset)
            (UInt64.toNat (_root_.meet_frontier_monotone s.causeFrontier oc)) :=
          meet_frontier_glb s.causeOffset s.causeFrontier oc hCauseLeft hCauseRight
        let hCauseNext : Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat sNext.causeFrontier) :=
          Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.causeOffset) (UInt64.toNat y)) hAct.2.1) hCauseMeet
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.causeFrontier)) hAct.2.2.2.1) hCauseNext

    theorem next_preserves_inv (s sNext : CutState)
        (hInv : ChandyLamportInv s) (hNext : Next s sNext) :
        ChandyLamportInv sNext :=
      Or.elim hNext
        (fun hExC =>
          Exists.elim hExC (fun req hAdvC => advanceCause_preserves_inv req s sNext hInv hAdvC))
        (fun hRest =>
          Or.elim hRest
            (fun hExE =>
              Exists.elim hExE (fun req hAdvE => advanceEffect_preserves_inv req s sNext hAdvE))
            (fun hRest2 =>
              Or.elim hRest2
                (fun hHeal => healCut_establishes_inv s sNext hHeal)
                (fun hExOc =>
                  Exists.elim hExOc (fun oc hExOe =>
                    Exists.elim hExOe (fun oe hMeet =>
                      meetCut_preserves_inv oc oe s sNext hInv hMeet)))))

    -- Full TLA+ Temporal Safety Theorem: `Spec ⊨ □ (Lift ChandyLamportInv)`
    theorem spec_satisfies_chandy_lamport :
        Spec ⊨ □ (Lift ChandyLamportInv) :=
      invariantSatisfies Spec ChandyLamportInv
        init_establishes_inv
        next_preserves_inv

    end TlaCausalCut
    end Wire
    end Astream
}
