// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for Kitty Graphics Protocol (`APC G ... ST`) chunked assembly and
// bounded image memory arena (`Astream.Term.TlaKittyGraphicsBudget`), mounted under
// `cfg(clean_islands)` in `kitty_graphics_arena.rs`. Proves `chunkBytes <= imageCap` and
// `arenaBytes <= arenaCap` across multi-chunk image uploads, placements, and evictions.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def kitty_chunk_bytes_clamp (proposed_bytes : UInt64) (image_cap : UInt64) : UInt64 :=
      if proposed_bytes < image_cap then proposed_bytes else image_cap

    def kitty_arena_bytes_clamp (proposed_arena : UInt64) (arena_cap : UInt64) : UInt64 :=
      if proposed_arena < arena_cap then proposed_arena else arena_cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaKittyGraphicsBudget)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaKittyGraphicsBudget

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaKittyGraphicsBudget.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaKittyGraphicsBudget.Always

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

    -- ========================================================================
    -- 3. Kitty Graphics Chunk & Arena Budget State Machine
    -- ========================================================================

    structure KittyArenaState where
      chunkBytes : UInt64
      imageCap   : UInt64
      arenaBytes : UInt64
      arenaCap   : UInt64

    def KittyArenaInv (s : KittyArenaState) : Prop :=
      Nat.le (UInt64.toNat s.chunkBytes) (UInt64.toNat s.imageCap) ∧
      Nat.le (UInt64.toNat s.arenaBytes) (UInt64.toNat s.arenaCap)

    def Init (imageCap arenaCap : UInt64) (s : KittyArenaState) : Prop :=
      s.chunkBytes = (0 : UInt64) ∧
      s.imageCap = imageCap ∧
      s.arenaBytes = (0 : UInt64) ∧
      s.arenaCap = arenaCap

    def AppendChunk (proposedChunk : UInt64) (s sNext : KittyArenaState) : Prop :=
      sNext.chunkBytes = _root_.kitty_chunk_bytes_clamp proposedChunk s.imageCap ∧
      sNext.imageCap = s.imageCap ∧
      sNext.arenaBytes = s.arenaBytes ∧
      sNext.arenaCap = s.arenaCap

    def CommitOrEvictArena (proposedArena : UInt64) (s sNext : KittyArenaState) : Prop :=
      sNext.chunkBytes = (0 : UInt64) ∧
      sNext.imageCap = s.imageCap ∧
      sNext.arenaBytes = _root_.kitty_arena_bytes_clamp proposedArena s.arenaCap ∧
      sNext.arenaCap = s.arenaCap

    def Next (s sNext : KittyArenaState) : Prop :=
      (∃ pc : UInt64, AppendChunk pc s sNext) ∨
      (∃ pa : UInt64, CommitOrEvictArena pa s sNext)

    def Spec (imageCap arenaCap : UInt64) : StateMachine KittyArenaState :=
      StateMachine.mk (Init imageCap arenaCap) Next

    theorem chunk_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kitty_chunk_bytes_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem arena_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kitty_arena_bytes_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (imageCap arenaCap : UInt64) (s : KittyArenaState)
        (hInit : Init imageCap arenaCap s) : KittyArenaInv s :=
      And.intro
        (zero_u64_le s.chunkBytes s.imageCap hInit.1)
        (zero_u64_le s.arenaBytes s.arenaCap hInit.2.2.1)

    theorem appendChunk_preserves_inv (pc : UInt64) (s sNext : KittyArenaState)
        (hInv : KittyArenaInv s) (hAct : AppendChunk pc s sNext) : KittyArenaInv sNext :=
      let hC1 : Nat.le (UInt64.toNat sNext.chunkBytes) (UInt64.toNat s.imageCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.imageCap)) hAct.1)
          (chunk_clamp_le pc s.imageCap)
      let hC2 : Nat.le (UInt64.toNat sNext.chunkBytes) (UInt64.toNat sNext.imageCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.chunkBytes) (UInt64.toNat y)) hAct.2.1)
          hC1
      let hA1 : Nat.le (UInt64.toNat sNext.arenaBytes) (UInt64.toNat s.arenaCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.arenaCap)) hAct.2.2.1)
          hInv.2
      let hA2 : Nat.le (UInt64.toNat sNext.arenaBytes) (UInt64.toNat sNext.arenaCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.arenaBytes) (UInt64.toNat y)) hAct.2.2.2)
          hA1
      And.intro hC2 hA2

    theorem commitOrEvict_preserves_inv (pa : UInt64) (s sNext : KittyArenaState)
        (hAct : CommitOrEvictArena pa s sNext) : KittyArenaInv sNext :=
      let hC : Nat.le (UInt64.toNat sNext.chunkBytes) (UInt64.toNat sNext.imageCap) :=
        zero_u64_le sNext.chunkBytes sNext.imageCap hAct.1
      let hA1 : Nat.le (UInt64.toNat sNext.arenaBytes) (UInt64.toNat s.arenaCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.arenaCap)) hAct.2.2.1)
          (arena_clamp_le pa s.arenaCap)
      let hA2 : Nat.le (UInt64.toNat sNext.arenaBytes) (UInt64.toNat sNext.arenaCap) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.arenaBytes) (UInt64.toNat y)) hAct.2.2.2)
          hA1
      And.intro hC hA2

    theorem next_preserves_inv (s sNext : KittyArenaState)
        (hInv : KittyArenaInv s) (hNext : Next s sNext) : KittyArenaInv sNext :=
      Or.elim hNext
        (fun hExC => Exists.elim hExC (fun pc hC => appendChunk_preserves_inv pc s sNext hInv hC))
        (fun hExA => Exists.elim hExA (fun pa hA => commitOrEvict_preserves_inv pa s sNext hA))

    theorem spec_satisfies_kitty_arena_safety (imageCap arenaCap : UInt64) :
        (Spec imageCap arenaCap) ⊨ □ (Lift KittyArenaInv) :=
      invariantSatisfies (Spec imageCap arenaCap) KittyArenaInv
        (init_establishes_inv imageCap arenaCap)
        next_preserves_inv

    end TlaKittyGraphicsBudget
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def kitty_fits_budget_isl (bytes : UInt64) (cap : UInt64) : Bool :=
      decide (bytes ≤ cap)
}
