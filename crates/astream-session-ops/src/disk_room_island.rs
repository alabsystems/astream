// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `disk_room.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `disk_room.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def disk_free_mb_clamp (free_mb : UInt64) (max_mb : UInt64) : UInt64 :=
      if free_mb < max_mb then free_mb else max_mb

    def disk_reclaimed_advance (prev_mb : UInt64) (cand_mb : UInt64) : UInt64 :=
      if prev_mb < cand_mb then cand_mb else prev_mb

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Disk Room Watchdog Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaDiskRoomWatchdog

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

    structure DiskRoomState where
      free_mb : UInt64
      max_volume_mb : UInt64
      reclaimed_mb : UInt64
      prev_reclaimed_mb : UInt64

    def DiskRoomInv (s : DiskRoomState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.free_mb) (UInt64.toNat s.max_volume_mb))
        (Nat.le (UInt64.toNat s.prev_reclaimed_mb) (UInt64.toNat s.reclaimed_mb))

    def Init (s : DiskRoomState) : Prop :=
      And
        (s.free_mb = 0)
        (And (s.reclaimed_mb = 0) (s.prev_reclaimed_mb = 0))

    def diskStep (raw_free : UInt64) (cand_reclaimed : UInt64) (s : DiskRoomState) : DiskRoomState :=
      DiskRoomState.mk
        (_root_.disk_free_mb_clamp raw_free s.max_volume_mb)
        s.max_volume_mb
        (_root_.disk_reclaimed_advance s.reclaimed_mb cand_reclaimed)
        s.reclaimed_mb

    def Next (s : DiskRoomState) (s' : DiskRoomState) : Prop :=
      ∃ (raw_free : UInt64), ∃ (cand_reclaimed : UInt64),
        s' = diskStep raw_free cand_reclaimed s

    def Spec : StateMachine DiskRoomState :=
      StateMachine.mk Init Next

    theorem free_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.disk_free_mb_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem reclaimed_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.disk_reclaimed_advance prev cand)) :=
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

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : DiskRoomState) (hInit : Init s) :
      DiskRoomInv s :=
      And.intro
        (zero_le_cap s.free_mb s.max_volume_mb (And.left hInit))
        (eq_zero_le
          s.prev_reclaimed_mb
          s.reclaimed_mb
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : DiskRoomState) (s' : DiskRoomState)
      (_hInv : DiskRoomInv s) (hNext : Next s s') :
      DiskRoomInv s' :=
      Exists.elim hNext (fun (rf : UInt64) (hRest : ∃ (cr : UInt64), s' = diskStep rf cr s) =>
        Exists.elim hRest (fun (cr : UInt64) (hEq : s' = diskStep rf cr s) =>
          Eq.mpr
            (congrArg (fun (st : DiskRoomState) => DiskRoomInv st) hEq)
            (And.intro
              (free_le_max rf s.max_volume_mb)
              (reclaimed_monotone s.reclaimed_mb cr))))

    theorem disk_room_safety_always :
      Satisfies (Runs Spec) (Always (Lift DiskRoomInv)) :=
      invariantSatisfies Spec DiskRoomInv init_establishes_inv next_preserves_inv

    end TlaDiskRoomWatchdog
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def disk_has_room_isl (free_mb : UInt64) (room_floor_mb : UInt64) : Bool :=
      decide (room_floor_mb ≤ free_mb)
}
