// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `flood_child.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `flood_child.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `islands/flood_child_twins.rs` of the functions it
// compiles from Clean.
clean {
    -- Clean-origin (I5) monotone burst step advance.
    def flood_child_advance_step (step : UInt64) (next : UInt64) : UInt64 :=
      if step < next then next else step

    namespace Astream
    namespace Host
    namespace TlaFloodChild

    def flood_child_within_burst_isl (step : UInt64) : Bool :=
      decide (step < 8)

    theorem flood_child_advance_step_ge_step : forall (step : UInt64) (next : UInt64),
        Nat.le (UInt64.toNat step) (UInt64.toNat (_root_.flood_child_advance_step step next)) :=
      fun step next => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt step next)) =>
          Nat.le (UInt64.toNat step) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => step) (fun _ => next))))
        (instDecidableUInt64Lt step next)
        (fun _ => Nat.le.refl (UInt64.toNat step))
        (fun h => Nat.le_of_lt h)

    end TlaFloodChild
    end Host
    end Astream
}
