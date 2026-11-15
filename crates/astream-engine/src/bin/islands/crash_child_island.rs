// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `crash_child.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `crash_child.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `islands/crash_child_twins.rs` of the functions it
// compiles from Clean.
clean {
    -- Clean-origin (I5) monotone append sequence advance.
    def crash_child_advance_seq (seq : UInt64) (next : UInt64) : UInt64 :=
      if seq < next then next else seq

    namespace Astream
    namespace Engine
    namespace TlaCrashChild

    def crash_child_can_append_isl (seq : UInt64) : Bool :=
      decide (seq < 20000)

    theorem crash_child_advance_seq_ge_seq : forall (seq : UInt64) (next : UInt64),
        Nat.le (UInt64.toNat seq) (UInt64.toNat (_root_.crash_child_advance_seq seq next)) :=
      fun seq next => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt seq next)) =>
          Nat.le (UInt64.toNat seq) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => seq) (fun _ => next))))
        (instDecidableUInt64Lt seq next)
        (fun _ => Nat.le.refl (UInt64.toNat seq))
        (fun h => Nat.le_of_lt h)

    end TlaCrashChild
    end Engine
    end Astream
}
