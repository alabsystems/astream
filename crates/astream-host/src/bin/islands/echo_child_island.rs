// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `echo_child.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `echo_child.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `islands/echo_child_twins.rs` of the functions it
// compiles from Clean.
clean {
    -- Clean-origin (I5) monotone line counter advance.
    def echo_child_advance_lines (lines : UInt64) (next : UInt64) : UInt64 :=
      if lines < next then next else lines

    namespace Astream
    namespace Host
    namespace TlaEchoChild

    def echo_child_is_quit_len_isl (len : UInt64) : Bool :=
      decide (len == 4)

    theorem echo_child_advance_lines_ge_lines : forall (lines : UInt64) (next : UInt64),
        Nat.le (UInt64.toNat lines) (UInt64.toNat (_root_.echo_child_advance_lines lines next)) :=
      fun lines next => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt lines next)) =>
          Nat.le (UInt64.toNat lines) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => lines) (fun _ => next))))
        (instDecidableUInt64Lt lines next)
        (fun _ => Nat.le.refl (UInt64.toNat lines))
        (fun h => Nat.le_of_lt h)

    end TlaEchoChild
    end Host
    end Astream
}
