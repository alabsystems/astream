// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `pty_child.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `pty_child.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `islands/pty_child_twins.rs` of the functions it
// compiles from Clean.
clean {
    -- Clean-origin (I5) payload length clamp.
    def pty_child_clamp_len (len : UInt64) (cap : UInt64) : UInt64 :=
      if len < cap then len else cap

    namespace Astream
    namespace Host
    namespace TlaPtyChild

    def pty_child_payload_nonempty_isl (len : UInt64) : Bool :=
      decide (len > 0)

    theorem pty_child_clamp_len_bounded : forall (len : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.pty_child_clamp_len len cap)) (UInt64.toNat cap) :=
      fun len cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => len))) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun h => Nat.le_of_lt h)

    end TlaPtyChild
    end Host
    end Astream
}
