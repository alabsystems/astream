// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `seccomp_child.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `seccomp_child.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
clean {
    -- Clean-origin (I5) read-buffer byte clamp.
    def seccomp_child_clamp_read (got : UInt64) (cap : UInt64) : UInt64 :=
      if got < cap then got else cap

    namespace Astream
    namespace Host
    namespace TlaSeccompChild

    def seccomp_child_digest_len_valid_isl (len : UInt64) : Bool :=
      decide (len = 8)

    theorem seccomp_child_clamp_read_bounded : forall (got : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.seccomp_child_clamp_read got cap)) (UInt64.toNat cap) :=
      fun got cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt got cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => got))) (UInt64.toNat cap))
        (instDecidableUInt64Lt got cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun h => Nat.le_of_lt h)

    end TlaSeccompChild
    end Host
    end Astream
}
