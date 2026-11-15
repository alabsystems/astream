// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `cfg(clean_islands)` for this crate's Clean islands, asked of the compiler.

#[path = "../astream-wire/clean_islands.rs"]
mod clean_islands;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    clean_islands::emit();
}
