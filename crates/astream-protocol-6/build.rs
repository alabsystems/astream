// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#[path = "../astream-wire/clean_islands.rs"]
mod clean_islands;

fn main() {
    clean_islands::emit();
}
