// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `contract_fn!`: a contracted fn, written once. Under a Trust compiler (`cfg(clean_islands)`,
//! which build.rs sets through `clean_islands.rs`) the fn carries its native `ensures` clause,
//! so its proof is about the code every build runs; every other compiler gets the plain fn and
//! never parses the clause, which no stock rustc can. Each astream crate mounts this file
//! (`#[macro_use] #[path = ...] mod contract_fn;`), so the rule has one spelling.

#[cfg(clean_islands)]
macro_rules! contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret
            $($clauses)+
        { $($body)* }
    };
    (
        $(#[$meta:meta])*
        $vis:vis const fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis const fn $name($($arg: $arg_ty),*) -> $ret
            $($clauses)+
        { $($body)* }
    };
}

#[cfg(not(clean_islands))]
macro_rules! contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret { $($body)* }
    };
    (
        $(#[$meta:meta])*
        $vis:vis const fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis const fn $name($($arg: $arg_ty),*) -> $ret { $($body)* }
    };
}
