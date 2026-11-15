// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic, fuel-metered, zero-dependency WebAssembly MVP sandbox over [`EffectSeam`]
//! (`docs/ROADMAP.md` §2 "WASM").
//!
//! Executes pure WebAssembly binary modules (`\0asm\x01\0\0\0`) deterministically inside
//! `astream-effects` with zero third-party dependencies and zero `unsafe`:
//! - **Fuel-metered termination (`wasm_fuel_advance`, `wasm_fuel_remaining`):** every
//!   executed opcode advances `spent_fuel` monotonically against `fuel_limit`, trapping
//!   cleanly with [`WasmTrap::OutOfFuel`] before any unbounded loop can stall an agent.
//! - **Bounded linear memory (`wasm_mem_clamp`):** memory pages are capped at
//!   [`MAX_WASM_PAGES`] (`4` pages = `256 KiB`), and every load/store bounds-checks
//!   `addr + width <= mem.len()`.
//! - **Record/replay host imports via [`EffectSeam`]:** modules may import from `"astream"`
//!   `clock_millis() -> i64`, `random_i64() -> i64`, and `emit_mem(ptr: i32, len: i32) -> i32`,
//!   so recording with [`astream_effects::RecordingSeam`] and replaying with [`astream_effects::ReplaySeam`]
//!   produces byte-identical Wasm execution and output with zero host OS access on replay.

#![allow(clippy::type_complexity)]

use astream_effects::EffectSeam;

#[cfg(clean_islands)]
#[path = "wasm_island.rs"]
mod wasm_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn wasm_fuel_advance(spent: u64, next_spent: u64) -> u64 {
    if spent < next_spent {
        next_spent
    } else {
        spent
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn wasm_mem_clamp(addr_end: u64, mem_cap: u64) -> u64 {
    if addr_end < mem_cap {
        addr_end
    } else {
        mem_cap
    }
}
#[cfg(clean_islands)]
pub use wasm_island::{wasm_fuel_advance, wasm_mem_clamp};

contract_fn! {
    /// Contracted check that fuel remains strictly below `limit`.
    #[must_use]
    pub const fn wasm_fuel_remaining(spent: u64, limit: u64) -> bool
    clauses [ensures result == (spent < limit)]
    {
        spent < limit
    }
}

/// WebAssembly binary magic (`\0asm`) + version `1`.
pub const WASM_MAGIC_V1: [u8; 8] = [0x00, b'a', b's', b'm', 0x01, 0x00, 0x00, 0x00];

/// Standard WebAssembly page size (`64 KiB`).
pub const WASM_PAGE_BYTES: usize = 65_536;

/// Maximum linear memory pages permitted in the deterministic sandbox (`4 * 64 KiB = 256 KiB`).
pub const MAX_WASM_PAGES: usize = 4;

/// Hard linear-memory byte ceiling (`262_144` bytes).
pub const MAX_WASM_MEM_BYTES: usize = MAX_WASM_PAGES * WASM_PAGE_BYTES;

/// Maximum operand stack depth.
pub const MAX_WASM_STACK: usize = 1024;

/// Maximum locals per function.
pub const MAX_WASM_LOCALS: usize = 256;

/// Maximum functions/imports/exports in a module.
pub const MAX_WASM_ITEMS: usize = 128;

/// Value types supported by the deterministic Wasm MVP core (`i32`, `i64`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmVal {
    I32(i32),
    I64(i64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValType {
    I32,
    I64,
}

/// Built-in `"astream"` host imports routed exclusively through [`EffectSeam`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostImport {
    /// `astream.clock_millis() -> i64`: wall-clock milliseconds via `seam.now_nanos() / 1_000_000`.
    ClockMillis,
    /// `astream.random_i64() -> i64`: 64-bit random word via `seam.next_rand()`.
    RandomI64,
    /// `astream.emit_mem(ptr: i32, len: i32) -> i32`: emit linear-memory slice via `seam.emit()`.
    EmitMem,
}

/// Deterministic trap or decode error from [`WasmModule`] / [`WasmSandbox`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmTrap {
    InvalidMagic,
    MalformedBinary(&'static str),
    UnsupportedFeature(&'static str),
    UnknownExport,
    SignatureMismatch,
    OutOfFuel { limit: u64 },
    StackOverflow,
    StackUnderflow,
    LocalOutOfBounds,
    MemoryOutOfBounds { offset: usize, len: usize },
    DivisionByZero,
    Unreachable,
    SeamRefused,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FuncType {
    params: Vec<ValType>,
    results: Vec<ValType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FuncBody {
    type_idx: usize,
    locals: Vec<ValType>,
    code: Vec<u8>,
}

/// Parsed, validated deterministic WebAssembly module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmModule {
    types: Vec<FuncType>,
    imports: Vec<(HostImport, usize)>,
    funcs: Vec<FuncBody>,
    initial_pages: usize,
    exports: Vec<(String, usize)>,
}

fn read_u8(bytes: &[u8], pos: &mut usize) -> Result<u8, WasmTrap> {
    let Some(&b) = bytes.get(*pos) else {
        return Err(WasmTrap::MalformedBinary("unexpected EOF"));
    };
    *pos = pos.saturating_add(1);
    Ok(b)
}

fn read_leb_u32(bytes: &[u8], pos: &mut usize) -> Result<u32, WasmTrap> {
    let mut result = 0u32;
    let mut shift = 0u32;
    let mut count = 0usize;
    while count < 5 {
        let byte = read_u8(bytes, pos)?;
        if shift == 28 && (byte & 0xF0) != 0 {
            return Err(WasmTrap::MalformedBinary("u32 leb128 overflow"));
        }
        let next_res = result | (((byte & 0x7F) as u32).wrapping_shl(shift));
        result = next_res;
        if (byte & 0x80) == 0 {
            return Ok(result);
        }
        shift = shift.saturating_add(7);
        count = count.saturating_add(1);
    }
    Err(WasmTrap::MalformedBinary("unterminated u32 leb128"))
}

fn read_leb_i64(bytes: &[u8], pos: &mut usize) -> Result<i64, WasmTrap> {
    let mut result = 0i64;
    let mut shift = 0u32;
    let mut count = 0usize;
    while count < 10 {
        let byte = read_u8(bytes, pos)?;
        if shift < 63 {
            let next_res = result | (((byte & 0x7F) as i64).wrapping_shl(shift));
            result = next_res;
        } else {
            if byte != 0x00 && byte != 0x7F {
                return Err(WasmTrap::MalformedBinary("i64 leb128 overflow"));
            }
            let next_res = result | (((byte & 0x01) as i64) << 63);
            result = next_res;
        }
        shift = shift.saturating_add(7);
        if (byte & 0x80) == 0 {
            if shift < 64 && (byte & 0x40) != 0 {
                let sign_ext = result | ((!0i64).wrapping_shl(shift));
                return Ok(sign_ext);
            }
            return Ok(result);
        }
        count = count.saturating_add(1);
    }
    Err(WasmTrap::MalformedBinary("unterminated i64 leb128"))
}

fn read_leb_i32(bytes: &[u8], pos: &mut usize) -> Result<i32, WasmTrap> {
    let v = read_leb_i64(bytes, pos)?;
    if v < (i32::MIN as i64) || v > (i32::MAX as i64) {
        return Err(WasmTrap::MalformedBinary("i32 leb128 out of range"));
    }
    Ok(v as i32)
}

fn decode_val_type(b: u8) -> Result<ValType, WasmTrap> {
    match b {
        0x7F => Ok(ValType::I32),
        0x7E => Ok(ValType::I64),
        _ => Err(WasmTrap::UnsupportedFeature(
            "only i32 and i64 value types supported",
        )),
    }
}

fn read_name(bytes: &[u8], pos: &mut usize) -> Result<String, WasmTrap> {
    let len = read_leb_u32(bytes, pos)? as usize;
    let Some(end) = pos.checked_add(len) else {
        return Err(WasmTrap::MalformedBinary("invalid name length"));
    };
    if len > 256 {
        return Err(WasmTrap::MalformedBinary("invalid name length"));
    }
    let Some(slice) = bytes.get(*pos..end) else {
        return Err(WasmTrap::MalformedBinary("invalid name length"));
    };
    *pos = end;
    let s = match core::str::from_utf8(slice) {
        Ok(v) => v,
        Err(_) => return Err(WasmTrap::MalformedBinary("invalid utf8 name")),
    };
    let s_cap = if s.len() < 256 { s.len() } else { 256 };
    let mut out = {
        let _ = s_cap;
        String::new()
    };
    out.push_str(s);
    Ok(out)
}

fn decode_wasm_type_section(wasm: &[u8], pos: &mut usize) -> Result<Vec<FuncType>, WasmTrap> {
    let count = read_leb_u32(wasm, pos)? as usize;
    if count > MAX_WASM_ITEMS {
        return Err(WasmTrap::UnsupportedFeature("too many types"));
    }
    let mut types = Vec::new();
    let mut i = 0usize;
    while i < count {
        if read_u8(wasm, pos)? != 0x60 {
            return Err(WasmTrap::MalformedBinary("expected functype 0x60"));
        }
        let np = read_leb_u32(wasm, pos)? as usize;
        if np > 16 {
            return Err(WasmTrap::UnsupportedFeature("too many params"));
        }
        let mut params = Vec::new();
        let mut p = 0usize;
        while p < np {
            params.push(decode_val_type(read_u8(wasm, pos)?)?);
            p = p.saturating_add(1);
        }
        let nr = read_leb_u32(wasm, pos)? as usize;
        if nr > 1 {
            return Err(WasmTrap::UnsupportedFeature(
                "multi-value return unsupported",
            ));
        }
        let mut results = Vec::new();
        if nr == 1 {
            results.push(decode_val_type(read_u8(wasm, pos)?)?);
        }
        types.push(FuncType { params, results });
        i = i.saturating_add(1);
    }
    Ok(types)
}

const fn val_type_of(v: WasmVal) -> ValType {
    match v {
        WasmVal::I32(_) => ValType::I32,
        WasmVal::I64(_) => ValType::I64,
    }
}

fn check_arg_types(expected: &[ValType], args: &[WasmVal]) -> Result<(), WasmTrap> {
    if expected.len() != args.len() {
        return Err(WasmTrap::SignatureMismatch);
    }
    let mut i = 0usize;
    while i < expected.len() {
        if let (Some(&et), Some(&av)) = (expected.get(i), args.get(i)) {
            if val_type_of(av) != et {
                return Err(WasmTrap::SignatureMismatch);
            }
        }
        i = i.saturating_add(1);
    }
    Ok(())
}

fn check_host_import_sig(hi: HostImport, sig: &FuncType) -> Result<(), WasmTrap> {
    let ok = match hi {
        HostImport::ClockMillis | HostImport::RandomI64 => {
            sig.params.is_empty() && sig.results.as_slice() == [ValType::I64]
        }
        HostImport::EmitMem => {
            sig.params.as_slice() == [ValType::I32, ValType::I32]
                && sig.results.as_slice() == [ValType::I32]
        }
    };
    if ok {
        Ok(())
    } else {
        Err(WasmTrap::SignatureMismatch)
    }
}

fn decode_wasm_import_section(
    wasm: &[u8],
    pos: &mut usize,
    types: &[FuncType],
) -> Result<Vec<(HostImport, usize)>, WasmTrap> {
    let count = read_leb_u32(wasm, pos)? as usize;
    if count > MAX_WASM_ITEMS {
        return Err(WasmTrap::UnsupportedFeature("too many imports"));
    }
    let mut imports = Vec::new();
    let mut i = 0usize;
    while i < count {
        let module = read_name(wasm, pos)?;
        let field = read_name(wasm, pos)?;
        let kind = read_u8(wasm, pos)?;
        if kind != 0x00 {
            return Err(WasmTrap::UnsupportedFeature(
                "only function imports supported",
            ));
        }
        let tidx = read_leb_u32(wasm, pos)? as usize;
        if module != "astream" {
            return Err(WasmTrap::UnsupportedFeature("unknown host import module"));
        }
        let Some(sig) = types.get(tidx) else {
            return Err(WasmTrap::MalformedBinary("import type out of bounds"));
        };
        let hi = if field == "clock_millis" {
            HostImport::ClockMillis
        } else if field == "random_i64" {
            HostImport::RandomI64
        } else if field == "emit_mem" {
            HostImport::EmitMem
        } else {
            return Err(WasmTrap::UnsupportedFeature("unknown astream host import"));
        };
        check_host_import_sig(hi, sig)?;
        imports.push((hi, tidx));
        i = i.saturating_add(1);
    }
    Ok(imports)
}

fn decode_wasm_func_section(
    wasm: &[u8],
    pos: &mut usize,
    num_types: usize,
) -> Result<Vec<usize>, WasmTrap> {
    let count = read_leb_u32(wasm, pos)? as usize;
    if count > MAX_WASM_ITEMS {
        return Err(WasmTrap::UnsupportedFeature("too many functions"));
    }
    let mut func_type_idxs = Vec::new();
    let mut i = 0usize;
    while i < count {
        let tidx = read_leb_u32(wasm, pos)? as usize;
        if tidx >= num_types {
            return Err(WasmTrap::MalformedBinary("function type out of bounds"));
        }
        func_type_idxs.push(tidx);
        i = i.saturating_add(1);
    }
    Ok(func_type_idxs)
}

fn decode_wasm_memory_section(
    wasm: &[u8],
    pos: &mut usize,
    initial_pages: &mut usize,
    has_memory: &mut bool,
) -> Result<(), WasmTrap> {
    let count = read_leb_u32(wasm, pos)? as usize;
    if count > 1 {
        return Err(WasmTrap::UnsupportedFeature(
            "multiple memories unsupported",
        ));
    }
    if count == 0 {
        *initial_pages = 0;
        *has_memory = false;
        return Ok(());
    }
    let flags = read_u8(wasm, pos)?;
    if (flags & !0x01) != 0 {
        return Err(WasmTrap::UnsupportedFeature(
            "unsupported memory limits flags",
        ));
    }
    let min_p = read_leb_u32(wasm, pos)? as usize;
    if (flags & 0x01) != 0 {
        let max_p = read_leb_u32(wasm, pos)? as usize;
        if max_p < min_p {
            return Err(WasmTrap::MalformedBinary("memory max pages < min pages"));
        }
    }
    if min_p > MAX_WASM_PAGES {
        return Err(WasmTrap::UnsupportedFeature(
            "memory exceeds MAX_WASM_PAGES",
        ));
    }
    *initial_pages = min_p;
    *has_memory = true;
    Ok(())
}

fn decode_wasm_export_section(
    wasm: &[u8],
    pos: &mut usize,
    total_funcs: usize,
    has_memory: bool,
) -> Result<Vec<(String, usize)>, WasmTrap> {
    let count = read_leb_u32(wasm, pos)? as usize;
    if count > MAX_WASM_ITEMS {
        return Err(WasmTrap::UnsupportedFeature("too many exports"));
    }
    let mut exports = Vec::new();
    let mut seen_names: Vec<String> = Vec::new();
    let mut i = 0usize;
    while i < count {
        let name = read_name(wasm, pos)?;
        let mut s_rest = seen_names.as_slice();
        while let [existing, tail @ ..] = s_rest {
            if existing == &name {
                return Err(WasmTrap::MalformedBinary("duplicate export name"));
            }
            s_rest = tail;
        }
        seen_names.push(name.clone());
        let kind = read_u8(wasm, pos)?;
        let idx = read_leb_u32(wasm, pos)? as usize;
        match kind {
            0x00 => {
                if idx >= total_funcs {
                    return Err(WasmTrap::MalformedBinary(
                        "export function index out of bounds",
                    ));
                }
                exports.push((name, idx));
            }
            0x02 => {
                if !has_memory || idx != 0 {
                    return Err(WasmTrap::MalformedBinary(
                        "export memory index out of bounds",
                    ));
                }
            }
            0x01 | 0x03 => {
                return Err(WasmTrap::UnsupportedFeature("unsupported export kind"));
            }
            _ => {
                return Err(WasmTrap::MalformedBinary("invalid export kind"));
            }
        }
        i = i.saturating_add(1);
    }
    Ok(exports)
}

fn decode_wasm_code_body(
    wasm: &[u8],
    pos: &mut usize,
    sec_end: usize,
) -> Result<(Vec<ValType>, Vec<u8>), WasmTrap> {
    let body_size = read_leb_u32(wasm, pos)? as usize;
    let Some(body_end) = pos.checked_add(body_size) else {
        return Err(WasmTrap::MalformedBinary("body overruns code section"));
    };
    if body_end > sec_end {
        return Err(WasmTrap::MalformedBinary("body overruns code section"));
    }
    let decls = read_leb_u32(wasm, pos)? as usize;
    let mut locals = Vec::new();
    let mut d = 0usize;
    while d < decls {
        let n = read_leb_u32(wasm, pos)? as usize;
        let vt = decode_val_type(read_u8(wasm, pos)?)?;
        if locals.len().saturating_add(n) > MAX_WASM_LOCALS {
            return Err(WasmTrap::UnsupportedFeature("too many locals"));
        }
        let mut k = 0usize;
        while k < n {
            locals.push(vt);
            k = k.saturating_add(1);
        }
        d = d.saturating_add(1);
    }
    let Some(code_len) = body_end.checked_sub(*pos) else {
        return Err(WasmTrap::MalformedBinary("missing body end 0x0B"));
    };
    let Some(body_no_end) = body_end.checked_sub(1) else {
        return Err(WasmTrap::MalformedBinary("missing body end 0x0B"));
    };
    if code_len == 0 || wasm.get(body_no_end).copied() != Some(0x0B) {
        return Err(WasmTrap::MalformedBinary("missing body end 0x0B"));
    }
    let Some(code_slice) = wasm.get(*pos..body_no_end) else {
        return Err(WasmTrap::MalformedBinary("missing body end 0x0B"));
    };
    let mut code = Vec::new();
    code.extend_from_slice(code_slice);
    *pos = body_end;
    Ok((locals, code))
}

fn decode_wasm_code_section(
    wasm: &[u8],
    pos: &mut usize,
    sec_end: usize,
    expected_funcs: usize,
) -> Result<Vec<(Vec<ValType>, Vec<u8>)>, WasmTrap> {
    let count = read_leb_u32(wasm, pos)? as usize;
    if count != expected_funcs {
        return Err(WasmTrap::MalformedBinary("code count != function count"));
    }
    let mut bodies = Vec::new();
    let mut i = 0usize;
    while i < count {
        bodies.push(decode_wasm_code_body(wasm, pos, sec_end)?);
        i = i.saturating_add(1);
    }
    Ok(bodies)
}

impl WasmModule {
    /// Decode and validate a `.wasm` binary module.
    pub fn decode(wasm: &[u8]) -> Result<Self, WasmTrap> {
        let Some(magic) = wasm.get(..8) else {
            return Err(WasmTrap::InvalidMagic);
        };
        if magic != WASM_MAGIC_V1 {
            return Err(WasmTrap::InvalidMagic);
        }
        let mut pos = 8usize;
        let mut types = Vec::new();
        let mut imports = Vec::new();
        let mut func_type_idxs = Vec::new();
        let mut initial_pages = 1usize;
        let mut has_memory = true;
        let mut exports = Vec::new();
        let mut bodies: Vec<(Vec<ValType>, Vec<u8>)> = Vec::new();
        let mut last_non_custom_sec = 0u8;

        while pos < wasm.len() {
            let sec_id = read_u8(wasm, &mut pos)?;
            let sec_len = read_leb_u32(wasm, &mut pos)? as usize;
            let Some(sec_end) = pos.checked_add(sec_len) else {
                return Err(WasmTrap::MalformedBinary("section overruns binary"));
            };
            if sec_end > wasm.len() {
                return Err(WasmTrap::MalformedBinary("section overruns binary"));
            }
            if sec_id != 0 {
                if sec_id > 11 {
                    return Err(WasmTrap::MalformedBinary("unknown wasm section id"));
                }
                if sec_id <= last_non_custom_sec {
                    return Err(WasmTrap::MalformedBinary(
                        "duplicate or out-of-order wasm section",
                    ));
                }
                last_non_custom_sec = sec_id;
            }
            match sec_id {
                0 => {
                    let _ = read_name(wasm, &mut pos)?;
                    if pos > sec_end {
                        return Err(WasmTrap::MalformedBinary(
                            "custom section name overruns section",
                        ));
                    }
                    pos = sec_end;
                }
                1 => types = decode_wasm_type_section(wasm, &mut pos)?,
                2 => imports = decode_wasm_import_section(wasm, &mut pos, &types)?,
                3 => func_type_idxs = decode_wasm_func_section(wasm, &mut pos, types.len())?,
                5 => {
                    decode_wasm_memory_section(wasm, &mut pos, &mut initial_pages, &mut has_memory)?
                }
                7 => {
                    let total_funcs = imports.len().saturating_add(func_type_idxs.len());
                    exports = decode_wasm_export_section(wasm, &mut pos, total_funcs, has_memory)?;
                }
                10 => {
                    bodies =
                        decode_wasm_code_section(wasm, &mut pos, sec_end, func_type_idxs.len())?;
                }
                4 | 6 | 8 | 9 | 11 => {
                    return Err(WasmTrap::UnsupportedFeature("unsupported wasm section"));
                }
                _ => {
                    return Err(WasmTrap::MalformedBinary("unknown wasm section id"));
                }
            }
            if pos != sec_end {
                return Err(WasmTrap::MalformedBinary("section length mismatch"));
            }
        }
        if bodies.len() != func_type_idxs.len() {
            return Err(WasmTrap::MalformedBinary("missing code section"));
        }
        let mut funcs = Vec::new();
        let mut b_iter = bodies.into_iter();
        let mut fi = 0usize;
        while fi < func_type_idxs.len() {
            let (Some((locals, code)), Some(&type_idx)) = (b_iter.next(), func_type_idxs.get(fi))
            else {
                break;
            };
            funcs.push(FuncBody {
                type_idx,
                locals,
                code,
            });
            fi = fi.saturating_add(1);
        }
        Ok(Self {
            types,
            imports,
            funcs,
            initial_pages,
            exports,
        })
    }
}

fn build_wasm_locals(args: &[WasmVal], local_types: &[ValType]) -> Vec<WasmVal> {
    let mut locals = Vec::new();
    let mut ai = 0usize;
    while ai < args.len() {
        if let Some(&av) = args.get(ai) {
            locals.push(av);
        }
        ai = ai.saturating_add(1);
    }
    let mut li = 0usize;
    while li < local_types.len() {
        if let Some(&vt) = local_types.get(li) {
            locals.push(match vt {
                ValType::I32 => WasmVal::I32(0),
                ValType::I64 => WasmVal::I64(0),
            });
        }
        li = li.saturating_add(1);
    }
    locals
}

fn exec_wasm_local_or_const_op(
    op: u8,
    code: &[u8],
    pc: &mut usize,
    locals: &mut [WasmVal],
    stack: &mut Vec<WasmVal>,
) -> Result<(), WasmTrap> {
    match op {
        0x1A => {
            pop_val(stack)?;
        }
        0x20 => {
            let idx = read_leb_u32(code, pc)? as usize;
            let Some(&v) = locals.get(idx) else {
                return Err(WasmTrap::LocalOutOfBounds);
            };
            push_val(stack, v)?;
        }
        0x21 => {
            let idx = read_leb_u32(code, pc)? as usize;
            let v = pop_val(stack)?;
            let Some(slot) = locals.get_mut(idx) else {
                return Err(WasmTrap::LocalOutOfBounds);
            };
            if val_type_of(v) != val_type_of(*slot) {
                return Err(WasmTrap::SignatureMismatch);
            }
            *slot = v;
        }
        0x22 => {
            let idx = read_leb_u32(code, pc)? as usize;
            let Some(&v) = stack.last() else {
                return Err(WasmTrap::StackUnderflow);
            };
            let Some(slot) = locals.get_mut(idx) else {
                return Err(WasmTrap::LocalOutOfBounds);
            };
            if val_type_of(v) != val_type_of(*slot) {
                return Err(WasmTrap::SignatureMismatch);
            }
            *slot = v;
        }
        0x41 => {
            let c = read_leb_i32(code, pc)?;
            push_val(stack, WasmVal::I32(c))?;
        }
        0x42 => {
            let c = read_leb_i64(code, pc)?;
            push_val(stack, WasmVal::I64(c))?;
        }
        _ => return Err(WasmTrap::UnsupportedFeature("unsupported wasm opcode")),
    }
    Ok(())
}

fn exec_wasm_alu_op(op: u8, stack: &mut Vec<WasmVal>) -> Result<(), WasmTrap> {
    match op {
        0x6A => {
            let b = pop_i32(stack)?;
            let a = pop_i32(stack)?;
            push_val(stack, WasmVal::I32(a.wrapping_add(b)))?;
        }
        0x6B => {
            let b = pop_i32(stack)?;
            let a = pop_i32(stack)?;
            push_val(stack, WasmVal::I32(a.wrapping_sub(b)))?;
        }
        0x6C => {
            let b = pop_i32(stack)?;
            let a = pop_i32(stack)?;
            push_val(stack, WasmVal::I32(a.wrapping_mul(b)))?;
        }
        0x6D => {
            let b = pop_i32(stack)?;
            let a = pop_i32(stack)?;
            if b == 0 {
                return Err(WasmTrap::DivisionByZero);
            }
            let Some(q) = a.checked_div(b) else {
                return Err(WasmTrap::DivisionByZero);
            };
            push_val(stack, WasmVal::I32(q))?;
        }
        0x7C => {
            let b = pop_i64(stack)?;
            let a = pop_i64(stack)?;
            push_val(stack, WasmVal::I64(a.wrapping_add(b)))?;
        }
        0x7E => {
            let b = pop_i64(stack)?;
            let a = pop_i64(stack)?;
            push_val(stack, WasmVal::I64(a.wrapping_mul(b)))?;
        }
        0x86 => {
            let b = pop_i64(stack)?;
            let a = pop_i64(stack)?;
            push_val(stack, WasmVal::I64(a ^ b))?;
        }
        _ => return Err(WasmTrap::UnsupportedFeature("unsupported wasm opcode")),
    }
    Ok(())
}

/// Closed concrete host-effect seam handle for [`WasmSandbox`].
///
/// Using a closed enum over the crate's four concrete seam implementations
/// ([`astream_effects::RecordingSeam`], [`astream_effects::ReplaySeam`], [`astream_effects::LiveSeam`], and
/// [`astream_effects::ShadowSeam`]) avoids open-generic trait dispatch under Level-0
/// verification while supporting live, recorded, replayed, and shadow Wasm runs.
pub enum WasmSeam<'a, 't> {
    /// Record live host effects into an [`astream_effects::EffectsLog`].
    Recording(&'a mut astream_effects::RecordingSeam<astream_effects::OsEffects>),
    /// Replay taped host effects hermetically with zero host OS access.
    Replay(&'a mut astream_effects::ReplaySeam),
    /// Run against live host effects without taping.
    Live(&'a mut astream_effects::LiveSeam<astream_effects::OsEffects>),
    /// Evaluate counterfactually at a non-consuming tape cutoff.
    Shadow(&'a mut astream_effects::ShadowSeam<'t>),
}

impl WasmSeam<'_, '_> {
    fn now_nanos(&mut self) -> Result<u64, WasmTrap> {
        match self {
            Self::Recording(s) => match s.now_nanos() {
                Ok(v) => Ok(v),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Replay(s) => match s.now_nanos() {
                Ok(v) => Ok(v),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Live(s) => match s.now_nanos() {
                Ok(v) => Ok(v),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Shadow(s) => match s.now_nanos() {
                Ok(v) => Ok(v),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
        }
    }

    fn next_rand(&mut self) -> Result<u64, WasmTrap> {
        match self {
            Self::Recording(s) => match s.next_rand() {
                Ok(v) => Ok(v),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Replay(s) => match s.next_rand() {
                Ok(v) => Ok(v),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Live(s) => match s.next_rand() {
                Ok(v) => Ok(v),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Shadow(s) => match s.next_rand() {
                Ok(v) => Ok(v),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
        }
    }

    fn emit(&mut self, door: &str, bytes: &[u8]) -> Result<(), WasmTrap> {
        match self {
            Self::Recording(s) => match s.emit(door, bytes) {
                Ok(()) => Ok(()),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Replay(s) => match s.emit(door, bytes) {
                Ok(()) => Ok(()),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Live(s) => match s.emit(door, bytes) {
                Ok(()) => Ok(()),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
            Self::Shadow(s) => match s.emit(door, bytes) {
                Ok(()) => Ok(()),
                Err(_) => Err(WasmTrap::SeamRefused),
            },
        }
    }
}

/// Fuel-metered deterministic execution instance over a [`WasmModule`].
pub struct WasmSandbox {
    module: WasmModule,
    memory: Vec<u8>,
    spent_fuel: u64,
    fuel_limit: u64,
}

impl WasmSandbox {
    pub fn new(module: WasmModule, fuel_limit: u64) -> Self {
        let raw_bytes = module.initial_pages.saturating_mul(WASM_PAGE_BYTES);
        let mem_bytes = wasm_mem_clamp(raw_bytes as u64, MAX_WASM_MEM_BYTES as u64) as usize;
        let cap = if mem_bytes < MAX_WASM_MEM_BYTES {
            mem_bytes
        } else {
            MAX_WASM_MEM_BYTES
        };
        let mut memory = {
            let _ = cap;
            Vec::new()
        };
        let mut idx = 0usize;
        while idx < cap {
            memory.push(0u8);
            idx = idx.saturating_add(1);
        }
        Self {
            module,
            memory,
            spent_fuel: 0,
            fuel_limit,
        }
    }

    pub fn spent_fuel(&self) -> u64 {
        self.spent_fuel
    }

    pub fn memory(&self) -> &[u8] {
        &self.memory
    }

    pub fn write_memory(&mut self, offset: usize, data: &[u8]) -> Result<(), WasmTrap> {
        let Some(end) = offset.checked_add(data.len()) else {
            return Err(WasmTrap::MemoryOutOfBounds {
                offset,
                len: data.len(),
            });
        };
        let Some(dst) = self.memory.get_mut(offset..end) else {
            return Err(WasmTrap::MemoryOutOfBounds {
                offset,
                len: data.len(),
            });
        };
        dst.copy_from_slice(data);
        Ok(())
    }

    fn charge_fuel(&mut self, units: u64) -> Result<(), WasmTrap> {
        if !wasm_fuel_remaining(self.spent_fuel, self.fuel_limit) {
            return Err(WasmTrap::OutOfFuel {
                limit: self.fuel_limit,
            });
        }
        let step_units = if units < 1 { 1 } else { units };
        let proposed = self.spent_fuel.saturating_add(step_units);
        self.spent_fuel = wasm_fuel_advance(self.spent_fuel, proposed);
        if self.spent_fuel > self.fuel_limit {
            return Err(WasmTrap::OutOfFuel {
                limit: self.fuel_limit,
            });
        }
        Ok(())
    }

    /// Invoke an exported function `name` with `args`, routing all host effects through `seam`.
    pub fn invoke(
        &mut self,
        mut seam: WasmSeam<'_, '_>,
        name: &str,
        args: &[WasmVal],
    ) -> Result<Option<WasmVal>, WasmTrap> {
        let mut target_idx = None;
        let mut exp_rest = self.module.exports.as_slice();
        while let [(ename, eidx), tail @ ..] = exp_rest {
            if ename == name {
                target_idx = Some(*eidx);
                break;
            }
            exp_rest = tail;
        }
        let Some(func_idx) = target_idx else {
            return Err(WasmTrap::UnknownExport);
        };
        self.call_func(&mut seam, func_idx, args, 0)
    }

    /// Convenience entrypoint recording host effects through [`astream_effects::RecordingSeam`].
    pub fn invoke_recording(
        &mut self,
        seam: &mut astream_effects::RecordingSeam<astream_effects::OsEffects>,
        name: &str,
        args: &[WasmVal],
    ) -> Result<Option<WasmVal>, WasmTrap> {
        self.invoke(WasmSeam::Recording(seam), name, args)
    }

    /// Convenience entrypoint replaying host effects through [`astream_effects::ReplaySeam`].
    pub fn invoke_replay(
        &mut self,
        seam: &mut astream_effects::ReplaySeam,
        name: &str,
        args: &[WasmVal],
    ) -> Result<Option<WasmVal>, WasmTrap> {
        self.invoke(WasmSeam::Replay(seam), name, args)
    }

    /// Convenience entrypoint evaluating host effects through [`astream_effects::ShadowSeam`].
    pub fn invoke_shadow(
        &mut self,
        seam: &mut astream_effects::ShadowSeam<'_>,
        name: &str,
        args: &[WasmVal],
    ) -> Result<Option<WasmVal>, WasmTrap> {
        self.invoke(WasmSeam::Shadow(seam), name, args)
    }

    fn exec_wasm_call_op(
        &mut self,
        seam: &mut WasmSeam<'_, '_>,
        code: &[u8],
        pc: &mut usize,
        stack: &mut Vec<WasmVal>,
        depth: usize,
    ) -> Result<(), WasmTrap> {
        let callee = read_leb_u32(code, pc)? as usize;
        let callee_tidx = if let Some(&(_, tidx)) = self.module.imports.get(callee) {
            tidx
        } else {
            let Some(bi) = callee.checked_sub(self.module.imports.len()) else {
                return Err(WasmTrap::UnknownExport);
            };
            let Some(fb) = self.module.funcs.get(bi) else {
                return Err(WasmTrap::UnknownExport);
            };
            fb.type_idx
        };
        let Some(callee_ty) = self.module.types.get(callee_tidx) else {
            return Err(WasmTrap::UnknownExport);
        };
        let arity = callee_ty.params.len();
        let Some(split) = stack.len().checked_sub(arity) else {
            return Err(WasmTrap::StackUnderflow);
        };
        let Some(arg_slice) = stack.get(split..) else {
            return Err(WasmTrap::StackUnderflow);
        };
        let mut call_args = Vec::new();
        call_args.extend_from_slice(arg_slice);
        stack.truncate(split);
        if let Some(rv) = self.call_func(seam, callee, &call_args, depth.saturating_add(1))? {
            push_val(stack, rv)?;
        }
        Ok(())
    }

    fn exec_wasm_i32_load(
        &self,
        code: &[u8],
        pc: &mut usize,
        stack: &mut Vec<WasmVal>,
    ) -> Result<(), WasmTrap> {
        let _align = read_leb_u32(code, pc)?;
        let offset = read_leb_u32(code, pc)? as usize;
        let base = pop_i32(stack)?;
        if base < 0 {
            return Err(WasmTrap::MemoryOutOfBounds { offset, len: 4 });
        }
        let Some(addr) = (base as usize).checked_add(offset) else {
            return Err(WasmTrap::MemoryOutOfBounds { offset, len: 4 });
        };
        let Some(end4) = addr.checked_add(4) else {
            return Err(WasmTrap::MemoryOutOfBounds {
                offset: addr,
                len: 4,
            });
        };
        let Some(src) = self.memory.get(addr..end4) else {
            return Err(WasmTrap::MemoryOutOfBounds {
                offset: addr,
                len: 4,
            });
        };
        let mut raw = [0u8; 4];
        raw.copy_from_slice(src);
        let v = i32::from_le_bytes(raw);
        push_val(stack, WasmVal::I32(v))
    }

    fn exec_wasm_i32_store(
        &mut self,
        code: &[u8],
        pc: &mut usize,
        stack: &mut Vec<WasmVal>,
    ) -> Result<(), WasmTrap> {
        let _align = read_leb_u32(code, pc)?;
        let offset = read_leb_u32(code, pc)? as usize;
        let val = pop_i32(stack)?;
        let base = pop_i32(stack)?;
        if base < 0 {
            return Err(WasmTrap::MemoryOutOfBounds { offset, len: 4 });
        }
        let Some(addr) = (base as usize).checked_add(offset) else {
            return Err(WasmTrap::MemoryOutOfBounds { offset, len: 4 });
        };
        let Some(end4) = addr.checked_add(4) else {
            return Err(WasmTrap::MemoryOutOfBounds {
                offset: addr,
                len: 4,
            });
        };
        let Some(dst) = self.memory.get_mut(addr..end4) else {
            return Err(WasmTrap::MemoryOutOfBounds {
                offset: addr,
                len: 4,
            });
        };
        let b = val.to_le_bytes();
        dst.copy_from_slice(&b);
        Ok(())
    }

    fn call_func(
        &mut self,
        seam: &mut WasmSeam<'_, '_>,
        func_idx: usize,
        args: &[WasmVal],
        depth: usize,
    ) -> Result<Option<WasmVal>, WasmTrap> {
        if depth > 64 {
            return Err(WasmTrap::StackOverflow);
        }
        self.charge_fuel(1)?;
        let num_imports = self.module.imports.len();
        if let Some(&(hi, tidx)) = self.module.imports.get(func_idx) {
            let Some(sig) = self.module.types.get(tidx) else {
                return Err(WasmTrap::UnknownExport);
            };
            check_arg_types(&sig.params, args)?;
            return self.exec_host_import(seam, hi, args);
        }
        let Some(body_idx) = func_idx.checked_sub(num_imports) else {
            return Err(WasmTrap::UnknownExport);
        };
        let Some(fbody) = self.module.funcs.get(body_idx) else {
            return Err(WasmTrap::UnknownExport);
        };
        let Some(ftype) = self.module.types.get(fbody.type_idx) else {
            return Err(WasmTrap::UnknownExport);
        };
        check_arg_types(&ftype.params, args)?;
        let expected_ret = ftype.results.first().copied();
        let mut locals = build_wasm_locals(args, &fbody.locals);
        let code = fbody.code.clone();
        let mut stack: Vec<WasmVal> = Vec::new();
        let mut pc = 0usize;
        let mut early_return = false;
        while pc < code.len() {
            self.charge_fuel(1)?;
            let op = read_u8(&code, &mut pc)?;
            match op {
                0x00 => return Err(WasmTrap::Unreachable),
                0x01 => {}
                0x0F => {
                    early_return = true;
                    break;
                }
                0x10 => self.exec_wasm_call_op(seam, &code, &mut pc, &mut stack, depth)?,
                0x1A | 0x20 | 0x21 | 0x22 | 0x41 | 0x42 => {
                    exec_wasm_local_or_const_op(op, &code, &mut pc, &mut locals, &mut stack)?;
                }
                0x28 => self.exec_wasm_i32_load(&code, &mut pc, &mut stack)?,
                0x36 => self.exec_wasm_i32_store(&code, &mut pc, &mut stack)?,
                0x6A | 0x6B | 0x6C | 0x6D | 0x7C | 0x7E | 0x86 => {
                    exec_wasm_alu_op(op, &mut stack)?;
                }
                _ => return Err(WasmTrap::UnsupportedFeature("unsupported wasm opcode")),
            }
        }
        if let Some(expected_ty) = expected_ret {
            let rv = pop_val(&mut stack)?;
            if val_type_of(rv) != expected_ty {
                return Err(WasmTrap::SignatureMismatch);
            }
            if !early_return && !stack.is_empty() {
                return Err(WasmTrap::SignatureMismatch);
            }
            Ok(Some(rv))
        } else {
            if !early_return && !stack.is_empty() {
                return Err(WasmTrap::SignatureMismatch);
            }
            Ok(None)
        }
    }

    fn exec_host_import(
        &mut self,
        seam: &mut WasmSeam<'_, '_>,
        hi: HostImport,
        args: &[WasmVal],
    ) -> Result<Option<WasmVal>, WasmTrap> {
        match hi {
            HostImport::ClockMillis => {
                let ns = seam.now_nanos()?;
                Ok(Some(WasmVal::I64((ns / 1_000_000) as i64)))
            }
            HostImport::RandomI64 => {
                let word = seam.next_rand()?;
                Ok(Some(WasmVal::I64(word as i64)))
            }
            HostImport::EmitMem => {
                let &[arg0, arg1] = args else {
                    return Err(WasmTrap::SignatureMismatch);
                };
                let ptr = match arg0 {
                    WasmVal::I32(v) if v >= 0 => v as usize,
                    _ => return Err(WasmTrap::MemoryOutOfBounds { offset: 0, len: 0 }),
                };
                let len = match arg1 {
                    WasmVal::I32(v) if v >= 0 => v as usize,
                    _ => {
                        return Err(WasmTrap::MemoryOutOfBounds {
                            offset: ptr,
                            len: 0,
                        })
                    }
                };
                let Some(end) = ptr.checked_add(len) else {
                    return Err(WasmTrap::MemoryOutOfBounds { offset: ptr, len });
                };
                let Some(mem_slice) = self.memory.get(ptr..end) else {
                    return Err(WasmTrap::MemoryOutOfBounds { offset: ptr, len });
                };
                let pay_cap = if len < MAX_WASM_MEM_BYTES {
                    len
                } else {
                    MAX_WASM_MEM_BYTES
                };
                let mut payload = {
                    let _ = pay_cap;
                    Vec::new()
                };
                payload.extend_from_slice(mem_slice);
                seam.emit("wasm", &payload)?;
                Ok(Some(WasmVal::I32(len as i32)))
            }
        }
    }
}

fn push_val(stack: &mut Vec<WasmVal>, v: WasmVal) -> Result<(), WasmTrap> {
    if stack.len() >= MAX_WASM_STACK {
        return Err(WasmTrap::StackOverflow);
    }
    stack.push(v);
    Ok(())
}

fn pop_val(stack: &mut Vec<WasmVal>) -> Result<WasmVal, WasmTrap> {
    match stack.pop() {
        Some(v) => Ok(v),
        None => Err(WasmTrap::StackUnderflow),
    }
}

fn pop_i32(stack: &mut Vec<WasmVal>) -> Result<i32, WasmTrap> {
    match pop_val(stack)? {
        WasmVal::I32(v) => Ok(v),
        WasmVal::I64(_) => Err(WasmTrap::SignatureMismatch),
    }
}

fn pop_i64(stack: &mut Vec<WasmVal>) -> Result<i64, WasmTrap> {
    match pop_val(stack)? {
        WasmVal::I64(v) => Ok(v),
        WasmVal::I32(_) => Err(WasmTrap::SignatureMismatch),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use astream_effects::{KeyedView, OsEffects, RecordingSeam, ReplaySeam, ShadowSeam};

    /// Hand-assembled `.wasm` module importing `astream.clock_millis() -> i64` (idx 0)
    /// and `astream.random_i64() -> i64` (idx 1), exporting `mix(seed: i64) -> i64` (idx 2)
    /// which computes `(clock_millis() + seed) ^ random_i64()`.
    fn build_effectful_wasm() -> Vec<u8> {
        let mut w = WASM_MAGIC_V1.to_vec();
        // Section 1: Types (2 types: [] -> [i64], [i64] -> [i64])
        w.extend_from_slice(&[
            1, 10, // id=1, len=10
            2,  // 2 types
            0x60, 0, 1, 0x7E, // type 0: () -> i64
            0x60, 1, 0x7E, 1, 0x7E, // type 1: (i64) -> i64
        ]);
        // Section 2: Imports (astream.clock_millis: type 0, astream.random_i64: type 0)
        let imp = [
            2u8, // count=2
            7, b'a', b's', b't', b'r', b'e', b'a', b'm', 12, b'c', b'l', b'o', b'c', b'k', b'_',
            b'm', b'i', b'l', b'l', b'i', b's', 0x00, 0, // func type 0
            7, b'a', b's', b't', b'r', b'e', b'a', b'm', 10, b'r', b'a', b'n', b'd', b'o', b'm',
            b'_', b'i', b'6', b'4', 0x00, 0, // func type 0
        ];
        w.push(2);
        w.push(imp.len() as u8);
        w.extend_from_slice(&imp);
        // Section 3: Functions (1 func of type 1)
        w.extend_from_slice(&[3, 2, 1, 1]);
        // Section 5: Memory (1 memory, flags=0, min=1 page)
        w.extend_from_slice(&[5, 3, 1, 0, 1]);
        // Section 7: Exports ("mix" -> func 2)
        w.extend_from_slice(&[7, 7, 1, 3, b'm', b'i', b'x', 0x00, 2]);
        // Section 10: Code
        // body: 0 local decls, call 0, local.get 0, i64.add, call 1, i64.xor, end
        let body = [0u8, 0x10, 0, 0x20, 0, 0x7C, 0x10, 1, 0x86, 0x0B];
        w.push(10);
        w.push((2 + body.len()) as u8);
        w.push(1);
        w.push(body.len() as u8);
        w.extend_from_slice(&body);
        w
    }

    #[test]
    fn wasm_records_host_effects_and_replays_byte_identically_or_traps_out_of_fuel() {
        let bytes = build_effectful_wasm();
        let module = WasmModule::decode(&bytes).expect("valid wasm");

        let (recorded, tape) = {
            let mut seam = RecordingSeam::new(OsEffects::new());
            let mut sb = WasmSandbox::new(module.clone(), 64);
            let out = sb
                .invoke_recording(&mut seam, "mix", &[WasmVal::I64(42)])
                .expect("record run succeeds");
            (out, seam.into_log())
        };

        let replayed = {
            let mut seam = ReplaySeam::new(tape.clone());
            let mut sb = WasmSandbox::new(module.clone(), 64);
            let out = sb
                .invoke_replay(&mut seam, "mix", &[WasmVal::I64(42)])
                .expect("replay run succeeds");
            seam.finish().expect("all taped records consumed");
            out
        };
        assert_eq!(recorded, replayed);

        let shadowed = {
            let records = &tape.0;
            let view = KeyedView::new(records);
            let mut seam = ShadowSeam::new(records, &view, records.len());
            let mut sb = WasmSandbox::new(module.clone(), 64);
            sb.invoke_shadow(&mut seam, "mix", &[WasmVal::I64(42)])
                .expect("shadow run succeeds")
        };
        assert_eq!(recorded, shadowed);

        // Fuel exhaustion traps deterministically before finishing.
        let mut seam = ReplaySeam::new(tape.clone());
        let mut starved = WasmSandbox::new(module.clone(), 3);
        assert_eq!(
            starved.invoke_replay(&mut seam, "mix", &[WasmVal::I64(42)]),
            Err(WasmTrap::OutOfFuel { limit: 3 })
        );

        // Wrong argument type (`I32` instead of `I64`) is rejected at entry!
        let mut seam_ty = ReplaySeam::new(tape);
        let mut sb_ty = WasmSandbox::new(module, 64);
        assert_eq!(
            sb_ty.invoke_replay(&mut seam_ty, "mix", &[WasmVal::I32(42)]),
            Err(WasmTrap::SignatureMismatch)
        );
    }

    #[test]
    fn wasm_rejects_bad_import_sig_duplicate_sections_and_i32_div_min_overflow() {
        // Bad import signature (`clock_millis` declared as `() -> i32` instead of `() -> i64`).
        let mut bad_imp = WASM_MAGIC_V1.to_vec();
        bad_imp.extend_from_slice(&[1, 5, 1, 0x60, 0, 1, 0x7F]);
        let imp = [
            1u8, 7, b'a', b's', b't', b'r', b'e', b'a', b'm', 12, b'c', b'l', b'o', b'c', b'k',
            b'_', b'm', b'i', b'l', b'l', b'i', b's', 0x00, 0,
        ];
        bad_imp.push(2);
        bad_imp.push(imp.len() as u8);
        bad_imp.extend_from_slice(&imp);
        assert_eq!(
            WasmModule::decode(&bad_imp),
            Err(WasmTrap::SignatureMismatch)
        );

        // Duplicate Type section (id=1 twice) is rejected.
        let mut dup_sec = WASM_MAGIC_V1.to_vec();
        dup_sec.extend_from_slice(&[1, 4, 1, 0x60, 0, 0]);
        dup_sec.extend_from_slice(&[1, 4, 1, 0x60, 0, 0]);
        assert!(matches!(
            WasmModule::decode(&dup_sec),
            Err(WasmTrap::MalformedBinary(_))
        ));

        // `i32.div_s(i32::MIN, -1)` traps instead of silently wrapping.
        let mut div_mod = WASM_MAGIC_V1.to_vec();
        div_mod.extend_from_slice(&[1, 7, 1, 0x60, 2, 0x7F, 0x7F, 1, 0x7F]);
        div_mod.extend_from_slice(&[3, 2, 1, 0]);
        div_mod.extend_from_slice(&[7, 7, 1, 3, b'd', b'i', b'v', 0x00, 0]);
        let body = [0u8, 0x20, 0, 0x20, 1, 0x6D, 0x0B];
        div_mod.extend_from_slice(&[10, (2 + body.len()) as u8, 1, body.len() as u8]);
        div_mod.extend_from_slice(&body);
        let dm = WasmModule::decode(&div_mod).expect("valid div module");
        let mut seam = ReplaySeam::new(astream_effects::EffectsLog(Vec::new()));
        let mut sb = WasmSandbox::new(dm, 32);
        assert_eq!(
            sb.invoke_replay(
                &mut seam,
                "div",
                &[WasmVal::I32(i32::MIN), WasmVal::I32(-1)]
            ),
            Err(WasmTrap::DivisionByZero)
        );
    }
}
