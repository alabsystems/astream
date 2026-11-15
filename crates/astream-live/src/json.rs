//! A small, complete recursive-descent JSON parser — zero-dependency, so the
//! live-capture bridge can join the substrate workspace without pulling
//! `serde_json` into astream's reproducible-build graph.
//!
//! This is a *real* parser, not a fixture matcher: it handles objects, arrays,
//! strings (with `\"`, `\\`, `\/`, `\b\f\n\r\t`, and `\uXXXX` incl. surrogate
//! pairs), numbers, `true`/`false`/`null`, and arbitrary nesting/whitespace, and
//! rejects malformed input with an error rather than panicking — including
//! adversarial input: nesting past [`MAX_DEPTH`] is rejected before it can
//! exhaust the stack, and a lone/ill-formed surrogate is an error, never an
//! arithmetic underflow.

/// Maximum value-nesting depth the parser will descend. A hand-rolled
/// recursive-descent parser turns deeply-nested input into deep recursion, so an
/// attacker-chosen `[[[[...` would abort the process via a stack overflow — which
/// the panic-free contract forbids. Past this depth, [`parse`] returns `Err`
/// instead. 128 is far beyond any real Anthropic tool-input object.
pub const MAX_DEPTH: usize = 128;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "json_island.rs"]
mod json_island;
#[cfg(not(clean_islands))]
pub use crate::twins::json_clamp_depth;
#[cfg(clean_islands)]
pub use json_island::json_clamp_depth;

contract_fn! {
    /// Verified check that the current JSON recursion `depth` is within `max_depth`,
    /// linked via `clean-kernel-defeq` to `json_depth_within_max_isl`.
    #[must_use]
    pub const fn json_depth_within_max(depth: usize, max_depth: usize) -> bool
    clauses [ensures result == (depth <= max_depth)]
    {
        depth <= max_depth
    }
}

/// A parsed JSON value.
#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    /// `null`
    Null,
    /// `true` / `false`
    Bool(bool),
    /// A number, kept as its **raw source lexeme** (e.g. `"-3e2"`, `"9007199254740993"`).
    /// Numbers are not routed through `f64` on parse, so large integers and
    /// high-precision literals survive verbatim for faithful re-serialization
    /// (see `render_input`); use [`Json::as_f64`] for the numeric value.
    Num(String),
    /// a string
    Str(String),
    /// an array
    Arr(Vec<Json>),
    /// an object (insertion order preserved)
    Obj(Vec<(String, Json)>),
}

impl Json {
    /// The value at object key `k`, if this is an object that has it.
    pub fn get(&self, k: &str) -> Option<&Json> {
        match self {
            Json::Obj(entries) => {
                let mut rest = entries.as_slice();
                while let [(key, v), tail @ ..] = rest {
                    if key.as_bytes() == k.as_bytes() {
                        return Some(v);
                    }
                    rest = tail;
                }
                None
            }
            _ => None,
        }
    }
    /// This value as a `&str`, if it is a string.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s.as_str()),
            _ => None,
        }
    }
    /// This value's numeric value, if it is a number. Parses the preserved raw
    /// lexeme on demand (overflowing literals like `1e999` yield `f64::INFINITY`,
    /// per the standard `f64` parse).
    #[expect(
        clippy::manual_ok_err,
        reason = "a812042 spelled `.ok()` as a match for the verified lane; keep its form"
    )]
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Json::Num(s) => match s.parse::<f64>() {
                Ok(v) => Some(v),
                Err(_) => None,
            },
            _ => None,
        }
    }
    /// This value as a slice, if it is an array.
    pub fn as_array(&self) -> Option<&[Json]> {
        match self {
            Json::Arr(a) => Some(a.as_slice()),
            _ => None,
        }
    }
}

#[inline]
const fn nibble_to_hex_upper(n: u8) -> u8 {
    match n & 0xF {
        0 => b'0',
        1 => b'1',
        2 => b'2',
        3 => b'3',
        4 => b'4',
        5 => b'5',
        6 => b'6',
        7 => b'7',
        8 => b'8',
        9 => b'9',
        10 => b'A',
        11 => b'B',
        12 => b'C',
        13 => b'D',
        14 => b'E',
        _ => b'F',
    }
}

#[inline]
const fn hex_byte_to_u32(b: u8) -> Option<u32> {
    match b {
        b'0' => Some(0),
        b'1' => Some(1),
        b'2' => Some(2),
        b'3' => Some(3),
        b'4' => Some(4),
        b'5' => Some(5),
        b'6' => Some(6),
        b'7' => Some(7),
        b'8' => Some(8),
        b'9' => Some(9),
        b'a' | b'A' => Some(10),
        b'b' | b'B' => Some(11),
        b'c' | b'C' => Some(12),
        b'd' | b'D' => Some(13),
        b'e' | b'E' => Some(14),
        b'f' | b'F' => Some(15),
        _ => None,
    }
}

/// Encode a 16-bit code unit into its 4-byte uppercase ASCII hex `\uXXXX` payload.
#[must_use]
pub const fn encode_hex4_bytes(val: u16) -> [u8; 4] {
    [
        nibble_to_hex_upper(((val >> 12) & 0xF) as u8),
        nibble_to_hex_upper(((val >> 8) & 0xF) as u8),
        nibble_to_hex_upper(((val >> 4) & 0xF) as u8),
        nibble_to_hex_upper((val & 0xF) as u8),
    ]
}

/// Decode a 4-byte ASCII hex `\uXXXX` payload into its 16-bit numeric value (`0..=0xFFFF`).
#[must_use]
pub const fn decode_hex4_bytes(raw: &[u8; 4]) -> Option<u32> {
    let Some(d0) = hex_byte_to_u32(raw[0]) else {
        return None;
    };
    let Some(d1) = hex_byte_to_u32(raw[1]) else {
        return None;
    };
    let Some(d2) = hex_byte_to_u32(raw[2]) else {
        return None;
    };
    let Some(d3) = hex_byte_to_u32(raw[3]) else {
        return None;
    };
    Some((d0 << 12) | (d1 << 8) | (d2 << 4) | d3)
}

/// Combine a UTF-16 high surrogate (`0xD800..=0xDBFF`) and low surrogate
/// (`0xDC00..=0xDFFF`) into a supplementary scalar code point (`0x10000..=0x10FFFF`).
#[must_use]
pub const fn decode_surrogate_pair(hi: u32, lo: u32) -> Option<u32> {
    if hi >= 0xD800 && hi <= 0xDBFF && lo >= 0xDC00 && lo <= 0xDFFF {
        let hi_off = (hi - 0xD800) & 0x3FF;
        let lo_off = (lo - 0xDC00) & 0x3FF;
        Some(0x10000u32.wrapping_add((hi_off << 10) | lo_off))
    } else {
        None
    }
}

fn err_at(prefix: &str, mut n: usize) -> String {
    let mut buf = [0u8; 20];
    let mut idx = 20usize;
    loop {
        idx = idx.saturating_sub(1);
        if let Some(slot) = buf.get_mut(idx) {
            *slot = b'0' | ((n % 10) as u8);
        }
        n /= 10;
        if n == 0 || idx == 0 {
            break;
        }
    }
    let mut out = String::new();
    out.push_str(prefix);
    if let Some(mut rest) = buf.get(idx..) {
        while let &[b, ref tail @ ..] = rest {
            out.push(b as char);
            rest = tail;
        }
    }
    out
}

/// Parse a complete JSON document. Trailing non-whitespace is an error.
pub fn parse(input: &str) -> Result<Json, String> {
    let mut p = Parser {
        b: input.as_bytes(),
        i: 0,
        depth: 0,
    };
    p.ws();
    let v = p.value()?;
    p.ws();
    if p.i != p.b.len() {
        return Err(err_at("trailing bytes at ", p.i));
    }
    Ok(v)
}

struct Parser<'a> {
    b: &'a [u8],
    i: usize,
    /// Current value-nesting depth, bounded by [`MAX_DEPTH`] so hostile nesting
    /// cannot overflow the stack (a process abort the panic-free contract forbids).
    depth: usize,
}

impl Parser<'_> {
    fn ws(&mut self) {
        while let Some(&c) = self.b.get(self.i) {
            if c == b' ' || c == b'\t' || c == b'\n' || c == b'\r' {
                self.i = self.i.saturating_add(1);
            } else {
                break;
            }
        }
    }

    fn value(&mut self) -> Result<Json, String> {
        // Bound recursion depth: a value may contain a value (object/array), so
        // unbounded nesting is unbounded recursion. Past MAX_DEPTH we Err rather
        // than ride the call stack into a process-aborting overflow.
        self.depth = self.depth.saturating_add(1);
        if self.depth > MAX_DEPTH {
            self.depth = self.depth.saturating_sub(1);
            return Err(err_at("max nesting depth 128 exceeded at ", self.i));
        }
        let r = match self.b.get(self.i) {
            Some(b'{') => self.object(),
            Some(b'[') => self.array(),
            Some(b'"') => self.string().map(Json::Str),
            Some(b't') => self.lit("true", Json::Bool(true)),
            Some(b'f') => self.lit("false", Json::Bool(false)),
            Some(b'n') => self.lit("null", Json::Null),
            Some(c) if *c == b'-' || c.is_ascii_digit() => self.number(),
            _ => Err(err_at("unexpected byte at ", self.i)),
        };
        self.depth = self.depth.saturating_sub(1);
        r
    }

    fn lit(&mut self, word: &str, v: Json) -> Result<Json, String> {
        let Some(rem) = self.b.get(self.i..) else {
            return Err(err_at("invalid literal at ", self.i));
        };
        if matches!(rem.get(..word.len()), Some(head) if head == word.as_bytes()) {
            self.i = self.i.saturating_add(word.len());
            Ok(v)
        } else {
            Err(err_at("invalid literal at ", self.i))
        }
    }

    fn object(&mut self) -> Result<Json, String> {
        self.i = self.i.saturating_add(1); // {
        let mut out = Vec::new();
        self.ws();
        if matches!(self.b.get(self.i), Some(b'}')) {
            self.i = self.i.saturating_add(1);
            return Ok(Json::Obj(out));
        }
        loop {
            self.ws();
            if !matches!(self.b.get(self.i), Some(b'"')) {
                return Err(err_at("expected key string at ", self.i));
            }
            let key = self.string()?;
            self.ws();
            if !matches!(self.b.get(self.i), Some(b':')) {
                return Err(err_at("expected ':' at ", self.i));
            }
            self.i = self.i.saturating_add(1);
            self.ws();
            let val = self.value()?;
            out.push((key, val));
            self.ws();
            match self.b.get(self.i) {
                Some(b',') => self.i = self.i.saturating_add(1),
                Some(b'}') => {
                    self.i = self.i.saturating_add(1);
                    return Ok(Json::Obj(out));
                }
                _ => return Err(err_at("expected ',' or '}' at ", self.i)),
            }
        }
    }

    fn array(&mut self) -> Result<Json, String> {
        self.i = self.i.saturating_add(1); // [
        let mut out = Vec::new();
        self.ws();
        if matches!(self.b.get(self.i), Some(b']')) {
            self.i = self.i.saturating_add(1);
            return Ok(Json::Arr(out));
        }
        loop {
            self.ws();
            out.push(self.value()?);
            self.ws();
            match self.b.get(self.i) {
                Some(b',') => self.i = self.i.saturating_add(1),
                Some(b']') => {
                    self.i = self.i.saturating_add(1);
                    return Ok(Json::Arr(out));
                }
                _ => return Err(err_at("expected ',' or ']' at ", self.i)),
            }
        }
    }

    fn string(&mut self) -> Result<String, String> {
        self.i = self.i.saturating_add(1); // opening "
        let mut s = String::new();
        loop {
            let char_pos = self.i;
            let c = *self.b.get(char_pos).ok_or("unterminated string")?;
            self.i = char_pos.saturating_add(1);
            match c {
                b'"' => return Ok(s),
                b'\\' => {
                    let e = *self.b.get(self.i).ok_or("dangling escape")?;
                    self.i = self.i.saturating_add(1);
                    match e {
                        b'"' => s.push('"'),
                        b'\\' => s.push('\\'),
                        b'/' => s.push('/'),
                        b'b' => s.push('\u{08}'),
                        b'f' => s.push('\u{0c}'),
                        b'n' => s.push('\n'),
                        b'r' => s.push('\r'),
                        b't' => s.push('\t'),
                        b'u' => s.push(self.unicode_escape()?),
                        _ => return Err(err_at("bad escape at ", self.i)),
                    }
                }
                // RFC 8259 §7: control characters must be escaped in a string.
                0x00..=0x1f => return Err(err_at("unescaped control character at ", char_pos)),
                // A raw UTF-8 byte: collect the full code point.
                _ => {
                    let len = utf8_len(c);
                    let end = char_pos.saturating_add(len);
                    let chunk = self.b.get(char_pos..end).ok_or("truncated utf8")?;
                    let st = std::str::from_utf8(chunk).map_err(|_| "bad utf8")?;
                    s.push_str(st);
                    self.i = end;
                }
            }
        }
    }

    fn unicode_escape(&mut self) -> Result<char, String> {
        let cp = self.hex4()?;
        // High surrogate: must be followed by a \uXXXX low surrogate in
        // 0xDC00..=0xDFFF. Validate the low half BEFORE the arithmetic — an
        // unchecked `lo - 0xDC00` underflows (debug panic / release wraparound)
        // for any non-low-surrogate second escape.
        if cp >= 0xD800 && cp <= 0xDBFF {
            let next_i = self.i.saturating_add(1);
            if matches!(self.b.get(self.i), Some(b'\\')) && matches!(self.b.get(next_i), Some(b'u'))
            {
                self.i = self.i.saturating_add(2);
                let lo = self.hex4()?;
                let Some(c) = decode_surrogate_pair(cp, lo) else {
                    return Err("high surrogate not followed by a low surrogate".to_string());
                };
                let Some(ch) = char::from_u32(c) else {
                    return Err("bad surrogate".to_string());
                };
                return Ok(ch);
            }
            return Err("lone high surrogate".to_string());
        }
        // A lone low surrogate (0xDC00..=0xDFFF) is not a valid scalar value.
        let Some(ch) = char::from_u32(cp) else {
            return Err("bad code point".to_string());
        };
        Ok(ch)
    }

    fn hex4(&mut self) -> Result<u32, String> {
        let i0 = self.i;
        let i1 = i0.saturating_add(1);
        let i2 = i0.saturating_add(2);
        let i3 = i0.saturating_add(3);
        let (Some(&b0), Some(&b1), Some(&b2), Some(&b3)) = (
            self.b.get(i0),
            self.b.get(i1),
            self.b.get(i2),
            self.b.get(i3),
        ) else {
            return Err("short \\u".to_string());
        };
        // Exactly four hex digits: `from_str_radix` alone would also take a
        // leading `+` (`\u+041` as U+0041).
        let Some(v) = decode_hex4_bytes(&[b0, b1, b2, b3]) else {
            return Err("bad hex in \\u".to_string());
        };
        self.i = i0.saturating_add(4);
        Ok(v)
    }

    fn number(&mut self) -> Result<Json, String> {
        let start = self.i;
        if matches!(self.b.get(self.i), Some(b'-')) {
            self.i = self.i.saturating_add(1);
        }
        while let Some(c) = self.b.get(self.i) {
            if c.is_ascii_digit()
                || *c == b'.'
                || *c == b'e'
                || *c == b'E'
                || *c == b'+'
                || *c == b'-'
            {
                self.i = self.i.saturating_add(1);
            } else {
                break;
            }
        }
        let span = self.b.get(start..self.i).ok_or("bad number")?;
        let st = std::str::from_utf8(span).map_err(|_| "bad number")?;
        // Validate the lexeme against the RFC 8259 number grammar, but KEEP the
        // raw text: a large integer (> 2^53) or a high-precision literal would be
        // mangled by an f64 round-trip, so numbers survive verbatim for
        // re-serialization. The grammar check is NOT `f64::from_str` — Rust's
        // float grammar is broader (`01`, `1.`, `-.5`, `1.e5` all parse) and this
        // lexeme is re-emitted verbatim onto the durable log, where an
        // RFC-conformant consumer would reject it.
        if !is_rfc8259_number(st) {
            return Err(err_at("bad number at ", start));
        }
        Ok(Json::Num(st.to_string()))
    }
}

/// `-? (0 | [1-9][0-9]*) (\.[0-9]+)? ([eE][+-]?[0-9]+)?` — RFC 8259 §6, exactly.
#[must_use]
pub const fn skip_digits(mut rest: &[u8]) -> &[u8] {
    while let &[d, ref t @ ..] = rest {
        if !(d >= b'0' && d <= b'9') {
            break;
        }
        rest = t;
    }
    rest
}

/// Consume one or more ASCII digits from `rest`, returning the remaining tail.
#[must_use]
pub const fn take_one_or_more_digits(rest: &[u8]) -> Option<&[u8]> {
    let &[first, ref tail @ ..] = rest else {
        return None;
    };
    if !(first >= b'0' && first <= b'9') {
        return None;
    }
    let mut cur = tail;
    while let &[d, ref t @ ..] = cur {
        if !(d >= b'0' && d <= b'9') {
            break;
        }
        cur = t;
    }
    Some(cur)
}

/// Strip an optional leading `'-'` byte from `rest`.
#[must_use]
pub const fn skip_optional_minus(rest: &[u8]) -> &[u8] {
    if let &[first, ref tail @ ..] = rest {
        if first == b'-' {
            return tail;
        }
    }
    rest
}

/// Consume an RFC 8259 integer mantissa (`0 | [1-9][0-9]*`), returning the remaining tail.
#[must_use]
pub const fn take_int_digits(rest: &[u8]) -> Option<&[u8]> {
    let &[first, ref tail @ ..] = rest else {
        return None;
    };
    if first == b'0' {
        Some(tail)
    } else if first >= b'1' && first <= b'9' {
        let mut cur = tail;
        while let &[d, ref t @ ..] = cur {
            if !(d >= b'0' && d <= b'9') {
                break;
            }
            cur = t;
        }
        Some(cur)
    } else {
        None
    }
}

/// Consume an optional RFC 8259 fractional part (`(\.[0-9]+)?`).
#[must_use]
pub const fn take_optional_frac(rest: &[u8]) -> Option<&[u8]> {
    if let &[dot, ref after_dot @ ..] = rest {
        if dot == b'.' {
            let &[first, ref tail @ ..] = after_dot else {
                return None;
            };
            if !(first >= b'0' && first <= b'9') {
                return None;
            }
            let mut cur = tail;
            while let &[d, ref t @ ..] = cur {
                if !(d >= b'0' && d <= b'9') {
                    break;
                }
                cur = t;
            }
            return Some(cur);
        }
    }
    Some(rest)
}

/// Strip an optional leading `'+'` or `'-'` byte from `rest`.
#[must_use]
pub const fn skip_optional_sign(rest: &[u8]) -> &[u8] {
    if let &[sign, ref tail @ ..] = rest {
        if sign == b'+' || sign == b'-' {
            return tail;
        }
    }
    rest
}

/// Consume an optional RFC 8259 exponent part (`([eE][+-]?[0-9]+)?`).
#[must_use]
pub const fn take_optional_exp(rest: &[u8]) -> Option<&[u8]> {
    if let &[exp_ch, ref after_e @ ..] = rest {
        if exp_ch == b'e' || exp_ch == b'E' {
            let after_sign = if let &[sign, ref tail @ ..] = after_e {
                if sign == b'+' || sign == b'-' {
                    tail
                } else {
                    after_e
                }
            } else {
                after_e
            };
            let &[first, ref tail @ ..] = after_sign else {
                return None;
            };
            if !(first >= b'0' && first <= b'9') {
                return None;
            }
            let mut cur = tail;
            while let &[d, ref t @ ..] = cur {
                if !(d >= b'0' && d <= b'9') {
                    break;
                }
                cur = t;
            }
            return Some(cur);
        }
    }
    Some(rest)
}

/// Encode a 21-byte JSON parser token span `(start, end, depth, kind)` in little-endian byte order.
#[must_use]
pub const fn encode_json_token_span(start: u64, end: u64, depth: u32, kind: u8) -> [u8; 21] {
    [
        (start & 0xFF) as u8,
        ((start >> 8) & 0xFF) as u8,
        ((start >> 16) & 0xFF) as u8,
        ((start >> 24) & 0xFF) as u8,
        ((start >> 32) & 0xFF) as u8,
        ((start >> 40) & 0xFF) as u8,
        ((start >> 48) & 0xFF) as u8,
        ((start >> 56) & 0xFF) as u8,
        (end & 0xFF) as u8,
        ((end >> 8) & 0xFF) as u8,
        ((end >> 16) & 0xFF) as u8,
        ((end >> 24) & 0xFF) as u8,
        ((end >> 32) & 0xFF) as u8,
        ((end >> 40) & 0xFF) as u8,
        ((end >> 48) & 0xFF) as u8,
        ((end >> 56) & 0xFF) as u8,
        (depth & 0xFF) as u8,
        ((depth >> 8) & 0xFF) as u8,
        ((depth >> 16) & 0xFF) as u8,
        ((depth >> 24) & 0xFF) as u8,
        kind,
    ]
}

/// Decode a 21-byte JSON parser token span `(start, end, depth, kind)` from little-endian byte order,
/// returning `None` if `start > end` or `depth > MAX_DEPTH as u32`.
#[must_use]
pub const fn decode_json_token_span(bytes: &[u8; 21]) -> Option<(u64, u64, u32, u8)> {
    let start = (bytes[0] as u64)
        | ((bytes[1] as u64) << 8)
        | ((bytes[2] as u64) << 16)
        | ((bytes[3] as u64) << 24)
        | ((bytes[4] as u64) << 32)
        | ((bytes[5] as u64) << 40)
        | ((bytes[6] as u64) << 48)
        | ((bytes[7] as u64) << 56);
    let end = (bytes[8] as u64)
        | ((bytes[9] as u64) << 8)
        | ((bytes[10] as u64) << 16)
        | ((bytes[11] as u64) << 24)
        | ((bytes[12] as u64) << 32)
        | ((bytes[13] as u64) << 40)
        | ((bytes[14] as u64) << 48)
        | ((bytes[15] as u64) << 56);
    let depth = (bytes[16] as u32)
        | ((bytes[17] as u32) << 8)
        | ((bytes[18] as u32) << 16)
        | ((bytes[19] as u32) << 24);
    let kind = bytes[20];
    if start > end || depth > (MAX_DEPTH as u32) {
        return None;
    }
    Some((start, end, depth, kind))
}

const fn is_rfc8259_number(s: &str) -> bool {
    let mut scan = s.as_bytes();
    let mut state = 0u8;
    while let &[ch, ref tail @ ..] = scan {
        state = match state {
            0 => match ch {
                b'-' => 1,
                b'0' => 2,
                b'1'..=b'9' => 3,
                _ => return false,
            },
            1 => match ch {
                b'0' => 2,
                b'1'..=b'9' => 3,
                _ => return false,
            },
            2 => match ch {
                b'.' => 4,
                b'e' | b'E' => 6,
                _ => return false,
            },
            3 => match ch {
                b'0'..=b'9' => 3,
                b'.' => 4,
                b'e' | b'E' => 6,
                _ => return false,
            },
            4 => match ch {
                b'0'..=b'9' => 5,
                _ => return false,
            },
            5 => match ch {
                b'0'..=b'9' => 5,
                b'e' | b'E' => 6,
                _ => return false,
            },
            6 => match ch {
                b'+' | b'-' => 7,
                b'0'..=b'9' => 8,
                _ => return false,
            },
            7 => match ch {
                b'0'..=b'9' => 8,
                _ => return false,
            },
            8 => match ch {
                b'0'..=b'9' => 8,
                _ => return false,
            },
            _ => return false,
        };
        scan = tail;
    }
    matches!(state, 2 | 3 | 5 | 8)
}

const fn utf8_len(lead: u8) -> usize {
    match lead {
        0x00..=0x7f => 1,
        0xc0..=0xdf => 2,
        0xe0..=0xef => 3,
        _ => 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_nested_objects_arrays_escapes_and_unicode() {
        let v = parse(r#"{"a":[1,2.5,true,null],"b":{"c":"x\"y\né"},"d":-3e2}"#).unwrap();
        assert_eq!(v.get("a").unwrap().as_array().unwrap().len(), 4);
        assert_eq!(
            v.get("b").unwrap().get("c").unwrap().as_str().unwrap(),
            "x\"y\n\u{e9}"
        );
        // The number keeps its raw lexeme, and parses to the right value.
        assert_eq!(v.get("d"), Some(&Json::Num("-3e2".to_string())));
        assert_eq!(v.get("d").unwrap().as_f64(), Some(-300.0));
    }

    #[test]
    fn rejects_malformed_without_panicking() {
        assert!(parse("{").is_err());
        assert!(parse(r#"{"a":}"#).is_err());
        assert!(parse("[1,2").is_err());
        assert!(parse("nul").is_err());
        assert!(parse(r#""abc"#).is_err());
        assert!(parse(r#"{"a":1}x"#).is_err());
    }

    #[test]
    fn handles_surrogate_pairs() {
        // U+1F680 ROCKET as a UTF-16 surrogate pair.
        let v = parse(r#"{"e":"\uD83D\uDE80"}"#).unwrap();
        assert_eq!(v.get("e").unwrap().as_str().unwrap(), "\u{1F680}");
    }

    #[test]
    fn deep_nesting_errs_instead_of_overflowing_the_stack() {
        // Far past MAX_DEPTH: must be a clean Err, never a process abort.
        let deep = "[".repeat(MAX_DEPTH + 50);
        assert!(parse(&deep).is_err());
        // Just inside the bound still parses (closed off).
        let ok = format!("{}{}", "[".repeat(8), "]".repeat(8));
        assert!(parse(&ok).is_ok());
    }

    #[test]
    fn malformed_surrogates_err_without_underflow() {
        // High surrogate followed by a non-low-surrogate escape: an unchecked
        // `lo - 0xDC00` would underflow here. It must be an Err.
        assert!(parse(r#""\uD800\u0041""#).is_err());
        // High surrogate followed by a raw character, or by nothing at all.
        assert!(parse(r#""\uD800A""#).is_err());
        assert!(parse(r#""\uD800""#).is_err());
        // A lone low surrogate is not a valid scalar value.
        assert!(parse(r#""\uDC00""#).is_err());
    }

    #[test]
    fn a_unicode_escape_is_exactly_four_hex_digits() {
        // `u32::from_str_radix` accepts a leading `+`, so `\u+041` read as U+0041.
        for bad in [
            r#""\u+041""#,
            r#""\u+04""#,
            r#""\uD800\u+C00""#,
            r#""\u 041""#,
        ] {
            assert!(parse(bad).is_err(), "{bad} must be rejected");
        }
        assert_eq!(parse(r#""\u0041\u00e9""#), Ok(Json::Str("A\u{e9}".into())));
    }

    #[test]
    fn raw_control_characters_in_a_string_are_rejected() {
        // RFC 8259 §7: U+0000..U+001F must be escaped inside a string.
        for bad in ["\"a\nb\"", "\"tab\there\"", "\"\u{0}\"", "{\"k\u{1f}\":1}"] {
            assert!(parse(bad).is_err(), "{bad:?} must be rejected");
        }
        assert_eq!(parse(r#""a\nb""#), Ok(Json::Str("a\nb".into())));
        assert_eq!(parse("\"\u{7f}é\""), Ok(Json::Str("\u{7f}é".into())));
    }

    #[test]
    fn number_lexer_rejects_non_rfc8259_lexemes_that_f64_accepts() {
        // Every one of these is accepted by `f64::from_str` but is NOT a JSON
        // number (RFC 8259 §6); accepting it would re-emit the lexeme verbatim
        // into the durable tool-input bytes, which a real JSON consumer rejects
        // (or, for `007`, may read as octal).
        for bad in [
            "01", "007", "00.0", "1.", "-.5", ".5", "1.e5", "-", "1e", "1e+", "+1", "-01", "1.5e",
            "1E-", "--1", "1-", "1..2", "1e5.0",
        ] {
            assert!(
                parse(bad).is_err(),
                "{bad:?} is not an RFC 8259 number and must be rejected"
            );
            let doc = format!("{{\"n\":{bad}}}");
            assert!(
                parse(&doc).is_err(),
                "{doc} must be rejected inside an object"
            );
        }
        // The RFC grammar itself is fully accepted, raw lexeme preserved.
        for good in [
            "0",
            "-0",
            "7",
            "-7",
            "10",
            "1.5",
            "-1.5",
            "0.5",
            "1e5",
            "1E5",
            "1e+5",
            "1e-5",
            "1.5e-5",
            "-0.0e+0",
            "9007199254740993",
        ] {
            assert_eq!(
                parse(good),
                Ok(Json::Num(good.to_string())),
                "{good:?} is an RFC 8259 number"
            );
        }
    }

    #[test]
    fn large_integers_survive_verbatim() {
        // > 2^53: an f64 round-trip would mangle this; the raw lexeme must survive.
        let v = parse(r#"{"id":9007199254740993}"#).unwrap();
        assert_eq!(
            v.get("id"),
            Some(&Json::Num("9007199254740993".to_string()))
        );
    }

    #[test]
    fn json_token_span_codec_round_trips_and_enforces_bounds() {
        let enc = encode_json_token_span(12, 48, 3, 7);
        assert_eq!(decode_json_token_span(&enc), Some((12, 48, 3, 7)));
        let bad_range = encode_json_token_span(49, 48, 3, 7);
        assert_eq!(decode_json_token_span(&bad_range), None);
        let bad_depth = encode_json_token_span(12, 48, (MAX_DEPTH as u32) + 1, 7);
        assert_eq!(decode_json_token_span(&bad_depth), None);
    }
}
