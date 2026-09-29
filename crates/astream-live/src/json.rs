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
            Json::Obj(entries) => entries.iter().find(|(key, _)| key == k).map(|(_, v)| v),
            _ => None,
        }
    }
    /// This value as a `&str`, if it is a string.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    /// This value's numeric value, if it is a number. Parses the preserved raw
    /// lexeme on demand (overflowing literals like `1e999` yield `f64::INFINITY`,
    /// per the standard `f64` parse).
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Json::Num(s) => s.parse::<f64>().ok(),
            _ => None,
        }
    }
    /// This value as a slice, if it is an array.
    pub fn as_array(&self) -> Option<&[Json]> {
        match self {
            Json::Arr(a) => Some(a),
            _ => None,
        }
    }
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
        return Err(format!("trailing bytes at {}", p.i));
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
                self.i += 1;
            } else {
                break;
            }
        }
    }

    fn value(&mut self) -> Result<Json, String> {
        // Bound recursion depth: a value may contain a value (object/array), so
        // unbounded nesting is unbounded recursion. Past MAX_DEPTH we Err rather
        // than ride the call stack into a process-aborting overflow.
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return Err(format!(
                "max nesting depth {MAX_DEPTH} exceeded at {}",
                self.i
            ));
        }
        let r = match self.b.get(self.i) {
            Some(b'{') => self.object(),
            Some(b'[') => self.array(),
            Some(b'"') => self.string().map(Json::Str),
            Some(b't') => self.lit("true", Json::Bool(true)),
            Some(b'f') => self.lit("false", Json::Bool(false)),
            Some(b'n') => self.lit("null", Json::Null),
            Some(c) if *c == b'-' || c.is_ascii_digit() => self.number(),
            _ => Err(format!("unexpected byte at {}", self.i)),
        };
        self.depth -= 1;
        r
    }

    fn lit(&mut self, word: &str, v: Json) -> Result<Json, String> {
        if self.b[self.i..].starts_with(word.as_bytes()) {
            self.i += word.len();
            Ok(v)
        } else {
            Err(format!("invalid literal at {}", self.i))
        }
    }

    fn object(&mut self) -> Result<Json, String> {
        self.i += 1; // {
        let mut out = Vec::new();
        self.ws();
        if self.b.get(self.i) == Some(&b'}') {
            self.i += 1;
            return Ok(Json::Obj(out));
        }
        loop {
            self.ws();
            if self.b.get(self.i) != Some(&b'"') {
                return Err(format!("expected key string at {}", self.i));
            }
            let key = self.string()?;
            self.ws();
            if self.b.get(self.i) != Some(&b':') {
                return Err(format!("expected ':' at {}", self.i));
            }
            self.i += 1;
            self.ws();
            let val = self.value()?;
            out.push((key, val));
            self.ws();
            match self.b.get(self.i) {
                Some(b',') => self.i += 1,
                Some(b'}') => {
                    self.i += 1;
                    return Ok(Json::Obj(out));
                }
                _ => return Err(format!("expected ',' or '}}' at {}", self.i)),
            }
        }
    }

    fn array(&mut self) -> Result<Json, String> {
        self.i += 1; // [
        let mut out = Vec::new();
        self.ws();
        if self.b.get(self.i) == Some(&b']') {
            self.i += 1;
            return Ok(Json::Arr(out));
        }
        loop {
            self.ws();
            out.push(self.value()?);
            self.ws();
            match self.b.get(self.i) {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    return Ok(Json::Arr(out));
                }
                _ => return Err(format!("expected ',' or ']' at {}", self.i)),
            }
        }
    }

    fn string(&mut self) -> Result<String, String> {
        self.i += 1; // opening "
        let mut s = String::new();
        loop {
            let c = *self.b.get(self.i).ok_or("unterminated string")?;
            self.i += 1;
            match c {
                b'"' => return Ok(s),
                b'\\' => {
                    let e = *self.b.get(self.i).ok_or("dangling escape")?;
                    self.i += 1;
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
                        _ => return Err(format!("bad escape at {}", self.i)),
                    }
                }
                // RFC 8259 §7: control characters must be escaped in a string.
                0x00..=0x1f => {
                    return Err(format!("unescaped control character at {}", self.i - 1))
                }
                // A raw UTF-8 byte: collect the full code point.
                _ => {
                    let start = self.i - 1;
                    let len = utf8_len(c);
                    let end = start + len;
                    let chunk = self.b.get(start..end).ok_or("truncated utf8")?;
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
        if (0xD800..=0xDBFF).contains(&cp) {
            if self.b.get(self.i) == Some(&b'\\') && self.b.get(self.i + 1) == Some(&b'u') {
                self.i += 2;
                let lo = self.hex4()?;
                if !(0xDC00..=0xDFFF).contains(&lo) {
                    return Err("high surrogate not followed by a low surrogate".to_string());
                }
                let c = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                return char::from_u32(c).ok_or_else(|| "bad surrogate".to_string());
            }
            return Err("lone high surrogate".to_string());
        }
        // A lone low surrogate (0xDC00..=0xDFFF) is not a valid scalar value.
        char::from_u32(cp).ok_or_else(|| "bad code point".to_string())
    }

    fn hex4(&mut self) -> Result<u32, String> {
        let s = self.b.get(self.i..self.i + 4).ok_or("short \\u")?;
        // Exactly four hex digits: `from_str_radix` alone would also take a
        // leading `+` (`\u+041` as U+0041).
        let mut v = 0u32;
        for &c in s {
            let d = (c as char).to_digit(16).ok_or("bad hex in \\u")?;
            v = v * 16 + d;
        }
        self.i += 4;
        Ok(v)
    }

    fn number(&mut self) -> Result<Json, String> {
        let start = self.i;
        if self.b.get(self.i) == Some(&b'-') {
            self.i += 1;
        }
        while let Some(c) = self.b.get(self.i) {
            if c.is_ascii_digit()
                || *c == b'.'
                || *c == b'e'
                || *c == b'E'
                || *c == b'+'
                || *c == b'-'
            {
                self.i += 1;
            } else {
                break;
            }
        }
        let st = std::str::from_utf8(&self.b[start..self.i]).map_err(|_| "bad number")?;
        // Validate the lexeme against the RFC 8259 number grammar, but KEEP the
        // raw text: a large integer (> 2^53) or a high-precision literal would be
        // mangled by an f64 round-trip, so numbers survive verbatim for
        // re-serialization. The grammar check is NOT `f64::from_str` — Rust's
        // float grammar is broader (`01`, `1.`, `-.5`, `1.e5` all parse) and this
        // lexeme is re-emitted verbatim onto the durable log, where an
        // RFC-conformant consumer would reject it.
        if !is_rfc8259_number(st) {
            return Err(format!("bad number at {start}"));
        }
        Ok(Json::Num(st.to_string()))
    }
}

/// `-? (0 | [1-9][0-9]*) (\.[0-9]+)? ([eE][+-]?[0-9]+)?` — RFC 8259 §6, exactly.
fn is_rfc8259_number(s: &str) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    if b.first() == Some(&b'-') {
        i += 1;
    }
    // int: `0` or a non-zero digit followed by digits (no leading zeros).
    match b.get(i) {
        Some(b'0') => i += 1,
        Some(c) if c.is_ascii_digit() => {
            while b.get(i).is_some_and(u8::is_ascii_digit) {
                i += 1;
            }
        }
        _ => return false,
    }
    // frac: `.` then ONE OR MORE digits.
    if b.get(i) == Some(&b'.') {
        i += 1;
        let start = i;
        while b.get(i).is_some_and(u8::is_ascii_digit) {
            i += 1;
        }
        if i == start {
            return false;
        }
    }
    // exp: `e`/`E`, optional sign, ONE OR MORE digits.
    if matches!(b.get(i), Some(b'e') | Some(b'E')) {
        i += 1;
        if matches!(b.get(i), Some(b'+') | Some(b'-')) {
            i += 1;
        }
        let start = i;
        while b.get(i).is_some_and(u8::is_ascii_digit) {
            i += 1;
        }
        if i == start {
            return false;
        }
    }
    i == b.len()
}

fn utf8_len(lead: u8) -> usize {
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
}
