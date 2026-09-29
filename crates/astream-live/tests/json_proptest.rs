//! Property tests for the hand-rolled JSON parser — the live bridge's only
//! attacker-facing surface (it parses untrusted Anthropic-response bytes). The
//! headline contract is that it **never panics / aborts** on any input, and that
//! well-formed input round-trips -- in particular no stack overflow on deep
//! nesting and no arithmetic underflow on a malformed surrogate pair.

use astream_live::json::{self, Json};
use proptest::prelude::*;

proptest! {
    /// Arbitrary unicode text: parse returns Ok or Err, never panics.
    #[test]
    fn parse_never_panics_on_arbitrary_text(s in ".{0,512}") {
        let _ = json::parse(&s);
    }

    /// Arbitrary bytes (lossy to UTF-8): hostile network bytes must not abort.
    #[test]
    fn parse_never_panics_on_arbitrary_bytes(bytes in proptest::collection::vec(any::<u8>(), 0..512)) {
        let s = String::from_utf8_lossy(&bytes);
        let _ = json::parse(&s);
    }

    /// Deeply nested brackets: must Err past the depth bound, never overflow the
    /// stack. (Without the cap this aborts the process for large `n`.)
    #[test]
    fn deep_nesting_errs_never_overflows(n in 0usize..4000) {
        let s = "[".repeat(n);
        let _ = json::parse(&s);
    }

    /// A `\u` escape that may or may not form a valid surrogate pair: parse must
    /// not underflow/panic (an unchecked `lo - 0xDC00` would).
    #[test]
    fn surrogate_escapes_never_underflow(hi in 0u16.., lo in 0u16..) {
        let s = format!(r#""\u{hi:04X}\u{lo:04X}""#);
        let _ = json::parse(&s);
    }

    /// Well-formed integers round-trip: parse succeeds and the numeric value
    /// matches a direct `as f64` (both round identically past 2^53).
    #[test]
    fn well_formed_integers_round_trip(n in any::<i64>()) {
        let text = format!("{{\"v\":{n}}}");
        let v = json::parse(&text).expect("a JSON object with one integer parses");
        prop_assert_eq!(v.get("v").and_then(Json::as_f64), Some(n as f64));
    }
}
