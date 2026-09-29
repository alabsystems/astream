// A clean fixture: a declared cfg-feature and a test that exercises a symbol.
// The gate must report ZERO findings here.

#[cfg(feature = "ok")]
pub fn ok() -> i32 {
    42
}

fn value() -> i32 {
    42
}

#[test]
fn references_a_symbol() {
    assert_eq!(value(), 42);
}

// A real assertion keeps a message and a cast: neither may make the tautology
// lint flag a test that does exercise a symbol.
#[test]
fn references_a_symbol_with_message_and_cast() {
    assert_eq!(value(), 42, "value is 42");
    assert_eq!(value() as i64, 42);
    assert!(value() > 0, "positive: {}", value());
}
