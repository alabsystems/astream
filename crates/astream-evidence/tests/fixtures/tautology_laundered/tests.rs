// INTENTIONAL VIOLATION FIXTURE (scanned by the gate test only).
// Two more laundered constant-only "proofs": an assertion MESSAGE (a string's
// words are text, not identifiers) and an `as` cast to a primitive type (the
// cast keyword and the type name are not symbols under test). Both exercise
// zero product code; the old alphabetic-run heuristic saw "identifiers" in
// `header`/`size`/`as`/`u32` and let them through.

#[test]
fn message_laundered_constant() {
    assert_eq!(8 + 4 + 4, 16, "header size");
}

#[test]
fn cast_laundered_constant() {
    assert_eq!((8 + 4 + 4) as u32, 16);
}
