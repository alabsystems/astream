// INTENTIONAL VIOLATION FIXTURE (scanned by the gate test only).
// Laundered constant-only "proofs": a type suffix (`8u8`) used to be enough to
// fool the tautology lint into seeing an "identifier", and a bool-only assert
// was never flagged at all. Both exercise zero product code.

#[test]
fn suffix_laundered_constant() {
    assert_eq!(8u8 + 4u8 + 4u8, 16u8);
}

#[test]
fn bool_only_constant() {
    assert!(true);
}
