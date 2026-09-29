//! Differential property testing for the [`Filter`] matcher and the
//! [`Filter`] / [`Subject`] validators.
//!
//! The production matcher (`Filter::matches`) is *iterative*. This file
//! re-implements the same NATS-style semantics with a deliberately different
//! control structure — a *recursive* oracle — and asserts the two agree. If the
//! optimized matcher ever diverges from the spec, this test fails.
//!
//! What the generators actually produce (so nobody has to guess):
//!
//! * **Agreement** (`matcher_agrees_with_oracle`): *well-formed* filters of
//!   1..=8 segments, each a literal from a 5-token alphabet (`a`, `b`, `c`,
//!   `ab`, `abc` — prefix-colliding, so "starts with" is not "equals") or `*`,
//!   with an optional trailing `>`; and well-formed subjects of 1..=10 literal
//!   segments. Malformed input never reaches the oracle: it does not define
//!   semantics for it and neither does the matcher.
//! * **Instantiation** (`accepted_filter_matches_a_subject_built_from_it`):
//!   every generated well-formed filter must match the subject obtained by
//!   substituting a literal for each `*` and two literals for `>`.
//! * **Validation** (`structured_malformed_inputs_get_the_exact_error` and the
//!   exhaustive `every_validation_error_variant_is_reached`): *structured*
//!   malformed inputs — 0..=8 segments drawn from `{literal, *, >, fo*, "",
//!   control byte}` joined with `/`, with or without the leading slash — and the
//!   assertion is the **exact** `FilterError` / `SubjectError` variant the spec
//!   prescribes (first failure in document order), not merely `is_err()`. The
//!   exhaustive test enumerates every combination up to 3 segments and checks
//!   that every variant of both enums is reached at least once.
//! * **No-panic sweep** (`constructors_never_panic_on_arbitrary_input`):
//!   arbitrary strings of 0..=40 Unicode scalars. This reaches almost nothing
//!   past `Empty` / `MissingLeadingSlash` (the chance a sample even starts
//!   with `/` is tiny) and is kept only as a crash sweep; the structured tests
//!   above are what cover the error branches.
//!
//! The error branches are reached *by construction*, not by luck.

use astream_wire::{Filter, FilterError, Subject, SubjectError};
use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Matching oracle
// ---------------------------------------------------------------------------

/// Independent recursive oracle over segment slices. `filter` segments use the
/// literal tokens `"*"` and `">"`; everything else is a literal match. Assumes
/// `>` only appears last (the generator guarantees it for the agreement test).
fn oracle(filter: &[&str], subject: &[&str]) -> bool {
    match filter.split_first() {
        None => subject.is_empty(),
        Some((&">", _rest)) => !subject.is_empty(),
        Some((&"*", rest)) => match subject.split_first() {
            Some((_, srest)) => oracle(rest, srest),
            None => false,
        },
        Some((&lit, rest)) => match subject.split_first() {
            Some((s0, srest)) if *s0 == lit => oracle(rest, srest),
            _ => false,
        },
    }
}

/// Literal alphabet for the agreement test. Small enough that match / no-match
/// are both reachable; includes prefix-colliding tokens (`a` / `ab` / `abc`) so
/// a "starts-with" bug would not pass as "equals".
const LITERALS: &[&str] = &["a", "b", "c", "ab", "abc"];

fn literal() -> impl Strategy<Value = String> {
    prop::sample::select(LITERALS).prop_map(String::from)
}

/// Deepest filter the agreement generator produces (segments before an optional `>`).
const MAX_FILTER_SEGS: usize = 8;
/// Deepest subject the agreement generator produces.
const MAX_SUBJECT_SEGS: usize = 10;

/// A valid filter as its segment vector. `>` (if present) is forced last.
fn valid_filter_segs() -> impl Strategy<Value = Vec<String>> {
    let seg = prop_oneof![literal(), Just("*".to_string())];
    (
        prop::collection::vec(seg, 1..=MAX_FILTER_SEGS),
        any::<bool>(),
    )
        .prop_map(|(mut segs, trailing_multi)| {
            if trailing_multi {
                segs.push(">".to_string());
            }
            segs
        })
}

fn valid_subject_segs() -> impl Strategy<Value = Vec<String>> {
    prop::collection::vec(literal(), 1..=MAX_SUBJECT_SEGS)
}

fn join(segs: &[String]) -> String {
    let mut s = String::new();
    for seg in segs {
        s.push('/');
        s.push_str(seg);
    }
    s
}

/// The subject a well-formed filter "was built from": each `*` becomes one
/// literal, a trailing `>` becomes two (it needs at least one).
fn instantiate(fsegs: &[String]) -> Vec<String> {
    let mut out = Vec::with_capacity(fsegs.len() + 1);
    for seg in fsegs {
        match seg.as_str() {
            "*" => out.push("a".to_string()),
            ">" => {
                out.push("a".to_string());
                out.push("b".to_string());
            }
            lit => out.push(lit.to_string()),
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Validation oracle: the spec for Filter::new / Subject::new, transcribed
// independently (first failure in document order).
// ---------------------------------------------------------------------------

/// Segment tokens for the structured malformed generator. Each one is aimed at
/// a specific validator branch.
const TOKENS: &[&str] = &["a", "b", "*", ">", "fo*", "", "a\u{1}"];

fn token() -> impl Strategy<Value = String> {
    prop::sample::select(TOKENS).prop_map(String::from)
}

/// Join `segs` with `/`, with or without the leading slash. (With `leading`
/// false and an empty first segment the result still starts with `/` — the
/// oracle below judges the *string*, so that is handled, not special-cased.)
fn join_structured(segs: &[String], leading: bool) -> String {
    let mut s = String::new();
    for (i, seg) in segs.iter().enumerate() {
        if i > 0 || leading {
            s.push('/');
        }
        s.push_str(seg);
    }
    s
}

fn has_control(seg: &str) -> bool {
    seg.bytes().any(|b| b < 0x20 || b == 0x7f)
}

fn has_wildcard(seg: &str) -> bool {
    seg.contains('*') || seg.contains('>')
}

/// Expected result of `Filter::new(s)`: `Ok` or the exact error variant.
fn expect_filter(s: &str) -> Result<(), FilterError> {
    if s.is_empty() {
        return Err(FilterError::Empty);
    }
    let Some(rest) = s.strip_prefix('/') else {
        return Err(FilterError::MissingLeadingSlash);
    };
    let segs: Vec<&str> = rest.split('/').collect();
    let last = segs.len() - 1;
    for (i, seg) in segs.iter().enumerate() {
        if seg.is_empty() {
            return Err(FilterError::EmptySegment);
        }
        match *seg {
            "*" => {}
            ">" if i == last => {}
            ">" => return Err(FilterError::MultiNotLast),
            lit if has_wildcard(lit) => return Err(FilterError::PartialWildcard),
            lit if has_control(lit) => return Err(FilterError::ControlByte),
            _ => {}
        }
    }
    Ok(())
}

/// Expected result of `Subject::new(s)`: `Ok` or the exact error variant.
fn expect_subject(s: &str) -> Result<(), SubjectError> {
    if s.is_empty() {
        return Err(SubjectError::Empty);
    }
    let Some(rest) = s.strip_prefix('/') else {
        return Err(SubjectError::MissingLeadingSlash);
    };
    for seg in rest.split('/') {
        if seg.is_empty() {
            return Err(SubjectError::EmptySegment);
        }
        if has_wildcard(seg) {
            return Err(SubjectError::ContainsWildcard);
        }
        if has_control(seg) {
            return Err(SubjectError::ControlByte);
        }
    }
    Ok(())
}

/// Assert both constructors return exactly what the spec prescribes for `s`,
/// and that a string BOTH accept is matched by its own filter (reflexivity).
fn check_validation(s: &str) -> Result<(), TestCaseError> {
    let filter = Filter::new(s);
    let subject = Subject::new(s);
    prop_assert_eq!(
        filter.as_ref().map(|_| ()).map_err(Clone::clone),
        expect_filter(s),
        "Filter::new({:?})",
        s
    );
    prop_assert_eq!(
        subject.as_ref().map(|_| ()).map_err(Clone::clone),
        expect_subject(s),
        "Subject::new({:?})",
        s
    );
    if let (Ok(f), Ok(sub)) = (filter, subject) {
        prop_assert!(f.matches(&sub), "exact filter {:?} must match itself", s);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------

proptest! {
    /// The production matcher agrees with the independent oracle over
    /// well-formed filters (1..=8 segments + optional `>`) and subjects
    /// (1..=10 segments) drawn from the prefix-colliding alphabet.
    #[test]
    fn matcher_agrees_with_oracle(
        fsegs in valid_filter_segs(),
        ssegs in valid_subject_segs(),
    ) {
        let filter = Filter::new(join(&fsegs)).expect("generator yields valid filters");
        let subject = Subject::new(join(&ssegs)).expect("generator yields valid subjects");

        let f_refs: Vec<&str> = fsegs.iter().map(String::as_str).collect();
        let s_refs: Vec<&str> = ssegs.iter().map(String::as_str).collect();

        prop_assert_eq!(filter.matches(&subject), oracle(&f_refs, &s_refs));
    }

    /// Every accepted filter matches the subject it was built from (each `*`
    /// instantiated to one literal, `>` to two) — both in the matcher and in
    /// the oracle.
    #[test]
    fn accepted_filter_matches_a_subject_built_from_it(fsegs in valid_filter_segs()) {
        let filter = Filter::new(join(&fsegs)).expect("generator yields valid filters");
        let ssegs = instantiate(&fsegs);
        let subject = Subject::new(join(&ssegs)).expect("instantiation yields a valid subject");
        prop_assert!(filter.matches(&subject), "{} must match {}", filter.as_str(), subject.as_str());

        let f_refs: Vec<&str> = fsegs.iter().map(String::as_str).collect();
        let s_refs: Vec<&str> = ssegs.iter().map(String::as_str).collect();
        prop_assert!(oracle(&f_refs, &s_refs));
    }

    /// Structured malformed inputs — 0..=8 segments from
    /// `{a, b, *, >, fo*, "", control-byte}` with or without the leading slash —
    /// produce the EXACT `FilterError` / `SubjectError` variant the spec
    /// prescribes (inner `>` is `MultiNotLast`, `fo*` is `PartialWildcard`, an
    /// empty segment is `EmptySegment`, ...), and a string both constructors
    /// accept is matched by its own filter.
    #[test]
    fn structured_malformed_inputs_get_the_exact_error(
        segs in prop::collection::vec(token(), 0..=8),
        leading in any::<bool>(),
    ) {
        check_validation(&join_structured(&segs, leading))?;
    }

    /// Arbitrary strings must never panic the constructors. This is a crash
    /// sweep only: it practically never reaches past `Empty` /
    /// `MissingLeadingSlash` (see the module doc), so it asserts nothing about
    /// WHICH error is returned — the structured tests above do that.
    #[test]
    fn constructors_never_panic_on_arbitrary_input(raw in ".{0,40}") {
        check_validation(&raw)?;
    }

    /// A wildcard-free filter built from a subject's exact path matches it
    /// (reflexivity of exact patterns).
    #[test]
    fn exact_filter_matches_its_own_subject(ssegs in valid_subject_segs()) {
        let path = join(&ssegs);
        let subject = Subject::new(path.clone()).unwrap();
        let filter = Filter::new(path).unwrap();
        prop_assert!(filter.matches(&subject));
    }
}

/// Exhaustively enumerate every structured input of 0..=3 segments over
/// `TOKENS`, with and without the leading slash, assert the exact variant for
/// each, and prove every variant of BOTH error enums was reached at least once
/// — so a regression in any branch (`/>/a`, `/a/*b`, `/a//b`, ...) fails here
/// rather than depending on what proptest happened to draw.
#[test]
fn every_validation_error_variant_is_reached() {
    let mut inputs: Vec<String> = Vec::new();
    let mut prefixes: Vec<Vec<String>> = vec![Vec::new()];
    for _ in 0..=3 {
        for segs in &prefixes {
            inputs.push(join_structured(segs, true));
            inputs.push(join_structured(segs, false));
        }
        prefixes = prefixes
            .iter()
            .flat_map(|p| {
                TOKENS.iter().map(move |t| {
                    let mut q = p.clone();
                    q.push((*t).to_string());
                    q
                })
            })
            .collect();
    }

    let mut filter_seen: Vec<FilterError> = Vec::new();
    let mut subject_seen: Vec<SubjectError> = Vec::new();
    let mut filter_ok = 0usize;
    let mut subject_ok = 0usize;
    for s in &inputs {
        check_validation(s).unwrap_or_else(|e| panic!("{e}"));
        match expect_filter(s) {
            Ok(()) => filter_ok += 1,
            Err(e) if !filter_seen.contains(&e) => filter_seen.push(e),
            Err(_) => {}
        }
        match expect_subject(s) {
            Ok(()) => subject_ok += 1,
            Err(e) if !subject_seen.contains(&e) => subject_seen.push(e),
            Err(_) => {}
        }
    }

    for want in [
        FilterError::Empty,
        FilterError::MissingLeadingSlash,
        FilterError::EmptySegment,
        FilterError::PartialWildcard,
        FilterError::MultiNotLast,
        FilterError::ControlByte,
    ] {
        assert!(
            filter_seen.contains(&want),
            "FilterError::{want:?} never reached"
        );
    }
    for want in [
        SubjectError::Empty,
        SubjectError::MissingLeadingSlash,
        SubjectError::EmptySegment,
        SubjectError::ContainsWildcard,
        SubjectError::ControlByte,
    ] {
        assert!(
            subject_seen.contains(&want),
            "SubjectError::{want:?} never reached"
        );
    }
    assert!(
        filter_ok > 0 && subject_ok > 0,
        "accepting branch never reached"
    );
}

#[test]
fn locked_edge_cases() {
    // `>` needs at least one segment; `*` needs exactly one.
    assert!(!Filter::new("/a/>")
        .unwrap()
        .matches(&Subject::new("/a").unwrap()));
    assert!(Filter::new("/a/>")
        .unwrap()
        .matches(&Subject::new("/a/b/c").unwrap()));
    assert!(!Filter::new("/a/*")
        .unwrap()
        .matches(&Subject::new("/a/b/c").unwrap()));

    // Malformed patterns are rejected with the specific reason, not coerced.
    assert_eq!(Filter::new("/a/>/b"), Err(FilterError::MultiNotLast));
    assert_eq!(Filter::new("/>/a"), Err(FilterError::MultiNotLast));
    assert_eq!(Filter::new("/a/fo*"), Err(FilterError::PartialWildcard));
    assert_eq!(Filter::new("/a/*b"), Err(FilterError::PartialWildcard));
    assert_eq!(Filter::new("/a//b"), Err(FilterError::EmptySegment));
    assert_eq!(Filter::new("/"), Err(FilterError::EmptySegment));
    assert_eq!(Subject::new("/a/>"), Err(SubjectError::ContainsWildcard));

    // Prefix-colliding literals are not "starts-with" matches.
    assert!(!Filter::new("/a")
        .unwrap()
        .matches(&Subject::new("/ab").unwrap()));
    assert!(!Filter::new("/ab")
        .unwrap()
        .matches(&Subject::new("/a").unwrap()));
}
