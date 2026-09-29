//! The astream address grammar.
//!
//! Two distinct newtypes, validated in their constructors:
//!
//! * [`Subject`] — a publish target. No wildcards. e.g. `/a/stream/events`.
//! * [`Filter`] — a subscription pattern. NATS-style segment wildcards:
//!   `*` matches exactly one segment, `>` matches one-or-more trailing
//!   segments and must be the last segment. Partial-segment wildcards
//!   (`fo*`) are rejected.
//!
//! There is intentionally **no** public unchecked constructor on the publish
//! path. Both types require a leading `/` and non-empty segments.

use std::fmt;

/// Iterate the segments of a `/`-rooted path, dropping the leading empty piece:
/// exactly `path.split('/').skip(1)`, as a plain byte scan (the matcher's hot
/// loop re-splits both the filter and the subject on every call).
fn segments(path: &str) -> Segments<'_> {
    Segments {
        rest: path.find('/').map(|i| &path[i + 1..]),
    }
}

struct Segments<'a> {
    /// What follows the last `/` consumed; `None` once the final segment is out.
    rest: Option<&'a str>,
}

impl<'a> Iterator for Segments<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        let rest = self.rest?;
        // `/` is ASCII, so both slice points are char boundaries.
        match rest.bytes().position(|b| b == b'/') {
            Some(i) => {
                self.rest = Some(&rest[i + 1..]);
                Some(&rest[..i])
            }
            None => {
                self.rest = None;
                Some(rest)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Subject (publish target)
// ---------------------------------------------------------------------------

/// Why a string is not a valid [`Subject`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubjectError {
    Empty,
    MissingLeadingSlash,
    EmptySegment,
    ContainsWildcard,
    /// A segment contains a control byte (NUL, newline, tab, 0x1f, DEL, ...).
    ControlByte,
}

impl fmt::Display for SubjectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            SubjectError::Empty => "subject is empty",
            SubjectError::MissingLeadingSlash => "subject must start with '/'",
            SubjectError::EmptySegment => "subject has an empty segment",
            SubjectError::ContainsWildcard => "subject must not contain '*' or '>'",
            SubjectError::ControlByte => "subject must not contain control bytes",
        };
        f.write_str(msg)
    }
}

impl std::error::Error for SubjectError {}

/// A validated publish target. Guaranteed: starts with `/`, every segment is
/// non-empty, and no segment contains a wildcard.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Subject(String);

impl Subject {
    /// Validate and construct, or explain why the input is rejected.
    pub fn new(s: impl Into<String>) -> Result<Self, SubjectError> {
        let s = s.into();
        validate_subject(&s)?;
        Ok(Subject(s))
    }

    /// The full subject path.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// The segments, wildcard-free by construction.
    pub fn segments(&self) -> impl Iterator<Item = &str> {
        segments(&self.0)
    }
}

// ---------------------------------------------------------------------------
// Filter (subscription pattern)
// ---------------------------------------------------------------------------

/// Why a string is not a valid [`Filter`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FilterError {
    Empty,
    MissingLeadingSlash,
    EmptySegment,
    /// A wildcard char appears inside an otherwise-literal segment (`fo*`).
    PartialWildcard,
    /// `>` appeared somewhere other than the final segment.
    MultiNotLast,
    /// A segment contains a control byte (NUL, newline, tab, 0x1f, DEL, ...).
    ControlByte,
}

impl fmt::Display for FilterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            FilterError::Empty => "filter is empty",
            FilterError::MissingLeadingSlash => "filter must start with '/'",
            FilterError::EmptySegment => "filter has an empty segment",
            FilterError::PartialWildcard => "wildcards must be a whole segment ('*' or '>')",
            FilterError::MultiNotLast => "'>' must be the final segment",
            FilterError::ControlByte => "filter must not contain control bytes",
        };
        f.write_str(msg)
    }
}

impl std::error::Error for FilterError {}

/// Check every segment of a `/`-rooted pattern, reporting the first failure in
/// document order.
/// The [`Subject::new`] grammar, checked in place with no allocation.
fn validate_subject(s: &str) -> Result<(), SubjectError> {
    if s.is_empty() {
        return Err(SubjectError::Empty);
    }
    if !s.starts_with('/') {
        return Err(SubjectError::MissingLeadingSlash);
    }
    for seg in segments(s) {
        if seg.is_empty() {
            return Err(SubjectError::EmptySegment);
        }
        if seg.contains('*') || seg.contains('>') {
            return Err(SubjectError::ContainsWildcard);
        }
        if seg.bytes().any(|b| b < 0x20 || b == 0x7f) {
            return Err(SubjectError::ControlByte);
        }
    }
    Ok(())
}

fn validate_filter_segments(path: &str) -> Result<(), FilterError> {
    let mut parts = segments(path).peekable();
    while let Some(part) = parts.next() {
        if part.is_empty() {
            return Err(FilterError::EmptySegment);
        }
        match part {
            SINGLE => {}
            MULTI => {
                if parts.peek().is_some() {
                    return Err(FilterError::MultiNotLast);
                }
            }
            lit => {
                if lit.contains('*') || lit.contains('>') {
                    return Err(FilterError::PartialWildcard);
                }
                if lit.bytes().any(|b| b < 0x20 || b == 0x7f) {
                    return Err(FilterError::ControlByte);
                }
            }
        }
    }
    Ok(())
}

/// `*` — exactly one segment.
const SINGLE: &str = "*";
/// `>` — one or more trailing segments.
const MULTI: &str = ">";

/// A validated subscription pattern. It stores only the pattern string, so a
/// filter parsed from untrusted input costs its own length and nothing per
/// segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Filter {
    // Segments are re-split on use. Every segment of a validated filter is
    // exactly `*`, exactly `>` (last only), or a literal containing neither
    // character, so comparing a segment against SINGLE/MULTI classifies it.
    raw: String,
}

impl Filter {
    /// Validate and construct, or explain why the input is rejected.
    pub fn new(s: impl Into<String>) -> Result<Self, FilterError> {
        let s = s.into();
        if s.is_empty() {
            return Err(FilterError::Empty);
        }
        if !s.starts_with('/') {
            return Err(FilterError::MissingLeadingSlash);
        }
        validate_filter_segments(&s)?;
        Ok(Filter { raw: s })
    }

    /// The original pattern string.
    pub fn as_str(&self) -> &str {
        &self.raw
    }

    /// Does this filter match the given subject?
    ///
    /// Iterative, allocation-free matcher: it walks the filter and the
    /// subject's segments in lockstep. (`tests/router_differential.rs` checks it
    /// against an independently-coded recursive oracle over generated well-formed
    /// filters and subjects; the malformed and edge inputs go to the *validators*
    /// [`Filter::new`]/[`Subject::new`], whose every error variant that test
    /// reaches by construction.)
    pub fn matches(&self, subject: &Subject) -> bool {
        self.matches_segments(subject.segments())
    }

    /// Whether `subject` is a well-formed subject this filter matches: exactly
    /// `Subject::new(subject).is_ok_and(|s| self.matches(&s))`, without allocating
    /// a [`Subject`]. For scanning stored subject strings under a lock.
    pub fn matches_str(&self, subject: &str) -> bool {
        validate_subject(subject).is_ok() && self.matches_segments(segments(subject))
    }

    fn matches_segments<'a>(&self, mut subj: impl Iterator<Item = &'a str>) -> bool {
        for seg in segments(&self.raw) {
            match seg {
                // `>` matches one or more remaining segments: require at least one.
                MULTI => return subj.next().is_some(),
                SINGLE => {
                    if subj.next().is_none() {
                        return false;
                    }
                }
                lit => {
                    if subj.next() != Some(lit) {
                        return false;
                    }
                }
            }
        }
        // Filter exhausted: match iff the subject is exhausted too.
        subj.next().is_none()
    }

    /// Whether this filter **contains** `other`: every subject matching `other`
    /// also matches `self`. This is the capability-scoping primitive — a bearer
    /// granted `self` may subscribe with any `other` this contains. It is
    /// **sound** (never a false positive): where containment is uncertain it
    /// returns `false`, so an ACL built on it can only be too strict, never too
    /// permissive. `>` (1+ trailing) contains any longer or equal non-empty tail;
    /// `*` (exactly one) contains a single literal/`*` but never `>`; a literal
    /// contains only the identical literal.
    #[must_use]
    pub fn contains(&self, other: &Filter) -> bool {
        let mut b = segments(&other.raw);
        for sa in segments(&self.raw) {
            let sb = b.next();
            match sa {
                // `>` accepts every subject with at least one more segment; every
                // subject matching `other` has that iff `other` has a segment here.
                MULTI => return sb.is_some(),
                SINGLE => match sb {
                    // `other` could match a longer, variable tail here — not contained.
                    None | Some(MULTI) => return false,
                    Some(_) => {}
                },
                // A literal contains only the identical literal (never `*`/`>`,
                // which no literal equals).
                la => {
                    if sb != Some(la) {
                        return false;
                    }
                }
            }
        }
        // `self` exhausted (no trailing `>`): contained iff `other` ends here too.
        b.next().is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subject_validation() {
        assert!(Subject::new("/a/stream/events").is_ok());
        assert_eq!(Subject::new(""), Err(SubjectError::Empty));
        assert_eq!(Subject::new("a/b"), Err(SubjectError::MissingLeadingSlash));
        assert_eq!(Subject::new("/a//b"), Err(SubjectError::EmptySegment));
        assert_eq!(Subject::new("/a/"), Err(SubjectError::EmptySegment));
        assert_eq!(Subject::new("/a/*"), Err(SubjectError::ContainsWildcard));
        assert_eq!(Subject::new("/a/>"), Err(SubjectError::ContainsWildcard));
    }

    #[test]
    fn filter_validation_rejects_partial_and_misplaced_wildcards() {
        assert!(Filter::new("/a/*/c").is_ok());
        assert!(Filter::new("/a/>").is_ok());
        assert_eq!(Filter::new("/a/fo*"), Err(FilterError::PartialWildcard));
        assert_eq!(Filter::new("/a/>/c"), Err(FilterError::MultiNotLast));
        assert_eq!(Filter::new("/a//c"), Err(FilterError::EmptySegment));
        assert_eq!(Filter::new("a/b"), Err(FilterError::MissingLeadingSlash));
    }

    #[test]
    fn matching_basics() {
        let m = |f: &str, s: &str| Filter::new(f).unwrap().matches(&Subject::new(s).unwrap());
        assert!(m("/a/stream/events", "/a/stream/events"));
        assert!(!m("/a/stream/events", "/a/stream/other"));
        assert!(m("/a/*/events", "/a/stream/events"));
        assert!(!m("/a/*/events", "/a/stream/sub/events"));
        assert!(m("/a/>", "/a/stream/events"));
        assert!(m("/a/>", "/a/x"));
    }

    #[test]
    fn multi_requires_at_least_one_segment() {
        // The locked edge case: `/a/>` does NOT match `/a` alone.
        let f = Filter::new("/a/>").unwrap();
        assert!(!f.matches(&Subject::new("/a").unwrap()));
        assert!(f.matches(&Subject::new("/a/b").unwrap()));
    }

    #[test]
    fn subject_rejects_control_bytes() {
        assert!(Subject::new("/a/b").is_ok());
        assert_eq!(Subject::new("/a/\u{0}b"), Err(SubjectError::ControlByte));
        assert_eq!(Subject::new("/a/\u{1f}b"), Err(SubjectError::ControlByte));
        assert_eq!(Subject::new("/a/\u{7f}b"), Err(SubjectError::ControlByte));
        // structural errors still take precedence over the control-byte check
        assert_eq!(Subject::new("/a//\u{0}"), Err(SubjectError::EmptySegment));
    }

    #[test]
    fn filter_rejects_control_bytes() {
        assert!(Filter::new("/a/*/c").is_ok());
        assert_eq!(Filter::new("/a/\nb"), Err(FilterError::ControlByte));
        assert_eq!(Filter::new("/a/\u{1f}b"), Err(FilterError::ControlByte));
        // wildcard-structure errors keep precedence over the control-byte check
        assert_eq!(Filter::new("/a/fo*"), Err(FilterError::PartialWildcard));
    }

    #[test]
    fn segments_is_split_on_slash_skipping_the_first_piece() {
        for path in [
            "", "/", "//", "/a", "/a/", "a", "a/b", "/a//b", "/ab/c/>", "/é/ü/*", "/a/b/c/d",
        ] {
            let ours: Vec<&str> = segments(path).collect();
            let std: Vec<&str> = path.split('/').skip(1).collect();
            assert_eq!(ours, std, "{path:?}");
        }
    }

    #[test]
    fn matches_str_is_new_then_matches_without_the_allocation() {
        let filters = ["/a/>", "/a/*", "/a/b", "/*/b/>", "/a/*/c", "/>"];
        let subjects = [
            "/a",
            "/a/b",
            "/a/b/c",
            "/a/x/c",
            "/b/b/z",
            "/a/b/",
            "",
            "a/b",
            "//",
            "/a//b",
            "/a/*",
            "/a/>",
            "/a/b\u{7f}",
            "/a/\u{1}",
            "/\u{e9}/b/c",
        ];
        for f in filters {
            let filter = Filter::new(f).unwrap();
            for s in subjects {
                let slow = Subject::new(s).is_ok_and(|subj| filter.matches(&subj));
                assert_eq!(filter.matches_str(s), slow, "filter {f:?}, subject {s:?}");
            }
        }
    }

    #[test]
    fn a_filter_costs_its_pattern_and_nothing_per_segment() {
        // A filter is parsed from untrusted input (a Subscribe, a capability
        // grant) up to the 16 MiB frame cap. Its footprint must be the pattern
        // string alone: no per-segment vector entry or heap string, which for
        // `/a/a/a...` would multiply the input many times over.
        assert_eq!(std::mem::size_of::<Filter>(), std::mem::size_of::<String>());
        assert_eq!(
            std::mem::size_of::<Subject>(),
            std::mem::size_of::<String>()
        );

        let pattern = "/a".repeat(1 << 20); // a million one-byte segments
        let f = Filter::new(pattern.clone()).unwrap();
        assert_eq!(
            f.raw.capacity(),
            pattern.len(),
            "the input is kept, not grown"
        );
        // ... and it still matches exactly its own subject, and nothing shorter.
        assert!(f.matches(&Subject::new(pattern.clone()).unwrap()));
        assert!(!f.matches(&Subject::new(&pattern[..pattern.len() - 2]).unwrap()));
        let wide = Filter::new(format!("{}/>", &pattern[..pattern.len() - 2])).unwrap();
        assert!(wide.contains(&f));
        assert!(!f.contains(&wide));
    }

    #[test]
    fn single_requires_exactly_one_segment() {
        let f = Filter::new("/a/*").unwrap();
        assert!(f.matches(&Subject::new("/a/b").unwrap()));
        assert!(!f.matches(&Subject::new("/a").unwrap()));
        assert!(!f.matches(&Subject::new("/a/b/c").unwrap()));
    }
}
