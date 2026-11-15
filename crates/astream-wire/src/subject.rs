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

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "subject_island.rs"]
mod subject_island;
#[cfg(not(clean_islands))]
pub use crate::twins::segment_depth_advance;
#[cfg(clean_islands)]
pub use subject_island::segment_depth_advance;

contract_fn! {
    /// Whether a filter prefix of depth `filter_prefix_depth` can match or contain a
    /// subject/filter of depth `subject_depth` (`filter_prefix_depth <= subject_depth`).
    ///
    /// Verified against `Astream.Wire.TlaSubjectFilter.filter_depth_contains_isl` by
    /// `clean-kernel-defeq`.
    pub const fn filter_depth_contains(filter_prefix_depth: u64, subject_depth: u64) -> bool
    clauses [ensures result == (filter_prefix_depth <= subject_depth)]
    {
        filter_prefix_depth <= subject_depth
    }
}

const fn find_slash(mut rest: &[u8]) -> Option<usize> {
    let mut idx = 0usize;
    while let &[b, ref tail @ ..] = rest {
        if b == b'/' {
            return Some(idx);
        }
        idx = idx.saturating_add(1);
        rest = tail;
    }
    None
}

/// Iterate the segments of a `/`-rooted path, dropping the leading empty piece:
/// exactly `path.split('/').skip(1)`, as a plain byte scan (the matcher's hot
/// loop re-splits both the filter and the subject on every call).
fn segments(path: &str) -> Segments<'_> {
    let rest = match find_slash(path.as_bytes()) {
        Some(i) => match i.checked_add(1) {
            Some(next) => path.get(next..),
            None => None,
        },
        None => None,
    };
    Segments { rest }
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
        match find_slash(rest.as_bytes()) {
            Some(i) => {
                self.rest = match i.checked_add(1) {
                    Some(next) => rest.get(next..),
                    None => None,
                };
                rest.get(..i)
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

impl SubjectError {
    /// Static human-readable description of the subject validation error.
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            SubjectError::Empty => "subject is empty",
            SubjectError::MissingLeadingSlash => "subject must start with '/'",
            SubjectError::EmptySegment => "subject has an empty segment",
            SubjectError::ContainsWildcard => "subject must not contain '*' or '>'",
            SubjectError::ControlByte => "subject must not contain control bytes",
        }
    }
}

impl fmt::Display for SubjectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
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
        match validate_subject(&s) {
            Ok(()) => Ok(Subject(s)),
            Err(e) => Err(e),
        }
    }

    /// The full subject path.
    #[must_use]
    pub const fn as_str(&self) -> &str {
        self.0.as_str()
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

impl FilterError {
    /// Static human-readable description of the filter validation error.
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            FilterError::Empty => "filter is empty",
            FilterError::MissingLeadingSlash => "filter must start with '/'",
            FilterError::EmptySegment => "filter has an empty segment",
            FilterError::PartialWildcard => "wildcards must be a whole segment ('*' or '>')",
            FilterError::MultiNotLast => "'>' must be the final segment",
            FilterError::ControlByte => "filter must not contain control bytes",
        }
    }
}

impl fmt::Display for FilterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl std::error::Error for FilterError {}

/// Check every segment of a `/`-rooted pattern, reporting the first failure in
/// document order.
/// The [`Subject::new`] grammar, checked in place with no allocation and a single
/// byte scan per segment.
pub const fn validate_subject(s: &str) -> Result<(), SubjectError> {
    let bytes = s.as_bytes();
    let &[first, ref after_slash @ ..] = bytes else {
        return Err(SubjectError::Empty);
    };
    if first != b'/' {
        return Err(SubjectError::MissingLeadingSlash);
    }
    let mut rest = after_slash;
    let mut seg_len = 0usize;
    let mut seg_has_ctrl = false;
    while let &[b, ref tail @ ..] = rest {
        if b == b'/' {
            if seg_len == 0 {
                return Err(SubjectError::EmptySegment);
            }
            if seg_has_ctrl {
                return Err(SubjectError::ControlByte);
            }
            seg_len = 0;
            seg_has_ctrl = false;
        } else if b == b'*' || b == b'>' {
            return Err(SubjectError::ContainsWildcard);
        } else {
            if b < 0x20 || b == 0x7f {
                seg_has_ctrl = true;
            }
            seg_len = seg_len.saturating_add(1);
        }
        rest = tail;
    }
    if seg_len == 0 {
        return Err(SubjectError::EmptySegment);
    }
    if seg_has_ctrl {
        return Err(SubjectError::ControlByte);
    }
    Ok(())
}

/// Validate a `/`-rooted subscription filter string in place.
pub const fn validate_filter_str(path: &str) -> Result<(), FilterError> {
    let bytes = path.as_bytes();
    let &[first, ref after_slash @ ..] = bytes else {
        return Err(FilterError::Empty);
    };
    if first != b'/' {
        return Err(FilterError::MissingLeadingSlash);
    }
    let mut rest = after_slash;
    let mut seg_len = 0usize;
    let mut seg_wild = 0u8;
    let mut seg_has_ctrl = false;
    while let &[b, ref tail @ ..] = rest {
        if b == b'/' {
            if seg_len == 0 {
                return Err(FilterError::EmptySegment);
            }
            if seg_len == 1 && seg_wild == b'>' {
                return Err(FilterError::MultiNotLast);
            }
            if seg_wild != 0 && !(seg_len == 1 && seg_wild == b'*') {
                return Err(FilterError::PartialWildcard);
            }
            if seg_has_ctrl {
                return Err(FilterError::ControlByte);
            }
            seg_len = 0;
            seg_wild = 0;
            seg_has_ctrl = false;
        } else {
            if b == b'*' || b == b'>' {
                seg_wild = b;
            } else if b < 0x20 || b == 0x7f {
                seg_has_ctrl = true;
            }
            seg_len = seg_len.saturating_add(1);
        }
        rest = tail;
    }
    if seg_len == 0 {
        return Err(FilterError::EmptySegment);
    }
    if seg_len == 1 && (seg_wild == b'*' || seg_wild == b'>') {
        return Ok(());
    }
    if seg_wild != 0 {
        return Err(FilterError::PartialWildcard);
    }
    if seg_has_ctrl {
        return Err(FilterError::ControlByte);
    }
    Ok(())
}

const fn skip_to_after_slash(mut rem: &[u8]) -> Option<&[u8]> {
    while let &[b, ref tail @ ..] = rem {
        if b == b'/' {
            return Some(tail);
        }
        rem = tail;
    }
    None
}

#[derive(Clone, Copy)]
enum LiteralStep<'a, 'b> {
    BothEnded,
    BothContinue(&'a [u8], &'b [u8]),
    Mismatch,
}

const fn step_literal_segment<'a, 'b>(a: &'a [u8], b: &'b [u8]) -> LiteralStep<'a, 'b> {
    let mut ar = a;
    let mut br = b;
    while let &[ba, ref ta @ ..] = ar {
        let &[bb, ref tb @ ..] = br else {
            return LiteralStep::Mismatch;
        };
        if ba == b'/' && bb == b'/' {
            return LiteralStep::BothContinue(ta, tb);
        }
        if ba == b'/' || bb == b'/' || ba != bb {
            return LiteralStep::Mismatch;
        }
        ar = ta;
        br = tb;
    }
    if br.is_empty() {
        LiteralStep::BothEnded
    } else {
        LiteralStep::Mismatch
    }
}

const fn filter_matches_after_slash(mut f_rem: &[u8], mut s_rem: &[u8]) -> bool {
    loop {
        match f_rem {
            b">" => return true,
            b"*" => return skip_to_after_slash(s_rem).is_none(),
            &[b'*', b'/', ref f_next @ ..] => {
                let Some(s_next) = skip_to_after_slash(s_rem) else {
                    return false;
                };
                f_rem = f_next;
                s_rem = s_next;
            }
            _ => match step_literal_segment(f_rem, s_rem) {
                LiteralStep::BothEnded => return true,
                LiteralStep::BothContinue(f_next, s_next) => {
                    f_rem = f_next;
                    s_rem = s_next;
                }
                LiteralStep::Mismatch => return false,
            },
        }
    }
}

const fn filter_contains_after_slash(mut a_rem: &[u8], mut b_rem: &[u8]) -> bool {
    loop {
        match a_rem {
            b">" => return true,
            b"*" => {
                return !matches!(b_rem, b">") && skip_to_after_slash(b_rem).is_none();
            }
            &[b'*', b'/', ref a_next @ ..] => {
                if matches!(b_rem, b">" | &[b'>', b'/', ..]) {
                    return false;
                }
                let Some(b_next) = skip_to_after_slash(b_rem) else {
                    return false;
                };
                a_rem = a_next;
                b_rem = b_next;
            }
            _ => match step_literal_segment(a_rem, b_rem) {
                LiteralStep::BothEnded => return true,
                LiteralStep::BothContinue(a_next, b_next) => {
                    a_rem = a_next;
                    b_rem = b_next;
                }
                LiteralStep::Mismatch => return false,
            },
        }
    }
}

/// A validated subscription pattern. It stores only the pattern string, so a
/// filter parsed from untrusted input costs its own length and nothing per
/// segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Filter {
    // Segments are re-split on use. Every segment of a validated filter is
    // exactly `*`, exactly `>` (last only), or a literal containing neither
    // character, so comparing a segment against `*`/`>` classifies it.
    raw: String,
}

impl Filter {
    /// Validate and construct, or explain why the input is rejected.
    pub fn new(s: impl Into<String>) -> Result<Self, FilterError> {
        let s = s.into();
        match validate_filter_str(&s) {
            Ok(()) => Ok(Filter { raw: s }),
            Err(e) => Err(e),
        }
    }

    /// The original pattern string.
    #[must_use]
    pub const fn as_str(&self) -> &str {
        self.raw.as_str()
    }

    /// Does this filter match the given subject?
    ///
    /// Iterative, allocation-free matcher: it walks the filter and the
    /// subject's segments in lockstep. (`tests/suite/router_differential.rs` checks it
    /// against an independently-coded recursive oracle over generated well-formed
    /// filters and subjects; the malformed and edge inputs go to the *validators*
    /// [`Filter::new`]/[`Subject::new`], whose every error variant that test
    /// reaches by construction.)
    #[must_use]
    pub const fn matches(&self, subject: &Subject) -> bool {
        let &[b'/', ref f_after @ ..] = self.raw.as_bytes() else {
            return false;
        };
        let &[b'/', ref s_after @ ..] = subject.0.as_bytes() else {
            return false;
        };
        filter_matches_after_slash(f_after, s_after)
    }

    /// Whether `subject` is a well-formed subject this filter matches: exactly
    /// `Subject::new(subject).is_ok_and(|s| self.matches(&s))`, without allocating
    /// a [`Subject`]. For scanning stored subject strings under a lock.
    ///
    /// Checks segment matching first so non-matching subjects short-circuit on the
    /// first mismatched literal segment without scanning the rest of `subject`.
    #[must_use]
    pub const fn matches_str(&self, subject: &str) -> bool {
        let &[b'/', ref f_after @ ..] = self.raw.as_bytes() else {
            return false;
        };
        let &[b'/', ref s_after @ ..] = subject.as_bytes() else {
            return false;
        };
        filter_matches_after_slash(f_after, s_after) && matches!(validate_subject(subject), Ok(()))
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
    pub const fn contains(&self, other: &Filter) -> bool {
        let &[b'/', ref a_after @ ..] = self.raw.as_bytes() else {
            return false;
        };
        let &[b'/', ref b_after @ ..] = other.raw.as_bytes() else {
            return false;
        };
        filter_contains_after_slash(a_after, b_after)
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

    #[test]
    fn clean_origin_segment_depth_and_containment_guards() {
        assert_eq!(segment_depth_advance(3, 1), 3);
        assert_eq!(segment_depth_advance(3, 3), 3);
        assert_eq!(segment_depth_advance(3, 5), 5);
        assert!(filter_depth_contains(2, 2));
        assert!(filter_depth_contains(2, 4));
        assert!(!filter_depth_contains(4, 2));
    }
}
