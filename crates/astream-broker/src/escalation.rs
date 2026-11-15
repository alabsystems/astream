// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! THE ESCALATION TABLE: which records the broker flushes IN FULL before it shows or
//! acks them, on a tier whose ordinary ack does not wait for a full flush
//! ([`Durability::Ordered`](crate::Durability::Ordered) and
//! [`Durability::Relaxed`](crate::Durability::Relaxed)).
//!
//! The table is DATA the embedder hands the open ([`OpenOptions::escalation`]), matched
//! by the broker as each record is staged — never a flag a client sets on its request.
//! That is the whole point of putting it here: the broker decides, so a record an OLDER
//! client writes (one that has never heard of escalation) is escalated exactly like a
//! new one's. No request tag, no protocol version and no error code are spent on it.
//!
//! Three kinds of rule, each a reason a record must survive a power loss:
//!
//! - [`Escalate::Subject`]: the record's subject matches the filter (the
//!   `astream_wire::Filter` grammar). Catches a record by WHERE it goes, whoever wrote
//!   it — including a writer with no bound principal (an unbound root grant).
//! - [`Escalate::PrincipalPrefix`]: the producer that wrote it is BOUND
//!   ([`BrokerLog::binding`](crate::BrokerLog::binding), which counts a bind staged
//!   earlier in the same batch) to a principal starting with the prefix. Catches a
//!   record by WHO wrote it. On a broker that binds nobody (an unguarded one) this rule
//!   sees nothing.
//! - [`Escalate::Group`]: the record carries a consumer-group commit whose group
//!   matches the filter. The ONLY rule that sees a pure commit record, which is hidden
//!   (`/a/commit`) and written by producer 0.
//!
//! Hidden subjects (`/a/commit`, `/a/will`, `/a/bind`, `/a/retire`) are never matched by
//! the first two rules: they are the broker's own bookkeeping, and a subject filter as
//! broad as `>` must not drag every will registration into a full flush.
//!
//! Why a table and not a closure: the broker's shared state holds no caller-supplied
//! `dyn Fn` on purpose (an open principal for Trust's thread-spawn census, see
//! `Shared`), and a table built from data can be assembled at run time (from a
//! configuration, say) as easily as written in code: [`parse_escalation_file`] reads one
//! from text, the form astream keeps aterm's table and horizon in
//! (`tests/fixtures/aterm-broker.escalate`, which aterm's own tests hold equal to the table
//! it opens with). `asb serve` takes no table: on an `asb` broker every record rides the
//! tier's own promise.
//!
//! [`OpenOptions::escalation`]: crate::OpenOptions::escalation

use std::io;
use std::time::Duration;

use astream_wire::Filter;

use crate::store::is_hidden_subject;

/// One escalation rule — see the module docs.
#[non_exhaustive]
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Debug, Clone, Eq, Hash)]
pub enum Escalate {
    /// Records whose subject matches this filter (hidden subjects excepted).
    Subject(String),
    /// Records written by a producer bound to a principal starting with this prefix
    /// (hidden subjects excepted). An empty prefix is refused at the open: it would
    /// escalate every bound producer, and reads as a forgotten argument.
    PrincipalPrefix(String),
    /// Records carrying a consumer-group commit whose group matches this filter.
    Group(String),
}

impl PartialEq for Escalate {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Escalate::Subject(a), Escalate::Subject(b)) => a.as_str() == b.as_str(),
            (Escalate::PrincipalPrefix(a), Escalate::PrincipalPrefix(b)) => {
                a.as_str() == b.as_str()
            }
            (Escalate::Group(a), Escalate::Group(b)) => a.as_str() == b.as_str(),
            _ => false,
        }
    }
}

/// An escalation table: the rules a log is opened with ([`OpenOptions`]), checked when
/// the log opens (a filter that does not parse refuses the open, naming it) and in force
/// from its first batch on. The default is empty: nothing is escalated.
///
/// [`OpenOptions`]: crate::OpenOptions
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Escalation {
    rules: Vec<Escalate>,
}

impl Escalation {
    /// A table of `rules`.
    pub fn new(rules: impl IntoIterator<Item = Escalate>) -> Escalation {
        let mut out = Vec::new();
        for r in rules {
            out.push(r);
        }
        Escalation { rules: out }
    }

    /// The rules, in the order given.
    #[must_use]
    pub fn rules(&self) -> &[Escalate] {
        &self.rules
    }

    /// Whether the table has no rules.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// Parse every rule, refusing the first that is not one (`InvalidInput`, naming it).
    pub(crate) fn compile(&self) -> io::Result<Rules> {
        let mut rules = Rules::default();
        for rule in &self.rules {
            match rule {
                Escalate::Subject(raw) => match Filter::new(raw) {
                    Ok(f) => rules.subjects.push(f),
                    Err(e) => {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("escalation rule Subject({raw:?}) is not a filter: {e:?}"),
                        ))
                    }
                },
                Escalate::Group(raw) => match Filter::new(raw) {
                    Ok(f) => rules.groups.push(f),
                    Err(e) => {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            format!("escalation rule Group({raw:?}) is not a filter: {e:?}"),
                        ))
                    }
                },
                Escalate::PrincipalPrefix(prefix) if prefix.is_empty() => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "escalation rule PrincipalPrefix(\"\") would escalate every bound \
                         producer: name the prefix",
                    ))
                }
                Escalate::PrincipalPrefix(prefix) => rules.prefixes.push(prefix.clone()),
            }
        }
        rules.count = u16::try_from(self.rules.len()).unwrap_or(u16::MAX);
        Ok(rules)
    }
}

/// The machine-readable reason an escalation file was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum EscalationParseKind {
    /// A rule has an unknown name or not exactly one argument.
    Syntax,
    /// A rule or the complete table is refused by the broker's open validation.
    InvalidRule,
    /// A horizon is not a representable whole number of milliseconds.
    InvalidHorizon,
    /// A second horizon was supplied.
    DuplicateHorizon,
}

/// An escalation-file refusal, with its source line and reason independent of its wording.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EscalationParseError {
    line: Option<usize>,
    kind: EscalationParseKind,
    detail: String,
}

impl EscalationParseError {
    fn at(line: usize, kind: EscalationParseKind, detail: String) -> Self {
        Self {
            line: Some(line),
            kind,
            detail,
        }
    }

    /// The one-based line of a refusal, or none for a whole-table refusal.
    #[must_use]
    pub const fn line(&self) -> Option<usize> {
        self.line
    }

    /// The refusal's machine-readable reason.
    #[must_use]
    pub const fn kind(&self) -> EscalationParseKind {
        self.kind
    }
}

impl std::fmt::Display for EscalationParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(line) = self.line {
            write!(f, "line {line}: ")?;
        }
        f.write_str(&self.detail)
    }
}

impl std::error::Error for EscalationParseError {}

/// An ESCALATION FILE: a table as text, one rule per line in its order, each a word and its
/// argument split on spaces: `subject <filter>` ([`Escalate::Subject`]), `principal
/// <prefix>` ([`Escalate::PrincipalPrefix`]) or `group <filter>` ([`Escalate::Group`]), so
/// neither a filter nor a prefix with a space in it can be written here. Blank lines and `#`
/// comments are skipped. At most one `horizon=<n>ms` line names the Ordered horizon the table
/// is served with (`Durability::Ordered { horizon }`); the table itself never reads it.
///
/// Returns the table, in the file's order, and the horizon (`None` without that line). Each
/// rule is refused where the open would refuse it (a filter that does not parse; an empty
/// prefix, which this grammar cannot spell), and the table is checked whole as the open
/// checks it, so a file this answers `Ok` for is a table the open takes. A line's refusal
/// carries its one-based line; a whole-table refusal has none.
pub fn parse_escalation_file(
    text: &str,
) -> Result<(Escalation, Option<Duration>), EscalationParseError> {
    let mut rules = Vec::new();
    let mut horizon = None;
    for (i, line) in text.lines().enumerate() {
        let n = i.saturating_add(1);
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(v) = line.strip_prefix("horizon=") {
            if horizon.is_some() {
                return Err(EscalationParseError::at(
                    n,
                    EscalationParseKind::DuplicateHorizon,
                    "a second horizon".into(),
                ));
            }
            horizon = Some(parse_horizon(v).map_err(|e| {
                EscalationParseError::at(n, EscalationParseKind::InvalidHorizon, e)
            })?);
            continue;
        }
        let rule = parse_escalation_line(line)
            .map_err(|e| EscalationParseError::at(n, EscalationParseKind::Syntax, e))?;
        if let Err(e) = Escalation::new([rule.clone()]).compile() {
            return Err(EscalationParseError::at(
                n,
                EscalationParseKind::InvalidRule,
                e.to_string(),
            ));
        }
        rules.push(rule);
    }
    let table = Escalation::new(rules);
    if let Err(e) = table.compile() {
        return Err(EscalationParseError {
            line: None,
            kind: EscalationParseKind::InvalidRule,
            detail: e.to_string(),
        });
    }
    Ok((table, horizon))
}

/// The table of an escalation file ([`parse_escalation_file`]): its `horizon=` line, if it
/// has one, is checked and not returned.
pub fn parse_escalation(text: &str) -> Result<Escalation, EscalationParseError> {
    match parse_escalation_file(text) {
        Ok((table, _)) => Ok(table),
        Err(e) => Err(e),
    }
}

/// One rule line of an escalation file: its word and its one argument.
fn parse_escalation_line(line: &str) -> Result<Escalate, String> {
    let mut words = line.split_ascii_whitespace();
    let (Some(head), arg, None) = (words.next(), words.next(), words.next()) else {
        return Err(format!(
            "{line:?}: a rule is a word and one argument, with no space in it"
        ));
    };
    let Some(arg) = arg else {
        return Err(format!("{head}: no argument"));
    };
    match head {
        "subject" => Ok(Escalate::Subject(arg.to_string())),
        "principal" => Ok(Escalate::PrincipalPrefix(arg.to_string())),
        "group" => Ok(Escalate::Group(arg.to_string())),
        other => Err(format!(
            "{other:?}: expected subject, principal, group or horizon="
        )),
    }
}

/// A `horizon=` value: a whole number of milliseconds, `<n>ms`.
fn parse_horizon(v: &str) -> Result<Duration, String> {
    let Some(digits) = v.strip_suffix("ms") else {
        return Err(format!("horizon={v}: expected <n>ms"));
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("horizon={v}: expected <n>ms"));
    }
    match digits.parse::<u64>() {
        Ok(ms) => Ok(Duration::from_millis(ms)),
        Err(_) => Err(format!("horizon={v}: not a number of milliseconds")),
    }
}

/// A parsed table, as the log holds it.
#[derive(Debug, Default)]
pub(crate) struct Rules {
    subjects: Vec<Filter>,
    prefixes: Vec<String>,
    groups: Vec<Filter>,
    /// How many rules the table was given (what the `Hello` block reports).
    count: u16,
}

impl Rules {
    /// How many rules the table holds.
    pub(crate) const fn count(&self) -> u16 {
        self.count
    }

    /// Whether a record on `subject`, by a producer bound to `principal` (if any),
    /// carrying a commit of `group` (if any), is escalated.
    pub(crate) fn matches(
        &self,
        subject: &str,
        principal: Option<&str>,
        group: Option<&str>,
    ) -> bool {
        let visible = !is_hidden_subject(subject);
        if visible {
            for f in &self.subjects {
                if f.matches_str(subject) {
                    return true;
                }
            }
            if let Some(p) = principal {
                for x in &self.prefixes {
                    if p.starts_with(x.as_str()) {
                        return true;
                    }
                }
            }
        }
        if let Some(g) = group {
            for f in &self.groups {
                if f.matches_str(g) {
                    return true;
                }
            }
        }
        false
    }

    /// Whether the table is empty (nothing to match, so staging skips the lookups).
    pub(crate) const fn is_empty(&self) -> bool {
        self.count == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table() -> Rules {
        Escalation::new([
            Escalate::Subject("/f/*/fleet/>".into()),
            Escalate::PrincipalPrefix("h-".into()),
            Escalate::Group("/f/*/cur/p/>".into()),
        ])
        .compile()
        .expect("the table parses")
    }

    #[test]
    fn each_rule_catches_its_own_kind_of_record() {
        let t = table();
        assert_eq!(t.count(), 3);
        assert!(
            t.matches("/f/F/fleet/h-a/halt", None, None),
            "a subject rule"
        );
        assert!(
            t.matches("/f/F/in/n/s/h-a/ask", Some("h-alice"), None),
            "a principal rule"
        );
        assert!(
            t.matches("/a/commit", None, Some("/f/F/cur/p/alice/inbox")),
            "a group rule sees a pure commit"
        );
        assert!(
            !t.matches("/f/F/in/n/s/s-1/note", Some("n-1"), None),
            "machine chatter"
        );
        assert!(
            !t.matches("/a/commit", None, Some("/f/F/cur/n/node/inbox")),
            "a node's commit"
        );
    }

    /// The subject and principal rules never see the broker's own hidden records: a
    /// person's producer binding (`/a/bind`), or a will, stays on the ordinary path.
    #[test]
    fn hidden_subjects_escape_the_subject_and_principal_rules() {
        let all = Escalation::new([
            Escalate::Subject("/>".into()),
            Escalate::PrincipalPrefix("h-".into()),
        ])
        .compile()
        .unwrap();
        for hidden in ["/a/bind", "/a/will", "/a/retire", "/a/commit"] {
            assert!(!all.matches(hidden, Some("h-alice"), None), "{hidden}");
        }
        assert!(all.matches("/x", None, None));
    }

    #[test]
    fn a_rule_that_is_not_one_refuses_by_name() {
        for (bad, says) in [
            (Escalate::Subject("not a filter".into()), "Subject"),
            (Escalate::Group("".into()), "Group"),
            (Escalate::PrincipalPrefix(String::new()), "PrincipalPrefix"),
        ] {
            let err = Escalation::new([bad]).compile().unwrap_err();
            assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
            assert!(err.to_string().contains(says), "{err}");
        }
        assert!(Escalation::default().compile().unwrap().is_empty());
    }

    /// A file reads as its table, rule for rule and in its order, comments and blank lines
    /// skipped, with the horizon its one `horizon=` line names; without one, none.
    /// `parse_escalation` is the same table.
    #[test]
    fn an_escalation_file_reads_as_its_table_and_horizon() {
        let text = concat!(
            "# a table\n\nhorizon=250ms\nsubject /f/*/fleet/>\n",
            "  principal h-  \n# between\ngroup /f/*/cur/p/>\n",
        );
        let want = Escalation::new([
            Escalate::Subject("/f/*/fleet/>".into()),
            Escalate::PrincipalPrefix("h-".into()),
            Escalate::Group("/f/*/cur/p/>".into()),
        ]);
        let (table, horizon) = parse_escalation_file(text).unwrap();
        assert_eq!(table, want);
        assert_eq!(horizon, Some(Duration::from_millis(250)));
        assert_eq!(parse_escalation(text).unwrap(), want);
        assert_ne!(
            parse_escalation("principal h-\nsubject /f/*/fleet/>\ngroup /f/*/cur/p/>").unwrap(),
            want,
            "the order is the file's"
        );
        assert_eq!(
            parse_escalation_file("subject /x\n").unwrap(),
            (Escalation::new([Escalate::Subject("/x".into())]), None)
        );
        assert_eq!(
            parse_escalation_file("horizon=0ms").unwrap(),
            (Escalation::default(), Some(Duration::ZERO))
        );
        assert_eq!(
            parse_escalation_file("horizon=18446744073709551615ms").unwrap(),
            (Escalation::default(), Some(Duration::from_millis(u64::MAX)))
        );
        assert_eq!(
            parse_escalation_file("# nothing\n").unwrap(),
            (Escalation::default(), None)
        );
    }

    /// Every line the open would refuse, and every line that is not one of the grammar's,
    /// is refused with its line and typed reason.
    #[test]
    fn an_escalation_file_refuses_each_bad_line_by_number() {
        use EscalationParseKind::{DuplicateHorizon, InvalidHorizon, InvalidRule, Syntax};
        for (text, line, kind) in [
            ("subject /ok\nsubject not-a-filter", 2, InvalidRule),
            ("subject /ok\nsubject fo*", 2, InvalidRule),
            ("group /a//b", 1, InvalidRule),
            ("principal", 1, Syntax),
            ("subject /a /b", 1, Syntax),
            ("prefix h-", 1, Syntax),
            ("horizon=100", 1, InvalidHorizon),
            ("horizon=1s", 1, InvalidHorizon),
            ("horizon=ms", 1, InvalidHorizon),
            ("horizon=+5ms", 1, InvalidHorizon),
            ("horizon=99999999999999999999ms", 1, InvalidHorizon),
            ("horizon=1ms\n\nhorizon=1ms", 3, DuplicateHorizon),
        ] {
            let err = parse_escalation_file(text).unwrap_err();
            assert_eq!((err.line(), err.kind()), (Some(line), kind), "{text:?}");
            assert!(parse_escalation(text).is_err(), "{text:?}");
        }
    }
}
