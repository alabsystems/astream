// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! RETENTION CLASSES: the rules a broker retains its log by, and the pure planning they
//! take (`REQUIREMENTS-fabric-operations` R4, "Design (2026-10-19)").
//!
//! # The rules
//!
//! A broker's retention is a list of [`Rule`]s, each `(filter, class, max_age, max_bytes)`,
//! plus a DEFAULT rule for every subject no rule names ([`Retention`]). A subject belongs to
//! the first rule whose filter matches it, and a broker-internal (hidden) subject to the
//! default rule, which counts its bytes and never holds it (its bindings, wills and group
//! commits are carried in `<log>.state`). A broker with no rules never compacts by itself.
//!
//! There are two classes:
//!
//! - **prefix**: exactly one rule, the bulk stream (`/f/<F>/pub/*/*/ev` in a fabric). It
//!   alone holds the CUT, the log's new base, down to the oldest record it still wants: the
//!   newest records of its class within its `max_bytes`, none older than its `max_age`.
//!   Below the cut its records are gone, so its floor is the base.
//! - **hold**: every other rule, the default one included. A hold rule never holds the cut
//!   back. Below the cut, each record a hold rule still wants is carried, by its absolute
//!   offset, in the held store (`held.rs`): one that keeps ALL ([`Keep::All`]) wants every
//!   record within its `max_age` that its readers have not read ([`Rule::until_read`]); one
//!   that keeps the LAST value only ([`Keep::Last`]) wants nothing beyond each subject's
//!   `Last` row. Every compaction carries every quiet subject's `Last` row and its charge in
//!   `<log>.state`, whatever its rule, until the subject is retired or a rule that forgets
//!   lets it go ("Forgetting", below).
//!
//! # Every class bounded
//!
//! A class's bytes are its records' in the retained suffix plus its held ones. A class past
//! its own `max_bytes` gives up its oldest: a hold class drops its oldest held records, and
//! when its records above the cut alone are past it, the cut rises to put the oldest of them
//! below, where they are dropped instead of carried. So a hold rule never holds the cut back
//! (one held mail cannot pin every subject's records, which a cut that is the minimum over
//! every rule's floor would), and the retained and held record bytes together stay within
//! the sum of the rules' `max_bytes`, plus what the log took since the planning: broker RAM
//! follows the rules, beside the `Last` rows the subject caps bound
//! ([`MAX_SUBJECTS_PER_PRODUCER`](crate::store::MAX_SUBJECTS_PER_PRODUCER)).
//!
//! A class past its bytes gives up AT LEAST A QUARTER of them ([`SLACK_DIV`]), its oldest,
//! or down to its bytes when it is further past them than that: so a class that has just
//! given records up has a quarter of its bytes of room, less what it was past them by,
//! before it is past them again. A cut
//! copies the log it keeps, so without that room a log at its bounds would be copied whole
//! for every batch it took; with it, a class's records ask for a cut at most once a quarter
//! of its bytes. A log far past its bounds keeps exactly its bytes (R4's acceptance: 100 of
//! 250 records, the oldest 151).
//!
//! The broker's writer asks for a tick when a batch takes SOME CLASS past the room the last
//! planning left it (`Plan::room`), counted by the class of each record it takes, never by
//! the log's length: a class at its bytes while another class's records arrive asks for
//! nothing until a record of its own does.
//!
//! # Told, never silent
//!
//! A record a [`Keep::All`] hold rule gave up (past its bytes or its age, or read by every
//! reader it names) raises its SUBJECT's floor past it; a `Fetch` below the floor of what
//! its filter can match answers `ERR retained-from=<floor>` (`proto::RETAINED_FROM_PREFIX`)
//! instead of an empty page, and a record given up while still unread is logged, one line
//! per subject and count. Records of one subject are given up oldest first (bytes and age
//! take the oldest, and a group that read a record read every older one of its filter), so a
//! subject's floor never passes a record of it the store still holds. `oldest` is that
//! floor for a filter, the offset at and above which the filter is complete: the base for
//! what the prefix rule and the last-value rules can match, the matching subjects' floors
//! (and where the rules took effect) for the rest, the greatest of them over what the
//! filter matches. So of a filter whose subjects have different floors, records some subject
//! still holds can lie below it.
//!
//! A TAIL is told too (R4's addendum, A9): one whose cursor is below its filter's oldest is
//! sent a gap notice before its next record, counted from the `Ledger` of what the hold
//! rules gave up where that names every record of the filter it lost (`counted_from`), and
//! is delivered every record of its filter retention still holds there. A `Fetch` from a
//! reader that asked for the notices reads the same way (`BrokerLog::fetch_told`): below the
//! oldest, while retention still holds records of its filter there, it reads them from its
//! `from`, the notice ahead of the page; `retained-from=` is the answer when it holds none of
//! them, and to a reader that did not ask.
//!
//! # Forgetting
//!
//! A subject's `Last` row outlives its records: a cut carries every quiet subject's newest
//! record in `<log>.state` (`carried_last`) and the producer it is charged to
//! (`carried_charges`), so `Last` answers a presence row or a halt long after the record's
//! own rule gave it up, and the subject keeps its place in its producer's budget
//! ([`MAX_SUBJECTS_PER_PRODUCER`](crate::store::MAX_SUBJECTS_PER_PRODUCER)). That is right
//! for a subject whose last value is read, and wrong for a lane whose records go once read
//! (a fabric's mail): its producer's budget fills with lanes no record of which survives,
//! until it can open no new one (`ERR_SUBJECT_BOUND`). A rule that FORGETS
//! ([`Rule::forgetting`], `forget` in a rules file) lets such a subject go: once retention
//! has given up every record of it, it leaves `Last` and its charged producer's count goes
//! down by one. Off by default; a rule that keeps the last value only cannot forget.
//!
//! A tick, after its retention lands (and a tick that changes nothing too), forgets each
//! subject of a forgetting rule that every guard of a `Retire` allows, the same guards a
//! subject retire takes: its newest record (its `Last` offset) lies below the base, no
//! record of it is left in the held store, no will that can still append targets it (a live
//! will, a durable one, and one a cut carried), it is no broker-internal subject, the log is
//! not a replica, and no uncarried cut has tainted the charges. A subject a guard keeps is
//! carried as before and looked at again at the next tick. At most [`FORGET_MAX`] subjects a
//! tick; a tick that reaches it asks for another.
//!
//! A forget IS A RETIRE, made by the broker: one marked `/a/retire` record per subject
//! (`BrokerRecord::marked_retire`, under the producer the subject is charged to), staged by
//! the broker's writer like every other op, which judges the guards again against its
//! batch (a record of the subject staged or landed since the tick looked keeps it). So
//! everything a retire already does follows: the `Last` view's history (a page read
//! against a head below the record still answers the row), the replay at an open (which
//! applies the record to the rows `<log>.state` carried), the next cut's carried charges
//! (which drop the subject once the record is below it), replication (a follower applies
//! the leader's record and forgets nothing of its own), and every count. Dropping the
//! subject from the carried state at the cut itself was the alternative, and it is worse:
//! the forget would have no offset, so a `Last` page pinned below it could not be answered
//! consistently, a follower or a reopen that judged it again could judge it otherwise
//! (a will a connection holds is not in the log), and a forget at a tick that cuts nothing
//! (the read that releases the last held record) would wait for the next compaction, since
//! only a compaction writes `<log>.state`. [`RetentionTick::forgotten`](crate::RetentionTick)
//! counts the subjects a tick forgot.
//!
//! # Record times
//!
//! The log's records carry no time. The retention tick STAMPS what it has not seen yet with
//! its own clock (`stamp`): a record's age is measured from the first tick that saw it, so it
//! reads at most one tick younger than it is, never older. The stamps are DURABLE: each job
//! writes the ones its tick took into the held store (`held.rs`, its `S` frames), so a
//! reopen reads every record's age back, and an age rule cuts by when a record was first
//! seen whatever the restarts between (a record no tick saw before a restart is stamped at
//! the first tick after it, a restart's downtime younger). A crash that loses records a tick
//! stamped cuts the stamps back to the log's head at the open (`clamp_stamps`), so a record
//! that takes a lost one's offset is never read as old as it. Held records keep their own
//! stamp in the held store. Every age decision is the tick's, taken at the time it is handed
//! (`Broker::retention_tick_at`), so a test drives it with a hand clock and nothing reads
//! the wall clock here.

use crate::brecord::BrokerRecord;
use crate::store::is_hidden_subject;
use astream_wire::{Filter, Subject};
use std::collections::HashMap;
use std::io;
use std::time::Duration;

/// The most rules a broker takes (the default rule apart).
pub const MAX_RULES: usize = 32;

/// The most classes a broker's rules make: one per rule and the default one.
const MAX_CLASSES: usize = MAX_RULES + 1;

/// The most reader templates one rule names ([`Rule::until_read`]).
pub const MAX_READERS: usize = 8;

/// The most subjects one retention tick forgets ([`Rule::forgetting`]): the writer stages
/// them as one op, so a tick's forgets stay within one batch the size of the writer's own
/// bound, and a tick that reaches it asks for another.
pub const FORGET_MAX: usize = 4096;

/// The highest segment a reader template can name (`{N}`).
const MAX_TEMPLATE_SEGMENT: usize = 64;

/// A class past its bytes gives up at least `max_bytes / SLACK_DIV` of them (see the module
/// docs, "Every class bounded").
pub const SLACK_DIV: u64 = 4;

/// The least a class past `max` bytes gives up.
const fn slack(max: u64) -> u64 {
    max / SLACK_DIV
}

/// The most per-subject floors one [`oldest`] reads before it answers the greatest of all
/// of them instead: a bound on the work a `Fetch` does under the log lock, never a
/// guess below a floor (the fallback is larger, never smaller).
pub(crate) const FLOOR_SCAN_MAX: usize = 65_536;

/// The most records a [`Ledger`] names: as many as the held store keeps floors for.
pub(crate) const LEDGER_MAX: usize = 65_536;

/// The most bytes of subject names a [`Ledger`] takes, as the floors' names are bounded.
pub(crate) const LEDGER_BYTES_MAX: usize = 8 << 20;

mod planner;

// THE PLANNING (`retention/planner.rs`) is the crate's, and in a test or debug build it is
// also pub: a simulation of this broker plans every cut by it as the tick does (aterm's
// deterministic fabric simulation, its item B05). Never behind a cargo feature.
#[cfg(test)]
pub(crate) use planner::ByIndex;
#[cfg(any(test, debug_assertions))]
pub use planner::{
    carried_since, clamp_stamps, counted_from, oldest, plan, plan_with, prune_stamps, stamp, Held,
    Ledger, Plan, Planned, Stamps, View, Why,
};
#[cfg(not(any(test, debug_assertions)))]
pub(crate) use planner::{
    carried_since, clamp_stamps, counted_from, oldest, prune_stamps, stamp, Held, Ledger, Plan,
    Stamps, Why,
};
pub(crate) use planner::{plan_over, Entry, Records, Scene};
#[cfg(test)]
use planner::{stamped_at, STAMPS_MAX};

/// A rule's class (see the module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Class {
    /// The one rule that holds the cut: its records below it are gone.
    Prefix,
    /// A rule whose still-wanted records below the cut are carried in the held store.
    Hold,
}

/// What a hold rule wants below the cut.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Keep {
    /// Every record within its `max_age` its readers have not read.
    All,
    /// Each subject's `Last` row only (which every compaction carries in `<log>.state`).
    Last,
}

/// One retention rule: `(filter, class, max_age, max_bytes)`, what a hold rule keeps, and the
/// consumer groups that read its records. Built with [`Rule::prefix`], [`Rule::hold`] or
/// [`Rule::default_hold`] and the bounds after them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    filter: Option<Filter>,
    class: Class,
    keep: Keep,
    max_age_ms: Option<u64>,
    max_bytes: Option<u64>,
    read_by: Vec<String>,
    forget: bool,
}

fn invalid(msg: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, msg)
}

/// A duration in whole milliseconds, saturating.
fn millis(d: Duration) -> u64 {
    u64::try_from(d.as_millis()).unwrap_or(u64::MAX)
}

impl Rule {
    fn with(filter: &str, class: Class) -> io::Result<Rule> {
        let Ok(f) = Filter::new(filter) else {
            return Err(invalid(format!("retention: {filter:?} is not a filter")));
        };
        Ok(Rule {
            filter: Some(f),
            class,
            keep: Keep::All,
            max_age_ms: None,
            max_bytes: None,
            read_by: Vec::new(),
            forget: false,
        })
    }

    /// The PREFIX rule over `filter`: the one rule that holds the cut.
    pub fn prefix(filter: &str) -> io::Result<Rule> {
        Rule::with(filter, Class::Prefix)
    }

    /// A HOLD rule over `filter`, keeping every record ([`Keep::All`]) until its bounds.
    pub fn hold(filter: &str) -> io::Result<Rule> {
        Rule::with(filter, Class::Hold)
    }

    /// The DEFAULT rule as a broker takes it unless told otherwise: a hold rule over every
    /// subject no other rule names that keeps each subject's `Last` row only, with no bounds.
    #[must_use]
    pub const fn default_hold() -> Rule {
        Rule {
            filter: None,
            class: Class::Hold,
            keep: Keep::Last,
            max_age_ms: None,
            max_bytes: None,
            read_by: Vec::new(),
            forget: false,
        }
    }

    /// The default rule keeping every record ([`Keep::All`]) until its bounds.
    #[must_use]
    pub const fn default_keeping_all() -> Rule {
        Rule {
            filter: None,
            class: Class::Hold,
            keep: Keep::All,
            max_age_ms: None,
            max_bytes: None,
            read_by: Vec::new(),
            forget: false,
        }
    }

    /// No record older than `age` is wanted.
    #[must_use]
    pub fn max_age(mut self, age: Duration) -> Rule {
        self.max_age_ms = Some(millis(age));
        self
    }

    /// The class's records, retained and held, stay within `bytes` ([`record_bytes`]).
    #[must_use]
    pub const fn max_bytes(mut self, bytes: u64) -> Rule {
        self.max_bytes = Some(bytes);
        self
    }

    /// A hold rule that keeps each subject's `Last` row only.
    #[must_use]
    pub const fn last_only(mut self) -> Rule {
        self.keep = Keep::Last;
        self
    }

    /// A rule that FORGETS its subjects (see the module docs, "Forgetting"): once retention
    /// has given up every record of a subject this rule governs, the subject leaves the
    /// last-value index and the producer it is charged to gets that subject of its budget
    /// back ([`MAX_SUBJECTS_PER_PRODUCER`](crate::store::MAX_SUBJECTS_PER_PRODUCER)), live
    /// and across a reopen. For a lane whose records go once read (a fabric's mail), whose
    /// `Last` row no reader wants once the records are gone. Only a rule that keeps every
    /// record ([`Keep::All`]) forgets: [`Retention::new`] refuses one that keeps the last
    /// value only, whose `Last` row is what it keeps.
    #[must_use]
    pub const fn forgetting(mut self) -> Rule {
        self.forget = true;
        self
    }

    /// A record of this rule is READ once the consumer group `template` names has committed
    /// past it; a record every named group has read is wanted no more. `{N}` in the template
    /// is the record subject's `N`-th segment, from 1: in a fabric,
    /// `/f/{2}/cur/{4}/node/inbox` is the inbox group of the node `/f/<F>/in/<node>/…` names.
    /// A record whose subject has too few segments for a template has no group there, and is
    /// held for its `max_age` alone. Refused for a template that does not make a subject.
    pub fn until_read(mut self, template: &str) -> io::Result<Rule> {
        if self.read_by.len() >= MAX_READERS {
            return Err(invalid(format!(
                "retention: a rule names at most {MAX_READERS} reader groups"
            )));
        }
        let Some(probe) = expand_with(template, |_| Some("x")) else {
            return Err(invalid(format!(
                "retention: the reader template {template:?} has a placeholder that is not {{1}} to {{{MAX_TEMPLATE_SEGMENT}}}"
            )));
        };
        if Subject::new(probe).is_err() {
            return Err(invalid(format!(
                "retention: the reader template {template:?} does not make a subject"
            )));
        }
        self.read_by.push(template.to_string());
        Ok(self)
    }

    /// The rule's filter; `None` for the default rule.
    #[must_use]
    pub fn filter(&self) -> Option<&str> {
        match &self.filter {
            Some(f) => Some(f.as_str()),
            None => None,
        }
    }

    /// The rule's class.
    #[must_use]
    pub const fn class(&self) -> Class {
        self.class
    }

    /// What the rule keeps below the cut.
    #[must_use]
    pub const fn keep(&self) -> Keep {
        self.keep
    }

    /// The age past which no record is wanted.
    #[must_use]
    pub const fn age(&self) -> Option<Duration> {
        match self.max_age_ms {
            Some(ms) => Some(Duration::from_millis(ms)),
            None => None,
        }
    }

    /// The bytes the class stays within.
    #[must_use]
    pub const fn bytes(&self) -> Option<u64> {
        self.max_bytes
    }

    /// The reader group templates ([`until_read`](Self::until_read)).
    #[must_use]
    pub fn readers(&self) -> &[String] {
        &self.read_by
    }

    /// Whether the rule forgets its subjects once it has given up all of their records
    /// ([`forgetting`](Self::forgetting)).
    #[must_use]
    pub const fn forgets(&self) -> bool {
        self.forget
    }

    /// Refused for a rule that keeps the last value only and forgets: its subjects' `Last`
    /// rows are what it keeps, so only a rule that keeps every record forgets.
    fn check_forget(&self) -> Result<(), String> {
        if self.forget && self.keep == Keep::Last {
            let which = match self.filter() {
                Some(f) => format!("the rule over {f:?}"),
                None => "the default rule".to_string(),
            };
            return Err(format!(
                "retention: {which} keeps the last value only and forgets: a subject's `Last` \
                 row is what it keeps, so only a rule that keeps every record forgets"
            ));
        }
        Ok(())
    }

    /// Whether the rule keeps every record below the cut in the held store.
    const fn holds_records(&self) -> bool {
        matches!((self.class, self.keep), (Class::Hold, Keep::All))
    }

    /// Whether `rec`, at `age_ms`, is past this rule's age.
    fn aged(&self, age_ms: u64) -> bool {
        match self.max_age_ms {
            Some(max) => age_ms > max,
            None => false,
        }
    }

    /// Whether every reader group this rule names for the record of `subject` at
    /// `offset` has committed past it.
    /// `false` with no reader that applies: such a record is held for its age alone.
    fn read(&self, subject: &str, offset: u64, groups: &HashMap<String, u64>) -> bool {
        let mut any = false;
        for t in &self.read_by {
            let Some(group) = expand(t, subject) else {
                continue;
            };
            any = true;
            match groups.get(&group) {
                Some(&upto) if upto >= offset => {}
                _ => return false,
            }
        }
        any
    }
}

/// `template` with each `{N}` replaced by `seg(N)`; `None` for a placeholder that is not
/// `{1}` to `{MAX_TEMPLATE_SEGMENT}`, or that `seg` has nothing for.
fn expand_with<'a>(template: &str, seg: impl Fn(usize) -> Option<&'a str>) -> Option<String> {
    let mut out = String::new();
    let mut rest = template;
    while let Some(open) = rest.find('{') {
        out.push_str(rest.get(..open)?);
        let after = rest.get(open.saturating_add(1)..)?;
        let close = after.find('}')?;
        let n: usize = after.get(..close)?.parse().ok()?;
        if n == 0 || n > MAX_TEMPLATE_SEGMENT {
            return None;
        }
        out.push_str(seg(n)?);
        rest = after.get(close.saturating_add(1)..)?;
    }
    if rest.contains('}') {
        return None;
    }
    out.push_str(rest);
    Some(out)
}

/// The group `template` names for `subject` (see [`Rule::until_read`]).
fn expand(template: &str, subject: &str) -> Option<String> {
    let segs: Vec<&str> = subject
        .split('/')
        .skip(1)
        .take(MAX_TEMPLATE_SEGMENT)
        .collect();
    expand_with(template, |n| match n.checked_sub(1) {
        Some(i) => segs.get(i).copied(),
        None => None,
    })
}

/// Whether some subject can match both filters. SOUND for the use it has: it never answers
/// `false` for two filters that share a subject (where a segment could go either way it
/// says `true`), so a floor it is asked about is never missed, only, at worst, answered for
/// a filter that could not have reached it.
pub(crate) fn filters_overlap(a: &str, b: &str) -> bool {
    let mut x = a.split('/').skip(1);
    let mut y = b.split('/').skip(1);
    loop {
        match (x.next(), y.next()) {
            (None, None) => return true,
            // `>` takes one or more segments: anything left on the other side, or another `>`.
            (Some(">"), Some(_)) | (Some(_), Some(">")) => return true,
            (Some(_), None) | (None, Some(_)) => return false,
            (Some(s), Some(t)) => {
                if s != "*" && t != "*" && s != t {
                    return false;
                }
            }
        }
    }
}

/// A record's bytes as retention counts them: its frame's length on a plaintext log (the
/// frame header, the record's fields, its subject and body, a commit it carries), without
/// the batch mark. A sealed log stores a fixed overhead more per record.
#[must_use]
pub fn record_bytes(rec: &BrokerRecord) -> u64 {
    crate::brecord::plaintext_frame_bytes(rec)
}

/// A broker's retention rules: every [`Rule`] in order, then the default one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Retention {
    rules: Vec<Rule>,
    default: Rule,
}

impl Retention {
    /// The rules, checked: at most [`MAX_RULES`], each with a filter, exactly one of them
    /// [`Class::Prefix`] (keeping all, naming no reader), `default` with no filter and
    /// [`Class::Hold`], and none that both keeps the last value only and forgets
    /// ([`Rule::forgetting`]). What Hello advertises must fit its entry.
    pub fn new(rules: Vec<Rule>, default: Rule) -> io::Result<Retention> {
        if rules.len() > MAX_RULES {
            return Err(invalid(format!(
                "retention: {} rules, at most {MAX_RULES}",
                rules.len()
            )));
        }
        let mut prefixes = 0usize;
        for r in &rules {
            let Some(f) = r.filter() else {
                return Err(invalid(
                    "retention: only the default rule has no filter".to_string(),
                ));
            };
            if r.class == Class::Prefix {
                prefixes = prefixes.saturating_add(1);
                if r.keep != Keep::All || !r.read_by.is_empty() {
                    return Err(invalid(format!(
                        "retention: the prefix rule {f:?} keeps every record it wants and names no reader"
                    )));
                }
            }
        }
        if prefixes != 1 {
            return Err(invalid(format!(
                "retention: exactly one prefix rule holds the cut, not {prefixes}"
            )));
        }
        if default.filter.is_some() || default.class != Class::Hold {
            return Err(invalid(
                "retention: the default rule is a hold rule with no filter".to_string(),
            ));
        }
        for r in rules.iter().chain(std::iter::once(&default)) {
            r.check_forget().map_err(invalid)?;
        }
        let r = Retention { rules, default };
        if r.encode().len() > usize::from(u16::MAX) {
            return Err(invalid(
                "retention: the rules do not fit Hello's entry".to_string(),
            ));
        }
        Ok(r)
    }

    /// The rules, without the default one.
    #[must_use]
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// The default rule.
    #[must_use]
    pub const fn default_rule(&self) -> &Rule {
        &self.default
    }

    /// How many classes there are: one per rule and the default one, last. At most
    /// [`MAX_RULES`] and one ([`Retention::new`] checks it; bounded here too, so every
    /// allocation sized by it is visibly bounded where it is made).
    pub(crate) fn classes(&self) -> usize {
        self.rules
            .len()
            .saturating_add(1)
            .min(MAX_RULES.saturating_add(1))
    }

    /// One `zero` per class. The count is checked against [`MAX_CLASSES`] here, beside the
    /// allocation, so the verified lane sees the bound where the vector is made: a plain
    /// `if` that dominates it (a match guard's bound did not reach the lane's solver).
    /// [`classes`](Self::classes) never exceeds it, so the empty answer is never given.
    pub(crate) fn per_class<T: Clone>(&self, zero: T) -> Vec<T> {
        let n = self.classes();
        if n > MAX_CLASSES {
            return Vec::new();
        }
        vec![zero; n]
    }

    /// The rule of class `c` (the default rule for `c` past the rules).
    pub(crate) fn rule(&self, c: usize) -> &Rule {
        match self.rules.get(c) {
            Some(r) => r,
            None => &self.default,
        }
    }

    /// Whether `subject` falls to a hold rule that keeps only its `Last` row.
    #[must_use]
    pub fn keeps_last(&self, subject: &str) -> bool {
        let rule = self.rule(self.class_of(subject));
        rule.class() == Class::Hold && rule.keep() == Keep::Last
    }

    /// Whether `subject` falls to a rule that forgets ([`Rule::forgetting`]).
    pub(crate) fn forgets(&self, subject: &str) -> bool {
        self.rule(self.class_of(subject)).forget
    }

    /// Whether any rule, the default one included, forgets.
    pub(crate) fn forgets_any(&self) -> bool {
        self.default.forget || self.rules.iter().any(|r| r.forget)
    }

    /// The class of `subject`: the first rule whose filter matches it, else the default one,
    /// which every hidden subject is.
    pub(crate) fn class_of(&self, subject: &str) -> usize {
        if !is_hidden_subject(subject) {
            for (i, r) in self.rules.iter().enumerate() {
                if let Some(f) = &r.filter {
                    if f.matches_str(subject) {
                        return i;
                    }
                }
            }
        }
        self.rules.len()
    }

    /// The classes `filter` can reach: every rule whose filter can share a subject with it,
    /// and the default one unless a single rule's filter holds every subject it matches.
    pub(crate) fn reached_by(&self, filter: &Filter) -> Vec<usize> {
        let mut out = Vec::new();
        let mut covered = false;
        for (i, r) in self.rules.iter().enumerate() {
            if let Some(f) = &r.filter {
                if filters_overlap(f.as_str(), filter.as_str()) {
                    out.push(i);
                }
                if f.contains(filter) {
                    covered = true;
                }
            }
        }
        if !covered {
            out.push(self.rules.len());
        }
        out
    }

    /// The classes a subject of ANOTHER rules' default class can be in here: every rule
    /// whose filter is none of `named` (theirs), and the default one. A subject no rule of
    /// theirs names matches none of `named`, so none of the rules here with those filters.
    pub(crate) fn reached_by_default_of(&self, named: &[&str]) -> Vec<usize> {
        let mut out = Vec::new();
        for (i, r) in self.rules.iter().enumerate() {
            match r.filter() {
                Some(f) if named.contains(&f) => {}
                _ => out.push(i),
            }
        }
        out.push(self.rules.len());
        out
    }

    /// Hello's entry for the rules (`proto` tag 0x05), and the held store's `R` frame's: `n
    /// u8`, then per rule, the default one last, `class u8, keep u8, max_age_ms u64 LE,
    /// max_bytes u64 LE` (`u64::MAX`: none), `filter len u16 LE` and its bytes (none for the
    /// default rule), `readers u8` and each `len u16 LE` and its bytes. `keep` is bits: bit 0
    /// for [`Keep::Last`] (clear: [`Keep::All`]), bit 1 for a rule that forgets
    /// ([`Rule::forgetting`]); no other bit is set, so rules that forget nothing encode as
    /// they did before the bit, and an older decoder refuses rules that forget rather than
    /// read them as rules that do not.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let n = u8::try_from(self.classes()).unwrap_or(u8::MAX);
        out.push(n);
        for r in self.rules.iter().chain(std::iter::once(&self.default)) {
            put_rule(&mut out, r);
        }
        out
    }

    /// The rules Hello's entry advertises, the default one last; `None` for bytes that are
    /// not that layout or rules that do not check ([`Retention::new`]).
    #[must_use]
    pub fn decode(b: &[u8]) -> Option<Retention> {
        let (&n, mut rest) = b.split_first()?;
        let mut rules = Vec::new();
        for _ in 0..n {
            let (r, tail) = take_rule(rest)?;
            rules.push(r);
            rest = tail;
        }
        if !rest.is_empty() {
            return None;
        }
        let default = rules.pop()?;
        Retention::new(rules, default).ok()
    }
}

/// The `keep` byte's bit for [`Keep::Last`] ([`Retention::encode`]).
const KEEP_LAST: u8 = 1;

/// The `keep` byte's bit for a rule that forgets ([`Retention::encode`]).
const KEEP_FORGET: u8 = 2;

fn put_u16_str(out: &mut Vec<u8>, s: &str) {
    let len = u16::try_from(s.len()).unwrap_or(u16::MAX);
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(s.as_bytes().get(..usize::from(len)).unwrap_or(&[]));
}

fn put_rule(out: &mut Vec<u8>, r: &Rule) {
    out.push(match r.class {
        Class::Prefix => 0,
        Class::Hold => 1,
    });
    let keep = match r.keep {
        Keep::All => 0,
        Keep::Last => KEEP_LAST,
    };
    out.push(if r.forget { keep | KEEP_FORGET } else { keep });
    out.extend_from_slice(&r.max_age_ms.unwrap_or(u64::MAX).to_le_bytes());
    out.extend_from_slice(&r.max_bytes.unwrap_or(u64::MAX).to_le_bytes());
    put_u16_str(out, r.filter().unwrap_or(""));
    out.push(u8::try_from(r.read_by.len()).unwrap_or(u8::MAX));
    for t in &r.read_by {
        put_u16_str(out, t);
    }
}

fn take_u64(b: &[u8]) -> Option<(u64, &[u8])> {
    let (head, rest) = b.split_first_chunk::<8>()?;
    Some((u64::from_le_bytes(*head), rest))
}

fn take_u16_str(b: &[u8]) -> Option<(&str, &[u8])> {
    let (len, rest) = b.split_first_chunk::<2>()?;
    let len = usize::from(u16::from_le_bytes(*len));
    let s = rest.get(..len)?;
    Some((std::str::from_utf8(s).ok()?, rest.get(len..)?))
}

fn take_rule(b: &[u8]) -> Option<(Rule, &[u8])> {
    let (&class, rest) = b.split_first()?;
    let (&keep, rest) = rest.split_first()?;
    let (age, rest) = take_u64(rest)?;
    let (bytes, rest) = take_u64(rest)?;
    let (filter, rest) = take_u16_str(rest)?;
    let (&readers, mut rest) = rest.split_first()?;
    let class = match class {
        0 => Class::Prefix,
        1 => Class::Hold,
        _ => return None,
    };
    let mut r = if filter.is_empty() {
        Rule::default_keeping_all()
    } else {
        Rule::with(filter, class).ok()?
    };
    r.class = class;
    if keep & !(KEEP_LAST | KEEP_FORGET) != 0 {
        return None;
    }
    r.keep = if keep & KEEP_LAST == 0 {
        Keep::All
    } else {
        Keep::Last
    };
    r.forget = keep & KEEP_FORGET != 0;
    r.max_age_ms = if age == u64::MAX { None } else { Some(age) };
    r.max_bytes = if bytes == u64::MAX { None } else { Some(bytes) };
    for _ in 0..readers {
        let (t, tail) = take_u16_str(rest)?;
        r = r.until_read(t).ok()?;
        rest = tail;
    }
    Some((r, rest))
}

/// One rule as a line of a rules file (`asb serve --retain-file`): `<prefix|hold|default>`,
/// then its options, then its filter (none for `default`), split on spaces. The options are
/// `age=<n><ms|s|m|h|d>`, `bytes=<n>[KiB|MiB|GiB]`, `last`, `forget` ([`Rule::forgetting`])
/// and `read=<template>`. A filter with a space in it cannot be written here. Returns whether
/// the line is the default rule.
pub fn parse_rule_line(line: &str) -> Result<(bool, Rule), String> {
    let mut words = line.split_ascii_whitespace();
    let Some(head) = words.next() else {
        return Err("an empty rule".to_string());
    };
    let rest: Vec<&str> = words.collect();
    let (opts, filter) = match head {
        "default" => (&rest[..], None),
        "prefix" | "hold" => match rest.split_last() {
            Some((f, opts)) => (opts, Some(*f)),
            None => return Err(format!("{head}: no filter")),
        },
        other => return Err(format!("{other:?}: expected prefix, hold or default")),
    };
    let mut rule = match (head, filter) {
        ("prefix", Some(f)) => Rule::prefix(f).map_err(|e| e.to_string())?,
        ("hold", Some(f)) => Rule::hold(f).map_err(|e| e.to_string())?,
        _ => Rule::default_keeping_all(),
    };
    for opt in opts {
        if *opt == "last" {
            rule = rule.last_only();
        } else if *opt == "forget" {
            rule = rule.forgetting();
        } else if let Some(v) = opt.strip_prefix("age=") {
            rule = rule.max_age(parse_age(v)?);
        } else if let Some(v) = opt.strip_prefix("bytes=") {
            rule = rule.max_bytes(parse_bytes(v)?);
        } else if let Some(v) = opt.strip_prefix("read=") {
            rule = rule.until_read(v).map_err(|e| e.to_string())?;
        } else {
            return Err(format!(
                "{opt:?}: expected age=, bytes=, last, forget or read="
            ));
        }
    }
    rule.check_forget()?;
    Ok((head == "default", rule))
}

/// A RULES FILE (`asb serve --retain-file`): one [`parse_rule_line`] per line, blank lines
/// and `#` comments skipped, at most one `default` line ([`Rule::default_hold`] without
/// one), checked as [`Retention::new`] checks them. Refused past [`MAX_RULES`] rules as it
/// reads, so a long file costs no more than the rules a broker can take. Each refusal names
/// its line.
pub fn parse_rules(text: &str) -> Result<Retention, String> {
    let mut rules = Vec::new();
    let mut default: Option<Rule> = None;
    for (i, line) in text.lines().enumerate() {
        let n = i.saturating_add(1);
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (is_default, rule) = match parse_rule_line(line) {
            Ok(r) => r,
            Err(e) => return Err(format!("line {n}: {e}")),
        };
        if is_default {
            if default.is_some() {
                return Err(format!("line {n}: a second default rule"));
            }
            default = Some(rule);
        } else {
            if rules.len() >= MAX_RULES {
                return Err(format!("line {n}: more than {MAX_RULES} rules"));
            }
            rules.push(rule);
        }
    }
    let default = match default {
        Some(d) => d,
        None => Rule::default_hold(),
    };
    match Retention::new(rules, default) {
        Ok(r) => Ok(r),
        Err(e) => Err(e.to_string()),
    }
}

fn split_number(v: &str) -> Result<(u64, &str), String> {
    let digits = v.bytes().take_while(u8::is_ascii_digit).count();
    let Some((n, unit)) = v.split_at_checked(digits) else {
        return Err(format!("{v:?}: not a number"));
    };
    match n.parse::<u64>() {
        Ok(n) => Ok((n, unit)),
        Err(_) => Err(format!("{v:?}: not a number")),
    }
}

fn parse_age(v: &str) -> Result<Duration, String> {
    let (n, unit) = split_number(v)?;
    let ms: u64 = match unit {
        "ms" => 1,
        "s" => 1000,
        "m" => 60_000,
        "h" => 3_600_000,
        "d" => 86_400_000,
        _ => return Err(format!("age={v}: expected ms, s, m, h or d")),
    };
    Ok(Duration::from_millis(n.saturating_mul(ms)))
}

fn parse_bytes(v: &str) -> Result<u64, String> {
    let (n, unit) = split_number(v)?;
    let mul: u64 = match unit {
        "" => 1,
        "KiB" => 1 << 10,
        "MiB" => 1 << 20,
        "GiB" => 1 << 30,
        _ => return Err(format!("bytes={v}: expected KiB, MiB or GiB")),
    };
    Ok(n.saturating_mul(mul))
}

#[cfg(test)]
#[path = "retention_tests.rs"]
mod tests;
