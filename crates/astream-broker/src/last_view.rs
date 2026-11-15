// Copyright 2026 Andrew Yates
//! Owned retirement history for a checked last-value read.
//!
//! A view owns a forward cursor, including links filled AFTER its head was read.
//! Publishing a newer head releases the store's old cursor, not a live view's.
//! Long-lived views and records returned to callers can still retain payloads.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::{Arc, OnceLock};

use astream_wire::Filter;

use crate::BrokerRecord;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "last_view_island.rs"]
mod last_view_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{
    last_view_available_advance, last_view_not_above_pub, last_view_not_before_avail,
    last_view_prune_clamp,
};
#[cfg(clean_islands)]
pub use last_view_island::{
    last_view_available_advance, last_view_not_above_pub, last_view_not_before_avail,
    last_view_prune_clamp,
};

/// Three-parameter checked `[avail, pub_head]` view-window admission kernel matching
/// `last_view_window_admits_code_isl` in `last_view_island.rs`, composed over Clean-origin
/// [`last_view_not_before_avail`] and [`last_view_not_above_pub`].
#[must_use]
pub const fn last_view_window_admits_code(avail: u64, pub_head: u64, req_vis: u64) -> u64 {
    if 0 < last_view_not_before_avail(avail, req_vis) {
        last_view_not_above_pub(pub_head, req_vis)
    } else {
        0
    }
}

contract_fn! {
    /// Kernel-certified partial-prefix maintenance quantum guard (`steps <= max_work`),
    /// linked via `clean-kernel-defeq` to `last_view_prune_within_quantum_isl`.
    #[must_use]
    pub const fn last_view_prune_within_quantum(steps: u64, max_work: u64) -> bool
    clauses [ensures result == (steps <= max_work)]
    {
        steps <= max_work
    }
}

/// A checked last-value read could not prove its requested history or read a retained value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LastViewError {
    TooOld {
        requested: u64,
        available: u64,
    },
    NotPublished {
        requested: u64,
        published: u64,
    },
    AbovePromoted {
        requested: u64,
        promoted: u64,
    },
    PublishedBackwards {
        requested: u64,
        published: u64,
    },
    WrongOpen,
    ChangedFilter,
    CursorBackwards,
    /// The last-value index still retains this offset, but its frame cannot be read.
    UnreadableRetained {
        offset: u64,
    },
}

impl fmt::Display for LastViewError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "last-value history: {self:?}")
    }
}

impl std::error::Error for LastViewError {}

struct Retired {
    subject: String,
    removed: Arc<BrokerRecord>,
    bt_ms: Option<u64>,
    offset: u64,
}

struct Link {
    next: OnceLock<(Retired, Arc<Link>)>,
}

impl Link {
    fn empty() -> Arc<Self> {
        Arc::new(Self {
            next: OnceLock::new(),
        })
    }
}

impl Drop for Link {
    fn drop(&mut self) {
        // Taking the edge before dropping each unique node prevents a recursive
        // Arc chain destructor. into_inner consumes a shared reference without the
        // try_unwrap/Err-drop race that could recursively drop its last owner. A
        // shared node belongs to another cursor and stops this traversal.
        let mut next = self.next.take().map(|(_, next)| next);
        while let Some(link) = next {
            match Arc::into_inner(link) {
                Some(mut unique) => next = unique.next.take().map(|(_, next)| next),
                None => break,
            }
        }
    }
}

/// Detached history; drop this AFTER releasing an external log mutex.
///
/// Destruction is iterative, but its work is the detached history's size. It has
/// no elapsed-time guarantee. Views and returned record handles may share it.
pub struct LastViewGarbage {
    _history: Option<Arc<Link>>,
    _latest: BTreeMap<String, u64>,
}

impl LastViewGarbage {
    fn empty() -> Self {
        Self {
            _history: None,
            _latest: BTreeMap::new(),
        }
    }
}

/// A last-value read pinned to one published head and one open log.
///
/// Keep this through every internal scan round. It is not a persisted cursor or a
/// complete historical snapshot: ordinary values replaced above the pin retain
/// the existing omission-and-tail contract. Do not keep a view indefinitely and
/// expect bounded memory; it owns retirement evidence until that evidence is read
/// or this view is dropped, and its overlay lives for this view's lifetime. Drop
/// the view after releasing an external log mutex: releasing its suffix and overlay
/// is iterative but can do work proportional to the retained history.
pub struct LastView {
    owner: Arc<()>,
    visible: u64,
    cursor: Arc<Link>,
    filter: Option<String>,
    after: String,
    seen: BTreeSet<String>,
    pub(crate) overlay: BTreeMap<String, Arc<BrokerRecord>>,
    pub(crate) overlay_bt: BTreeMap<String, u64>,
}

impl LastView {
    #[must_use]
    pub const fn visible(&self) -> u64 {
        self.visible
    }

    pub(crate) fn bind(&mut self, filter: &Filter, after: &str) -> Result<(), LastViewError> {
        if self
            .filter
            .as_deref()
            .is_some_and(|old| old != filter.as_str())
        {
            return Err(LastViewError::ChangedFilter);
        }
        if after < self.after.as_str() {
            return Err(LastViewError::CursorBackwards);
        }
        if self.filter.is_none() {
            self.filter = Some(filter.as_str().to_string());
        }
        self.after = after.to_string();
        Ok(())
    }

    /// Charge retirement visits against the SAME budget as subject-index visits.
    /// Called under the log lock, so reaching the open tail is this round's boundary.
    pub(crate) fn drain(&mut self, filter: &Filter, after: &str, budget: &mut usize) -> bool {
        while *budget != 0 {
            let Some((retired, next)) = self.cursor.next.get() else {
                return true;
            };
            *budget = budget.saturating_sub(1);
            if retired.offset >= self.visible
                && retired.subject.as_str() > after
                && filter.matches_str(&retired.subject)
                && self.seen.insert(retired.subject.clone())
                && retired.removed.seq.0 < self.visible
            {
                if let Some(bt) = retired.bt_ms {
                    self.overlay_bt.insert(retired.subject.clone(), bt);
                }
                self.overlay
                    .insert(retired.subject.clone(), retired.removed.clone());
            }
            let next = next.clone();
            self.cursor = next;
        }
        self.cursor.next.get().is_none()
    }
}

/// One bounded step. `Pending` is NOT a complete empty page.
pub enum LastStep {
    Pending,
    Page(Vec<Arc<BrokerRecord>>, Option<String>),
}

impl LastStep {
    /// Consume a ready page; `None` means more bounded work is still required.
    pub fn into_page(self) -> Option<(Vec<Arc<BrokerRecord>>, Option<String>)> {
        match self {
            Self::Pending => None,
            Self::Page(rows, after) => Some((rows, after)),
        }
    }
}

// Maintenance quantum, not a history lifetime or a data-eviction limit.
const PRUNE_WORK: usize = 64;

pub(crate) struct RetireHistory {
    owner: Arc<()>,
    head: Arc<Link>,
    tail: Arc<Link>,
    available: u64,
    published: u64,
    last_offset: Option<u64>,
    latest: BTreeMap<String, u64>,
}

impl RetireHistory {
    pub(crate) fn new(recovered_head: u64) -> Self {
        let head = Link::empty();
        Self {
            owner: Arc::new(()),
            head: head.clone(),
            tail: head,
            available: recovered_head,
            published: recovered_head,
            last_offset: None,
            latest: BTreeMap::new(),
        }
    }

    /// Only the private broker constructor, before handing the log to its threads.
    /// Recovery cannot supply a pre-open view: a lower quorum head is TooOld until
    /// it catches up, even though publishing that lower initial head is legitimate.
    pub(crate) fn start_published(&mut self, head: u64) {
        self.published = head;
    }

    pub(crate) fn view(&self, visible: u64) -> Result<LastView, LastViewError> {
        if last_view_not_before_avail(self.available, visible) == 0 {
            return Err(LastViewError::TooOld {
                requested: visible,
                available: self.available,
            });
        }
        if last_view_not_above_pub(self.published, visible) == 0 {
            return Err(LastViewError::NotPublished {
                requested: visible,
                published: self.published,
            });
        }
        Ok(LastView {
            owner: self.owner.clone(),
            visible,
            cursor: self.head.clone(),
            filter: None,
            after: String::new(),
            seen: BTreeSet::new(),
            overlay: BTreeMap::new(),
            overlay_bt: BTreeMap::new(),
        })
    }

    pub(crate) fn check(&self, view: &LastView) -> Result<(), LastViewError> {
        if Arc::ptr_eq(&self.owner, &view.owner) {
            Ok(())
        } else {
            Err(LastViewError::WrongOpen)
        }
    }

    #[cfg(test)]
    pub(crate) fn append(&mut self, subject: String, removed: Arc<BrokerRecord>, offset: u64) {
        self.append_with_bt(subject, removed, None, offset);
    }

    pub(crate) fn append_with_bt(
        &mut self,
        subject: String,
        removed: Arc<BrokerRecord>,
        bt_ms: Option<u64>,
        offset: u64,
    ) {
        let next = Link::empty();
        let retired = Retired {
            subject: subject.clone(),
            removed,
            bt_ms,
            offset,
        };
        // The tail is filled exactly once by the log's sole locked promoter.
        assert!(
            self.tail.next.set((retired, next.clone())).is_ok(),
            "retirement tail filled twice"
        );
        self.tail = next;
        self.last_offset = Some(offset);
        self.latest.insert(subject, offset);
    }

    pub(crate) fn pending(&self, subject: &str, visible: u64) -> Option<u64> {
        self.latest
            .get(subject)
            .copied()
            .filter(|offset| *offset >= visible)
    }

    /// The owner reports an ACTUAL published head, never a query's requested head.
    /// Limit partial-prefix trimming; a fully visible chain detaches in constant work.
    pub(crate) fn advance(&mut self, visible: u64) -> Result<LastViewGarbage, LastViewError> {
        if last_view_not_before_avail(self.published, visible) == 0 {
            return Err(LastViewError::PublishedBackwards {
                requested: visible,
                published: self.published,
            });
        }
        self.published = visible;
        self.available = last_view_available_advance(self.available, visible);
        if self.last_offset.is_none_or(|last| last < visible) {
            let history = std::mem::replace(&mut self.head, self.tail.clone());
            let latest = std::mem::take(&mut self.latest);
            return Ok(LastViewGarbage {
                _history: Some(history),
                _latest: latest,
            });
        }
        let max_steps = last_view_prune_clamp(PRUNE_WORK as u64, PRUNE_WORK as u64);
        let mut cursor = self.head.clone();
        if last_view_prune_within_quantum(max_steps, PRUNE_WORK as u64) {
            let mut step = 0u64;
            while step < max_steps {
                let Some((event, next)) = cursor.next.get() else {
                    break;
                };
                if event.offset >= visible {
                    break;
                }
                if self.latest.get(&event.subject) == Some(&event.offset) {
                    self.latest.remove(&event.subject);
                }
                let next = next.clone();
                cursor = next;
                step = step.saturating_add(1);
            }
        }
        if Arc::ptr_eq(&cursor, &self.head) {
            return Ok(LastViewGarbage::empty());
        }
        let history = std::mem::replace(&mut self.head, cursor);
        Ok(LastViewGarbage {
            _history: Some(history),
            _latest: BTreeMap::new(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use astream_wire::Offset;

    fn record(offset: u64, subject: &str, body: &[u8]) -> Arc<BrokerRecord> {
        Arc::new(BrokerRecord {
            seq: Offset(offset),
            producer_id: 7,
            producer_seq: offset + 1,
            subject: subject.into(),
            body: body.to_vec(),
            commit: None,
        })
    }

    #[test]
    fn a_view_keeps_future_retirements_but_the_store_releases_its_past() {
        let all = Filter::new("/>").unwrap();
        let mut history = RetireHistory::new(2);
        let mut old = history.view(2).unwrap();
        let payload = record(0, "/a/item", b"before the pin");
        let weak = Arc::downgrade(&payload);
        // The event did not exist when old was captured. A snapshot of only the
        // then-present events would miss it and would fail this control.
        history.append("/a/item".into(), payload, 2);
        let garbage = history.advance(3).unwrap();
        drop(garbage);
        assert!(
            weak.upgrade().is_some(),
            "the live old cursor owns the payload"
        );
        assert!(matches!(
            history.view(2),
            Err(LastViewError::TooOld {
                requested: 2,
                available: 3
            })
        ));
        let mut current = history.view(3).unwrap();
        let mut work = 1;
        assert!(current.drain(&all, "", &mut work));
        assert!(
            current.overlay.is_empty(),
            "a new view cannot resurrect the retired value"
        );
        let mut work = 1;
        assert!(old.drain(&all, "", &mut work));
        assert_eq!(work, 0);
        assert_eq!(old.overlay["/a/item"].seq, Offset(0));
        assert_eq!(old.overlay["/a/item"].body, b"before the pin");
        let returned = old.overlay["/a/item"].clone();
        drop(old);
        assert!(weak.upgrade().is_some(), "a returned handle still owns it");
        assert_eq!(returned.body, b"before the pin");
        drop(returned);
        assert!(
            weak.upgrade().is_none(),
            "publication, view release, and returned-handle release free it"
        );

        // Promotion can precede visibility. Capturing only the current tail would
        // miss this already-promoted but still hidden retirement.
        let mut held = RetireHistory::new(2);
        held.append("/a/held".into(), record(0, "/a/held", b"held"), 2);
        let mut pinned = held.view(2).unwrap();
        assert!(matches!(
            held.view(3),
            Err(LastViewError::NotPublished { .. })
        ));
        drop(held.advance(2).unwrap());
        assert_eq!(held.pending("/a/held", 2), Some(2));
        let mut work = 1;
        assert!(pinned.drain(&all, "", &mut work));
        assert_eq!(pinned.overlay["/a/held"].body, b"held");
        drop(held.advance(3).unwrap());
        assert_eq!(held.pending("/a/held", 3), None);
        assert!(matches!(
            held.advance(2),
            Err(LastViewError::PublishedBackwards { .. })
        ));

        // Each retirement visit consumes work, including one that finds no subject
        // index entry. Exhausting a step is Pending, not a complete empty answer.
        let mut bounded = RetireHistory::new(2);
        let mut view = bounded.view(2).unwrap();
        bounded.append("/a/one".into(), record(0, "/a/one", b"one"), 2);
        bounded.append("/a/two".into(), record(1, "/a/two", b"two"), 3);
        let mut work = 1;
        assert!(!view.drain(&all, "", &mut work));
        assert_eq!(work, 0);
        assert_eq!(view.overlay.len(), 1);
        let mut work = 1;
        assert!(view.drain(&all, "", &mut work));
        assert_eq!(view.overlay.len(), 2);
        assert_eq!(work, 0);

        // The first retirement after H supplies H's value. A later republish and
        // retirement of the same subject must not replace that evidence.
        let mut repeated = RetireHistory::new(2);
        let mut view = repeated.view(2).unwrap();
        repeated.append("/a/repeated".into(), record(0, "/a/repeated", b"first"), 2);
        repeated.append("/a/repeated".into(), record(3, "/a/repeated", b"later"), 4);
        let mut work = 2;
        assert!(view.drain(&all, "", &mut work));
        assert_eq!(view.overlay["/a/repeated"].body, b"first");
        let other = RetireHistory::new(2);
        assert_eq!(other.check(&view), Err(LastViewError::WrongOpen));
        view.bind(&all, "/a/a").unwrap();
        assert_eq!(view.bind(&all, ""), Err(LastViewError::CursorBackwards));
        assert_eq!(
            view.bind(&Filter::new("/other/>").unwrap(), "/a/a"),
            Err(LastViewError::ChangedFilter)
        );

        // A partially visible prefix is cleaned in bounded maintenance work.
        // The next view still charges any untrimmed old event before its pending
        // event, rather than scanning the whole prefix inside one Last step.
        let visible = u64::try_from(PRUNE_WORK).unwrap() + 2;
        let mut partial = RetireHistory::new(0);
        let first = record(0, "/a/partial/first", b"published");
        let first_weak = Arc::downgrade(&first);
        partial.append("/a/partial/first".into(), first, 1);
        for offset in 2..=visible {
            let subject = format!("/a/partial/{offset}");
            partial.append(subject.clone(), record(0, &subject, b"part"), offset);
        }
        drop(partial.advance(visible).unwrap());
        assert!(first_weak.upgrade().is_none());
        let mut partial_view = partial.view(visible).unwrap();
        let mut work = 1;
        assert!(!partial_view.drain(&all, "", &mut work));
        assert_eq!(work, 0);
        assert!(partial_view.overlay.is_empty());
        let mut work = 1;
        assert!(partial_view.drain(&all, "", &mut work));
        assert_eq!(work, 0);
        assert_eq!(partial_view.overlay.len(), 1);
        assert_eq!(
            partial_view.overlay[&format!("/a/partial/{visible}")].body,
            b"part"
        );

        // Independent payloads in an unshared chain are all released. The actual
        // Link Drop loop, rather than a recursively owned next field, handles it.
        let mut chain = RetireHistory::new(1);
        let mut weak = Vec::new();
        for offset in 1u8..9 {
            let payload = record(0, "/a/chain", &[offset]);
            weak.push(Arc::downgrade(&payload));
            chain.append("/a/chain".into(), payload, u64::from(offset));
        }
        let garbage = chain.advance(9).unwrap();
        assert!(weak.iter().all(|payload| payload.upgrade().is_some()));
        drop(garbage);
        assert!(weak.iter().all(|payload| payload.upgrade().is_none()));
    }
}
