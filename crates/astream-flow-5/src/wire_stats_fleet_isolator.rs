//! Multi-tenant fleet-scope capability isolator for `Request::Stats` (`broker.wire-stats`).

#[cfg(clean_islands)]
#[path = "wire_stats_fleet_isolator_island.rs"]
mod wire_stats_fleet_isolator_island;
#[cfg(clean_islands)]
pub use wire_stats_fleet_isolator_island::{stats_face_count_clamp, stats_last_bt_advance};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn stats_face_count_clamp(faces: u64) -> u64 {
    if faces < 4096 {
        faces
    } else {
        4096
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn stats_last_bt_advance(prev_bt: u64, sample_bt: u64) -> u64 {
    if prev_bt < sample_bt {
        sample_bt
    } else {
        prev_bt
    }
}

contract_fn! {
    #[must_use]
    pub const fn stats_grant_within_depth(grant_depth: u64) -> bool
    clauses [ensures result == (grant_depth < 3)]
    {
        grant_depth < 3
    }
}

#[inline]
#[must_use]
pub const fn stats_grant_covers_fleet(grant_depth: u64, fleet_match: u64) -> bool {
    stats_grant_within_depth(grant_depth) && fleet_match >= 1
}

const fn bytes_eq(mut a: &[u8], mut b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    while let [ha, ta @ ..] = a {
        let [hb, tb @ ..] = b else {
            return false;
        };
        if *ha != *hb {
            return false;
        }
        a = ta;
        b = tb;
    }
    true
}

const fn bytes_contains_slash(mut s: &[u8]) -> bool {
    while let [b, tail @ ..] = s {
        if *b == b'/' {
            return true;
        }
        s = tail;
    }
    false
}

/// Authorize a `Stats` query for `target_fleet` (`Some("alpha")` or `None` for root `/>`)
/// against a live attached capability grant pattern (e.g. `"/>"`, `"/f/alpha/>"`, or
/// narrow `"/f/alpha/in/n1/>"`).
#[must_use]
pub const fn grant_authorizes_stats(grant_pattern: &str, target_fleet: Option<&str>) -> bool {
    let g = grant_pattern.as_bytes();
    if bytes_eq(g, b"/>") {
        return stats_grant_covers_fleet(0, 1);
    }
    let Some(want_fleet) = target_fleet else {
        return false;
    };
    let [b'/', b'f', b'/', exact_fleet @ .., b'/', b'>'] = g else {
        return false;
    };
    // If `exact_fleet` contains `/`, it is a sub-fleet grant (`depth >= 3`), which R5 forbids.
    let depth = if bytes_contains_slash(exact_fleet) {
        3u64
    } else {
        2u64
    };
    let matched = if !exact_fleet.is_empty()
        && !bytes_eq(exact_fleet, b"*")
        && bytes_eq(exact_fleet, want_fleet.as_bytes())
    {
        1u64
    } else {
        0u64
    };
    stats_grant_covers_fleet(depth, matched)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admits_root_and_whole_fleet_grants_while_rejecting_narrow_and_sibling_grants() {
        assert!(grant_authorizes_stats("/>", None));
        assert!(grant_authorizes_stats("/>", Some("alpha")));
        assert!(grant_authorizes_stats("/f/alpha/>", Some("alpha")));
        assert!(!grant_authorizes_stats("/f/alpha/>", Some("beta")));
        assert!(!grant_authorizes_stats("/f/alpha/>", None));
        assert!(!grant_authorizes_stats("/f/alpha/in/n1/>", Some("alpha")));
        assert_eq!(stats_face_count_clamp(9999), 4096);
        assert_eq!(stats_last_bt_advance(100, 90), 100);
    }
}
