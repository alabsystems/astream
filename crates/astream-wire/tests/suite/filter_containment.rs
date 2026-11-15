//! Claim `wire.filter.containment`: `Filter::contains` is SOUND — over a
//! generated subject space, `A.contains(B)` implies every subject matching `B`
//! also matches `A` (never a false positive), so a capability ACL built on it is
//! only ever too strict, never too permissive. Plus known cases and reflexivity.

use astream_wire::{Filter, Subject};

fn f(s: &str) -> Filter {
    Filter::new(s).unwrap()
}

#[test]
fn containment_known_cases() {
    assert!(f("/a/>").contains(&f("/a/x/out")));
    assert!(f("/a/>").contains(&f("/a/>")));
    assert!(f("/a/>").contains(&f("/a/x/>")));
    assert!(!f("/a/>").contains(&f("/a"))); // `>` needs a 1+ tail
    assert!(!f("/a/>").contains(&f("/>"))); // `/>` also matches /z/...
    assert!(f("/a/*/out").contains(&f("/a/x/out")));
    assert!(f("/a/*").contains(&f("/a/x")));
    assert!(!f("/a/*").contains(&f("/a/>"))); // `*` is exactly one, `>` is 1+
    assert!(!f("/a/*").contains(&f("/a/x/y")));
    assert!(f("/a/x/out").contains(&f("/a/x/out")));
    assert!(!f("/a/x/out").contains(&f("/a/x/err")));
    assert!(!f("/a/x").contains(&f("/a/x/out")));
    for p in ["/a", "/a/b", "/a/*", "/a/>", "/a/*/c", "/>"] {
        assert!(f(p).contains(&f(p)), "contains must be reflexive: {p}");
    }
}

// All `/`-rooted subjects of length 1..=3 over a small alphabet.
fn subject_space() -> Vec<String> {
    let alpha = ["a", "b", "x", "out", "c"];
    let mut out = Vec::new();
    for a in alpha {
        out.push(format!("/{a}"));
        for b in alpha {
            out.push(format!("/{a}/{b}"));
            for c in alpha {
                out.push(format!("/{a}/{b}/{c}"));
            }
        }
    }
    out
}

#[test]
fn containment_is_sound_over_the_subject_space() {
    let filters = [
        "/a/>", "/a/*", "/a/*/out", "/a/x/out", "/a/b/>", "/>", "/a/*/*", "/a/b/c", "/*/out", "/*",
    ];
    let subjects: Vec<Subject> = subject_space()
        .iter()
        .map(|s| Subject::new(s.as_str()).unwrap())
        .collect();

    let mut checked = 0u64;
    for &fa in &filters {
        for &fb in &filters {
            let (a, b) = (f(fa), f(fb));
            if a.contains(&b) {
                for s in &subjects {
                    if b.matches(s) {
                        assert!(
                            a.matches(s),
                            "UNSOUND: {fa} contains {fb}, but {} matches {fb} and NOT {fa}",
                            s.as_str()
                        );
                        checked += 1;
                    }
                }
            }
        }
    }
    assert!(
        checked > 0,
        "the soundness check must actually exercise matches"
    );
}
