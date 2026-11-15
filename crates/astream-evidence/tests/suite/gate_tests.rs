//! The merge gate must reject each failure mode of the predecessor, pass clean code, and
//! — the ultimate proof — pass astream's own tree.

use astream_evidence::gate::{check_root, run_gate, Violation};
use std::path::{Path, PathBuf};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(name)
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..")
}

fn has(violations: &[Violation], lint: &str) -> bool {
    violations.iter().any(|v| v.lint == lint)
}

fn details<'a>(violations: &'a [Violation], lint: &str) -> Vec<&'a str> {
    violations
        .iter()
        .filter(|v| v.lint == lint)
        .map(|v| v.detail.as_str())
        .collect()
}

/// Removes a test's scratch directory when dropped, so the test leaves nothing behind
/// whether it passes or panics.
struct Cleanup(std::path::PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn rejects_undeclared_cfg_feature() {
    let v = run_gate(&fixture("undeclared_cfg"));
    assert!(
        has(&v, "undeclared-cfg"),
        "expected undeclared-cfg; got {v:?}"
    );
}

#[test]
fn optional_dependency_features_follow_cargos_rules() {
    // An optional dependency declares a like-named feature — in a target table
    // too — unless `dep:` names it in [features], which suppresses that feature.
    let v = run_gate(&fixture("undeclared_cfg_optional"));
    let d = details(&v, "undeclared-cfg");
    assert_eq!(d.len(), 1, "exactly the dep:-suppressed feature; got {v:?}");
    assert!(d[0].contains("\"hidden\""), "{v:?}");
}

#[test]
fn rejects_drift_and_unlinked_task_markers() {
    let v = run_gate(&fixture("drift"));
    assert!(has(&v, "drift-marker"), "expected drift-marker; got {v:?}");

    // Exercise the public gate over a file this case owns: a linked task note
    // accepts the same Unicode spacing as the old text scanner.
    let base = std::env::temp_dir().join(format!("astream-gate-linked-{}", std::process::id()));
    std::fs::create_dir(&base).expect("exclusive scratch dir");
    let _tmp = Cleanup(base.clone());
    let note = base.join("notes.md");
    let marker = astream_evidence::needles::task_marker();
    for spacing in [" ", "\t", "\u{a0}", "\u{2003}", "\u{b}"] {
        std::fs::write(&note, format!("{marker}{spacing}(#123) explained\n")).expect("linked note");
        let v = run_gate(&base);
        assert!(
            !has(&v, "drift-marker"),
            "a numeric issue link remains linked: {v:?}"
        );
    }
    std::fs::write(&note, format!("{marker}\u{a0}(#not-an-issue)\n")).expect("invalid link");
    assert!(has(&run_gate(&base), "drift-marker"));
    std::fs::write(
        &note,
        format!("{marker}\u{a0}(#123) then {marker} without a link\n"),
    )
    .expect("second unlinked note");
    assert!(has(&run_gate(&base), "drift-marker"));
}

#[test]
fn rejects_constant_only_test() {
    let v = run_gate(&fixture("tautology"));
    assert!(has(&v, "tautology"), "expected tautology; got {v:?}");
}

#[test]
fn rejects_git_dependency() {
    let v = run_gate(&fixture("gitdep"));
    assert!(has(&v, "no-git-deps"), "expected no-git-deps; got {v:?}");
}

#[test]
fn rejects_single_quoted_git_dependency() {
    // `git = '...'` is valid TOML that cargo resolves as a git dependency.
    let v = run_gate(&fixture("gitdep_singlequote"));
    assert!(has(&v, "no-git-deps"), "expected no-git-deps; got {v:?}");
}

#[test]
fn rejects_oddly_spaced_git_dependency() {
    // `git  =  "..."` — odd whitespace is still a git dependency.
    let v = run_gate(&fixture("gitdep_spaced"));
    assert!(has(&v, "no-git-deps"), "expected no-git-deps; got {v:?}");
}

#[test]
fn rejects_git_dependency_in_patch_table() {
    // `[patch.crates-io] x = { git = ... }` is the canonical way to redirect a
    // registry crate to a git checkout; the dependency tables stay clean.
    let v = run_gate(&fixture("gitdep_patch"));
    let d = details(&v, "no-git-deps");
    assert!(
        d.iter().any(|d| d.contains("\"sha2\"")),
        "the patched git dependency must be flagged; got {v:?}"
    );
}

#[test]
fn rejects_git_dependency_in_replace_table() {
    let v = run_gate(&fixture("gitdep_replace"));
    let d = details(&v, "no-git-deps");
    assert!(
        d.iter().any(|d| d.contains("toml:0.8.0")),
        "the replaced git dependency must be flagged; got {v:?}"
    );
}

#[test]
fn rejects_git_source_in_lockfile_without_manifest() {
    // Cargo.lock is what cargo actually fetches: a `git+` source there is a
    // git dependency however it entered the graph. This fixture has no
    // manifest: lockfile scanning must not depend on a nearby Cargo.toml.
    let v = run_gate(&fixture("gitdep_lock"));
    let d = details(&v, "no-git-deps");
    assert!(
        d.iter()
            .any(|d| d.contains("\"sketchy\"") && d.contains("git source")),
        "the locked git source must be flagged; got {v:?}"
    );
    assert!(
        v.iter().any(|x| x.path.ends_with("Cargo.lock")),
        "the finding must point at the lockfile; got {v:?}"
    );
}

#[test]
fn rejects_asymmetric_spacing_undeclared_cfg() {
    // The ghost2 / ghost3 references in the fixture use asymmetric and tab
    // spacing around the '='; each must be caught by name, proving the
    // whitespace-insensitive scan. (The literal trigger lives only in the
    // fixture, never here, so this test file does not flag itself.)
    let v = run_gate(&fixture("undeclared_cfg"));
    let d = details(&v, "undeclared-cfg");
    assert!(
        d.iter().any(|d| d.contains("ghost2")),
        "asymmetric-spaced ghost2 must be caught; got {d:?}"
    );
    assert!(
        d.iter().any(|d| d.contains("ghost3")),
        "asymmetric-spaced ghost3 must be caught; got {d:?}"
    );
}

#[test]
fn rejects_newline_spaced_undeclared_cfg() {
    // A line break around the `=` is whitespace to the attribute grammar too;
    // a space/tab-only skip left ghost4 invisible.
    let v = run_gate(&fixture("undeclared_cfg"));
    let d = details(&v, "undeclared-cfg");
    assert!(
        d.iter().any(|d| d.contains("ghost4")),
        "newline-spaced ghost4 must be caught; got {d:?}"
    );
}

#[test]
fn rejects_verify_path_dependency_edge() {
    // A verify* crate as a PATH dependency enters the build graph without being
    // a workspace member; the member-only check missed it.
    let v = run_gate(&fixture("verify_pathdep"));
    assert!(
        has(&v, "verify-isolation"),
        "a verify* path-dependency must be flagged; got {v:?}"
    );
}

#[test]
fn rejects_verify_path_dependency_edge_in_a_target_table() {
    let v = run_gate(&fixture("verify_target_pathdep"));
    assert!(
        has(&v, "verify-isolation"),
        "a verify* path-dependency under [target.*] must be flagged; got {v:?}"
    );
}

#[test]
fn rejects_type_suffix_and_bool_tautology() {
    // A type-suffixed numeric constant and a boolean-only assertion are
    // constant-only "proofs" too; the laundered forms live in the fixture, not
    // here.
    let v = run_gate(&fixture("tautology_suffix"));
    assert!(has(&v, "tautology"), "expected tautology; got {v:?}");
}

#[test]
fn rejects_message_and_cast_laundered_tautologies() {
    // The assertion-message form and the `as`-cast form (see the fixture; the
    // literal forms are not repeated here, where the gate would find them): a
    // message's words and a cast's type name are not symbols under test. The
    // fixture holds exactly these two tests, so exactly two findings.
    let v = run_gate(&fixture("tautology_laundered"));
    let n = details(&v, "tautology").len();
    assert_eq!(n, 2, "both laundered forms must be flagged; got {v:?}");
}

#[test]
fn rejects_drift_markers_in_widened_fileset() {
    // A checkpoint marker and a fake issue link, hiding in .txt and an
    // extension-less NOTES file rather than .rs/.md/.toml.
    let v = run_gate(&fixture("drift_variants"));
    assert!(has(&v, "drift-marker"), "expected drift-marker; got {v:?}");
    assert!(
        v.iter().any(|x| x.path.contains("notes.txt")),
        "the .txt note must be scanned; got {v:?}"
    );
}

#[test]
fn rejects_drift_marker_in_non_utf8_file() {
    // One Latin-1 byte makes `read_to_string` fail; the file must still be
    // scanned, or that byte would hide every marker in it.
    let v = run_gate(&fixture("drift_nonutf8"));
    let d = details(&v, "drift-marker");
    assert!(
        d.iter().any(|d| d.contains("incomplete-checkpoint")),
        "the marker behind a non-UTF-8 byte must be caught; got {v:?}"
    );
}

#[test]
fn rejects_an_unlinked_task_marker_after_a_linked_one_on_the_same_line() {
    // Every marker on a line needs its own link: one linked note must not
    // license an unlinked one after it.
    let v = run_gate(&fixture("drift_second_marker"));
    let d = details(&v, "drift-marker");
    assert_eq!(d.len(), 2, "one finding each on lines 1 and 3; got {v:?}");
    assert!(
        d[0].starts_with("line 1: task note without an issue link"),
        "{v:?}"
    );
    assert!(
        d[1].starts_with("line 3: task note without an issue link"),
        "{v:?}"
    );
}

#[test]
fn scans_directories_merely_named_fixtures() {
    // Only the gate's OWN fixtures path is exempt; a `fixtures` directory
    // anywhere else was a one-`mkdir` bypass of every lint.
    let v = run_gate(&fixture("fixtures_elsewhere"));
    assert!(
        v.iter()
            .any(|x| x.lint == "drift-marker" && x.path.contains("fixtures/notes.md")),
        "a violation under src/fixtures/ must be found; got {v:?}"
    );
}

#[cfg(unix)]
#[test]
fn does_not_follow_symlinks() {
    // A link to a parent (`..`), an outside directory, or an outside file must
    // neither re-walk the tree nor pull out-of-tree findings into the scan.
    let base = std::env::temp_dir().join(format!("astream-gate-symlink-{}", std::process::id()));
    let _tmp = Cleanup(base.clone());
    let outside = base.join("outside");
    let root = base.join("root");
    std::fs::create_dir_all(&outside).expect("temp dirs");
    std::fs::create_dir_all(&root).expect("temp dirs");
    // The marker is assembled so this test source never carries it.
    let note = format!("[{}] out-of-tree checkpoint\n", "INCOMPLETE");
    std::fs::write(outside.join("notes.md"), note).expect("outside note");
    std::os::unix::fs::symlink("../outside", root.join("link")).expect("dir symlink");
    std::os::unix::fs::symlink("..", root.join("loop")).expect("parent symlink");
    std::os::unix::fs::symlink("../outside/notes.md", root.join("filelink")).expect("file symlink");

    let v = run_gate(&root);
    std::fs::remove_dir_all(&base).expect("cleanup");
    assert!(
        v.is_empty(),
        "nothing behind a symlink may be scanned; got {v:?}"
    );
}

#[test]
fn skips_named_tool_state_dirs_but_scans_every_other_dot_directory() {
    // Only NAMED tool-state directories are pruned — `.git`, an editor's
    // `.idea`, an agent harness's `.claude/worktrees/<run>` holding a whole
    // checkout of this repo. None of that is this tree's source, so a violation
    // planted there must not be reported. Every OTHER dot-directory is source:
    // `helper = { path = "../.vendor/helper" }` is a dependency cargo compiles,
    // so a cfg typo in it dead-codes a module that really ships — the exact
    // predecessor class. Pruning it by name shape would hide that from every lint.
    let base = std::env::temp_dir().join(format!("astream-gate-hidden-{}", std::process::id()));
    let _tmp = Cleanup(base.clone());
    let git_dep = "[package]\nname = \"x\"\n[dependencies]\nfoo = { git = \"https://example.invalid/foo\" }\n";
    // Assembled at runtime so this file never literally contains the trigger:
    // the gate scans its own tree (see `passes_on_the_real_repo`).
    let undeclared_cfg = format!("#[cfg({} = \"ghost\")]\nmod extra;\n", "feature");
    let helper_manifest = "[package]\nname = \"helper\"\nversion = \"0.0.0\"\n";

    let harness = base.join(".claude").join("worktrees").join("run-1");
    std::fs::create_dir_all(harness.join("src")).expect("temp dirs");
    std::fs::write(harness.join("Cargo.toml"), git_dep).expect("harness Cargo.toml");
    std::fs::write(harness.join("src").join("lib.rs"), &undeclared_cfg).expect("harness lib.rs");
    let v = run_gate(&base);
    assert!(
        !has(&v, "no-git-deps") && !has(&v, "undeclared-cfg"),
        "nothing inside a NAMED tool-state directory may be scanned; got {v:?}"
    );

    // A dot-directory that is NOT on the list is scanned like any source tree.
    let vendored = base.join(".vendor").join("helper");
    std::fs::create_dir_all(vendored.join("src")).expect("temp dirs");
    std::fs::write(vendored.join("Cargo.toml"), helper_manifest).expect("vendored Cargo.toml");
    std::fs::write(vendored.join("src").join("lib.rs"), &undeclared_cfg).expect("vendored lib.rs");
    let v = run_gate(&base);
    assert!(
        v.iter()
            .any(|x| x.lint == "undeclared-cfg" && x.path.contains(".vendor")),
        "a path dependency vendored into an unlisted dot-directory must still be linted; got {v:?}"
    );

    // Control: the identical git dependency outside any dot-directory.
    let visible = base.join("visible");
    std::fs::create_dir_all(&visible).expect("temp dirs");
    std::fs::write(visible.join("Cargo.toml"), git_dep).expect("visible Cargo.toml");
    let v = run_gate(&base);
    std::fs::remove_dir_all(&base).expect("cleanup");
    assert!(
        has(&v, "no-git-deps"),
        "the control violation outside the hidden directory must be reported; got {v:?}"
    );
}

#[test]
fn a_non_utf8_manifest_is_still_scanned_for_git_dependencies() {
    // Cargo requires UTF-8 manifests, but the gate must not treat a decoding
    // error as "no findings": one stray Latin-1 byte in a comment would
    // otherwise bypass the manifest scan (as `read_text_lossy` prevents for the
    // marker lints).
    let base = std::env::temp_dir().join(format!("astream-gate-latin1-{}", std::process::id()));
    let _tmp = Cleanup(base.clone());
    std::fs::create_dir_all(&base).expect("temp dirs");
    let mut bytes = b"# caf\xe9\n[package]\nname = \"x\"\n[dependencies]\n".to_vec();
    bytes.extend_from_slice(b"foo = { git = \"https://example.invalid/foo\" }\n");
    std::fs::write(base.join("Cargo.toml"), &bytes).expect("non-UTF-8 Cargo.toml");
    let v = run_gate(&base);
    std::fs::remove_dir_all(&base).expect("cleanup");
    assert!(
        has(&v, "no-git-deps"),
        "a git dependency in a non-UTF-8 manifest must still be reported; got {v:?}"
    );
}

#[test]
fn rejects_duplicate_evidence_blocks() {
    // A second, hand-edited evidence block pasted after the first must not slip
    // past the (first-region-only) comparison. The fixture's FIRST block is
    // byte-identical to the manifest render, so the duplicate is the ONLY
    // thing wrong with it: the finding must be the duplicate-marker rejection,
    // not a stale-content mismatch that would fire anyway.
    let v = run_gate(&fixture("doc_dup"));
    let d = details(&v, "doc-tamper");
    assert!(
        d.iter().any(|d| d.contains("duplicated")),
        "expected the duplicated-markers finding; got {v:?}"
    );
    assert!(
        !d.iter().any(|d| d.contains("stale")),
        "the first block must match the render exactly; got {v:?}"
    );
}

#[test]
fn manifest_integrity_rejects_noop_command() {
    // A confident claim backed by `command = "true"` is decorative evidence.
    let v = run_gate(&fixture("noop_evidence"));
    assert!(
        has(&v, "manifest-integrity"),
        "expected manifest-integrity; got {v:?}"
    );
}

#[test]
fn manifest_integrity_rejects_every_denylisted_noop() {
    // Each program the claim text names (and the rest of the denylist, and an
    // absolute path to one) must be rejected individually.
    let v = run_gate(&fixture("noop_evidence_all"));
    for id in [
        "noop.true",
        "noop.colon",
        "noop.echo",
        "noop.printf",
        "noop.cat",
        "noop.head",
        "noop.tail",
        "noop.absolute",
    ] {
        assert!(
            v.iter().any(|x| x.lint == "manifest-integrity"
                && x.path.contains(id)
                && x.detail.contains("no-op command")),
            "{id} must be rejected as a no-op; got {v:?}"
        );
    }
}

#[test]
fn manifest_integrity_rejects_command_that_does_not_fit_its_kind() {
    let v = run_gate(&fixture("kind_shape"));
    let flagged = |id: &str, needle: &str| {
        v.iter().any(|x| {
            x.lint == "manifest-integrity" && x.path.contains(id) && x.detail.contains(needle)
        })
    };
    assert!(
        flagged("test.not.targo.test", "must be `targo --unverified test"),
        "a test claim not running targo test must be flagged; got {v:?}"
    );
    assert!(
        flagged(
            "build.not.targo.build",
            "must run `targo --unverified build|check"
        ),
        "a build claim not building must be flagged; got {v:?}"
    );
    assert!(
        flagged("selftest.unpinned", "expected_output_sha"),
        "an unpinned selftest must be flagged; got {v:?}"
    );
    assert!(
        !v.iter().any(|x| x.path.contains("shaped.fine")),
        "a well-shaped claim must not be flagged; got {v:?}"
    );
}

#[test]
fn manifest_integrity_rejects_stock_toolchain_and_unnamed_lanes() {
    // astream's claims run on the Trust toolchain: a stock program (in any `&&`
    // step, behind env assignments), a rustup `+toolchain` selector, and a
    // compiling targo verb with no lane are each rejected.
    let v = run_gate(&fixture("stock_toolchain"));
    let flagged = |id: &str, needle: &str| {
        v.iter().any(|x| {
            x.lint == "manifest-integrity"
                && x.path.ends_with(&format!("[{id}]"))
                && x.detail.contains(needle)
        })
    };
    for (id, needle) in [
        ("stock.cargo", "stock Rust toolchain (`cargo`)"),
        ("stock.chained", "stock Rust toolchain (`cargo`)"),
        ("stock.rustup", "stock Rust toolchain (`rustup`)"),
        ("lane.missing", "names no lane"),
        ("lane.selector", "`+nightly` selects a rustup toolchain"),
    ] {
        assert!(
            flagged(id, needle),
            "{id} must be rejected ({needle}); got {v:?}"
        );
    }
    for id in ["unverified.fine", "trust.fine"] {
        assert!(
            !v.iter().any(|x| x.path.ends_with(&format!("[{id}]"))),
            "{id} names its lane on every step; got {v:?}"
        );
    }
}

#[test]
fn manifest_integrity_rejects_unknown_kind() {
    let v = run_gate(&fixture("bad_kind"));
    let d = details(&v, "manifest-integrity");
    assert!(
        d.iter().any(|d| d.contains("unknown kind")),
        "a misspelled kind must be rejected; got {v:?}"
    );
}

#[test]
fn manifest_integrity_rejects_unknown_platform() {
    let v = run_gate(&fixture("bad_platform"));
    let d = details(&v, "manifest-integrity");
    assert!(
        d.iter().any(|d| d.contains("unknown platform")),
        "a platform that matches no host must be rejected; got {v:?}"
    );
}

#[test]
fn manifest_integrity_rejects_claim_citing_missing_artifact() {
    // A claim whose command cites a script absent from the tree must fail at
    // gate time, not only when `run` executes it.
    let v = run_gate(&fixture("missing_artifact"));
    assert!(
        has(&v, "manifest-integrity"),
        "expected manifest-integrity; got {v:?}"
    );
}

#[test]
fn manifest_integrity_does_not_read_an_env_assignment_as_a_cited_path() {
    let v = run_gate(&fixture("env_path_assignment"));
    assert!(
        v.is_empty(),
        "an env assignment is not a cited path; got {v:?}"
    );
}

#[test]
fn manifest_integrity_rejects_a_noop_behind_env_assignments() {
    // `VAR=value echo ...` runs `echo`: the assignments are not the program.
    let v = run_gate(&fixture("noop_env_prefix"));
    assert!(
        v.iter().any(|x| x.lint == "manifest-integrity"
            && x.path.contains("noop.behind.env")
            && x.detail.contains("no-op command")),
        "a no-op behind env assignments must be rejected; got {v:?}"
    );
}

#[test]
fn manifest_integrity_rejects_a_command_that_can_mask_its_exit_status() {
    // `targo --unverified test ... || true` and its relatives exit 0 whatever the tests did,
    // so the claim would read as verified over a failure.
    let v = run_gate(&fixture("masked_status"));
    let masked = |id: &str| {
        v.iter().any(|x| {
            x.lint == "manifest-integrity"
                && x.path.ends_with(&format!("[{id}]"))
                && x.detail.contains("failing exit status")
        })
    };
    for id in [
        "masked.or",
        "masked.semicolon",
        "masked.pipe",
        "masked.background",
        "masked.newline",
        "masked.negated",
    ] {
        assert!(masked(id), "{id} must be rejected; got {v:?}");
    }
    for id in ["chained.fine", "quoted.fine", "redirect.fine"] {
        assert!(!masked(id), "{id} cannot mask a failure; got {v:?}");
    }
}

#[test]
fn check_root_refuses_what_is_not_a_workspace() {
    // Process-unique: a fixed shared temp path that something else has created
    // turns this into a silent false pass (refused for the wrong reason).
    let missing =
        std::env::temp_dir().join(format!("astream-gate-no-such-root-{}", std::process::id()));
    assert!(
        check_root(&missing).is_err(),
        "a nonexistent root must be refused"
    );
    // A crate directory: has a Cargo.toml but no manifest/README to judge.
    let err = check_root(&fixture("clean")).expect_err("a bare crate dir must be refused");
    assert!(err.contains("not an astream workspace root"), "{err}");
    check_root(&repo_root()).expect("the repository root is a workspace root");
}

#[test]
fn rejects_trust_only_syntax_a_stock_rustc_would_open() {
    // An inline island, an island file mounted without cfg(clean_islands), and a bare
    // contract clause; the gated island file and the clause inside `contract_fn!` pass.
    let v = run_gate(&fixture("stock_lexable"));
    let d = details(&v, "stock-lexable");
    assert_eq!(
        d.len(),
        3,
        "exactly the three stock-unreadable spots; got {v:?}"
    );
    assert!(d[0].starts_with("line 2: an inline `clean"), "{v:?}");
    assert!(d[1].contains("`mod ungated_island;` is not gated"), "{v:?}");
    assert!(d[2].starts_with("line 17: a bare contract clause"), "{v:?}");
}

#[test]
fn passes_clean_fixture() {
    let v = run_gate(&fixture("clean"));
    assert!(v.is_empty(), "clean fixture must pass; got {v:?}");
}

#[test]
fn passes_on_the_real_repo() {
    // astream's own tree must pass its own gate — including this gate's source,
    // which must never trip its own lints (see needles.rs).
    let v = run_gate(&repo_root());
    assert!(v.is_empty(), "astream must pass its own gate; got {v:?}");
}

#[test]
fn a_build_directory_is_skipped_by_its_tag_whatever_it_is_named() {
    // A build directory can carry a name `SKIP_DIRS` does not hold (`target` as
    // a symlink to `target.noindex`; symlinks are never followed). Walked like
    // source, its compiled binaries report their marker words as this tree's
    // violations, so the cache tag, not the name, must be what skips it.
    const SIG: &str = "Signature: 8a477f597d28d172789f06886806bc55";
    let base = std::env::temp_dir().join(format!("astream-gate-cache-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let _tmp = Cleanup(base.clone());
    let build = base.join("target.noindex/debug/deps");
    std::fs::create_dir_all(&build).expect("temp dirs");
    // A file the drift lint would certainly report, inside the build tree.
    // ASSEMBLED, never a literal: a test that spelled the marker out would be
    // caught by the gate reading THIS file — which is the same discipline
    // `src/needles.rs` keeps, and `passes_on_the_real_repo` is what enforces it.
    let marker = format!(
        "// {}: a half-finished note\n",
        astream_evidence::needles::task_marker()
    );
    std::fs::write(build.join("blob.rs"), marker).expect("blob");

    // Untagged, it is ordinary source under an unremarkable name, and IS scanned
    // — so this test cannot pass merely because the fixture is empty.
    let before = run_gate(&base);
    assert!(
        before.iter().any(|x| x.path.contains("target.noindex")),
        "an untagged directory must be scanned; got {before:?}"
    );

    // Tagged, it is a tool cache and is skipped, whatever it is called.
    std::fs::write(
        base.join("target.noindex/CACHEDIR.TAG"),
        format!("{SIG}\n# This file is a cache directory tag.\n"),
    )
    .expect("tag");
    let after = run_gate(&base);
    assert!(
        !after.iter().any(|x| x.path.contains("target.noindex")),
        "a CACHEDIR.TAG directory must not be scanned; got {after:?}"
    );

    // And the skip is NAMED, never silent: one file creating an exclusion has to
    // be readable in the gate's own output.
    let (_v, caches) = astream_evidence::gate::run_gate_reporting(&base);
    assert!(
        caches.iter().any(|d| d.ends_with("target.noindex")),
        "the skipped cache must be reported; got {caches:?}"
    );

    // A tag whose signature is wrong is NOT a cache tag: the spec's line is the
    // whole check, so a file merely named CACHEDIR.TAG cannot hide source.
    std::fs::write(
        base.join("target.noindex/CACHEDIR.TAG"),
        "not the signature\n",
    )
    .expect("tag");
    let forged = run_gate(&base);
    assert!(
        forged.iter().any(|x| x.path.contains("target.noindex")),
        "only the spec signature counts; got {forged:?}"
    );
}

fn unsafe_cordon_level(src: &str) -> Option<&'static str> {
    let file = syn::parse_file(src).ok()?;
    let mut level = None;
    for attr in file.attrs {
        let Some(next) = ["allow", "expect", "warn", "deny", "forbid"]
            .into_iter()
            .find(|name| attr.path().is_ident(*name))
        else {
            continue;
        };
        let arguments = attr
            .parse_args_with(
                syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
            )
            .ok()?;
        if arguments
            .iter()
            .any(|arg| matches!(arg, syn::Meta::Path(path) if path.is_ident("unsafe_code")))
        {
            if level == Some("forbid") && next != "forbid" {
                return None;
            }
            level = Some(next);
        }
    }
    level
}

fn audit_unsafe_cordon(crates_dir: &Path) -> Vec<String> {
    let mut violations = Vec::new();
    let Ok(entries) = std::fs::read_dir(crates_dir) else {
        violations.push(format!("missing crates dir: {}", crates_dir.display()));
        return violations;
    };
    let mut crate_dirs: Vec<PathBuf> = entries
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir() && p.join("Cargo.toml").is_file())
        .collect();
    crate_dirs.sort();
    for crate_dir in crate_dirs {
        let Some(crate_name) = crate_dir.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        let mut roots: Vec<(String, PathBuf)> = Vec::new();
        for rel in ["src/lib.rs", "src/main.rs"] {
            let p = crate_dir.join(rel);
            if p.is_file() {
                roots.push((rel.to_string(), p));
            }
        }
        if let Ok(bins) = std::fs::read_dir(crate_dir.join("src/bin")) {
            let mut bin_files: Vec<PathBuf> = bins
                .flatten()
                .map(|e| e.path())
                .filter(|p| p.is_file() && p.extension().and_then(|e| e.to_str()) == Some("rs"))
                .collect();
            bin_files.sort();
            for p in bin_files {
                if let Some(fname) = p.file_name().and_then(|n| n.to_str()) {
                    roots.push((format!("src/bin/{fname}"), p));
                }
            }
        }
        for (rel, path) in roots {
            let src = std::fs::read_to_string(&path).unwrap_or_default();
            let is_cordon_lib = (crate_name == "astream-sys" || crate_name == "astream-host")
                && rel == "src/lib.rs";
            let required = if is_cordon_lib { "deny" } else { "forbid" };
            if unsafe_cordon_level(&src) != Some(required) {
                violations.push(format!(
                    "{crate_name}/{rel}: missing #![{required}(unsafe_code)]"
                ));
            }
        }
    }
    violations
}

#[test]
fn every_workspace_crate_and_binary_root_enforces_the_unsafe_cordon() {
    let real = audit_unsafe_cordon(&repo_root().join("crates"));
    assert!(
        real.is_empty(),
        "every non-cordon lib/bin root must carry #![forbid(unsafe_code)] \
         and cordon lib roots #![deny(unsafe_code)]: {real:?}"
    );

    // Only a valid crate-level policy counts; comments, strings and nested
    // module attributes cannot supply it.
    let base = std::env::temp_dir().join(format!("astream-cordon-audit-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let _tmp = Cleanup(base.clone());
    std::fs::create_dir_all(base.join("rogue/src/bin")).expect("mkdir rogue");
    std::fs::write(
        base.join("rogue/Cargo.toml"),
        "[package]\nname = \"rogue\"\n",
    )
    .expect("write Cargo.toml");
    std::fs::write(
        base.join("rogue/src/bin/tool.rs"),
        "// #![forbid(unsafe_code)]\nfn main() {}\n",
    )
    .expect("write tool.rs");
    let caught = audit_unsafe_cordon(&base);
    assert_eq!(
        caught,
        vec!["rogue/src/bin/tool.rs: missing #![forbid(unsafe_code)]".to_string()]
    );

    for body in [
        "/* #![forbid(unsafe_code)] */\nfn main() {}\n",
        "const NOTE: &str = \"#![forbid(unsafe_code)]\";\nfn main() {}\n",
        "const NOTE: &str = r#\"#![forbid(unsafe_code)]\"#;\nfn main() {}\n",
        "mod nested { #![forbid(unsafe_code)] }\nfn main() {}\n",
        "#![forbid(unsafe_code)]\n#![allow(unsafe_code)]\nfn main() {}\n",
        "#![forbid(unsafe_code)]\nfn main( {\n",
    ] {
        std::fs::write(base.join("rogue/src/bin/tool.rs"), body).expect("write inert mention");
        assert_eq!(
            audit_unsafe_cordon(&base),
            vec!["rogue/src/bin/tool.rs: missing #![forbid(unsafe_code)]".to_string()],
            "the root requires a valid, effective crate policy: {body}"
        );
    }

    // A grouped crate attribute is effective even when a preceding doc string
    // contains `//`. Module-local allowances do not lower the cordon lib's root.
    std::fs::write(
        base.join("rogue/src/bin/tool.rs"),
        "#![doc = \"https://example.invalid\"] #![forbid(dead_code, unsafe_code)]\nfn main() {}\n",
    )
    .expect("write grouped policy");
    std::fs::create_dir_all(base.join("astream-sys/src")).expect("mkdir cordon");
    std::fs::write(
        base.join("astream-sys/Cargo.toml"),
        "[package]\nname = \"astream-sys\"\n",
    )
    .expect("write cordon Cargo.toml");
    std::fs::write(
        base.join("astream-sys/src/lib.rs"),
        "#![deny(unsafe_code)]\nmod ffi { #![allow(unsafe_code)] }\n",
    )
    .expect("write cordon policy");
    assert!(audit_unsafe_cordon(&base).is_empty());

    for body in [
        "#![deny(unsafe_code)]\n#![allow(unsafe_code)]\n",
        "mod nested { #![deny(unsafe_code)] }\n",
    ] {
        std::fs::write(base.join("astream-sys/src/lib.rs"), body)
            .expect("write ineffective policy");
        assert_eq!(
            audit_unsafe_cordon(&base),
            vec!["astream-sys/src/lib.rs: missing #![deny(unsafe_code)]".to_string()],
            "the cordon lib requires an effective crate-level policy: {body}"
        );
    }
}
