// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The tests of [`crate::capfile`], kept out of `capfile.rs` because `asb` and
//! `aspump` compile that file into themselves by path: in it, every one of these
//! would run again in each binary, over the same source under the same cfg.

use crate::capfile::*;

/// A tag whose bytes are `base, base+1, …`, so eight of them cover every byte
/// value once.
fn tag_from(base: u8) -> [u8; TAG_BYTES] {
    let mut tag = [0u8; TAG_BYTES];
    for (i, b) in tag.iter_mut().enumerate() {
        *b = base.wrapping_add(i as u8);
    }
    tag
}

fn hex_of(tag: &[u8; TAG_BYTES]) -> String {
    tag.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn debug_output_names_the_grant_but_never_the_tag() {
    let line = Line {
        grant: "ro:/f/F/>".to_string(),
        tag: tag_from(0xa0),
    };
    assert_eq!(
        format!("{line:?}"),
        r#"Line { grant: "ro:/f/F/>", tag: "<redacted>" }"#
    );
}

/// The tag is written as lowercase hex, high nibble first, every byte two
/// digits — pinned on bytes that exercise every nibble value in both halves.
#[test]
fn format_line_writes_the_tag_as_two_lowercase_hex_digits_per_byte() {
    let mut tag = [0u8; TAG_BYTES];
    for (i, b) in tag.iter_mut().enumerate() {
        *b = u8::try_from(i * 0x11 % 256).unwrap() ^ 0x0f;
    }
    tag[TAG_BYTES - 1] = 0xff;
    let line = format_line("ro:/f/>", &tag);
    let want: String = tag.iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(line, format!("ro:/f/> {want}"));
    assert_eq!(parse_line(&line).unwrap().unwrap().tag, tag);
}

/// What a mint prints is what the reader reads — for a grant holding a space,
/// several spaces, or ENDING in one, since the tag is the whitespace-free tail.
#[test]
fn a_formatted_line_round_trips_even_when_the_grant_holds_a_space() {
    for grant in [
        "ro:/f/F/pub/>",
        "rw,p=n-a1b2c3d4e5f60718:/f/F/in/*/*/n-a1b2c3d4e5f60718/*",
        "ro:/f/F/pub a/>",
        "ro:/f/F/a  b/c d/>",
        "ro:/f/F/pub a/> ",
        "ro:/f/F/#tag/>",
    ] {
        for base in (0..=u8::MAX).step_by(TAG_BYTES) {
            let tag = tag_from(base);
            let line = format_line(grant, &tag);
            assert_eq!(
                line,
                format!("{grant} {}", hex_of(&tag)),
                "one space, lowercase"
            );
            assert_eq!(
                parse_line(&line),
                Ok(Some(Line {
                    grant: grant.to_string(),
                    tag
                })),
                "{line:?}"
            );
        }
    }
    // Uppercase hex is read too; only the writer is lowercase.
    let upper = format!("ro:/f/F/> {}", "AB".repeat(TAG_BYTES));
    assert_eq!(parse_line(&upper).unwrap().unwrap().tag, [0xab; TAG_BYTES]);
}

/// Blank and `#` lines are skipped, and ONLY those: a `#` inside a grant is a
/// grant, and a `#` after the tag is a malformed tag, not a trailing comment.
#[test]
fn blank_and_comment_lines_are_skipped_and_nothing_else_is() {
    let tag = hex_of(&tag_from(7));
    let commented_out = format!("#ro:/f/F/> {tag}");
    for skipped in [
        "",
        "   ",
        "\t \r",
        "#",
        "# the ring",
        "   # indented",
        commented_out.as_str(),
    ] {
        assert_eq!(parse_line(skipped), Ok(None), "{skipped:?}");
    }
    assert!(parse_line(&format!("ro:/f/#/> {tag}")).unwrap().is_some());
    assert_eq!(
        parse_line(&format!("ro:/f/F/> {tag} # note")),
        Err(Error::TagLength(4))
    );
    // Surrounding whitespace and a CR are trimmed, not read as grant or tag.
    let padded = parse_line(&format!("  ro:/f/F/>\t{tag}  \r"))
        .unwrap()
        .unwrap();
    assert_eq!(padded.grant, "ro:/f/F/>");
    assert_eq!(padded.tag, tag_from(7));
}

/// A grant with no tag, and a tag with no grant, are the same shape error — and
/// so is a line whose only separator is NON-ASCII whitespace: a mint writes one
/// ASCII space, and the separator is ASCII whitespace only.
#[test]
fn a_line_missing_either_half_is_a_shape_error() {
    let tag = hex_of(&tag_from(0));
    let indented = format!("  {tag}");
    let nbsp = format!("ro:/f/F/>\u{a0}{tag}");
    let ideographic = format!("ro:/f/F/>\u{3000}{tag}");
    for bad in [
        "ro:/f/F/>",
        "ro:/f/F/>   ",
        tag.as_str(),
        indented.as_str(),
        nbsp.as_str(),
        ideographic.as_str(),
    ] {
        assert_eq!(parse_line(bad), Err(Error::Shape), "{bad:?}");
    }
}

/// The tag is EXACTLY 32 bytes of strict hex. Every refusal is an error, never
/// a panic, and no error message echoes the tag it refused.
#[test]
fn the_tag_is_exactly_32_bytes_of_strict_hex() {
    let good = hex_of(&tag_from(0x40));
    for n in [2, 62, 63, 65, 66, 128] {
        let tag: String = good.chars().cycle().take(n).collect();
        let e = parse_line(&format!("ro:/f/F/> {tag}")).unwrap_err();
        assert_eq!(e, Error::TagLength(n), "{n} digits");
        assert!(
            !e.to_string().contains(&tag),
            "the refusal echoes the tag: {e}"
        );
    }
    let cases = [
        ("zz".repeat(TAG_BYTES), 0),
        (format!("0g{}", &good[2..]), 1),
        ("+f".repeat(TAG_BYTES), 0),
        ("-1".repeat(TAG_BYTES), 0),
        (format!("0x{}", &good[2..]), 1),
        // Multibyte: 64 BYTES of valid UTF-8, so the length check passes and
        // the decoder meets a byte of a character, not a char boundary.
        (format!("é{}", &good[2..]), 0),
        (format!("{}é{}", &good[..31], &good[33..]), 31),
        (format!("{}é{}", &good[..32], &good[34..]), 32),
        (format!("{}é", &good[..62]), 62),
    ];
    for (tag, at) in cases {
        assert_eq!(tag.len(), TAG_BYTES * 2, "{tag:?} is 64 bytes");
        let e = parse_line(&format!("ro:/f/F/> {tag}")).unwrap_err();
        assert_eq!(e, Error::TagNotHex(at), "{tag:?}");
        assert!(e.to_string().starts_with("tag: not valid hex"), "{e}");
    }
}

/// A ring reads in order, skipping blanks and comments; the first bad line
/// refuses the whole text and is named `path:line`, counting every line.
#[test]
fn parse_text_reads_a_ring_and_names_path_and_line() {
    let (a, b) = (tag_from(1), tag_from(2));
    let ring = format!(
        "# node ring\n\nro:/f/F/pub a/> {}\r\n  rw,p=n-a1:/f/F/in/n-a1/> {}\n",
        hex_of(&a),
        hex_of(&b)
    );
    assert_eq!(
        parse_text("node.cap", &ring),
        Ok(vec![
            Line {
                grant: "ro:/f/F/pub a/>".to_string(),
                tag: a
            },
            Line {
                grant: "rw,p=n-a1:/f/F/in/n-a1/>".to_string(),
                tag: b
            },
        ])
    );
    assert_eq!(parse_text("empty.cap", "\n# nothing\n"), Ok(vec![]));

    let bad = format!("{ring}# next\nro:/f/F/>\nro:/f/F/> zz\n");
    let e = parse_text("node.cap", &bad).unwrap_err();
    assert_eq!(
        e,
        Malformed {
            path: "node.cap".to_string(),
            line: 6,
            error: Error::Shape
        }
    );
    assert_eq!(e.to_string(), "node.cap:6: expected `<grant> <tag-hex>`");
}

/// The file reader: `path:line` for a malformed line, and a read error naming
/// the path — distinct from a malformed one — for a file it cannot read.
#[test]
fn read_file_names_path_and_line_and_keeps_a_read_error_distinct() {
    let dir = std::env::temp_dir().join(format!("astream-capfile-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let tag = tag_from(9);

    let good = dir.join("good.cap");
    std::fs::write(
        &good,
        format!("# ring\n{}\n", format_line("ro:/f/F/ a/>", &tag)),
    )
    .unwrap();
    assert_eq!(
        read_file(&good).unwrap(),
        vec![Line {
            grant: "ro:/f/F/ a/>".to_string(),
            tag
        }]
    );

    let bad = dir.join("bad.cap");
    std::fs::write(&bad, format!("\nro:/f/F/> {}\n", "zz".repeat(TAG_BYTES))).unwrap();
    let e = read_file(&bad).unwrap_err();
    assert!(
        matches!(&e, ReadError::Malformed(m) if m.line == 2 && m.error == Error::TagNotHex(0)),
        "{e:?}"
    );
    assert_eq!(
        e.to_string(),
        format!("{}:2: tag: not valid hex at char 0", bad.display())
    );

    let missing = dir.join("missing.cap");
    let e = read_file(&missing).unwrap_err();
    assert!(matches!(&e, ReadError::Io { .. }), "{e:?}");
    assert!(
        e.to_string()
            .starts_with(&format!("{}: ", missing.display())),
        "{e}"
    );

    let binary = dir.join("binary.cap");
    std::fs::write(&binary, [b'r', b'o', 0xff, b'\n']).unwrap();
    assert!(matches!(read_file(&binary), Err(ReadError::Io { .. })));

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// The secret-file rule: check_private, read_secret_file, SECRET_MIN
// ---------------------------------------------------------------------------

struct SecretScratch(std::path::PathBuf);

impl SecretScratch {
    fn path(&self) -> &std::path::Path {
        &self.0
    }
}

impl Drop for SecretScratch {
    fn drop(&mut self) {
        // Only a directory this guard exclusively created reaches cleanup.
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Allocate a private root without adopting or removing any preexisting entry.
fn secret_scratch(name: &str) -> SecretScratch {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let builder = std::fs::DirBuilder::new();
    #[cfg(unix)]
    let builder = {
        use std::os::unix::fs::DirBuilderExt;
        let mut private_builder = builder;
        private_builder.mode(0o700);
        private_builder
    };
    for _ in 0..1024 {
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let dir =
            std::env::temp_dir().join(format!("astream-secret-{name}-{}-{n}", std::process::id()));
        match builder.create(&dir) {
            Ok(()) => return SecretScratch(dir),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => panic!("create owned secret scratch: {e}"),
        }
    }
    panic!("could not allocate an exclusive secret scratch name");
}

#[cfg(unix)]
fn chmod(path: &std::path::Path, mode: u32) {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).unwrap();
}

/// A cap file read through [`read_file`] is outside the secret-file rule: it reads a ring at
/// 0644, where [`read_private_file`] and [`read_private_ring`] refuse the same file. What a
/// face that reads by [`read_file`] may rely on for a cap file is whatever keeps the file
/// private, never this module.
#[cfg(unix)]
#[test]
fn secret_file_rule_is_not_what_read_file_reads_a_cap_file_by() {
    let scratch = secret_scratch("cap");
    let path = scratch.path().join("ring.cap");
    std::fs::write(&path, format_line("ro:/f/F/pub/>", &tag_from(1)) + "\n").unwrap();
    chmod(&path, 0o644);
    assert_eq!(
        read_file(&path)
            .expect("read_file holds no owner rule")
            .len(),
        1
    );
    assert_eq!(
        read_private_file(&path).expect_err("the owner rule").kind(),
        std::io::ErrorKind::PermissionDenied
    );
    assert_eq!(
        read_private_ring(&path).expect_err("the owner rule").kind(),
        std::io::ErrorKind::PermissionDenied
    );
}

/// [`read_private_ring`] reads what [`read_file`] reads wherever the ring's file is its owner's
/// alone, in any directory, by any number of names, and refuses each wider mode at once, naming
/// the file and the `chmod` that closes it.
#[cfg(unix)]
#[test]
fn secret_file_read_private_ring_holds_the_file_and_only_the_file() {
    let scratch = secret_scratch("ring");
    let dir = scratch.path();
    chmod(dir, 0o755);
    let path = dir.join("ring.cap");
    let text = format_line("ro:/f/F/pub/>", &tag_from(1)) + "\n# a comment\n";
    std::fs::write(&path, &text).unwrap();
    for mode in [0o600, 0o400] {
        chmod(&path, mode);
        assert_eq!(
            read_private_ring(&path).expect("its owner's alone, in a 0755 directory"),
            read_file(&path).expect("the plain read")
        );
    }
    chmod(&path, 0o600);
    let second = dir.join("second.cap");
    std::fs::hard_link(&path, &second).unwrap();
    assert_eq!(read_private_ring(&path).expect("a second name").len(), 1);
    std::fs::remove_file(&second).unwrap();

    for mode in [0o640, 0o604, 0o644, 0o660] {
        chmod(&path, mode);
        let e = read_private_ring(&path).expect_err("a wider mode");
        assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied, "{mode:o}");
        let said = e.to_string();
        assert!(
            said.starts_with(&format!("{} is mode {mode:04o}: ", path.display())),
            "{said}"
        );
        assert!(
            said.contains(&format!("chmod 600 {}", path.display())),
            "{said}"
        );
    }
    chmod(&path, 0o600);

    for (name, bytes) in [("empty", ""), ("comment", "# none yet\n")] {
        let ring = dir.join(name);
        std::fs::write(&ring, bytes).unwrap();
        chmod(&ring, 0o600);
        assert_eq!(read_private_ring(&ring).expect("no length floor"), vec![]);
    }

    let broken = dir.join("broken");
    std::fs::write(&broken, "# one\nro:/f/F/> nothex\n").unwrap();
    chmod(&broken, 0o600);
    let e = read_private_ring(&broken).expect_err("a malformed line");
    assert_eq!(e.kind(), std::io::ErrorKind::InvalidData);
    assert!(
        e.to_string()
            .starts_with(&format!("{}:2: ", broken.display())),
        "{e}"
    );

    let binary = dir.join("binary");
    std::fs::write(&binary, [0xff, 0xfe]).unwrap();
    chmod(&binary, 0o600);
    let e = read_private_ring(&binary).expect_err("not UTF-8");
    assert_eq!(e.kind(), std::io::ErrorKind::InvalidData);
    assert!(
        e.to_string()
            .starts_with(&format!("{}:1: ", binary.display())),
        "{e}"
    );
    std::fs::write(&binary, b"# one\n\n# three\n\xff\xfe\n").unwrap();
    let e = read_private_ring(&binary).expect_err("not UTF-8 on a later line");
    assert_eq!(e.kind(), std::io::ErrorKind::InvalidData);
    assert!(
        e.to_string()
            .starts_with(&format!("{}:4: ", binary.display())),
        "{e}"
    );

    let absent = dir.join("absent");
    let e = read_private_ring(&absent).expect_err("no file");
    assert_eq!(e.kind(), std::io::ErrorKind::NotFound);
    assert!(
        e.to_string()
            .starts_with(&format!("{}: ", absent.display())),
        "{e}"
    );

    let e = read_private_ring(dir).expect_err("a directory");
    assert_eq!(e.kind(), std::io::ErrorKind::InvalidInput);
    assert_eq!(
        e.to_string(),
        format!(
            "{} is a directory: a secret file is a regular file",
            dir.display()
        )
    );
}

/// A link at the path is refused without opening what it names, naming the file and what to do,
/// where the plain read follows it.
#[cfg(unix)]
#[test]
fn secret_file_read_private_ring_follows_no_link() {
    let scratch = secret_scratch("ring-link");
    let real = scratch.path().join("real.cap");
    std::fs::write(&real, format_line("ro:/f/F/pub/>", &tag_from(1)) + "\n").unwrap();
    chmod(&real, 0o600);
    let link = scratch.path().join("link.cap");
    std::os::unix::fs::symlink(&real, &link).unwrap();
    assert_eq!(
        read_file(&link).expect("the plain read follows it").len(),
        1
    );
    let e = read_private_ring(&link).expect_err("a link at the path");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    assert_eq!(
        e.to_string(),
        format!(
            "{} is a symlink: a private ring is read through no link, so name the file it \
             points at",
            link.display()
        )
    );
}

/// A FIFO at the path is refused at once, behind the one-minute hang detector: [`read_file`]
/// would wait for a writer that never comes.
#[cfg(unix)]
#[test]
fn secret_file_read_private_ring_refuses_a_fifo_without_waiting_for_a_writer() {
    let scratch = secret_scratch("ring-fifo");
    let fifo = scratch.path().join("ring.cap");
    let made = std::process::Command::new("mkfifo")
        .arg("-m")
        .arg("600")
        .arg(&fifo)
        .status()
        .expect("run mkfifo");
    assert!(made.success(), "mkfifo");
    let shown = fifo.display().to_string();
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(read_private_ring(&fifo));
    });
    let e = rx
        .recv_timeout(std::time::Duration::from_secs(60))
        .expect("read_private_ring waited on a FIFO")
        .expect_err("a FIFO is no ring");
    assert_eq!(e.kind(), std::io::ErrorKind::InvalidInput);
    assert_eq!(
        e.to_string(),
        format!("{shown} is a FIFO: a secret file is a regular file")
    );
}

/// [`refusal_of`] names the clause a refusal holds, for a caller that acts on it, and only for what
/// the rule refused: an open the OS refused has the same kind and is the OS's words, so a caller
/// can tell a file the rule will not take from one it cannot open. The words are the same either
/// way, the path first.
#[cfg(unix)]
#[test]
fn secret_file_refusal_of_names_the_clause_and_nothing_the_rule_did_not_say() {
    let scratch = secret_scratch("ring-clause");
    let dir = scratch.path();
    let path = dir.join("ring.cap");
    std::fs::write(&path, format_line("ro:/f/F/pub/>", &tag_from(1)) + "\n").unwrap();

    chmod(&path, 0o644);
    let e = read_private_ring(&path).expect_err("a wider mode");
    assert_eq!(
        refusal_of(&e),
        Some(Refusal::File(astream_sys::NotPrivate::Mode(0o644)))
    );
    assert!(
        e.to_string()
            .starts_with(&format!("{} is mode 0644: ", path.display())),
        "{e}"
    );

    chmod(&path, 0o600);
    assert!(read_private_ring(&path).is_ok(), "the control");

    let link = dir.join("link.cap");
    std::os::unix::fs::symlink(&path, &link).unwrap();
    let e = read_private_ring(&link).expect_err("a link");
    assert_eq!(refusal_of(&e), Some(Refusal::Link));

    let e = read_private_ring(dir).expect_err("a directory");
    assert_eq!(
        refusal_of(&e),
        Some(Refusal::File(astream_sys::NotPrivate::Kind("a directory")))
    );

    let e = read_private_ring(dir.join("absent")).expect_err("no file");
    assert_eq!(e.kind(), std::io::ErrorKind::NotFound);
    assert_eq!(refusal_of(&e), None);

    let broken = dir.join("broken");
    std::fs::write(&broken, "ro:/f/F/> nothex\n").unwrap();
    chmod(&broken, 0o600);
    let e = read_private_ring(&broken).expect_err("a malformed line");
    assert_eq!(refusal_of(&e), None);

    // Root opens a file of mode 000 regardless, so only another user sees the OS refuse it.
    if astream_sys::euid() != 0 {
        chmod(&path, 0o000);
        let e = read_private_ring(&path).expect_err("the OS refuses the open");
        assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
        assert_eq!(refusal_of(&e), None, "{e}");
        assert!(
            e.to_string().starts_with(&format!("{}: ", path.display())),
            "{e}"
        );
        chmod(&path, 0o600);
    }
}

/// On macOS a 0600 ring carrying an `everyone allow read` entry is open to every user, and is
/// refused naming `chmod -N`; once cleared it reads.
#[cfg(target_os = "macos")]
#[test]
fn secret_file_read_private_ring_refuses_an_access_list_that_lets_others_in() {
    let scratch = secret_scratch("ring-acl");
    let path = scratch.path().join("ring.cap");
    std::fs::write(&path, format_line("ro:/f/F/pub/>", &tag_from(1)) + "\n").unwrap();
    chmod(&path, 0o600);
    chmod_acl(&["+a", "everyone allow read"], &path);
    let e = read_private_ring(&path).expect_err("an allow entry");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    assert_eq!(
        refusal_of(&e),
        Some(Refusal::File(astream_sys::NotPrivate::Acl))
    );
    assert!(
        e.to_string()
            .contains(&format!("chmod -N {}", path.display())),
        "{e}"
    );
    chmod_acl(&["-N"], &path);
    assert_eq!(read_private_ring(&path).expect("cleared").len(), 1);
}

/// 0600 or tighter passes; any group/other bit is refused, as `PermissionDenied`
/// naming the mode and the `chmod`, path first, by EACH of the three functions: the
/// check and both readers hold the same clause on the same open, so none of them
/// may answer a mode refusal in its own words. The passing modes are the control:
/// the same file, the same bytes, only the mode moved, and both readers then return
/// those bytes.
#[cfg(unix)]
#[test]
fn secret_file_other_users_can_read_is_refused_naming_the_chmod() {
    let scratch = secret_scratch("priv");
    let dir = scratch.path();
    let path = dir.join("k");
    let shown = path.display().to_string();
    let bytes = [0x5a; SECRET_MIN];
    std::fs::write(&path, bytes).unwrap();
    for (mode, ok) in [
        (0o600, true),
        (0o400, true),
        (0o700, true),
        (0o640, false),
        (0o604, false),
        (0o644, false),
        (0o660, false),
    ] {
        chmod(&path, mode);
        let checked = check_private(&path);
        let private = read_private_file(&path);
        let secret = read_secret_file(&path);
        if ok {
            assert!(checked.is_ok(), "{mode:o}: {checked:?}");
            assert_eq!(private.expect("owner-only"), bytes, "{mode:o}");
            assert_eq!(secret.expect("owner-only"), bytes, "{mode:o}");
            continue;
        }
        for (door, e) in [
            ("check_private", checked.expect_err("group/other bit")),
            ("read_private_file", private.expect_err("group/other bit")),
            ("read_secret_file", secret.expect_err("group/other bit")),
        ] {
            assert_eq!(
                e.kind(),
                std::io::ErrorKind::PermissionDenied,
                "{door} {mode:o}"
            );
            let text = e.to_string();
            assert!(
                text.starts_with(&format!("{shown} is mode {mode:04o}: ")),
                "{door}: {text}"
            );
            assert!(
                text.contains(&format!("chmod 600 {shown}")),
                "{door}: {text}"
            );
        }
    }
}

/// `read_private_file` is the owner-only rule WITHOUT the length floor: the bytes
/// of a file shorter than a secret come back exactly, where `read_secret_file`
/// refuses the same file. That is the reader for a file whose caller decodes it (a
/// hex key), and the control that the floor is `read_secret_file`'s alone.
#[cfg(unix)]
#[test]
fn secret_file_private_reader_has_no_length_floor() {
    let scratch = secret_scratch("plain");
    let dir = scratch.path();
    let path = dir.join("k.hex");
    let hex = format!("{}\n", "ab".repeat(8));
    std::fs::write(&path, &hex).unwrap();
    chmod(&path, 0o600);
    assert_eq!(
        read_private_file(&path).expect("owner-only"),
        hex.as_bytes()
    );
    assert_eq!(
        read_secret_file(&path).expect_err("17 bytes").kind(),
        std::io::ErrorKind::InvalidData
    );
    std::fs::write(&path, b"").unwrap();
    assert_eq!(read_private_file(&path).expect("empty"), b"");
}

/// A secret is owner-only and at least 32 bytes, or refused with the reason by kind,
/// and is read byte for byte: a trailing newline is part of it, and so are 32 bytes
/// of which the last is a space (what `head -c 32 /dev/urandom` writes about one
/// time in twenty-five). Controls: 31 bytes is refused where 32 is not, and the
/// newline-terminated secret is NOT its trimmed text.
#[cfg(unix)]
#[test]
fn secret_file_is_owner_only_long_enough_and_read_byte_for_byte() {
    let scratch = secret_scratch("mint");
    let dir = scratch.path();
    let path = dir.join("mint.secret");
    assert_eq!(
        read_secret_file(&path).expect_err("absent").kind(),
        std::io::ErrorKind::NotFound
    );
    assert_eq!(
        check_private(&path).expect_err("absent").kind(),
        std::io::ErrorKind::NotFound
    );

    let mut bytes = vec![0x5a; 31];
    bytes.push(b'\n');
    std::fs::write(&path, &bytes).unwrap();
    chmod(&path, 0o644);
    let e = read_secret_file(&path).expect_err("0644");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    chmod(&path, 0o600);
    let got = read_secret_file(&path).expect("0600, 32 bytes");
    assert_eq!(got, bytes);
    assert_ne!(got, bytes.trim_ascii());

    let mut spaced = vec![b'k'; 31];
    spaced.push(b' ');
    std::fs::write(&path, &spaced).unwrap();
    assert_eq!(
        read_secret_file(&path).expect("32, the last a space"),
        spaced
    );

    std::fs::write(&path, [0x5a; SECRET_MIN - 1]).unwrap();
    let e = read_secret_file(&path).expect_err("short");
    assert_eq!(e.kind(), std::io::ErrorKind::InvalidData);
    let shown = path.display().to_string();
    assert_eq!(
        e.to_string(),
        format!(
            "{shown} holds 31 bytes; a secret file holds at least 32 (a short key mints \
             capabilities that seal nothing)"
        )
    );
    std::fs::write(&path, b"").unwrap();
    assert_eq!(
        read_secret_file(&path).expect_err("empty").kind(),
        std::io::ErrorKind::InvalidData
    );
}

/// Every refusal names the path FIRST and an OS error names it ONCE: the OS never
/// names the path it failed on, so the reader re-wraps the error as `<path>: …`
/// with its kind kept, and a caller that prefixes only its flag (`--secret-file
/// {e}`) prints the path exactly once. Negative control: the raw OS error for the
/// same missing file does NOT name the path, so the wrap is what does.
#[test]
fn secret_file_refusals_name_the_path_first_and_keep_the_kind() {
    let scratch = secret_scratch("path");
    let dir = scratch.path();
    let missing = dir.join("absent.secret");
    let shown = missing.display().to_string();
    for e in [
        check_private(&missing).expect_err("absent"),
        read_private_file(&missing).expect_err("absent"),
        read_secret_file(&missing).expect_err("absent"),
    ] {
        assert_eq!(e.kind(), std::io::ErrorKind::NotFound);
        let text = e.to_string();
        assert!(text.starts_with(&format!("{shown}: ")), "{text}");
        assert_eq!(text.matches(&shown).count(), 1, "{text}");
    }
    let raw = std::fs::File::open(&missing).expect_err("absent");
    assert!(!raw.to_string().contains(&shown), "{raw}");

    // Reject path syntax before opening the directory. Normal names are exercised
    // by the private-directory aggregate below; these must not escape or normalize
    // into a different component on the host platform.
    for name in ["", ".", "..", "sub/k", "./k", "sub/../k", "k/", "/k"] {
        assert_eq!(
            read_secret_in(dir, name).expect_err("one component").kind(),
            std::io::ErrorKind::InvalidInput,
            "{name:?}"
        );
    }
    #[cfg(windows)]
    for name in [
        r"sub\k",
        r"..\k",
        r"\k",
        r"C:\k",
        r"C:k",
        r"\\server\share\k",
        r"\\?\C:\k",
    ] {
        assert_eq!(
            read_secret_in(dir, name).expect_err("one component").kind(),
            std::io::ErrorKind::InvalidInput,
            "{name:?}"
        );
    }

    // An owner-only directory is no secret file: it is refused at the open, before a
    // byte is read, as InvalidInput naming what it is, path first and once, by each of
    // the three functions. (Before the regular-file clause it opened, passed the mode
    // and failed at the read with EISDIR.)
    #[cfg(unix)]
    {
        let sub = dir.join("sub");
        std::fs::create_dir_all(&sub).unwrap();
        chmod(&sub, 0o700);
        let sub_shown = sub.display().to_string();
        for e in [
            check_private(&sub).expect_err("a directory is not a secret"),
            read_private_file(&sub).expect_err("a directory is not a secret"),
            read_secret_file(&sub).expect_err("a directory is not a secret"),
        ] {
            assert_eq!(e.kind(), std::io::ErrorKind::InvalidInput, "{e}");
            let text = e.to_string();
            assert_eq!(
                text,
                format!("{sub_shown} is a directory: a secret file is a regular file")
            );
        }
    }
}

/// A read error discards authority, including the prefix read before the failure;
/// a successful read keeps those exact bytes, including its trailing newline.
#[test]
fn a_failed_secret_read_wipes_the_bytes_it_already_collected() {
    struct PartialError<'a>(&'a [u8]);
    impl std::io::Read for PartialError<'_> {
        fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
            if self.0.is_empty() {
                return Err(std::io::Error::other("captured read failure"));
            }
            let n = out.len().min(self.0.len());
            out[..n].copy_from_slice(&self.0[..n]);
            self.0 = &self.0[n..];
            Ok(n)
        }
    }
    let prefix = [0xa5; SECRET_MIN];
    let mut secret = Vec::new();
    let error = read_secret_into(&mut PartialError(&prefix), &mut secret).unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::Other);
    assert_eq!(error.to_string(), "captured read failure");
    assert_eq!(secret, vec![0; prefix.len()]);

    let mut exact = [0x5a; SECRET_MIN];
    exact[SECRET_MIN - 1] = b'\n';
    let mut secret = Vec::new();
    read_secret_into(&mut std::io::Cursor::new(exact), &mut secret).unwrap();
    assert_eq!(secret, exact);
}

/// `chmod <args> <path>` (macOS's, which takes `+a` and `-N`), which must succeed.
#[cfg(target_vendor = "apple")]
fn chmod_acl(args: &[&str], path: &std::path::Path) {
    let ran = std::process::Command::new("/bin/chmod")
        .args(args)
        .arg(path)
        .status()
        .expect("run chmod");
    assert!(ran.success(), "chmod {args:?} {}", path.display());
}

/// On macOS a 0600 secret carrying an `everyone allow read` entry is open to every
/// user though its mode says otherwise: each reader refuses it as PermissionDenied,
/// path first, naming `chmod -N <path>`, and so does `read_secret_in` for a 0700
/// directory carrying an `everyone allow list` entry, naming `chmod -N <dir>`.
/// Controls: after `chmod -N` the same file and directory pass and the bytes come
/// back; a DENY entry takes nothing away and passes.
#[cfg(target_vendor = "apple")]
#[test]
fn secret_file_an_access_list_that_allows_others_is_refused() {
    let scratch = secret_scratch("acl");
    let dir = scratch.path();
    let path = dir.join("mint.secret");
    let shown = path.display().to_string();
    let bytes = [0x5a; SECRET_MIN];
    std::fs::write(&path, bytes).unwrap();
    chmod(&path, 0o600);
    chmod_acl(&["+a", "everyone allow read"], &path);
    for (door, e) in [
        ("check_private", check_private(&path).expect_err("ACL")),
        (
            "read_private_file",
            read_private_file(&path).expect_err("ACL"),
        ),
        (
            "read_secret_file",
            read_secret_file(&path).expect_err("ACL"),
        ),
        (
            "read_secret_in",
            read_secret_in(dir, "mint.secret").expect_err("ACL"),
        ),
    ] {
        assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied, "{door}");
        let text = e.to_string();
        assert!(
            text.starts_with(&format!(
                "{shown} carries an access list (ACL) that lets other users in"
            )),
            "{door}: {text}"
        );
        assert!(
            text.contains(&format!("`chmod -N {shown}`")),
            "{door}: {text}"
        );
    }
    chmod_acl(&["-N"], &path);
    assert_eq!(read_secret_file(&path).expect("no ACL"), bytes);
    assert_eq!(read_secret_in(dir, "mint.secret").expect("no ACL"), bytes);
    chmod_acl(&["+a", "everyone deny write"], &path);
    assert_eq!(read_secret_file(&path).expect("a deny entry"), bytes);

    chmod_acl(&["+a", "everyone allow list"], dir);
    let e = read_secret_in(dir, "mint.secret").expect_err("the directory's ACL");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    let text = e.to_string();
    let dir_shown = dir.display().to_string();
    assert!(
        text.starts_with(&format!("{shown}: its directory {dir_shown} carries")),
        "{text}"
    );
    assert!(text.contains(&format!("`chmod -N {dir_shown}`")), "{text}");
    chmod_acl(&["-N"], dir);
    assert_eq!(read_secret_in(dir, "mint.secret").expect("no ACL"), bytes);
}

/// A FIFO at a secret's path is refused AT ONCE, as InvalidInput naming it, by the
/// path reader and by `read_secret_in`: the open is non-blocking, so nothing waits for
/// a writer that never comes. Each read runs on its own thread behind the one-minute
/// hang detector, so a blocking open fails the test rather than hanging it.
#[cfg(unix)]
#[test]
fn secret_file_a_fifo_is_refused_without_waiting_for_a_writer() {
    let scratch = secret_scratch("fifo");
    let dir = scratch.path().to_path_buf();
    let fifo = dir.join("mint.secret");
    let made = std::process::Command::new("mkfifo")
        .arg("-m")
        .arg("600")
        .arg(&fifo)
        .status()
        .expect("run mkfifo");
    assert!(made.success(), "mkfifo");
    let shown = fifo.display().to_string();
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(read_secret_file(&fifo));
        let _ = tx.send(read_secret_in(&dir, "mint.secret"));
    });
    for door in ["read_secret_file", "read_secret_in"] {
        let e = rx
            .recv_timeout(std::time::Duration::from_secs(60))
            .unwrap_or_else(|_| panic!("{door} waited on a FIFO"))
            .expect_err("a FIFO is no secret file");
        assert_eq!(e.kind(), std::io::ErrorKind::InvalidInput, "{door}");
        assert_eq!(
            e.to_string(),
            format!("{shown} is a FIFO: a secret file is a regular file"),
            "{door}"
        );
    }
}

/// `read_secret_in` holds the directory and the file's links to aterm's rule; the
/// path reader keeps following a link the operator names. Over real files: a 32-byte
/// secret in a 0700 directory reads exactly (the control of every refusal below);
/// a symlink to it and a second hard link to it are refused by `read_secret_in` as
/// PermissionDenied, path first, while `read_secret_file` follows the symlink and
/// reads the hard link (the path API is unchanged); a directory open to others is
/// refused naming `chmod 700 <dir>`, a symlinked directory is refused, a name of more
/// than one component is InvalidInput, a missing directory or file is NotFound (a
/// missing file even in a loose directory), and
/// `/` (root's, holding `/usr`) is refused for its owner unless the reader is root (then
/// for its mode).
#[cfg(unix)]
#[test]
fn secret_file_in_a_private_directory_is_read_through_no_link() {
    let scratch = secret_scratch("in");
    let dir = scratch.path();
    let bytes = [0x5a; SECRET_MIN];
    let real = dir.join("mint.secret");
    std::fs::write(&real, bytes).unwrap();
    chmod(&real, 0o600);
    assert_eq!(read_secret_in(dir, "mint.secret").expect("private"), bytes);

    let link = dir.join("linked.secret");
    std::os::unix::fs::symlink(&real, &link).unwrap();
    let e = read_secret_in(dir, "linked.secret").expect_err("a symlink");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    assert!(
        e.to_string()
            .starts_with(&format!("{} is a symlink: ", link.display())),
        "{e}"
    );
    assert_eq!(
        read_secret_file(&link).expect("the path API follows"),
        bytes
    );

    let second = dir.join("second.secret");
    std::fs::hard_link(&real, &second).unwrap();
    for name in ["mint.secret", "second.secret"] {
        let e = read_secret_in(dir, name).expect_err("two links");
        assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied, "{name}");
        assert!(
            e.to_string()
                .starts_with(&format!("{} has 2 links: ", dir.join(name).display())),
            "{e}"
        );
    }
    assert_eq!(read_secret_file(&second).expect("the path API"), bytes);
    std::fs::remove_file(&second).unwrap();
    assert_eq!(
        read_secret_in(dir, "mint.secret").expect("one link again"),
        bytes
    );

    chmod(dir, 0o755);
    let e = read_secret_in(dir, "mint.secret").expect_err("a loose directory");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    let text = e.to_string();
    assert!(
        text.starts_with(&format!(
            "{}: its directory {} is mode 0755: ",
            real.display(),
            dir.display()
        )),
        "{text}"
    );
    assert!(
        text.contains(&format!("`chmod 700 {}`", dir.display())),
        "{text}"
    );
    // The 0600 secret in it was readable by nobody else: the refusal closes the
    // directory without telling its owner to treat the secret as exposed.
    assert!(!text.contains("exposed"), "{text}");
    // No secret is NotFound whatever its directory is: the directory is judged when
    // there is a secret in it to keep.
    assert_eq!(
        read_secret_in(dir, "absent.secret")
            .expect_err("absent in a loose directory")
            .kind(),
        std::io::ErrorKind::NotFound
    );
    chmod(dir, 0o700);

    let dir_link = scratch.path().with_extension("link");
    std::os::unix::fs::symlink(dir, &dir_link).unwrap();
    let e = read_secret_in(&dir_link, "mint.secret").expect_err("a symlinked directory");
    let _ = std::fs::remove_file(&dir_link);
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    assert!(e.to_string().contains("is a symlink"), "{e}");

    for name in ["sub/mint.secret", "..", ".", ""] {
        assert_eq!(
            read_secret_in(dir, name).expect_err("one component").kind(),
            std::io::ErrorKind::InvalidInput,
            "{name:?}"
        );
    }
    assert_eq!(
        read_secret_in(dir, "absent.secret")
            .expect_err("absent")
            .kind(),
        std::io::ErrorKind::NotFound
    );
    assert_eq!(
        read_secret_in(dir.join("absent"), "mint.secret")
            .expect_err("no directory")
            .kind(),
        std::io::ErrorKind::NotFound
    );

    // `/usr` is there on every Unix, so `/` is judged as the directory it is in.
    let e = read_secret_in("/", "usr").expect_err("root's directory");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    if astream_sys::euid() == 0 {
        assert!(e.to_string().contains("is mode 0755"), "{e}");
    } else {
        assert!(e.to_string().contains("is owned by uid 0"), "{e}");
    }
}

/// `read_secret_at` is `read_secret_in` over one path's directory and file name, every
/// refusal naming the path EXACTLY as given. Over real files: the same 32-byte secret
/// in a 0700 directory reads (the control); a symlink to it is refused; the same
/// directory at 0755 is refused naming `chmod 700 <dir>`; a bare name is read in the
/// current directory and named as given, never as `./<name>` (a missing one is
/// NotFound starting `<name>: `); and a path that names no file is InvalidInput.
#[cfg(unix)]
#[test]
fn secret_file_at_a_path_is_its_directory_and_name() {
    let scratch = secret_scratch("at");
    let dir = scratch.path();
    let bytes = [0x5a; SECRET_MIN];
    let real = dir.join("mint.secret");
    std::fs::write(&real, bytes).unwrap();
    chmod(&real, 0o600);
    assert_eq!(read_secret_at(&real).expect("private"), bytes);

    let link = dir.join("linked.secret");
    std::os::unix::fs::symlink(&real, &link).unwrap();
    let e = read_secret_at(&link).expect_err("a symlink");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    assert!(
        e.to_string()
            .starts_with(&format!("{} is a symlink: ", link.display())),
        "{e}"
    );

    chmod(dir, 0o755);
    let e = read_secret_at(&real).expect_err("a loose directory");
    chmod(dir, 0o700);
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    let text = e.to_string();
    assert!(
        text.starts_with(&format!(
            "{}: its directory {} is mode 0755: ",
            real.display(),
            dir.display()
        )),
        "{text}"
    );
    assert!(
        text.contains(&format!("`chmod 700 {}`", dir.display())),
        "{text}"
    );

    // The test's current directory holds no such file.
    let bare = format!("astream-absent-{}.secret", std::process::id());
    let e = read_secret_at(&bare).expect_err("absent");
    assert_eq!(e.kind(), std::io::ErrorKind::NotFound);
    assert!(e.to_string().starts_with(&format!("{bare}: ")), "{e}");

    for nothing in ["/", "", "x/.."] {
        assert_eq!(
            read_secret_at(nothing).expect_err("no file").kind(),
            std::io::ErrorKind::InvalidInput,
            "{nothing:?}"
        );
    }
}

/// `read_secret_at_narrowed` reads a secret as `read_secret_at` will once its
/// directory is 0700, and waives nothing else. Over real files: a 0600 secret in a
/// 0755 directory reads, though `read_secret_at` refuses the same read (the control);
/// a 0644 secret there is still refused for its own mode, naming `chmod 600`; a second
/// link is still refused; a symlinked directory is still refused; a missing secret is
/// NotFound; and on macOS an access-list allow entry on the 0755 directory is still
/// refused, naming `chmod -N <dir>`: only a directory refused for its mode bits alone
/// passes.
#[cfg(unix)]
#[test]
fn secret_file_narrowed_waives_only_the_directorys_mode() {
    let scratch = secret_scratch("narrowed");
    let dir = scratch.path();
    let bytes = [0x5a; SECRET_MIN];
    let real = dir.join("mint.secret");
    std::fs::write(&real, bytes).unwrap();
    chmod(&real, 0o600);
    chmod(dir, 0o755);
    assert_eq!(
        read_secret_at(&real)
            .expect_err("a loose directory, as it stands")
            .kind(),
        std::io::ErrorKind::PermissionDenied
    );
    assert_eq!(
        read_secret_at_narrowed(&real).expect("once narrowed"),
        bytes
    );

    chmod(&real, 0o644);
    let e = read_secret_at_narrowed(&real).expect_err("the file's own mode");
    assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
    assert!(
        e.to_string()
            .starts_with(&format!("{} is mode 0644: ", real.display())),
        "{e}"
    );
    assert!(e.to_string().contains("chmod 600"), "{e}");
    chmod(&real, 0o600);

    let second = dir.join("second.secret");
    std::fs::hard_link(&real, &second).unwrap();
    let e = read_secret_at_narrowed(&real).expect_err("two links");
    assert!(e.to_string().contains("has 2 links"), "{e}");
    std::fs::remove_file(&second).unwrap();

    let dir_link = scratch.path().with_extension("link");
    std::os::unix::fs::symlink(dir, &dir_link).unwrap();
    let e = read_secret_at_narrowed(dir_link.join("mint.secret")).expect_err("a symlinked dir");
    let _ = std::fs::remove_file(&dir_link);
    assert!(e.to_string().contains("is a symlink"), "{e}");

    assert_eq!(
        read_secret_at_narrowed(dir.join("absent.secret"))
            .expect_err("absent")
            .kind(),
        std::io::ErrorKind::NotFound
    );

    #[cfg(target_vendor = "apple")]
    {
        chmod_acl(&["+a", "everyone allow list"], dir);
        let e = read_secret_at_narrowed(&real).expect_err("the directory's ACL");
        chmod_acl(&["-N"], dir);
        assert_eq!(e.kind(), std::io::ErrorKind::PermissionDenied);
        assert!(
            e.to_string()
                .contains(&format!("`chmod -N {}`", dir.display())),
            "{e}"
        );
    }
    chmod(dir, 0o700);
    assert_eq!(read_secret_at(&real).expect("narrowed by hand"), bytes);
}
