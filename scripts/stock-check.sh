#!/usr/bin/env bash
# scripts/stock-check.sh — STOCK EXCEPTION: every astream crate still compiles under a stock
# rustc, the compiler aterm builds astream with in its cross cells (Linux, Windows, the
# x86_64-apple-darwin slice) and in its Linux lane. Nothing here builds what ships; it only
# compiles (`cargo check`).
#
# Why a compile and not only the gate's stock-lexable lint: the lint keeps Trust-only syntax
# where a stock compiler never reads it, but code that only cfg(clean_islands) keeps alive
# still fails a stock build, and every Trust step of `make ci` stays green over it. On
# 2026-10-17 a copy of capfile_line_advance in astream-cap's twins.rs was called from no
# stock-compiled code, so astream-cap's #![deny(dead_code)] refused it under every compiler
# without cfg(clean_islands), and aterm's linux cells stopped there (fixed in b8a8cff).
#
# Warnings are refused too, because aterm judges them: its linux, linux-arm and x86_64 macOS
# cells count every rustc warning as a finding (aterm-verify's cells.rs, is_cell_warning),
# and `ship release` refuses on one. The same dead twin in any crate but astream-cap, which
# alone denies dead_code, is only a warning, so a check that compiled it would pass. The
# stock build carries RUSTFLAGS="$DENY", the lints aterm's cells excuse allowed again: the
# two that only say the stock rustc does not know a lint name the Trust rustc does. cargo
# caps every registry dependency's lints, so only astream's own code is judged.
#
# Per target, in both feature configurations (as `make test`, for the same reason):
#   rustup run $STOCK_TOOLCHAIN cargo check --locked --keep-going --workspace --all-targets \
#     [--target <triple> --config <ring's build-script override>] [--all-features]
# for the host and x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu, x86_64-apple-darwin
# and x86_64-pc-windows-msvc. The host row names no --target, so RUSTFLAGS reaches the build
# scripts as well, which a --target build compiles without it (they compile for the host
# alone, so one row judges them). On Windows two targets are Unix-only and left out: the asb
# binary (Broker::serve is a Unix-socket server) and astream-broker's unit tests (their
# fixture serves one). The broker's library, which aterm's Windows cells compile, its
# integration tests and its examples are checked there.
#
# EXIT CODE = VERDICT (as scripts/verify-ready.sh):
#   0  every target and feature set compiled under the stock toolchain, with no warning
#   1  REFUSED: the stock compiler refused or warned on at least one, an astream build script
#      failed, or Cargo.lock needs a change --locked forbids (the table says which row, the
#      log says why)
#   2  COULD NOT RUN: no rustup, no stock toolchain, a toolchain that is really Trust, a
#      target's standard library not installed, or cargo stopping for any other reason
#      before it compiled (a registry it cannot reach, a missing linker). Not a verdict,
#      and never a pass.
#
# STOCK_TOOLCHAIN names the rustup toolchain (default `stable`); rustup never installs it
# here. Builds and logs go to target/stock (override with STOCK_OUT_DIR), apart from the
# Trust builds' fingerprints.
set -u
cd "$(dirname "$0")/.." || exit 2

say() { printf '%s\n' "$*"; }
could_not_run() {
  say "COULD NOT RUN (exit 2): $*"
  say "  no stock compiler checked astream, so this is not a pass"
  exit 2
}

# The stock compile must see no ambient compiler or flags: a RUSTC left by an outer Trust
# build would compile the islands and make this check vacuous. After clearing them,
# bind RUSTC to the stock compiler rustup resolves below, never to a PATH proxy.
unset RUSTC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER RUSTFLAGS CARGO_ENCODED_RUSTFLAGS \
  CARGO_BUILD_RUSTFLAGS CARGO_BUILD_TARGET
export RUSTUP_AUTO_INSTALL=0
DENY="-D warnings -A unknown_lints -A renamed_and_removed_lints"
export RUSTFLAGS="$DENY"

TC="${STOCK_TOOLCHAIN:-stable}"
CROSS=(x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu x86_64-apple-darwin x86_64-pc-windows-msvc)
# ring's build script compiles C and assembly for the target, which needs a C toolchain
# for that triple: on a Mac the Apple one could serve x86_64-apple-darwin, but no Linux or
# Windows target has one (measured 2026-10-17: the script fails for x86_64 and aarch64
# Linux and x86_64 Windows). On every cross row, x86_64-apple-darwin included, it is
# replaced by cargo's own override,
# keyed by ring's `links` name, so the rows do not depend on the machine: ring 0.17.14's script
# emits only rustc-link-search, rustc-link-lib and rerun-if directives, and nothing in
# its src/ reads OUT_DIR, so a check that never links sees the same crate (aterm's
# `verify cells` applies the same override per triple, tools/cross-cell-gate.tsv). The
# host row runs the real script. A ring bump changes the `links` name, so this override
# replaces nothing and the cross rows stop at ring's script until it is re-read.
RING_LINKS=ring_core_0_17_14_

say "== Stock toolchain (STOCK EXCEPTION) =="
RUSTUP=$(command -v rustup) || RUSTUP="${CARGO_HOME:-${HOME:-}/.cargo}/bin/rustup"
[ -x "$RUSTUP" ] || could_not_run "no rustup on PATH or in \${CARGO_HOME:-\$HOME/.cargo}/bin; install rustup and \`rustup toolchain install $TC\`"
stock_rustc=$("$RUSTUP" which --toolchain "$TC" rustc 2>&1) ||
  could_not_run "rustup cannot locate the \`$TC\` compiler ($(printf '%s\n' "$stock_rustc" | head -n 1)); \`rustup toolchain install $TC\`"
# Cargo invokes a bare rustc unless RUSTC names one. Homebrew's rustup need not
# install ~/.cargo/bin/rustc, and the PATH compiler may be aterm's reroute stub
# (or another toolchain). Probe and compile with exactly the same executable.
export RUSTC="$stock_rustc"
vv=$("$RUSTC" -vV 2>&1) ||
  could_not_run "cannot run the \`$TC\` compiler at $RUSTC ($(printf '%s\n' "$vv" | head -n 1))"
# The test every astream build script applies (crates/astream-wire/clean_islands.rs): a
# `trust:` line in -vV is Trust, which would compile the islands this check exists to skip.
if printf '%s\n' "$vv" | grep -q '^trust:'; then
  could_not_run "\`$TC\` is a Trust compiler (its rustc -vV has a trust: line), not a stock one"
fi
host=$(printf '%s\n' "$vv" | sed -n 's/^host: //p')
release=$(printf '%s\n' "$vv" | sed -n 's/^release: //p')
[ -n "$host" ] || could_not_run "\`$RUSTC -vV\` names no host"
installed=$("$RUSTUP" target list --installed --toolchain "$TC" 2>&1) ||
  could_not_run "rustup cannot list the \`$TC\` toolchain's targets ($(printf '%s\n' "$installed" | head -n 1))"
targets=("$host")
for t in "${CROSS[@]}"; do [ "$t" = "$host" ] || targets+=("$t"); done
missing=()
for t in "${targets[@]}"; do printf '%s\n' "$installed" | grep -qx "$t" || missing+=("$t"); done
[ ${#missing[@]} -eq 0 ] ||
  could_not_run "the \`$TC\` toolchain has no standard library for ${missing[*]}: \`rustup target add --toolchain $TC ${missing[*]}\`"
say "  $TC: rustc $release, host $host; targets ${targets[*]}"
say "  RUSTFLAGS=\"$DENY\": a rustc warning is a refusal"

OUT="${STOCK_OUT_DIR:-target/stock}"
mkdir -p "$OUT" || exit 2
OUT="$(cd "$OUT" && pwd)" || exit 2
export CARGO_TARGET_DIR="$OUT/target"

refused=0
stopped=0
rows=()
# One `cargo check` of one row: label, then the selection.
check() {
  local label=$1 log
  shift
  log="$OUT/$label.log"
  say ""
  say "== $label: cargo check --locked --keep-going $* =="
  "$RUSTUP" run "$TC" cargo check --locked --keep-going "$@" >"$log" 2>&1
  local rc=$? verdict=ok
  if [ $rc -ne 0 ]; then
    # What stopped cargo decides the verdict. rustc refusing a crate (a warning among the
    # reasons), one of astream's own build scripts failing (a path package, so its path
    # follows its version), and a Cargo.lock that --locked will not let cargo rewrite are
    # this repo's; anything else is this machine's.
    if grep -q '^error: could not compile' "$log" ||
      grep -Eq '^error: failed to run custom build command for `[^`]* \((/|[A-Za-z]:)' "$log" ||
      grep -Eq '^error: .*lock ?file.*--locked' "$log"; then
      verdict="REFUSED"
      refused=1
      grep -E '^error|^ +--> ' "$log" | head -n 20 | sed 's/^/    /'
    else
      verdict="COULD NOT RUN: cargo exited $rc before compiling"
      stopped=1
      grep -E '^error' "$log" | head -n 5 | sed 's/^/    /'
    fi
  fi
  say "  -> $verdict (log: $log)"
  rows+=("| $label | $* | $verdict |")
}

for t in "${targets[@]}"; do
  for features in default all; do
    # The selection rides in "$@": macOS's bash 3.2 calls an empty array unbound. The host
    # row names no --target (see the top of this file).
    set --
    [ "$t" = "$host" ] ||
      set -- --target "$t" --config "target.$t.$RING_LINKS.rustc-link-lib=[\"$RING_LINKS\"]"
    [ "$features" = default ] || set -- "$@" --all-features
    case "$t" in
      *-windows-*)
        check "$t-$features" "$@" --workspace --exclude astream-broker --all-targets
        check "$t-$features-broker" "$@" -p astream-broker --lib --test '*' --examples
        ;;
      *)
        check "$t-$features" "$@" --workspace --all-targets
        ;;
    esac
  done
done

say ""
say "== Summary: stock rustc $release ($TC), RUSTFLAGS=\"$DENY\" =="
say "| check | cargo check --locked --keep-going ... | verdict |"
say "|---|---|---|"
for r in "${rows[@]}"; do say "$r"; done
say ""
if [ $refused -ne 0 ]; then
  say "REFUSED (exit 1): stock cargo refused astream (a compile error or warning, a failing astream"
  say "  build script, or a Cargo.lock --locked will not rewrite); see the rows and logs above."
  exit 1
fi
if [ $stopped -ne 0 ]; then
  could_not_run "cargo stopped before compiling at least one row; see the rows above"
fi
say "OK (exit 0): a stock rustc compiles every astream crate for ${targets[*]}, with no warning."
exit 0
