#!/usr/bin/env bash
# scripts/verify-trust.sh — re-run astream-wire's compiler-enforced verification survey under
# the Trust toolchain and report it HONESTLY: per function, per policy, exit code = verdict.
#
# Trust (https://github.com/alabsystems/trust) is a rust-lang/rust fork whose verifier runs as a
# MIR pass DURING compilation. It AUTO-GENERATES the Level-0 safety obligations (integer overflow,
# array/slice bounds, div/rem-by-zero, shift overflow, allocation bounds, panic-freedom) from the
# crate's real MIR — no harnesses, no annotations — and discharges what it can. Verification is
# on by default; `-Z trust-policy` selects only how the verdicts are ENFORCED:
#   advisory  every obligation is reported, none is fatal      -> the per-function survey table
#   strict    Trust's default: a refutation, or an unproved obligation with NO runtime fallback,
#             is a build error; a gap rustc still checks at runtime is reported, not fatal
#   certify   full static discharge: EVERY unproved obligation is a build error (the release gate)
#
# This builds the REAL crate (`cargo build -p astream-wire --lib`), so every verdict is about
# astream-wire's own functions — never a hand-copied mirror of them, which would stay "proved"
# whatever the crate did. The library has no dependencies, so nothing but astream's code is
# verified.
#
# It is an ATTACHED, RE-RUNNABLE artifact, not a `make ci` claim: Trust is a separately built
# toolchain and never a workspace dependency, so its state can never break the substrate build.
# The captured report is evidence/verify/trust-wire.md; this script is how it is re-captured.
#
# EXIT CODE = VERDICT (the output says which):
#   0  the crate builds under BOTH the strict and the certify policy (every obligation proved)
#   1  verification RAN and the crate does not fully verify (refuted / unproved obligations);
#      the per-function table says exactly which
#   2  the toolchain or its CLI failed (not installed, unknown flag, a non-verification compile
#      error): NOT a verdict about astream's code — never read it as one
#   3  the installed Trust is not the pinned commit. The artifact was captured with the pin, so
#      an unpinned run is not comparable to it; TRUST_ALLOW_UNPINNED=1 surveys anyway.
#
# Logs: target/trust-verify/{advisory,strict,certify,targo}.log (override with TRUST_OUT_DIR;
# keep it inside the repository — targo refuses a world-writable target path such as /tmp).
# Cost: three fresh Trust builds of a dependency-free crate plus one targo run — a few minutes.
#
# No `set -e`: every build's exit code is captured and judged explicitly below. The
# setup steps that must not fail are checked one by one instead (exit 2: not a verdict).
set -u
cd "$(dirname "$0")/.." || exit 2

# The Trust commit evidence/verify/trust-wire.md was captured with. `rustc --version` of the
# installed toolchain must contain it: rustc 1.99.0-dev (4b3506be5 2026-08-20).
TRUST_PINNED_COMMIT="4b3506be5"

OUT="${TRUST_OUT_DIR:-target/trust-verify}"
mkdir -p "$OUT" || exit 2
# Keep Trust's artifacts out of the stock target dir: a different rustc, different fingerprints.
# (Absolute, so the path survives targo's own directory changes. Unchecked, a failed `cd`
# would leave OUT empty and aim CARGO_TARGET_DIR and every log at `/`.)
OUT="$(cd "$OUT" && pwd)" || exit 2
export CARGO_TARGET_DIR="$OUT/target"

say() { printf '%s\n' "$*"; }

cli_error() { # $1 = what happened, $2 = where to look
  say ""
  say "  -> TOOLCHAIN/CLI ERROR (exit 2): $1"
  say "     This is NOT a verification verdict about astream's code. See: $2"
  exit 2
}

# A compiler/CLI failure that is not a Trust verdict: an unknown flag, a missing toolchain, or an
# ordinary (non-verification) compile error. Trust's own verdict lines all start `error: Trust`.
has_cli_error() {
  grep -qE 'unknown unstable option|Unrecognized option|error: unknown|error\[E[0-9]+\]|error: failed to run|error: could not find|error: failed to parse|error: no such command|toolchain .* is not installed' "$1"
}

# Functions named in `error: Trust ... for \`fn\`` verdict lines of a log, sorted, unique.
failing_functions() {
  sed -n 's/^error: Trust .* for `\([^`]*\)`.*/\1/p' "$1" | sort -u
}

# cargo's own error count from `could not compile ... due to N previous error(s)`.
error_count() {
  local n
  n=$(sed -n 's/.*could not compile.*due to \([0-9][0-9]*\) previous error.*/\1/p' "$1" | head -1)
  if [ -z "$n" ]; then n=$(grep -c '^error: Trust' "$1"); fi
  printf '%s' "$n"
}

# ---------------------------------------------------------------------------------------------
say "== 0. Toolchain =="
if ! version=$(rustup run trust rustc --version 2>&1); then
  say "Trust toolchain not installed (rustup toolchain 'trust' missing): $version"
  say "  build it from the Trust checkout and 'rustup toolchain link trust <sysroot>'"
  exit 2
fi
say "installed: $version"
say "pinned:    $TRUST_PINNED_COMMIT  (the commit evidence/verify/trust-wire.md was captured with)"
unpinned=0
case "$version" in
  *"$TRUST_PINNED_COMMIT"*) say "  -> matches the pin" ;;
  *)
    if [ "${TRUST_ALLOW_UNPINNED:-0}" = "1" ]; then
      unpinned=1
      say "  -> WARNING: NOT the pinned commit. Verdicts below are NOT comparable to the captured"
      say "     artifact (TRUST_ALLOW_UNPINNED=1 given; re-capture the artifact if you adopt them)."
    else
      say "  -> MISMATCH (exit 3): the installed Trust is not the pinned commit, so this run"
      say "     cannot re-verify the captured artifact. Install the pin, or set"
      say "     TRUST_ALLOW_UNPINNED=1 to survey under this toolchain anyway."
      exit 3
    fi
    ;;
esac

# The flags this script relies on must exist on this toolchain: a removed flag's "unknown
# option" error is a CLI error (exit 2), never to be read as a REFUTED verdict.
zhelp=$(rustup run trust rustc -Z help 2>&1)
for flag in trust-policy trust-verify-output; do
  if ! printf '%s\n' "$zhelp" | grep -q -- "$flag="; then
    cli_error "rustc -Z help does not list -Z $flag (Trust CLI drift; update this script)" "rustc -Z help"
  fi
done

# build POLICY OUTPUT-MODE : a fresh (never cached) Trust build of the astream-wire library.
build() {
  local policy=$1 mode=$2
  # A cached artifact would carry no verifier output, so the survey table would be empty and a
  # previously-green strict build would be "green" without running. Always rebuild.
  rustup run trust cargo clean --quiet -p astream-wire >"$OUT/clean.log" 2>&1 || true
  RUSTFLAGS="-Z trust-policy=$policy -Z trust-verify-output=$mode" \
    rustup run trust cargo build --locked -p astream-wire --lib >"$OUT/$policy.log" 2>&1
}

# ---------------------------------------------------------------------------------------------
say ""
say "== 1. Survey (-Z trust-policy=advisory): every auto-generated obligation, per function =="
say "   (builds the dependency-free library: only astream-wire's own functions are verified;"
say "    nothing is fatal under this policy)"
build advisory json
rc=$?
if has_cli_error "$OUT/advisory.log"; then
  cli_error "the advisory build hit a compiler/CLI error (exit $rc)" "$OUT/advisory.log"
fi
if [ $rc -ne 0 ]; then
  cli_error "the advisory build failed (exit $rc) although the advisory policy never fails on a verdict" "$OUT/advisory.log"
fi
if ! grep -q 'TRUST_JSON:{"type":"function_result"' "$OUT/advisory.log"; then
  cli_error "the advisory build emitted no per-function verifier rows (verification did not run?)" "$OUT/advisory.log"
fi

say ""
say "Functions with at least one obligation (a function the verifier found trivially panic-free —"
say "no obligation at all — is counted below the table, not listed):"
say ""
say "| function | obligations | proved | failed | unknown | runtime-checked | not proved: kind -> outcome (file:line) |"
say "|---|---|---|---|---|---|---|"
# One TRUST_JSON function_result row per function. The per-function counters close every row, so
# they are read from its tail (a nested diagnostic can never be mistaken for them); each
# obligation is split on its `obligation_id` key so kind, outcome and location pair up without a
# JSON parser. Rows without obligation ids are the verifier's own inventory gaps
# (`native-verification-gap`), reported as such. Named functions sort before derived impls.
grep -o 'TRUST_JSON:{"type":"function_result".*' "$OUT/advisory.log" | awk '
  function field(s, key,   m) { if (match(s, "\"" key "\":\"[^\"]*\"")) { m = substr(s, RSTART, RLENGTH); sub("\"" key "\":\"", "", m); sub("\"$", "", m); return m } return "" }
  function num(s, key,   m) { if (match(s, "\"" key "\":[0-9]+")) { m = substr(s, RSTART, RLENGTH); sub("\"" key "\":", "", m); return m + 0 } return 0 }
  {
    fn = field($0, "function")
    if (index($0, "\"kind\":\"no_obligations\"") > 0) next
    tail = $0
    if (match(tail, /"proved":[0-9]+,"failed":[0-9]+,"unknown":[0-9]+,"timed_out":[0-9]+,"skipped":[0-9]+,"runtime_checked":[0-9]+,"cached":[0-9]+,"total":[0-9]+\}$/)) tail = substr(tail, RSTART)
    total = num(tail, "total"); proved = num(tail, "proved"); failed = num(tail, "failed")
    unknown = num(tail, "unknown"); rtc = num(tail, "runtime_checked")
    notes = ""
    n = split($0, ob, /\{"obligation_id"/)
    for (i = 2; i <= n; i++) {
      outcome = field(ob[i], "outcome")
      if (outcome == "proved" || outcome == "") continue
      kind = field(ob[i], "kind"); file = field(ob[i], "file"); line = num(ob[i], "line_start")
      sub(/.*\//, "", file)
      tag = kind " -> " outcome
      if (file != "") tag = tag " (" file ":" line ")"
      notes = notes (notes == "" ? "" : "; ") tag
    }
    if (n <= 1) notes = field($0, "kind") " -> " field($0, "outcome")
    if (notes == "") notes = "-"
    printf "%s\t| `%s` | %d | %d | %d | %d | %d | %s |\n", (substr(fn, 1, 1) == "<" ? 1 : 0), fn, total, proved, failed, unknown, rtc, notes
  }' | sort | cut -f2-
trivial=$(grep -c '"kind":"no_obligations"' "$OUT/advisory.log")
say ""
say "Functions with no panic obligation at all (trivially panic-free; the compiler counts each as"
say "one proved obligation): $trivial"
say ""
say "crate totals (the compiler's crate_summary row):"
grep -o 'TRUST_JSON:{"type":"crate_summary".*' "$OUT/advisory.log" | sed -e 's/^TRUST_JSON://' -e 's/[{}"]//g' -e 's/,/  /g' | sed 's/^/  /'

# ---------------------------------------------------------------------------------------------
say ""
say "== 2. Strict policy (-Z trust-policy=strict, Trust's default): does the crate build? =="
build strict human
strict_rc=$?
if has_cli_error "$OUT/strict.log"; then
  cli_error "the strict build hit a compiler/CLI error (exit $strict_rc)" "$OUT/strict.log"
fi
strict_errors=$(error_count "$OUT/strict.log")
if [ $strict_rc -eq 0 ]; then
  say "  -> BUILDS (exit 0): no refutation and no unproved obligation without a runtime fallback."
  strict_state="pass"
else
  say "  -> DOES NOT BUILD (cargo exit $strict_rc): $strict_errors error(s)"
  grep -E 'could not compile' "$OUT/strict.log" | sed 's/^/     /'
  say "     functions failing strict verification:"
  failing_functions "$OUT/strict.log" | sed 's/^/       /'
  strict_state="fail"
fi

# ---------------------------------------------------------------------------------------------
say ""
say "== 3. Certify policy (-Z trust-policy=certify): is every obligation statically proved? =="
build certify human
certify_rc=$?
if has_cli_error "$OUT/certify.log"; then
  cli_error "the certify build hit a compiler/CLI error (exit $certify_rc)" "$OUT/certify.log"
fi
certify_errors=$(error_count "$OUT/certify.log")
if [ $certify_rc -eq 0 ]; then
  say "  -> BUILDS (exit 0): every Level-0 obligation statically discharged."
  certify_state="pass"
else
  say "  -> DOES NOT BUILD (cargo exit $certify_rc): $certify_errors error(s)"
  grep -E 'could not compile' "$OUT/certify.log" | sed 's/^/     /'
  extra=$(comm -13 <(failing_functions "$OUT/strict.log") <(failing_functions "$OUT/certify.log"))
  if [ -n "$extra" ]; then
    say "     functions failing certify verification beyond the strict list above:"
    printf '%s\n' "$extra" | sed 's/^/       /'
  else
    say "     (the same functions as under strict; certify additionally fails every"
    say "      runtime-checked obligation in them)"
  fi
  certify_state="fail"
fi

# ---------------------------------------------------------------------------------------------
say ""
say "== 4. Whole-crate report via targo (Trust's cargo frontend; informational, not the verdict) =="
if command -v targo >/dev/null 2>&1; then
  # targo applies its default hardened profile (unix_hardened), which adds boundary VCs, so its
  # obligation count differs from the survey above. Its exit code: 0 pass, 1 violations,
  # 2 it could not run (then its own error line is shown and nothing is concluded from it).
  targo trust check -p astream-wire >"$OUT/targo.log" 2>&1
  targo_rc=$?
  say "   targo trust check -p astream-wire (exit $targo_rc):"
  grep -E '^(Level|Summary|Coverage|Result):|^  (proved|failed|unknown) by kind:|^  Gate:|^targo trust: error' "$OUT/targo.log" | sed 's/^ *//' | sed 's/^/     /'
  if ! grep -qE '^Summary:' "$OUT/targo.log"; then
    say "     (no summary produced; see $OUT/targo.log)"
  fi
else
  say "   targo not on PATH; skipped."
fi

# ---------------------------------------------------------------------------------------------
say ""
say "== VERDICT =="
say "  toolchain: $version"
if [ $unpinned -eq 1 ]; then
  say "  (UNPINNED toolchain — not comparable to evidence/verify/trust-wire.md)"
fi
if [ "$strict_state" = "pass" ] && [ "$certify_state" = "pass" ]; then
  say "  PROVED (exit 0): astream-wire builds under the strict AND the certify policy — every"
  say "  auto-generated Level-0 obligation is statically discharged."
  exit 0
fi
say "  NOT FULLY VERIFIED (exit 1): strict=$strict_state ($strict_errors error(s)),"
say "  certify=$certify_state ($certify_errors error(s)). The survey table above says which"
say "  functions and which obligations; the crate does NOT build drop-in under Trust's default"
say "  policy at this commit. Logs: $OUT/"
exit 1
