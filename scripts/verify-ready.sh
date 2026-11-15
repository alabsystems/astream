#!/usr/bin/env bash
# scripts/verify-ready.sh — the verified-lane gate over astream's READY targets: every target
# below has ZERO failed Level-0 rows under `targo trust check --allow-l0-gaps`, and this script
# keeps it that way.
#
# Per target it runs ONE fresh verified check and reads that run's report.json
# (`verification_gate.counts`). A target passes only when ALL of these hold:
#   - verification ran and wrote a report (else exit 2: a toolchain/CLI problem, not a verdict);
#   - it emitted at least one obligation (a vacuous run proves nothing and does not pass);
#   - targo exited 0 and the report's own decision is pass or conditional-pass (this script
#     only adds reasons to fail; it never overrides the toolchain's FAIL);
#   - failed == 0 and contract_panics == 0 (a refuted obligation is a regression);
#   - the report says coverage is complete (every eligible unit was processed);
#   - proved >= the target's FLOOR (a proof that silently stopped going through is a regression).
# Unknown, runtime-checked, assumed and mandated rows are reported and NEVER counted toward the
# floor. This is the ADVISORY lane: CONDITIONAL-PASS means "no refutation", not "proved" — the
# unknown rows are open obligations. Strict (`targo trust check`) and certify are the
# destination; scripts/verify-trust.sh runs those for astream-wire.
#
# Floors are 80% of the proved count measured with Trust 321aaeda7 (2026-10-02); raise a floor
# when more is proved, never lower one to go green.
#
# One floor moved DOWN, with its proofs, not past them: on 2026-10-20 (realign/astream-primitives,
# the same Trust 321aaeda7) astream-cap's HMAC core moved to astream-digest, taking its 328 proved
# obligations with it (hmac_ipad 128, hmac_opad 128, pad_digest_key 64, hmac_sha256_parts 8), and
# astream-aead's copy of the same code was deleted for the shared one. Measured before -> after
# (after = e467a1d, the branch merged onto main 93ebb71, where capfile reads every secret file
# through one open): astream-cap 627 -> 302, astream-digest 413 -> 746, astream-aead 2171 -> 1847,
# failed 0 in each. astream-cap's and astream-digest's floors are re-based to 80% of the new
# counts (241, 596); astream-aead's 1736 still holds and stays.
#
# All 137 library and binary targets across all 131 workspace crates are gated below: 21 in
# astream's own 15 crates and 116 in the 116 standalone models (README, "Standalone models").
#
# EXIT CODE = VERDICT:
#   0  every target: verification ran, failed == 0, proved >= floor
#   1  verification ran and at least one target regressed (the table says which and why)
#   2  invalid target label or toolchain/CLI failure (not the real targo, no report,
#      compile error): NOT a verdict about astream's code
#
# Logs and reports: $CARGO_TARGET_DIR/trust-ready/<label>.log and .../<label>/report.json
# (target/trust-ready by default; TRUST_OUT_DIR overrides this report root). Verified
# fingerprints use the separate sibling <report-root>.target.noindex, which the driver
# creates and manages. Never precreate that target or place logs/reports inside it before
# admission. A publisher-provided artifact root encloses both siblings, preserving its
# native and cross-target fingerprint discovery. Keep an explicit TRUST_OUT_DIR
# directly beneath that root when publication must collect its rows. The publisher
# provides a private artifact root because the verified lane refuses world-writable
# ancestors such as /tmp.
# Each compiler log is forwarded unchanged for the publisher's census and diagnostics.
# TRUST_JOBS sets -j (default 4). Needs jq.
set -u
cd "$(dirname "$0")/.." || exit 2

# label | proved floor | targo trust check target selection
TARGETS=(
  "astream-wire|658|-p astream-wire --lib"
  "astream-effects|407|-p astream-effects --lib"
  "astream-pump|384|-p astream-pump --lib"
  "astream-pump-bin|156|-p astream-pump --bins"
  "astream-kafka|1293|-p astream-kafka --lib --all-features"
  "astream-cap|256|-p astream-cap --lib --all-features"
  "astream-evidence-bin|245|-p astream-evidence --bins"
  "astream-evidence|318|-p astream-evidence --lib"
  "astream-agent|257|-p astream-agent --lib"
  "astream-aead|2128|-p astream-aead --lib --all-features"
  "astream-live|206|-p astream-live --lib"
  "astream-live-bin|278|-p astream-live --bins"
  "astream-digest|682|-p astream-digest --lib"
  "astream-engine|729|-p astream-engine --lib"
  "astream-engine-bin|344|-p astream-engine --bins"
  "astream-vt-ext|124|-p astream-vt-ext --lib"
  "astream-session-ops|156|-p astream-session-ops --lib"
  "astream-fabric|144|-p astream-fabric --lib"
  "astream-fabric-ops|126|-p astream-fabric-ops --lib"
  "astream-cap-ext|500|-p astream-cap-ext --lib"
  "astream-protocol-1|97|-p astream-protocol-1 --lib"
  "astream-protocol-2|48|-p astream-protocol-2 --lib"
  "astream-protocol-3|204|-p astream-protocol-3 --lib"
  "astream-protocol-4|129|-p astream-protocol-4 --lib"
  "astream-protocol-5|78|-p astream-protocol-5 --lib"
  "astream-protocol-6|48|-p astream-protocol-6 --lib"
  "astream-integrity-1|172|-p astream-integrity-1 --lib"
  "astream-integrity-2|41|-p astream-integrity-2 --lib"
  "astream-integrity-3|104|-p astream-integrity-3 --lib"
  "astream-integrity-4|83|-p astream-integrity-4 --lib"
  "astream-integrity-5|67|-p astream-integrity-5 --lib"
  "astream-integrity-6|148|-p astream-integrity-6 --lib"
  "astream-coalesce-1|348|-p astream-coalesce-1 --lib"
  "astream-coalesce-2|146|-p astream-coalesce-2 --lib"
  "astream-coalesce-3|138|-p astream-coalesce-3 --lib"
  "astream-coalesce-4|275|-p astream-coalesce-4 --lib"
  "astream-coalesce-5|140|-p astream-coalesce-5 --lib"
  "astream-coalesce-6|62|-p astream-coalesce-6 --lib"
  "astream-flow-1|63|-p astream-flow-1 --lib"
  "astream-flow-2|52|-p astream-flow-2 --lib"
  "astream-flow-3|56|-p astream-flow-3 --lib"
  "astream-flow-4|56|-p astream-flow-4 --lib"
  "astream-flow-5|54|-p astream-flow-5 --lib"
  "astream-flow-6|65|-p astream-flow-6 --lib"
  "astream-leases-1|156|-p astream-leases-1 --lib"
  "astream-leases-2|52|-p astream-leases-2 --lib"
  "astream-leases-3|172|-p astream-leases-3 --lib"
  "astream-leases-4|141|-p astream-leases-4 --lib"
  "astream-leases-5|68|-p astream-leases-5 --lib"
  "astream-leases-6|196|-p astream-leases-6 --lib"
  "astream-routing-1|158|-p astream-routing-1 --lib"
  "astream-routing-2|172|-p astream-routing-2 --lib"
  "astream-routing-3|134|-p astream-routing-3 --lib"
  "astream-routing-4|51|-p astream-routing-4 --lib"
  "astream-routing-5|143|-p astream-routing-5 --lib"
  "astream-routing-6|58|-p astream-routing-6 --lib"
  "astream-storage-1|140|-p astream-storage-1 --lib"
  "astream-storage-2|196|-p astream-storage-2 --lib"
  "astream-storage-3|60|-p astream-storage-3 --lib"
  "astream-storage-4|54|-p astream-storage-4 --lib"
  "astream-storage-5|52|-p astream-storage-5 --lib"
  "astream-storage-6|60|-p astream-storage-6 --lib"
  "astream-cognition-1|55|-p astream-cognition-1 --lib"
  "astream-cognition-2|61|-p astream-cognition-2 --lib"
  "astream-cognition-3|64|-p astream-cognition-3 --lib"
  "astream-cognition-4|59|-p astream-cognition-4 --lib"
  "astream-cognition-5|104|-p astream-cognition-5 --lib"
  "astream-cognition-6|49|-p astream-cognition-6 --lib"
  "astream-security-1|170|-p astream-security-1 --lib"
  "astream-security-2|58|-p astream-security-2 --lib"
  "astream-security-3|60|-p astream-security-3 --lib"
  "astream-security-4|57|-p astream-security-4 --lib"
  "astream-security-5|54|-p astream-security-5 --lib"
  "astream-security-6|65|-p astream-security-6 --lib"
  "astream-resync-1|54|-p astream-resync-1 --lib"
  "astream-resync-2|67|-p astream-resync-2 --lib"
  "astream-resync-3|55|-p astream-resync-3 --lib"
  "astream-resync-4|56|-p astream-resync-4 --lib"
  "astream-resync-5|60|-p astream-resync-5 --lib"
  "astream-resync-6|55|-p astream-resync-6 --lib"
  "astream-guards-1|51|-p astream-guards-1 --lib"
  "astream-guards-2|60|-p astream-guards-2 --lib"
  "astream-guards-3|65|-p astream-guards-3 --lib"
  "astream-guards-4|69|-p astream-guards-4 --lib"
  "astream-guards-5|59|-p astream-guards-5 --lib"
  "astream-guards-6|54|-p astream-guards-6 --lib"
  "astream-failover-ops|16|-p astream-failover-ops --lib"
  "astream-mesh-discovery|28|-p astream-mesh-discovery --lib"
  "astream-cert-auth|54|-p astream-cert-auth --lib"
  "astream-presence-ext|40|-p astream-presence-ext --lib"
  "astream-retire-history|35|-p astream-retire-history --lib"
  "astream-restore-ops|11|-p astream-restore-ops --lib"
  "astream-quota-sched|25|-p astream-quota-sched --lib"
  "astream-pty-mux|10|-p astream-pty-mux --lib"
  "astream-audit-seal|14|-p astream-audit-seal --lib"
  "astream-wan-delta|17|-p astream-wan-delta --lib"
  "astream-worktree-sync|16|-p astream-worktree-sync --lib"
  "astream-mcp-bridge|19|-p astream-mcp-bridge --lib"
  "astream-subagent-dag|12|-p astream-subagent-dag --lib"
  "astream-abrew-pkg|11|-p astream-abrew-pkg --lib"
  "astream-env-scrub|12|-p astream-env-scrub --lib"
  "astream-transcript-idx|12|-p astream-transcript-idx --lib"
  "astream-sys-telemetry|40|-p astream-sys-telemetry --lib"
  "astream-autopilot-ctl|10|-p astream-autopilot-ctl --lib"
  "astream-git-align|10|-p astream-git-align --lib"
  "astream-grapheme-layout|17|-p astream-grapheme-layout --lib"
  "astream-sim-fabric|16|-p astream-sim-fabric --lib"
  "astream-tunnel-relay|10|-p astream-tunnel-relay --lib"
  "astream-smt-governor|39|-p astream-smt-governor --lib"
  "astream-agy-quota|39|-p astream-agy-quota --lib"
  "astream-macos-tcc|10|-p astream-macos-tcc --lib"
  "astream-fabric-mail|10|-p astream-fabric-mail --lib"
  "astream-osc-protocol|10|-p astream-osc-protocol --lib"
  "astream-atpkg-toolchain|39|-p astream-atpkg-toolchain --lib"
  "astream-scrollback-tier|10|-p astream-scrollback-tier --lib"
  "astream-pty-signal|38|-p astream-pty-signal --lib"
  "astream-link-cut|37|-p astream-link-cut --lib"
  "astream-abrew-bottle|42|-p astream-abrew-bottle --lib"
  "astream-keybind-chord|37|-p astream-keybind-chord --lib"
  "astream-secret-vault|41|-p astream-secret-vault --lib"
  "astream-metal-damage|41|-p astream-metal-damage --lib"
  "astream-self-restart|40|-p astream-self-restart --lib"
  "astream-cross-cells|39|-p astream-cross-cells --lib"
  "astream-ordered-barrier|42|-p astream-ordered-barrier --lib"
  "astream-speculative-echo|40|-p astream-speculative-echo --lib"
  "astream-held-compactor|40|-p astream-held-compactor --lib"
  "astream-uds-owner|40|-p astream-uds-owner --lib"
  "astream-ext-authority|44|-p astream-ext-authority --lib"
  "astream-lease-failover|42|-p astream-lease-failover --lib"
  "astream-seccomp-replay|39|-p astream-seccomp-replay --lib"
  "astream-subject-retire|44|-p astream-subject-retire --lib"
  "astream-sys|125|-p astream-sys --lib"
  "astream-host|264|-p astream-host --lib"
  "astream-host-bin|159|-p astream-host --bins"
  "astream-term|486|-p astream-term --lib"
  "astream-broker-bin|288|-p astream-broker --bins"
  "astream-broker|2650|-p astream-broker --lib --all-features"
)

say() { printf '%s\n' "$*"; }

# Reject every unknown request before toolchain checks or report side effects.
# The selection loop below retains TARGETS order; no arguments still means all.
for want in "$@"; do
  match=0
  for t in "${TARGETS[@]}"; do
    [ "${t%%|*}" = "$want" ] && match=1 && break
  done
  if [ "$match" -eq 0 ]; then
    say "unknown READY target label: $want"
    exit 2
  fi
done

# A verified run must see no ambient compiler flags: they would change what is verified.
unset TRUSTFLAGS RUSTFLAGS CARGO_ENCODED_RUSTFLAGS CARGO_ENCODED_TRUSTFLAGS CARGO_BUILD_RUSTFLAGS
# Intermediates belong in the verified target, never in an inherited native
# build directory. A .noindex target also needs no additional shim relocation.
unset CARGO_BUILD_BUILD_DIR TARGO_BUILD_BUILD_DIR

say "== Toolchain =="
# `targo --unverified --version` is the discriminator: the real targo accepts the flag, upstream
# cargo installed under the name `targo` rejects it — and would verify nothing.
if ! targo_version=$(targo --unverified --version 2>&1); then
  say "\`targo --unverified --version\` failed: this is not the Trust targo ($targo_version)"
  say "  run \`aterm pkg doctor\`"
  exit 2
fi
command -v jq >/dev/null || { say "jq is required to read report.json"; exit 2; }
say "  $targo_version"

OUT="${TRUST_OUT_DIR:-${CARGO_TARGET_DIR:-target}/trust-ready}"
mkdir -p "$OUT" || exit 2
OUT="$(cd "$OUT" && pwd)" || exit 2
# Keep compiler custody separate from script-owned logs/reports. atpkg refuses
# a precreated, unmanaged explicit target: let the driver create/register this
# sibling on first use and reuse its own custody on later runs. Never remove it
# or manufacture ownership metadata. Its .noindex suffix avoids another nested
# intermediates directory, so publication finds both native and cross profiles.
READY_TARGET="${OUT}.target.noindex"
export CARGO_TARGET_DIR="$READY_TARGET"
JOBS="${TRUST_JOBS:-4}"

regressed=0
rows=()
for t in "${TARGETS[@]}"; do
  IFS='|' read -r label floor selection <<<"$t"
  if [ $# -gt 0 ]; then
    match=0
    for want in "$@"; do
      [ "$label" = "$want" ] && match=1 && break
    done
    [ $match -eq 1 ] || continue
  fi
  log="$OUT/$label.log"
  rep="$OUT/$label"
  rm -rf "${rep:?}"
  say ""
  say "== $label: targo trust check --allow-l0-gaps --locked -j $JOBS $selection =="
  # shellcheck disable=SC2086 # $selection is a list of words on purpose
  targo trust check --allow-l0-gaps --locked -j "$JOBS" $selection --report-dir "$rep" >"$log" 2>&1
  rc=$?
  # targo trust check exits 0 (pass) or 1 (violations) when verification ran.
  if [ $rc -ne 0 ] && [ $rc -ne 1 ]; then
    cat "$log"
    say "  -> TOOLCHAIN/CLI ERROR (exit 2): targo exited $rc without a verdict. See $log"
    exit 2
  fi
  # Do not turn the compiler's verdict into only a script summary: the publication
  # engine needs the actual banners from every selected target to retain its census.
  # A valid report without a banner is a transport failure, never a green gate.
  if ! grep -qE '^[[:space:]]*Gate:[[:space:]]*[A-Z-]+[[:space:]]*\[[a-z-]+ lane, exit [0-9]+\][[:space:]]*\([^)]*\)[[:space:]]*$' "$log"; then
    cat "$log"
    say "  -> TOOLCHAIN/CLI ERROR (exit 2): targo printed no readable Gate banner. See $log"
    exit 2
  fi
  cat "$log"
  if ! [ -s "$rep/report.json" ] || ! jq -e '.verification_gate.counts' "$rep/report.json" >/dev/null; then
    say "  -> TOOLCHAIN/CLI ERROR (exit 2): no report.json with gate counts. See $log"
    exit 2
  fi
  read -r total proved failed unknown rtc assumed mandated panics decision rep_exit coverage < <(jq -r \
    '.verification_gate | [.counts.total, .counts.proved, .counts.failed, .counts.unknown,
      .counts.runtime_checked, .counts.assumed, .counts.mandated, .counts.contract_panics,
      .decision, .exit_code, .coverage.coverage_complete] | map(tostring) | @tsv' \
    "$rep/report.json")
  # Every count must be a number: a missing/null field would make each `[ -eq ]` below
  # false and read as "ok". A report we cannot read is a toolchain problem, not a pass.
  for v in "$total" "$proved" "$failed" "$unknown" "$rtc" "$assumed" "$mandated" "$panics" "$rep_exit"; do
    case "$v" in
      '' | *[!0-9]*)
        say "  -> TOOLCHAIN/CLI ERROR (exit 2): report.json gate counts are not all integers. See $rep/report.json"
        exit 2
        ;;
    esac
  done
  if [ "$rep_exit" -ne "$rc" ]; then
    say "  -> TOOLCHAIN/CLI ERROR (exit 2): targo exited $rc but its report says exit_code $rep_exit. See $log"
    exit 2
  fi
  # The report's own decision is authoritative: our checks only ADD reasons to fail.
  verdict="ok"
  if [ "$total" -eq 0 ]; then
    verdict="REGRESSED: no obligations (vacuous)"
  elif [ "$failed" -gt 0 ]; then
    verdict="REGRESSED: $failed failed"
  elif [ "$panics" -gt 0 ]; then
    verdict="REGRESSED: $panics contract panic(s)"
  elif [ "$rc" -ne 0 ] || { [ "$decision" != "pass" ] && [ "$decision" != "conditional-pass" ]; }; then
    verdict="REGRESSED: gate decision $decision (targo exit $rc)"
  elif [ "$coverage" != "true" ]; then
    verdict="REGRESSED: coverage incomplete"
  elif [ "$proved" -lt "$floor" ]; then
    verdict="REGRESSED: proved $proved < floor $floor"
  fi
  [ "$verdict" = "ok" ] || regressed=1
  say "  $decision (targo exit $rc): proved $proved (floor $floor), failed $failed, unknown $unknown, runtime-checked $rtc, assumed $assumed, mandated $mandated / $total -> $verdict"
  if [ "$failed" -gt 0 ]; then
    grep -E '\[FAILED\]' "$log" | sort -u | sed 's/^ */    /'
  fi
  rows+=("| $label | $floor | $proved | $failed | $unknown | $rtc | $assumed | $mandated | $total | $verdict |")
done

say ""
say "== Summary (advisory lane; unknown rows are open obligations, never counted as proved) =="
say "| target | floor | proved | failed | unknown | runtime-checked | assumed | mandated | total | verdict |"
say "|---|---|---|---|---|---|---|---|---|---|"
for r in "${rows[@]}"; do say "$r"; done
say ""
if [ $regressed -ne 0 ]; then
  say "REGRESSED (exit 1): see the rows above. Logs and reports: $OUT/"
  exit 1
fi
say "OK (exit 0): every READY target has 0 failed rows and meets its proved floor."
exit 0
