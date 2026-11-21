.PHONY: toolchain build stock test gate render run ci fmt tippy doc verify-ready

# astream builds on the Trust toolchain, the lab's toolchain for Rust: `targo` is the
# build driver, `targo tippy` the linter, `targo fmt` the formatter. Every compiling
# verb names its lane — `--unverified` here (no proof claim); `targo trust ...` is
# the verified lane (scripts/verify-trust.sh). There is no stock fallback: the one
# stock step, `stock`, only checks that a stock rustc still compiles astream.

# `targo --unverified --version` is the one check that tells the real targo from
# upstream cargo installed under its name (cargo rejects the flag).
#
# Under `rustup run <toolchain> make ...` (the release gate, publish/config.sh) every
# bare `targo` below, and in the evidence claims, still resolves through PATH, which
# can reach a targo built at another commit than the toolchain rustup names. Refuse
# that split: the PATH targo must report the same version, commit included.
toolchain:
	@targo --unverified --version || { echo "make: targo (the Trust toolchain) is required; run \`aterm pkg doctor\`" >&2; exit 1; }
	@if [ -n "$${RUSTUP_TOOLCHAIN:-}" ]; then \
	  pinned=$$(rustup run "$$RUSTUP_TOOLCHAIN" targo --unverified --version) || { echo "make: RUSTUP_TOOLCHAIN=$$RUSTUP_TOOLCHAIN, but \`rustup run $$RUSTUP_TOOLCHAIN targo\` failed" >&2; exit 1; }; \
	  onpath=$$(targo --unverified --version); \
	  [ "$$onpath" = "$$pinned" ] || { echo "make: the targo on PATH ($$onpath) is not rustup's $$RUSTUP_TOOLCHAIN targo ($$pinned)" >&2; exit 1; }; \
	fi

build:
	targo --unverified build --locked --workspace

# STOCK EXCEPTION: aterm compiles astream with a stock rustc in its cross cells and its
# Linux lane, where no Clean island compiles (cfg(clean_islands) is Trust's alone), so code
# that only an island keeps alive breaks them, or warns there, while every Trust step stays
# green. This checks the workspace, all targets and both feature sets with rustup's stable for
# the host and the Linux, x86_64 macOS and Windows targets, warnings denied (aterm's cells
# judge them); COULD NOT RUN when no stock toolchain or target is installed, never a pass.
stock:
	scripts/stock-check.sh

# BOTH feature configurations, because neither is a superset of the other: default
# features skip every `#[cfg(feature = "...")]` test, and `--all-features` skips the
# `#[cfg(not(feature = "..."))]` fallbacks. Running both is the only arrangement under
# which no test is silently absent from the gate. astream-broker's `retention` is a
# DEFAULT feature, so its fallbacks are built by a third run without default features.
test:
	targo --unverified test --locked --workspace
	targo --unverified test --locked --workspace --all-features
	targo --unverified test --locked -p astream-broker --no-default-features

gate:
	targo --unverified run --quiet --locked -p astream-evidence -- gate

render:
	targo --unverified run --quiet --locked -p astream-evidence -- render --write

run:
	targo --unverified run --quiet --locked -p astream-evidence -- run

fmt:
	targo fmt --all -- --check

# Both feature configurations, as for `test`: the capability (`cap`) and sealed
# transport (`aead`) code is feature-gated and off by default, and the default build
# carries `cfg(not(feature))` fallbacks the all-features build never compiles.
tippy:
	targo tippy --locked --workspace --all-targets -- -D warnings
	targo tippy --locked --workspace --all-targets --all-features -- -D warnings
	targo tippy --locked -p astream-broker --all-targets --no-default-features -- -D warnings

# rustdoc with warnings denied (a broken intra-doc link is a doc that drifted
# from the code), in both feature configurations for the same reason as `test`: a
# link to a feature-gated item breaks the default build's docs.
doc:
	RUSTDOCFLAGS="-D warnings" targo --unverified doc --locked --workspace --no-deps
	RUSTDOCFLAGS="-D warnings" targo --unverified doc --locked --workspace --no-deps --all-features
	RUSTDOCFLAGS="-D warnings" targo --unverified doc --locked -p astream-broker --no-deps --no-default-features

# The full merge gate, on Trust but for `stock`, its one stock step; run it locally
# before pushing — there is no hosted CI. fmt, tippy (every feature) and rustdoc run
# with warnings denied, so a formatting, lint, or doc regression — including one in the
# feature-gated cap/aead security code — fails the gate, and a crate a stock rustc
# cannot compile fails `stock`.
ci: toolchain fmt build stock test gate tippy doc run

# The verified lane over the READY targets (0 failed Level-0 rows each): fails on any
# failed row or a proved count below its floor; unknown rows never count as proved.
# Advisory lane (`--allow-l0-gaps`), ~2 minutes; not part of `ci`. See the script.
verify-ready: toolchain
	scripts/verify-ready.sh
