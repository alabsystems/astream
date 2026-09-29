.PHONY: build test gate render run ci fmt clippy doc

build:
	cargo build --locked --workspace

# BOTH feature configurations, because neither is a superset of the other: default
# features skip every `#[cfg(feature = "...")]` test, and `--all-features` skips the
# `#[cfg(not(feature = "..."))]` fallbacks. Running both is the only arrangement under
# which no test is silently absent from the gate.
test:
	cargo test --locked --workspace
	cargo test --locked --workspace --all-features

gate:
	cargo run --quiet --locked -p astream-evidence -- gate

render:
	cargo run --quiet --locked -p astream-evidence -- render --write

run:
	cargo run --quiet --locked -p astream-evidence -- run

fmt:
	cargo fmt --all -- --check

# Both feature configurations, as for `test`: the capability (`cap`) and sealed
# transport (`aead`) code is feature-gated and off by default, and the default build
# carries `cfg(not(feature))` fallbacks the all-features build never compiles.
clippy:
	cargo clippy --locked --workspace --all-targets -- -D warnings
	cargo clippy --locked --workspace --all-targets --all-features -- -D warnings

# rustdoc with warnings denied (a broken intra-doc link is a doc that drifted
# from the code), in both feature configurations for the same reason as `test`: a
# link to a feature-gated item breaks the default build's docs.
doc:
	RUSTDOCFLAGS="-D warnings" cargo doc --locked --workspace --no-deps
	RUSTDOCFLAGS="-D warnings" cargo doc --locked --workspace --no-deps --all-features

# The full merge gate. The hosted workflow (.github/workflows/ci.yml, development tree only) runs exactly
# this target on Linux; run it locally before pushing. fmt, clippy (every feature)
# and rustdoc run with warnings denied, so a formatting, lint, or doc regression —
# including one in the feature-gated cap/aead security code — fails the gate.
ci: fmt build test gate clippy doc run
