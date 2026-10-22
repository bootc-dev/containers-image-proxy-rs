# Build everything
build:
    cargo build --all-targets --all-features

# Run all tests using nextest
test:
    #!/bin/bash
    set -euo pipefail
    if command -v cargo-nextest &>/dev/null; then
        cargo nextest run --all-features
    else
        cargo test --all-targets --all-features
    fi
    # https://github.com/rust-lang/cargo/issues/6669
    cargo test --doc --all-features

# Check formatting
fmt-check:
    cargo fmt -- --check -l

# Run clippy
clippy:
    cargo clippy --all-targets --all-features -- -D warnings

# Full lint check (formatting + clippy), mirrors CI
lint: fmt-check clippy

# Run semver checks against the last published version
semver-check:
    cargo semver-checks

# Lint and test (used by CI, and for local development)
ci: lint test
