# set global cargo args
cargo_args := "--workspace --quiet"

# extract minimal supported Rust version from Cargo.toml
msrv := `grep -m1 rust-version Cargo.toml | sed 's/^rust-version\s*=\s*"\(.\+\)"$/\1/'`

[default]
all: check-all test audit-all

[private]
@cargo name args:
    tput sc; echo -n "{{BOLD}}{{name}}...{{NORMAL}}"
    cargo {{args}} &>/dev/null \
        && (tput rc; echo "{{BOLD}}{{name}} {{NORMAL+GREEN}}ok{{NORMAL}}") \
        || (tput rc; echo "{{BOLD}}{{name}} {{NORMAL+RED}}fail{{NORMAL}}")
    tput ed

[private]
cargo_check version description *args: \
    (cargo "check " + version + " (" + description + ")" \
        "+" + version + " check " + cargo_args + " " + args)

check-all: fmt clippy check check-msrv check-windows

fmt: \
    (cargo "check fmt" "fmt --check")

clippy: \
    (cargo "check clippy" "clippy " + cargo_args)

check: \
    (cargo_check "stable" "default features") \
    (cargo_check "stable" "all features" "--all-features") \
    (cargo_check "stable" "no default features" "--no-default-features")

check-msrv: \
    (cargo_check msrv "default features") \
    (cargo_check msrv "all features" "--all-features") \
    (cargo_check msrv "no default features" "--no-default-features")

check-windows: \
    (cargo_check "stable" "default features, windows" "--target=x86_64-pc-windows-msvc") \

test: \
    (cargo "tests" "test --workspace")

audit-all: audit deny vet

audit: \
    (cargo "check audit" "audit -q")

deny: \
    (cargo "check deny" "deny check")

vet: \
    (cargo "check vet" "vet check")
