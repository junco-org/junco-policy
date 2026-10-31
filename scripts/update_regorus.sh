#!/usr/bin/env bash
# Mirror the four shared library crates into the sibling Regorus checkout, then run its full
# Verus proof gate and history benchmarks. Overwrites everything inside the mapped crates.
set -euo pipefail

if (($#)); then
    echo "usage: scripts/update_regorus.sh" >&2
    exit 2
fi

fail() {
    echo "update_regorus: $*" >&2
    exit 1
}

src_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
dest_root="$(dirname -- "$src_root")/regorus"
crates=(history-syntax junco-core history-store history-semantics)

# Validate every boundary before the first write so a bad later mapping cannot leave a partial copy.
[[ -L $dest_root ]] && fail "refusing symlinked Regorus root: $dest_root"
[[ -d $dest_root ]] || fail "missing Regorus checkout: $dest_root"
[[ -L $dest_root/src ]] && fail "refusing symlinked Regorus source directory: $dest_root/src"
[[ -d $dest_root/src ]] || fail "missing Regorus source directory: $dest_root/src"
[[ -f $dest_root/Cargo.toml ]] || fail "missing Regorus manifest: $dest_root/Cargo.toml"
awk '/^\[/ { pkg = ($0 == "[package]") }
     pkg && /^name[[:space:]]*=[[:space:]]*"regorus"[[:space:]]*$/ { found = 1 }
     END { exit !found }' "$dest_root/Cargo.toml" ||
    fail "not a regorus package manifest: $dest_root/Cargo.toml"
for crate in "${crates[@]}"; do
    for dir in "$src_root/crates/$crate" "$dest_root/src/$crate"; do
        [[ -L $dir ]] && fail "refusing symlinked crate directory: $dir"
        [[ -d $dir ]] || fail "missing crate directory: $dir"
        [[ -f $dir/Cargo.toml && ! -L $dir/Cargo.toml ]] || fail "missing crate manifest: $dir/Cargo.toml"
    done
done

for tool in rsync cargo rustup verus cargo-verus; do
    command -v "$tool" >/dev/null || fail "required tool not on PATH: $tool"
done
export RUSTUP_TOOLCHAIN=1.98.1
rustup run 1.98.1 rustc --version
verus --version
cargo verus --help >/dev/null
"${VERUS_Z3_PATH:-z3}" --version

run() {
    printf '\n==> %s\n' "$*"
    "$@"
}

for crate in "${crates[@]}"; do
    run rsync -a --checksum --delete \
        --exclude=.git/ --exclude=/target/ --exclude=.verus-solver-log/ --exclude=Cargo.lock \
        "$src_root/crates/$crate/" "$dest_root/src/$crate/"
done

cd -- "$dest_root"
# Unlocked once so Regorus's own lockfile absorbs copied manifest changes; everything after is locked.
run cargo fetch

run cargo verus verify --locked -p history-syntax --no-default-features
run cargo verus verify --locked -p history-syntax --features serde,std
run cargo verus verify --locked -p junco-core --no-default-features
run cargo verus verify --locked -p junco-core --features runtime,std,serde
run cargo verus verify --locked -p history-store --no-default-features --features runtime
run cargo verus verify --locked -p history-store --features runtime,std
run cargo verus verify --locked -p history-semantics --no-default-features --features runtime
run cargo verus verify --locked -p history-semantics --features runtime,std,cache
run cargo verus verify --locked
run cargo verus verify --locked --features history
run cargo verus verify --locked --no-default-features --features history,arc,std

run cargo bench --locked --bench history_table --features history -- --save-baseline history-cached
run cargo bench --locked --bench history_table --no-default-features --features history,arc,std \
    -- --save-baseline history-uncached

printf '\n==> Regorus updated, verified and benchmarked: %s\n' "$dest_root"
