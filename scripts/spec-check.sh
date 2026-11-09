#!/usr/bin/env bash
# Tests the assumed specifications of the verified crates against the real implementations
# (spec-check/src/lib.rs). Fetches the verus-spec-check release paired with the pinned Verus
# binary into spec-check/vendor/ on first use; extra arguments go to `cargo test`.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
tag="verus-2026-10-04"
vendor="$root/spec-check/vendor/verus-spec-check"

if [ ! -d "$vendor" ]; then
    git clone --quiet --depth 1 --branch "$tag" https://github.com/verus-lang/verus-spec-check "$vendor"
fi
if [ "$(git -C "$vendor" describe --tags --exact-match 2>/dev/null)" != "$tag" ]; then
    echo "spec-check/vendor/verus-spec-check is not at $tag; remove it to refetch" >&2
    exit 1
fi

cd "$root/spec-check"
exec cargo test --locked "$@"
