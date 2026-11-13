#!/usr/bin/env bash
# Reproduces the `verify-core` CI job (.github/workflows/ci.yml) locally: checks the pinned
# toolchain, runs thirteen `cargo verus verify` configurations, and prints a summary table.
#
# Usage: scripts/verify-all.sh [--list] [--download DIR] [--jobs N] [--target-root DIR]
#                              [--only PATTERN...] [-- VERUS_ARGS...]
#   --list             check the toolchain and print selected commands; verify nothing
#   --download DIR     fetch the pinned, sha256-checked Verus and Z3 releases into DIR
#   --jobs N           run up to N configurations concurrently (default: 1)
#   --target-root DIR  keep a separate persistent Cargo target directory per configuration
#   --only PATTERN...  select configurations containing any supplied argument-string pattern
#   -- ARGS            extra Verus arguments; concurrent jobs should divide the available cores
#
# Toolchain lookup: Verus from $VERUS_DIST (an unpacked release directory) or from `verus` and
# `cargo-verus` on PATH; Z3 from $VERUS_Z3_PATH or `z3` on PATH; Rust via rustup.
set -euo pipefail

verus_version=0.2026.10.04.426d8b0
z3_version=4.16.0
rust_toolchain=1.98.1-x86_64-unknown-linux-gnu
# Pinned release assets, identical to ci.yml.
verus_url=https://github.com/verus-lang/verus/releases/download/release%2F0.2026.10.04.426d8b0/verus-0.2026.10.04.426d8b0-x86-linux.zip
verus_sha256=624018662868563a7bec0dd07be5e4dd0c3d61124b4b55105765884bf2d4d1a0
z3_url=https://github.com/Z3Prover/z3/releases/download/z3-4.16.0/z3-4.16.0-x64-glibc-2.39.zip
z3_sha256=7288c49a5bd6dbafd7b0b0d1f65956b91672da24b08f09242919af159be3418e

# The original eleven CI configurations, followed by the two public reviewer clients.
configs=(
    "-p history-syntax --no-default-features"
    "-p history-syntax --features serde,std"
    "-p junco-core --no-default-features"
    "-p junco-core --features runtime,std,serde"
    "-p history-store --no-default-features --features runtime"
    "-p history-store --features runtime,std"
    "-p history-semantics --no-default-features --features runtime"
    "-p history-semantics --features runtime,std,cache"
    "-p history-semantics --features runtime,std,cache --test public_specs"
    "-p history-analysis --no-default-features --features runtime"
    "-p history-analysis --no-default-features --features runtime,std"
    "-p history-semantics --features runtime,std,cache --test reviewer"
    "-p history-analysis --no-default-features --features runtime,std --test reviewer"
)

usage() { sed -n '2,15p' "$0" | sed 's/^# \{0,1\}//'; }
fail() { echo "verify-all: $*" >&2; exit 1; }

list_only=0
download_dir=
verus_args=()
jobs=1
target_root=
only_patterns=()
while (($#)); do
    case $1 in
        --list) list_only=1; shift ;;
        --download)
            (($# >= 2)) || fail "--download needs a directory"
            download_dir=$2; shift 2 ;;
        --jobs)
            (($# >= 2)) || fail "--jobs needs a positive integer"
            [[ $2 =~ ^[1-9][0-9]*$ ]] || fail "--jobs needs a positive integer"
            jobs=$2
            ((jobs > 0)) || fail "--jobs needs a positive integer"
            shift 2 ;;
        --target-root)
            (($# >= 2)) && [[ -n $2 ]] || fail "--target-root needs a directory"
            target_root=$2; shift 2 ;;
        --only)
            shift
            before=${#only_patterns[@]}
            while (($#)) && [[ $1 != --* && $1 != -h ]]; do
                only_patterns+=("$1")
                shift
            done
            ((${#only_patterns[@]} > before)) || fail "--only needs at least one pattern"
            ;;
        --) shift; verus_args=("$@"); break ;;
        -h|--help) usage; exit 0 ;;
        *) usage >&2; exit 2 ;;
    esac
done

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$root"

selected=()
for i in "${!configs[@]}"; do
    if ((${#only_patterns[@]} == 0)); then
        selected+=("$i")
    else
        for pattern in "${only_patterns[@]}"; do
            if [[ ${configs[$i]} == *"$pattern"* ]]; then
                selected+=("$i")
                break
            fi
        done
    fi
done
((${#selected[@]})) || fail "--only matched no configurations"

if ((jobs > 1)) && [[ -z $target_root ]]; then
    target_root="${CARGO_TARGET_DIR:-$root/target}/verify-all"
fi
if [[ -n $target_root ]]; then
    mkdir -p "$target_root"
    target_root="$(cd "$target_root" && pwd -P)"
fi

target_of() {
    local name=${1//[^a-zA-Z0-9]/_}
    printf '%s/%s' "$target_root" "$name"
}

# Fetches URL into DIR/NAME unless a copy with the expected sha256 is already there.
fetch() {
    local url=$1 sum=$2 out=$3
    if [[ -f $out ]] && echo "$sum  $out" | sha256sum --check --strict --status; then
        return
    fi
    curl -fsSL "$url" -o "$out.part"
    echo "$sum  $out.part" | sha256sum --check --strict --quiet || fail "sha256 mismatch for $url"
    mv "$out.part" "$out"
}

if [[ -n $download_dir ]]; then
    for tool in curl sha256sum unzip; do
        command -v "$tool" >/dev/null || fail "--download needs $tool on PATH"
    done
    mkdir -p "$download_dir"
    download_dir="$(cd "$download_dir" && pwd -P)"
    fetch "$verus_url" "$verus_sha256" "$download_dir/verus.zip"
    fetch "$z3_url" "$z3_sha256" "$download_dir/z3.zip"
    rm -rf "$download_dir/verus-dist" "$download_dir/z3"
    unzip -q "$download_dir/verus.zip" -d "$download_dir/verus-dist"
    unzip -q "$download_dir/z3.zip" -d "$download_dir/z3"
    VERUS_DIST="$download_dir/verus-dist"
    VERUS_Z3_PATH="$(find "$download_dir/z3" -type f -name z3 -perm -u+x | head -n1)"
    [[ -n $VERUS_Z3_PATH ]] || fail "no z3 binary in $z3_url"
fi

# --- Verus -------------------------------------------------------------------------------------
if [[ -n ${VERUS_DIST:-} ]]; then
    [[ -d $VERUS_DIST ]] || fail "VERUS_DIST is not a directory: $VERUS_DIST"
    verus_bin="$(find "$VERUS_DIST" -type f -name verus -perm -u+x | head -n1)"
    cargo_verus_bin="$(find "$VERUS_DIST" -type f -name cargo-verus -perm -u+x | head -n1)"
    [[ -n $verus_bin ]] || fail "no executable verus under VERUS_DIST=$VERUS_DIST"
    [[ -n $cargo_verus_bin ]] || fail "no executable cargo-verus under VERUS_DIST=$VERUS_DIST"
else
    verus_bin="$(command -v verus)" || fail "verus not on PATH; set VERUS_DIST or use --download DIR"
    cargo_verus_bin="$(command -v cargo-verus)" || fail "cargo-verus not on PATH; set VERUS_DIST or use --download DIR"
fi
version_json="$(dirname "$verus_bin")/version.json"
[[ -f $version_json ]] || fail "missing $version_json next to $verus_bin"
json_field() { sed -n "s/^ *\"$1\": *\"\([^\"]*\)\".*/\1/p" "$version_json" | head -n1; }
found_version="$(json_field version)"
[[ $found_version == "$verus_version" ]] || fail "Verus $found_version found, $verus_version required ($version_json)"
found_toolchain="$(json_field toolchain)"
found_toolchain="${found_toolchain%% *}"
[[ $found_toolchain == "$rust_toolchain" ]] ||
    fail "this Verus expects Rust toolchain '$found_toolchain', $rust_toolchain required"
export PATH="$(dirname "$cargo_verus_bin"):$(dirname "$verus_bin"):$PATH"

# --- Z3 ----------------------------------------------------------------------------------------
if [[ -z ${VERUS_Z3_PATH:-} ]]; then
    VERUS_Z3_PATH="$(command -v z3)" || fail "set VERUS_Z3_PATH to a Z3 $z3_version binary or put z3 on PATH"
fi
[[ -x $VERUS_Z3_PATH ]] || fail "VERUS_Z3_PATH is not executable: $VERUS_Z3_PATH"
z3_banner="$("$VERUS_Z3_PATH" --version)"
[[ $z3_banner == "Z3 version $z3_version "* ]] || fail "Z3 $z3_version required, found: $z3_banner"
export VERUS_Z3_PATH

# --- Rust --------------------------------------------------------------------------------------
command -v rustup >/dev/null || fail "rustup not on PATH"
export RUSTUP_TOOLCHAIN="$rust_toolchain"
rustc_banner="$(rustup run "$rust_toolchain" rustc --version 2>/dev/null)" ||
    fail "Rust $rust_toolchain missing; install it with: rustup toolchain install $rust_toolchain --profile minimal --component rustc-dev --component llvm-tools --component rustfmt"

echo "Verus:  $found_version ($verus_bin)"
echo "Z3:     ${z3_banner} ($VERUS_Z3_PATH)"
echo "Rust:   $rustc_banner (RUSTUP_TOOLCHAIN=$RUSTUP_TOOLCHAIN)"
echo

command_of() {
    local cmd="cargo verus verify --locked $1"
    ((${#verus_args[@]})) && cmd+=" -- ${verus_args[*]}"
    if [[ -n $target_root ]]; then
        cmd="CARGO_TARGET_DIR=$(printf '%q' "$(target_of "$1")") $cmd"
    fi
    printf '%s' "$cmd"
}

if ((list_only)); then
    echo "cargo fetch --locked"
    for i in "${selected[@]}"; do command_of "${configs[$i]}"; echo; done
    exit 0
fi

cargo fetch --locked

logs="$(mktemp -d)"
pids=()
cleanup() {
    local pid
    for pid in "${pids[@]}"; do kill "$pid" 2>/dev/null || true; done
    rm -rf -- "$logs"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
results=()
failed=0

run_config() {
    local i=$1
    local -a args
    read -r -a args <<<"${configs[$i]}"
    if [[ -n $target_root ]]; then
        export CARGO_TARGET_DIR
        CARGO_TARGET_DIR="$(target_of "${configs[$i]}")"
    fi
    if ((${#verus_args[@]})); then
        cargo verus verify --locked "${args[@]}" -- "${verus_args[@]}"
    else
        cargo verus verify --locked "${args[@]}"
    fi
}

record_result() {
    local i=$1 status=$2 counts verified=- errors=0 verdict
    # The target package is checked last; sum errors from its dependencies as well.
    counts="$(sed -n 's/.*verification results:: \([0-9]*\) verified, \([0-9]*\) errors.*/\1 \2/p' "$logs/$i.log")"
    if [[ -n $counts ]]; then
        verified="$(tail -n1 <<<"$counts" | cut -d' ' -f1)"
        errors="$(awk '{ s += $2 } END { print s }' <<<"$counts")"
    fi
    if ((status != 0 || errors != 0)); then
        failed=1
        verdict="FAIL (exit $status)"
    elif [[ -z $counts ]]; then
        verdict="pass (cached; counts not emitted)"
    else
        verdict=pass
    fi
    results[$i]="${configs[$i]}|$verified|$errors|$verdict"
}

if ((jobs == 1)); then
    # Preserve the default live output and shared Cargo target/cache behavior.
    for i in "${selected[@]}"; do
        printf '\n==> %s\n' "$(command_of "${configs[$i]}")"
        status=0
        run_config "$i" 2>&1 | tee "$logs/$i.log" || status=$?
        record_result "$i" "$status"
    done
else
    next=0
    running=0
    while ((next < ${#selected[@]} || running > 0)); do
        while ((next < ${#selected[@]} && running < jobs)); do
            i=${selected[$next]}
            printf '\n==> Starting %s\n' "$(command_of "${configs[$i]}")"
            (
                status=0
                run_config "$i" >"$logs/$i.log" 2>&1 || status=$?
                printf '%s\n' "$status" >"$logs/$i.status"
                exit "$status"
            ) &
            pids[$i]=$!
            next=$((next + 1))
            running=$((running + 1))
        done
        # Refill on completion, not by launch order. Bash 5.0 lacks wait -n -p.
        wait -n || true
        for i in "${!pids[@]}"; do
            if [[ -f $logs/$i.status ]]; then
                read -r status <"$logs/$i.status"
            elif kill -0 "${pids[$i]}" 2>/dev/null; then
                continue
            else
                status=0
                wait "${pids[$i]}" || status=$?
            fi
            wait "${pids[$i]}" 2>/dev/null || true
            printf '\n==> Completed %s\n' "$(command_of "${configs[$i]}")"
            cat "$logs/$i.log"
            record_result "$i" "$status"
            unset 'pids[i]'
            running=$((running - 1))
        done
    done
fi

printf '\n| %s | %s | %s | %s |\n|---|---:|---:|---|\n' "cargo verus verify --locked ..." verified errors result
for i in "${selected[@]}"; do
    IFS='|' read -r config verified errors verdict <<<"${results[$i]}"
    printf '| `%s` | %s | %s | %s |\n' "$config" "$verified" "$errors" "$verdict"
done
if ((failed)); then
    echo "verify-all: at least one configuration failed" >&2
    exit 1
fi
echo "All ${#selected[@]} configurations verified."
