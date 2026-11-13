#!/usr/bin/env bash
# Builds the anonymized supplementary-material tarball of this repository.
#
# Usage: scripts/make-supplement.sh [--check] [OUT]
#   OUT      tarball path, relative to the repository root
#            (default: ../pldi2027-supplement/junco-proofs.tar.gz)
#   --check  also run `cargo check --locked --workspace` in the staged tree
#
# Stages the working tree (tracked and untracked, non-ignored files), drops internal notes and
# maintenance scripts, vendors the two git dependencies into third_party/, strips copyright
# headers and identifying manifest fields, regenerates TRUST.md, and refuses to write the
# tarball while any identifying string remains outside the justified allow-list below.
# This script itself is not shipped: it names the strings it scans for.
set -euo pipefail

check=0
out=
while (($#)); do
    case $1 in
        --check) check=1; shift ;;
        -h|--help) sed -n '2,13p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
        -*) echo "make-supplement: unknown option $1" >&2; exit 2 ;;
        *) [[ -z $out ]] || { echo "make-supplement: one OUT only" >&2; exit 2; }; out=$1; shift ;;
    esac
done

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$root"
out="${out:-../pldi2027-supplement/junco-proofs.tar.gz}"
[[ $out == /* ]] || out="$root/$out"
for tool in git cargo python3 tar gzip; do
    command -v "$tool" >/dev/null || { echo "make-supplement: $tool required" >&2; exit 1; }
done

work="$(mktemp -d)"
trap 'rm -rf -- "$work"' EXIT
name=junco-proofs
stage="$work/$name"
mkdir -p "$stage"

# --- 1. Copy the working tree, minus internal material. --------------------------------------
# docs/history/: internal working notes (absolute paths, tool and agent names); docs/verification/INTERFACES.md stays.
# scripts/*update_regorus*: maintenance scripts for mirroring into a downstream project.
# scripts/make-supplement.sh: this script (it lists the identifying strings).
excluded='^(docs/history/|STATUS\.md$|scripts/update_regorus\.sh$|scripts/test_update_regorus\.sh$|scripts/make-supplement\.sh$)'
git ls-files -co --exclude-standard -z | while IFS= read -r -d '' f; do
    [[ $f =~ $excluded ]] && continue
    [[ -e $f || -L $f ]] || continue  # deleted but still tracked
    mkdir -p "$stage/$(dirname "$f")"
    cp -P -- "$f" "$stage/$f"
done

# --- 2. Vendor the git dependencies (hosted under an author's account). ----------------------
cargo fetch --locked --quiet
cargo metadata --locked --format-version 1 >"$work/metadata.json"

python3 - "$stage" "$work/metadata.json" <<'PY'
import json, os, re, shutil, sys

stage, metadata = sys.argv[1], sys.argv[2]
vendored = {"verus-bumpalo": "verus-bumpalo", "hashconsius": "hashconsius"}
packages = {p["name"]: p for p in json.load(open(metadata))["packages"]}

def rewrite(path, fn):
    with open(path, encoding="utf-8") as f:
        text = f.read()
    new = fn(text)
    with open(path, "w", encoding="utf-8") as f:
        f.write(new)

def to_path(text, rel_of):
    """Replace `name = { git = "...", rev = "..." ...}` by a path dependency for vendored crates."""
    for name in vendored:
        pat = re.compile(r'(?m)^(%s\s*=\s*\{\s*)git\s*=\s*"[^"]*"\s*,\s*rev\s*=\s*"[^"]*"' % re.escape(name))
        text = pat.sub(lambda m: m.group(1) + 'path = "%s"' % rel_of(name), text)
    return text

def library_only(text):
    """Drop dev-dependencies, benches and tests: as path dependencies Cargo would resolve their
    dev-dependencies into Cargo.lock, which git dependencies do not."""
    return re.sub(r"(?ms)^\[(dev-dependencies|\[bench\]|\[test\])\]\n.*?(?=^\[|\Z)", "", text)

for name, dest in vendored.items():
    pkg = packages.get(name)
    if pkg is None or not (pkg.get("source") or "").startswith("git+"):
        sys.exit(f"make-supplement: {name} is not a git dependency in cargo metadata")
    src = os.path.dirname(pkg["manifest_path"])
    target = os.path.join(stage, "third_party", dest)
    shutil.copytree(src, target, ignore=shutil.ignore_patterns(
        ".git", ".cargo-ok", "Cargo.lock", "rust-toolchain.toml", "target", ".gitignore", "benches", "tests"))
    rewrite(os.path.join(target, "Cargo.toml"),
            lambda t, dest=dest: library_only(to_path(t, lambda n: "../" + vendored[n])))

rewrite(os.path.join(stage, "crates/history-store/Cargo.toml"),
        lambda t: to_path(t, lambda n: "../../third_party/" + vendored[n]))

# Path dependencies have no `source` in Cargo.lock; nothing else in the lock changes.
for lock in ("Cargo.lock", "fuzz/Cargo.lock"):
    p = os.path.join(stage, lock)
    if os.path.exists(p):
        rewrite(p, lambda t: re.sub(r'(?m)^source = "git\+[^"]*"\n', "", t))

# Keep the vendored crates out of the root workspace, as git dependencies were.
def exclude_third_party(t):
    new, n = re.subn(r'(?m)^exclude = \[([^\]]*)\]', lambda m: 'exclude = [%s, "third_party"]' % m.group(1), t, count=1)
    if n != 1:
        sys.exit("make-supplement: no workspace exclude list in Cargo.toml")
    return new
rewrite(os.path.join(stage, "Cargo.toml"), exclude_third_party)
PY

# --- 3. Scrub identifying text. ----------------------------------------------------------------
python3 - "$stage" <<'PY'
import os, re, sys

stage = sys.argv[1]
report = []

def text_files():
    for dirpath, dirnames, filenames in os.walk(stage):
        for n in filenames:
            p = os.path.join(dirpath, n)
            if os.path.islink(p):
                continue
            try:
                with open(p, encoding="utf-8") as f:
                    yield p, f.read()
            except (UnicodeDecodeError, OSError):
                continue

def write(p, t):
    with open(p, "w", encoding="utf-8") as f:
        f.write(t)

third_party_data = re.compile(r"^(benches/|fuzz/benches/)")
for p, t in text_files():
    rel = os.path.relpath(p, stage)
    new = t
    # Copyright header lines naming the employer.
    new = re.sub(r"(?m)^[ \t]*(//+|#|\*)[ \t]*Copyright \(c\) Microsoft Corporation\.?[^\n]*\n", "", new)
    # Identifying manifest fields.
    if os.path.basename(p) == "Cargo.toml":
        new = re.sub(r'(?ms)^(authors|repository|homepage)\s*=\s*(\[.*?\]|"[^"\n]*")[ \t]*\n', "", new)
    # Our own LICENSE files (third-party benchmark data keeps its licenses).
    if os.path.basename(p).upper().startswith("LICENSE") and not third_party_data.match(rel):
        new = re.sub(r"(?mi)^(\s*Copyright\s*(\(c\)|©)?\s*(\d{4}([-–]\d{4})?)?,?\s*)(.+)$",
                     lambda m: m.group(1) + "Anonymous authors", new)
    # The vendored allocator's README uses its repository name; use the crate name instead.
    if rel.startswith("third_party/"):
        new = re.sub(r"(?i)\bbumpus\b", "verus-bumpalo", new)
    if new != t:
        write(p, new)
        report.append(rel)

# README: the downstream-integration section, hosting details, and an internal revision.
readme = os.path.join(stage, "README.md")
with open(readme, encoding="utf-8") as f:
    t = f.read()
steps = [
    (r"(?ms)^## Regorus integration\n.*?(?=^## |\Z)", ""),
    (r"Verified helper dependencies are pinned to\s*\[bumpus\]\([^)]*\) \(`verus-bumpalo`\) commit\s*`[0-9a-f]+` and\s*\[hashconsius\]\([^)]*\) commit\s*`[0-9a-f]+`\.",
     "The verified helper dependencies `verus-bumpalo` and `hashconsius` are vendored in\n`third_party/`."),
    (r"on an Azure development host", "on a cloud development host"),
    (r"against `origin/main` at `[0-9a-f]+`", "against an earlier revision"),
    (r"\A(# [^\n]*\n)", r"\1\nTo check the proofs, see [VERIFY.md](VERIFY.md); [TRUST.md](TRUST.md) lists the trusted\nitems.\n"),
]
for pat, rep in steps:
    t, n = re.subn(pat, rep, t, count=1)
    if n != 1:
        sys.exit(f"make-supplement: README scrub pattern not found: {pat[:60]}")
t = t.rstrip("\n") + "\n"
write(readme, t)
report.append("README.md")
print("scrubbed: " + ", ".join(sorted(set(report))))
PY

# --- 4. Regenerate the trust inventory over the shipped crates and vendored dependencies. ----
(cd "$stage" && bash scripts/trust-scan.sh >TRUST.md)

# --- 5. Scan for identifying strings. ------------------------------------------------------------
# The pattern: employer, institution, author names and handles, local paths, GitHub accounts,
# the downstream project, the hosting provider, and names and revisions of author-hosted
# repositories.
pattern='microsoft|cmu\.edu|ioannidis|zkent|t-zakkent|zak kent|lef |/home/|/tmp/|github\.com/[a-z]|regorus|azure|elefthei|bumpus|888a6983|d7c17483|684911c'
python3 - "$stage" "$pattern" <<'PY'
import fnmatch, os, re, sys

stage, pattern = sys.argv[1], re.compile(sys.argv[2], re.I)
# (path glob, allowed text, justification). A hit is allowed only if removing every allowed
# text that applies to its file leaves no match on the line.
ALLOW = [
    ("*", r"https://github\.com/rust-lang/crates\.io-index",
     "crates.io registry index URL in Cargo.lock files (Rust infrastructure)"),
    ("*", r"https://github\.com/verus-lang/[\w./%-]*",
     "Verus and verus-spec-check releases: the public, third-party toolchain"),
    ("*", r"https://github\.com/Z3Prover/[\w./%-]*",
     "Z3 release: the public, third-party solver"),
    ("benches/resharp/data/*", r".*",
     "vendored third-party benchmark corpora (subtitles, Rust sources) of the RE# benchmark"),
    ("benches/resharp/README.md", r"https://github\.com/ieviev/resharp[^)\s]*",
     "attribution of the third-party RE# benchmark sources"),
    ("benches/smt/README.md", r"https://github\.com/cdstanford/regex-smt-benchmarks|/tmp/regex-smt-benchmarks",
     "attribution of the third-party regex SMT benchmarks; a scratch clone path in instructions"),
    ("fuzz/benches/dogwood/*", r"https://github\.com/dogwood-policy/dogwood[^)\s]*",
     "attribution of the third-party Dogwood benchmark"),
    ("fuzz/examples/replay_curve.rs", r"/tmp/junco-profile",
     "scratch output directory of a profiling example (generic, not a local path)"),
]
offending, allowed = [], {}
for dirpath, dirnames, filenames in os.walk(stage):
    for n in filenames:
        p = os.path.join(dirpath, n)
        rel = os.path.relpath(p, stage)
        try:
            lines = open(p, encoding="utf-8", errors="replace").read().split("\n")
        except OSError:
            continue
        hits = [(i + 1, l) for i, l in enumerate(lines) if pattern.search(l)]
        if pattern.search(rel):
            offending.append(f"{rel}: (file name)")
        for no, line in hits:
            rest, used = line, []
            for glob, text, why in ALLOW:
                if fnmatch.fnmatch(rel, glob) and re.search(text, rest):
                    rest = re.sub(text, "", rest)
                    used.append(why)
            if pattern.search(rest):
                offending.append(f"{rel}:{no}: {line.strip()[:200]}")
            else:
                for why in used:
                    allowed.setdefault(why, set()).add(rel)
for why, files in allowed.items():
    shown = sorted(files)
    more = f" and {len(shown) - 3} more" if len(shown) > 3 else ""
    print(f"allowed: {why}: {', '.join(shown[:3])}{more}")
if offending:
    print("make-supplement: identifying strings remain:", file=sys.stderr)
    for o in offending:
        print("  " + o, file=sys.stderr)
    sys.exit(1)
print("scan: clean")
PY

# --- 6. Optionally check that the staged tree builds. ------------------------------------------
if ((check)); then
    (cd "$stage" && RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-1.98.1}" CARGO_TARGET_DIR="$work/target" \
        cargo check --locked --workspace --quiet)
    echo "cargo check --locked --workspace: ok"
fi

# --- 7. Write the tarball with neutral ownership and timestamps. -------------------------------
mkdir -p "$(dirname "$out")"
out="$(cd "$(dirname "$out")" && pwd -P)/$(basename "$out")"
tar -C "$work" --sort=name --owner=0 --group=0 --numeric-owner --mtime='2026-01-01 00:00:00Z' \
    -cf - "$name" | gzip -n -9 >"$out.part"
mv "$out.part" "$out"
echo "wrote $out ($(du -h "$out" | cut -f1), $(tar -tzf "$out" | grep -vc '/$') files)"
