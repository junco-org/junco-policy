#!/usr/bin/env bash
# Lists every trusted (unverified) declaration in the Verus crates as Markdown.
#
# Usage: scripts/trust-scan.sh [DIR...] > TRUST.md
# Default: crates/ and, if present, third_party/ (vendored verified dependencies) of the
# repository root. Explicit DIRs are relative to the current directory; the first path component
# below each DIR names the crate. Comments and string literals are ignored; `target/` directories
# are skipped. Exit status is 0 whether or not trusted items exist; the output is the inventory.
set -euo pipefail

if (($# == 0)); then
    cd "$(dirname "${BASH_SOURCE[0]}")/.."
    set -- crates
    [[ -d third_party ]] && set -- "$@" third_party
fi
command -v python3 >/dev/null || { echo "trust-scan: python3 required" >&2; exit 1; }

exec python3 - "$@" <<'PY'
import bisect
import os
import re
import sys
from collections import defaultdict

KINDS = [
    ("assume_specification",
     "a contract for an external (std/third-party) function that Verus assumes without proof"),
    ("external_fn_specification",
     "a contract for an external function, declared in the older attribute form; assumed"),
    ("external_body",
     "a function or type whose body Verus does not check; its signature contract is assumed"),
    ("external_type_specification",
     "makes an external type usable in verified code; `opaque` marks types whose fields are hidden"),
    ("external_trait_specification",
     "declares the specification of an external trait for verified code; its methods' contracts are assumed"),
    ("external",
     "an item Verus ignores entirely (`#[verifier::external]`); verified code cannot call it unless it has another spec"),
    ("admit",
     "`admit()`: closes a proof obligation without proof"),
    ("assume",
     "`assume(p)`: adds `p` as a fact without proof"),
    ("exec_allows_no_decreases_clause",
     "an executable function whose termination is not proved (its loops/recursion have no `decreases`)"),
]
KIND_NAMES = [k for k, _ in KINDS]

def strip_code(text):
    """Replace comments and string/char literal contents with spaces, keeping line structure."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j): depth += 1; j += 2
                elif text.startswith("*/", j): depth -= 1; j += 2
                else: j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j])); i = j
        elif c == "r" and re.match(r'r#*"', text[i:i + 10]) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            m = re.match(r'r(#*)"', text[i:])
            close = '"' + m.group(1)
            j = text.find(close, i + len(m.group(0)))
            j = n if j < 0 else j + len(close)
            out.append(re.sub(r"[^\n]", " ", text[i:j])); i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(re.sub(r"[^\n]", " ", text[i:j])); i = j
        elif c == "'":
            m = re.match(r"'(\\.|\\x[0-9a-fA-F]{2}|\\u\{[0-9a-fA-F]+\}|[^\\'\n])'", text[i:])
            if m:  # a char literal; otherwise a lifetime
                out.append(" " * len(m.group(0))); i += len(m.group(0))
            else:
                out.append(c); i += 1
        else:
            out.append(c); i += 1
    return "".join(out)

ATTR_KIND = re.compile(
    r"(?:verifier\s*::\s*|verus_verify\s*\(\s*|verifier\s*\(\s*)"
    r"(external_body|external_fn_specification|external_type_specification|"
    r"external_trait_specification|external_trait_extension|external|exec_allows_no_decreases_clause)\b"
)
CALL_KIND = re.compile(r"(?<![\w.:])(admit|assume)\s*\(")
ASSUME_SPEC = re.compile(r"\bassume_specification\b")

def describe(text):
    """A short name for the declaration starting at `text`."""
    t = re.sub(r"\s+", " ", text).strip()
    m = re.search(r"\bfn\s+(\w+)", t)
    if m and not re.match(r"(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+)?impl\b", t):
        return "fn " + m.group(1)
    m = re.search(r"\b(?:struct|enum|union|trait|type|mod|impl)\b.*", t)
    t = m.group(0) if m else t
    return re.split(r"\s*[{;]", t)[0][:110]

def bracket_end(code, i):
    """Offset just past the `]` matching the `[` at or after offset `i`."""
    depth = 0
    j = code.index("[", i)
    while j < len(code):
        if code[j] == "[": depth += 1
        elif code[j] == "]":
            depth -= 1
            if depth == 0: return j + 1
        j += 1
    return len(code)

def crate_of(top, path):
    top = os.path.normpath(top)
    return os.path.join(top, os.path.relpath(path, top).split(os.sep)[0])

def scan(top, path, raw, findings):
    code = strip_code(raw)
    src = raw.split("\n")
    newlines = [k for k, ch in enumerate(code) if ch == "\n"]
    line_of = lambda off: bisect.bisect_right(newlines, off - 1) + 1
    crate = crate_of(top, path)
    for m in ASSUME_SPEC.finditer(code):
        t = re.compile(r"\[\s*(.*?)\s*\]\s*\(", re.S).search(code, m.end())
        item = re.sub(r"\s+", " ", t.group(1)) if t else src[line_of(m.start()) - 1].strip()
        findings.append((crate, "assume_specification", path, line_of(m.start()), item))
    for m in CALL_KIND.finditer(code):
        line = line_of(m.start())
        findings.append((crate, m.group(1), path, line, src[line - 1].strip()[:110]))
    # One pass over items: attribute blocks and the `{`-nesting of their declarations.
    stack, seg_start, block, i, n = [], 0, [], 0, len(code)
    while i < n:
        if code.startswith("#![", i):
            i = bracket_end(code, i); continue
        if code.startswith("#[", i):
            j = bracket_end(code, i)
            block.append((code[i:j], i)); i = j; continue
        c = code[i]
        if c.isspace():
            i += 1; continue
        if block:
            attrs = {m.group(1) for a, _ in block for m in ATTR_KIND.finditer(a)}
            if attrs:
                line = min(line_of(off) for a, off in block if ATTR_KIND.search(a))
                item = describe(code[i:code.find("\n", i) if "\n" in code[i:] else n])
                owner = next((h for h in reversed(stack) if h), None)
                if owner and not item.startswith("impl"):
                    item = f"{owner} :: {item}"
                if "external_type_specification" in attrs:
                    note = " (opaque)" if "external_body" in attrs else ""
                    findings.append((crate, "external_type_specification", path, line, item + note))
                elif "external_trait_specification" in attrs:
                    note = " (with external_trait_extension)" if "external_trait_extension" in attrs else ""
                    findings.append((crate, "external_trait_specification", path, line, item + note))
                else:
                    findings.extend((crate, k, path, line, item) for k in KIND_NAMES if k in attrs)
            block = []
        if c == "{":
            header = re.sub(r"#!?\[.*?\]", " ", code[seg_start:i], flags=re.S)
            m = re.search(r"(?:^|[\s;])((?:unsafe\s+)?impl\b[^;]*)$", header, re.S)
            stack.append(describe(m.group(1)) if m else None)
            seg_start = i + 1
        elif c == "}":
            if stack: stack.pop()
            seg_start = i + 1
        elif c == ";":
            seg_start = i + 1
        i += 1

findings = []  # (crate, kind, path, line, item)
for top in sys.argv[1:]:
    for dirpath, dirnames, filenames in os.walk(top):
        dirnames[:] = sorted(d for d in dirnames if d not in ("target", ".git", "vendor"))
        for name in sorted(filenames):
            if name.endswith(".rs"):
                path = os.path.normpath(os.path.join(dirpath, name))
                with open(path, encoding="utf-8") as f:
                    scan(top, path, f.read(), findings)

crates = sorted({f[0] for f in findings} | {crate_of(t, os.path.join(t, d)) for t in sys.argv[1:]
                for d in (os.listdir(t) if os.path.isdir(t) else []) if os.path.isdir(os.path.join(t, d))})
count = defaultdict(int)
for c, k, *_ in findings:
    count[(c, k)] += 1
scanned = [os.path.normpath(t) for t in sys.argv[1:]]

print("# Trust inventory of the Verus proofs")
print()
print("Generated by `scripts/trust-scan.sh` (scanned: " + ", ".join(f"`{t}/`" for t in scanned)
      + "; `target/` skipped). Do not edit by hand; rerun the script.")
print()
print("Everything Verus checks is verified against its contract; the items below are the places")
print("where a contract or fact is *assumed*. Matches in comments and string literals are ignored.")
print("Counted kinds:")
print()
for k, d in KINDS:
    print(f"- `{k}`: {d}.")
print()
print("An `external_body` attribute on an external type specification makes that type opaque and")
print("is reported once, with the type. Not counted: `external_derive` (derived trait impls that")
print("Verus ignores), `opaque`/`rlimit`/`spinoff_prover` (proof-engineering controls), and the")
print("hypotheses of theorems (stated in each `requires`). Not scanned: `vstd`, Verus's standard")
print("library, which is part of the pinned toolchain.")
if "third_party" not in scanned:
    print("Also not scanned: the verified helper crates `verus-bumpalo` and `hashconsius`, which")
    print("`history-store` takes as pinned git dependencies; Verus verifies them as dependencies.")
print()
print("## Totals")
print()
print("| kind | " + " | ".join(f"`{os.path.basename(c)}`" for c in crates) + " | total |")
print("|---|" + "---:|" * (len(crates) + 1))
for k in KIND_NAMES:
    row = [count[(c, k)] for c in crates]
    print(f"| `{k}` | " + " | ".join(str(v) for v in row) + f" | {sum(row)} |")
tot = [sum(count[(c, k)] for k in KIND_NAMES) for c in crates]
print("| **total** | " + " | ".join(f"**{v}**" for v in tot) + f" | **{sum(tot)}** |")
print()
for c in crates:
    items = [f for f in findings if f[0] == c]
    print(f"## `{c}`")
    print()
    if not items:
        print("No trusted items.")
        print()
        continue
    for k in KIND_NAMES:
        ks = sorted((f for f in items if f[1] == k), key=lambda f: (f[2], f[3]))
        if not ks:
            continue
        print(f"### `{k}` ({len(ks)})")
        print()
        for _, _, path, line, item in ks:
            print(f"- `{path}:{line}`: `{item}`")
        print()
PY
