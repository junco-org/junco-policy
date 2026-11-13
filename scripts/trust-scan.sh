#!/usr/bin/env bash
# Lists every trusted (unverified) declaration in the Verus crates as Markdown.
#
# Usage: scripts/trust-scan.sh [DIR...] > TRUST.md
# Default: crates/ and, if present, third_party/ (vendored verified dependencies) of the
# repository root. Explicit DIRs are relative to the current directory; the first path component
# below each DIR names the crate. Comments and string literals are ignored; `target/` directories
# are skipped. The verified helper crates `verus-bumpalo` and `hashconsius` are scanned at the
# revisions pinned in Cargo.lock from the cargo git checkout (`cargo fetch` populates it) and
# reported separately. Exit status is 0 whether or not trusted items exist; the output is the
# inventory.
set -euo pipefail

if (($# == 0)); then
    cd "$(dirname "${BASH_SOURCE[0]}")/.."
    set -- crates
    [[ -d third_party ]] && set -- "$@" third_party
fi
command -v python3 >/dev/null || { echo "trust-scan: python3 required" >&2; exit 1; }

exec python3 - "$@" <<'PY'
import bisect
import glob
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
    ("axiom",
     "`axiom fn`: a proof fact stated without a body; justified in a comment beside it"),
    ("uninterp",
     "`uninterp spec fn`: a specification function with no body; its meaning is fixed only by the "
     "trusted contracts that mention it. Items marked **meaning** carry a claim about the running "
     "code; the others abstract a native value (an identity, a lock invariant, a view)"),
    ("derived_eq_claim",
     "a `PartialEqSpecImpl`/`OrdSpecImpl`/`PartialOrdSpecImpl` impl: the claim of what a type's "
     "`PartialEq`/`Ord` computes (`eq_spec`, `obeys_eq_spec`); Verus does not check `derive`d impls "
     "(`external_derive`), so the claim is trusted for every derived impl"),
    ("unannotated_pub_fn",
     "`pub fn` outside `verus!` with no `#[verus_verify]`/`#[verus_spec]`: executable code Verus "
     "ignores; callers get no contract (test-util mutators, `Domains` builders, trait impls)"),
]
KIND_NAMES = [k for k, _ in KINDS]

# Uninterpreted specs whose meaning the trusted contracts rely on, with that meaning.
MEANING = {
    "arc_identity": "native allocation identity of an `Arc`; faithful because every compared type "
                    "has a unique-per-allocation value (comment at the declaration)",
    "reference_identity": "native identity of a `&T`; same fidelity argument as `arc_identity`",
    "representatives": "the entries of an external_body hash map, as `eq_spec` classes under `key_laws`",
    "members": "the entries of an external_body hash set, as `eq_spec` classes under `key_laws`",
    "groups": "the entries of an external_body hash multimap, as `eq_spec` classes under `key_laws`",
    "successor_cache_view": "the entries of the LRU successor cache; contracts allow eviction, never a fabricated entry",
    "snapshot_published": "persistent provenance of a codebook snapshot under the registry resource",
    "singleton_store": "the process-wide numeric store of an arity (static installation)",
    "numeric_authorities": "the process-wide coordinate and history-key allocators (static installation)",
    "process_store_ids": "the process-wide store-id allocator (static installation)",
    "diagnostic_output": "what a policy rule's diagnostic callback returns for a denial",
    "policy_rule_source": "the source rule a policy rule was built from",
    "policy_rule_diagnostic": "the diagnostic callback a policy rule retains",
    "trace_rule_source": "the source rule a trace rule was built from (`TraceRule::clone` preserves it)",
    "trace_rule_diagnostic": "the diagnostic callback a trace rule retains",
    "trace_arc_call": "the result of invoking a trace diagnostic callback",
}

HELPER_CRATES = ("verus-bumpalo", "hashconsius")

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
ANNOTATED = re.compile(r"\b(verus_verify|verus_spec|verifier)\b")
CFG_TEST = re.compile(r"cfg\s*\(\s*test\s*\)")
CALL_KIND = re.compile(r"(?<![\w.:])(admit|assume)\s*\(")
ASSUME_SPEC = re.compile(r"\bassume_specification\b")
AXIOM_FN = re.compile(r"\baxiom\s+fn\s+(\w+)")
UNINTERP_FN = re.compile(r"\buninterp\s+spec\s+fn\s+(\w+)")
EQ_CLAIM = re.compile(r"\b(?:PartialEq|Ord|PartialOrd)SpecImpl\b[^;{]*\bfor\b")
PUB_FN = re.compile(r"^(?:pub(?:\([^)]*\))?)\s+(?:(?:const|unsafe|async|extern\s+\"[^\"]*\")\s+)*fn\s+(\w+)")
VERUS_MACRO = re.compile(r"\bverus\s*!\s*\{")

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

def brace_end(code, i):
    """Offset just past the `}` matching the `{` at offset `i` (code has no string literals)."""
    depth, j = 0, i
    while j < len(code):
        if code[j] == "{": depth += 1
        elif code[j] == "}":
            depth -= 1
            if depth == 0: return j + 1
        j += 1
    return len(code)

def crate_of(top, path):
    top = os.path.normpath(top)
    return os.path.join(top, os.path.relpath(path, top).split(os.sep)[0])

def scan(crate, path, raw, findings, shown=None):
    shown = shown or path
    code = strip_code(raw)
    src = raw.split("\n")
    newlines = [k for k, ch in enumerate(code) if ch == "\n"]
    line_of = lambda off: bisect.bisect_right(newlines, off - 1) + 1
    verus_regions = [(m.end() - 1, brace_end(code, m.end() - 1)) for m in VERUS_MACRO.finditer(code)]
    in_verus = lambda off: any(a <= off < b for a, b in verus_regions)
    test_file = os.path.basename(path) == "tests.rs" or "tests" in path.split(os.sep)
    for m in ASSUME_SPEC.finditer(code):
        t = re.compile(r"\[\s*(.*?)\s*\]\s*\(", re.S).search(code, m.end())
        item = re.sub(r"\s+", " ", t.group(1)) if t else src[line_of(m.start()) - 1].strip()
        findings.append((crate, "assume_specification", shown, line_of(m.start()), item))
    for m in CALL_KIND.finditer(code):
        line = line_of(m.start())
        findings.append((crate, m.group(1), shown, line, src[line - 1].strip()[:110]))
    for m in AXIOM_FN.finditer(code):
        findings.append((crate, "axiom", shown, line_of(m.start()), "fn " + m.group(1)))
    for m in UNINTERP_FN.finditer(code):
        name = m.group(1)
        note = f" — **meaning**: {MEANING[name]}" if name in MEANING else ""
        findings.append((crate, "uninterp", shown, line_of(m.start()), "fn " + name + note))
    # One pass over items: attribute blocks and the `{`-nesting of their declarations.
    # `stack` holds, per open brace: (owner impl description or None, annotated, cfg(test)).
    stack, seg_start, block, i, n = [], 0, [], 0, len(code)
    pending = ("", False, False)  # attribute text, annotated, cfg(test) of the item being read
    while i < n:
        if code.startswith("#![", i):
            i = bracket_end(code, i); continue
        if code.startswith("#[", i):
            j = bracket_end(code, i)
            block.append((code[i:j], i)); i = j; continue
        c = code[i]
        if c.isspace():
            i += 1; continue
        if block or (seg_start == i or code[seg_start:i].strip() == ""):
            attr_text = " ".join(a for a, _ in block)
            pending = (attr_text, bool(ANNOTATED.search(attr_text)), bool(CFG_TEST.search(attr_text)))
        if block:
            attrs = {m.group(1) for a, _ in block for m in ATTR_KIND.finditer(a)}
            if attrs:
                line = min(line_of(off) for a, off in block if ATTR_KIND.search(a))
                item = describe(code[i:code.find("\n", i) if "\n" in code[i:] else n])
                owner = next((h for h, _, _ in reversed(stack) if h), None)
                if owner and not item.startswith("impl"):
                    item = f"{owner} :: {item}"
                if "external_type_specification" in attrs:
                    note = " (opaque)" if "external_body" in attrs else ""
                    findings.append((crate, "external_type_specification", shown, line, item + note))
                elif "external_trait_specification" in attrs:
                    note = " (with external_trait_extension)" if "external_trait_extension" in attrs else ""
                    findings.append((crate, "external_trait_specification", shown, line, item + note))
                else:
                    findings.extend((crate, k, shown, line, item) for k in KIND_NAMES if k in attrs)
            block = []
        if code[seg_start:i].strip() == "":
            head = code[i:code.find("\n", i) if "\n" in code[i:] else n]
            owner = next((h for h, _, _ in reversed(stack) if h), None)
            m = PUB_FN.match(re.sub(r"\s+", " ", head))
            if m and not in_verus(i) and not test_file and not pending[1] and not pending[2] \
                    and not any(ann or test for _, ann, test in stack):
                item = f"{owner} :: fn {m.group(1)}" if owner else "fn " + m.group(1)
                findings.append((crate, "unannotated_pub_fn", shown, line_of(i), item))
        if c == "{":
            header = re.sub(r"#!?\[.*?\]", " ", code[seg_start:i], flags=re.S)
            m = re.search(r"(?:^|[\s;])((?:unsafe\s+)?impl\b[^;]*)$", header, re.S)
            if m and EQ_CLAIM.search(m.group(1)):
                findings.append((crate, "derived_eq_claim", shown, line_of(i), describe(m.group(1))))
            stack.append((describe(m.group(1)) if m else None, pending[1], pending[2]))
            pending = ("", False, False)
            seg_start = i + 1
        elif c == "}":
            if stack: stack.pop()
            seg_start = i + 1
        elif c == ";":
            pending = ("", False, False)
            seg_start = i + 1
        i += 1

def walk(top, skip=("target", ".git", "vendor")):
    for dirpath, dirnames, filenames in os.walk(top):
        dirnames[:] = sorted(d for d in dirnames if d not in skip)
        for name in sorted(filenames):
            if name.endswith(".rs"):
                yield os.path.normpath(os.path.join(dirpath, name))

findings = []  # (crate, kind, path, line, item)
for top in sys.argv[1:]:
    for path in walk(top):
        with open(path, encoding="utf-8") as f:
            scan(crate_of(top, path), path, f.read(), findings)

# Helper crates: pinned revision from Cargo.lock, source from the cargo git checkout.
helper_findings, helper_notes = [], []
lock = open("Cargo.lock", encoding="utf-8").read() if os.path.exists("Cargo.lock") else ""
cargo_home = os.environ.get("CARGO_HOME") or os.path.join(os.path.expanduser("~"), ".cargo")
for name in HELPER_CRATES:
    m = re.search(r'name = "%s"\nversion = "[^"]*"\nsource = "git\+[^#"]*#([0-9a-f]+)"' % re.escape(name), lock)
    if not m:
        helper_notes.append(f"`{name}`: not in Cargo.lock"); continue
    rev = m.group(1)
    label = f"{name}@{rev[:7]}"
    found = None
    for manifest in sorted(glob.glob(os.path.join(cargo_home, "git", "checkouts", "*", rev[:7], "Cargo.toml"))):
        if re.search(r'^name = "%s"' % re.escape(name), open(manifest, encoding="utf-8").read(), re.M):
            found = os.path.dirname(manifest); break
    if not found:
        helper_notes.append(f"`{label}`: checkout not found under `{cargo_home}/git/checkouts`; run `cargo fetch`")
        continue
    helper_notes.append(f"`{label}`: scanned `src/` of `$CARGO_HOME/{os.path.relpath(found, cargo_home)}`")
    src_dir = os.path.join(found, "src")
    for path in walk(src_dir):
        with open(path, encoding="utf-8") as f:
            scan(label, path, f.read(), helper_findings, shown=f"{label}/{os.path.relpath(path, found)}")

crates = sorted({f[0] for f in findings} | {crate_of(t, os.path.join(t, d)) for t in sys.argv[1:]
                for d in (os.listdir(t) if os.path.isdir(t) else []) if os.path.isdir(os.path.join(t, d))})
scanned = [os.path.normpath(t) for t in sys.argv[1:]]

def totals(rows, cols, label):
    count = defaultdict(int)
    for c, k, *_ in rows:
        count[(c, k)] += 1
    print("| kind | " + " | ".join(f"`{label(c)}`" for c in cols) + " | total |")
    print("|---|" + "---:|" * (len(cols) + 1))
    for k in KIND_NAMES:
        row = [count[(c, k)] for c in cols]
        print(f"| `{k}` | " + " | ".join(str(v) for v in row) + f" | {sum(row)} |")
    tot = [sum(count[(c, k)] for k in KIND_NAMES) for c in cols]
    print("| **total** | " + " | ".join(f"**{v}**" for v in tot) + f" | **{sum(tot)}** |")
    print()

def listing(rows, cols):
    for c in cols:
        items = [f for f in rows if f[0] == c]
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
                print(f"- `{path}:{line}`: `{item}`" if " — " not in item
                      else f"- `{path}:{line}`: `{item.split(' — ')[0]}` — {item.split(' — ', 1)[1]}")
            print()

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
print("is reported once, with the type. Not counted: `external_derive` by itself (derived trait impls")
print("that Verus ignores; the equality claims made about them are counted), `opaque`/`rlimit`/")
print("`spinoff_prover` (proof-engineering controls), `pub fn`s in `#[cfg(test)]` modules and test")
print("files, and the hypotheses of theorems (stated in each `requires`). Not scanned: `vstd`,")
print("Verus's standard library, which is part of the pinned toolchain; the root crate `src/`, which")
print("is not verified at all (see Unverified glue below).")
print()
print("## Totals")
print()
totals(findings, crates, os.path.basename)
listing(findings, crates)
print("## Helper crates (pinned git dependencies of `history-store`)")
print()
print("Verus verifies `verus-bumpalo` and `hashconsius` as dependencies at the revisions pinned in")
print("`Cargo.lock`; their own trusted items are counted here, separately from the totals above.")
print()
for note in helper_notes:
    print(f"- {note}")
print()
helper_cols = sorted({f[0] for f in helper_findings})
if helper_cols:
    totals(helper_findings, helper_cols, lambda c: c)
    listing(helper_findings, helper_cols)
print("## Trusted leaves of the search")
print()
print("- `crates/history-store/src/cache.rs`: the LRU successor cache behind `successor_cache_view`.")
print("  Its contracts allow any entry to be evicted and never a fabricated one; the search's")
print("  correctness does not depend on hits, only on the cached values being the ones once inserted.")
print("- The hash containers `NativeMap`/`NativeSet`/`NativeGroups` (`crates/history-store/src/typed/map.rs`,")
print("  `crates/history-analysis/src/native.rs`): external_body wrappers over hashbrown whose")
print("  contracts hold under `key_laws` (R4, `crates/junco-core/src/spec/hypotheses.rs`): the key's")
print("  `Hash`/`Eq` are faithful to `eq_spec` (vstd's `obeys_key_model`, the single trust token),")
print("  instantiated for the library's own key types by the `axiom` items above.")
print("- Identity of stores: `arc_identity`/`reference_identity` are functions of the pointee's spec")
print("  value (Verus erases `Arc<T>` and `&T` to `T`). The wrappers that equate them with pointer")
print("  comparison are faithful because `HistoryStore` is one static singleton per arity and")
print("  `Store<E>` carries a never-recycled id from the verified allocator; neither is `Clone`.")
print()
print("## Unverified glue")
print()
print("- The root crate `src/` is not verified. `RulePolicy::check` (`src/policy/rules.rs`) adds to")
print("  the verified `TracePolicy`/`History`: a `could_fire` head filter selecting the rules compiled")
print("  for each event; one `TracePolicy` per distinct event of a batch; decide-then-append of")
print("  granted events; audit mode, which also appends denied events; and error-to-deny (compile or")
print("  history errors become `Deny`). The verified `check_step` covers each `TracePolicy::decide`,")
print("  not this composition.")
print("- The root event types `LockEvent`, `FlowEvent`, `AgentEvent` implement `Event` by hand in the")
print("  unverified crate; `event_laws` (R1) is a hypothesis for them, stated at each impl.")
print("- User `Hash`/`Eq` code runs under the store lock; a panic there unwinds through the lock and")
print("  is outside the trusted base (the store assumes its lock invariant on re-entry).")
PY
