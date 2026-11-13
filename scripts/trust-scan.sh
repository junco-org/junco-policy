#!/usr/bin/env bash
# Lists every trusted (unverified) declaration in the Verus crates as Markdown.
#
# Usage: scripts/trust-scan.sh [DIR...] > TRUST.md
# Default: crates/ and the src/ trees of the Cargo.lock-pinned verified helpers.
# Explicit DIRs are relative to the current directory. Comments and string literals
# are ignored; target/ directories are skipped. Missing pinned helpers are an error:
# run cargo fetch --locked first. Counts describe source, not a feature-unified build.
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
import json
import subprocess
import sys
from collections import defaultdict

KINDS = [
    ("proof_axiom",
     "an external-body proof function; its ensures are axioms, not executable wrappers"),
    ("uninterpreted_spec",
     "an uninterpreted specification; meaning is supplied by contracts/hypotheses, not a body"),
    ("external_derive_claim",
     "an obeys_*_spec claim on a type with ignored external derives; audit the native derive"),
    ("unannotated_public_exec",
     "an executable public item (or trait-impl method) outside an enclosing verification annotation; a review candidate, not an axiom"),
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
EXEC_DECL = re.compile(r"(?:(pub(?:\([^)]*\))?)\s+)?(?:(?:unsafe|async|const)\s+)*fn\s+(\w+)")

AXIOM_JUSTIFICATIONS = {
    "lemma_search_key_hash_coherent": "decision 4 exact internal (u32, RegexId) key: only hash_coherent is assumed; equality laws are verified",
    "lemma_regex_pair_hash_coherent": "decision 4 exact internal (RegexId, RegexId) key: only hash_coherent is assumed; equality laws are verified",
    "lemma_test_pair_hash_coherent": "decision 4 exact internal (TestId, TestId) key: only hash_coherent is assumed; equality laws are verified",
    "lemma_parts_hash_coherent": "decision 4 internal ordered-parts key, represented by PartsKey: only hash_coherent is assumed; native equality and view facts are verified",
    "native_constraint_hash_coherent": "decision 4 exact internal Constraint key: only hash_coherent is assumed; its assumed exec specification is a hashing axiom, not an equality axiom",
}
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
    for m in re.finditer(r"\buninterp\s+spec\s+fn\s+(\w+)", code):
        findings.append((crate, "uninterpreted_spec", path, line_of(m.start()), "spec fn " + m.group(1)))
    external_derives = "external_derive" in code
    if external_derives:
        for m in re.finditer(r"\b(?:open\s+|closed\s+)?spec\s+fn\s+(obeys_\w+_spec)\b[^{};]*\{\s*true\s*\}", code):
            findings.append((crate, "external_derive_claim", path, line_of(m.start()), "spec fn " + m.group(1) + " = true (file contains external_derive)"))
    for m in ASSUME_SPEC.finditer(code):
        t = re.compile(r"\[\s*(.*?)\s*\]\s*\(", re.S).search(code, m.end())
        item = re.sub(r"\s+", " ", t.group(1)) if t else src[line_of(m.start()) - 1].strip()
        findings.append((crate, "assume_specification", path, line_of(m.start()), item))
    for m in CALL_KIND.finditer(code):
        line = line_of(m.start())
        findings.append((crate, m.group(1), path, line, src[line - 1].strip()[:110]))
    # One pass over items: attribute blocks and the `{`-nesting of their declarations.
    stack, seg_start, block, i, n = [], 0, [], 0, len(code)
    verified_stack = []
    seen_functions = set()
    while i < n:
        if code.startswith("#![", i):
            i = bracket_end(code, i); continue
        if code.startswith("#[", i):
            j = bracket_end(code, i)
            block.append((code[i:j], i)); i = j; continue
        c = code[i]
        if c.isspace():
            i += 1; continue
        attrs = {m.group(1) for a, _ in block for m in ATTR_KIND.finditer(a)}
        if block:
            if attrs:
                line = min(line_of(off) for a, off in block if ATTR_KIND.search(a))
                declaration = code[i:]
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
                    proof_axiom = "external_body" in attrs and bool(re.match(r"(?:pub(?:\([^)]*\))?\s+)?(?:broadcast\s+)?proof\s+fn\b", declaration))
                    findings.extend((crate, "proof_axiom" if k == "external_body" and proof_axiom else k,
                                     path, line, item) for k in KIND_NAMES if k in attrs)
        # Verus macro bodies and #[verus_verify] impls cover their methods. Outside
        # them, retain every unannotated public/trait-impl exec candidate, including
        # cfg(test)/test-util code; no claim is made that every candidate is reachable.
        declaration = EXEC_DECL.match(code, i) if i == 0 or not (code[i - 1].isalnum() or code[i - 1] == "_") else None
        annotated = any(re.search(r"\bverus_verify\b", a) for a, _ in block) or bool(attrs)
        function_offset = i + declaration.group(0).rfind("fn ") if declaration else -1
        first_function = declaration and function_offset not in seen_functions
        if declaration:
            seen_functions.add(function_offset)
        spec_or_proof = bool(re.search(r"\b(?:spec|proof)\s*$", code[max(0, i - 32):i]))
        if first_function and not spec_or_proof and not annotated and not any(verified_stack):
            owner = next((h for h in reversed(stack) if h), None)
            if declaration.group(1) or (owner and " for " in owner):
                item = ("".join([owner, " :: "]) if owner else "") + "fn " + declaration.group(2)
                findings.append((crate, "unannotated_public_exec", path, line_of(i), item))
        block = []
        if c == "{":
            header = re.sub(r"#!?\[.*?\]", " ", code[seg_start:i], flags=re.S)
            m = re.search(r"(?:^|[\s;])((?:unsafe\s+)?impl\b[^;]*)$", header, re.S)
            stack.append(describe(m.group(1)) if m else None)
            verified_stack.append(bool(re.search(r"\bverus\s*!\s*$", header))
                                  or bool(re.search(r"#\[\s*verus_verify\b", code[seg_start:i])))
            seg_start = i + 1
        elif c == "}":
            if stack: stack.pop()
            if verified_stack: verified_stack.pop()
            seg_start = i + 1
        elif c == ";":
            seg_start = i + 1
        i += 1

findings = []  # (crate, kind, path, line, item)
roots = [(top, None) for top in sys.argv[1:]]
helpers = []
if "crates" in sys.argv[1:]:
    metadata = json.loads(subprocess.check_output(
        ["cargo", "metadata", "--locked", "--offline", "--format-version", "1"], text=True))
    for name in ("verus-bumpalo", "hashconsius"):
        package, = [p for p in metadata["packages"] if p["name"] == name]
        source = package["source"]
        if not source or not source.startswith("git+") or "#" not in source:
            raise SystemExit(f"trust-scan: {name} is not pinned to a git revision")
        root = os.path.join(os.path.dirname(package["manifest_path"]), "src")
        label = "dependencies/" + name
        helpers.append((name, source, root))
        roots.append((root, label))
for top, label in roots:
    if not os.path.isdir(top):
        raise SystemExit(f"trust-scan: missing source directory: {top}")
    for dirpath, dirnames, filenames in os.walk(top):
        dirnames[:] = sorted(d for d in dirnames if d not in ("target", ".git", "vendor"))
        for name in sorted(filenames):
            if name.endswith(".rs"):
                path = os.path.normpath(os.path.join(dirpath, name))
                start = len(findings)
                with open(path, encoding="utf-8") as f:
                    scan(top, path, f.read(), findings)
                if label:
                    findings[start:] = [(label, kind, label + "/src/" + os.path.relpath(p, top), line, item)
                                        for _, kind, p, line, item in findings[start:]]

crates = sorted({f[0] for f in findings})
count = defaultdict(int)
for c, k, *_ in findings:
    count[(c, k)] += 1
scanned = [os.path.normpath(t) for t in sys.argv[1:]] + [name + " (pinned src)" for name, _, _ in helpers]

print("# Trust inventory of the Verus proofs")
print()
print("Generated by `scripts/trust-scan.sh` (scanned: " + ", ".join(f"`{t}/`" for t in scanned)
      + "; `target/` skipped). Do not edit by hand; rerun the script.")
print()
print("The declaration inventory below distinguishes assumed contracts, uninterpreted models,")
print("and unverified execution candidates. These categories are not additive measures of trust:")
print("one item can have multiple roles. Comments and string literals are ignored. All source")
print("configurations are scanned (including test-util/tests); cfg reachability is not evaluated.")
print("Counted kinds:")
print()
for k, d in KINDS:
    print(f"- `{k}`: {d}.")
print()
print("An opaque external type is counted once with its type, not again as an external body.")
print("Proof axioms are separated from executable external bodies. Unannotated-public-exec")
print("is a conservative lexical candidate list: enclosing verus! and #[verus_verify] are")
print("recognized, not arbitrary macro expansion. external_derive obeys claims are flagged")
print("conservatively whenever their source file contains an external derive.")
print("Not scanned: vstd (part of the pinned toolchain), Rust/std or other non-verified")
print("dependencies. Their contracts are covered by the listed external boundaries.")
print()
print("## Pinned verified helper sources")
print()
for name, source, _ in helpers:
    print(f"- `{name}`: `{source}`; scan includes its src/ tree, not tests/benchmarks.")
if not helpers:
    print("Not included in this explicitly selected scan; run the default scan for release inventory.")
print()
print("## Interpretation and guarantee boundary")
print()
print("- Meaningful uninterpreted specifications include hash_coherent (native hash/eq faithfulness),")
print("  snapshot_published (persistent codebook snapshots), diagnostic_output (callback meaning),")
print("  arc_identity/reference_identity (restricted live-owner identity), and mutex/record validity,")
print("  authority and observation tokens. These are not proved merely because they lack bodies;")
print("  all uninterpreted declarations are enumerated below, including representation selectors.")
print("- Successor search trusts GraphCaches::{successor_cache,successor_get,successor_put}: the")
print("  native LRU must preserve cached successor values and keys, including misses/eviction.")
print("- User Hash/Eq must obey the stated key laws and return normally. Panic, caught unwind,")
print("  re-entry after a user Hash/Eq panic, and unsafe client duplication/corruption are outside")
print("  the guarantee. Mutex leaves do not prove poisoning/recovery of a partially mutated map.")
print("- Benchmarks no longer enable test-util in root/fuzz dev-dependencies. Production paths")
print("  use the verified runtime,std,cache semantics and runtime analysis configuration; fault")
print("  injection and work-counter configurations are not benchmark configurations.")
print("  The two instrumentation regressions are preserved in tests/progress/counters.rs and")
print("  run explicitly with `cargo test --locked -p junco-policy --features test-util --test progress counters::`.")
print("  That opt-in native test feature is not part of the verified benchmark build.")
print("  The diagnostic fuzz replay_curve example requires its separate work-probe feature;")
print("  default fuzz all-target/benchmark builds do not activate those counters.")
print("- The root RulePolicy evaluation glue is unverified: could_fire filtering, per-candidate")
print("  TracePolicy compilation, decide-then-append, denied-event append in audit mode, and")
print("  error-to-deny conversion are outside Validator::check's theorem.")
print("- Root LockEvent/AgentEvent/FlowEvent retain public custom tagged enums, not tuple aliases.")
print("  Their hand-written Event projections need R1 projection/arity laws and R4 component")
print("  equality/hash laws. Analyzer use additionally needs surjectivity; the root crate is not")
print("  a verified target. Changing the public component vocabulary is not a behavior-neutral derive.")
print("- Existing TraceRule::clone's trusted leaf clones self.rule and the diagnostic Arc.")
print("  A source-preservation contract on this leaf rests on that native clone, not a new proof axiom.")
print()
print("## Arc/reference identity audit (Verus 0.2026.10.04.426d8b0)")
print()
print("Arc<T> and &T are modeled by referent value, not native address. A pinned-toolchain")
print("proof establishes equality of two Arc::new(0u64) results and two separate &0u64 locals")
print("(2 verified, 0 errors). Native allocation addresses are therefore not recoverable from")
print("arbitrary equal referent values.")
print("Therefore the generic uninterpreted identity functions do NOT prove pointer injectivity.")
print("The six audited leaves remain unchanged and rely on the following restricted invariants:")
print()
print("- share_store and borrow_store operate on non-Clone/non-Copy Store<E> with all fields")
print("  pub(crate), no public field setters, and Store::new as its sole constructor. It obtains")
print("  an owned linear RegistryBirth and a checked process-wide never-recycled u64 store id;")
print("  id, history_registry, store_id_receipt and registry_birth are carried in the value.")
print("  Existing lemma_registry_births_distinct, lemma_store_receipts_distinct and")
print("  independently_constructed_stores_client prove independent constructions have distinct")
print("  registry/id values. Persistent StoreIdReceipt alone is duplicable and is NOT freshness;")
print("  the linear RegistryBirth plus authoritative issuance supply it. Safe moves preserve")
print("  logical owner identity, but cannot leave two live independent owned Store values.")
print("- CompiledRule::same_owner compares live Arc<Store<E>> allocations under that same")
print("  construction invariant; a clone shares allocation. No generic Arc<T> pointer theorem")
print("  or arbitrary-user-type injectivity is claimed.")
print("- share_numeric_owner, borrow_numeric_owner and same_numeric_reference operate on")
print("  non-Clone/non-Copy HistoryStore with pub(crate) fields, no public field setters, and")
print("  HistoryStore::new as its sole constructor. Its static")
print("  registry permanently retains one Arc per arity; equal arity shares that allocation,")
print("  different arities have different domains lengths and hence different logical values.")
print("  The singleton_valid constructor leaf supplies installation/mutex fidelity, not fresh")
print("  identity; numeric_store_wf carries that fact without a separate proof axiom.")
print("These construction facts justify the six restricted trusted leaves; they do not turn")
print("the uninterpreted identity mappings themselves into proved address models. Adding a")
print("constructor, Clone implementation or unsafe duplicator requires re-auditing this boundary.")
print()
print("## Approved key trust")
print()
print("Only decision 4's five internal-key hash_coherent introductions may add proof trust.")
print("Native equality, equivalence and PartsKey view reflection are proved, never assumed.")
print("Primitive-key and Component2/3/4 compositional axioms are NOT approved. R4 retains one")
print("uninterpreted hash_coherent hypothesis. Concrete u8/u32 event witnesses may assume only")
print("their exact component-type hash premise and must prove all other bundle conjuncts.")
print("Every actual proof axiom is enumerated below, including helper dependency axioms; counts")
print("describe scanned source, not anticipated migration results. No arbitrary-user-key axiom is approved.")
print("An assumed exec hashing introduction is also an axiom: native_constraint_hash_coherent is")
print("reported under assume_specification when present, not proof_axiom. The latter counts external-body")
print("proof functions only; it must not be mistaken for the total number of logical axioms.")
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
            note = ""
            if k in ("proof_axiom", "assume_specification"):
                name = re.search(r"\bfn\s+(\w+)", item)
                key = name.group(1) if name else item.rsplit("::", 1)[-1].strip()
                justification = AXIOM_JUSTIFICATIONS.get(key)
                if k == "proof_axiom" or justification:
                    note = " — " + (justification or "AUDIT REQUIRED: no per-declaration approval/justification recorded")
            print(f"- `{path}:{line}`: `{item}`{note}")
        print()
PY
