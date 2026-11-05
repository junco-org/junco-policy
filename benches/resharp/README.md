# RE# comparison benchmark

```sh
cargo bench --bench resharp -- --noplot
cargo bench --bench resharp -- 'corpus/literal-miss/' --noplot
```

Each Criterion group compares two functions:

- `junco`: `history_semantics::Validator::permits` on a committed history of one event per byte.
  Rollback and re-append of the final event happen outside the timed call, invalidating the retained
  cursor so each call replays the history with warm derivative tables. Empty histories need no
  rollback. Compilation, seeding, and verdict assertions are untimed.
- `resharp`: `Regex::is_match`, with `UnicodeMode::Ascii` and `multiline(false)`. Compilation is
  untimed; RE#'s cached DFA stays warm across iterations.

Throughput is haystack bytes per second. RE# works over a bounded byte alphabet; junco components
are open domains, and the bench carries each byte as the event's resource, interned on first sight.
Unanchored workloads use **contains** semantics (`All · p · All` versus `is_match`), so both engines
stop at the first match; `corpus/literal-miss` deliberately forces a scan of the whole haystack.
For early matches, reported throughput uses the full haystack size, not the number of bytes visited.
Search order and fast paths differ: RE# can search backwards, while junco folds forwards.
Equal verdicts therefore do not imply equal numbers of bytes visited.
A nullable contains pattern such as `.*` succeeds without visiting any events.

Every run asserts that junco's verdict equals RE#'s for every workload. Each timed junco result is
also checked. Criterion filters apply inside `bench_function`, so even a filtered run constructs,
seeds, and preflights all 40 supported workloads (22 scan, 8 validation, 10 corpus).
Only one validator is alive at a time.
Sampling is Flat, with 20 samples, 500 ms warm-up, and 2 s measurement per engine and workload.
The benchmark runs on a 64 MiB stack, as originally required for the large corpus translations.

## Credits

[RE#](https://github.com/ieviev/resharp) by Ian Erik Varatalu (MIT), crate `resharp 0.7.6`.
The [RE# paper](https://dl.acm.org/doi/10.1145/3704837) is linked from the upstream README.
Workloads are ported from:

- [`resharp-engine/examples/popular-crates.rs`](https://github.com/ieviev/resharp/blob/a16be2d2ccc14b992dd9360b2f6926703fb13ba2/resharp-engine/examples/popular-crates.rs)
- [`resharp-engine/benches/comparison.rs`](https://github.com/ieviev/resharp/blob/a16be2d2ccc14b992dd9360b2f6926703fb13ba2/resharp-engine/benches/comparison.rs)
- [`resharp-engine/benches/ismatch.rs`](https://github.com/ieviev/resharp/blob/a16be2d2ccc14b992dd9360b2f6926703fb13ba2/resharp-engine/benches/ismatch.rs)

Data files are copied from upstream `data/` at commit
`a16be2d2ccc14b992dd9360b2f6926703fb13ba2`.
Unlike upstream's `popular-crates` find-all comparison, this target measures existence only.

## Translation

`translate.rs` parses standard syntax using `regex-syntax` with UTF-8 and Unicode disabled.
`Symbol::Byte(u8)` is an event with unit principal/action and the byte as its resource.
`Symbol::Candidate` is the only event matching the rule head. Haystack `check`s therefore append
without evaluating the rule; `permits(&Symbol::Candidate)` evaluates its `Require` tail.
The candidate itself is not part of the committed history. Require permits exactly when the
history belongs to the tail language.

| Standard syntax | `history_syntax` form |
|---|---|
| Literal | Concatenation of one-event resource equalities |
| Class with 0 members | `Empty` |
| Class with 1 member | One `Eq` atom |
| Class with 2–128 members | `Or` of `Eq` atoms |
| Class with 129–255 members | `And` of `Neq` atoms for excluded bytes |
| Class with all 256 bytes | One-event `True` test |
| `.`, `[^…]` | Byte class; dot excludes newline |
| `\s`, `\d`, `\w` | ASCII whitespace, digits, word bytes |
| `*`, `+`, `?`, `{m,n}` | Star, concatenation, nested optional suffixes |
| `a\|b` | Union |
| `^…$` | Exact whole-history match |
| Unanchored `p` | `All · p · All` |
| Edge `\b` | Left `(ε \| All·\W)`, right `(\W·All \| ε)` |
| `(?i)` | ASCII-folded byte classes |

Edge `\b` is supported only next to a word character, as in these corpus patterns. Interior
look assertions fail loudly; this is not a general lookaround translator. Large classes use
inequalities instead of enumerating the event resource domain. Although a negated class can also
accept `Candidate`, histories contain only `Byte` events.

Custom patterns use regular-language operations directly. Here `C(p) = All · p · All`, `ε` is the
empty history, `Σ = All`, `¬` is whole-language complement, and `∩` is intersection.

| Workload | RE# pattern | Junco tail |
|---|---|---|
| script-tag | `(?i)<script[^>]*>~(_*</script>_*)</script>` | `C(open · ¬C(close) · close)`; open/close ASCII-folded |
| deleted-at-token | `(?<!\_)deleted\_at(?!\_)` | `(ε \| Σ·[^_]) · deleted_at · (ε \| [^_]·Σ)` |
| decimal-point | `(?<=\d)\.(?=\S)` | `C(\d\.\S)` |
| attribute-whitespace | `(?<="\|')\s+(?=[^<>\s]+=)` | `C(["']\s+[^<>\s]+=)` |
| password-strength | `^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$` | `[A-Za-z\d@$!%*?&]{8,} ∩ C([a-z]) ∩ C([A-Z]) ∩ C(\d) ∩ C([@$!%*?&])` |
| username-no-symbols-only | `^(?![\-\_]*$)[A-Za-z0-9][A-Za-z0-9\-\_]{3,20}[A-Za-z0-9]$` | `¬([-_]*) ∩ [A-Za-z0-9][A-Za-z0-9_-]{3,20}[A-Za-z0-9]` |
| lookaround | `(?<=\s)[A-Z][a-z]+(?=\s)` | `C(\s[A-Z][a-z]+\s)` |

RE#'s bare `_` means any byte; literal underscores outside classes are escaped in RE# patterns.
Junco's standard parser treats `_` literally. Lookaround translations consume the context bytes;
that preserves existence, not match offsets or captures, neither of which is measured here.

## Workloads

### Popular scan

Groups are `popular/scan/<name>`. All use upstream `build_haystack()` verbatim: 19 fixed lines
cycled, each followed by newline, until at least 1 MiB. This includes prose, URLs, markup, escapes,
templates, identifiers, and punctuation.

| Name | Pattern |
|---|---|
| whitespace | `\s+` |
| digits | `\d+` |
| dot-star | `.*` |
| html-tag | `<[^>]+>` |
| blank-lines | `\n{3,}` |
| ansi-escape | `\x1b\[[0-9;]*m` |
| template-var | `\$\{([^}]+)\}` |
| html-tag-any | `<[^>]*>` |
| word | `\w+` |
| dash-run | `-+` |
| literal-test | `test` |
| semver | `\d+\.\d+\.\d+` |
| digits-class | `[0-9]+` |
| code-span | <code>`([^`]+)`</code> |
| quoted-string | `"([^"]+)"` |
| md-link | `\[([^\]]+)\]\(([^)]+)\)` |
| multi-space | `\s{2,}` |
| uppercase-letter | `[A-Z]` |
| script-tag | `(?i)<script[^>]*>~(_*</script>_*)</script>` |
| deleted-at-token | `(?<!\_)deleted\_at(?!\_)` |
| decimal-point | `(?<=\d)\.(?=\S)` |
| attribute-whitespace | `(?<="\|')\s+(?=[^<>\s]+=)` |

### Popular validation

Groups are `popular/validate/<name>`. Patterns are exact matches, without an outer contains wrapper.

| Name | Pattern | Sample |
|---|---|---|
| email | `^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$` | `user.name+tag@example.co` |
| iso-date | `^\d{4}-\d{2}-\d{2}$` | `2021-08-14` |
| empty-line | `^$` | Empty |
| numeric-line | `^\d+$` | `1234567890` |
| identifier | `^[a-zA-Z_][a-zA-Z0-9_]*$` | `some_ident_name123` |
| slug | `^[a-zA-Z0-9_-]+$` | `some-slug_name-123` |
| password-strength | `^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$` | `P@ssw0rd!` |
| username-no-symbols-only | `^(?![\-\_]*$)[A-Za-z0-9][A-Za-z0-9\-\_]{3,20}[A-Za-z0-9]$` | `valid123` |

### Corpus

Groups are `corpus/<name>`. Every supported row uses contains semantics. In the attempted upstream
patterns below, `dictionary(n)` joins the first `n` lines of upstream's `regexes/length-15.txt` with `|`.
Payloads for omitted workloads are not shipped. Eight workloads hit junco's existing graph limit:
`Runtime(GraphLimit { limit: 102400 })` at `add_rule`, or `GraphLimit { limit: 102400 }` at `permits`.
They are not registered; runtime limits are unchanged.

| Name | Pattern | Haystack |
|---|---|---|
| literal-hit | `Sherlock Holmes` | en-sampled.txt |
| literal-miss | `ZZZYYYXXX999` | en-sampled.txt |
| bounded-repeat-hit | `\b[0-9A-Za-z_]{12,}\b` | en-sampled.txt, 2,500 lines |
| alternation-hit | `Sherlock\|Holmes\|Watson\|Irene\|Adler` | en-sampled.txt |
| dictionary-hit (not ported: `add_rule` graph limit) | `dictionary(2663)` | en-sampled.txt |
| word-boundary-hit | `\b[A-Z][a-z]+\b` | en-sampled.txt |
| bounded-repeat | `[A-Za-z]{8,13}` | en-sampled.txt, 5,000 lines |
| url | `https?://[a-zA-Z0-9./_?&=#%-]+` | rust-src-tools-3b0d4813.txt, 10,000-line prefix |
| bounded-repeat-context (not ported: `permits` graph limit) | `[A-Za-z]{10}\s+[\s\S]{0,100}Result[\s\S]{0,100}\s+[A-Za-z]{10}` | rust-src, 500 lines |
| date-monster (not ported: `permits` graph limit) | `regexes/date.txt` | rust-src, 10,000 lines |
| dictionary-500 (not ported: `permits` graph limit) | `dictionary(500)` | en-medium.txt |
| dictionary-full (not ported: `add_rule` graph limit) | `dictionary(2663)` | en-medium.txt |
| phone | `(\(?\+?[0-9]*\)?)?[0-9_\- ()]{7,}` | en-sampled.txt, 5,000 lines |
| dictionary-sorted (not ported: `add_rule` graph limit) | `dictionary(2663)` | length-15-sorted.txt |
| dictionary-context (not ported: `add_rule` graph limit) | `regexes/dictionary-fixed-context.txt` | length-15-sorted.txt |
| dotstar-eq-redos | `.*=.*` | cloud-flare-redos.txt |
| dictionary-nocase (not ported: `add_rule` graph limit) | `(?i)(dictionary(2663))` | en-sampled.txt |
| lookaround | `(?<=\s)[A-Z][a-z]+(?=\s)` | en-sampled.txt |

Deviations from upstream:

- `url` uses the 10,000-line source prefix instead of the full 7,384,531-byte file.
- Duplicates `literal`, `literal-alternation`, `readme/dictionary`, and `readme/literal*` are folded
  into the equivalent rows above.
- `is_match/vs-find-all` is not ported: it compares RE# internally, not the two engines.
- `readme/dictionary-seeded` is not ported: it requires another 944 KB haystack.
- Byte classes and folding use ASCII mode for both engines rather than upstream's Unicode Full
  mode in `popular-crates`.

## Data

Haystacks are read as bytes, never as `String`. Only the three files used by supported workloads
are retained.
Line-limited haystacks exclude the final selected newline, matching upstream's
`lines().take(n).join("\n")` on these LF-only files.

| Target under `data/` | Upstream path under `data/` | Bytes | Copy |
|---|---|---:|---|
| haystacks/en-sampled.txt | haystacks/en-sampled.txt | 899,232 | Verbatim |
| haystacks/cloud-flare-redos.txt | haystacks/cloud-flare-redos.txt | 10,001 | Verbatim |
| haystacks/rust-src-tools-3b0d4813.txt | haystacks/rust-src-tools-3b0d4813.txt | 280,646 | First 10,000 lines of 7,384,531 bytes |

Re-fetch from the repository root:

```sh
base=https://raw.githubusercontent.com/ieviev/resharp/a16be2d2ccc14b992dd9360b2f6926703fb13ba2/data
mkdir -p benches/resharp/data/haystacks
for f in en-sampled.txt cloud-flare-redos.txt; do curl -fsSL "$base/haystacks/$f" -o "benches/resharp/data/haystacks/$f"; done
curl -fsSL "$base/haystacks/rust-src-tools-3b0d4813.txt" | head -n 10000 > benches/resharp/data/haystacks/rust-src-tools-3b0d4813.txt
```

## License

The patterns and haystacks under `data/` and the workload definitions derive from
the MIT-licensed RE# repository:

```text
MIT License

Copyright (c) 2025 Ian Erik Varatalu

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
