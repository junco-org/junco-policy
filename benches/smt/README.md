# SMT regex inclusion benchmark

`cargo bench --bench smt` measures the time spent in
`history_analysis::PolicyAnalyzer::tail_included(head, left, right)` for each RegExLib Subset
inclusion instance. These tails have no candidate variables, so an inhabited constant head
preserves ordinary language inclusion. Criterion IDs are
`regexlib_subset/{sat,unsat}/notsubset_i_j`; head, regex and analyzer construction and verdict
preflight checks are outside the timed call. No memory measurement is performed.

## Credits

These instances are the `regexlib_subset` benchmarks of Caleb Stanford, Margus Veanes, and
Nikolaj Bjørner, *Symbolic Boolean Derivatives for Efficiently Solving Extended Regular Expression
Constraints*, PLDI 2021, published at
<https://github.com/cdstanford/regex-smt-benchmarks> (MIT). They were first assembled for Nikolaj
Bjørner, Vijay Ganesh, Raphael Michel, and Margus Veanes, *An SMT-LIB Format for Sequences and
Regular Expressions*, SMT 2012, from regular expressions on <https://regexlib.com>.

The translation uses upstream commit `8c5523b2c46c5d8d3d77231881f0834921aaea1b`.

## Dataset

There are 100 inclusion instances built from 20 distinct regexes:

- The 90 `sat/notsubset_i_j.smt2` files (`i ≠ j`) ask whether `B_i ⊑ B_j`; inclusion fails.
- The 10 `unsat/notsubset_i_i.smt2` files ask whether a restricted variant `A_i ⊑ B_i`;
  inclusion holds. For example, a restricted variant uses `[1-9]` where the other uses `\d`.

`included: true` in `INSTANCES` means inclusion holds, corresponding to upstream `unsat`:
the SMT query asks for a string in the left language but not the right language.

## Translation

- A character is the action of `Char(u8)`; its principal and resource are both `()`.
- A range or union of ranges becomes one `Test(Or[Eq atoms])` over the representatives inside it.
- Nested `re.union` and `re.++` chains are flattened. Empty-string terms drop out of concatenations.
- Bounded loops use a right-nested optional tail of depth `hi - lo`, so a derivative of the
  loop is one term rather than a union.

| SMT-LIB | `history_syntax` |
| --- | --- |
| `re.++` | `RegexExpr::concat` |
| `re.union` | `RegexExpr::union`, merging range children into one character test |
| `re.range` | One character-class test over representative actions |
| `re.*` | `RegexExpr::star` |
| `re.+ r` | `r · r*` |
| `re.opt r` | `ε ∪ r` |
| `(_ re.loop lo hi) r` | `r^lo · (ε ∪ r·(ε ∪ r·…))`, with `hi - lo` optional copies |
| `str.to_re ""` | `RegexExpr::epsilon()` |

The dataset's 29 distinct ranges partition all 256 bytes into 47 classes that no range splits.
`ALPHABET` contains one representative byte per class and is declared as the entire action
universe with `Domains::infinite().with_domain(Component(1), &ALPHABET.map(Component3::C1))`. No fresh action characters exist.
Every character test is a union of whole classes, so inclusion over the representatives is
identical to inclusion over the full 8-bit alphabet. The dataset has no complement,
intersection, `re.allchar`, or `re.all`; loop upper bounds are at most 67.

## Regenerate

Run from the repository root with Python 3 (standard library only) and Rust 1.98.1:

```sh
git clone --depth 1 https://github.com/cdstanford/regex-smt-benchmarks /tmp/regex-smt-benchmarks
python3 benches/smt/translate.py /tmp/regex-smt-benchmarks/regexlib_subset > benches/smt/regexlib_subset.rs
cargo +1.98.1 fmt -p junco-policy
```

## License

The regular expressions in `regexlib_subset.rs` derive from the MIT-licensed benchmark repository:

```text
MIT License

Copyright (c) 2021 Caleb Stanford

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
