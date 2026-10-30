# bumpus

A verified, fixed single-chunk bump allocator. `src/lib.rs` contains allocation and reclamation proofs; `src/layout.rs` is the trusted `Layout::size`/`Layout::align` bridge.

## Specification

The contracts below apply to verified callers holding a well-formed `BumpState`. Allocation and reset preserve the arena's identity and pointer provenance.

### Arena model

One fixed chunk occupies the half-open byte range `[start, end)`. Allocation proceeds downward from `cursor`:

```text
start <= cursor <= end
capacity = end - start
remaining = cursor - start
in_arena(addr, size) = start <= addr && addr + size <= end
align_down(x, a) = x - x % a
```

These are mathematical integer expressions, not wrapping machine arithmetic. `Bump::{start, end, cursor, capacity, remaining, in_arena}` exposes this model to proofs. `remaining` is the space below the cursor, not the total number of free bytes.

Free bytes and outstanding allocation ranges form a disjoint partition of the chunk. Distinct outstanding allocations have disjoint byte ranges, and every byte in `[start, cursor)` is free. Zero-sized allocations may share an address.

### Creation and allocation

- `AllocErr` names why a request was refused: `Capacity` (`cap == 0 || cap > MAX_CAP`), `Global` (global-allocator failure, an unrepresentable chunk end, or a container's pointer table), `Exhausted` (does not fit in this chunk, including a slice byte count that overflows `usize`).
- `try_with_capacity(cap)` creates an empty arena with `capacity = remaining = cap`, `cursor = end`, and `start` a multiple of `CHUNK_ALIGN` (16). Invalid capacities return exactly `Capacity`; the arena never grows.
- For `try_alloc(s, a)` with `a` a power of two, let `c` be the old cursor and `p = align_down(c - s, a)`. Allocation succeeds **if and only if** `s <= c - start` and `start <= p`. `try_alloc_layout(layout)` is `try_alloc(layout.size(), layout.align())`.
- Success returns a pointer at exactly `p`, sets `cursor = p`, and adds one fresh outstanding allocation. The pointer is aligned to `a`, its byte range `[p, p + s)` lies inside the arena, and the caller receives its uninitialized-memory permission (`PointsToRaw`) and return token (`BumpTok`). Alignment padding stays owned by the arena.
- Failure is exactly `Exhausted` and leaves the entire tracked state unchanged. In particular, `s + a - 1 <= remaining` is sufficient for success.

### Permissions and reclamation

`BumpTok::{inst, id, alloc}` identifies an allocation and its `Alloc { addr, size }` record. `BumpState::outstanding()` is the set of live allocation IDs. Given a token from the same arena instance, `BumpTok::agree` proves its ID is outstanding and `BumpState::addr_of(id) == token.alloc().addr`.

Every entry in a return map `back` must contain that allocation's token and complete raw-memory permission, with the arena's provenance (`back_wf`). The map may contain only outstanding IDs.

- `reset_to(mark, back)` requires `start <= mark <= end` and every unreturned allocation's starting address to be at least `mark`. It consumes the returned permissions and tokens, sets `cursor = mark`, and removes exactly `back.dom()` from the outstanding IDs. Unreturned allocations and their permissions remain valid; their stored values are preserved. The mark need not be a previously saved cursor.
- `reset(back)` requires **every** outstanding permission and token. It is `reset_to(end, back)`: no outstanding allocations remain and `remaining = capacity`. The same layout allocated from the initial cursor and immediately after a full reset yields the same address.
- `free(back)` likewise requires every outstanding permission and token, consumes the arena and tracked state, and releases the chunk to the global allocator.

Reclamation does not run allocation destructors. There is no `Drop` implementation: omitting `free` leaks the chunk. Permissions must be returned explicitly; reset cannot invalidate an owner whose permission is still held by a caller.

`TypedArena<T>` stores initialized `T: Copy` values by index; `SliceArena<T>` stores immutable copied slices by index. Both encapsulate tracked permissions and allocation tokens behind type invariants, expose fallible `with_capacity`/`try_push` plus `len`/`get`, and require explicit `free`. Freeing runs no destructors (`T: Copy`). The crate supports `no_std` with `alloc` on 32-bit and 64-bit targets.

Both containers expose `capacity()`, `remaining()`, and `aligned()` (the cursor is a multiple of `align_of::<T>()`) to proofs:

- `with_capacity(c)` yields `capacity() == remaining() == c`, and `aligned()` whenever `align_of::<T>() <= CHUNK_ALIGN` and `c % align_of::<T>() == 0`. Invalid capacities return exactly `Capacity`.
- `try_push` never changes `capacity()`. Any error leaves the contents, `remaining()`, and `aligned()` unchanged.
- From an aligned cursor, a successful push keeps the cursor aligned and consumes exactly `w` bytes (`w = size_of::<T>()` for a value, `w = len * size_of::<T>()` for a slice), and `Exhausted` is returned only when `w > remaining()`. Same-type pushes therefore never pad, and a chunk of `n * size_of::<T>()` bytes holds `n` values.

### Verification boundary

Tracked permissions and tokens are proof resources, not runtime ownership checks. Memory-safety guarantees require verified callers to satisfy the contracts; ordinary Rust raw-pointer dereferences still require `unsafe`. The crate-local trusted statements are:

- `try_allocate` (`src/lib.rs`): an external body that calls the global allocator and fabricates its `PointsToRaw`/`Dealloc` permissions with `Tracked::assume_new()`, mirroring vstd's `allocate` contract. A failed allocation is unconstrained.
- `slice_ref` (`src/arena.rs`): an external body that forms a shared slice from a `SlicePerm` (non-null, aligned base; initialized, contiguous, single-provenance elements; at most `isize::MAX` bytes).
- `Layout::size`/`Layout::align` (`src/layout.rs`): `assume_specification`s stating that `align` is a power of two that fits in `usize`. No `global layout` directive is declared, so no pointer-width or primitive-alignment axiom is assumed.
- vstd's raw-pointer, layout, ghost-map, and `PCell` axioms.

Tracked values are affine: Verus does not report an arena that is dropped without `free`, and a panic between a container's `inner.take()` and its restoration leaks the chunk. Leak freedom and behavior under unwinding are therefore not verified. Proofs were checked on x86_64; the contracts contain no target-specific constants.

`smoke` proves pointer reuse after partial and full reset and reads `42` from an allocation retained across the partial rewind.

## Verification

Checks: `cargo verus verify`, `cargo test --release`, `cargo build --release --all-targets`, and `cargo bench --bench bump`.

## Benchmark

Run `cargo bench --bench bump` to compare against crates.io `bumpalo = 3.20.3`, using 200 samples and a 10-second measurement window per function. Each timed iteration performs 10,000 allocations followed by an arena reset; arena construction is outside the timed loop. `small` allocates `u8`; `big` allocates `[usize; 32]`.

The `/const` variants expose the layout to the optimizer so both allocators can fold layout-dependent branches. The `/opaque` variants hide the layout with `black_box` on every allocation.

One local release-mode run on Linux x86_64 (WSL2) produced:

| Group | Slope ratio | Median ratio |
| --- | ---: | ---: |
| small/const | 0.62× | 0.62× |
| small/opaque | 0.47× | 0.47× |
| big/const | 0.39× | 0.38× |
| big/opaque | 0.43× | 0.43× |

Each ratio is **verus-bumpalo time / bumpalo time**, not a throughput ratio: below 1 means verus-bumpalo took less time. For example, 0.62× means 62% of bumpalo's time, or 38% less time. Slope uses Criterion's linear-regression time-per-iteration estimate; median uses the median per-iteration time across samples. These are measurements from one run, not a machine-independent speedup guarantee.

The acceptance threshold is ≤1.30× for both `/const` slope ratios (median if slope is unavailable); both rows passed in this run.

Estimates are read from `$CRITERION_HOME`, else `$CARGO_TARGET_DIR/criterion`, else `target/criterion`. Missing or invalid estimates print `n/a`; filtered runs can display stale rows for groups that were not run.
