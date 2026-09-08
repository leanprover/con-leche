---
name: lean-rc-linearity
description: Lean 4 reference-counting and linearity: how to keep hot data structures unshared, diagnose copies, and avoid codegen traps
allowed-tools: Read, Bash, Grep
---

# Lean 4 reference counting and linearity

Canonical source: <https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/>.
Runtime background distilled from Henrik Böving, *Everything You Need To Know About
The Lean Runtime* (Lean FRO offsite, 2026-05-18). Project findings cite `DESIGN.md`
sections and commits in this repo; toolchain evidence is `lean.h` at v4.33.0.

## 0. The one rule

**An in-place update happens iff the object is at RC 1 at the moment of the
mutation.** Anything alive across that moment — a variable the compiler chose to
keep live, a closure that captured it, a tuple the loop is threading — is a second
reference, so the mutation copies the whole structure instead.

Corollary that costs the most time to learn: **compiler liveness placement decides
this, not source order.** Every RC-2 holder found in this project was a
compiler-liveness surprise, invisible in the source. Reason about it, then
*measure* it (§4).

## 1. Rules first (apply these while writing)

1. **Use-then-consume.** Every use of a value must finish *before* the mutation
   that consumes it. If a rare branch needs the pre-mutation value, decide the
   branch **before** the expensive step, don't straddle it. (`DESIGN.md` "FEnv
   linearity", §3.4.)
2. **No `for`/`mut` loops over threaded state on a hot path.** Compiled `forIn`
   boxes the accumulator tuple and keeps the previous iteration live into the next
   step call. Use explicit tail recursion with the accumulators as plain
   arguments. (`progressLoop`/`diagLoop`/`parseExportStream` in `Main.lean`,
   `ConLeche/Frontend/Export.lean`.)
3. **`modify`, not `get`/`set`.** `let s ← get; let s := f s; set s` leaves the ref
   holding its own copy while you mutate; `modify f` hands ownership through. The
   VEIR parser went 22 s → 4.5 s on exactly this change (`getContext`/`setContext`
   → `modifyContext`).
4. **One-shot container ops, not read-modify-write.** `HashMap.alter` over
   `getD` + `insert`; `Array.modify`/`set` over read-then-write.
5. **State reads that cross a call must be opaque.** A read helper that inlines to
   a pure projection can be *sunk* past a later call, keeping the projected value
   alive across it. Mark it `@[noinline]` (§3.1).
6. **Closure capture is an owned reference for the closure's whole lifetime.**
   Building `ops fe` (a record of closures over `fe`) and passing it to a long call
   pins `fe` for the duration of that call, even though the source "just passes a
   parameter" (§3.4).
7. **Borrow read-only parameters.** `@&` (or inferred borrowing) elides RC on
   traversals entirely (§2.3).
8. **Prefer a phase that returns only `Bool`.** It provably cannot retain anything
   it built (§5.2).

## 2. Mechanics (enough to reason from)

### 2.1 Object model

Every heap object starts with an 8-byte header:

```c
typedef struct { int m_rc; unsigned m_cs_sz:16; unsigned m_other:8; unsigned m_tag:8; } lean_object;
```

`m_rc`: `> 0` single-threaded, `= 1` unique, `= 0` persistent, `< 0` multi-threaded
(atomic RC). `m_tag` is 8 bits → at most 256 constructors. **Every indirection
costs ≥ 8 bytes**, which is why flattening nested structs into scalar fields is a
real memory win (leanprover/lean4#11162: ~1 GB off Mathlib's language server by
inlining `Lsp.Range`/`Position` into `Nat` fields).

Representations: enum inductives → unboxed integers; single-ctor single-field
inductives → that field; everything else `lean_ctor_object`; `Array` →
`lean_array_object`; `ByteArray`/`FloatArray` → `lean_sarray_object`; `UIntN`/`USize`
→ native ints; `Float32`/`Float` → `float`/`double`; `Nat`/`Int` → tagged scalar or
boxed MPZ.

Boxing when an unboxed value is passed where a `lean_object*` is expected:
`UInt8/16/32` → tagged `((n << 1) | 1)`; `UInt64`/`USize`/floats → a single-field
ctor allocation; `Nat`/`Int` → tagged while small, MPZ otherwise. Chains like
`n.toNat.toUInt64` pay this repeatedly; a struct of `UInt64` fields beats a
polymorphic `Prod'`.

### 2.2 In-place update and reuse

`Array`/`ByteArray` always update in place at RC 1; `lean_ctor_object` when the
compiler decides to. **Reuse**: when the optimizer sees `x` will be `dec`-ed and
then an object of the same layout allocated, it emits a runtime uniqueness check
and reuses `x`'s memory instead of hitting the allocator.

### 2.3 The RC ABI

Three argument kinds:

* **scalar** (`uint8`, tagged) — never RC-ed;
* **owned** `(x : obj)` — the *callee* must `dec` it;
* **borrowed** `(x : @& obj)` — the *caller* stays responsible.

Insertion is then forced: `inc x` when passing `x` as owned while still using it
later; `dec x` once `x` is dead, owned and not transferred. A parameter is inferred
borrowed if it is only read from, only passed on as borrowed, and never used in
reuse — and modern Lean lets you write `@&` on ordinary functions, not just
`@[extern]`. Marking a recursive read-only traversal `@&Node α β → …` removes the
RC traffic from the whole walk.

Avoiding RC matters beyond the counter bump: it adds code size, adds
"is it mt?" branches, and LLVM refuses to optimize across atomics (it will not
prove `*x` still reads 42 after an `atomic_fetch_add` on an unrelated pointer).

### 2.4 Compiler knobs you will actually reach for

* Inlining is annotation-driven (auto-inline only below `compiler.small`, default 1):
  `@[inline]`/`@[always_inline]`, `@[macro_inline]` (parameters treated lazily —
  fixes control-flow helpers like a custom `ite`), `@[noinline]`, and
  `inline (f x)` at a call site.
* Specialization: type classes specialize by default; `@[specialize]`,
  `@[specialize f]`, `@[nospecialize]`, `@[weak_specialize]` (for `Inhabited`-style
  classes that should ride along only). Inner `let rec go` loops usually need an
  explicit `@[specialize]` to escape closure/vtable passing.
* Tracing: `trace.Compiler` (everything), `trace.Compiler.saveBase` /
  `saveImpure` (end-of-phase IR), `trace.Compiler.simp`, `trace.Compiler.result`,
  plus `pp.funBinderTypes` / `pp.letVarTypes`. (`trace.compiler.ir.result` is gone.)

### 2.5 Concurrency notes (rarely relevant here, but sharp)

Putting a value into `Std.Mutex`, `IO.Ref` or `Std.Channel` marks it multi-threaded
→ atomic RC forever after. `IO.Ref` is a TAS spinlock: for real multi-threading use
`Std.Mutex`. Blocking inside `IO.asTask` does **not** context-switch and stalls the
pool — use `Async`/`Async.sleep`. Prefer bounded channels.

## 3. The three-and-a-half RC-2 holder incidents in this repo

All four have the same shape: **a value stayed live across a mutation site because
of where the compiler placed liveness, not because the source shared it.**
Retention *across* a mutation = `inc` = copy at that site.

### 3.1 Sunk pure store reads → `@[noinline] withStore`

`withStore f` inlined to the pure application `f s.store`. When the result was not
consumed before the next call, the compiler *sank* the application past that call
(profitable when the call can throw) — e.g. `inferBodyI` computed `getAppArgsI`
only after `r.infer` returned, keeping the projected `EStore` at RC 2 across the
entire nested inference. ~6100 whole-table copies per run; ~35 % of the
init-prelude probe. Fix: `withStore` is `@[noinline]` — an opaque state-threading
call cannot be reordered, so the projection lives and dies inside the callee.
(`ConLeche/Kernel/CoreI.lean:279-291`; `DESIGN.md` "The whole-arena copy-on-write
strikes".) Note `viewI` stays `@[inline]`: its result is always immediately
matched, and branch selection forces it before any later state op.

### 3.2 `progressLoop`: the boxed `forIn` accumulator

`CON_LECHE_PROGRESS`'s `for`/`mut` loop compiled to `forIn`, whose state tuple
`(fe, s)` stays live into the next step call — so the interned state *entered every
declaration* at RC 2 and the first mutation struck (+110 G instructions in both
modes). Fix: explicit tail recursion, accumulators as plain arguments
(`Main.lean:86`).

### 3.3 `diagLoop`: the diagnostic second pass

"Non-progress is >20× slower" on Mathlib prefixes was *not* the verified fold —
`checkDeclsPure`'s `List.foldlM` compiles to a specialized tail-recursive loop
threading state uniquely (confirmed in the generated C). It was `checkMain`'s
diagnostic second pass (error branch only, and every big Mathlib stream ends in a
decline): its `for d in decls2` loop's boxed state tuple kept the re-parsed arena
at RC 2 into every step, so each declaration's first arena mutation copied the
whole node/hash tables. Copy cost grows with the arena, which is why small streams
never showed it. Fix: `diagLoop`, same explicit-recursion pattern (`Main.lean:124`;
`DESIGN.md` "Mathlib-scoping driver fixes" item 2).

### 3.4 The FEnv cert branch (#99): closure capture across the value check

Every `defnDecl` cost a full copy of the `FEnv.idx` bucket array — a hidden O(n²)
in the number of definitions. The driver branches kept `fe` live across
`checkDefnValP` for the *conditional* Nat-op certification
(`certifyNatEqs (sharedOps fe) fe.env`, `checkDivModPinF … fe fe2`, intentionally
pre-insertion), so `fe` was pinned at RC 2 and the final `fe.push` copied the map.
`sharedOps fe` (`ConLeche/Kernel/CheckerS.lean:329`) is a record of five closures
each capturing `fe` — **capture is an owned reference held for the callee's whole
lifetime.**

Fix (the use-then-consume shape): the rare branch is a pure name test over 16
pinned names, so it is decided **before** the value check; the common path
tail-calls with `fe` consumed (`CheckerS.lean:1252`, `:1504`). Measured: copies
2532 → 297, init-prelude 27.98 G → 27.82 G, and the `many` scale shape's doubling
exponent 1.16/1.27/1.43 → 1.00/1.00/1.01 (at n = 16000, 8.91 G → 4.54 G).

## 4. Diagnosis toolkit

Work in this order; the striking frame lies (§4.5).

1. **`dbgTraceIfShared` probes at mutation sites** — the *diag/linearity* pattern.
   Throwaway branch, probes at every persistent-container mutation:
   `EStore.intern`/`internL` (the node/cons table pushes) and `FEnv.push`'s
   map-insert site, plus per-site tags so you can attribute counts to callers.
   Run the probe on your branch **and on an identically-probed baseline** and
   compare counts — absolute numbers mean nothing, deltas do. Revert the probes
   after. (`DESIGN.md` "Linearity of the reordered push"; the #99 and Mathlib-scoping
   audits used the same pattern.)
2. **Read the generated C.** In `.lake/build/ir/<Module>.c`, find the mutation call
   and check for a surviving `lean_inc_ref` on the argument before it. The #64
   confirmation read exactly this: in `CheckerS.c`'s `checkDefnValP` the three
   `(coreKnotI fe checkFuel)` uses are CSE'd into one record, destructured and
   `lean_dec_ref`'d immediately; the last `fe`-capturing closure is consumed on the
   next line; `FEnv_push(fe, …)` receives `fe` with **no surviving `lean_inc_ref`**
   — the insert mutates in place. Also useful for confirming a `foldlM` really
   compiled to a unique-threading tail loop.
3. **Profile symbols.** `perf record` / Samply: a tower of
   `lean_copy_expand_array`, `lean_array_push`, `lean_del_core`,
   `lean_dec_ref_cold`, `lean_st_ref_set` at the top is lost linearity, not work.
4. **Runtime gadget.** Break on `lean_copy_expand_array_nonlinear` in gdb — the
   runtime's non-linearity hook — to catch the copies as they happen and count them
   per run.
5. **Attribute the holder, not the strike.** RC 2 discovered *at* a mutation was
   taken far away: `finish` out of the copy, then set hardware watchpoints on the
   fresh tables' refcount words and scan the heap for holders. Freed-but-unreused
   shells (shallow `lean_free_object` of destructured records) make post-hoc
   pointer scans lie — **only a watchpoint at the moment of the `inc` is
   conclusive.**
6. **Measure with `perf stat -e instructions:u`, median of 3**, with a per-shape
   startup baseline subtracted; wall-clock on a loaded machine is noise.

## 5. Two structural arguments that buy linearity for free

### 5.1 Snapshot / frozen-substrate

Read-only sharing is free: a frozen structure at RC 2 costs nothing because nobody
mutates it. The two-tier arena is built on this — `enableTierTwo` freezes tier one
and routes interns to tier two; `truncateTierTwo` drops tier two wholesale
(`Array.shrink 0`, keeping capacity) and clears the flag. A "snapshot" is then a
retained handle plus a pure header copy, and **RC death of the snapshot is
truncation** — no transport theory needed. (`DESIGN.md` "Two-tier arena
internals".)

### 5.2 The Bool barrier

If a per-item pipeline is split into an *install* phase (everything that produces or
stores state) followed by a *check* phase **whose result type is only
success/failure**, then at the moment the check phase ends *no live reference into
its temporaries can exist* — a phase returning a `Bool` cannot retain. That makes
dropping/truncating its allocations sound with no proof obligation, and it gives
you the pre-push value for free: the check phase receives the very pre-push `FEnv`
(the push happens after), so no counter-filtered view and no retained second map is
needed. Measured to add **zero** copies over the pre-split baseline.
(`DESIGN.md` "Driver split: install phase / Bool-barrier check phase".)

## 6. Codegen landmines (Nat arithmetic and initialization)

Evidence is `lean.h` at v4.33.0 — **re-check on toolchain bumps**; these are
implementation facts, not guarantees.

| Op | Codegen | Verdict |
|---|---|---|
| `Nat.shiftLeft` (`<<<`) | `LEAN_EXPORT lean_nat_shiftl` — **no** inline scalar fast path | avoid on hot paths |
| `Nat.shiftRight` (`>>>`) | `static inline` scalar fast path | fine |
| `Nat.land` (`&&&`), `Nat.lor` (`\|\|\|`), `Nat.xor` | `static inline` scalar fast paths | fine |
| `Nat.div`, `Nat.mod` | `static inline` scalar fast paths | fine (div/mod-by-2 decode is cheap) |
| `Nat.add`, `Nat.mul` | `LEAN_ALWAYS_INLINE` scalar fast paths | see mul caveat |

* **`<<<` is the expensive one.** In the #89 packed-keys experiment the shift form
  regressed every workload: init-prelude cert 26.6 G → 42.9 G instructions, recorded
  as **+55–73 %** at per-node frequency. Rewriting the lanes as `mul`/`add` Horner
  arithmetic fixed it (and is the omega-friendly form for injectivity proofs).
  Commit `878ecb3`; refined in `DESIGN.md` "Tag scheme decision". *Historical note:
  `878ecb3`'s message also called `lean_nat_lor` out-of-line; that is superseded —
  at v4.33.0 `lean_nat_lor` has a `static inline` scalar fast path and only
  `lean_nat_shiftl` is out-of-line.*
* **`Nat` literals ≥ 2^32 compile to a runtime decimal parse.** The emitter uses
  `lean_unsigned_to_nat(n)` up to `2^32 - 1` and `lean_cstr_to_nat("…")` above it —
  a GMP string parse **at every evaluation of that literal expression**. Measured at
  5 % of the #89 probe (commit `4d60aca`). Fix: hoist the literal behind a top-level
  `def` (parsed once), e.g. `tierTag := 2^62` in `ConLeche/Kernel/IExpr.lean`.
  Separately, values above `LEAN_MAX_SMALL_NAT = SIZE_MAX >> 1 = 2^63 - 1` leave the
  tagged-scalar regime entirely and become MPZ allocations — keep computed keys
  below `2^63`.
* **`Nat.mul`'s overflow check is a hardware division.** `lean_nat_mul`'s scalar
  path is `r = n1*n2; if (r <= LEAN_MAX_SMALL_NAT && r / n1 == n2)`. Reading the
  source, prefer `p + p` to `2 * p` in per-node arithmetic (not separately measured
  here — worth a quick `perf stat` if it is in your inner loop).
* **Dense keys need a mixer.** Packed child indices cluster ~3× under the identity
  `Hashable Nat` even after Std's scramble (18.8 % of cycles in the intern
  bucket-chain walk). A `def` synonym of `Nat` with a `Hashable` that finalizes with
  one `UInt64` multiply + xor-shift restores uniform buckets, stays scalar at
  runtime, and adds no proof obligations (`4d60aca`).
* **0-ary closed `def`s run in the module initializer.** They are evaluated at
  process start whenever the module's object code is linked in. A closed parse of a
  1.96 MB embedded JSON cost **~0.26 G instructions at every process start** (twice,
  under the OOM supervisor re-exec). Fix: make it a *function* of its input, so it
  runs only where it is applied — closed subterms extracted from function bodies
  become lazy `once`-cells, so no eager work remains
  (`ConLeche/PinGen.lean:445-454`).

## 7. Checklist before landing a hot-path change

- [ ] No `for`/`mut` loop threads state on the hot path.
- [ ] Rare/conditional branches decided *before* the expensive step they'd straddle.
- [ ] No pure state read whose result is first used after an intervening call
      (else `@[noinline]` the reader).
- [ ] No closure-capturing record built before a long call that ends in a mutation
      of the captured value.
- [ ] Read-only traversal parameters borrowed (`@&`).
- [ ] Per-node arithmetic free of `<<<` and of `Nat` literals ≥ 2^32.
- [ ] Linearity verified by probe counts **against an identically-probed baseline**,
      or by absence of `lean_inc_ref` before the mutation in the generated C.
- [ ] `perf stat -e instructions:u`, median of 3, startup-adjusted.
