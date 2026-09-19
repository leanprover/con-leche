# nanoclo — design study

Checkout: `_tmp/ref/nanoclo`, HEAD `4cdd12f`
("Deepen speculative comparisons iteratively along the unfold chain", 2026-09-09).
The arena runs `cdeb070` (2026-09-08); the two differ only in the speculation
escalation described in §4.6 plus a 31-bit index bound and a panic message
(`git diff --stat cdeb070 HEAD` touches `src/closure.rs`, `src/nbe.rs`,
`src/nbe_conv.rs`, `src/parser.rs`, `src/tc.rs`, 53 insertions).

All file:line citations are into that checkout unless stated otherwise.

**The headline finding, up front:** despite the name and the README's first
paragraph, **the conversion engine at HEAD is not the closure machine — it is
normalisation by evaluation over an interned value graph**, adopted wholesale
from sokonanoda in a series of commits on 2026-08-10 that ends with
`cdcb24d "Delete the closure conversion machine"`. What survives of the
delayed-substitution idea is (a) the *interned environment* data structure,
which the value evaluator reuses as its own environment, and (b) *inference*,
which still runs on closures and still delays substitution. So nanoclo is
"sokonanoda's conversion + nanoclo's inference + nanoda's inductive
installer", not "nanoda with a closure-based whnf".

---

## 1. Overview and layout

### 1.1 Crate layout

Single Rust crate, edition 2021, one binary (`src/main.rs`) and a library
(`src/lib.rs`). Dependencies (`Cargo.toml:16-29`): `smallvec`, `stacker`,
`mimalloc` (set as `#[global_allocator]`, `src/main.rs:1-2`), `indexmap`,
`rustc-hash`, `hashbrown`, `num-bigint`/`num-integer`/`num-traits`, `semver`,
`serde`/`serde_json`. Release profile is `opt-level=3`, `lto=true`,
`overflow-checks=true` (`Cargo.toml:9-14`).

Module map, line counts (`wc -l src/**/*.rs`, 13284 total):

| file | lines | role |
|---|---|---|
| `src/parser.rs` | 1691 | export-file parser, with a hand-written byte-match fast path |
| `src/inductive.rs` | 1757 | inductive/recursor generation + validation (pure syntax; from nanoda) |
| `src/nbe_eval.rs` | 1301 | NbE evaluator, whnf, iota, Nat/String acceleration, readback, value typing |
| `src/util.rs` | 1087 | `Ptr`, `LeanDag` (the interning arenas), `TcCtx`, `Config`, Nat primitives |
| `src/closure.rs` | 1036 | interned environments, jump-pointer lookup, read sets/views, `reify`, `eq_mod` |
| `src/pretty_printer.rs` | 952 | pretty printer (not on the checking path) |
| `src/tc.rs` | 929 | `TypeChecker`, drivers, `infer_*` on closures, `def_eq`/`whnf` entry points |
| `src/expr.rs` | 763 | `Expr`, `inst`, `abstr`, smart constructors |
| `src/nbe_conv.rs` | 685 | conversion (unification) on values |
| `src/nbe.rs` | 539 | value/spine arenas and intern tables |
| `src/env.rs` | 332 | `Declar`, `Env`, visibility cutoff |
| `src/level.rs` | 307 | universe levels: simplify, leq, antisymm |
| `src/quot.rs` | 274 | `Quot` primitive installation |
| `src/debug_printer.rs`, `src/name.rs`, `src/unique_hasher.rs` | 216/91/41 | support |
| `src/tests/*` | 1174 | unit tests (level algebra, names, Nat literal ops) |

There are also 12 hand-written perf regressions under `tests/perf/*.lean`
(`beta-ladder`, `let-ladder`, `church-numerals`, `discarded-argument`,
`args-before-unfold`, `shared-subterm`, `folded-constant`,
`unroll-versus-evaluate`, `refute-cheap-first/last`, `repeated-subproblem`,
`identical-nesting`), which are exactly the names quoted in the commit
messages as instruction-count measurements.

`src/lib.rs:8-25` declares the module list; note `nbe`, `nbe_conv`, `nbe_eval`
are `pub(crate)` while `closure` is `pub`. `src/lib.rs:27` sets
`STACK_SIZE = 1 << 30` (1 GiB) — every checking thread is spawned with it
(`src/tc.rs:143-146`, `src/tc.rs:211-213`).

### 1.2 README design section (verbatim, `README.md:5-11`)

> Terms in flight are closures: an expression paired with an interned
> environment. Entering a binder extends the environment in O(1), a variable
> occurrence reads its entry through skew-binary jump pointers in O(log i),
> and substitution into a body happens only when a type crosses back out of
> the checker. On a spine of n binders whose variables are read far below
> them, checking costs O(n) where substituting into the body at each binder
> costs O(n²); the `beta-ladder` and `let-ladder` tests in the Lean Kernel
> Arena measure exactly this.
>
> Inference remembers the type of a term against the bindings that term
> reads, rather than against the whole environment it stood in. A subterm the
> proof reaches along many branches then asks one question whenever those
> branches agree on the bindings it names, whatever else they bind: checking
> `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective` reaches one
> such subterm under 543 binder telescopes that differ only outside it, and
> infers it once rather than 543 times.
>
> Conversion evaluates both sides into a graph of interned values, unified by
> one match per pair: a value names its construction, so two equal terms
> reached twice compare as integers, an argument evaluates at most once
> through its thunk, and a constant unfolds at most once per instantiation. A
> delayed argument is named by the bindings it reads rather than by the
> environment it sits in, so `f x` reached under two environments that agree
> on `f` and `x` is one thunk however the rest of those environments differ,
> and the two occurrences evaluate once between them. Comparing the arguments
> of two applications of one constant is speculative, and one budget of
> conversion steps covers a comparison and everything it nests; a comparison
> that exhausts it is abandoned for the unfolding route, so a mistaken bet
> costs a constant rather than an asymptotic factor.
>
> The value representation, the conversion algorithm, and the fast path of the
> export parser come from sokonanoda (Apache-2.0), whose normalisation by
> evaluation follows smalltt. The closure machinery above is nanoclo's own.

### 1.3 Design history from the git log

The repository's history is truncated at 50 commits (`git log --oneline | wc -l`
= 50); the root commit `7e977ad "Keep the core module's name"` already refers
to "the original port", so the fork's own prehistory (the closure port on top
of nanoda_lib) is not in this checkout. Two named ancestors appear in the
messages: `9c08a4d "Rename to nanoclo"` explains the previous name —

> GHC's rapier delayed substitution behind unique names and an in-scope set,
> and rebuilt terms as it went. Nothing of that is left here: a term in flight
> is a closure over an interned environment, de Bruijn indices need no
> freshening, and reification happens only at a type boundary. … nanoclo is
> nano plus closures

The arc of the visible history, in order:

1. **2026-08-07/08 — closure era polish.** `653e555` removes a pre-descent
   structural sweep; `80dafab` memoises proof irrelevance on "the head, its
   environment and the arity" (church-numerals 96M → 81M instructions);
   `afcba7a` deletes the nanoda functions the closure core replaced.
2. **2026-08-10 — the NbE takeover, one commit per step.** `1af0f57`
   "Resurrect the value-mode conversion behind NANOCLO_NBE" brings the three
   `nbe*` modules back "from the history that 07eb000 deleted, unchanged",
   costing 37% on bitvec because of boundary translation. `d407622`
   "Evaluation reads the checker's environments" deletes the parallel value
   environment: `Entry` gains a `V(ValId)` case. `8baf6ca` "Inference consumes
   values; conversion is unconditionally value-mode" removes the flag.
   `cdcb24d` **"Delete the closure conversion machine"** — "def_eq evaluates
   both sides and unifies the values; the whnf machine, lazy delta, eq_mod's
   callers among them, the speculative fuel of the closure world and the
   closure def-eq caches are gone. What remains of closure.rs serves
   inference: environments, lookup, reify, and the projection that normalizes
   an entry before it is interned."
   Then a tuning run: `f329f4e` (drop the eval memo — values already share),
   `fa5b03d` (drop stacker probes; 1 GiB stacks), `3b5237c` (def-eq roots
   memoise their value; spine unification walks interned nodes in place),
   `c7a3a30` (a whole application chain evaluates as one step),
   `f73e321` (one hash probe per construction), `97f5cb9` (byte-match parser
   fast path, "parsing was 13% of the bitvec run against 4% in sokonanoda").
3. **2026-08-11 — the read-set/view machinery, nanoclo's own contribution.**
   `f9b137f` "Read sets stay exact past one word", `a8d3067` "Read sets live as
   long as the expressions they describe", `a54f726` "Thunks are shared across
   environments agreeing on what a term reads", `fffe293` "A view is built once
   per set and environment", `f07f79e` "Spine interning keys applications by
   (parent, value)". These carry the biggest measured wins (see §5.3).
   `e021753` then drops the syntactic `eq_mod` front from `is_def_eq`
   ("Every closure pair the front answered, the value graph answers from the
   memo it already fills, at the same cost").
4. **2026-09-08/09 — soundness and speculation.** `cdeb070` rejects orphan
   recursors (ports nanoda_lib `f04456a3`/`8a327a18`); `9047474` lifts the
   export-index guard to 2^31; `4cdd12f` makes an aborted speculative
   comparison hand double its budget to the next probe down the unfold chain
   — "One comparison in the FLT export needs ~10^7 steps; restarting it from
   zero every 4096 steps kept the checker on one theorem for 13 hours. With
   the deepening the theorem checks in 0.25s."

---

## 2. The term representation

### 2.1 The syntactic type

`src/expr.rs:19-100`, verbatim (abridged of doc comments):

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<'a> {
    StringLit { hash: u64, ptr: StringPtr<'a> },
    NatLit    { hash: u64, ptr: BigUintPtr<'a> },
    Proj { hash: u64, ty_name: NamePtr<'a>, idx: usize, structure: ExprPtr<'a>,
           num_loose_bvars: u16, has_fvars: bool },
    Var  { hash: u64, dbj_idx: u16 },
    Sort { hash: u64, level: LevelPtr<'a> },
    Const{ hash: u64, name: NamePtr<'a>, levels: LevelsPtr<'a> },
    App  { hash: u64, fun: ExprPtr<'a>, arg: ExprPtr<'a>,
           num_loose_bvars: u16, has_fvars: bool },
    Pi   { hash: u64, binder_name: NamePtr<'a>, binder_style: BinderStyle,
           binder_type: ExprPtr<'a>, body: ExprPtr<'a>,
           num_loose_bvars: u16, has_fvars: bool },
    Lambda { /* same shape as Pi */ },
    Let  { hash: u64, binder_name: NamePtr<'a>, binder_type: ExprPtr<'a>,
           val: ExprPtr<'a>, body: ExprPtr<'a>,
           num_loose_bvars: u16, has_fvars: bool, nondep: bool },
    Local { hash: u64, binder_name: NamePtr<'a>, binder_style: BinderStyle,
            binder_type: ExprPtr<'a>, id: FVarId },
}
```

- **Bound variables are de Bruijn indices** (`Var { dbj_idx: u16 }`), so at
  most 65535 open binders.
- **Free variables are `Local` nodes carrying their own binder type**
  (`src/closure.rs:6-8`: "Free variables are nanoda `Local` expressions
  carrying their binder type, so no separate local context is needed").
  Their identity (`src/expr.rs:103-108`):

```rust
pub enum FVarId {
    DbjLevel(u32),
    Unique(u32),
}
```

  The checking path uses `DbjLevel` exclusively (`fvar_at`,
  `src/closure.rs:602-605` → `TcCtx::remake_dbj_level`, `src/util.rs:729-739`);
  `Unique` survives for the inductive installer.
- Every node caches `num_loose_bvars: u16` and `has_fvars: bool`
  (`src/expr.rs:738-758`), which is what makes "is this subterm closed?" O(1)
  — the pivot of the whole design.
- Literals are separate constructors holding pointers to interned `BigUint`
  and `Cow<str>` (`Nat`/`String` kernel extensions, off by default,
  `src/util.rs:965-969`).
- Projections carry the structure's *name* and a 0-based field index
  (params excluded).

### 2.2 Allocation, hashing, interning

There is no `Rc`/`Arc` on terms and **no `unsafe` anywhere in the crate**
(`grep -rn unsafe src/` hits only the config option `unsafe_permit_all_axioms`
and the export's `is_unsafe` field). Everything is an index:

```rust
pub struct Ptr<A> { raw: u32, ph: PhantomData<A> }    // src/util.rs:40-44
const TC_BIT: u32 = 1 << 31;                          // src/util.rs:47
```

Bit 31 selects one of two arenas, bits 0–30 the index
(`src/util.rs:34-68`). The two arenas are `LeanDag`s (`src/util.rs:769-777`):

```rust
pub struct LeanDag<'a> {
    pub names:   UniqueIndexSet<Name<'a>>,
    pub levels:  UniqueIndexSet<Level<'a>>,
    pub exprs:   UniqueIndexSet<Expr<'a>>,
    pub uparams: FxIndexSet<Arc<[LevelPtr<'a>]>>,
    pub strings: FxIndexSet<CowStr<'a>>,
    pub bignums: Option<FxIndexSet<BigUint>>,
}
```

`IndexSet`s, i.e. **every term is hash-consed on construction**: `alloc_expr`
(`src/util.rs:481-511`) probes the long-lived export dag first and falls back
to the per-context scratch dag, skipping the export probe when a child already
lives in the scratch dag (an export node can never point into scratch). So
`ExprPtr` equality *is* structural equality, and `Ptr::get_hash` is just the
raw u32 (`src/util.rs:67`). Each node also stores its own precomputed 64-bit
hash (`hash64!` macro, `src/util.rs:99-111`); `Hash for Expr` writes only that
(`src/expr.rs:127-129`), and `UniqueHasher` (`src/unique_hasher.rs`) passes it
through.

The scratch dag is per `TcCtx`, i.e. per checking thread, reset per
declaration — except in the serial driver, where `persist_dag` keeps it across
declarations with a 2^22-expression epoch bound (`src/util.rs:346-364`, commit
`fa67854`). Soundness argument given there: declarations are checked in export
order, so anything visible when an entry was made precedes every later
declaration.

`Levels` (universe argument lists) are interned as `Arc<[LevelPtr]>`
(`src/util.rs:82`) — the only `Arc` on the hot path, and `read_levels` clones
it (`src/util.rs:449-454`), an atomic refcount bump per read.

---

## 3. The closure / delayed substitution

### 3.1 What a closure is

```rust
pub(crate) type EnvId = u32;                       // src/closure.rs:18
pub(crate) const ENV_NIL: EnvId = 0;               // src/closure.rs:19

pub(crate) struct Clo<'t> { pub e: ExprPtr<'t>, pub env: EnvId }   // 45-49
```

An expression pointer plus an environment id. The environment is a persistent
cons-list in an arena (`src/closure.rs:35-43`):

```rust
pub(crate) struct EnvNode<'t> {
    pub(crate) entry: Entry<'t>,
    pub(crate) parent: EnvId,
    pub(crate) len: u32,
    /// one past the highest de Bruijn level bound anywhere in this chain
    pub(crate) next_level: u32,
    /// Myers jump pointer for O(log n) indexing
    pub(crate) jump: EnvId,
}
```

with three kinds of entry (`src/closure.rs:26-33`):

```rust
pub(crate) enum Entry<'t> {
    Val(ExprPtr<'t>, EnvId),   // a delayed substitution: another closure
    Neu(ExprPtr<'t>),          // the `Local` expr standing for an opened binder
    V(crate::nbe::ValId),      // an already-evaluated value (pushed by the NbE side)
}
```

So **closures nest**: an environment entry is itself a closure `(e, env)`, and
the environment it points at may be any other environment in the arena. There
is no separate "value" in the closure world — `Entry::V` is the bridge to the
NbE value arena added by commit `d407622`.

### 3.2 Interning and O(1) extension

`push_entry` (`src/closure.rs:368-414`) is the only way to extend. The
extension request is packed into two words and looked up in `env_intern`:

```rust
fn pack_entry_key(env: EnvId, entry: Entry) -> (u64, u64) {   // src/closure.rs:65-72
    match entry {
        Entry::Val(e, venv) => ((env as u64) << 32 | e.get_hash(), (venv as u64) << 1 | 1),
        Entry::Neu(e)       => ((env as u64) << 32 | e.get_hash(), 0),
        Entry::V(v)         => ((env as u64) << 32 | v as u64, 2),
    }
}
```

Hence "O(1) binder entry extension": one hash probe, one `Vec::push`, no
copying — and, because it is a *hash-consed* cons, **the same extension built
twice is the same `EnvId`**, so every cache keyed on an environment hits across
paths. `push_entry` first normalises the entry (`src/closure.rs:369-381`):

> The entry is part of the identity of every environment built on top of it, so
> it enters in normal form: a value that reads nothing from its own environment
> carries none, and a value that is a variable is replaced by what that variable
> stands for. Without this, one binding reached along two paths yields two
> environments and splits every cache keyed on them.

(`norm_clo`, `src/closure.rs:802-816`, which chases bvar→`Val` chains via
`chase`, `src/closure.rs:1013-1035`, and drops the environment of a closed term.)

`push_entry_v` (`src/closure.rs:343-366`) is the specialised version for an
evaluated entry: "Everything the new node holds comes from the parent node, so a
miss costs one probe."

### 3.3 The jump pointers

Built in `push_entry`/`push_entry_v` (`src/closure.rs:398-406`):

```rust
// Myers jump: if dist(parent) == dist(parent.jump), jump to parent.jump.jump
let p = &self.ctx.rp.envs[env as usize];
let jump = {
    let d1 = p.len - self.ctx.rp.envs[p.jump as usize].len;
    let j = &self.ctx.rp.envs[p.jump as usize];
    let d2 = j.len - self.ctx.rp.envs[j.jump as usize].len;
    if d1 == d2 { j.jump } else { env }
};
```

This is Myers' applicative stack / skew-binary jump list: a node's `jump`
either doubles the previous skip or falls back to the parent. Lookup
(`src/closure.rs:569-593`):

```rust
pub(crate) fn lookup(&self, env: EnvId, i: u16) -> Entry<'t> {
    let len = self.env_len(env);
    assert!((i as u32) < len, "loose bvar: …");
    let mut cur = env;
    let target = len - 1 - i as u32;
    loop {
        let n = &self.ctx.rp.envs[cur as usize];
        if n.len == target + 1 { return n.entry; }
        let j = &self.ctx.rp.envs[n.jump as usize];
        if j.len > target { cur = n.jump; } else { cur = n.parent; }
    }
}
```

O(log i) node reads for index `i`, each read being one `Vec` index — no
pointer chasing through heap cells, and (important for a Lean port) **no
mutation**: the jump field is computed once at construction from the parent.

Note the `assert!` on an out-of-range index: an environment shorter than the
term's de Bruijn range is a hard panic, which is how a mis-projected key is
caught (see §3.5).

### 3.4 When substitution is forced

There is never a general `instantiate` on the checking path. `reify`
(`src/closure.rs:818-876`) is the only place a closure becomes an expression:

```rust
pub(crate) fn reify(&mut self, c: Clo<'t>) -> ExprPtr<'t> {
    if c.env == ENV_NIL || self.lbr(c.e) == 0 { return c.e; }
    self.reify_go(c.env, 0, c.e)
}
```

`reify_go` walks the term with an offset for binders crossed, replacing a
loose `Var` by its entry (a `V` entry goes through `nb_readback`,
`src/closure.rs:844`), and memoises on `(e, env, offset)` in a two-generation
table. The call sites are few and all at *boundaries*:

- `infer` at the top (`src/tc.rs:326-329`) — the public `ExprPtr → ExprPtr`
  inference used by the inductive installer;
- `infer_lambda`, where the inferred body type has to be abstracted over the
  fvars just opened (`src/tc.rs:687-690`, "this is one of the places
  reification stays");
- `infer_pi`/`infer_let`/`infer_proj`, to get a binder domain as an expression
  (`src/tc.rs:704`, `src/tc.rs:722`);
- `nb_readback` on a `Thunk` or `Lam`/`Pi` value (`src/nbe_eval.rs:1036-1054`);
- the argument-type check when the syntactic front fails (`src/tc.rs:780`).

`Expr::inst` (`src/expr.rs:157-210`) and `abstr` (`src/expr.rs:288-337`) still
exist, and **`inst` is called only from `src/inductive.rs`** (~20 sites, e.g.
`src/inductive.rs:432,459,763,887,1079`); `abstr_levels_at`
(`src/expr.rs:274-281`, over `abstr_aux_levels`, `src/expr.rs:225-270`) is the
one used by `infer_lambda`.

### 3.5 Closing over a free variable: how `abstract` interacts

Free variables are named by **de Bruijn level, not by a counter**
(`src/closure.rs:596-605`):

> The free variable standing for a binder opened over an environment of `level`
> entries. Naming it by that level, rather than by a counter, makes two openings
> of the same binder produce the same variable, so the closures, environments and
> cache keys built on top of it coincide instead of being fresh every time. The
> binder type is part of the variable's identity, so a level shared by two
> binders of different types still gives two variables.

The level to use is `next_level(e, env) = max_level(e).max(env.next_level)`
(`src/closure.rs:337-340`), where `max_level` scans the expression for the
highest `DbjLevel` occurring in it, memoised in `lvl_cache`
(`src/closure.rs:307-335`). So a binder is opened at a level nothing already in
scope can collide with, and — crucially — *deterministically*, so hash-consing
works across independent visits. `abstr_aux_levels` then re-binds every level
≥ `start_pos` seen from under `num_open_binders` binders
(`src/expr.rs:225-270`), memoised on `(e, start, open)`.
`infer_lambda` opens a whole run of binders before inferring the body, "so the
fvars standing for them are abstracted out of the inferred type in one
traversal rather than one traversal per binder" (`src/tc.rs:660-698`).

### 3.6 Read sets and views — nanoclo's own idea

The thing the README's second paragraph is about. A closure `(e, env)` only
*reads* some of `env`; two closures agreeing there should share cache entries.
`Uses` (`src/closure.rs:73-88`):

```rust
pub(crate) enum Uses {
    Dense,        // every index below the term's range — projection is the identity
    Mask(u64),    // exact, fits a word
    Wide(u32),    // exact, interned word vector, up to MAX_USES_WORDS = 8 words
    Deep,         // past that bound: key on the whole environment
}
```

`uses_mask` (`src/closure.rs:420-467`) computes it bottom-up — "Union at an
application is a bitwise or and passing a binder is a shift, both constant
time" — memoised in `umask_cache`, whose lifetime is the *dag's*, not the
declaration's (commit `a8d3067`: recomputing them per declaration made
`uses_mask` 7.4% of cut_afftrans).

Two consumers:

- **`key(c)`** (`src/closure.rs:709-726`) → `project`/`project_wide`
  (`src/closure.rs:728-793`): rebuilds a *fresh minimal environment* from the
  read entries, so environments agreeing there become literally the same
  `EnvId`. Used to key the infer caches (`src/tc.rs:602-604`). If the set names
  an entry the environment lacks, the whole environment is returned — "a
  coarser key rather than a wrong one, and a term whose variables really do
  escape is caught by `lookup`".
- **`read_key(e, env)`** (`src/closure.rs:619-628`) → `view_of_mask` /
  `view_of_wide` / `intern_view` (`src/closure.rs:633-702`): interns the
  *list of picked entries* whole as a "view" id, tagged with
  `VIEW_BIT = 1<<31` so it can sit in an `EnvId`-shaped key slot without
  colliding. This is what thunks are interned under (`nb_thunk`,
  `src/nbe_eval.rs:160-164`), giving the README's "`f x` reached under two
  environments that agree on `f` and `x` is one thunk".

`MAX_USES_WORDS = 8` is deliberately a *value* bound, not a cost bound
(`src/closure.rs:90-98`, commit `554586c`): a set of n positions costs one
environment rebuilt from n entries at every node that asks for a key, which on
a ladder of n binders each reading its predecessors is quadratic; measured,
lifting the bound to 16384 bits takes n=1000/2000/4000 to 176M/625M/2213M
instructions, 3.54× per doubling, 43.65% of it rebuilding environments.

### 3.7 `eq_mod`: syntactic equality modulo delayed substitution

`src/closure.rs:879-995`. Compares `(ae, aenv, aoff)` against
`(be, benv, boff)` structurally, resolving bvar heads through their entries,
with a canonical (symmetric) memo key packing all six arguments and a
`composite` predicate deciding whether an entry is worth storing. A `V` entry
met on either side answers `false` immediately (`src/closure.rs:890,898`) —
the closure world cannot see into the value world.

Commit `e021753` removed its use as the front of `is_def_eq`; it survives at
exactly one hot site, the argument-type check in `infer_s`
(`src/tc.rs:776-786`), where it answers before any value is built and falls
through to the value engine when it fails.

---

## 4. whnf and definitional equality — on **values**, not closures

### 4.1 The value representation (`src/nbe.rs`)

```rust
pub(crate) type ValId  = u32;
pub(crate) type VEnvId = crate::closure::EnvId;   // literally the checker's environments
pub(crate) type SpineId = u32;                    // src/nbe.rs:22-31

pub(crate) enum RigidHead<'t> {                   // src/nbe.rs:49-56
    BVar(u32, ValId),                 // opened binder: de Bruijn LEVEL + its type value
    Local(ExprPtr<'t>),               // free variable from the surrounding declaration
    Const(ConstKind, NamePtr<'t>, LevelsPtr<'t>),
}
pub(crate) enum Elim<'t> {                        // src/nbe.rs:60-63
    App(ValId),
    Proj { ty_name: NamePtr<'t>, idx: usize },
}
pub(crate) enum Value<'t> {                       // src/nbe.rs:66-99
    Rigid  { head: RigidHead<'t>, spine: SpineId },
    Unfold { name: NamePtr<'t>, levels: LevelsPtr<'t>, spine: SpineId, forced: Option<ValId> },
    Lam { binder_name, binder_style, binder_type: ExprPtr<'t>, domain: Option<ValId>,
          env: VEnvId, body: ExprPtr<'t> },
    Pi  { binder_name, binder_style, domain: ValId, env: VEnvId, body: ExprPtr<'t> },
    Sort   { level: LevelPtr<'t> },
    NatLit { ptr: BigUintPtr<'t> },
    StrLit { ptr: StringPtr<'t> },
    Thunk  { env: VEnvId, expr: ExprPtr<'t>, forced: Option<ValId> },
}
```

This is "glued" NbE in the smalltt style: `Unfold` is a constant application
kept folded with a `forced` slot; `Lam`/`Pi` bodies are *closures over the
checker's own interned environment*; `Thunk` is a delayed argument with a
`forced` slot. Values live in `Vec<Value>` and are **interned on construction**
(`mk_rigid`, `mk_unfold`, `mk_lam`, `mk_pi`, `mk_sort`, `mk_nat`, `mk_str`,
`mk_thunk_keyed` — `src/nbe.rs:391-523`), so `ValId` equality is "these two
values have the same construction history", checkable as an integer compare.
Spines are interned cons-lists too, with a separate table per elimination kind
(`spine_snoc`, `src/nbe.rs:310-341`; commit `f07f79e`).

`Lam`'s domain is stored *unevaluated* (`binder_type: ExprPtr`) with a lazy
`domain: Option<ValId>` filled by `nb_lam_domain` (`src/nbe_eval.rs:339-353`);
`Pi`'s domain is a `ValId` (delayed as a thunk at construction,
`src/nbe_eval.rs:120-123`).

### 4.2 Evaluation (`nb_eval`, `src/nbe_eval.rs:54-146`)

One match on the expression node (the node is read once — commit `3148b8e`),
with `env` reset to `VENV_NIL` when the node is closed:

- `Var` → `lookup` the entry, turn it into a value (`entry_val`,
  `src/nbe_eval.rs:167-176`: a `V` is itself, a `Val(e,env)` becomes a thunk, a
  `Neu(fv)` becomes a `Rigid{Local}`), then force it.
- `App` → **the whole application chain at once** (commit `c7a3a30`): collect
  the arguments, evaluate the head, and when the head is stuck (`Rigid`, or
  `Unfold` that is not a Nat primitive), push *all* remaining arguments onto
  its spine in one go and intern one value. Otherwise apply one at a time.
- `Lambda` → `mk_lam(.., env, body)`: **no substitution, the environment is
  captured**.
- `Pi` → domain delayed via `nb_delay`, body captured.
- `Let` → the value is evaluated *eagerly* and pushed with `push_entry_v`,
  looping over a run of `Let`s (`src/nbe_eval.rs:124-132`).
- `Proj` → evaluate the structure, then `nb_proj`.

`nb_delay` (`src/nbe_eval.rs:148-158`) evaluates anything already in normal
form (var, sort, literal, local, const) and thunks only composites — "a thunk
over it would cost more than the value".

**Beta extends the environment**: `nb_apply` on a `Lam` does
`push_entry_v(env, a)` then `nb_eval` of the body (`src/nbe_eval.rs:240-244`).
On a `Rigid`/`Unfold` it extends the spine.

**Delta**: `nb_unfold_const(name, levels)` (`src/nbe_eval.rs:449-485`)
level-substitutes the definition body and evaluates it **under the empty
environment**, memoised on `(name, levels)`; the level-instantiated *expression*
is additionally shared through `rp.g_unfold`, a cache that lives with the
scratch dag and thus (serial driver) across declarations. The spine is then
replayed on the head value and the result written into the `Unfold` node's
`forced` slot (`nb_unfold_go`, `src/nbe_eval.rs:410-446`), so a constant
application unfolds at most once.

**Iota**: `nb_iota` (`src/nbe_eval.rs:487-496`) memoises both "it fired, here" and
"it is stuck" on the value id. `nb_fire_recursor` (`src/nbe_eval.rs:572-635`)
whnfs the major premise, tries K-reduction (`nb_k_reduce`,
`src/nbe_eval.rs:713-746`), structure eta (`nb_struct_eta_reduce`,
`src/nbe_eval.rs:751-805`), and Nat-literal recursion (`nb_nat_rec`,
`src/nbe_eval.rs:637-679`), then looks up the rec rule (memoised on
`(rule.val, levels)`) and applies prefix/fields/indices. Quotient elimination is
a case of the same function (`nb_fire_quot`, `src/nbe_eval.rs:528-566`).

`nb_whnf` (`src/nbe_eval.rs:369-392`) is a small loop: force, unfold if
`Unfold`, iota if a recursor/quot head, else stop. It is the only place
`stacker::maybe_grow` is used.

### 4.3 The conversion algorithm (`src/nbe_conv.rs`)

`nb_unify::<RIGID>` (`src/nbe_conv.rs:60-79`) in order:

1. force both sides;
2. **`if x == y { return true }`** — integer comparison of interned ids. The
   module header says this "settles every pair that shares any construction
   history: the same definition unfolded twice, the same argument evaluated
   under two spellings of one environment, the same recursor step reached along
   two routes";
3. speculation budget check (§4.6);
4. `nb_unify_cached` (`:81-117`): if either side `is_cacheable` (a Pi, Lam,
   Unfold, or recursor/quot-headed rigid — `:26-37`), consult `conv_pos` /
   `conv_neg` keyed by the ordered pair of `ValId`s. Negative caching is
   suppressed when either side is a `Lam` (eta may still save it) and when the
   comparison is speculative (a separate `conv_neg_probe` set, cleared with the
   guess);
5. `nb_unify_go` (`:119-154`): Nat rule → String rule → `nb_unify_direct` →
   (if RIGID) proof irrelevance → eta for a lambda against a non-lambda →
   structure eta.

`nb_unify_direct` (`:156-292`) is one `match` on the pair:

- Sort/Sort → `eq_antisymm` on levels;
- NatLit/NatLit, StrLit/StrLit → pointer equality (literals are interned);
- **Pi/Pi and Lam/Lam** → compare domains, then open both with **one shared
  fresh variable** `mk_bvar(depth, dom)` and recurse at `depth+1`
  (`:161-181`). `mk_bvar` interns on `(level, type value)`
  (`src/nbe.rs:407-409`), so two openings of the same binder are the same
  variable — the value analogue of §3.5;
- Rigid/Rigid → if either head is a recursor/quot, go to `nb_unify_iota`;
  else if either head is a `Const`, require matching name+levels and compare
  spines; else `head_eq` (BVar level equality / Local pointer equality) and
  spines;
- **Unfold/Unfold** (`:196-235`) — the lazy-delta core: if names+levels match,
  first try the **speculative spine probe**; then proof irrelevance; then, if
  heads match, unfold both; otherwise compare `ReducibilityHint`s
  (`nb_hint`, `:440-445`) and unfold the one "nearer the leaves", "so the two
  meet at a shared subterm rather than at normal forms";
- Unfold vs anything → unfold it (with `nb_unfold_demand` as a last resort,
  which forces even a Nat primitive that would rather stay folded);
- recursor-headed rigid vs anything → iota it.

Note what is **absent** relative to Lean's kernel: there is no separate
`whnf_core`/`lazy_delta` pair, no `Expr`-level structural equality pass, and no
pointer-equality shortcut *other than* value-id equality (which subsumes it).

### 4.4 How two closures with different environments are compared

They are not, at conversion time — both sides are *evaluated* first
(`is_def_eq`, `src/tc.rs:609-613`):

```rust
pub(crate) fn is_def_eq(&mut self, t: Clo<'t>, s: Clo<'t>) -> bool {
    self.ctx.rp.ctrs[3] += 1;
    let a = self.nb_of_clo(t);
    let b = self.nb_of_clo(s);
    self.nb_conv(0, a, b)
}
```

`nb_of_clo` (`src/tc.rs:539-546`) memoises `(ExprPtr, EnvId) → ValId` in
`clo_val_cache`, populated **only at def-eq entry points** (commit `3b5237c`:
"A def-eq entry point is where one repeated term would rewalk its whole
skeleton"). Differences in environment are then absorbed by value interning:
the same argument under two spellings of one environment is one thunk (because
the thunk keys on the *read view*, §3.6), hence one `ValId`, hence step 2 of
`nb_unify` settles it.

### 4.5 Proof irrelevance, eta, structures

- `nb_proof_irrel` (`:454-476`): both sides must be `Rigid`/`Unfold` (or a
  lambda, handled pointwise by `nb_proof_irrel_lam`, `:478-486`); infer both
  types as *values* (`nb_type`, memoised per value), test each is a Prop
  (`nb_type_level` → `is_zero`), then unify the two types. It is tried at
  several points inside `nb_unify_direct`, not just once at the top.
- Eta for functions: `nb_unify_go:131-149`, only when exactly one side is a
  `Lam`.
- Structure eta: `nb_struct_eta` (`:508-537`) — for each side, infer its type,
  whnf, check it is an inductive; a "unit-like" structure (one constructor, no
  fields) answers `true` outright; otherwise `nb_eta_struct` (`:541-568`)
  compares each constructor field against the corresponding projection.
- A structure whose universe *may* be zero is left alone
  (`nb_may_be_prop`, `:595-600`, used at `src/nbe_eval.rs:783-785`) — commit
  `39575e7`/`204b1dd` fixed exactly this: testing "is zero" instead of "may be
  zero" let an instantiation send a parameter to zero and meet an expanded
  proof where upstream met the premise.

### 4.6 The speculative comparison (`nb_spine_probe`)

The point: facing `f a =?= f b` for a definition `f`, comparing `a` against
`b` is a *guess* — they may differ while the applications are equal. nanoclo
runs the guess under a step budget (`src/nbe_conv.rs:366-406`):

```rust
fn nb_spine_probe(&mut self, depth: u32, sx: SpineId, sy: SpineId) -> bool {
    let key = if sx < sy { (sx, sy) } else { (sy, sx) };
    if self.ctx.nb.probe_fail.contains(&key) { … return false; }   // HEAD only
    let outer = self.ctx.nb.probe_depth == 0;
    let mut granted = 0;
    if outer {
        granted = if self.ctx.nb.probe_escalate > 0 {
            std::mem::take(&mut self.ctx.nb.probe_escalate)
        } else { SPEC_BUDGET };
        self.ctx.nb.probe_fuel = granted;
        self.ctx.nb.probe_aborted = false;
    }
    self.ctx.nb.probe_depth += 1;
    let r = self.nb_unify_spine::<true>(depth, sx, sy);
    self.ctx.nb.probe_depth -= 1;
    if self.ctx.nb.probe_depth == 0 {
        if !self.ctx.nb.conv_neg_probe.is_empty() { self.ctx.nb.conv_neg_probe.clear(); }
        if self.ctx.nb.probe_aborted { … probe_fail.insert(key);
            self.ctx.nb.probe_escalate = (granted * 2).min(1 << 20); return false; }
        if !r { self.ctx.nb.probe_fail.insert(key); }
    }
    r
}
```

`SPEC_BUDGET = 4096` (`src/tc.rs:16`). One budget covers the outermost probe
*and everything it nests*; `nb_unify` decrements `probe_fuel` and sets
`probe_aborted` when it hits zero (`src/nbe_conv.rs:67-77`). An abandoned
comparison records nothing positive; its negatives live in `conv_neg_probe`
and are discarded. Reduction itself is left unbounded, "since a truncated weak
head normal form would be recorded by the memos that reduction shares with
inference" (`src/tc.rs:456-467`).

What HEAD adds over the arena's `cdeb070` (commit `4cdd12f`): a `probe_fail`
set so a losing spine pair goes straight to the unfolding route next time, and
`probe_escalate`, which hands twice the grant to the probe the unfolding
launches next (capped at 2^20), cleared as soon as an unfold/iota pair
resolves. Quoted effect: "One comparison in the FLT export needs ~10^7 steps;
restarting it from zero every 4096 steps kept the checker on one theorem for
13 hours. With the deepening the theorem checks in 0.25s."

Measured frequency (commit `ea8744b`): "the budget stops 2 comparisons on
bitvec_lemmas and 1243 on cut_colim" — rare, but catastrophic when it matters.

### 4.7 Failure handling

There is none, in the graceful sense. Everything is `assert!`/`panic!`:
`assert_def_eq` (`src/tc.rs:355`), "application type mismatch"
(`src/tc.rs:800`), "function expected" (`src/tc.rs:765`), "invalid projection"
(`src/tc.rs:811-843`), `lookup`'s loose-bvar assert (`src/closure.rs:571-577`),
and a `panic!("native reduction (Lean.reduceBool/Lean.reduceNat) not
supported")` at the memoised point where a constant becomes a value
(`src/nbe_eval.rs:189-196`, commit `677d789`). A failed check aborts the
process; there is no reject/decline distinction.

---

## 5. Caching and sharing

### 5.1 Per-`TcCtx` (closure side, `CloState`, `src/closure.rs:100-148`)

| cache | key → value | lifetime |
|---|---|---|
| `env_intern` | `pack_entry_key(parent, entry)` → `EnvId` | declaration |
| `infer_cache_check` / `infer_cache_only` | `key(Clo)` (read-set–projected closure) → `Clo` | declaration |
| `reify_go_cache` | `(ExprPtr, EnvId, offset)` → `ExprPtr` | declaration, `Gen2` |
| `lvl_cache` | `ExprPtr` → max fvar level + 1 | declaration |
| `prop_cache` | type `ExprPtr` → is-a-Prop | declaration |
| `umask_cache` | `ExprPtr` → `Uses` | **dag** (survives declarations) |
| `proj_cache` / `proj_cache_w` | `(mask/wide-id, EnvId)` → projected `EnvId` | declaration |
| `view_cache` / `view_cache_w` | `(mask/wide-id, EnvId)` → view id | declaration, `Gen2` |
| `wide_uses` / `wide_intern` | word vectors ↔ ids | dag |
| `view_slices` / `view_table` | entry lists ↔ view ids (`hashbrown::HashTable`) | declaration |
| `eq_mod_cache` | packed canonical 6-tuple → bool | declaration, `Gen2` |
| `g_unfold` | const `ExprPtr` → level-instantiated body `ExprPtr` | dag |
| `g_inst_ty` | const `ExprPtr` → level-instantiated type `ExprPtr` | dag |

`Gen2` (`src/closure.rs:238-291`) is a two-generation memo: entries land in
`new`; at `CCAP = 1<<20` entries `new` becomes `old` and a fresh `new` starts;
a hit in `old` is promoted. So the tables are bounded but keep what is being
used.

`reset_decl` (`src/closure.rs:199-227`, `src/util.rs:158-190`,
`src/nbe.rs:239-292`) clears in place, keeping allocation up to a threshold —
commit `e5187b8`: "one context per thread and reset it before each
declaration, so a table grows to the size the largest declaration needs once,
instead of regrowing from empty for every declaration."

### 5.2 Per-`TcCtx` (value side, `Vals`, `src/nbe.rs:109-179`)

Intern tables: `spine_intern_app` `(SpineId, ValId)`, `spine_intern_proj`
`(SpineId, NamePtr, usize)`, `rigid_intern` `(RigidHead, SpineId)`,
`unfold_intern` `(Name, Levels, SpineId)`, `lam_intern`
`(binder_type ExprPtr, VEnvId, body ExprPtr)`, `pi_intern`
`(domain ValId, VEnvId, body ExprPtr)`, `sort_intern`, `nat_intern`,
`str_intern`, `thunk_intern` `(key_env, ExprPtr)` — note the thunk key is the
*read view*, not the environment (`mk_thunk_keyed`, `src/nbe.rs:503-523`).

Memos: `clo_val_cache` `(ExprPtr, VEnvId) → ValId` (def-eq roots only);
`unfold_cache`, `const_val_cache`, `const_ty_cache`, `const_lvl_cache`,
`rec_rule_cache`, `iota_cache`, `struct_eta_cache`, `open_cache`
(does an opened binder occur), `type_cache` `ValId → ValId`, `local_cache`.

Conversion results: `conv_pos`, `conv_neg`, `conv_neg_probe`, `probe_fail`.

All of these are cleared per declaration, since `ValId`s name arena positions
("values name arena positions, so nothing survives a declaration boundary",
`src/nbe.rs:237-238`). The intern tables are **preallocated at 2^14**
(`src/nbe.rs:186-190`, commit `1b1f6e7`: "table growth was 21% of
church-numerals").

Also global-ish: `expr_cache` in `TcCtx` (`src/util.rs:174-190`) holds
`inst_cache`, `abstr_cache`, `abstr_cache_levels`, `subst_cache`,
`dsubst_cache`, `simplify_cache` (level simplification memoised per pointer,
commit `f9d4e66`).

### 5.3 Measurements quoted in commit messages

Instruction counts (`perf stat`), in units of G (10⁹) for corpora and M for
the perf tests. Corpora referenced: `bitvec` (bitvec_lemmas), `colim`
(cut_colim), `cut_wt`, `afftrans` (cut_afftrans), `mathlib`.

- `f73e321` interning one probe: bitvec 183→171G, church 44→41M, shared-subterm 62→54M.
- `f329f4e` drop eval memo: bitvec 221→215G, church 53→48M ("the single-use inserts were 114M on bitvec at a 19% hit rate").
- `fa5b03d` no stacker probe: bitvec 215→206G, church 48→45M.
- `12d80f9` raw eq_mod key: bitvec 206→202G.
- `97f5cb9` parser fast path: bitvec 202→183G ("parsing was 13% of the bitvec run against 4% in sokonanoda").
- `3b5237c` def-eq root memo + in-place spine walk: church 40→36M, bitvec 171→167G.
- `c7a3a30` application chain as one step: bitvec 167→156G, shared-subterm 52→49M.
- `3148b8e` one node read: bitvec 156→154G.
- `f9d4e66` level simplify memo: bitvec 154→150G ("colim spends 9% of its run in level algebra where sokonanoda's simplify cache keeps it under 2%").
- `f9b137f` exact wide read sets: bitvec −2.3, colim −16.6, cut_wt −36.0, afftrans −40.7, mathlib −109.1 (G).
- `a8d3067` read sets live with the dag: bitvec −2.6 (101.0G), colim −19.8 (518.7G), cut_wt −32.4 (877.2G), afftrans −35.4 (971.5G) — "All four now below sokonanoda's 128.9, 559.4, 908.9 and 1000.9."
- `a54f726` thunks shared by read view: bitvec −6.5 (103.6G), colim −45.4 (538.5G), cut_wt −97.3 (909.6G), afftrans −123.3 (1006.9G), mathlib −276.2 (2430.1G); "colim RSS 2875 → 1786 MB".
- `f07f79e` spine interning split by kind: "spine_snoc runs 747M times on cut_wt against 613M spine extensions in sokonanoda at half the per-probe cost"; bitvec −1.5, colim −7.8, cut_wt −14.3, afftrans −16.5, mathlib −40.4 (G).
- `fffe293` view memo (the last commit quoting corpus numbers): colim −13.3 (505.5G), cut_wt −27.4 (850.0G), afftrans −30.2 (941.5G), mathlib −70.6 (2281.5G); "shared-subterm 47.9 → 48.6M, still under nanoda's 51.9 and sokonanoda's 55.1".

(Chronological order of the 2026-08-11 run is `f9b137f`, `f07f79e`, `a54f726`,
`a8d3067`, `1b1f6e7`, `554586c`, `fffe293`.) The last in-tree mathlib figure is
therefore **≈2281.5G instructions**, and the read-set/view family alone
(`f9b137f` + `a54f726` + `fffe293`) accounts for ~456G of the reduction.

Diagnostics: 26 counters in `CloState::ctrs` (`src/closure.rs:141-167`),
accumulated into process-wide atomics and dumped with `NANOCLO_CTRS`;
per-declaration dumps behind `NANOCLO_DECLCTRS`/`NANOCLO_DECLTIME`
(`src/tc.rs:147-186`).

---

## 6. Type inference / checking

**Inference runs on closures**, and (since commit `cef98ed`) *returns* a
closure: `infer_clo(Clo, InferFlag) -> Clo` (`src/tc.rs:595`). The `ExprPtr`
entry point just reifies (`src/tc.rs:326-329`).

`InferFlag` is `Check` or `InferOnly` (`src/tc.rs:30-33`) — the latter skips
the def-eq checks when the term is known well-typed.

`infer_go` (`src/tc.rs:615-680`) by case:

- `Var` → `lookup(env, idx)`: a `Neu(fv)` returns the fvar's own
  `binder_type` (free variables carry their type, §2.1); a `Val(e,env)`
  recursively infers *that* closure; a `V(v)` asks the value engine
  (`nb_type`) and reads back.
- `Local` → its `binder_type`.
- `Sort` → `succ(level)`, with a universe-parameter scope check under `Check`.
- `Const` → level-substituted declaration type, memoised globally in
  `g_inst_ty` keyed by the `Const` expression pointer (which already encodes
  name+levels, since expressions are hash-consed); the *checks* still run per
  occurrence, only the instantiation is reused (`src/tc.rs:653-668`).
- Lambda/Pi/Let/App/Proj → consult `infer_cache_check`/`infer_cache_only`
  keyed by `self.key(c)`, i.e. the closure with its environment **projected
  onto the read set** — this is the README's "543 telescopes" mechanism.

Binder entry: `infer_lambda` (`src/tc.rs:660-698`) reifies the binder domain,
optionally checks it is a sort, picks a de Bruijn level with
`next_level(e, env).max(max_level(d))`, builds `fvar_at(level, d)`, pushes
`Entry::Neu(fv)`, and loops over the whole run of binders before inferring the
body; then reifies, `cheap_beta_reduce`s (`src/tc.rs:890-923`), and abstracts
all the levels back in one pass. `infer_pi` (`:700-717`) does one binder and
combines universes with `imax` + `simplify`.

**`let`**: `infer_let` (`src/tc.rs:719-737`) under `Check` infers the type of
the value and asserts it def-eq to the ascription, then pushes
`Entry::Val(val, c.env)` — **the value is delayed, not substituted and not
evaluated** — and infers the body. (Contrast `nb_eval`'s `Let`, which *does*
evaluate eagerly, `src/nbe_eval.rs:124-132`.)

**Application**: `infer_s` (`src/tc.rs:739-803`) walks the spine built by
`mk_sclo` (`src/tc.rs:418-427`). For each argument: if the function type is
*syntactically* a `Pi`, peel it without evaluating the domain; otherwise force
the function type to a `Pi` *value*. Under `Check`, the argument-type check
first tries `eq_mod` on closures, then falls back to values (reifying the
argument type first so that "every site that infers it keys the value memo the
same way"). Then `push_entry(pi_env, Entry::Val(arg.e, arg.env))` and continue
with `(body, env2)` — the codomain is never instantiated.

**Projection**: `infer_proj` (`src/tc.rs:803-880`) forces the structure's type
to a value, reads the inductive head and its arguments off the spine, then
walks the constructor type as a closure pushing parameters (`push_entry_v`)
and earlier fields (as *closures over a `Proj` expression*, `src/tc.rs:867-870`
— a neat trick: `Proj(i_name, fi, Var 0)` under an environment binding `Var 0`
to the structure closure). Prop-ness of earlier field types is checked via
`is_prop_of` when the structure's universe may be zero.

**Declarations** (`check_declar_in`, `src/tc.rs:72-131`):
`check_declar_info` asserts no duplicate universe parameters, no free
variables in the type, and that the type infers as a sort (plus, for theorems,
a "soft" Prop check); then for a definition/theorem/opaque, `infer(val, Check)`
and `assert_def_eq` against the ascribed type. Inductives go to
`check_inductive_declar_in`, `Quot` to `check_quot`. Constructors and
recursors get their type checked plus structural checks against the export
(§9).

Visibility: `Env` carries a `cutoff` index into the export's `IndexMap`, set
to the position of the declaration being checked (`EnvLimit::ByName`,
`src/env.rs:205-256`, `src/env.rs:273-280`), so a declaration can only see
what precedes it.

---

## 7. Environment and inductives

Constant storage is an `FxIndexMap<NamePtr, Declar>` built once by the parser
(`src/env.rs:230`), with `Declar` an enum of Axiom/Definition/Theorem/Opaque/
Quot/Inductive/Constructor/Recursor plus their data records
(`src/env.rs:54-166`). Lookup is `get_declar` (`src/env.rs:262-265`), checking
an optional *temporary extension* used only while checking nested inductives
(`new_w_temp_ext`, `src/env.rs:241-254`), then the persistent map subject to
the cutoff.

**The inductive installer is entirely syntactic and independent of the closure
and value machinery.** `src/inductive.rs` manipulates `ExprPtr` throughout:
positivity (`check_positivity1`, `:753`), valid-application checks
(`is_valid_ind_app`, `:778`), nested specialisation
(`specialize_nested`/`replace_all_nested`, `:343`/`:696`), large-elimination
test (`:965`), motive/minor/major construction (`:1042`-`:1185`), recursor rule
generation (`mk_rec_rule1`, `:1219`), and the def-eq cross-checks against the
exported declarations (`assert_nonnested_*_def_eq`, `:1261`-`:1330`). It uses
only three expression-level services from the checker:

- `self.whnf(e)` (`src/tc.rs:330-345`) — evaluates, whnfs, reads back;
- `self.infer(e, flag)` / `infer_then_whnf` / `ensure_infers_as_sort`;
- `self.assert_def_eq(e1, e2)` / `self.def_eq(x, y)` (`src/tc.rs:353-357`).

and the pure syntactic `ctx.inst` / `ctx.abstr` / `inst_forall_params`
(`src/expr.rs:133-155`), which are called *only* from `inductive.rs` on the
checking path. So the answer to "could ConLeche keep its own inductive
installer and swap only whnf/defeq?" is **yes, cleanly**: nanoclo's own
installer is nanoda's, unmodified in structure, sitting on top of three
`ExprPtr → ExprPtr` / `bool` entry points. The install does call whnf and
def_eq, but only through those boundaries — it never sees a `Clo`, a `ValId`
or an `EnvId`.

The one leak: `reify` must be able to read a value back
(`nb_readback`, `src/nbe_eval.rs:1034-1082`) because `whnf` is required to
produce an expression. `nb_readback` is *folded* readback — an unforced
constant reads back as the constant applied, a thunk as its own expression
under its environment — not a normal form.

`src/quot.rs` builds the `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` declarations
from macros over expression constructors (`src/quot.rs:8-70`), again pure
syntax.

---

## 8. Other tricks

- **Parallelism.** `check_all_declars_par` (`src/tc.rs:201-229`): N threads,
  each with its own `TcCtx` (hence its own scratch dag, environments, value
  arena and every cache), pulling declaration indices from one
  `AtomicUsize`. The only shared mutable state is that counter and the
  diagnostic `G_CTRS` atomics. `num_threads > 1` selects it
  (`src/tc.rs:233-239`); the parallel driver does **not** set `persist_dag`
  ("the parallel driver checks out of order and keeps a per-declaration dag",
  commit `fa67854`). `cfg1.json`/`cfg4.json`/`cfg8.json` are the 1/4/8-thread
  configs. Shared-nothing: this is embarrassingly parallel at declaration
  granularity, at the cost of re-instantiating constants per thread.
- **Allocation.** `mimalloc` as global allocator (`src/main.rs:1-2`); arenas
  are `Vec`s reset in place; `smallvec` for spines (inline 8,
  `src/closure.rs:57`) and picked views.
- **Stack.** 1 GiB thread stacks so conversion can recurse natively; one
  `stacker::maybe_grow` remains in `nb_whnf`.
- **Nat acceleration.** Literals are `BigUint`s. `Nat.succ` of a literal
  becomes a literal instead of growing a unary spine
  (`src/nbe_eval.rs:246-256`); a Nat primitive whose spine arguments are
  already literals is answered at application time so the recursive definition
  never unfolds (`src/nbe_eval.rs:258-272`); `Nat.add`/`sub`/`mul`/`pow` whose
  second argument is a literal of more than 8 bits refuse to unfold at all
  unless demanded (`nb_nat_defer`, `src/nbe_eval.rs:845-862`); `Nat.rec` on a
  literal steps without expanding it (`nb_nat_rec`, `:637-679`); conversion
  compares `Nat.succ a` vs `Nat.succ b` by predecessors
  (`nb_conv_nat`, `src/nbe_conv.rs:572-598`). Exponent/shift bounds are checked
  before the base is read (`:893-896`) — a denial-of-service guard.
- **String acceleration.** A literal meets `String.mk`/`String.ofList` by
  spelling itself out as a `List Char` (`nb_conv_str`, `src/nbe_conv.rs:602-625`,
  `str_lit_to_constructor`, `src/expr.rs:527-556`), restored by commit `677d789`.
- **Export parsing.** `fast_line` (`src/parser.rs:823-…`) matches the
  exporter's canonical byte sequences directly (keys alphabetical, no spaces,
  no escapes) and falls back to serde for anything else
  (`go1`, `src/parser.rs:809-821`). Commit `97f5cb9`: parsing was 13% of the
  bitvec run, 4% in sokonanoda whose parser this mirrors; bitvec 202→183G.
  Export indices are sparse and translated through `name_map`/`level_map`/
  `expr_map` vectors (`src/parser.rs:52-57`), bounded by `MAX_EXPORT_INDEX =
  1<<31` (`src/parser.rs:61-62`).
- **Pointer equality.** There is no `ptr_eq` in the Lean sense: hash-consing
  makes index equality *be* structural equality, for expressions
  (`ExprPtr`), environments (`EnvId`), values (`ValId`) and spines
  (`SpineId`). Nearly every fast path in the codebase is one `==` on a u32.
- **Level algebra.** `simplify` memoised per pointer (`src/level.rs:55-62`);
  `leq`/`eq_antisymm` short-circuit on equal interned pointers
  (`src/level.rs:238-262`).
- **`@eagerReduce`.** A hint the term can carry: `@eagerReduce A a` in argument
  position sets `ctx.eager_mode` while the argument's type is checked
  (`src/tc.rs:770-774`, `is_eager_reduce_app`, `src/expr.rs:569-578`). Restored
  by root commit `0374e01`, which notes "Unverified: no term is known that
  makes eager_mode change an outcome". At HEAD the flag is set but nothing on
  the value path reads it — a vestige.

---

## 9. What is trusted vs checked

**Checked** (relative to the official kernel, nanoclo does the same work):
- every declaration's type infers as a sort; no duplicate universe parameters;
  no free variables in a declaration type (`check_declar_info`,
  `src/tc.rs:247-273`);
- definition/theorem/opaque bodies infer to a type def-eq to the ascription;
- theorems must land in `Prop` (an extra check nanoda added,
  `src/tc.rs:261-270`);
- every universe parameter used is bound in the declaration's `uparams`
  (`check_level`, `src/tc.rs:627-634`);
- inductive specifications, constructor positivity, and **the recursors and
  recursor rules are re-derived from the inductive declaration and checked
  def-eq against the exported ones** (`assert_nonnested_recursors_def_eq`,
  `src/inductive.rs:1308-1330`; `assert_nonnested_rec_rule_def_eq`, `:1291`);
- since `cdeb070`: the set of exported recursors naming an inductive must
  *equal* the set derived from it (`ck_recursor_names`,
  `src/inductive.rs:156`), every recursor's `all_inductives` head must be an
  inductive declared earlier in the export (`src/tc.rs:101-127`), and a
  constructor must be listed in its inductive's `all_ctor_names`
  (`src/tc.rs:86-99`). This closes the arena's `extra-rec`/`orphan-rec`
  attacks.
- declaration visibility is cut at the declaration's own index, so no forward
  references (`src/env.rs:245-254`).

**Trusted**:
- the export file's *parse* — the format version must be in [3.1.0, 3.2.0)
  (`src/parser.rs:21-37`), and names/levels/exprs are taken as given;
- the axiom whitelist, per config (`permitted_axioms`,
  `unpermitted_axiom_hard_error`, `unsafe_permit_all_axioms`,
  `README.md:37-41`);
- declaration *metadata* used for reduction: `num_params`, `num_fields`,
  `num_motives`, `num_minors`, `num_indices`, `major_idx`, `is_k`,
  `ctor_telescope_size_wo_params` and the `ReducibilityHint`s are read from the
  export and drive iota; for the nested/mutual case they are cross-checked via
  `aux_data_ck` (`src/env.rs:89-165`), but in the non-nested path they are
  largely taken on faith;
- the Nat and String kernel extensions, when enabled: `BigUint` arithmetic
  (`src/util.rs:116-172`) stands in for the unary definitions;
- `Lean.reduceBool`/`Lean.reduceNat` are refused outright
  (`src/nbe_eval.rs:189-196`), matching nanoda — a declaration reaching them
  panics rather than being trusted;
- the speculation budget and the `Gen2` cache eviction are performance-only:
  an exhausted probe falls back to the sound route, and a `Gen2` eviction only
  loses a memo. (Worth checking in a port: `probe_fail` caches a *negative*
  spine-pair result across the whole declaration — it is only consulted as a
  "don't speculate, unfold instead" hint, so it cannot turn a true into a
  false, but it is the subtlest bit of state in the file.)

---

## 10. Portability notes for a Lean host

The striking thing is how *little* Rust-specific machinery is load-bearing.
There is **no `unsafe`, no `Rc`/`RefCell` on the hot path, no interior
mutability except `Vec`/`HashMap` behind `&mut self`, and no shared-memory
threading beyond one atomic counter.** Contrast sokonanoda, which is built on
`bumpalo::Bump` arenas, `&'a Value` pointers, `Cell`/`OnceCell` interior
mutability and an `unsafe` pointer-tagged `Elim`
(`_tmp/ref/sokonanoda/src/value.rs:44-77,90-134`).
nanoclo is much closer to something a Lean 4 program can be.

Mechanism by mechanism:

| mechanism | Rust feature used | Lean 4 analogue |
|---|---|---|
| `Ptr<A>` = tagged u32 index | `PhantomData`, bit 31 tag | a `UInt32` with the same tagging, or two separate `Array`s and a sum index. No RC traffic at all — this is *better* than Lean object pointers for cache density, but Lean cannot index-into-`Array` without a bounds proof or `Array.get!`. |
| `LeanDag` = `IndexSet` hash-consing | `indexmap`, `&mut` | `HashMap Expr UInt32` + `Array Expr` in an `IO.Ref`/`StateM`; ConLeche already has an arena with a WF invariant, which is the right home. The `alloc_expr` "cannot be in export" pre-filter (`src/util.rs:483-505`) needs the two-arena split to survive. |
| cached `hash`, `num_loose_bvars`, `has_fvars` per node | plain fields | identical; Lean's `Expr` already does this. A ConLeche `Expr` would need the loose-bvar count, which is the single most-used field here. |
| interned environments (`EnvNode` in a `Vec`, `env_intern` hash map) | `Vec` + `HashMap`, `&mut` | **expressible as an ordinary inductive with a persistent map**: see below. |
| Myers jump pointers | a `u32` field computed at construction | trivially portable — the field is immutable, computed from the parent and the parent's jump, i.e. a pure function of the cons. A purely functional persistent list *without* interning can carry the same field; it is Okasaki's skew-binary random-access list in disguise. |
| `Gen2` two-generation memo | `HashMap`, swap | `Std.HashMap` pair in a state monad. |
| `forced: Option<ValId>` on `Thunk`/`Unfold`, `domain: Option<ValId>` on `Lam` | mutation through `&mut self.vals[i]` | **this is the one place that genuinely needs mutable state.** Either an `Array Value` in `ST`/`IO.Ref` updated destructively (with linearity care — see the `lean-rc-linearity` skill), or Lean's `Thunk` for the `Thunk` case. Note `Unfold.forced` and `Lam.domain` are *memo slots keyed by an interned id*, so a side table `HashMap ValId ValId` is an equivalent, slower encoding. |
| value/spine interning | `HashMap` probes | same; the `entry` API's "one probe per construction" (commit `f73e321`) has no Lean equivalent in `Std.HashMap` — expect two lookups or an `alter`-style API. |
| `smallvec` spines | stack inline | `Array`; Lean has no inline-capacity vector. |
| 1 GiB stacks + `stacker` | `std::thread::Builder::stack_size` | Lean's interpreter/compiled code recursion depth; deep conversion recursion is a real risk, and an explicit worklist may be needed where nanoclo just recurses. |
| parallelism | `thread::scope` + `AtomicUsize`, shared-nothing per declaration | `Task`/`IO` with a work queue; since contexts share nothing but the read-only export, this maps directly. |
| `mimalloc` | global allocator | not applicable; Lean has its own allocator. |
| `BigUint` | `num-bigint` | `Nat` (already a GMP bignum). |
| byte-match parser | slice patterns | `ByteArray`/`String` matching; mechanical. |

### Could the closure be an ordinary inductive with a persistent environment?

Yes, and almost verbatim. The core is:

```lean
inductive Entry where
  | val : ExprPtr → Env → Entry     -- a delayed closure
  | neu : ExprPtr → Entry           -- an opened binder's Local
  | v   : ValId  → Entry
inductive Env where
  | nil
  | cons (entry : Entry) (parent : Env) (len : Nat) (nextLevel : Nat) (jump : Env)
```

`len`, `nextLevel` and `jump` are all *pure functions of the cons*, computed
once at construction — no mutation, no identity requirement. `lookup` is then
a structural recursion on `Env` guided by `len`, exactly as
`src/closure.rs:569-593`, and **the jump pointers become a second recursive
field of the same inductive**, i.e. a DAG-shaped persistent structure (each
node is shared by its parent and by whoever jumps to it, so Lean's reference
counting keeps it alive naturally). The complexity argument is unchanged:
O(log i) node visits.

What is *lost* without interning: `EnvId` equality stops being a cheap test.
That matters in four places — `env_intern` (§3.2), `proj_cache`/`view_cache`
keyed on `(mask, EnvId)`, `thunk_intern` keyed on `(view, ExprPtr)`, and the
`infer_cache` keyed on a projected `Clo`. Options in Lean: (a) keep a hash on
each `Env` node and use structural equality with a `ptrEq` fast path — the
`prune`/`hash` approach sokonanoda takes
(`sokonanoda/src/value.rs:264-290`); (b) keep the interning table and hand out
`UInt32` ids as nanoclo does, which needs a mutable state monad but no
`unsafe`; (c) accept coarser keys. Given how much of nanoclo's measured win
(§5.3) comes from environment-keyed caches, (b) looks necessary rather than
optional.

The **value graph** is the harder port: its whole performance story is
"interning makes `x == y` decide construction-identity", plus destructive
`forced` slots. A Lean version would either intern in a state monad
(`ValId = UInt32` into an `Array Value`, mutable `forced`) or fall back to
`ptrEq` + structural hash. The former is closer to nanoclo and probably the
right target, but it is a mutable graph inside a verified checker — the
`Std.HashMap` pattern in ConLeche's CLAUDE.md (a structure carrying its own
invariant) is the obvious shape for it.

The **read-set/view machinery** ports without difficulty: `Uses` is a plain
inductive over `UInt64` masks and word arrays, `uses_mask` is a pure memoised
function of an `ExprPtr`, and `project`/`intern_view` are pure functions once
the environment representation is fixed.

---

## 11. Summary

### Abstract (20 lines)

nanoclo is a fork of nanoda_lib that keeps nanoda's expression DAG, parser,
pretty printer and inductive installer, and replaces inference and conversion.
Expressions are hash-consed into two `IndexSet` arenas and named by 32-bit
tagged indices, each node caching its hash, loose-bvar count and fvar flag, so
"are these terms equal / is this closed" are O(1). Terms in flight during
*inference* are closures `(ExprPtr, EnvId)` over an interned, persistent
environment whose nodes carry Myers jump pointers: extending is one hash probe
plus a push, lookup of de Bruijn index i is O(log i), and no substitution
happens until a type must cross back out (`reify`). Free variables are
`Local` nodes carrying their own type and named by de Bruijn *level*, so two
openings of a binder produce the same variable and every downstream cache
coincides. nanoclo's distinctive contribution is the *read set*: the loose-bvar
indices a term actually reads, computed bottom-up as a bitmask and used to
project or "view" an environment down to just those entries, so two closures
that agree on what a term reads share one cache entry and one thunk.
Conversion, by contrast, is normalisation by evaluation adopted from
sokonanoda: both sides evaluate to an interned value graph (rigid heads with
interned spines, glued `Unfold` nodes with a forced slot, lazy `Thunk`s,
closures for binders) in which value identity is integer equality, and
unification is one match per pair with positive/negative memos, eta, structure
eta, memoised proof irrelevance, hint-ordered lazy delta, and Nat/String
literal acceleration. Comparing the arguments of two applications of one
constant is speculative under a 4096-step fuel budget shared by the whole
nested comparison, with (at HEAD) geometric re-granting along the unfold
chain. Everything is safe Rust, index-based, shared-nothing across threads.

### Five surprises

1. **The name lies about the architecture.** "nanoclo = nano + closures", and
   the README leads with delayed substitution — but `cdcb24d "Delete the
   closure conversion machine"` removed the closure whnf/def-eq entirely on
   2026-08-10. What is left of `closure.rs` "serves inference: environments,
   lookup, reify, and the projection that normalizes an entry before it is
   interned." Conversion at HEAD is sokonanoda's NbE.
2. **Evaluation reads the *checker's* environments, not its own.**
   `VEnvId = crate::closure::EnvId` (`src/nbe.rs:25`) and `Entry` grew a
   `V(ValId)` case, so one interned environment structure serves both the
   closure-based inference and the value-based conversion
   (commit `d407622`). That fusion is what made the NbE port pay.
3. **An evaluation memo was *removed* because it was redundant.**
   `f329f4e "Values carry their own sharing; the evaluation memo is gone"` —
   with interning, thunk `forced` slots and `Unfold` nodes, the `(expr, env) →
   value` cache had a 19% hit rate and 114M single-use inserts on bitvec.
   Similarly `e021753` dropped the syntactic front from `is_def_eq` and
   `12d80f9` *un*-projected the `eq_mod` key. Three optimisations deleted for
   being negative.
4. **The read-set bound is a value bound, not a cost bound.**
   `MAX_USES_WORDS = 8` is not about the expense of holding a big bitmask; a
   set of n positions costs "one environment rebuilt from n entries at every
   node that asks for a key", quadratic on a ladder. Commit `554586c` measures
   3.54× per doubling when the bound is lifted. That is an unusually
   self-aware piece of tuning.
5. **One speculation budget decided a 13-hour run.** `4cdd12f`: an FLT
   comparison needing ~10⁷ steps, restarted from 4096 every time, kept the
   checker on a single theorem for 13 hours; the geometric re-grant brings it
   to 0.25s. A constant-factor heuristic with a pathological asymptotic
   failure mode, fixed by doubling.

### Why 4× slower than sokonanoda and 2.3× faster than nanoda?

Arena numbers quoted in the task: mathlib in 7.9 min (nanoclo) vs 2.1 min
(sokonanoda), 18 min (nanoda), 32.9 min (official).

**Why faster than nanoda (2.3×).** nanoda instantiates. Its `infer_lambda`,
`infer_pi`, `infer_let`, `def_eq_binder_aux` and `whnf` all call `ctx.inst(...)`
on every binder crossed (`nanoda_lib/src/tc.rs:629,639,660,666,690,814,823,884,896`),
rebuilding the body each time; nanoclo pushes an environment entry instead, and
reifies only at boundaries. On the arena's own `beta-ladder`/`let-ladder` this
is the O(n) vs O(n²) difference the README names. On top of that nanoclo has the
value graph (a constant unfolds once per instantiation, an argument evaluates
once), the byte-match parser (13%→~0 of the bitvec run), hash-consed everything,
and mimalloc. Note nanoda's own numbers are not in these commit messages; the
in-tree comparisons are against sokonanoda only.

**Why slower than sokonanoda (≈3.8×).** The evidence in the commit messages
points three ways, and I think they compound:

1. *nanoclo runs two machines where sokonanoda runs one.* Inference is on
   closures with its own caches (`infer_cache_check/only`, `reify_go_cache`,
   `eq_mod_cache`, `prop_cache`, the projection and view tables), conversion is
   on values with its own (`clo_val_cache`, ten memos, four conversion sets),
   and every crossing pays `nb_of_clo`, `reify` or `nb_readback`. Commit
   `d407622` states this outright: "The cost is the doubled machinery around
   conversion, which goes when inference moves onto values" — and inference
   never did move onto values; `8baf6ca`/`cef98ed` moved it only as far as
   "consumes values, produces closures". sokonanoda has one representation and
   infers on it (`sokonanoda/src/infer.rs`, 276 lines against nanoclo's
   `tc.rs` 929 + `closure.rs` 1036).
2. *Index-and-intern costs more per node than pointer-and-cell.* Every nanoclo
   value construction is a hash probe into an `FxHashMap` (`src/nbe.rs:391-523`);
   sokonanoda allocates into a bump arena and computes a lazy `digest`/`canon`
   only when a comparison needs one
   (`sokonanoda/src/value.rs:93-190`). Commit `f07f79e` measures the difference
   in the one place they overlap: "spine_snoc runs 747M times on cut_wt against
   613M spine extensions in sokonanoda at half the per-probe cost" — i.e.
   nanoclo does 22% more spine extensions and each probe costs about twice
   what sokonanoda's does. `c0d78a3` is blunter: "the corpus cost is the
   per-node price of the value machinery, not who calls it."
3. *Level algebra and auxiliary walks.* `f9d4e66`: "colim spends 9% of its run
   in level algebra where sokonanoda's simplify cache keeps it under 2%".
   `a8d3067`: `uses_mask` was 7.4% of cut_afftrans before its cache was moved
   to the dag's lifetime. The read-set machinery buys a lot (§5.3) but is not
   free, and sokonanoda achieves similar sharing through environment pruning
   (`Env::Framed`/`prune`, `sokonanoda/src/value.rs:264-292`) built into the
   representation rather than as a side computation.

**The caveat, and it is a large one.** The commit messages claim nanoclo
*beat* sokonanoda on instruction count on the four corpora after
`a8d3067`/`a54f726` ("All four now below sokonanoda's 128.9, 559.4, 908.9 and
1000.9"; "Sokonanoda is behind on bitvec, colim and mathlib, ahead by 0.1% on
cut_wt and 0.6% on afftrans"). If those measurements are right and the arena
wall clock says 3.8× slower, the gap is **not instructions retired** — it is
memory-system behaviour, or the two are not being measured on the same thing.
Threading is not the explanation: both checkers have the identical
`num_threads` config knob defaulting to 0 → serial
(nanoclo `src/util.rs:962-963` + `src/tc.rs:233-239`;
sokonanoda `src/util.rs:1292` + `src/tc.rs:220-225`), so an arena run gives
both the same shape of configuration. The likeliest remaining cause is
locality: every nanoclo value, spine, environment and thunk construction is a
probe into an `FxHashMap` whose working set is declaration-sized (colim RSS
was 2.9 GB before `a54f726`, 1.8 GB after; `src/nbe.rs:186-213` preallocates
ten tables at 2^14 per thread), whereas sokonanoda bump-allocates and follows
pointers, computing a `digest` only when a comparison demands one. Hash probes
retire few instructions and stall for many cycles, which is exactly the shape
of "equal instruction counts, 4× the wall clock". I could not resolve this
from the checkout alone: the in-tree numbers are
`perf stat -e instructions:u` on named corpora (bitvec_lemmas, cut_colim,
cut_wt, cut_afftrans, mathlib) and the arena's are wall clock on its own
mathlib export, and no commit message reconciles the two.
