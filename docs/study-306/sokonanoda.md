# sokonanoda — design study (task #306)

Checkout read: `_tmp/ref/sokonanoda`, commit `28c03d0`
("share more work", 2026-09-12). All paths below are relative to that checkout;
line numbers are from that commit.

---

## 1. Overview and layout

### Crate layout

```
src/main.rs            86   binary: config file -> parse -> check_all_declars
src/lib.rs             27   module list; STACK_SIZE = 2 GiB
src/util.rs          1386   tagged pointers, interners, TcCtx, TcCache, Config, arenas
src/expr.rs           692   syntactic Expr + inst/lift/subst + fv masks
src/value.rs          576   Value, Env, Spine, Elim, Closure, digests
src/eval.rs          2129   NbE evaluator, whnf/force, iota, proj, Nat literals
src/conv.rs           811   definitional equality on values
src/infer.rs          276   type inference on syntax against a value context
src/quote.rs          157   readback value -> Expr
src/relevance.rs      161   per-constant argument "signature" (Prop / unused args)
src/tc.rs             275   TypeChecker struct, per-declaration driver, thread pool
src/env.rs            330   Declar/Inductive/Ctor/Recursor data, Env lookup
src/inductive.rs     2134   inductive-type installation and validation
src/quot.rs           275   Quot axiomatisation check
src/level.rs          297   universe levels, simplify/leq/eq_antisymm
src/name.rs           195   hierarchical names + per-name side table
src/parser.rs        1578   hand-written SWAR JSON-lines parser with serde fallback
src/debug_printer.rs  193
src/tests*, tests/arena.rs        tests (incl. Lean-kernel-arena harness)
                    12937   total
```

Dependencies that matter (`Cargo.toml:26-40`): `bumpalo` + `stumpalo` (two
arenas), `hashbrown::HashTable` (raw hash tables), `rustc-hash` (FxHasher),
`smallvec`, `mimalloc` as global allocator (`src/main.rs:6-7`), `memmap2`
(export file is mmapped, `src/util.rs:1358-1368`), `num-bigint`. Release profile is
`opt-level=3, lto="fat", codegen-units=1, overflow-checks=false`
(`Cargo.toml:8-12`).

### README claims

Current `README.md`:

> It is essentially a testing bed for high-performance typechecking for Lean.
> … Currently, it is about 9x faster than the official kernel, measured on
> mathlib. Basically, the core conversion algorithm is entirely replaced by
> something closure-based. There are also some non-theoretical, purely
> programming optimisations.

Lineage: fork of `nanoda_lib` → `sonanoda` (datokrat) → `still-nanoda`
(SchrodingerZhu) → this. Earlier README revisions (recoverable with
`git log -p README.md`) carry the only quantitative attributions in the repo:

* "Local-First Expr Allocation Check … **5% speedup** in Cedar and Mathlib"
  (commit `289d48d`, README text at `f1c4b12^`).
* "Local-only Expression Filtering … another **10% speedup** in Cedar and
  Mathlib."
* "Normalisation by evaluation: conversion checking is implemented by
  evaluating each term into a value, instead of repeatedly WHNFing
  expressions. Constants applied to their arguments keep both their unreduced
  form and (lazily) the definition body … ('glued' evaluation). This change
  brings another **35% speedup** in Mathlib. However it uses **40% more peak
  memory**, probably due to the use of bump arena allocation." (README at
  commit `7c74b01` "NbE"; text deleted by `0668a6f`.)

No other commit quantifies its gain; the remaining ~50 commits have bare
one-line messages.

### What the git log says about the optimisation history

`git log --oneline` (newest first), annotated from the diffs:

```
28c03d0 share more work         hash-cons env_extend + a single neutral_app
                                path; mark bvars/const heads canonical
fe8edcc sparse environments     Env::Framed / WideFramed: an environment
                                pruned to the fv-mask of the expression
ceaabb5 delete binder names     binder names and BinderStyle removed from Expr
        and plicity             entirely (Expr 40 bytes); pretty printer deleted
7b51784 port over fixes
49b0e9c binder optimisations    infer: reuse the binder type as the Pi closure
                                when the body type is the domain (infer.rs:130)
9b4ea12 eagerness in some places
0fab887 Smallvec                SpineArgs = SmallVec<[V;8]>
247021b tweak inline hints
9ad006e Entry                   HashMap Entry API to avoid double lookups
b38b875 probe caps              budgeted speculative spine comparison
84023dd Parser streaming        bounded-memory streaming of stdin input
13a9760 Parser stuff
ba5814a pointer-equality on spines     `ptr::eq(sx,sy)` shortcut in unify_spine
4ed825a pointer-equality for levels
4f0bc57 Much better algorithm for proof irrelevance in spines  -> relevance.rs
c293178 union find stuff        positive conv cache as union-find (later reverted)
8eaaf4b interners on the thread thread-local interner + tagged local/global ptrs
88506dc unfold key narrowing
7cb1703 proj
8212fd5 fix: more struct and inductive checks
6e2dd3f Optimisations
90b05dc fix: proof irrelevance under bvar
d245a52 fix: k-rec bug Thread the proper depth
fd05f02 perf: stumpalo allocator
c8dcb27 perf: borrow closures
698c744 perf: remove unnecessary clones
a6e72ae perf: walk spines in place
33f6754 fix: reduce string literal to constructor before iota
70bd739 fix possible hash collision unsoundness
7c74b01 NbE                     the big one: +3184 lines, conv.rs/eval.rs/value.rs
289d48d Add local-first expr allocation cache
```

Note `c293178` ("union find stuff") replaced the positive conversion cache with
a union-find over value addresses (transitive closure of "these two values are
convertible"); it was reverted before the current commit — `src/union_find.rs`
is deleted and the cache is a plain `FxHashSet<(usize,usize)>` again
(`src/util.rs:1046`).

---

## 2. Term representations

### Syntactic `Expr` (src/expr.rs:17-76)

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<'a> {
    StringLit { hash: u64, ptr: StringPtr<'a> },
    NatLit    { hash: u64, ptr: BigUintPtr<'a> },
    Proj      { hash: u64, ty_name: NamePtr<'a>, idx: u16, structure: ExprPtr<'a>, fv_mask: u64 },
    Var       { hash: u64, dbj_idx: u16 },
    Sort      { hash: u64, level: LevelPtr<'a> },
    Const     { hash: u64, name: NamePtr<'a>, levels: LevelsPtr<'a> },
    App       { hash: u64, fun: ExprPtr<'a>, arg: ExprPtr<'a>, fv_mask: u64 },
    /// Binder names and plicity are presentation metadata and are deliberately omitted.
    Pi        { hash: u64, binder_type: ExprPtr<'a>, body: ExprPtr<'a>, fv_mask: u64 },
    Lambda    { hash: u64, binder_type: ExprPtr<'a>, body: ExprPtr<'a>, fv_mask: u64 },
    Let       { hash: u64, data: &'a LetData<'a>, fv_mask: u64 },
}
const _: () = assert!(std::mem::size_of::<Expr<'static>>() == 40);   // expr.rs:692
```

* **Binders**: de Bruijn *indices* (`Var.dbj_idx: u16`) in syntax. Binder names
  and implicit/instance annotations are **not represented at all** (commit
  `ceaabb5` deleted them, along with the 938-line pretty printer). `Let` carries
  a `nondep: bool` from the export file, kept only in the hash.
* **No free variables / locals in the syntax at all.** nanoda's `Local`
  constructor is gone; open terms are handled on the value side by
  `RigidHead::BVar(level, ty)` — i.e. de Bruijn *levels* only in values.
* **`mdata` is rejected**: `panic!("Expr.mdata not supported")` (parser.rs:1290).
* **Hash**: every node stores a precomputed `u64` structural hash; `Hash` just
  writes it (`expr.rs:101-103`). Hashes combine child *pointer addresses*
  (`hash64!(APP_HASH, fun, arg)`, util.rs:829), so hashing is O(1) per node.
  `70bd739` "fix possible hash collision unsoundness" made the interner compare
  structurally after the hash match rather than trusting the hash
  (`util.rs:334-345`).
* **`fv_mask: u64`**: a bitmask of which of the lowest 64 loose de Bruijn indices
  actually occur (`expr.rs:640-676`). This is the enabler of the "sparse
  environment" trick (§8).
* **Allocation and identity**: `ExprPtr` is a packed `NonZeroU64`
  (util.rs:157-206): bits 3..47 the address, bit 0 a *local/global* tag, bits
  48..63 the cached `num_loose_bvars`. So `num_loose_bvars(e)` and "is this term
  closed" are free, and `PartialEq`/`Hash` on `ExprPtr` are integer
  comparisons. Terms are **hash-consed** into arenas (`stumpalo::Arena`) via
  `hashbrown::HashTable` interners (`util.rs:302-379`), two levels: a global
  `Dag` built by the parser (shared, read-only, one per process) and a
  thread-local `Dag` for terms created during checking; `alloc_expr` checks the
  *local* table first (util.rs:723-728 — this is the "local-first expr
  allocation cache", 5%), while names/levels/strings/bignums check the global
  table first (util.rs:705-721). The tag bit records which arena a pointer came
  from.

`LevelsPtr` packs a slice address + length + local bit into one `NonZeroU64`
(util.rs:245-300); `Level`, `Name`, `CowStr`, `BigUint` use the `tagged_ptr!`
macro (util.rs:78-155), with the tag being bit 0 (or the aarch64 top byte under
the optional `top-byte-ignore` feature).

`name::NameNode` (name.rs:81-116) is an interned name plus a **mutable side
table**: an `AtomicU32 decl_idx` (the name's index in the declaration map, set
at parse time, `parser.rs:1244-1249`) and an `AtomicU8 nat_red` (which builtin
Nat operation, if any, this name denotes, set once in `Dag::mk_name_cache`,
util.rs:912-940). Environment lookup is therefore **not** a hash lookup: it is
`declars[name.decl_idx()]` with a visibility cutoff (env.rs:276-283).

### Semantic `Value` (src/value.rs:89-135)

```rust
pub type V<'a> = &'a Value<'a>;   pub type E<'a> = &'a Env<'a>;
pub type C<'a> = &'a Ctx<'a>;     pub type S<'a> = &'a Spine<'a>;

#[derive(Debug, Clone, Copy)]
pub struct Closure<'a> { pub env: E<'a>, pub ctx: Option<C<'a>>, pub body: ExprPtr<'a> }

#[derive(Debug, Clone, Copy)]
pub enum RigidHead<'a> {
    BVar(u32, V<'a>),                 // de Bruijn LEVEL + its type
    Axiom(NamePtr<'a>, LevelsPtr<'a>),
    Ctor(NamePtr<'a>, LevelsPtr<'a>),
    Recursor(NamePtr<'a>, LevelsPtr<'a>),
    QuotConst(NamePtr<'a>, LevelsPtr<'a>),
    Inductive(NamePtr<'a>, LevelsPtr<'a>),
}

#[derive(Debug)]
pub enum Value<'a> {
    Rigid  { head: RigidHead<'a>, spine: S<'a>, canon: Cell<bool>, key: Cell<u64> },
    Unfold { head: UnfoldHead<'a>, spine: S<'a>,
             head_value: &'a OnceCell<V<'a>>,   // the definition body, shared per (name,levels)
             forced:     OnceCell<V<'a>>,       // this application, unfolded
             canon: Cell<bool>, key: Cell<u64> },
    Lam    { binder_type: ExprPtr<'a>, body: Closure<'a>, canon: Cell<bool>, key: Cell<u64> },
    Pi     { domain: V<'a>, body: Closure<'a>, canon: Cell<bool>, key: Cell<u64> },
    Sort   { level: LevelPtr<'a>, key: Cell<u64> },
    NatLit { ptr: BigUintPtr<'a>, key: Cell<u64> },
    StrLit { ptr: StringPtr<'a>, key: Cell<u64> },
    Thunk  { env: E<'a>, expr: ExprPtr<'a>, forced: OnceCell<V<'a>>, key: Cell<u64> },
}
const _: () = assert!(std::mem::size_of::<Value<'static>>() == 56);   // value.rs:568
```

This is the **glued / "lazy delta" value** of smalltt: a `Unfold` value is a
constant applied to a spine that remembers *both* the folded form (head name,
levels, spine) and, in a `OnceCell`, the unfolded one. Conversion compares the
folded forms first and unfolds only when that is inconclusive (§4).

* **Spine** (value.rs:350-353) is a snoc-list of `Elim`s with a cached length, a
  `has_proj` flag and a lazily computed `key`.
* **`Elim`** (value.rs:33-78) is a *pointer-tagged u64*: an even address is an
  application argument (`Elim::app` stores the `&Value` address); an odd one
  packs the projection's type-name address in bits 1..48 and the field index in
  bits 49.. . So a spine element is 8 bytes and a proj costs no allocation.
* **`Env`** (value.rs:263-292) has four shapes: `Nil` (with an optional universe
  substitution `lsub`), `Cons`, `Framed { mask: u64, slots: &[V] }` (a *sparse*
  environment: only the slots named by the mask are present, indexed by
  `popcount` below the bit — value.rs:405-411) and `WideFramed` (sorted `u16`
  index array + slots, for >64 loose bvars). Each non-Nil shape carries a
  one-entry memo `prune: Cell<(u64, Option<E>)>` of its last pruning.
* **`Ctx`** (value.rs:343-347) is a *separate* list of the **types** of the
  binders, used only by inference (a `Closure` with `ctx: Some(_)` is an
  "infer closure" whose body is a type to be inferred rather than evaluated —
  value.rs:418-422, eval.rs:930-936).
* **`Thunk`** exists in the type and is handled everywhere, but
  **`mk_thunk` is never called** in this commit (`grep mk_thunk src/` finds only
  the definition, value.rs:564). Evaluation is call-by-value; the only laziness
  left is the `OnceCell`s on `Unfold`. (nanoclo is the sibling that actually
  uses delayed substitutions.)
* **Value identity**: two content-equal values are meant to be the *same
  pointer*. Every constructor goes through a hash-consing wrapper keyed on the
  addresses of its parts: `mk_bvar_hc`, `mk_unfold_hc`, `mk_rigid_hc`,
  `mk_lam_hc`, `mk_pi_hc`, `spine_snoc_hc`, `env_extend`, `neutral_app`
  (eval.rs:51-116, 370-436, 83-89, 836-862). `canon: Cell<bool>` marks a value
  whose sub-structure has already been canonicalised, so
  `canonicalize_for_spine` (eval.rs:441-456) is a no-op on the fast path.
* **`key: Cell<u64>`** is a lazily computed 64-bit *content digest*
  (value.rs:145-255). Its low bit is a "closed" flag (no free bvars) and bit 63
  a "computed" flag; `kmix` is a xor-multiply-rotate mix. A second, 128-bit
  digest `global_key` (eval.rs:1160-1242) is computed on demand and is the key
  of the cross-declaration whnf store (§8).

---

## 3. The evaluator (NbE)

`eval(depth, env, e) -> V` — src/eval.rs:556-579 (cached wrapper) and 581-734
(the real thing).

* **Caching of eval itself** (eval.rs:556-579): if the term is closed and there
  is no universe substitution, look it up in `closed_eval_cache: Expr -> V`.
  Otherwise, for `App/Proj/Let/Pi/Lambda`, *prune* the environment to the
  expression's `fv_mask` (`key_env`, eval.rs:271-279) and look up
  `open_eval_cache: (pruned-env-address, Expr) -> V`. Because the pruned
  environment is itself interned (`intern_frame`, eval.rs:91-112), two different
  environments that agree on the variables this subterm actually reads give the
  *same* cache key — this is the "sparse environments" commit and it is what
  makes the evaluation of a shared subterm under many different telescopes
  collapse to one.
* **Application** (eval.rs:581-676): the App case is unrolled by hand. It walks
  the right spine of nested `App`s, detects the common case where every function
  position is the same expression ("`all_same`"), evaluates the leaf once, and
  then folds; if the function evaluates to a `Rigid` (and is not `Nat.succ`) it
  goes straight to `neutral_app` (pure spine extension, no beta) instead of the
  general `apply`.
* **`apply(depth, f, a)`** (eval.rs:864-901): `Lam` → extend the closure's
  environment and `eval` the body (β immediately, call-by-value); `Rigid` →
  `neutral_app` (snoc onto the spine), except `Nat.succ` applied to a literal,
  which folds to a `NatLit` (`try_fire_rigid`, eval.rs:940-959); `Unfold` →
  snoc onto the spine, but if the head is a builtin Nat operation try the
  literal reduction immediately (`do_nat_red_shallow`).
* **Strict / lazy**: arguments are evaluated **eagerly** (`let a = self.eval(...)`,
  eval.rs:663) and `let`-values too (eval.rs:711-718). Laziness is confined to
  δ: an `Unfold` value never unfolds until asked.
* **Delta-unfolding during eval**: never. `eval_const` (eval.rs:744-768) looks at
  the declaration *kind* only, and builds a `Rigid` for ctors/recursors/
  inductives/axioms/quot and an `Unfold` (with a fresh `OnceCell` for the head
  value) for definitions and theorems. The unfolded body is computed at most once
  per `(name, levels)` and cached in `unfold_const_cache` (eval.rs:1634-1645);
  the unfolding of a *whole application* is cached in the value's own `forced`
  cell (eval.rs:1551-1594). So both folded and unfolded forms coexist, exactly
  the "glued" scheme.
* **`whnf`** is two functions:
  * `whnf_head` (eval.rs:1049-1081): loop { force thunk; if `Unfold` → unfold one
    step; if recursor/quot head → `iota_value`; else stop }.
  * `force_all` (eval.rs:1355-1418): the same, but with an explicit *stack* of
    pending recursor applications (`ForceStep::Descend(major)`) so that reducing
    a recursor whose major premise is itself a recursor application does not
    recurse on the Rust stack. Results are memoised in `iota_cache` /
    `iota_stuck` keyed by the value address.
  Both ends call `note_whnf` to consider storing the result in the persistent
  whnf store (§8).
* **Readback / quote** (src/quote.rs): `quote(depth, v) -> ExprPtr` exists and is
  memoised by `(value address, depth)`. It is used in exactly two places:
  1. `note_whnf` (eval.rs:1107) — the whnf store keeps the *expression*, not the
     value, because the value arena is reset between sessions while the
     expression arena is not;
  2. throughout `inductive.rs` (lines 471, 477, 540, 571, 1163, 1297, 1304,
     1327, 1337, 1976, 1986), where motives, minor premises and recursor types
     are *constructed as syntax* after walking telescopes as values.
  `quote_weak` (quote.rs:77-135) is a variant that stops at unforced thunks and
  re-instantiates them syntactically. Quote is **not** used for type inference
  or error messages (there are no error messages: failure is `panic!`).

---

## 4. Definitional equality

Entry points (conv.rs:25-55): `def_eq_core` (two `Expr`s: eval both, try proof
irrelevance, then `unify`), `conv_types_at`, `def_eq_at`. Everything funnels
into

```rust
fn unify<const RIGID: bool>(&mut self, depth: u32, x: V, y: V) -> bool
```

The `RIGID` const generic distinguishes the full algorithm (`true`) from a
"structural only, no unfolding" pass (`false`), used when comparing the spines
of two `Unfold`/recursor values whose heads already agree.

Order of tests:

1. **Force thunks, then `ptr::eq(x, y)`** (conv.rs:85-91). Because values are
   aggressively hash-consed, this is the dominant success path.
2. **Conversion cache** (`unify_general`, conv.rs:95-131). Only "cacheable"
   pairs (Pi, Lam, Unfold, recursor/quot-headed Rigid — conv.rs:14-22) are
   cached, keyed by the *sorted pair of value addresses*. There are three sets:
   `conv_cache_pos`, `conv_cache_neg` and `conv_cache_neg_probe` (negatives
   established only under a truncated speculative probe, thrown away when a
   probe is abandoned).
3. **Probe budget** (conv.rs:135-141): inside a speculative probe each `unify`
   step decrements `probe_budget`; at zero the probe is marked exhausted and
   returns false.
4. **Nat literal / `Nat.succ` bridging** (`conv_nat`, conv.rs:688-712): if
   either side is a literal or a `Nat.zero`/`Nat.succ` application (and not both
   literals), compare zero-ness, else peel one `succ`/decrement one literal and
   recurse.
5. **`unify_direct`** (conv.rs:153-360), a single big `match` on the pair:
   * `Sort/Sort` → `eq_antisymm` on levels; `NatLit/NatLit`, `StrLit/StrLit` →
     pointer equality of the interned payload.
   * `BVar/BVar` → same level, then spines.
   * `Ctor/Ctor`, `Inductive/Inductive`, `Axiom/Axiom` with equal names and
     levels → compare spines, with the *relevance signature* mask (§8).
   * `Recursor/…`, `QuotConst/…` → `unify_iota` (conv.rs:444-476): if heads
     match, first a **speculative spine probe**; then proof irrelevance; then
     iota-reduce either side and retry; if nothing progressed and the heads
     match, compare spines for real.
   * `Pi/Pi`: a fast path — if the two closures have the *same body pointer*,
     the *same domain pointer* and pointer-equal environments (`envs_ptr_equal`,
     conv.rs:57-81), succeed immediately. Otherwise compare domains, then apply
     both closures to one fresh `BVar(depth)` and recurse at `depth+1`.
   * `Lam/Lam`: same fast path, with the domain obtained by `lam_domain`
     (memoised evaluation of the stored `binder_type`, eval.rs:818-841).
   * `Unfold/Unfold`: the heart of lazy delta.
     - heads equal → **spine probe** first (speculative "same head, compare args
       first"); then proof irrelevance; then `unfold_pair` (unfold *both*).
     - heads different → compare `ReducibilityHint`s (`Abbrev > Regular(h) >
       Opaque`, env.rs:18-32) and unfold the *greater* one; if that side
       refuses to unfold, try the other; if both are stuck, `unfold_value_demand`
       (which forces even the deferred big-Nat cases, eval.rs:1545-1549).
   * `Unfold` vs anything (and symmetric) → proof irrelevance, then unfold and
     retry.
   * recursor/quot vs anything → proof irrelevance, then iota one side, then
     the other, then unfold the other side if it is an `Unfold`.
6. **`unify_cold`** (conv.rs:547-572), only when `RIGID`: proof irrelevance
   again, then **eta for lambda** (one side a `Lam`, the other not: apply both
   to a fresh variable), then `try_struct_eta`.
7. **`try_struct_eta`** (conv.rs:574-592): compute the type of each side; if it
   is an inductive application, then (a) if the inductive is a **unit-like**
   type (single constructor, no fields — `is_unit_inductive`, conv.rs:676-686)
   return true outright; (b) if it can be a structure, try
   `try_eta_struct_v` in both directions, which projects each field out of one
   side and compares against the constructor arguments of the other
   (conv.rs:650-674).
8. Everything else → `false`. **Failure handling is by `panic!`**: a failed
   `def_eq` at a check site is `assert!(..., "def_eq failed")`
   (infer.rs:274), and `main` catches the unwind and exits 1 (main.rs:24-27).

**Proof irrelevance** (`try_proof_irrel_at`, conv.rs:601-623) is tried *early
and often* — before every unfolding step, not only as a last resort:

```rust
if self.statically_not_proof(x) || self.statically_not_proof(y) { return false; }
let tx = self.value_type(depth, x);  if !self.is_prop_type(depth, tx) { return false; }
let ty = self.value_type(depth, y);  if !self.is_prop_type(depth, ty) { return false; }
self.conv_types_at(depth, tx, ty)
```

`statically_not_proof` (conv.rs:524-545) is the cheap veto: from the head
constant's precomputed signature it knows whether the result type at this arity
is *known not to be a Prop*, and then skips the whole type inference.
`try_proof_irrel_lam` (conv.rs:625-649) handles the case where one side is a
lambda by eta-expanding first (the fix in `90b05dc`).

**The speculative probe** (`spine_probe`/`probe_pass`, conv.rs:396-428) is the
distinctive heuristic. When two values have the same unfoldable head, rather
than committing to "compare the arguments" (which can diverge into an expensive
dead end) or to "unfold" (which loses sharing), it compares the argument pairs
under a **budget of `PROBE_CAP = 2048` unify steps each**. If every pair is
decided and all are equal → equal. If any pair is decidedly unequal → fall
through to the unfolding route. If a pair exhausts its budget, the probe is
"not decided" and the pair is treated as unknown (and `conv_cache_neg_probe` is
cleared so the provisional negatives do not leak). `unbudgeted` (conv.rs:34-46)
saves and restores the probe state around nested type-level comparisons.

---

## 5. Iota, projections, recursors, quot, literals

* **Recursor firing** (`fire_recursor`, eval.rs:1695-1732). The major premise is
  normalised to a constructor application by, in order: `major_to_ctor`
  (literal → constructor), `try_k_reduce`, `try_struct_eta_reduce`. Then the
  matching `RecRule` is found by constructor name, and its **RHS is evaluated as
  a value** — `eval_inst(rec_rule.val, rec.info.uparams, levels)`, memoised in
  `rec_rule_cache: (rule-value-expr, levels) -> V` — and then applied by
  `apply_many` to (a) the params/motives/minors prefix of the recursor's
  arguments, (b) the constructor's non-parameter arguments, (c) the arguments
  after the major premise. So yes: the rule RHS becomes a closure/value once per
  `(rule, universe instantiation)` and is then β-applied, rather than being
  substituted syntactically each time.
* **`Nat.rec` on a literal** (`nat_rec_natlit`, eval.rs:1734-1765): if the
  inductive is `Nat` and the major premise is a `NatLit`, the zero/succ minor is
  selected directly and the IH is built as `Nat.rec … (n-1)` with a literal
  predecessor — no `succ`-chain is materialised.
* **K-like reduction** (`try_k_reduce`, eval.rs:1814-1859): if `rec.is_k`, infer
  the type of the major premise, check it is an application of the recursor's
  inductive, rebuild `ctor params…` from the *type's* arguments, and accept only
  if the new constructor's type is convertible with the major's type
  (`conv_types_at`). `k_pre_reduce` (eval.rs:1680-1694) tries this before
  whnf'ing the major at all.
* **Struct eta for the major premise** (`try_struct_eta_reduce`,
  eval.rs:1767-1812): for a neutral major of a structure type, build
  `C p₁…pₙ x.1 … x.k` from projections. Memoised in `struct_eta_cache`.
* **Projections on values** (`do_proj`, eval.rs:1257-1288): whnf the structure;
  if it is a constructor application, take spine element `num_params + idx`;
  if it is a Nat/String literal, expand to constructor form first; otherwise
  extend the spine with a `Proj` elim. Projection *typing* is
  `proj_field_type_with` (eval.rs:1301-1353), which walks the constructor's
  telescope applying earlier projections.
* **Quotient reduction** (`do_quot_iota`/`fire_quot`,
  eval.rs:1905-1950): hardcoded argument positions — the `Quot.mk` argument is at
  index 5 for `Quot.lift` and 4 for `Quot.ind`, with the remaining arguments
  from index 6/5; the result is `f a` applied to the rest. Names come from the
  `NameCache` built once at parse time.
* **Nat literal acceleration** (`do_nat_red_at`, eval.rs:1952-1998, dispatch
  table `name::NatRed`): `succ, add, sub, mul, pow, mod, div, beq, ble, land,
  lor, xor, gcd, shiftLeft, shiftRight`, plus **`Nat.div.go` and
  `Nat.modCore.go`** (5-argument internal helpers reduced straight to div/mod —
  eval.rs:1962-1969). Arithmetic is `num_bigint::BigUint`; `nat_sub`, `nat_div`,
  `nat_mod` implement Lean's total variants (util.rs:532-556). Whether a name is
  a builtin is a *single atomic byte load on the interned name node*
  (`name.as_ref().is_nat_red()`, eval.rs:960-963) — not a hash lookup.
  A deliberate **anti**-optimisation: `nat_red_defer` (eval.rs:965-982) refuses
  to reduce `add/sub/mul/pow` eagerly when the second argument is a literal
  larger than 8 bits, so that e.g. `2^64` is not materialised unless demanded;
  `unfold_value_demand` forces it when conversion really needs it.
* **`Nat.succ n` vs literal**: three places bridge the two representations —
  `try_fire_rigid` (application of `Nat.succ` to a literal folds to a literal),
  `value_to_bignum_at` (eval.rs:2067-2110: peels `succ`s and adds them to a
  literal at the bottom, optionally forcing), and `conv_nat` (conv.rs:688-712,
  compares a literal against a `succ`-form by decrementing).
* **String literals**: `str_lit_to_constructor` (expr.rs:451-489) builds
  `String.ofList (List.cons (Char.ofNat c) …)`; `33f6754` made sure a string
  literal is expanded to constructor form *before* iota.

---

## 6. Type inference / checking

`infer_value(flag, depth, env, ctx, e) -> V` (src/infer.rs:77-172) works on
**syntax** `e` but against a **value** environment `env` (values of the bound
variables) *and* a parallel context `ctx` (values of their **types**), and
returns a **value**.

* **Bound variables**: `Var{dbj_idx}` → `ctx.lookup(dbj_idx)` (infer.rs:79) —
  the type of a bound variable is found in the type context, which is a plain
  cons-list indexed by de Bruijn index (value.rs:424-436). Going under a binder
  introduces `mk_bvar_hc(depth, dom)`, a `Rigid(BVar(level, type))` carrying its
  own type, where `level` is a de Bruijn **level**; the value goes into `env`
  and the type into `ctx` (infer.rs:125-128, 145-147).
* **Inference cache** (infer.rs:110-116, 169-171): keyed by
  `(pruned-env address, Expr)` again, with a `CheckScope` telling whether the
  cached result was obtained in `Check` mode under the current declaration's
  universe parameters — so an `InferOnly` query may reuse a `Check` entry but
  not vice versa.
* **`InferFlag`** (tc.rs:38-42): `Check` performs the definitional-equality side
  conditions (argument type vs. domain, let value vs. its ascription, binder
  types are sorts, universe parameters are declared); `InferOnly` omits them and
  is used when inference is called during *reduction* of terms already known
  well-typed.
* **App** (`infer_app_v`, infer.rs:174-197): collect the spine, infer the
  function type once, then for each argument force the type to a `Pi`, check the
  argument in `Check` mode, and instantiate the codomain — with two shortcuts:
  if the codomain closure's body is closed, just evaluate it; if the body
  ignores its binder, apply the closure to the *domain* value instead of
  evaluating the argument at all (infer.rs:187-194). Arguments whose values are
  never needed are therefore never evaluated.
* **Lambda** (infer.rs:120-141): the result type is
  `Pi(dom, Closure::mk_infer(pruned env, ctx, body))` — i.e. the codomain is a
  *deferred inference*, performed only when the Pi is applied
  (`apply_closure` with `ctx: Some(_)` calls `infer_value(InferOnly, …)`,
  eval.rs:930-936). Commit `49b0e9c` added the special case: when the inferred
  body type is atomic, closed and *equal to the domain*, the closure is replaced
  by a plain evaluation closure over `binder_type`, which makes the resulting Pi
  hash-consable.
* **Proj** (`infer_proj_v`, infer.rs:199-254), including the Prop-structure
  check: projecting a non-proof field out of a `Prop` structure panics.
* **Declaration checking** (infer.rs:256-275):

```rust
pub(crate) fn check_declar_info_v(&mut self, d: &Declar<'t>) {
    assert!(self.ctx.no_dupes_all_params(info.uparams), ...);
    let ty_ty = self.infer_value(Check, 0, empty_env, empty_ctx, info.ty);
    let sort  = self.ensure_sort_v(0, ty_ty);
    if let Declar::Theorem { .. } = d { assert!(self.ctx.is_zero(sort), ...); }
}
pub(crate) fn check_def_like_v(&mut self, d: &Declar<'t>, val: ExprPtr<'t>) {
    self.check_declar_info_v(d);
    let val_ty   = self.infer_value(Check, 0, empty_env, empty_ctx, val);
    let declared = self.eval(0, empty_env, d.info().ty);
    assert!(self.def_eq_at(0, val_ty, declared), "def_eq failed");
}
```

Definitions, theorems and opaques all get the full treatment (tc.rs:99-103);
axioms, constructors and recursors get only `check_declar_info_v` plus
structural checks that the recursor lives in its inductive block
(tc.rs:104-129).

---

## 7. Environment and inductives

* **Storage**: `declars: FxIndexMap<NamePtr, Declar>` built once by the parser
  (util.rs:434). Lookup is **by index, not by hash**: each interned
  `NameNode` stores the declaration's index in an `AtomicU32`, and
  `Env::get_old_declar` (env.rs:276-283) does
  `if idx < self.cutoff { Some(&self.declars[idx]) } else { None }`.
* **Visibility / prefix environments**: an `Env` carries a `cutoff`; checking
  declaration *d* uses `EnvLimit::ByName(d.info().name)` so only declarations
  *earlier in the export file* are visible (tc.rs:97, env.rs:250-258). This is
  what lets independent threads check different chunks of one immutable,
  fully-parsed environment without any synchronisation.
* **Temporary extensions**: `Env::new_w_temp_ext` adds an overlay map, used
  exclusively by the inductive checker for the specialised types it invents when
  handling nested inductives (env.rs:244-266).
* **Inductive installation** (`src/inductive.rs`, 2134 lines) is essentially
  nanoda's, kept **on the syntactic representation**: it builds motives, minor
  premises, recursor types and recursor rules as `Expr`s with the `mk_pis_*` /
  `mk_lambdas_*` helpers (inductive.rs:489-522), then asserts that what it
  reconstructed is definitionally equal to what the export file declared
  (`assert_nonnested_tys_def_eq`, `assert_nonnested_ctors_def_eq`,
  `assert_nonnested_recursors_def_eq`, inductive.rs:1569-1644) — or, for nested
  inductives, `restore_and_check` (inductive.rs:2098+).
* **But it does call into the value machinery.** Telescope walking is done by
  evaluating to a value and forcing (`value_of` + `force_pi`/`weak_pi`,
  quote.rs:142-156; used e.g. at inductive.rs:465-467, 1084-1096), positivity is checked on values
  (`check_positivity1`, inductive.rs:877-902), "does the inductive occur here"
  is a value traversal with its own cache (`value_has_ind_occ`,
  inductive.rs:946-981), valid-application checks look at
  `Value::Rigid { head: RigidHead::Inductive(..) }` (inductive.rs:1025-1073),
  and the results are read back with `quote`. Definitional equality is invoked
  via `def_eq_at`/`assert_def_eq`.
* **Answer to the porting question**: the *logic* of the inductive installer is
  independent of NbE and could keep ConLeche's own installer; what it needs from
  the reduction layer is (i) "force this type to a Pi and give me the domain and
  the instantiated codomain", (ii) "is this a fully applied occurrence of one of
  these inductives", (iii) `def_eq`. In sokonanoda those are all phrased against
  values, but each has a syntactic counterpart (`whnf`, `unfold_apps`,
  `def_eq`). So swapping only whnf/defeq is plausible, *provided* the installer
  can express its telescope walk in terms of whichever representation the new
  reducer exposes.

---

## 8. The "other heavy optimisation tricks"

Ordered roughly by apparent weight.

1. **Hash-consing, at three levels.**
   * Syntax: interned `Expr`/`Level`/`Name`/`Levels`/string/bignum in a global
     (parse-time) and a thread-local table (util.rs:302-379, 700-760). Attributed
     5% (local-first order) + 10% (local-only filtering) in the old README.
   * Values: `bvar_hc, spine_hc, app_hc, env_hc, lam_hc, pi_hc, rigid_hc,
     unfold_hc, content_hc, thunk_hc` in `TcCache` (util.rs:1058-1077), all keyed
     by *addresses* of the parts. `28c03d0` ("share more work") extended this to
     `env_extend` and unified the neutral-application path.
   * Environments: `frames: hashbrown::HashTable<E>` interns the pruned
     environment frames (eval.rs:91-112).
2. **Pointer-equality shortcuts everywhere**: `ptr::eq(x,y)` at the top of
   `unify` (conv.rs:88), `ptr::eq(sx,sy)` in `unify_spine` and `spine_probe`
   (`ba5814a`), `envs_ptr_equal` + same-body-pointer fast paths for Pi and Lam
   (conv.rs:190-213), `LevelPtr` equality before `eq_antisymm` (`4ed825a`,
   level.rs:245, 251-256), and `ptr::eq(next, cur)` as the "did unfolding make
   progress" test.
3. **Sparse environments / fv-masks** (`fe8edcc`). `Expr` carries a 64-bit mask
   of which loose bvars it reads; `key_env` prunes the environment to exactly
   that set, interns the result, and uses its address as a cache key. Effect:
   the evaluation and the inferred type of a subterm are shared across *all*
   telescopes that agree on the variables the subterm actually mentions. The
   prune itself is memoised three ways: a one-slot `Cell` on the environment, a
   1024-entry direct-mapped table `prune_dm` (util.rs:1073), and the frame
   interner. Uses BMI2 `pext` for the slot selection when available
   (eval.rs:523-550).
4. **Caches in `TcCache`** (util.rs:1044-1082), ~35 maps. The interesting ones:
   * `conv_cache_pos / conv_cache_neg / conv_cache_neg_probe` — convertibility
     of value-address pairs, positive *and* negative. Initial capacity 4096.
   * `type_cache: (pruned env, Expr) -> CachedType` — inferred types.
   * `open_eval_cache: (pruned env, Expr) -> V`, `closed_eval_cache: Expr -> V`.
   * `iota_cache`, `iota_stuck`, `struct_eta_cache`, `canon_cache`,
     `fvar_cache`, `ind_occ_cache`, `lam_domain_cache`, `quote_cache`.
   * `unfold_const_cache`, `const_head_type_cache`, `const_head_value_cache`,
     `const_result_level_cache`, `rec_rule_cache` — per `(name, levels)`.
   All of these are **per thread**, and are cleared (`clear_session`,
   util.rs:1178-1216) whenever the value arena is reset, because their keys are
   raw addresses into that arena. Maps grown beyond `KEEP_CAP = 32768` are
   dropped rather than cleared (util.rs:1218-1234).
5. **The persistent whnf store** — the only cache that survives a session
   (`note_whnf`/`store_lookup`, eval.rs:1083-1158). Design:
   * Key: the value's 64-bit content `digest()`; the stored entry is
     `(u128 global_key, ExprPtr quoted_result)`. A hit is only accepted after
     recomputing the 128-bit `global_key` and comparing (eval.rs:1145-1147), so
     a 64-bit collision cannot cause a wrong answer.
   * The result is stored as a **quoted expression** in the long-lived thread
     arena, and re-evaluated on a hit — precisely so it outlives the bump arena
     resets.
   * Admission control: only *closed* values, only after the same digest has
     been seen `WHNF_ADMIT_THRESHOLD = 2` times, tracked in a 4 MiB byte table
     `whnf_admit` (`WHNF_ADMIT_LEN = 1<<22`, util.rs:1350); two 1024×64-bit
     Bloom-style filters (`whnf_store_filter` keyed by the full digest,
     `whnf_head_filter` keyed by a shallow head key) make the miss path a couple
     of loads.
   This is how work is shared *across declarations* on one thread.
6. **Relevance signatures** (`4f0bc57`, src/relevance.rs). For each
   `(constant, universe instantiation)` a `Sig` is computed once and cached in
   `TcCtx::sig_cache`:
   * `prop_arg & arg_known`: argument positions whose domain is *known* to live
     in `Prop` — these arguments are **skipped when comparing two spines with
     the same head** (`unify_spine`, conv.rs:509-513), which is proof
     irrelevance applied without ever inferring a type;
   * `absent_arg` (`absent_args`, relevance.rs:132-159): argument positions that
     the definition's *body* does not mention and whose binder the rest of the
     *type* ignores — also skipped;
   * `prop_result / result_known`: whether the result at each arity is known to
     be a Prop, used by `statically_not_proof` to veto the expensive proof
     irrelevance path (conv.rs:524-545).
7. **Budgeted speculative conversion** (`b38b875`): described in §4. "Compare
   the arguments first, but give up after 2048 steps and unfold instead."
8. **Arena / bump allocation**. Two arenas: `stumpalo::Arena` for interned
   syntax (per process for the parsed DAG; per thread for terms created during
   checking — `8eaaf4b`), and `bumpalo::Bump` for values, reset whenever a
   session exceeds `SESSION_BUDGET = 16 MiB` (tc.rs:9, 142-168). Values are
   never freed individually and never reference-counted. `SessionBump`/
   `SessionCache` (util.rs:1237-1271) reuse the cache *allocations* across
   sessions through an `unsafe` lifetime transmute.
9. **Threads** (tc.rs:184-226). `std::thread::scope`, `num_threads` from the
   config, each thread claiming chunks of `CHUNK_SIZE = 64` declarations with one
   `AtomicUsize::fetch_add`. Shared: the parsed export file (immutable), the
   interned global DAG, and the `AtomicU32`/`AtomicU8` side tables on name nodes.
   Private: the local interner, the value arena, and the whole `TcCache`. There
   is **no cross-thread cache**. Each thread gets a **2 GiB stack**
   (`STACK_SIZE`, lib.rs:27) — the algorithms are deeply recursive.
10. **Parser speed** (`13a9760`, `84023dd`, `fd05f02`). The export file is
    **mmapped** (util.rs:1358-1368); lines are parsed by a hand-written
    byte-level recogniser with a SWAR newline scan (`find_newline`,
    parser.rs:394-417), SWAR digit parsing (`digit_run`/`packed_digits`,
    parser.rs:374-392) and a special-cased fast path for `{"app":…}` lines
    (`fast_line`, parser.rs:843-862) — the commonest line kind. Anything the
    fast path rejects falls back to `serde_json` per line (`slow_line`,
    parser.rs:797-806). stdin input is streamed in 4 MiB chunks cut at the last
    newline (parser.rs:340-366) to bound peak memory. Back-references are
    resolved through `Vec`s indexed by the export file's own indices, tolerating
    sparse/out-of-order indices (`put_at`, parser.rs:634).
11. **Small representational wins**: `Expr` 40 bytes, `Value` 56, `Spine` 32
    (static asserts); `Elim` is one tagged `u64`; `ExprPtr`/`LevelsPtr` are one
    `NonZeroU64` each with metadata in the spare bits; `SpineArgs =
    SmallVec<[V; 8]>` (`0fab887`, eval.rs:13); `mimalloc` as the global
    allocator; `Entry` API to avoid double hash lookups (`9ad006e`).

No commit or README text attributes a fraction of the total speedup to any of
6–11; only the NbE change (35%) and the two interner changes (5%, 10%) are
quantified anywhere in the repository.

---

## 9. What is trusted vs checked

**Checked** (the same obligations the official kernel discharges):

* Every declaration's type is inferred in `Check` mode and must be a sort;
  theorem types must be `Prop` (infer.rs:256-266).
* **Theorem values are fully checked** — `Theorem` goes through
  `check_def_like_v` exactly like `Definition` (tc.rs:100). No "trust the proof"
  shortcut.
* Universe parameters: no duplicates, all parameters occurring in a `Sort` or a
  `Const`'s level list must be declared (infer.rs:81-96).
* Declarations may only refer to *earlier* declarations (the `cutoff`), so the
  environment is built in order, and duplicate names are rejected at parse time
  (parser.rs:1247).
* Inductive blocks: positivity, valid occurrences, uniform parameters, large
  elimination, and — crucially — the constructors and recursors are
  *reconstructed* and asserted definitionally equal to those in the export file
  (inductive.rs:1569-1644, 2029-2110). Recursors must live in their own
  inductive block (tc.rs:106-127).
* `Quot` is checked against a reconstructed axiomatisation, including that `Eq`
  and `Eq.refl` have their expected types (quot.rs:43+).
* Projections out of `Prop` structures into non-`Prop` fields are rejected
  (infer.rs:236-249).
* `is_unsafe` declarations are rejected (`assert!(!is_unsafe)` at
  parser.rs:1301, 1327, 1361, 1381, 1412).
* Axioms must be on the configured allow-list unless
  `unsafe_permit_all_axioms` is set; otherwise they are skipped or hard-error
  (parser.rs:718-727, 1300-1325; `Config` at util.rs:1277-1310).

**Trusted / skipped / different**:

* **Binder names and plicity are discarded**, so nothing about them can be
  checked (they carry no logical content, but a checker that re-exports would
  lose them).
* **`Expr.mdata` is not supported** — the parser panics rather than declining
  (parser.rs:1290).
* **Nat/String acceleration is keyed by name only.** `Nat.add` is whatever
  declaration bears that name; nothing checks that its definition agrees with
  BigUint addition (util.rs:912-940, name.rs:103-115). `Nat.div.go` and
  `Nat.modCore.go` — *internal helpers*, not part of the official kernel's
  builtin set — are reduced by fiat (eval.rs:1962-1969). Both extensions are
  off unless the config enables them.
* **Relevance-based argument skipping** (§8.6) is a soundness-relevant
  shortcut: `absent_arg` positions are not compared at all. The justification is
  that the head's definition ignores them; it is not an axiom of the kernel.
* The **spine probe** can declare two terms equal from their arguments alone
  without ever unfolding — sound for a congruence, but it relies on the spine
  structure (incl. the proj elims) matching exactly.
* **Failure mode is `panic!` with no diagnosis**; `catch_unwind` in `main` maps
  *any* panic to exit 1 (reject). An internal invariant violation is therefore
  indistinguishable from a real rejection — the arena test harness works around
  this by string-matching `"def_eq failed"` (tests/arena.rs:92-98). `Decline`
  (exit 2) is used only by the parser, for version mismatches and for bvar
  indices or literals exceeding implementation limits.
* Several `unsafe` shortcuts are load-bearing: the tagged pointers, the
  `Elim` bit-packing (assumes ≤48-bit addresses and ≥8-byte alignment), the
  `SessionBump::get` lifetime laundering, `transmute_name`. A memory-safety bug
  there is a soundness bug.

---

## 10. Portability notes for a Lean host

| Trick | Rust feature it rests on | Remark for a Lean 4 port |
|---|---|---|
| Interning `Expr`/`Value` with address equality | arena + raw `&'a T` + `NonNull` bit-packing | Lean has no stable address-as-identity for RC'd objects, but `ptrEq`/`ptrAddrUnsafe` works while a value is reachable; an interning table `HashMap Key Expr` in an `ST`/`IO.Ref` gives the same *sharing*. The bit-packed `ExprPtr` (loose-bvar count in the pointer) has no analogue — a field in the object is the equivalent, and Lean's `Expr`-like structures already cache such data. |
| `key: Cell<u64>` lazy content digest | interior mutability on a shared immutable value | Needs a mutable field; in Lean this becomes either an eagerly computed hash field (the usual choice) or a `Thunk`. |
| `canon: Cell<bool>` | interior mutability | Same; or drop it and always canonicalise through the interner. |
| `Unfold { head_value: &OnceCell, forced: OnceCell }` (glued values) | interior mutability + shared arena reference | `Thunk` gives exactly this memoised-once semantics, and `head_value` (shared per `(name, levels)`) is a `Thunk` in a per-constant cache. This is the single most important trick and it ports cleanly. |
| Hash-consing caches keyed by *addresses* | stable arena addresses | Does **not** port directly: Lean object addresses move under RC/compaction assumptions and are not reusable as map keys across a GC-free but RC'd heap. Use content keys (the `digest`) or explicit integer ids assigned at intern time. This is pervasive here (~20 of the 35 caches) and is the main representational obstacle. |
| Cache invalidation by "reset the arena, clear the caches" | bump allocation | In Lean, RC reclaims automatically; the equivalent is to bound cache size, which is *easier*, not harder. |
| `fv_mask` + pruned environments | u64 bitmask on the term, `pext` | Ports directly (`UInt64` and pure bit tricks); `pext` is an optional fast path with a portable fallback already written (eval.rs:528-550). |
| `Env::Framed`/`WideFramed` sparse environments | arena-allocated slices | Ports as arrays; the interning of frames again needs content keys rather than addresses. |
| `Elim` tagged `u64` | `unsafe` pointer packing, 48-bit address assumption | Not portable; use a two-constructor inductive. Cost: one extra allocation per spine element. |
| Persistent whnf store keyed by digest, storing quoted syntax | long-lived arena + `catch_unwind`-free code | Ports well: the key is a content digest, not an address, and the payload is an `Expr`. The Bloom filters are plain `ByteArray`s. Requires a `quote`/readback, which ConLeche would need to add. |
| Relevance `Sig` per constant | `FxHashMap` in the per-thread context | Pure data; ports directly. Needs a *proof* if the checker is verified: skipping Prop-typed and unused arguments is a real proof obligation. |
| Budgeted probe (`probe_budget`, `probe_exhausted`) | mutable counters in the shared cache struct | A state monad / `IO.Ref` counter. Note it makes conversion **non-deterministic in cost but deterministic in answer** only if the budget is fixed — a verified checker must prove the fallback path is taken on exhaustion. |
| Threads sharing an immutable environment, `AtomicUsize` work queue | `std::thread::scope`, shared `&` | `Task`s over disjoint ranges of the declaration array; the shared data is immutable so RC contention on the shared `Expr` DAG is the real question (`lean-rc-linearity`). The per-thread caches would be per-`Task` state. |
| `AtomicU32 decl_idx` on interned names → array-indexed env lookup | interior mutability on a shared interned node | In Lean: a `HashMap Name Nat` computed once, or store the index in the declaration record and resolve names to indices at parse time. |
| 2 GiB stacks | `thread::Builder::stack_size` | Lean's recursion is heap-allocated for `partial`/well-founded definitions but native stack for structural ones; deep `whnf` recursion is a real risk. sokonanoda's `force_all` already converts one such recursion into an explicit stack (eval.rs:1355-1418) — worth copying. |
| mmap + SWAR parser | `memmap2`, `unsafe` byte slicing | `IO.FS.readBinFile` + `ByteArray` scanning; the SWAR tricks port as `UInt64` arithmetic. Gains here matter mostly for very large exports. |
| mimalloc, LTO, codegen-units=1 | cargo profile | No analogue; Lean's allocator is fixed. |

---

## 11. Summary

### Abstract

sokonanoda is a ~13 kloc Rust external kernel for Lean 4 whose conversion check
is normalisation by evaluation in the style of smalltt, wrapped in an unusually
thorough layer of interning and memoisation. Syntax is a 40-byte hash-consed
`Expr` with de Bruijn indices, no binder names, no metadata, a precomputed hash
and a 64-bit mask of the loose variables it reads; pointers to it are packed
`NonZeroU64`s carrying the loose-variable count and an arena tag. Values are
56-byte arena-allocated nodes: neutral `Rigid` values with a head and a
snoc-spine of tagged 8-byte eliminations, `Lam`/`Pi` closures over an
environment, literals, and the key construct, `Unfold` — a constant applied to
a spine that remembers both its folded form and, in `OnceCell`s, the unfolded
one. Evaluation is call-by-value (the `Thunk` constructor exists but is never
built in this commit); the only laziness is δ. Conversion is one big match on a
pair of values, ordered: pointer equality, a positive/negative pair cache, Nat
literal bridging, head-and-spine comparison with a *budgeted speculative probe*
(2048 steps) before falling back to unfolding the side with the larger
reducibility hint, then lambda eta, structure eta and unit-like types, with
proof irrelevance attempted before every unfolding step and vetoed cheaply by a
precomputed per-constant signature. That signature also records which argument
positions are Prop-typed or unused in the definition's body; those are skipped
when comparing spines. Environments are *pruned* to the free-variable mask of
the expression being evaluated and interned, so the evaluation and the inferred
type of a shared subterm collapse across all telescopes that agree on the
variables it mentions. A per-thread whnf store keyed by a 64-bit content digest
(verified against a 128-bit one) and holding *quoted syntax* carries reduction
results across declarations and across value-arena resets, with a
seen-twice admission threshold and Bloom filters on the miss path. Inference
runs on syntax against parallel value/type contexts, introduces de Bruijn-level
variables carrying their own types, and defers a lambda's codomain as an
"infer closure". The inductive installer is nanoda's, still written against
syntax, but it walks telescopes as values and reads back with `quote`.
Parallelism is trivial: the export file is parsed once into an immutable
indexed environment, each declaration sees only its prefix, and threads claim
chunks of 64 declarations; nothing is shared but read-only data. The README
claims ~9× the official kernel on Mathlib; the only quantified individual
contributions in the repository are 35% for the NbE rewrite (at +40% peak
memory) and 5% + 10% for two interner changes.

### The five most surprising things

1. **The persistent whnf store stores *expressions*, not values, keyed by a
   content digest with a 128-bit verifier** (eval.rs:1083-1158). It is the only
   cache that survives an arena reset, it has an admission threshold of two
   sightings and two Bloom filters guarding its miss path, and it is the
   mechanism by which one thread shares reduction work *between declarations*.
   Nothing in nanoda's lineage suggests this.
2. **Conversion skips arguments it can prove irrelevant without inferring
   anything** (relevance.rs). A per-constant bitmask says which argument
   positions are Prop-typed and which the definition's body ignores; both are
   dropped from spine comparison. The same signature is used *negatively*, as a
   cheap veto on the expensive proof-irrelevance path.
3. **The speculative comparison has an explicit budget and a "provisional
   negative" cache** (conv.rs:396-428, `conv_cache_neg_probe`). Comparing
   arguments before unfolding is standard; treating it as a *bet with a
   2048-step stake*, and carefully quarantining the negative results learned
   while the bet was running, is not.
4. **Environments are content-addressed by free-variable mask.** `key_env`
   prunes an environment to exactly the variables the subterm reads and interns
   the result, so the eval cache and the type cache are keyed by "(what this
   term reads, this term)" rather than "(where this term stood, this term)".
   Combined with three layers of pruning memo (a `Cell` on the environment, a
   1024-slot direct-mapped table, the frame interner) and a BMI2 `pext`.
5. **`Value::Thunk` is dead code, and binder names do not exist.** The type that
   makes NbE look lazy is never constructed here — evaluation is strict, and
   sharing comes entirely from hash-consing plus the glued `Unfold`. Meanwhile a
   whole commit (`ceaabb5`) deleted binder names, plicity and the 938-line
   pretty printer from the checker, shrinking `Expr` to 40 bytes; the checker
   consequently cannot print a single readable term, and every failure is an
   unwinding `panic!` that `main` converts to exit 1.

### Cross-reference: shared code with nanoclo

nanoclo's README states explicitly: *"The value representation, the conversion
algorithm, and the fast path of the export parser come from sokonanoda
(Apache-2.0), whose normalisation by evaluation follows smalltt. The closure
machinery above is nanoclo's own."* Concretely, nanoclo's `src/nbe.rs`,
`src/nbe_conv.rs`, `src/nbe_eval.rs` (539 + 685 + 1301 lines) correspond to
sokonanoda's `value.rs`/`conv.rs`/`eval.rs`, and both parsers share the SWAR
fast path. The divergence is that nanoclo *does* use delayed substitutions
(thunks named by the bindings they read, skew-binary environment jump
pointers), which in sokonanoda survives only as the never-constructed
`Value::Thunk`.
