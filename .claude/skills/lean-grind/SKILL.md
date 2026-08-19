---
name: lean-grind
description: Use when writing or tuning `grind` calls or @[grind] annotations in Lean 4 proofs — covers annotation forms (=, →, ←, cases, ext, etc.), parameters, arithmetic solvers (cutsat), E-matching patterns, case-split behavior, diagnostics, and when grind will diverge and what to do instead.
allowed-tools: Read, Bash, Grep
---

# The `grind` tactic (Lean v4.33.0)

`grind` is an SMT-style proof search: it works **by contradiction**, incrementally
asserting facts and combining cooperating engines:

- **Congruence closure** — tracks equivalence classes of terms; `f a = f b` follows from `a = b`.
- **Constraint propagation** — propagates truth values through `∧/∨/¬/ite/...`.
- **E-matching** — instantiates annotated theorems whose *pattern* matches a term
  in the goal, modulo the current equivalence classes.
- **Case analysis** — splits on `ite`/`dite`, `match`, `@[grind cases]` predicates.
- **Arithmetic solvers** — `lia` (a.k.a. cutsat, linear Int/Nat arith incl. `∣`, `%`, `/`),
  `ring` (commutative (semi)ring/field polynomial equalities), `linarith` (ordered modules),
  `ac` (assoc/comm operators), `order` (pre/partial/linear orders).

Goal terms have *generation* 0; instantiating a theorem from gen-`n` terms produces
gen-`n+1` terms. Limits on generation, instances, rounds, and splits keep search finite.

## Invocation

```lean
grind                                    -- everything annotated + hypotheses
grind [foo, Nat.max_def, bar]            -- add extra theorems (pattern inferred as with @[grind])
grind [= foo, ← bar, → baz]              -- per-lemma modifier, same grammar as the attribute
grind [-List.getElem_append]             -- remove an annotated theorem for this call
grind only [foo, bar]                    -- ONLY the listed theorems (plus solvers); faster
grind?                                   -- succeeds and prints a minimal `grind only [...]`
grind (splits := 3) -splitMatch +splitImp [foo]   -- config before the lemma list
```

Passing a **function name** (`grind [myFun]`) makes its equational lemmas available to
E-matching, i.e. grind can unfold `myFun` at matching call sites. `grind [Nat.max_def]`
similarly teaches grind the definition of `max` on `Nat` (which `lia` needs — see below).

Key config options (`(name := v)` for numbers, `+name`/`-name` for Bools; defaults shown):

| option | default | meaning |
|---|---|---|
| `splits` | 9 | max case-splits per search branch (search tree depth) |
| `ematch` | 5 | max E-matching rounds between case splits |
| `gen` | 8 | max term generation (length of instantiation chains) |
| `instances` | 1000 | max E-matching instances per branch |
| `splitIte` / `splitMatch` | true | split `ite`/`dite` / `match` terms |
| `splitImp` | false | split on propositional antecedent of hypotheses `A → B` |
| `splitIndPred` | false | split all inductive predicates (not just `@[grind cases]`) |
| `matchEqs` | true | use `match`-equations as E-matching theorems |
| `ext` / `funext` / `etaStruct` | true | extensionality theorems / split on lambda `=` / structure eta |
| `lia` / `qlia` | true / false | integer solver / cheap-but-incomplete rational mode |
| `ring` / `ringSteps` | true / 100000 | ring solver / step cap |
| `linarith`, `ac`, `order`, `inj`, `funCC` | true | other engines |
| `zeta` / `zetaDelta` | true | unfold `let` / local definitions during normalization |

Thin wrappers when you want just one solver: `lia`, `grind_order`, `grind_linarith`
(the `cutsat` tactic name is deprecated for `lia`).

## `@[grind]` attribute variants

Attached to theorems (or defs); also usable per-lemma inside `grind [...]`.
Supports `local`/`scoped`, e.g. `@[local grind cases]`, `attribute [grind =] foo`.

| form | pattern source / effect | use for |
|---|---|---|
| `@[grind]` | heuristic: conclusion, then hypotheses L-to-R, until all args covered | general lemmas |
| `@[grind =]` | LHS of the equality conclusion | simp-like rewrites (`f x = ...`) |
| `@[grind =_]` | RHS of the equality | reverse-direction rewrites |
| `@[grind _=_]` | both (macro for `=` and `=_`) | equalities useful both ways |
| `@[grind →]` | multi-pattern from **hypotheses** (forward reasoning) | `h : P x → Q x`-style propagation, e.g. `mem_of_...` |
| `@[grind ←]` | multi-pattern from **conclusion** (backward reasoning) | lemmas fired when their conclusion appears, e.g. `not_mem_empty` |
| `@[grind =>]` (`⇒`) | hypotheses L-to-R, then conclusion | |
| `@[grind <=]` (`⇐`) | conclusion, then hypotheses R-to-L | |
| `@[grind ←=]` | fire an equality conclusion when the *disequality* is assumed | injectivity-like eq lemmas |
| `@[grind cases]` | case-split on this inductive predicate when a hypothesis has this type | inversion |
| `@[grind cases eager]` | split it already during preprocessing | |
| `@[grind intro]` | add all constructors of an inductive predicate as E-matching theorems | proving `Even (x+6)` etc. |
| `@[grind ext]` | extensionality theorem (fired on `a ≠ b`) | |
| `@[grind inj]` | conclusion must be `Function.Injective f` | |
| `@[grind norm]` | use as a normalization (preprocessing simp) rule; best when it *eliminates a symbol entirely* | `max_def`-style eliminations |
| `@[grind unfold]` | unfold this definition during preprocessing | small non-recursive defs |
| `@[grind funCC]` | track partial applications of this constant for congruence closure | |
| `@[grind symbol <prio>]` | bias pattern selection toward/away from a constant (`0` = never in patterns) | |
| `@[grind!]` / `! mod` | pick *minimal* indexable subexpressions as patterns | tighter patterns |
| `@[grind?]` | like `@[grind]` but prints the selected pattern | debugging annotations |

`@[grind]` on a **def** exposes its equational lemmas to E-matching (grind can unfold it
at call sites); prefer this over `@[grind unfold]` for recursive/match-defined functions.

Custom patterns when the heuristic picks badly:

```lean
grind_pattern Rtrans => R x y, R y z        -- multi-pattern: both must match
grind_pattern myThm => f x y where size x < 5   -- also: guard e, is_ground x, gen < n, ...
```

Annotate conservatively: only tag a lemma if instantiating it whenever the pattern
matches is *always* a good idea. Prefer `→`/`←` (conditional firing) over `=`-saturation
for lemmas with many consequences.

## Arithmetic

- **`lia` (cutsat)**: complete for linear `Int`/`Nat` (and `Fin`, `UIntN` via `ToInt`):
  `=`, `≤`, `<`, `≠`, `∣`, `%`, `/` by constants. Nonlinear terms like `x * x` become
  opaque atoms. `+qlia` is faster but incomplete; `-lia` disables.
- **`ring`**: polynomial equalities/disequalities over `Lean.Grind.CommRing`/`Field`
  instances (all core numeric types have them); handles characteristic, `a / b = a * b⁻¹`.
  Cap runaway normalization with `(ringSteps := n)`.
- **`linarith`**: linear inequalities over ordered `IntModule`s (types not embeddable in `Int`).
- Solvers see only what E-matching/normalization surfaces: e.g. `lia` does not know
  the *definition* of `Nat.max`, so add `grind [Nat.max_def]` (or `@[grind norm]` it).

## Diagnostics when grind fails

Failure prints the unsolved goal plus **Goal diagnostics** — grind's shared whiteboard:

- `[facts] Asserted facts` — every fact grind asserted (hypotheses + instances). If an
  expected instantiation is missing here, your pattern never matched.
- `[eqc] Equivalence classes` / `True propositions` / `False propositions` — what grind
  currently knows equal/provable/refutable. Scan for the *missing link*: two terms you
  know are equal sitting in different classes means a lemma/annotation is missing.
- `[ematch] E-matching patterns` — patterns of the theorems actually used.
- `[cases] Case analyses` — splits performed on this branch.
- `[limits] Thresholds reached` — tells you exactly which cap was hit and the option to
  raise, e.g. `(instances := 1000)`, `(splits := 9)`, `(ematch := 5)`, `(liaSteps := ...)`.
- `[cutsat] Assignment satisfying linear constraints` — a countermodel: your goal is
  *not* implied by the linear facts grind has; a nonlinear fact or definition is missing.

`set_option trace.grind.ematch.instance true in example ...` shows every instance as it
is generated — the tool for finding looping lemmas. `@[grind?]` shows chosen patterns.

## Failure / divergence modes and mitigations

- **Instance explosion / timeout**: a saturating lemma (often `_=_` or a bad `=` pattern)
  feeds itself. Find it via the trace, demote it to `→`/`←`, tighten with `grind_pattern
  ... where gen < 2`, or use `grind only [...]` (derive the list with `grind?` on a
  smaller goal). Lowering `(gen := 2)` or `(ematch := 2)` also curbs chains.
- **Split explosion**: many `match`/`ite` sites ⇒ exponential branches. `-splitMatch`,
  `(splits := 3)`, or `split <;> grind` to do the one split you want manually.
- **Large contexts**: grind asserts *everything*; irrelevant hypotheses with matching
  patterns cause noise. `clear` unused hypotheses or use `grind only`.
- **Function-valued equalities / lambdas**: hypotheses like `h : f = fun x => ...` or
  goals full of binders hurt congruence closure (binders block it) and `funext := true`
  splits on lambda equalities. Prefer pointwise lemmas (`h : ∀ x, f x = ...`), or
  `simp only [funext_iff] at h`, or avoid grind here.
- **Nonlinear Int/Nat goals**: `lia` treats `x*y` as an atom and `ring` only does
  equalities. Provide the key nonlinear step as a hypothesis (`have := Nat.mul_le_mul ...`)
  or fall back to `nlinarith`-style manual reasoning.

## Making a library grind-friendly (what to do in this project)

1. State lemmas about each recursive function's behavior on each constructor and tag
   `@[grind =]` (they look like simp lemmas). Tag the function itself `@[grind]` only if
   unfolding at every call site is genuinely desirable.
2. Inversion/agreement lemmas (`f x = some y → ...`) get `@[grind →]`; existence/closure
   lemmas whose conclusion is the trigger get `@[grind ←]`.
3. `@[grind cases]` on inductive predicates you routinely invert; `@[grind intro]` on
   ones you routinely prove.
4. Keep definitions first-order where possible: a `def` returning a function
   (`upd : ... → (Nat → V)`) is much worse for grind than one taking all arguments.
5. After a proof works with bare `grind [a, b, c]`, either promote `a b c` to `@[grind]`
   attributes at their declaration, or keep `grind?`-minimized `grind only` calls.

## Known pitfalls in this project

- `simp [f]; grind` on small goals with `ite`/`Nat.max` works well — simp exposes the
  structure, grind finishes with `lia` + splits.
- grind can **diverge for minutes** on goals containing lambda/do-notation bind chains or
  hypotheses with function equalities. Observed: `simp [upd]; grind` where `upd` is a
  function-valued def diverged. Prefer `split <;> simp_all` or `omega` there; or avoid
  introducing the function equality at all (use pointwise `upd_eq` lemmas).
- `omega` understands `Max.max` but **not** `Nat.max` applications — `simp [Nat.max_def]`
  first, or use `grind` (with `[Nat.max_def]` if needed) instead.
- `Option`/`Except` monad proofs: `@[grind =]` the bind/map simp lemmas and `@[grind cases]`
  nothing — instead split on the scrutinee with `cases h : e <;> grind` when bind chains
  get deep; grind's `splitMatch` handles shallow ones fine.
