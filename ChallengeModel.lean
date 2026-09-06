import Setlec.Cached.ParsedC
import Setlec.Semantics.Sem

/-!
# Comparator challenge: the model

The checker's acceptance claim in model form (config in
`comparator-model.json`, proofs in `SolutionModel.lean`).  Trusted here:
the shipped checker up to its driver `checkDeclsSPCachedD`, the
`SetTheory` interface with its derived set constructions, and `Sem`, the
interpretation of a checker term (`Setlec/Semantics/Sem.lean`).

## What to read

Beyond the checker (the theorem's subject: its `Expr`, `ConstantInfo`
and `Env` are the data the statement ranges over), the statement's
meaning rests on these declarations and nothing else:

* **The interface** `SetTheory V` (`Setlec/SetTheory/Core.lean`):
  membership `Mem`; extensionality; the operations `upair`, `sUnion`,
  `power`, `image` (replacement) with their membership laws; regularity;
  and `univChain`, an ω-chain of Grothendieck universes
  (`IsTGUniverse`, with `Equinumerous` for Tarski's clause).
* **The encodings** (`Setlec/SetTheory/Derive/*`, each one to three
  lines): `empty`; `sing`, `upair`, the Kuratowski pair `kpair`; `sep`
  (separation, from replacement); `graph F A` (the graph of `F` on `A`),
  `sigmaPairs`, and `piSet A B` (the graphs in `A → B x`, a dependent
  product); `app f a` (the value of graph `f` at `a`; `pt` when `f = pt`,
  a proof applied to anything is a proof); `sfst`/`ssnd` (the pair
  projections, by `Classical.choose`); the proof point `pt`, the
  singleton `{{∅, {{∅}}}}` chosen fresh from pairs and graphs, with
  `unitSet = {pt}`, `truthVal p` (`unitSet` if `p` else `∅`) and
  `univZero = power unitSet`, the two truth values; and `univ`, `Sort 0`
  to `univZero` and `Sort (n+1)` to `univChain (n+2)`.
* **The two regimes** (`Setlec/SetModel/Ops.lean`): `piR v A B` is the
  truth value of "every `x ∈ A` has some `y ∈ B x`" at `v = 0` and
  `piSet A B` otherwise; `lamR v A F` is `pt` at `v = 0` and
  `graph F A` otherwise.
* **The interpretation** `Sem`, one rule per syntax form, with `push`
  (extend the variable environment), `regime` (the binder's annotation
  evaluated at `φ`: `0` when it says "proposition") and `projV`
  (`sfst ∘ ssnd^i`).  A literal denotes what its constructor form
  denotes, the checker's `natLitToConstructor` and `strLitToConstructor`;
  a term that does not resolve has no denotation.  `Sem_functional`
  below says a term has at most one.
* **Levels and annotations**: `Level.eval` and `Level.substFn`
  (`Setlec/Verify/Level.lean`, an assignment of naturals to universe
  parameters and its transport along an instantiation), and
  `PropWhen.holds` (the checker's annotation datum, "all these
  parameters are zero").
-/

namespace Setlec

open SetTheory

/--
If the checker at `cfgP` (what `setlec --verified`, the default, runs)
accepts `ds` with environment `env'`, then in every model `V` of
`SetTheory` there is a set `cval n φ` for every constant `n` and level
assignment `φ` such that, under `Sem`, every stored definition and
theorem denotes its body and every stored constant is a member of its
type.  In particular every theorem's statement is true.
-/
theorem model_exists (V : Type w) [SetTheory V]
    (h : Cached.checkDeclsSPCachedD cfgP ds = .ok env') :
    ∃ cval : Name → (Name → Nat) → V,
      (∀ (cv : ConstantVal) (value : Expr),
        ((∃ hint, ConstantInfo.defnInfo cv value hint ∈ env'.consts) ∨
          ConstantInfo.thmInfo cv value ∈ env'.consts) →
        ∀ (φ : Name → Nat) (ρ : Nat → V),
          Semantics.Sem cval env' φ 0 ρ value (cval cv.name φ)) ∧
      (∀ c ∈ env'.consts, ∀ (φ : Name → Nat) (ρ : Nat → V),
        ∃ T, Semantics.Sem cval env' φ 0 ρ c.toConstantVal.type T ∧ cval c.name φ ∈ˢ T) :=
  sorry

/-- `Sem` is functional: a term has at most one denotation. -/
theorem Sem_functional (V : Type w) [SetTheory V]
    (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat)
    (d : Nat) (ρ : Nat → V) (e : Expr) {v w : V}
    (hv : Semantics.Sem cval env φ d ρ e v) (hw : Semantics.Sem cval env φ d ρ e w) :
    v = w :=
  sorry
