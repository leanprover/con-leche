import Setlec.SetR.Annot.Pass
import Setlec.SetR.Sound.Main

/-!
# Unique kinding, semantically (task #151, tier A)

The tier's semantic half, consuming the **landed** soundness
(`Setlec/SetR/Sound/Main.lean`) and nothing else.  Two facts:

* `ZetaEq.interp_eq` — the semantic reading of the pass's erase
  contract: an annotation's erasure has the interpretation of the term
  it annotates.  (`Setlec/SetR/Annot/Pass.lean` explains why the
  contract is up to zeta.)
* `sortFact_unique` — **unique kinding**: two sort facts about *the same
  type*, under a context that has a satisfying valuation, carry the same
  numeral.

## Unique kinding: the exact statement, and the route

```
    DefEq μ env cval φ Δ tA (.sort u) →
    DefEq μ env cval φ Δ tA (.sort v) →
    Sat V Δ ρ → u = v
```

`DefEq`-soundness is *unconditional* under `Sat` (the T4 architecture),
so both premises read as interpretation equalities at the **one** value
`interp V ρ tA`: `univ u = interp V ρ tA = univ v`.  The numeral is then
recovered by injectivity of the universe tower
(`SetTheory.univ_inj`).

**The membership route does not exist, and that is the tier's headline
negative result.**  One might hope for

```
    interp V ρ A ∈ˢ univ u → interp V ρ A ∈ˢ univ v → u = v
```

which would give cross-tree coherence for free (two annotations of one
term, justified by unrelated derivations, would have to agree).  It is
**false**: the tower is cumulative — `SetTheory.univ_mono` says
`m ≤ n → univ m ⊆ˢ univ n` — so every member of `univ u` is a member of
every `univ v` above it.  Membership fixes a *lower bound* on the sort,
never the sort.  Only the equality `univ u = univ v` separates the
levels, and that needs the two facts to be about the same type.

This is why the tier-A record makes **no cross-tree coherence claim**
(`Setlec/SetR/Annot/Pass.lean`): within one annotation every numeral is
justified in its own context (per-tree correctness, by construction),
and agreement *between* annotations is tier C's business — where the
`∀ ρ, Sat V Δ ρ → …` shape of every statement makes an unsatisfiable
context vacuous, and `sortFact_unique` settles the satisfiable ones,
through the shared inferred type each pair of facts is threaded onto.

## `univ_inj`

`SetTheory.univ_inj` (`Setlec/SetTheory/Derive/Univ.lean`) is the
handle: `univ u = univ v → u = v`, from `univ_mono`, `univ_mem_univ` and
`not_mem_self`.  It did not exist when this tier was written and was
proved here; it is a general fact about the tower with no #151 content,
so it was **relocated verbatim** to its home beside `univ_mono` (the
eighth relocation of the campaign — see `Setlec/SetR/DESIGN.md`).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

/-! ## The erase contract, semantically -/

/-- Zeta-contracting a `let` node does not move the interpretation: the
`letE` clause of `interp` is already the contractum's reading
(`interp_inst0`).  This is the semantic form of `Annotates.zetaEq` — an
annotation's erasure interprets as the term it annotates. -/
theorem ZetaEq.interp_eq {V : Type w} [SetTheory V] :
    ∀ {e e' : VExpr}, ZetaEq e e' →
      ∀ ρ : Nat → V, interp V ρ e = interp V ρ e' := by
  intro e e' h
  induction h with
  | bvar => intro _; rfl
  | sort => intro _; rfl
  | const => intro _; rfl
  | prf => intro _; rfl
  | app _ _ ihf iha => intro ρ; simp only [interp_app, ihf ρ, iha ρ]
  | lam _ _ ihA ihb =>
    intro ρ
    simp only [interp_lam, ihA ρ]
    exact congrArg _ (funext fun x => ihb (cons V x _))
  | pi _ _ ihA ihB =>
    intro ρ
    simp only [interp_pi, ihA ρ]
    exact congrArg _ (funext fun x => ihB (cons V x _))
  | letE _ _ _ _ ihv ihb =>
    intro ρ
    simp only [interp_letE, ihv ρ]
    exact ihb _
  | zeta _ ih =>
    intro ρ
    rw [interp_letE, ← interp_inst0]
    exact ih ρ
  | eqE _ _ _ _ iha ihb => intro ρ; simp only [interp_eqE, iha ρ, ihb ρ]
  | proj _ ih => intro ρ; simp only [interp_proj, ih ρ]

/-! ## Unique kinding -/

section Kinding

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- A sort fact *is* the statement that the type's interpretation is the
universe of that level. -/
theorem interp_eq_univ_of_sortFact (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {tA : VExpr} {u : Nat}
    (hu : DefEq μ env cval φ Δ tA (.sort u))
    {ρ : Nat → V} (hρ : Sat V Δ ρ) : interp V ρ tA = univ u :=
  DefEq.sound henv hu ρ hρ

/-- **Unique kinding, semantic form.**  Two sort facts about the *same*
type agree, at any context with a satisfying valuation.

This is the statement tier C consumes; the proof is exactly the module
docstring's route — `DefEq`-soundness is unconditional, so both facts
read as equalities at the one value `interp V ρ tA`, and `univ_inj`
recovers the numeral. -/
theorem sortFact_unique (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {tA : VExpr} {u v : Nat}
    (hu : DefEq μ env cval φ Δ tA (.sort u))
    (hv : DefEq μ env cval φ Δ tA (.sort v))
    {ρ : Nat → V} (hρ : Sat V Δ ρ) : u = v :=
  univ_inj (V := V)
    ((interp_eq_univ_of_sortFact henv hu hρ).symm.trans
      (interp_eq_univ_of_sortFact henv hv hρ))

/-- The linked form: the two facts need not be about a syntactically
identical type, only about two types the family identifies.  (This is
the shape a consumer that owns a conversion between the two inferred
types uses; `HasSort.ofConv` is its syntactic companion.) -/
theorem sortFact_unique_of_conv (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {tA tA' : VExpr} {u v : Nat}
    (hu : DefEq μ env cval φ Δ tA (.sort u))
    (hconv : DefEq μ env cval φ Δ tA tA')
    (hv : DefEq μ env cval φ Δ tA' (.sort v))
    {ρ : Nat → V} (hρ : Sat V Δ ρ) : u = v :=
  sortFact_unique henv hu (hconv.trans hv) hρ

/-- **What a cached binder sort buys**: the domain's interpretation
inhabits the annotated level.  This is the elimination tier C's
soundness induction performs at every `AVExpr` binder — the whole
purpose of carrying the numeral.

Note what it does *not* buy: the converse.  By cumulativity
(`univ_mono`) the membership holds at every level above `u` too, so it
cannot be read back as "the sort is `u`" — see the module docstring. -/
theorem HasSort.mem_univ (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {A : VExpr} {u : Nat}
    (h : HasSort μ env cval φ Δ A u)
    {ρ : Nat → V} (hρ : Sat V Δ ρ) : interp V ρ A ∈ˢ (univ u : V) := by
  obtain ⟨tA, hA, hu⟩ := h
  have hmem := (Infer.sound henv hA ρ hρ).2
  rwa [interp_eq_univ_of_sortFact henv hu hρ] at hmem

/-- A cached binder sort also gives the domain's own truthfulness
(`Infer`-soundness' subject conjunct) — the second half of what a
binder annotation is worth to tier C. -/
theorem HasSort.annotOkV (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {A : VExpr} {u : Nat}
    (h : HasSort μ env cval φ Δ A u)
    {ρ : Nat → V} (hρ : Sat V Δ ρ) : AnnotOkV V ρ A := by
  obtain ⟨tA, hA, -⟩ := h
  exact (Infer.sound henv hA ρ hρ).1

/-- The pass's erase contract, semantically: an annotation's erasure
interprets as its subject. -/
theorem Annotates.interp_erase {Δ : List VExpr} {e : VExpr} {ea : AVExpr}
    (h : Annotates μ env cval φ Δ e ea) (ρ : Nat → V) :
    interp V ρ ea.erase = interp V ρ e :=
  (h.zetaEq.interp_eq ρ).symm

end Kinding

end Setlec.SetR
