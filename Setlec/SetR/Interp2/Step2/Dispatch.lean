import Setlec.SetR.Interp2.Step2.Lit

/-!
# `CheckStep2`, the dispatch — the clause lemmas against the runs

Where the per-clause lemmas of `Step2/{Infer,WhnfCore,DefEq,Loop}.lean`
meet the checker's own case split.  One lemma per `inferBody` branch,
shaped exactly as `Bridge/Infer.lean`'s `infer_*_claimR` family, with
the conclusion in the annotated currency.

The unfolding recipe is v1's, verbatim — `rw [inferTypeCore_succ]` then
`simp only [inferBody, viewM, Expr.view, …]` — and it transfers
unchanged, because the *checker* is the same function; only what the
clause then produces differs.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level inferTypeCore inferBody
  viewM)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **I1 (`.sort`).**  The clause returns `.sort (.succ u)` outright,
`denote2` evaluates both levels, and the row is `sound_sort`. -/
theorem infer_sort_claim2 (m : EnvS2 V env) {d : Nat} {u : Level}
    {t : Expr} {Δa : List AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.sort u) = .ok t) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.sort u) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind, Except.ok.injEq] at h
  subst h
  refine ⟨.sort (u.eval φ), .sort (u.eval φ + 1), ?_, ?_, ?_⟩
  · rw [denote2]
  · rw [denote2]; simp [Level.eval]
  · intro ρ _
    simpa [Level.eval] using sound_sort V ρ (u.eval φ)

/-- **I2 (`.fvar`).**  The leaf returns its own annotation, so the
claim needs two facts about it that `Claims2`'s hypothesis side does
not carry — see this file's closing note.  Both are taken explicitly
here, in exactly the shape a context correspondence in the annotated
currency would supply, so the clause is usable the moment one exists. -/
theorem infer_fvar_claim2 (m : EnvS2 V env) {d idx : Nat} {n : Name}
    {ty t : Expr} {Δa : List AVExpr} {Aa tya : AVExpr}
    (hi : Δa[d - 1 - idx]? = some Aa)
    (h : inferTypeCore μ env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hden : denote2 μ m.acval env φ (fuel + 1) d ty = some tya)
    (hlink : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ tya
        = interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.fvar idx n ty) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hlt =>
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨.bvar (d - 1 - idx), tya, by rw [denote2], hden, ?_⟩
    intro ρ hρ
    refine ⟨by simp, ?_⟩
    rw [interp2_bvar, hlink ρ hρ]
    exact hρ (d - 1 - idx) Aa hi
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `bvar` is outside the fragment: the checker throws. -/
theorem infer_bvar_claim2 (m : EnvS2 V env) {d i : Nat} {t : Expr}
    {Δa : List AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.bvar i) = .ok t) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.bvar i) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## STOP — the `.fvar` clause refutes `Claims2`'s hypothesis side

`Claims2` was sealed with the context correspondence reused rather than
re-invented: `CtxOkR` at the **erasures** (`Δa.map AVExpr.erase`), on
the reasoning that it is a *function* of the annotated context and so
needs no new relation.  The conclusion side never wanted more.  **The
`.fvar` clause does**, and it wants exactly two things `CtxOkR` states
only in the relational currency:

1. **definedness** — that the leaf's annotation `ty` has a `denote2`.
   `CtxOkR`'s leaf package gives `denote cval env φ d ty = some T`; the
   annotated denotation is a different function and its definedness
   does not follow;
2. **the leaf-to-entry link** — the claim needs
   `ρ k ∈ˢ interp2 ρ tya` while `Sat2` offers
   `ρ k ∈ˢ interp2 (fun j => ρ (j+k+1)) Aa`.  `CtxOkR` bridges the
   corresponding v1 gap with `∃ T', Infer … ∧ DefEq … T' T` — **a
   relational package**, and turning a `DefEq` into an `interp2`
   equality is precisely the move the step-3 map showed does not exist
   (no `VExpr → AVExpr`, so `DefEq` has no `interp2` reading).

So the erasure route is sound for the *conclusion* and insufficient for
the *hypothesis*, and the difference shows up at one clause out of
eleven.  Both facts are taken explicitly above, so `infer_fvar_claim2`
is usable the moment a supplier exists; what it needs is a **context
correspondence stated in the annotated currency** — the `CtxOk2` this
seal's predecessor declined to invent.

*Rule: a hypothesis reused from another currency is only as good as the
weakest clause that reads it.  Check the clause that reads the context,
not the ones that only pass it along.* -/

/-- **The proposed repair**, stated but *not* wired in: `Claims2`'s
statement is a sealed artifact and swapping its context hypothesis is a
junction decision, not a consumer's.

`CtxOk2` is `CtxOkR`'s leaf package transposed — per `fvar` leaf, the
annotation denotes under `denote2`, and its interpretation agrees with
the context entry read in the entry's own tail context.  The second
conjunct is where `CtxOkR`'s `∃ T', Infer … ∧ DefEq …` lived; here it
is the semantic fact directly, because that is what the consumer reads
and the relational form has no `interp2` meaning.

Substituting this for `CtxOkR (Δa.map erase)` in all four claims closes
`infer_fvar_claim2` by supplying both of its explicit hypotheses, and
touches no other clause — the other ten pass the context along without
reading it. -/
def CtxOk2 {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel d : Nat) (Δa : List AVExpr) (e : Expr) :
    Prop :=
  Δa.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2.2 ∧
    ∃ tya Aa,
      denote2 μ m.acval env φ fuel d l.2.2 = some tya ∧
      Δa[d - 1 - l.1]? = some Aa ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ tya
          = interp2 V (fun j => ρ (j + (d - 1 - l.1) + 1)) Aa

/-- `CtxOk2` supplies exactly what `infer_fvar_claim2` takes
explicitly — the repair's correctness, checked rather than asserted. -/
theorem CtxOk2.fvar_leaf {env : Env} {m : EnvS2 V env} {μ : CheckMode}
    {φ : Name → Nat} {fuel d idx : Nat} {n : Name} {ty : Expr}
    {Δa : List AVExpr}
    (hC : CtxOk2 m μ φ fuel d Δa (.fvar idx n ty)) :
    ∃ tya Aa,
      denote2 μ m.acval env φ fuel d ty = some tya ∧
      Δa[d - 1 - idx]? = some Aa ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ tya
          = interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa := by
  obtain ⟨-, hleaf⟩ := hC
  obtain ⟨-, -, tya, Aa, h1, h2, h3⟩ :=
    hleaf (idx, n, ty) (by simp [Expr.fvarLeaves])
  exact ⟨tya, Aa, h1, h2, h3⟩

end Setlec.SetR.Interp2