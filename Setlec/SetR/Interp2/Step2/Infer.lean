import Setlec.SetR.Annot.EnvS2U
import Setlec.SetR.Interp2.Claims2

/-!
# `CheckStep2`, the inference quarter — Tier A clauses

Per-clause lemmas for `InferClaims2`, one per `inferBody` branch, in
the shape the dispatch lemma consumes: the clause's own run fact plus
the induction hypotheses at `fuel`, producing the claim's conclusion at
the node.

The campaign map (`Setlec/SetR/DESIGN.md`, "the induction's map") fixes
the discipline: **depth-increasing recursion goes through the IH at
`fuel`; depth-preserving iteration goes through the continuation at
`budget`.**  `inferBody` is pure recursion — it never loops — so every
clause here is IH-only, and no budget appears.

Tier A is the clauses whose suppliers are landed: the leaves
(`.sort`/`.fvar`/`.const`) need no IH at all, and the structural
clauses compose an IH with the matching row of
`Interp2/Skeleton.lean`.  The literal clauses are Tier B (the
transposition batch) and iota does not appear in this quarter.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name Level inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The leaves

No induction hypothesis, no frame consumption beyond definedness: the
clause's conclusion *is* the matching skeleton row. -/

/-- **`.sort`.**  `inferBody` returns `.sort (.succ u)` outright, and
`denote2` evaluates both levels, so the row is `sound_sort` at the
evaluated numeral. -/
theorem inferStep2_sort (m : EnvS2UM V μ env) {d : Nat} {u : Level}
    {Δa : List AVExpr} :
    ∀ {ea ta : AVExpr},
      denote2 μ m.acval env φ 0 d (.sort u) = some ea →
      denote2 μ m.acval env φ 0 d (.sort (.succ u)) = some ta →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  intro ea ta hea hta ρ _
  rw [denote2] at hea hta
  obtain rfl := Option.some.inj hea
  obtain rfl := Option.some.inj hta
  simpa [Level.eval] using sound_sort V ρ (u.eval φ)

/-- **`.fvar`.**  The clause returns the leaf's own annotation, and the
context correspondence hands the membership over: the row is
`sound_bvar` at the index the leaf opens. -/
theorem inferStep2_fvar (m : EnvS2UM V μ env) {d idx : Nat} {n : Name}
    {ty : Expr} {Δa : List AVExpr} {Aa : AVExpr}
    (hi : Δa[d - 1 - idx]? = some Aa) :
    ∀ {ea : AVExpr},
      denote2 μ m.acval env φ 0 d (.fvar idx n ty) = some ea →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧
          ρ (d - 1 - idx)
            ∈ˢ interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa := by
  intro ea hea ρ hρ
  rw [denote2] at hea
  obtain rfl := Option.some.inj hea
  exact sound_bvar V hρ hi

/-! ## The structural clauses

Each composes the induction hypotheses at the subterms with the
matching row.  Stated over the rows' *inputs* rather than over the
checker's run, so that the dispatch lemma — which owns the run — feeds
them and they stay independent of `inferBody`'s exact spelling. -/

/-- **`.forallE`.**  `sound_pi` at the two sort facts the clause's own
`ensureSort` runs supply. -/
theorem inferStep2_pi {ρ : Nat → V} {u v : Nat} {Aa Ba : AVExpr}
    (hokA : AnnotOk2 V ρ Aa)
    (hokB : ∀ x, x ∈ˢ interp2 V ρ Aa → AnnotOk2 V (cons x ρ) Ba)
    (hA : interp2 V ρ Aa ∈ˢ (univ u : V))
    (hB : ∀ x, x ∈ˢ interp2 V ρ Aa →
      interp2 V (cons x ρ) Ba ∈ˢ (univ v : V)) :
    AnnotOk2 V ρ (.pi u v Aa Ba) ∧
      interp2 V ρ (.pi u v Aa Ba)
        ∈ˢ interp2 V ρ (.sort (Setlec.TT.imax u v)) :=
  sound_pi V hokA hokB hA hB

/-- **`.lam`.**  `sound_lam`; the kind-`0` fibre premise is the #152
codomain check's worth, and the row needs **no** empty-domain side
condition (campaign record). -/
theorem inferStep2_lam {ρ : Nat → V} {u v : Nat} {Aa ba Ba : AVExpr}
    (hokA : AnnotOk2 V ρ Aa)
    (hokb : ∀ x, x ∈ˢ interp2 V ρ Aa → AnnotOk2 V (cons x ρ) ba)
    (hb : ∀ x, x ∈ˢ interp2 V ρ Aa →
      interp2 V (cons x ρ) ba ∈ˢ interp2 V (cons x ρ) Ba)
    (hcod : v = 0 → ∀ x, x ∈ˢ interp2 V ρ Aa →
      interp2 V (cons x ρ) Ba ∈ˢ (univZero : V)) :
    AnnotOk2 V ρ (.lam v Aa ba) ∧
      interp2 V ρ (.lam v Aa ba) ∈ˢ interp2 V ρ (.pi u v Aa Ba) :=
  sound_lam V hokA hokb hb hcod

/-- **`.app`.**  `sound_app`, at both kinds — the clause the app slot's
kind-`0` amendment made a theorem rather than a residue. -/
theorem inferStep2_app {ρ : Nat → V} {u v : Nat} {fa aa Aa Ba : AVExpr}
    (hokf : AnnotOk2 V ρ fa) (hoka : AnnotOk2 V ρ aa)
    (hf : interp2 V ρ fa ∈ˢ interp2 V ρ (.pi u v Aa Ba))
    (ha : interp2 V ρ aa ∈ˢ interp2 V ρ Aa)
    (hcod : v = 0 → ∀ x, x ∈ˢ interp2 V ρ Aa →
      interp2 V (cons x ρ) Ba ∈ˢ (univZero : V)) :
    AnnotOk2 V ρ (.app fa aa) ∧
      interp2 V ρ (.app fa aa) ∈ˢ interp2 V ρ (Ba.inst aa) :=
  sound_app V hokf hoka hf ha hcod

/-- **`.letE`.**  ζ is annotation-free: the row is an identity on the
body's facts at the substituted value. -/
theorem inferStep2_letE {ρ : Nat → V} {Ta va ba Ba : AVExpr}
    (hokT : AnnotOk2 V ρ Ta) (hokv : AnnotOk2 V ρ va)
    (hokb : AnnotOk2 V (cons (interp2 V ρ va) ρ) ba)
    (hb : interp2 V (cons (interp2 V ρ va) ρ) ba
      ∈ˢ interp2 V (cons (interp2 V ρ va) ρ) Ba) :
    AnnotOk2 V ρ (.letE Ta va ba) ∧
      interp2 V ρ (.letE Ta va ba)
        ∈ˢ interp2 V (cons (interp2 V ρ va) ρ) Ba :=
  sound_letE V hokT hokv hokb hb

/-- **`.proj`, field 0.**  The subject's `Σ`-package is the invariant's
own proj clause, so the row consumes nothing else. -/
theorem inferStep2_projFst {ρ : Nat → V} {ea : AVExpr}
    (hok : AnnotOk2 V ρ (.proj 0 ea)) :
    ∃ (u : Nat) (A : V), A ∈ˢ (univ u : V) ∧
      interp2 V ρ (.proj 0 ea) ∈ˢ A :=
  sound_proj_fst V hok

/-- **`.proj`, field 1.** -/
theorem inferStep2_projSnd {ρ : Nat → V} {ea : AVExpr}
    (hok : AnnotOk2 V ρ (.proj 1 ea)) :
    ∃ (v : Nat) (Bf : V → V),
      interp2 V ρ (.proj 1 ea) ∈ˢ Bf (sfst (interp2 V ρ ea)) ∧
      Bf (sfst (interp2 V ρ ea)) ∈ˢ (univ v : V) :=
  sound_proj_snd V hok

/-! ## Seal 6/7 — what the amendment did to this layer

**Nothing, and that is the finding worth recording.**  Eight of the
ten rows above (`pi`, `lam`, `app`, `letE`, the two `proj`s, and the
two hereditary halves they carry) mention **no fuel at all**: they are
`Interp2/Skeleton.lean`'s rows at the clause's own inputs, and the
amended claims changed only *which fuel* an input is available at, not
what the input is.  So `InferQ.lean`'s re-pointed clauses consume the
same rows, and the layer is fuel-agnostic by construction.

The two leaf rows are pinned at fuel `0` for no reason but the
spelling — `denote2`'s `sort` and `fvar` equations do not read the
fuel — so their fuel-general twins are below.  They are what a clause
holding a subject's annotation at the amended claim's arbitrary `F`
consumes.

*Rule, for the next amendment: a statement layer that names no fuel
survives a fuel repair untouched.  The cost of the repairs landed one
layer up, at the clauses, and one layer down, in the residues — never
here.*
-/

/-- **`.sort`, at any annotation fuel.**  `inferStep2_sort` with the
`0` freed; `denote2`'s `sort` equation is fuel-free. -/
theorem inferStep2_sortF (m : EnvS2UM V μ env) {F d : Nat} {u : Level}
    {Δa : List AVExpr} :
    ∀ {ea ta : AVExpr},
      denote2 μ m.acval env φ F d (.sort u) = some ea →
      denote2 μ m.acval env φ F d (.sort (.succ u)) = some ta →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  intro ea ta hea hta ρ _
  rw [denote2] at hea hta
  obtain rfl := Option.some.inj hea
  obtain rfl := Option.some.inj hta
  simpa [Level.eval] using sound_sort V ρ (u.eval φ)

/-- **`.fvar`, at any annotation fuel.**  `inferStep2_fvar` with the
`0` freed; `denote2`'s `fvar` equation returns the de Bruijn index and
does not recurse into the annotation, so no fuel is read. -/
theorem inferStep2_fvarF (m : EnvS2UM V μ env) {F d idx : Nat}
    {n : Name} {ty : Expr} {Δa : List AVExpr} {Aa : AVExpr}
    (hi : Δa[d - 1 - idx]? = some Aa) :
    ∀ {ea : AVExpr},
      denote2 μ m.acval env φ F d (.fvar idx n ty) = some ea →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧
          ρ (d - 1 - idx)
            ∈ˢ interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa := by
  intro ea hea ρ hρ
  rw [denote2] at hea
  obtain rfl := Option.some.inj hea
  exact sound_bvar V hρ hi

end Setlec.SetR.Interp2
