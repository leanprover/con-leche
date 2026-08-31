import Setlec.SetR.Annot.Spine2
import Setlec.SetR.Annot.Pass
import Setlec.SetR.Annot.Canon
import Setlec.SetR.EnvS

/-!
# `EnvS2` — the annotated-environment invariant, core (migration step 1)

The interp2 consistency stack's environment invariant, by
**containment**: an `EnvS2` holds the landed collapse-lane `EnvS`
(whose V-free syntactic fields — `wf`, the pins, the stored shapes —
the migration reuses wholesale, the ninth shared-tier reuse) plus the
interp2-side fields.  When the twelve stand over `interp2` the
collapse fields retire and the survivors inline — the containment is
the migration's scaffolding, not its end state.

Core fields: the canonical annotated valuation `acval` with its
erasure link, the interp2 truthfulness of its leaves, and the interp2
membership fact (`mem_type2`).  The recursor law (`RecRulesV2`) is
deliberately **absent**: it is stated by its supplier when the bottoms
migrate (the T5 rule).

## The `CvalAnnot` field is gone; the predicate is not

A tenth field `cval_annot : ∀ μ φ, CvalAnnot μ env base.cval φ` sat
here until the cleanup seal.  It was **projected once** in the whole
tree — `bodies_of_envS2UInImage` (`Interp2/EnvS2UDef.lean`), i.e. by
the measurement of its own residue — and supplied by every `EnvS2`
construction site, so it cost a proof at each of them and bought
nothing.  `CvalAnnot` itself stays exactly where it earns its keep:
as an **explicit hypothesis** of `Annot/Pass.lean`'s two existence
theorems, which is the pattern this structure should have copied.

*Rule (seal 43): withdrawing a field is not withdrawing its
proposition.*  The four probe-level suppliers
(`probeEnvS_cvalAnnot`, `defProbeEnvS_cvalAnnot`,
`lamDefEnvS_cvalAnnot`, `piProbeEnvS_cvalAnnot`) are kept as
standalone theorems — they are content about the probes, not about
the field.

## The currency amendment (the consumer seal's finding)

`annot_ok2`/`mem_type2` were first stated over the `Annotates`
*relation*, because this module landed at migration step 1 — before R1
took canonical annotations.  **They could not serve `denote2`, and the
obstruction is structural, not a missing lemma**: `Annotates` has no
structural `letE` clause (only `zeta`, so it annotates the ζ-reduct),
while `denote2`'s `letE` clause *is* structural and `denote` is
structural there too (`Setlec/Verify/Denote.lean`).  So for any subject
carrying a `let`, a `denote2` output is **not** an `Annotates`
annotation of the same term, and no bridging theorem between the two
can exist as they are stated.

The seam was invisible because it is vacuous on *this* side — stored
terms carry no `letE` today (the checker zeta-expands at annotation
time) — and bites only on **subject** terms, which is exactly what
`Claims2` quantifies over.  Hence the amendment: the two fields are
restated in the `denote2` currency (`acval_ok2`, `mem_type2`), where
coherence is the determinism of a function and a stored leaf has
exactly one annotation.  (`cval_annot`, which stayed in the relational
currency at that seal because it closed a *named ledger obligation*
and was not in the seam, has since been withdrawn — see below.)

*Rule: when a resolution changes the currency of a tier, the fields
that were stated in the old one are not merely stale — check whether
the two currencies can still denote the same object at all before
assuming a bridge exists.*

Alongside: `CtxAnn`/`Sat2` — the annotated context and its
satisfaction, the context currency of the graded soundness in either
formulation (relation-level or run-level).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR

universe w

variable (V : Type w) [SetTheory V]

/-! ## The annotated context -/

/-- A pointwise annotation of a context: entry `i` is annotated in its
own tail context, exactly as `Sat` reads types in the outer
environment. -/
inductive CtxAnn (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : List VExpr → List AVExpr → Prop where
  | nil : CtxAnn μ env cval φ [] []
  | cons {A : VExpr} {Δ : List VExpr} {Aa : AVExpr} {Δa : List AVExpr} :
      Annotates μ env cval φ Δ A Aa →
      CtxAnn μ env cval φ Δ Δa →
      CtxAnn μ env cval φ (A :: Δ) (Aa :: Δa)

/-- `ρ` satisfies an annotated context over `interp2` — the `Sat`
transpose. -/
def Sat2 (Δa : List AVExpr) (ρ : Nat → V) : Prop :=
  ∀ i Aa, Δa[i]? = some Aa →
    ρ i ∈ˢ interp2 V (fun j => ρ (j + i + 1)) Aa

theorem Sat2_nil (ρ : Nat → V) : Sat2 V [] ρ := by
  intro i Aa hi
  cases hi

theorem Sat2_cons {Δa : List AVExpr} {Aa : AVExpr} {ρ : Nat → V} {x : V}
    (hρ : Sat2 V Δa ρ) (hx : x ∈ˢ interp2 V ρ Aa) :
    Sat2 V (Aa :: Δa) (cons x ρ) := by
  intro i Aa' hi
  cases i with
  | zero =>
    obtain rfl : Aa = Aa' := by simpa using hi
    exact hx
  | succ i =>
    have h := hρ i Aa' (by simpa using hi)
    exact h

/-- The annotation of a `CtxAnn` entry, positionally. -/
theorem CtxAnn.get {μ : CheckMode} {env : Env} {cval : TConstVal}
    {φ : Name → Nat} :
    ∀ {Δ : List VExpr} {Δa : List AVExpr},
      CtxAnn μ env cval φ Δ Δa →
      ∀ i A, Δ[i]? = some A → ∃ Aa, Δa[i]? = some Aa ∧
        Annotates μ env cval φ (Δ.drop (i + 1)) A Aa := by
  intro Δ Δa h
  induction h with
  | nil => intro i A hi; cases hi
  | @cons A' Δ' Aa' Δa' hA _ ih =>
    intro i A hi
    cases i with
    | zero =>
      obtain rfl : A' = A := by simpa using hi
      exact ⟨Aa', rfl, by simpa using hA⟩
    | succ i =>
      obtain ⟨Aa, h1, h2⟩ := ih i A (by simpa using hi)
      exact ⟨Aa, by simpa using h1, by simpa using h2⟩

/-! ## The invariant -/

/-- The annotated-environment invariant (see the module docstring). -/
structure EnvS2 (env : Env) where
  /-- the landed collapse-lane invariant, contained: its V-free
  syntactic fields serve both stacks during the migration -/
  base : EnvS V env
  /-- **the canonical annotated valuation** — the annotated leaf each
  stored constant contributes to `denote2`.  An install-fixed object,
  which is what makes annotation coherence the *determinism of a
  function* rather than a relational invariant (R1, WALL 3's
  resolution) -/
  acval : Name → (Name → Nat) → AVExpr
  /-- `acval` erases to the collapse-lane valuation: `denote2_erase`'s
  hypothesis, i.e. exactly what makes a canonical annotation an
  annotation *of* the denotation -/
  acval_erase : ∀ (n : Name) (ψ : Name → Nat),
    (acval n ψ).erase = base.cval n ψ
  /-- every canonical valuation leaf is **closed**, in the only form
  `AVExpr` can say it: lifting is the identity at every cut.  The
  transpose of `EnvS.cval_closed`, and the field the dispatch quarter's
  context-threading lemmas (`CtxOk2.open`, `CtxOk2.weakenTop`) were
  carrying as an explicit `hacl` premise for want of a supplier — T5:
  a fired-law premise belongs to the supplier, not to every consumer.

  Note this field is *syntactic*, a condition on an install-fixed
  object with no `denote2` in it, so unlike the two STOP 2 refuted it
  cannot go false at a small fuel.  `AVExpr` has no `Closed` predicate
  and this deliberately does not add one — the lifting equation is
  what the consumers actually rewrite with. -/
  acval_closed : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
    (acval n ψ).liftN 1 k = acval n ψ
  /-- **the canonical valuation reads only its own level
  parameters** — the `acval` transpose of `EnvS.val_params`.

  Named by the defeq quarter as `AcvalParams2` and correctly
  identified there as *a missing environment field, not a missing
  proof*: it is the sole ingredient of `denote_const_congrR` beyond
  `Level.isEquivList` soundness, and the `const`/`const` case of
  `isDefEqCore` cannot close without it.  T5 — the premise belongs to
  its supplier.

  Syntactic, like `acval_closed`: an equation between two `acval`
  readings with no `denote2` in it, so the smallest-fuel hazard that
  refuted `acval_defn` cannot reach it. -/
  acval_params : ∀ (n : Name) (ci : ConstantInfo),
    env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      acval n ψ₁ = acval n ψ₂
  /-- every canonical valuation leaf is truthful over `interp2` —
  `annot_okV`'s successor.  Quantifying over `Annotates` (this field's
  shape before this seal) collapses here: in the `denote2` currency a
  stored leaf has exactly *one* annotation, namely `acval n ψ` -/
  acval_ok2 : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOk2 V ρ (acval n ψ)
  /-- every definition is canonically annotated by its body — the
  `denote2` successor of `EnvS.defn_eq`, and what makes the reduction
  loop's **delta step** free: the unfolded term's canonical annotation
  *is* the constant's own leaf, so the step moves neither the
  interpretation nor the invariant.

  The annotation is produced at a fuel `F' ≥ F` of the *supplier's*
  choosing, not at every fuel.  Demanding every fuel makes the field
  **false** — `denote2` returns `none` on binders at fuel `1`, so a
  single λ-bodied definition would empty the structure
  (`envS2_defn_lam_refuted`).  The existential form is what the delta
  exit actually consumes, and it composes with the reduction claims'
  own `F ≤ F'` slack -/
  acval_defn : ∀ (μ : CheckMode) (φ : Name → Nat) (F : Nat)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∃ F', F ≤ F' ∧
      denote2 μ acval env φ F' 0 value = some (acval cv.name φ)
  /-- ditto for theorems (`EnvS.thm_ok`'s successor), in the same
  existential form and for the same reason — a proof of any implication
  is a `λ` (`envS2_thm_lam_refuted`) -/
  acval_thm : ∀ (μ : CheckMode) (φ : Name → Nat) (F : Nat)
    (cv : ConstantVal) (value : Expr),
    ConstantInfo.thmInfo cv value ∈ env.consts →
    ∃ F', F ≤ F' ∧
      denote2 μ acval env φ F' 0 value = some (acval cv.name φ)
  /-- every stored constant inhabits its canonically-annotated type
  over `interp2` — `mem_type`'s successor in the `denote2` currency -/
  mem_type2 : ∀ (μ : CheckMode) (φ : Name → Nat) (fuel : Nat),
    ∀ c ∈ env.consts, ∀ ta : AVExpr,
    denote2 μ acval env φ fuel 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, interp2 V ρ (acval c.name φ) ∈ˢ interp2 V ρ ta

namespace EnvS2

/-- The empty environment's invariant: the empty `cval` is the bare
`.const .empty [0]` leaf at every name — its canonical annotation is
the same constructor one level up (so `acval_erase` is `rfl`),
truthfulness is the constant clause's `True`, and the membership field
is vacuous over `env.consts = []`. -/
noncomputable def empty : EnvS2 V Env.empty where
  base := EnvS.empty V
  acval := fun _ _ => .const .empty [0]
  acval_erase := fun _ _ => rfl
  acval_ok2 := fun _ _ _ => by simp
  acval_closed := fun _ _ _ => rfl
  acval_params := fun _ _ _ _ _ _ => rfl
  acval_defn := by intro μ φ F cv value hint hc; cases hc
  acval_thm := by intro μ φ F cv value hc; cases hc
  mem_type2 := by
    intro μ φ fuel c hc
    cases hc

end EnvS2

end Setlec.SetR.Interp2
