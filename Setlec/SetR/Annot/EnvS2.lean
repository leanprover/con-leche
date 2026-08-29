import Setlec.SetR.Annot.Spine2
import Setlec.SetR.Annot.Pass
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

Core fields this seal: the **annotation clauses as fields** (the tier-C
carried-obligations ledger's two `CvalAnnot` clauses, now supplied by
the environment rather than hypothesized), the interp2 truthfulness of
justified valuation annotations, and the interp2 membership fact
(`mem_type2`) in the conditional-on-type-annotation form.  The
recursor law (`RecRulesV2`) is deliberately **absent**: it is stated
by its supplier when the bottoms migrate (the T5 rule).

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
  /-- every stored valuation annotates, and λ-shaped stored valuations
  have sorted types — the two `CvalAnnot` clauses, now environment
  fields (closing the tier-C carried-obligations ledger's supplier
  question in the direction it named) -/
  cval_annot : ∀ (μ : CheckMode) (φ : Name → Nat),
    CvalAnnot μ env base.cval φ
  /-- every justified annotation of a stored valuation is truthful
  over `interp2` — `annot_okV`'s successor -/
  annot_ok2 : ∀ (μ : CheckMode) (φ : Name → Nat) (Δ : List VExpr)
    (n : Name) (ψ : Name → Nat) (ea : AVExpr),
    Annotates μ env base.cval φ Δ (base.cval n ψ) ea →
    ∀ ρ : Nat → V, AnnotOk2 V ρ ea
  /-- every stored constant inhabits its denoted type over `interp2`,
  through any justified annotations of the value and the type —
  `mem_type`'s successor, conditional on the type-side annotation
  (vacuous where none exists, exact where the consumer holds one) -/
  mem_type2 : ∀ (μ : CheckMode) (φ : Name → Nat),
    ∀ c ∈ env.consts, ∀ t,
    denoteClosed base.cval env φ c.toConstantVal.type = some t →
    ∀ (Δ : List VExpr) (ea ta : AVExpr),
    Annotates μ env base.cval φ Δ (base.cval c.name φ) ea →
    Annotates μ env base.cval φ Δ t ta →
    ∀ ρ : Nat → V, interp2 V ρ ea ∈ˢ interp2 V ρ ta

namespace EnvS2

/-- The empty environment's invariant: the empty `cval` is the bare
`.const .empty [0]` leaf at every name — it annotates by
`Annotates.const`, every annotation of it *is* that constructor
(syntax-directed inversion), truthfulness is the constant clause's
`True`, and the membership field is vacuous over `env.consts = []`. -/
noncomputable def empty : EnvS2 V Env.empty where
  base := EnvS.empty V
  cval_annot := by
    intro μ φ
    refine ⟨fun n ψ Δ => ⟨.const .empty [0], .const⟩, ?_⟩
    intro n ψ Δ T _ hlam _
    exact absurd hlam (by simp [EnvS.empty, emptyT, VExpr.isLam])
  annot_ok2 := by
    intro μ φ Δ n ψ ea h ρ
    cases h
    simp
  mem_type2 := by
    intro μ φ c hc
    cases hc

end EnvS2

end Setlec.SetR.Interp2
