import Setlec.SetR.Interp2.Step2.AssemblyP
import Setlec.SetR.Interp2.EnvS2U

/-!
# `EnvS2PM` — the P-tier environment invariant (task #161, P4)

The install tier's target, per the P4 design note in DESIGN.md: the
denote2-free environment carrier (`EnvS2Core`) *contained*, plus the
fields the P bundles read.  (Batch 8 slimmed the containment from
`EnvS2UM` to `EnvS2Core` — the FINDING in `Annot/EnvS2Core.lean`: the
P fold stores `denoteP`-numeraled leaves and so can never supply the
denote2-currency fields, which the P surface never reads.)  The deltas
against the canonical fields, each a payoff of the fuel-free reading:

* **existence, not uniqueness** — `defn_reads` is `AcvalDefnInstP`
  (batch 4): a stored definition's or theorem's value *reads*, to the
  constant's own leaf.  The canonical `acval_defn` retreated to a
  uniqueness form because all-fuel existence is refutable
  (`envS2_defn_lam_refuted` — `denote2` fails on binders at small
  fuel); `denoteP` has no fuel, and a checked value is never out of
  fragment.
* **the stored types read, are graded, and are inhabited** —
  `type_reads`/`type_okP`/`mem_typeP`, at the *uninstantiated* type
  over every ground assignment; `denotePInstLevels` (an equality)
  delivers every instantiated form, so no arity or fuel bookkeeping
  appears anywhere.
* **the leaves are bit-valid** — `acval_validV`, `acval_ok2`'s
  `AnnotValidV` companion; establishment at install is the P2 front
  door's own validation, transported by the claims.

The bundle-supplying layer below (`constTypeP_of` the worked example;
its siblings follow the same three-field read) is what the quarter
induction (`checkSoundP_of_inputs`) consumes — the structure exists so
that a `Nonempty (EnvS2PM …)` carried through the declaration fold
makes the induction's hypotheses *facts*.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable (V : Type w) [SetTheory V]

/-- **The P-tier environment invariant, at one mode** (see the module
docstring). -/
structure EnvS2PM (μ : CheckMode) (env : Env) where
  /-- the denote2-free environment carrier, contained (batch 8: the
  P fold stores `denoteP`-numeraled leaves, so it can never supply the
  denote2-currency fields `EnvS2UM` carries — and the P surface reads
  none of them) -/
  base2 : EnvS2Core V env
  /-- every leaf is bit-valid (`acval_ok2`'s `AnnotValidV` half) -/
  acval_validV : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotValidV V ρ (base2.acval n ψ)
  /-- every stored type reads, at every ground assignment -/
  type_reads : ∀ c ∈ env.consts, ∀ ψ : Name → Nat,
    ∃ ta : AVExpr,
      denoteP base2.acval env ψ 0 c.toConstantVal.type = some ta
  /-- the stored types' readings are graded -/
  type_okP : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : AVExpr),
    denoteP base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, AnnotOkP V ρ ta
  /-- stored constants inhabit their types' readings -/
  mem_typeP : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : AVExpr),
    denoteP base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V,
      interp2 V ρ (base2.acval c.name ψ) ∈ˢ interp2 V ρ ta
  /-- stored definition and theorem values read, to the constant's own
  leaf (existence — the fuel-free upgrade of `acval_defn`) -/
  defn_reads : AcvalDefnInstP base2
  /-- the two `Nat`-literal head facts, at every assignment -/
  nat_heads : ∀ φ : Name → Nat, NatHeadsP base2 φ

namespace EnvS2PM

variable {V}
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The leaf bit-validity residue, read off the field. -/
theorem acvalValidP (m : EnvS2PM V μ env) : AcvalValidP m.base2 :=
  m.acval_validV

/-- **The `const` residue, derived — the worked example of the
bundle-supplying layer.**  The three type fields at the composed
assignment `Level.substFn φ ks us`, carried to the instantiated form
by `denotePInstLevels` (an equality: no arity premise, no fuel). -/
theorem constTypeP (m : EnvS2PM V μ env) : ConstTypeP m.base2 φ := by
  intro d n ci us hf hlen
  have hmem := Setlec.SetR.Env.find?_mem hf
  have hname := Setlec.SetR.Env.find?_name hf
  obtain ⟨ta, hta⟩ :=
    m.type_reads ci hmem (Level.substFn φ ci.toConstantVal.levelParams us)
  have hwf := m.base2.base.wf ci hmem
  -- the reading is closed, hence depth-free
  have hcl : ∀ k : Nat, ta.liftN 1 k = ta := fun k =>
    denoteP_closed m.base2.acval_erase m.base2.base.cval_closed
      hwf.1 hwf.2.2.2.1 hta 1 k
  have hdepth :
      denoteP m.base2.acval env
          (Level.substFn φ ci.toConstantVal.levelParams us) d
          ci.toConstantVal.type = some ta :=
    denoteP_depth_of_closed m.base2.acval_closed hwf.1 hcl hta d
  -- the instantiated type's reading, by the crossing
  have hcross :
      denoteP m.base2.acval env φ d
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us)
        = denoteP m.base2.acval env
            (Level.substFn φ ci.toConstantVal.levelParams us) d
            ci.toConstantVal.type :=
    denotePInstLevels m.base2 φ ci.toConstantVal.levelParams us d
      ci.toConstantVal.type
  refine ⟨ta, ?_, m.type_okP ci hmem _ ta hta, ?_⟩
  · rw [hcross]; exact hdepth
  · have := m.mem_typeP ci hmem _ ta hta
    rwa [hname] at this

end EnvS2PM

/-- The empty environment carries the P invariant (the fold's base
case): the core is the mode-indexed empty's projection, and every P
field is vacuous — no constants, guards false, and the empty leaf
`.const .empty [0]` is bit-valid because a constant leaf carries no
binder. -/
noncomputable def EnvS2PM.empty (V : Type w) [SetTheory V]
    (μ : CheckMode) : EnvS2PM V μ Env.empty where
  base2 := (EnvS2UM.empty (V := V) μ).toCore
  acval_validV := fun _ _ _ => by
    show AnnotValidV V _ (.const .empty [0])
    simp
  type_reads := fun c hc => nomatch hc
  type_okP := fun c hc => nomatch hc
  mem_typeP := fun c hc => nomatch hc
  defn_reads := fun ψ cv value hmem => by
    rcases hmem with ⟨hint, hdt⟩ | hdt
    · exact nomatch hdt
    · exact nomatch hdt
  nat_heads := fun φ hg => by
    rw [show Setlec.natLitSupported Env.empty = false from rfl] at hg
    exact nomatch hg

end Setlec.SetR.Interp2
