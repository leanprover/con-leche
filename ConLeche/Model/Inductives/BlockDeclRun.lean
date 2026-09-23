module

public import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecPreRun

public section

/-!
# `declBlock` at the run — the composition (task #315, lane RM49)

`declBlock` (`DeclBlock.lean`) takes the recursor stage as ONE
hypothesis, `hrec`; `blockRecStaged_data` (`BlockRecData.lean` §A.18)
turns it into the stage's remaining obligations at one environment and
one valuation; the dispatch (`BlockRecPreHpre.lean`) and the rule
contract (`BlockRuleFit.lean`) produce the two largest of them.  This
file is where they meet.

## 1. The `ℓ = 0` arm's LEFT side

The endpoint's `ℓ = 0` arm (`blockRuleRhsOk_base`) asks for two facts:
the stored rule reads as the point (`blockRuleRaZ_run`, off the fourth
kernel guard) and the recursor's TYPE is a truth value.  The second is
here, because it needs the elimination-level package
(`blockRecElimLevel_run`) and the level PIN (`blockRecElimPin_run`),
both downstream of the endpoint's file: the type's binder bits follow
its conclusion's inferred sort, the pin equates that sort with the
checked elimination level `structElimLevel p.elim p.large`, and a
Π-tower whose head bit is `0` is a truth value. -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section TyZero

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **THE `ℓ = 0` ARM'S LEFT SIDE**: at a valuation where the checked
elimination level is zero, every recursor's type reads as a truth
value — so the recursor's value is the point, and so is every
application of it.  `FixRecLaw.lean`'s `hRpt`, at the block route. -/
theorem blockRecTyZ_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∀ j, j < rs.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ j) ∈ˢ (univZero : V) := by
  intro j hj ψ ρ hℓ
  obtain ⟨_, uOf, -, -, hbits, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hu : (uOf j).eval ψ = 0 := by
    have := blockRecElimPin_run h hruns ψ hj
    rw [hℓ] at this
    exact this
  obtain ⟨-, -, -, -, heq, hlen, -⟩ :=
    checkBlockRecK_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hj) ψ
  rw [heq]
  cases hrds : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ j with
  | nil => rw [hrds] at hlen; exact absurd hlen (by simp)
  | cons d rest =>
    have hd : d.2.1 = 0 :=
      (hbits ψ j hj d (by rw [hrds]; exact List.mem_cons_self)).mpr hu
    show interp V ρ (.pi d.1 d.2.1 d.2.2 _) ∈ˢ _
    rw [interp_pi, hd]
    exact piR_zero_mem_univZero

end TyZero

/-! ## 2. The composition

`declBlock_run` is `declBlock_data` at the lane's component choices —
`nCt := blockRecNCt`, the four syntactic components
`blockRulePdomsAV`/`blockRuleFdomsAV`/`blockRuleEsAV`/`blockRuleMkAV` —
with every seam conjunct that the run already pays DISCHARGED and the
rest named in ONE premise, `howed`, quantified over exactly what the
seam hands (the recursor stage's run and the constructors' records,
and — lane RM49's widening — that the block data IS the run's
`blockDataOf`).  `howed`'s conjuncts are the honest list of what the
composition still needs; each carries its owner in the comment above
it. -/

section Compose

/-- The seam's `nCt` bound: a recursor carries `blockRecNCt` rules. -/
theorem blockRecNCt_ge {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) : r.2.2.2.length ≤ blockRecNCt rs j := by
  rw [blockRecNCt, List.getD_eq_getElem?_getD, hr]
  exact Nat.le_refl _

end Compose

end ConLeche.Model
