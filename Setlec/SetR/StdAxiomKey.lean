import Setlec.SetR.Install.Axiom
import Setlec.Verify.StdAxiomPin

/-!
# The standard axioms' inhabitation key (task #148, T5)

`StdAxiomKeyS`, split by name as `stdAxiomOk` splits.

**The witnesses are the layer's own constants.**  `BConst.propext` and
`BConst.choice` exist, with `bval .propext = pt` and
`bval .choice us = choiceV V (lv us 0)`, and `TT/Semantics/ConstOk.lean`
already proves each inhabits *the layer's* type.  So the witness
obligations — closedness, level-invariance, `AnnotOkV` — are
one-liners, and the TT lane's syntactic `Iff.rec`/`Nonempty.rec`
elimination is **not needed**: `HasType` cannot see `bval`, but
membership is semantic, so the checker's hypothesis domain need only
be shown to *force* the conclusion.  `Model/StdAxioms.lean` is the
template, not `TTVerify/StdAxiomKey.lean`.

What is left, per half, is the forcing argument: `⟦Iff a b⟧` inhabited
forces `a = b`, and `⟦Nonempty A⟧` inhabited forces `A` inhabited.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory
universe w
variable {V : Type w} [SetTheory V]

/-- The `propext` half of `StdAxiomKeyS`. -/
def PropextKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → cvA.name = propextName →
    env.find? cvA.name = none →
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t

/-- The `Classical.choice` half. -/
def ChoiceKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → cvA.name = choiceName →
    env.find? cvA.name = none →
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t

/-- The two halves assemble. -/
theorem stdAxiomKeyS_of (hp : PropextKeyS V) (hc : ChoiceKeyS V) :
    StdAxiomKeyS V := by
  intro env m cvA hok hfresh
  by_cases hn : cvA.name = propextName
  · exact hp m hok hn hfresh
  · by_cases hn2 : cvA.name = choiceName
    · exact hc m hok hn2 hfresh
    · exfalso
      unfold stdAxiomOk at hok
      rw [if_neg hn, if_neg hn2] at hok
      exact nomatch hok

/-- `propext`'s pinned type, denoted. -/
theorem denote_propext_typeS {cval : TConstVal} {env : Env}
    {cvI : ConstantVal} {caps : IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    denote cval env ψ 0 propextA.type =
      some (.pi (.sort 0) (.pi (.sort 0)
        (.pi (VExpr.mkAppN (cval iffName ψ) [.bvar 1, .bvar 0])
          (VExpr.mkAppN (cval eqName (Level.substFn ψ
              eqA.toConstantVal.levelParams [.succ .zero]))
            [.sort 0, .bvar 2, .bvar 1])))) := by
  have hI : ∀ d, denote cval env ψ d (.const iffName [])
      = some (cval iffName ψ) :=
    fun d => denote_const_nolevelsS hfI hlpI ψ d
  have hQ : ∀ d, denote cval env ψ d (.const eqName [.succ .zero])
      = some (cval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [.succ .zero])) := by
    intro d
    rw [denote_const, hEq]
    exact if_pos rfl
  simp only [iffName, eqName] at hI hQ
  simp [propextA, denote_forallE, denote_sort, Expr.instantiate1,
    denote_app, denote_fvar, VExpr.mkAppN, hI, hQ, Level.eval,
    iffName, eqName]

end Setlec.SetR
