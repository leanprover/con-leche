import Setlec.SetR.Interp2.LevelLocal

/-!
# Seal 65's residue is **false**: `IotaLevelParamsW` has a countermodel

Seal 65 left `IotaLevelParams` (`Setlec/SetR/Interp2/LevelLocal.lean`)
open: `iotaRec` never relates a recursor redex's level arguments `us`
to the recursor's own `cv.levelParams`, so
`rhs.instantiateLevelParams cv.levelParams us` at a *short* `us` can
carry a level parameter that the subject never had — but no
countermodel had been built, and the seal noted that a firing iota must
still pass the rule lookup, both `iotaCerts` and the index comparison,
so those gates might already force the arity.

**They do not.**  This file exhibits a three-constant environment that
satisfies `EnvWF` and a redex that fires `iotaRec` at
`us.length = 1 < 2 = cv.levelParams.length`, leaking `.param w` into
the reduct.  So the residue as stated cannot be discharged: it is
false, not merely unproven.

## Why the gates do not bite

Every gate that mentions a level mentions the **constructor's**, never
the recursor's:

* `Level.isEquivList usj (cvj.levelParams.map (Level.subst lps us ∘ .param))`
  compares the major's levels against the *constructor's* parameters
  substituted — vacuous when the constructor has none;
* the two `iotaCerts` calls instantiate `cv.type` and `cvj.type`, so
  they can only see a leaked parameter that **occurs in those types**;
* the index comparison reads `cvj.type` only.

So a leak survives whenever the offending parameter occurs in the
rule's `rhs` and *nowhere* in the recursor's own type or the
constructor's level list.  `ConstWF` permits exactly that: it bounds
`RecRule.rhs`'s parameters by `cv.levelParams` and asks nothing about
occurrence.

## Scope of the claim, stated honestly

* This refutes `IotaLevelParams`/`IotaLevelParamsW` **as stated** — the
  quantification is over every `EnvWF` environment, and `EnvWF` is a
  purely syntactic invariant (closedness, parameters-within-declared,
  constants-resolve, loose-bvar bounds).  Nothing here says the
  environment is one the checker's install path could produce.
* On an *install-shaped* recursor every level parameter does occur in
  the recursor's type (the motive's sort) or in the constructor's level
  list, and then the `iotaCerts`/`isEquivList` gates do appear to force
  the arity back.  **That observation is not proved here** and is not
  claimed.
* The reference kernels all guard where we do not — see the report
  accompanying this file: official C++ `src/kernel/inductive.h:105`,
  lean4lean `Lean4Lean/Inductive/Reduce.lean:98`, and nanoda's
  `assert_eq!` in `subst_expr_levels` (`src/expr.rs:387`).  So the
  omission is a deviation of ours, and the closing move is the guard
  `us.length = cv.levelParams.length` in `iotaRec` — a *kernel* change,
  not this lane's to make.
-/

namespace Setlec.SetR.Interp2
namespace IotaArity

/-! ## The countermodel environment

`T : Type` with one nullary constructor `T.mk`, and a recursor
`T.rec.{u, w}` whose stored type is the level-free `T → T → T → T`
and whose single plain rule has right-hand side `Sort w`.  `w` is the
*second* level parameter, so a one-element `us` leaves it standing
(`Level.subst.go` runs the two lists in lockstep and falls through to
`.param n` once either is exhausted).
-/

/-- `T` -/
def nT : Name := Name.str .anonymous "T"
/-- `T.mk` -/
def nMk : Name := (Name.str .anonymous "T").str "mk"
/-- `T.rec` -/
def nRec : Name := (Name.str .anonymous "T").str "rec"
/-- the recursor's first level parameter (substituted) -/
def uName : Name := Name.str .anonymous "u"
/-- the recursor's second level parameter (**leaked**) -/
def wName : Name := Name.str .anonymous "w"

/-- The recursor's stored type, `T → T → T → T`: three `∀`s, so
`stripPis (mI + 1)` succeeds, and level-free, so instantiating it at a
short `us` hides nothing from `iotaCerts`. -/
def recTy : Expr :=
  .forallE .anonymous (.const nT [])
    (.forallE .anonymous (.const nT [])
      (.forallE .anonymous (.const nT []) (.const nT []) ⟨.default⟩)
      ⟨.default⟩)
    ⟨.default⟩

/-- The single rule: a canonical (`.plain`) rule on the nullary
constructor whose right-hand side mentions the second level
parameter. -/
def theRule : RecRule :=
  { ctor := nMk, nfields := 0, ctorParams := 0, fire := .plain,
    rhs := .sort (.param wName) }

/-- The environment: `T`, `T.mk`, `T.rec`. -/
def env : Env :=
  ⟨[.recInfo ⟨nRec, [uName, wName], recTy⟩ 2 2 [theRule],
    .ctorInfo ⟨nMk, [], .const nT []⟩ 0 0,
    .indInfo ⟨nT, [], .sort (.succ .zero)⟩ default]⟩

/-- The redex `T.rec.{0} T.mk T.mk T.mk` — **one** level argument
against **two** declared level parameters. -/
def redex : Expr :=
  .app (.app (.app (.const nRec [.zero]) (.const nMk []))
    (.const nMk [])) (.const nMk [])

/-- The reduct the checker actually produces. -/
def reduct : Expr :=
  .app (.app (.sort (.param wName)) (.const nMk [])) (.const nMk [])

/-! ## The three facts -/

/-- The environment is well-formed. -/
theorem envWF : EnvWF env := by
  intro c hc
  simp only [env, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · refine ⟨rfl, rfl, rfl, rfl, by rintro _ _ _ ⟨⟩, ?_, by rintro _ _ ⟨⟩⟩
    rintro cv mI rP rules ⟨rfl⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨rfl, rfl, rfl, rfl, by rintro _ _ ⟨⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, by rintro _ _ _ ⟨⟩, by rintro _ _ _ _ ⟨⟩,
      by rintro _ _ ⟨⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, by rintro _ _ _ ⟨⟩, by rintro _ _ _ _ ⟨⟩,
      by rintro _ _ ⟨⟩⟩

/-- The redex fires, at either mode. -/
theorem iota_fires (μ : CheckMode) :
    Setlec.iotaRecP μ env 16 0 redex = .ok (some reduct) := by
  cases μ <;> with_unfolding_all rfl

/-- The redex mentions no level parameter. -/
theorem redex_clean : redex.allLevelParamsDefined [] = true := rfl

/-- The reduct mentions `w`. -/
theorem reduct_dirty : reduct.allLevelParamsDefined [] = false := rfl

/-- **Seal 65's residue is false.**  `IotaLevelParams` fails at an
environment that `EnvWF` accepts. -/
theorem not_iotaLevelParams (μ : CheckMode) : ¬ IotaLevelParams μ env := by
  intro h
  exact absurd (h [] 16 0 redex reduct redex_clean (iota_fires μ))
    (by rw [reduct_dirty]; exact Bool.noConfusion)

/-- **The repaired shape is false too**: `EnvWF` is exactly what the
countermodel satisfies. -/
theorem not_iotaLevelParamsW (μ : CheckMode) : ¬ IotaLevelParamsW μ env :=
  fun h => not_iotaLevelParams μ (h envWF)

end IotaArity
end Setlec.SetR.Interp2
