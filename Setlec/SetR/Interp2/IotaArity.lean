import Setlec.SetR.Interp2.LevelLocal

/-!
# The environment that bought checker change #9 — now a regression test

## What this file used to be

Seal 65 left `IotaLevelParams` (`Setlec/SetR/Interp2/LevelLocal.lean`)
open: `iotaRec` never related a recursor redex's level arguments `us`
to the recursor's own `cv.levelParams`, so
`rhs.instantiateLevelParams cv.levelParams us` at a *short* `us` could
carry a level parameter the subject never had.  The seal noted that a
firing iota must still pass the rule lookup, both `iotaCerts` and the
index comparison, so those gates might already force the arity.

**They did not.**  This file exhibited a three-constant environment
satisfying `EnvWF` and a redex that fired `iotaRec` at
`us.length = 1 < 2 = cv.levelParams.length`, leaking `.param w` into
the reduct.  It carried four theorems:

* `iota_fires`  — `iotaRecP μ env 16 0 redex = .ok (some reduct)`;
* `reduct_dirty` — the reduct mentions `w`;
* `not_iotaLevelParams` — `¬ IotaLevelParams μ env`;
* `not_iotaLevelParamsW` — `¬ IotaLevelParamsW μ env`.

Together they refuted the residue **as stated**: over an arbitrary
`EnvWF` environment the unpatched `iotaRec` did not preserve the
subject's level parameters.

## Why the gates did not bite

Every gate that mentions a level mentions the **constructor's**, never
the recursor's:

* `Level.isEquivList usj (cvj.levelParams.map
  (Level.subst lps us ∘ .param))`
  compares the major's levels against the *constructor's* parameters
  substituted — vacuous when the constructor has none;
* the two `iotaCerts` calls instantiate `cv.type` and `cvj.type`, so
  they can only see a leaked parameter that **occurs in those types**;
* the index comparison reads `cvj.type` only.

So a leak survived whenever the offending parameter occurred in the
rule's `rhs` and *nowhere* in the recursor's own type or the
constructor's level list.  `ConstWF` permits exactly that: it bounds
`RecRule.rhs`'s parameters by `cv.levelParams` and asks nothing about
occurrence.

## What happened next

The reference kernels all guard where we did not — official C++
`src/kernel/inductive.h:105`, lean4lean
`Lean4Lean/Inductive/Reduce.lean:98`, and nanoda's `assert_eq!` in
`subst_expr_levels` (`src/expr.rs:387`).  So the omission was a
deviation of ours, and the closing move was the guard
`us.length = cv.levelParams.length` in `iotaRec`.  That guard is
**checker change #9** (`Setlec/Kernel/Core.lean`, ungated, with the
`iotaRecI`/`iotaRecNC` twins carrying it too).

This file is therefore **not** a refutation any more, and the four
theorems above are not weakened tombstones: the checker was fixed, so
what they denied became true.  `Setlec/Verify/LevelPres.lean` now
proves `iotaRec_lvlParamsW` outright, and
`Setlec/SetR/Interp2/LevelLocal.lean` proves `iotaLevelParamsW` from
it.  What remains here is the *regression test*: the same environment,
the same redex, and `iota_blocked` — the redex no longer fires.  If
the guard is ever removed, `iota_blocked` breaks.
-/

namespace Setlec.SetR.Interp2
namespace IotaArity

/-! ## The environment

`T : Type` with one nullary constructor `T.mk`, and a recursor
`T.rec.{u, w}` whose stored type is the level-free `T → T → T → T`
and whose single plain rule has right-hand side `Sort w`.  `w` is the
*second* level parameter, so a one-element `us` would leave it
standing (`Level.subst.go` runs the two lists in lockstep and falls
through to `.param n` once either is exhausted).
-/

/-- `T` -/
def nT : Name := Name.str .anonymous "T"
/-- `T.mk` -/
def nMk : Name := (Name.str .anonymous "T").str "mk"
/-- `T.rec` -/
def nRec : Name := (Name.str .anonymous "T").str "rec"
/-- the recursor's first level parameter (substituted) -/
def uName : Name := Name.str .anonymous "u"
/-- the recursor's second level parameter (**would leak**) -/
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

/-- The reduct the *unpatched* checker produced (`iota_fires`), kept
as the record of what the leak looked like. -/
def reduct : Expr :=
  .app (.app (.sort (.param wName)) (.const nMk [])) (.const nMk [])

/-! ## The facts -/

/-- The environment is well-formed — so nothing about the countermodel
was ruled out by `EnvWF`, then or now. -/
theorem envWF : EnvWF env := by
  intro c hc
  simp only [env, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · refine ⟨rfl, rfl, rfl, rfl, by rintro _ _ _ ⟨⟩, ?_,
      by rintro _ _ ⟨⟩⟩
    rintro cv mI rP rules ⟨rfl⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨rfl, rfl, rfl, rfl, by rintro _ _ ⟨⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, by rintro _ _ _ ⟨⟩, by rintro _ _ _ _ ⟨⟩,
      by rintro _ _ ⟨⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, by rintro _ _ _ ⟨⟩, by rintro _ _ _ _ ⟨⟩,
      by rintro _ _ ⟨⟩⟩

/-- **The regression test.**  Checker change #9's level-arity guard
stops the redex at the door: it no longer fires, at either mode.  This
is where `iota_fires` used to stand. -/
theorem iota_blocked (μ : CheckMode) :
    Setlec.iotaRecP μ env 16 0 redex = .ok none := by
  cases μ <;> with_unfolding_all rfl

/-- The redex mentions no level parameter. -/
theorem redex_clean : redex.allLevelParamsDefined [] = true := rfl

/-- …and the reduct the unpatched checker would have handed back
mentions `w`.  That gap — clean in, dirty out — is what the guard
closes. -/
theorem reduct_dirty : reduct.allLevelParamsDefined [] = false := rfl

end IotaArity
end Setlec.SetR.Interp2
