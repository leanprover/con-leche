import Setlec.SetR.SortSpec.Agree

/-!
# The converse is FALSE — mechanized

Seal 2 proved agreement in one direction: where `sortSpec` commits,
the checker's `sortOfE` returns the same level (`sortSpec_agree`).
The **converse** — completeness, "`sortOfE` succeeds ⟹ `sortSpec`
commits" — is not merely unproved.  It is false, and this file is its
tombstone.

Seal 2 recorded the countermodel as prose and flagged the evidential
grade itself: per (P4) an inherited paper argument is at a different
grade from this campaign's mechanized refutations, and a pilot must
not spend one as though it were the other.  So here it is, built.

## The witness

    def Alias : Type 1 := Type   -- a def whose VALUE is a sort
    axiom Foo  : Alias              -- declared type is a constant

`Foo` really is a type: `Alias` unfolds to `Type = Sort 1`, so
`Foo : Sort 1`.  Both functions are asked for `Foo`'s sort.

* `sortOfE` **reduces**: it infers `Alias`, δ-unfolds it to `Sort 1`,
  reads the level, and answers `1` (`converse_sortOfE`).
* `sortSpec` **does not reduce**: it reads `Foo`'s declared type
  `.const Alias []`, finds no syntactic sort, and answers `none`
  (`converse_sortSpec`).

`not_sortSpec_complete` puts the two together.

## What it pins down

This is exactly the `DeltaSortLinked` neighbourhood, and it shows the
gap is **unreachable by refutation, not merely by proof**: no strength
of a δ-sort-linking theorem can rescue completeness, because the
sortSpec side never takes the δ step that would expose the sort.

It also prices seal 1's `.const` decision precisely.  The partiality
that let agreement escape `DeltaSortLinked` is the *same* partiality
that makes the converse false.  One decision, both consequences —
there is no version of `sortSpec` that keeps the first and avoids the
second without an environment-order recursion (see seal 1).
-/

namespace Setlec.SetR.SortSpec

open Setlec (Env Expr Level Name CheckMode ConstantInfo ConstantVal
  inferTypeCore whnf whnfLoop whnfBody pureFns whnfLoopFuel)
open Setlec.SetR.Interp2 (sortOfE)

private def aliasName : Name := .str .anonymous "Alias"
private def fooName : Name := .str .anonymous "Foo"

/-- `def Alias : Type 1 := Type` — declared type `.sort 2`, value
`.sort 1`. -/
private def aliasDecl : ConstantInfo :=
  .defnInfo ⟨aliasName, [], .sort (.succ (.succ .zero))⟩
    (.sort (.succ .zero)) (.regular 1)

/-- `axiom Foo : Alias` — a declared type that is a *constant*, not a
syntactic sort, but which unfolds to one. -/
private def fooDecl : ConstantInfo :=
  .axiomInfo ⟨fooName, [], .const aliasName []⟩

/-- The two-constant countermodel environment. -/
private def cmEnv : Env := ⟨[aliasDecl, fooDecl]⟩

/-! ## The `sortSpec` side: `none` -/

/-- `sortSpec` reads `Foo`'s declared type, sees `.const Alias []`,
and declines: reading a level through the unfolding would be δ. -/
theorem converse_sortSpec :
    sortSpecE cmEnv [] (.const fooName []) = none := rfl

/-! ## The `sortOfE` side: `some 1`

The run infers `Alias`, then `whnf` δ-unfolds it and lands on
`Sort 1`.  Two loop iterations: one to unfold, one to see that the
reduct is already head-normal. -/

/-- The step budget admits the two iterations the chain needs (the
`whnfLoopFuel_succ` pattern, at depth two). -/
private theorem whnfLoopFuel_two : ∃ n, whnfLoopFuel = n + 1 + 1 :=
  ⟨99998, by unfold whnfLoopFuel; rfl⟩

private theorem converse_infer (μ : CheckMode) (F : Nat) :
    inferTypeCore μ cmEnv (F + 2) 0 (.const fooName [])
      = .ok (.const aliasName []) := rfl

private theorem converse_whnf (μ : CheckMode) (F : Nat) :
    whnf μ cmEnv (F + 2) 0 (.const aliasName [])
      = .ok (.sort (.succ .zero)) := by
  obtain ⟨k, hk⟩ := whnfLoopFuel_two
  rw [Setlec.whnf_succ]
  show whnfLoop (pureFns μ cmEnv (F + 1)) cmEnv 0 whnfLoopFuel _ = _
  rw [hk]
  rfl

/-- **The checker answers `1`.**  `Foo` is a type of sort `1`, and
`sortOfE` finds that out by reducing. -/
theorem converse_sortOfE (μ : CheckMode) (φ : Name → Nat) (F : Nat) :
    sortOfE μ cmEnv φ (F + 2) 0 (.const fooName []) = some 1 := by
  simp only [sortOfE, converse_infer, converse_whnf, Except.toOption]
  rfl

/-! ## Realizability

The countermodel is not junk input: both declarations are ones the
checker accepts.  `Alias`'s value `Sort 1` infers `Sort 2`, which is
its declared type on the nose; and `Foo`'s declared type `Alias`
infers `Sort 2`, so it passes the `ensureSort` an axiom's type must.
Both are `rfl`. -/

theorem cm_alias_value_types (μ : CheckMode) (F : Nat) :
    inferTypeCore μ cmEnv (F + 2) 0 (.sort (.succ .zero))
      = .ok (.sort (.succ (.succ .zero))) := rfl

theorem cm_foo_type_is_a_type (μ : CheckMode) (F : Nat) :
    inferTypeCore μ cmEnv (F + 2) 0 (.const aliasName [])
      = .ok (.sort (.succ (.succ .zero))) := rfl

/-! ## The refutation -/

/-- **`sortSpec` is not complete for `sortOfE`.**  There is an
environment and a subject on which the checker computes a sort and the
structural function declines — so no premise set that leaves
`sortSpec`'s `.const` clause reduction-free can recover the converse
of `sortSpec_agree`. -/
theorem not_sortSpec_complete :
    ¬ (∀ (env : Env) (μ : CheckMode) (φ : Name → Nat) (F d : Nat)
        (e : Expr) (k : Nat),
        sortOfE μ env φ F d e = some k →
        ∃ u : Level, sortSpecE env [] e = some u ∧ u.eval φ = k) := by
  intro hall
  obtain ⟨u, hu, -⟩ :=
    hall cmEnv .noModel (fun _ => 0) 2 0 (.const fooName []) 1
      (converse_sortOfE .noModel (fun _ => 0) 0)
  rw [converse_sortSpec] at hu
  exact nomatch hu

/-- The same fact as a bare disagreement, for the record: one
environment, one subject, `some 1` against `none`. -/
theorem converse_gap :
    sortOfE .noModel cmEnv (fun _ => 0) 2 0 (.const fooName [])
        = some 1 ∧
      sortSpecE cmEnv [] (.const fooName []) = none :=
  ⟨converse_sortOfE .noModel (fun _ => 0) 0, converse_sortSpec⟩

end Setlec.SetR.SortSpec
