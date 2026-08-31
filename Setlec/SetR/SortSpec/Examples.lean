import Setlec.SetR.SortSpec.Defs

/-!
# `sortSpec` worked instances

Machine-checked sanity for the definition in `SortSpec/Defs.lean`,
against `inferBody`'s own answers (`Kernel/Core.lean`).  Each block
records what the checker computes and what `sortSpec` computes.

These double as the *smallest-instance* and *vacuity* probes seal 0
requires for the substitution theorem (`SortSpec/Subst.lean`).
-/

namespace Setlec.SetR.SortSpec

open Setlec (Expr Level Name)

/-- A toy oracle: `Nat : Sort 1` and nothing else. -/
def natOnly : SortEnv := fun c _ n =>
  if c = Setlec.natName ∧ n = 0 then some (.succ .zero) else none

private def bm : Setlec.BinderMeta := ⟨.default⟩
private def nm : Name := .anonymous

/-! ## `Sort u : Sort (u+1)` — `inferBody`'s `.sort` clause -/

example : sortSpec natOnly [] (.sort .zero) = some (.succ .zero) :=
  rfl

/-! ## `∀ (_ : Nat), Prop` — the checker's `imax` of the two sorts -/

example :
    sortSpec natOnly []
        (.forallE nm (.const Setlec.natName []) (.sort .zero) bm)
      = some (.imax (.succ .zero) (.succ .zero)) := rfl

/-! ## The telescope case `∀ (α : Sort u) (_ : α), α`

The two inner occurrences of `α` are `bvar`s; their sort is read off
the *binder's declared type* `Sort u`, never off anything substituted
for `α`.  This is argument-blindness in the sort-context. -/

private def uu : Level := .param (.str .anonymous "u")

example :
    sortSpec natOnly []
        (.forallE nm (.sort uu)
          (.forallE nm (.bvar 0) (.bvar 1) bm) bm)
      = some (.imax (.succ uu) (.imax uu uu)) := rfl

/-! ## A `.lam` is not a type

`inferBody` gives a λ a `forallE` type, which `whnf` never turns into
a sort, so the checker's `sortOfE` fails on it too. -/

example : sortSpec natOnly [] (.lam nm (.sort .zero) (.bvar 0) bm)
    = none := rfl

/-! ## β-redexes are skipped, argument-blind

`(fun (α : Sort u) => α) Nat` has the sort of the *body* read in the
extended context — the argument `Nat` is never looked at. -/

example :
    sortSpec natOnly []
        (.app (.lam nm (.sort uu) (.bvar 0) bm)
          (.const Setlec.natName []))
      = some uu := rfl

/-- …and replacing the argument by anything at all keeps the answer. -/
example :
    sortSpec natOnly []
        (.app (.lam nm (.sort uu) (.bvar 0) bm) (.sort .zero))
      = some uu := rfl

/-! ## `let` is value-blind

The kernel infers `b.instantiate1 v`; `sortSpec` pushes the *type*. -/

example :
    sortSpec natOnly []
        (.letE nm (.sort uu) (.const Setlec.natName []) (.bvar 0))
      = some uu := rfl

/-! ## The wall cases (all `none`, all honest)

* a `.proj` node: the field's sort needs the *subject's type
  expression* (its level arguments), which a sort-only walk cannot
  produce;
* a constant the oracle does not answer for. -/

example : sortSpec natOnly [] (.proj nm 0 (.bvar 0)) = none := rfl

example : sortSpec natOnly [] (.const nm []) = none := rfl

/-! ## The ι probe

`Nat.rec`'s declared codomain is the motive application `motive t`,
not a syntactic sort, so `piCod` returns `none` after stripping the
arguments.  Modelled here by a head whose declared type ends in
`motive t` with `motive` a telescope binder. -/

/-- `∀ (motive : Nat → Sort u) (t : Nat), motive t` -/
private def recTy : Expr :=
  .forallE nm (.forallE nm (.const Setlec.natName []) (.sort uu) bm)
    (.forallE nm (.const Setlec.natName [])
      (.app (.bvar 1) (.bvar 0)) bm) bm

/-- Stripping both binders leaves `motive t`, which is not a
universe: `none`.  The *sort of that residual* is available (`u`),
but the sort of the recursor application itself is not. -/
example : piCod recTy 2 = none := rfl

/-- What *is* argument-blind and available: the residual's own sort,
`u`, read off the motive binder's declared type. -/
example :
    sortApp natOnly
        [.const Setlec.natName [],
         .forallE nm (.const Setlec.natName []) (.sort uu) bm]
        (.app (.bvar 1) (.bvar 0)) 0
      = some uu := rfl

/-! ## Vacuity probe for `SortSpec/Subst.lean`

The substitution theorem's premise is *"`v`'s sort profile matches
`A`'s codomain profile"* — `v : A` at the sort level.  It is
satisfiable: `A = Sort 1`, `v = Sort 0` (that is, `Prop : Type`). -/

example (Θ : List Expr) (m : Nat) (w : Level)
    (h : piCod (.sort (.succ .zero)) m = some w) :
    sortApp natOnly Θ (.sort .zero) m = some w := by
  cases m with
  | zero =>
    simp only [piCod_zero, levelOf, Option.some.injEq] at h
    subst h; rfl
  | succ k => exact nomatch h

end Setlec.SetR.SortSpec
