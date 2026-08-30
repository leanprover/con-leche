import Setlec.SetR.Interp2.Claims2C

/-!
# `CtxOk2D` — the context predicate with its fourth leaf conjunct

Generation five's supplier. `CtxOk2`'s leaf package has three
conjuncts — definedness, the slot, the `interp2` link — and **no
truthfulness**, which is why the inference quarter's `.fvar` clause
cannot deliver the returned type's `AnnotOk2` (seal 17). `CtxOk2Ann`
(`Step2/Dispatch.lean`) names the missing conjunct and carries the
evidence that it survives every constructor in the kit.

## Why a conjunction and not an edit

Ruling 2 of seal 18. Editing `CtxOk2` in place would change the
definition that the **tombstone witnesses** construct concretely —
`ctxOk2R_refuted` and `not_openCongLocal` build `CtxOk2` values by
hand — and those are untouchable under this campaign's
refutation-preservation practice. *A tombstone that can be edited to
suit a later definition is not a tombstone.* So `CtxOk2D` is a new
definition with a bridge, and `CtxOk2` keeps its meaning forever.

## The transport recipe — worked below, then repeated ~18 times

Every kit lemma lifts the same way: **split the conjunction, apply the
`CtxOk2` lemma and the `CtxOk2Ann` lemma, reassemble.** Both halves
already exist for every constructor the kit has; nothing new is
proved.

Two things the worked examples exist to teach, both of which caught
the junction writing them:

1. **The `CtxOk2Ann` half often needs the `CtxOk2` half as well.**
   `CtxOk2Ann.fuelMono` takes *both* — it reads definedness out of the
   `CtxOk2` package to know which `tya` the leaf denotes to. So the
   recipe is "apply both halves, **passing both where needed**", not
   "apply each to its own half".
2. **The two halves' argument orders differ**, and differ
   unpredictably. Read each signature. Do not pattern-match on the
   first arrangement that type-checks in the other half.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvS2 V env}
variable {μ : CheckMode} {φ : Name → Nat}

/-- **The context predicate, with truthfulness.**  `CtxOk2` plus the
fourth leaf conjunct, as a conjunction so that `CtxOk2` itself is
untouched. -/
def CtxOk2D (m : EnvS2 V env) (μ : CheckMode) (φ : Name → Nat)
    (F d : Nat) (Δa : List AVExpr) (e : Expr) : Prop :=
  CtxOk2 m μ φ F d Δa e ∧ CtxOk2Ann m μ φ F d Δa e

namespace CtxOk2D

/-- The bridge.  Every generation-four consumer reads through this. -/
theorem toCtxOk2 (h : CtxOk2D m μ φ F d Δa e) :
    CtxOk2 m μ φ F d Δa e := h.1

/-- …and the new half. -/
theorem toAnn (h : CtxOk2D m μ φ F d Δa e) :
    CtxOk2Ann m μ φ F d Δa e := h.2

/-- **Worked example 1 — restriction.**  The pattern in full: split,
apply both halves at the same arguments, reassemble.  Every other kit
lemma below is this proof with two names changed. -/
theorem of_subset {F d : Nat} {Δa : List AVExpr} {e e' : Expr}
    (h : CtxOk2D m μ φ F d Δa e)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    CtxOk2D m μ φ F d Δa e' :=
  ⟨CtxOk2.of_subset h.1 hsub, CtxOk2Ann.of_subset h.2 hsub⟩

/-- **Worked example 2 — fuel monotonicity.**  Same shape, and it shows
the trap: `CtxOk2Ann.fuelMono` takes **three** arguments, the
`CtxOk2` package among them, because it must read definedness out of
it to know which `tya` the leaf denotes to.  Half the list is like
this. -/
theorem fuelMono {F F' d : Nat} {Δa : List AVExpr} {e : Expr}
    (hle : F ≤ F') (h : CtxOk2D m μ φ F d Δa e) :
    CtxOk2D m μ φ F' d Δa e :=
  ⟨CtxOk2.fuelMono hle h.1, CtxOk2Ann.fuelMono hle h.1 h.2⟩

/-! ## The list — the serial batch's first section

Each is `⟨CtxOk2.X …, CtxOk2Ann.X …⟩` where both halves exist, and the
two worked examples above are the template.

**Available on both sides** (lift directly): `fvar_leaf`,
`of_fvarLeaves_nil`, `weakenTop`, `openCong`, `openS`.

**Available on `CtxOk2` only** — these need a `CtxOk2Ann` half first,
each a two-line `fun l hl => …` off `CtxOk2Ann.of_subset` because the
leaf sets are subsets: `length`, `nil`, `of_cover`, `app`, `app_fn`,
`app_arg`, `forallE_ty`, `forallE_body`, `lam_ty`, `lam_body`,
`letE_ty`, `letE_val`, `letE_body`, `proj_arg`, `fvar_ty`, `mono`,
`open`, `openCongC`, `wScoped`.

`wScoped` is the exception worth noting: its conclusion mentions no
context at all, so it is `CtxOk2.wScoped h.1` and needs no second
half.
-/

end CtxOk2D

end Setlec.SetR.Interp2
