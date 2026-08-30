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

### What the batch actually found

Three entries of the second list are **not** `of_subset` in disguise
and cost a premise the `CtxOk2` lemma does not take:

* `open`, `openS` and `openCongC` each gain the domain's **hoisted
  grading** `hok : ∀ ρ, Sat2 V Δa ρ → AnnotOk2 V ρ ta`, because
  `CtxOk2Ann.openCong` reads it to grade the *new* leaf — the opened
  variable's annotation is the domain, and the fourth conjunct has to
  say something about it.  This is not a defect: at every site that
  opens a binder the grading is one of `Claims2D`'s own hoisted
  premises, which is exactly the self-propagation argument of seal 17
  applied to the kit rather than to the claim.
* `openCongC` therefore takes `hok₂` where the `CtxOk2` version takes
  nothing, and `openCong` (generation three) already took it — so the
  generation-four shape is the one that *gains* an argument here, the
  only place in the lift where the newer shape is the more expensive
  one.
-/

/-- **Depth.**  Read off the `CtxOk2` half; the fourth conjunct says
nothing about the context's length. -/
theorem length {F d : Nat} {Δa : List AVExpr} {e : Expr}
    (h : CtxOk2D m μ φ F d Δa e) : Δa.length = d := h.1.1

/-- **Scoping**, the one entry with no second half: its conclusion
mentions no context at all. -/
theorem wScoped {F d : Nat} {Δa : List AVExpr} {e : Expr}
    (h : CtxOk2D m μ φ F d Δa e) : Expr.WScoped d e :=
  CtxOk2.wScoped h.1

/-- `fuelMono` under the name the quarters were promised. -/
theorem mono {F F' d : Nat} {Δa : List AVExpr} {e : Expr}
    (hle : F ≤ F') (h : CtxOk2D m μ φ F d Δa e) :
    CtxOk2D m μ φ F' d Δa e :=
  CtxOk2D.fuelMono hle h

/-- No leaves, nothing to say — on either half. -/
theorem of_fvarLeaves_nil {F d : Nat} {Δa : List AVExpr} {e : Expr}
    (hlen : Δa.length = d) (h : e.fvarLeaves = []) :
    CtxOk2D m μ φ F d Δa e :=
  ⟨CtxOk2.of_fvarLeaves_nil hlen h,
    CtxOk2Ann.of_fvarLeaves_nil h⟩

/-- Depth zero: the declaration-level shape. -/
theorem nil {F : Nat} {e : Expr} (h : e.fvarLeaves = []) :
    CtxOk2D m μ φ F 0 [] e :=
  ⟨CtxOk2.nil h, CtxOk2Ann.of_fvarLeaves_nil h⟩

/-- **The leaf package, both halves at once.**  The three conjuncts
`CtxOk2` supplies plus the fourth — and the fourth is applied at the
*same* `tya` the first delivers, which is the whole point of
`CtxOk2Ann` quantifying over `tya` rather than carrying its own
existential. -/
theorem fvar_leaf {F d idx : Nat} {Δa : List AVExpr} {n : Name}
    {ty : Expr} (h : CtxOk2D m μ φ F d Δa (.fvar idx n ty)) :
    ∃ tya Aa,
      denote2 μ m.acval env φ F d ty = some tya ∧
      Δa[d - 1 - idx]? = some Aa ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ tya
          = interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ tya := by
  obtain ⟨tya, Aa, hden, hi, hlink⟩ := CtxOk2.fvar_leaf h.1
  exact ⟨tya, Aa, hden, hi, hlink,
    CtxOk2Ann.fvar_leaf h.2 tya hden⟩

/-- Covered leaves inherit both halves. -/
theorem of_cover {F d : Nat} {Δa : List AVExpr} {L : List Expr}
    {e : Expr} (hlen : Δa.length = d)
    (hL : ∀ x ∈ L, CtxOk2D m μ φ F d Δa x)
    (hsub : ∀ l ∈ e.fvarLeaves, ∃ x ∈ L, l ∈ x.fvarLeaves) :
    CtxOk2D m μ φ F d Δa e :=
  ⟨CtxOk2.of_cover hlen (fun x hx => (hL x hx).1) hsub,
    fun l hl => by
      obtain ⟨x, hx, hlx⟩ := hsub l hl
      exact (hL x hx).2 l hlx⟩

/-- An application's leaves are its parts'. -/
theorem app {F d : Nat} {Δa : List AVExpr} {f x : Expr}
    (hf : CtxOk2D m μ φ F d Δa f) (hx : CtxOk2D m μ φ F d Δa x) :
    CtxOk2D m μ φ F d Δa (.app f x) :=
  ⟨CtxOk2.app hf.1 hx.1, fun l hl => by
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_append.mp hl with h | h
    · exact hf.2 l h
    · exact hx.2 l h⟩

/-! ### The projections, one per recursing `inferBody` branch

Every one of these is `of_subset` at the same `fvarLeaves` witness the
`CtxOk2` original uses, so the lift is *free*: `CtxOk2D.of_subset`
already carries both halves.  Spelled out so a consumer never has to
reopen `fvarLeaves`. -/

theorem app_fn {F d : Nat} {Δa : List AVExpr} {f x : Expr}
    (h : CtxOk2D m μ φ F d Δa (.app f x)) : CtxOk2D m μ φ F d Δa f :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem app_arg {F d : Nat} {Δa : List AVExpr} {f x : Expr}
    (h : CtxOk2D m μ φ F d Δa (.app f x)) : CtxOk2D m μ φ F d Δa x :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem forallE_ty {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : Setlec.BinderMeta}
    (h : CtxOk2D m μ φ F d Δa (.forallE n ty body mb)) :
    CtxOk2D m μ φ F d Δa ty :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem forallE_body {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : Setlec.BinderMeta}
    (h : CtxOk2D m μ φ F d Δa (.forallE n ty body mb)) :
    CtxOk2D m μ φ F d Δa body :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem lam_ty {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : Setlec.BinderMeta}
    (h : CtxOk2D m μ φ F d Δa (.lam n ty body mb)) :
    CtxOk2D m μ φ F d Δa ty :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem lam_body {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : Setlec.BinderMeta}
    (h : CtxOk2D m μ φ F d Δa (.lam n ty body mb)) :
    CtxOk2D m μ φ F d Δa body :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem letE_ty {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (h : CtxOk2D m μ φ F d Δa (.letE n ty val body)) :
    CtxOk2D m μ φ F d Δa ty :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]
    exact List.mem_append_left _ (List.mem_append_left _ hl)

theorem letE_val {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (h : CtxOk2D m μ φ F d Δa (.letE n ty val body)) :
    CtxOk2D m μ φ F d Δa val :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]
    exact List.mem_append_left _ (List.mem_append_right _ hl)

theorem letE_body {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (h : CtxOk2D m μ φ F d Δa (.letE n ty val body)) :
    CtxOk2D m μ φ F d Δa body :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem proj_arg {F d : Nat} {Δa : List AVExpr} {sn : Name}
    {i : Nat} {e : Expr}
    (h : CtxOk2D m μ φ F d Δa (.proj sn i e)) :
    CtxOk2D m μ φ F d Δa e :=
  h.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact hl

/-- A leaf's annotation is itself covered. -/
theorem fvar_ty {F d idx : Nat} {Δa : List AVExpr} {n : Name}
    {ty : Expr} (h : CtxOk2D m μ φ F d Δa (.fvar idx n ty)) :
    CtxOk2D m μ φ F d Δa ty :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hl

/-- **Weakening by one binder.**  Trap 2 in the flesh:
`CtxOk2.weakenTop` takes `henv`, `hacl`, the scoping and *then* the
package; `CtxOk2Ann.weakenTop` takes the package, the annotation half
and the scoping *last*.  The scoping is free on both — it is
`CtxOk2.wScoped` of the half we already hold. -/
theorem weakenTop {F d : Nat} {Δa : List AVExpr} {Ba : AVExpr}
    {e : Expr} (h : CtxOk2D m μ φ F d Δa e) :
    CtxOk2D m μ φ F (d + 1) (Ba :: Δa) e :=
  ⟨CtxOk2.weakenTop m.base.wf m.acval_closed h.1.wScoped h.1,
    CtxOk2Ann.weakenTop h.1 h.2 h.1.wScoped⟩

/-- **Opening a binder congruence**, generation-three shape. -/
theorem openCong {F d : Nat} {Δa : List AVExpr} {body ty : Expr}
    {n : Name} {ta₁ ta₂ : AVExpr}
    (hb : CtxOk2D m μ φ F d Δa body)
    (ht : CtxOk2D m μ φ F d Δa ty)
    (hty : denote2 μ m.acval env φ F d ty = some ta₂)
    (hok₁ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta₁)
    (hok₂ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta₂)
    (hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta₁ →
      AnnotOk2 V ρ ta₂ → interp2 V ρ ta₁ = interp2 V ρ ta₂) :
    CtxOk2D m μ φ F (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
  ⟨CtxOk2.openCong hb.1 ht.1 hty hok₁ hok₂ hdom,
    CtxOk2Ann.openCong hb.1 ht.1 hb.2 ht.2 hty hok₂⟩

/-- **Opening a binder congruence, generation-four shape** — `hdom` is
`DefEqClaims2D`'s conclusion partially applied, and this is the shape
the five `∀`/`λ` congruence sites hold.  `hok₂` is the one argument
the `CtxOk2` version does not take: the fourth conjunct has to grade
the *opened variable's* annotation, which is the domain. -/
theorem openCongC {F d : Nat} {Δa : List AVExpr} {body ty : Expr}
    {n : Name} {ta₁ ta₂ : AVExpr}
    (hb : CtxOk2D m μ φ F d Δa body)
    (ht : CtxOk2D m μ φ F d Δa ty)
    (hty : denote2 μ m.acval env φ F d ty = some ta₂)
    (hok₂ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta₂)
    (hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ ta₁ = interp2 V ρ ta₂) :
    CtxOk2D m μ φ F (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
  ⟨CtxOk2.openCongC hb.1 ht.1 hty hdom,
    CtxOk2Ann.openCong hb.1 ht.1 hb.2 ht.2 hty hok₂⟩

/-- **`CtxOk2Open`'s body in the new currency.**  Argument order is
`CtxOk2.openS`'s (type first); the `fvarsBelow` argument is dropped
because `CtxOk2D.wScoped` supplies it. -/
theorem openS {F d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {ta : AVExpr}
    (ht : CtxOk2D m μ φ F d Δa ty) (hb : CtxOk2D m μ φ F d Δa body)
    (hty : denote2 μ m.acval env φ F d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) :
    CtxOk2D m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
  ⟨CtxOk2.openS ht.1 hb.1 hty ht.1.wScoped.fvarsBelow,
    CtxOk2Ann.openS hb.1 ht.1 hb.2 ht.2 hty hok⟩

end CtxOk2D

/-- **`CtxOk2.open`'s transpose**, kept under its sealed name.  Stated
outside the namespace because `open` is not a namespace-relative
identifier; `CtxOk2.open` is declared the same way. -/
theorem CtxOk2D.open {F d : Nat} {Δa : List AVExpr}
    {body ty : Expr} {n : Name} {ta : AVExpr}
    (hb : CtxOk2D m μ φ F d Δa body) (ht : CtxOk2D m μ φ F d Δa ty)
    (hty : denote2 μ m.acval env φ F d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) :
    CtxOk2D m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty)) :=
  CtxOk2D.openS ht hb hty hok

end Setlec.SetR.Interp2
