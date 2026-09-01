import Setlec.SetR.Interp2.Claims2P

/-!
# The `CtxOkP` kit — restriction family (task #161, P3.4)

The context-discipline lemmas every threading clause of the P-tier
step proof reads: `CtxOk2`'s kit (`Step2/Dispatch.lean`) transposed to
the merged, fuel-free `CtxOkP`.  Going *down* is restriction
(`of_subset` at a `simp [Expr.fvarLeaves]`), spelled out per
`inferBody` branch so a consumer never reopens `fvarLeaves`.  Going
*up* through a binder (`open`/`openS`/`openCong`/`weakenTop`) needs
the `denoteP` depth shift (batch 1's `denoteP_shiftFrom`) and lands
with the P3.4 batch; `wScoped` waits with them (its helper is private
to `Dispatch.lean`).

The fuel-monotonicity pair (`fuelMono`/`mono`) has **no mirror**:
`CtxOkP` has no fuel.  Every quarter that consumed `CtxOk2D.mono`
consumes nothing here — the calls vanish at the swap.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}
variable {m : EnvS2UM V μ env} {φ : Name → Nat}

namespace CtxOkP

/-- Depth. -/
theorem length {d : Nat} {Δa : List AVExpr} {e : Expr}
    (h : CtxOkP m φ d Δa e) : Δa.length = d := h.1

/-- What the `.fvar` clause reads off the discipline: the whole leaf
package at the leaf itself. -/
theorem fvar_leaf {d idx : Nat} {n : Name} {ty : Expr}
    {Δa : List AVExpr}
    (h : CtxOkP m φ d Δa (.fvar idx n ty)) :
    idx < d ∧ Expr.fvarsBelow idx ty ∧
      ∃ tya Aa,
        denoteP m.acval env φ d ty = some tya ∧
        Δa[d - 1 - idx]? = some Aa ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ tya
            = interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ tya) :=
  h.2 (idx, n, ty) (by simp [Expr.fvarLeaves])

/-- No leaves, nothing to say. -/
theorem of_fvarLeaves_nil {d : Nat} {Δa : List AVExpr} {e : Expr}
    (hlen : Δa.length = d) (h : e.fvarLeaves = []) :
    CtxOkP m φ d Δa e := by
  refine ⟨hlen, fun l hl => ?_⟩
  rw [h] at hl
  exact nomatch hl

/-- Depth zero: the declaration-level shape. -/
theorem nil {e : Expr} (h : e.fvarLeaves = []) :
    CtxOkP m φ 0 ([] : List AVExpr) e :=
  of_fvarLeaves_nil rfl h

/-- Covered leaves inherit the package (list form; `of_subset` is the
singleton case). -/
theorem of_cover {d : Nat} {Δa : List AVExpr} {L : List Expr}
    {e : Expr} (hlen : Δa.length = d)
    (hL : ∀ x ∈ L, CtxOkP m φ d Δa x)
    (hsub : ∀ l ∈ e.fvarLeaves, ∃ x ∈ L, l ∈ x.fvarLeaves) :
    CtxOkP m φ d Δa e :=
  ⟨hlen, fun l hl => by
    obtain ⟨x, hx, hlx⟩ := hsub l hl
    exact (hL x hx).2 l hlx⟩

/-- Restriction along one expression — the only shape the threading
clauses need going down. -/
theorem of_subset {d : Nat} {Δa : List AVExpr} {e e' : Expr}
    (hC : CtxOkP m φ d Δa e)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    CtxOkP m φ d Δa e' :=
  ⟨hC.1, fun l hl => hC.2 l (hsub l hl)⟩

/-- An application's leaves are its parts'. -/
theorem app {d : Nat} {Δa : List AVExpr} {f x : Expr}
    (hf : CtxOkP m φ d Δa f) (hx : CtxOkP m φ d Δa x) :
    CtxOkP m φ d Δa (.app f x) := by
  refine ⟨hf.1, fun l hl => ?_⟩
  rw [Expr.fvarLeaves] at hl
  rcases List.mem_append.mp hl with h | h
  · exact hf.2 l h
  · exact hx.2 l h

/-! ### The projections, one per `inferBody` branch that recurses -/

theorem app_fn {d : Nat} {Δa : List AVExpr} {f x : Expr}
    (hC : CtxOkP m φ d Δa (.app f x)) : CtxOkP m φ d Δa f :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem app_arg {d : Nat} {Δa : List AVExpr} {f x : Expr}
    (hC : CtxOkP m φ d Δa (.app f x)) : CtxOkP m φ d Δa x :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem forallE_ty {d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : Setlec.BinderMeta}
    (hC : CtxOkP m φ d Δa (.forallE n ty body mb)) :
    CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem forallE_body {d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : Setlec.BinderMeta}
    (hC : CtxOkP m φ d Δa (.forallE n ty body mb)) :
    CtxOkP m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem lam_ty {d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : Setlec.BinderMeta}
    (hC : CtxOkP m φ d Δa (.lam n ty body mb)) :
    CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem lam_body {d : Nat} {Δa : List AVExpr} {n : Name}
    {ty body : Expr} {mb : Setlec.BinderMeta}
    (hC : CtxOkP m φ d Δa (.lam n ty body mb)) :
    CtxOkP m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem letE_ty {d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (hC : CtxOkP m φ d Δa (.letE n ty val body)) :
    CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]
    exact List.mem_append_left _ (List.mem_append_left _ hl)

theorem letE_val {d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (hC : CtxOkP m φ d Δa (.letE n ty val body)) :
    CtxOkP m φ d Δa val :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]
    exact List.mem_append_left _ (List.mem_append_right _ hl)

theorem letE_body {d : Nat} {Δa : List AVExpr} {n : Name}
    {ty val body : Expr}
    (hC : CtxOkP m φ d Δa (.letE n ty val body)) :
    CtxOkP m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem proj_arg {d : Nat} {Δa : List AVExpr} {sn : Name}
    {i : Nat} {e : Expr}
    (hC : CtxOkP m φ d Δa (.proj sn i e)) :
    CtxOkP m φ d Δa e :=
  hC.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact hl

/-- A leaf's annotation is itself covered. -/
theorem fvar_ty {d idx : Nat} {Δa : List AVExpr} {n : Name}
    {ty : Expr} (hC : CtxOkP m φ d Δa (.fvar idx n ty)) :
    CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hl

end CtxOkP

end Setlec.SetR.Interp2
