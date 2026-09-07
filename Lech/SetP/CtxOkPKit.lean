import Lech.SetP.OkPTransport
import Lech.SetP.Annot.BitShift

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

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}
variable {m : EnvS2Core V env} {φ : Name → Nat}

namespace CtxOkP

/-- Depth. -/
theorem length {d : Nat} {Δa : List AVExpr} {e : Expr}
    (h : CtxOkP m φ d Δa e) : Δa.length = d := h.1

/-- What the `.fvar` clause reads off the discipline: the whole leaf
package at the leaf itself. -/
theorem fvar_leaf {d idx : Nat} {ty : Expr}
    {Δa : List AVExpr}
    (h : CtxOkP m φ d Δa (.fvar idx ty)) :
    idx < d ∧ Expr.fvarsBelow idx ty ∧
      ∃ tya Aa,
        denoteP m.acval env φ d ty = some tya ∧
        Δa[d - 1 - idx]? = some Aa ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ tya
            = interp2 V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ tya) :=
  h.2 (idx, ty) (by simp [Expr.fvarLeaves])

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

theorem forallE_ty {d : Nat} {Δa : List AVExpr}
    {ty body : Expr} {mb : Lech.BinderMeta}
    (hC : CtxOkP m φ d Δa (.forallE ty body mb)) :
    CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem forallE_body {d : Nat} {Δa : List AVExpr}
    {ty body : Expr} {mb : Lech.BinderMeta}
    (hC : CtxOkP m φ d Δa (.forallE ty body mb)) :
    CtxOkP m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem lam_ty {d : Nat} {Δa : List AVExpr}
    {ty body : Expr} {mb : Lech.BinderMeta}
    (hC : CtxOkP m φ d Δa (.lam ty body mb)) :
    CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem lam_body {d : Nat} {Δa : List AVExpr}
    {ty body : Expr} {mb : Lech.BinderMeta}
    (hC : CtxOkP m φ d Δa (.lam ty body mb)) :
    CtxOkP m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem letE_ty {d : Nat} {Δa : List AVExpr}
    {ty val body : Expr}
    (hC : CtxOkP m φ d Δa (.letE ty val body)) :
    CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]
    exact List.mem_append_left _ (List.mem_append_left _ hl)

theorem letE_val {d : Nat} {Δa : List AVExpr}
    {ty val body : Expr}
    (hC : CtxOkP m φ d Δa (.letE ty val body)) :
    CtxOkP m φ d Δa val :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]
    exact List.mem_append_left _ (List.mem_append_right _ hl)

theorem letE_body {d : Nat} {Δa : List AVExpr}
    {ty val body : Expr}
    (hC : CtxOkP m φ d Δa (.letE ty val body)) :
    CtxOkP m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem proj_arg {d : Nat} {Δa : List AVExpr} {sn : Name}
    {i : Nat} {e : Expr}
    (hC : CtxOkP m φ d Δa (.proj sn i e)) :
    CtxOkP m φ d Δa e :=
  hC.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact hl

/-- A leaf's annotation is itself covered. -/
theorem fvar_ty {d idx : Nat} {Δa : List AVExpr}
    {ty : Expr} (hC : CtxOkP m φ d Δa (.fvar idx ty)) :
    CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hl

end CtxOkP

/-! ## The open family (task #161, P3 batch 2)

`CtxOk2`'s upward kit (`Step2/Dispatch.lean`) and its `CtxOk2D`
composites, transposed to `CtxOkP`.  Three things change, all of them
simplifications:

1. **No fuel.**  `CtxOk2D.fuelMono`/`mono` have no mirror at all.
2. **`EnvWF` is dropped** from `weakenTop` and everything above it.
   `CtxOk2.weakenTop` takes `henv : Lech.EnvWF env` for exactly one
   reason: `denote2_weaken_top` needs it, and `denote2_weaken_top`
   needs it only to move the two *sort runs* (`sortOfE`/`lamSortE`)
   across the shift.  `denoteP_weaken_top` (batch 1) has no runs and
   takes no `EnvWF`, so the premise has no occurrence left here.  The
   *leaf* premise `hacl` is not dropped — it is read out of the
   structure as `m.acval_closed`, as the `CtxOk2D` tier already does.
3. **The fourth conjunct rides `AnnotOkP.hoist_lift`** where the
   `CtxOk2Ann` half rides `AnnotOk2.hoist_lift`.  That is the whole
   delta of the merged predicate: `CtxOkP` carries at `AnnotOkP` what
   `CtxOk2D` carries at `AnnotOk2`, so every hoisted grading premise
   `hok` below is stated at `AnnotOkP`.

The `hdom` premise of `openCong`/`openCongC` is kept **verbatim** from
the `CtxOk2` originals: the currency is `interp2`, and it is
`DefEqClaims2P`'s conclusion partially applied.
-/

/-- Leafwise index bounds give the direct bound.  A private local copy
of `Dispatch.lean`'s helper of the same name, which is `private` there
and so not in scope here. -/
private theorem fvarsBelow_of_leavesP : ∀ (e : Expr) {d : Nat},
    (∀ l ∈ e.fvarLeaves, l.1 < d) → Expr.fvarsBelow d e := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d h
    exact h (idx, ty) (by simp [Lech.Expr.fvarLeaves])
  | app f a ihf iha =>
    intro d h
    exact ⟨ihf (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      iha (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | lam ty b _ iht ihb =>
    intro d h
    exact ⟨iht (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      ihb (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | forallE ty b _ iht ihb =>
    intro d h
    exact ⟨iht (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      ihb (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | letE t v b iht ihv ihb =>
    intro d h
    exact ⟨iht (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      ihv (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      ihb (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | proj _ _ e ih =>
    intro d h
    exact ih (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))
  | _ => intro d _; trivial

/-- Leafwise annotation bounds upgrade a direct bound to `WScoped`.
The `fvar` case is the whole content: the *leaf's own*
`fvarsBelow idx ty` is what lets the recursion drop from `d` to `idx`.
Private local copy of `Dispatch.lean`'s `wScoped_of_leaves`. -/
private theorem wScoped_of_leavesP : ∀ (e : Expr) {d : Nat},
    Expr.fvarsBelow d e →
    (∀ l ∈ e.fvarLeaves, Expr.fvarsBelow l.1 l.2) →
    Expr.WScoped d e := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d hfb h
    rw [Lech.Expr.WScoped]
    refine ⟨hfb, ih (h (idx, ty) (by simp [Lech.Expr.fvarLeaves]))
      (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | app f a ihf iha =>
    intro d hfb h
    rw [Lech.Expr.WScoped]
    exact ⟨ihf hfb.1
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      iha hfb.2
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | lam ty b _ iht ihb =>
    intro d hfb h
    rw [Lech.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      ihb hfb.2
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | forallE ty b _ iht ihb =>
    intro d hfb h
    rw [Lech.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      ihb hfb.2
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | letE t v b iht ihv ihb =>
    intro d hfb h
    rw [Lech.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      ihv hfb.2.1
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl])),
      ihb hfb.2.2
        (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))⟩
  | proj _ _ e ih =>
    intro d hfb h
    rw [Lech.Expr.WScoped]
    exact ih hfb
      (fun l hl => h l (by simp [Lech.Expr.fvarLeaves, hl]))
  | _ => intro d _ _; rw [Lech.Expr.WScoped]; trivial

namespace CtxOkP

/-- **`CtxOkP` implies well-scopedness.**  `CtxOk2.wScoped`'s mirror,
and what makes every opening lemma below take no scoping premise. -/
theorem wScoped {d : Nat} {Δa : List AVExpr} {e : Expr}
    (hC : CtxOkP m φ d Δa e) : Expr.WScoped d e :=
  wScoped_of_leavesP e
    (fvarsBelow_of_leavesP e (fun l hl => (hC.2 l hl).1))
    (fun l hl => (hC.2 l hl).2.1)

/-- **Weakening the context correspondence by one binder.**  Every
leaf of an already-scoped subject survives one more binder: its
annotation lifts (`denoteP_weaken_top`), its slot moves up by the new
head, `Sat2_tail` carries the link, and `AnnotOkP.hoist_lift` carries
the grading.

`henv` is **dropped** (see the section note): `denoteP_weaken_top`'s
only leaf premise is `hacl`, read here out of `m.acval_closed`.  The
`WScoped` premise `CtxOk2.weakenTop` takes is dropped too — `wScoped`
above supplies it from the package itself, as `CtxOk2D.weakenTop`
already does. -/
theorem weakenTop {d : Nat} {Δa : List AVExpr} {Ba : AVExpr} {e : Expr}
    (hC : CtxOkP m φ d Δa e) : CtxOkP m φ (d + 1) (Ba :: Δa) e := by
  have hw : Expr.WScoped d e := hC.wScoped
  refine ⟨by simp [hC.1], fun l hl => ?_⟩
  obtain ⟨hlt, hfb, tya, Aa, hden, hi, hlink, hok⟩ := hC.2 l hl
  have hwl : Expr.WScoped d l.2 :=
    (Lech.Expr.WScoped_leaves e hw l hl).2.mono (by omega)
  refine ⟨by omega, hfb, tya.liftN 1 0, Aa, ?_, ?_, ?_, ?_⟩
  · rw [denoteP_weaken_top m.acval_closed hwl, hden]
    rfl
  · rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
    simpa using hi
  · intro ρ hρ
    rw [show d + 1 - 1 - l.1 = d - 1 - l.1 + 1 from by omega,
      show AVExpr.liftN 1 tya 0 = tya.lift from rfl,
      interp2_lift (V := V) tya ρ, hlink _ (Sat2_tail hρ)]
    congr 1
  · exact AnnotOkP.hoist_lift (X := Ba) hok

/-- **Opening a binder congruence, annotated, in the P currency.**
`CtxOk2.openCongC` plus `CtxOk2Ann.openCong`'s fourth conjunct,
merged.  `hdom` is verbatim the `CtxOk2` original's — it is
`DefEqClaims2P`'s conclusion partially applied — and `hok₂` is the
*opened variable's* grading, at `AnnotOkP` because that is what
`CtxOkP`'s leaf package carries. -/
theorem openCongC {d : Nat} {Δa : List AVExpr} {body ty : Expr}
    {ta₁ ta₂ : AVExpr}
    (hb : CtxOkP m φ d Δa body) (ht : CtxOkP m φ d Δa ty)
    (hty : denoteP m.acval env φ d ty = some ta₂)
    (hok₂ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta₂)
    (hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ ta₁ = interp2 V ρ ta₂) :
    CtxOkP m φ (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d ty)) := by
  have hwt : Expr.WScoped d ty := ht.wScoped
  refine ⟨by simp [hb.1], fun l hl => ?_⟩
  rcases Lech.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact (weakenTop (Ba := ta₁) hb).2 l hl'
  · rw [Lech.Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨by omega, hwt.fvarsBelow, ta₂.liftN 1 0, ta₁, ?_, ?_, ?_,
        ?_⟩
      · rw [denoteP_weaken_top m.acval_closed hwt, hty]
        rfl
      · rw [show d + 1 - 1 - d = 0 from by omega]
        rfl
      · intro ρ hρ
        have hρ' : Sat2 V Δa (fun j => ρ (j + 1)) := Sat2_tail hρ
        show interp2 V ρ (AVExpr.liftN 1 ta₂ 0)
          = interp2 V (fun j => ρ (j + (d + 1 - 1 - d) + 1)) ta₁
        rw [show d + 1 - 1 - d = 0 from by omega,
          show AVExpr.liftN 1 ta₂ 0 = ta₂.lift from rfl,
          interp2_lift (V := V) ta₂ ρ]
        exact (hdom _ hρ').symm
      · exact AnnotOkP.hoist_lift (X := ta₁) hok₂
    · exact (weakenTop (Ba := ta₁) ht).2 l hl''

/-- **Opening a binder congruence**, the generation-three shape: the
two ρ-local gradings hoisted out of `hdom`.  Kept because the sealed
`CtxOk2.openCong`/`CtxOk2D.openCong` signatures are cited; `hdom` is
verbatim theirs with `AnnotOk2` raised to `AnnotOkP`. -/
theorem openCong {d : Nat} {Δa : List AVExpr} {body ty : Expr}
    {ta₁ ta₂ : AVExpr}
    (hb : CtxOkP m φ d Δa body) (ht : CtxOkP m φ d Δa ty)
    (hty : denoteP m.acval env φ d ty = some ta₂)
    (hok₁ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta₁)
    (hok₂ : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta₂)
    (hdom : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta₁ →
      AnnotOkP V ρ ta₂ → interp2 V ρ ta₁ = interp2 V ρ ta₂) :
    CtxOkP m φ (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
  openCongC hb ht hty hok₂ fun ρ hρ => hdom ρ hρ (hok₁ ρ hρ) (hok₂ ρ hρ)

/-- **`CtxOk2Open`'s body in the P currency.**  Argument order is
`CtxOk2.openS`'s (type first); the `fvarsBelow` argument the sealed
signature carries is dropped because `wScoped` supplies it. -/
theorem openS {d : Nat} {Δa : List AVExpr}
    {ty body : Expr} {ta : AVExpr}
    (ht : CtxOkP m φ d Δa ty) (hb : CtxOkP m φ d Δa body)
    (hty : denoteP m.acval env φ d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) :
    CtxOkP m φ (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
  openCongC hb ht hty hok fun _ _ => rfl

end CtxOkP

/-- **Opening a binder extends the context correspondence** — the
lemma the `.forallE`/`.lam`/`.letE` clauses of every quarter need to
reach their recursive call.  Stated outside the namespace because
`open` is not a namespace-relative identifier; `CtxOk2.open` and
`CtxOk2D.open` are declared the same way. -/
theorem CtxOkP.open {d : Nat} {Δa : List AVExpr} {body ty : Expr}
    {ta : AVExpr}
    (hb : CtxOkP m φ d Δa body) (ht : CtxOkP m φ d Δa ty)
    (hty : denoteP m.acval env φ d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) :
    CtxOkP m φ (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
  CtxOkP.openS ht hb hty hok

end Lech.SetP
