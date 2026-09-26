module

import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Denote.OpenRevDenote
public import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Annot.BitShift
public section

/-!
# The `CtxOk` kit — restriction family (task #161, P3.4)

The context-discipline lemmas every threading clause of the P-tier
step proof reads, for the fuel-free `CtxOk`.  Going *down* is restriction
(`of_subset` at a `simp [Expr.fvarLeaves]`), spelled out per
`inferBody` branch so a consumer never reopens `fvarLeaves`.  Going
*up* through a binder (`open`/`openS`/`openCongC`/`weakenTop`) needs
the `denoteMeta` depth shift (`denoteMeta_shiftFrom`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}
variable {m : EnvModel V env} {φ : Name → Nat}

namespace CtxOk

/-- Depth. -/
theorem length {d : Nat} {Δa : List AnnotTerm} {e : Expr}
    (h : CtxOk m φ d Δa e) : Δa.length = d := h.1

/-- What the `.fvar` clause reads off the discipline: the whole leaf
package at the leaf itself. -/
theorem fvar_leaf {d idx : Nat} {ty : Expr}
    {Δa : List AnnotTerm}
    (h : CtxOk m φ d Δa (.fvar idx ty)) :
    idx < d ∧ Expr.fvarsBelow idx ty ∧
      ∃ tya Aa,
        denoteMeta m.acval env φ d ty = some tya ∧
        Δa[d - 1 - idx]? = some Aa ∧
        (∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ tya
            = interp V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ tya) :=
  h.2 (idx, ty) (by simp [Expr.fvarLeaves])

/-- No leaves, nothing to say. -/
theorem of_fvarLeaves_nil {d : Nat} {Δa : List AnnotTerm} {e : Expr}
    (hlen : Δa.length = d) (h : e.fvarLeaves = []) :
    CtxOk m φ d Δa e := by
  refine ⟨hlen, fun l hl => ?_⟩
  rw [h] at hl
  exact nomatch hl

/-- Depth zero: the declaration-level shape. -/
theorem nil {e : Expr} (h : e.fvarLeaves = []) :
    CtxOk m φ 0 ([] : List AnnotTerm) e :=
  of_fvarLeaves_nil rfl h

/-- Restriction along one expression — the only shape the threading
clauses need going down. -/
theorem of_subset {d : Nat} {Δa : List AnnotTerm} {e e' : Expr}
    (hC : CtxOk m φ d Δa e)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    CtxOk m φ d Δa e' :=
  ⟨hC.1, fun l hl => hC.2 l (hsub l hl)⟩

/-- An application's leaves are its parts'. -/
theorem app {d : Nat} {Δa : List AnnotTerm} {f x : Expr}
    (hf : CtxOk m φ d Δa f) (hx : CtxOk m φ d Δa x) :
    CtxOk m φ d Δa (.app f x) := by
  refine ⟨hf.1, fun l hl => ?_⟩
  rw [Expr.fvarLeaves] at hl
  rcases List.mem_append.mp hl with h | h
  · exact hf.2 l h
  · exact hx.2 l h

/-! ### The projections, one per `inferBody` branch that recurses -/

theorem app_fn {d : Nat} {Δa : List AnnotTerm} {f x : Expr}
    (hC : CtxOk m φ d Δa (.app f x)) : CtxOk m φ d Δa f :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem app_arg {d : Nat} {Δa : List AnnotTerm} {f x : Expr}
    (hC : CtxOk m φ d Δa (.app f x)) : CtxOk m φ d Δa x :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem forallE_ty {d : Nat} {Δa : List AnnotTerm}
    {ty body : Expr} {mb : ConLeche.BinderMeta}
    (hC : CtxOk m φ d Δa (.forallE ty body mb)) :
    CtxOk m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem forallE_body {d : Nat} {Δa : List AnnotTerm}
    {ty body : Expr} {mb : ConLeche.BinderMeta}
    (hC : CtxOk m φ d Δa (.forallE ty body mb)) :
    CtxOk m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem lam_ty {d : Nat} {Δa : List AnnotTerm}
    {ty body : Expr} {mb : ConLeche.BinderMeta}
    (hC : CtxOk m φ d Δa (.lam ty body mb)) :
    CtxOk m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem lam_body {d : Nat} {Δa : List AnnotTerm}
    {ty body : Expr} {mb : ConLeche.BinderMeta}
    (hC : CtxOk m φ d Δa (.lam ty body mb)) :
    CtxOk m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem proj_arg {d : Nat} {Δa : List AnnotTerm} {sn : Name}
    {i : Nat} {e : Expr}
    (hC : CtxOk m φ d Δa (.proj sn i e)) :
    CtxOk m φ d Δa e :=
  hC.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact hl

end CtxOk

/-! ## The open family (task #161, P3 batch 2)

`CtxOk`'s upward kit:

1. **No fuel.**
2. **No `EnvWF`** in `weakenTop` and everything above it:
   `denoteMeta_weaken_top` has no sort runs and takes no `EnvWF`.  The
   *leaf* premise `hacl` is read out of the structure as
   `m.acval_closed`.
3. **The fourth conjunct rides `WellDenotedV.hoist_lift`**, so every
   hoisted grading premise `hok` below is stated at `WellDenotedV`.

The `hdom` premise of `openCongC`: the currency is `interp`, and it is
`DefEqClaim`'s conclusion partially applied.
-/

/-- Leafwise annotation bounds upgrade a direct bound to `WScoped`.
The `fvar` case is the whole content: the *leaf's own*
`fvarsBelow idx ty` is what lets the recursion drop from `d` to `idx`. -/
private theorem wScoped_of_leaves : ∀ (e : Expr) {d : Nat},
    Expr.fvarsBelow d e →
    (∀ l ∈ e.fvarLeaves, Expr.fvarsBelow l.1 l.2) →
    Expr.WScoped d e := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d hfb h
    rw [ConLeche.Expr.WScoped]
    refine ⟨hfb, ih (h (idx, ty) (by simp [ConLeche.Expr.fvarLeaves]))
      (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl]))⟩
  | app f a ihf iha =>
    intro d hfb h
    rw [ConLeche.Expr.WScoped]
    exact ⟨ihf hfb.1
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl])),
      iha hfb.2
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl]))⟩
  | lam ty b _ iht ihb =>
    intro d hfb h
    rw [ConLeche.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl])),
      ihb hfb.2
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl]))⟩
  | forallE ty b _ iht ihb =>
    intro d hfb h
    rw [ConLeche.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl])),
      ihb hfb.2
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl]))⟩
  | letE t v b iht ihv ihb =>
    intro d hfb h
    rw [ConLeche.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl])),
      ihv hfb.2.1
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl])),
      ihb hfb.2.2
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl]))⟩
  | proj _ _ e ih =>
    intro d hfb h
    rw [ConLeche.Expr.WScoped]
    exact ih hfb
      (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl]))
  | _ => intro d _ _; rw [ConLeche.Expr.WScoped]; trivial

namespace CtxOk

/-- **`CtxOk` implies well-scopedness**, which makes every opening lemma below take no scoping premise. -/
theorem wScoped {d : Nat} {Δa : List AnnotTerm} {e : Expr}
    (hC : CtxOk m φ d Δa e) : Expr.WScoped d e :=
  wScoped_of_leaves e
    (Verify.Expr.fvarsBelow_of_fvarLeaves (e := e) (fun l hl => (hC.2 l hl).1))
    (fun l hl => (hC.2 l hl).2.1)

/-- **Weakening the context correspondence by one binder.**  Every
leaf of an already-scoped subject survives one more binder: its
annotation lifts (`denoteMeta_weaken_top`), its slot moves up by the new
head, `Sat_tail` carries the link, and `WellDenotedV.hoist_lift` carries
the grading.

`henv` is **dropped** (see the section note): `denoteMeta_weaken_top`'s
only leaf premise is `hacl`, read here out of `m.acval_closed`.  No
`WScoped` premise either — `wScoped` above supplies it from the
package itself. -/
theorem weakenTop {d : Nat} {Δa : List AnnotTerm} {Ba : AnnotTerm} {e : Expr}
    (hC : CtxOk m φ d Δa e) : CtxOk m φ (d + 1) (Ba :: Δa) e := by
  have hw : Expr.WScoped d e := hC.wScoped
  refine ⟨by simp [hC.1], fun l hl => ?_⟩
  obtain ⟨hlt, hfb, tya, Aa, hden, hi, hlink, hok⟩ := hC.2 l hl
  have hwl : Expr.WScoped d l.2 :=
    (ConLeche.Expr.WScoped_leaves e hw l hl).2.mono (by omega)
  refine ⟨by omega, hfb, tya.liftN 1 0, Aa, ?_, ?_, ?_, ?_⟩
  · rw [denoteMeta_weaken_top m.acval_closed hwl, hden]
    rfl
  · rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
    simpa using hi
  · intro ρ hρ
    rw [show d + 1 - 1 - l.1 = d - 1 - l.1 + 1 from by omega,
      show AnnotTerm.liftN 1 tya 0 = tya.lift from rfl,
      interp_lift (V := V) tya ρ, hlink _ (Sat_tail hρ)]
    congr 1
  · exact WellDenotedV.hoist_lift (X := Ba) hok

/-- **Opening a binder congruence, annotated, in the P currency.**
`hdom` is `DefEqClaim`'s conclusion partially applied, and `hok₂` is the
*opened variable's* grading, at `WellDenotedV` because that is what
`CtxOk`'s leaf package carries. -/
theorem openCongC {d : Nat} {Δa : List AnnotTerm} {body ty : Expr}
    {ta₁ ta₂ : AnnotTerm}
    (hb : CtxOk m φ d Δa body) (ht : CtxOk m φ d Δa ty)
    (hty : denoteMeta m.acval env φ d ty = some ta₂)
    (hok₂ : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta₂)
    (hdom : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ ta₁ = interp V ρ ta₂) :
    CtxOk m φ (d + 1) (ta₁ :: Δa)
      (body.instantiate1 (.fvar d ty)) := by
  have hwt : Expr.WScoped d ty := ht.wScoped
  refine ⟨by simp [hb.1], fun l hl => ?_⟩
  rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact (weakenTop (Ba := ta₁) hb).2 l hl'
  · rw [ConLeche.Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨by omega, hwt.fvarsBelow, ta₂.liftN 1 0, ta₁, ?_, ?_, ?_,
        ?_⟩
      · rw [denoteMeta_weaken_top m.acval_closed hwt, hty]
        rfl
      · rw [show d + 1 - 1 - d = 0 from by omega]
        rfl
      · intro ρ hρ
        have hρ' : Sat V Δa (fun j => ρ (j + 1)) := Sat_tail hρ
        show interp V ρ (AnnotTerm.liftN 1 ta₂ 0)
          = interp V (fun j => ρ (j + (d + 1 - 1 - d) + 1)) ta₁
        rw [show d + 1 - 1 - d = 0 from by omega,
          show AnnotTerm.liftN 1 ta₂ 0 = ta₂.lift from rfl,
          interp_lift (V := V) ta₂ ρ]
        exact (hdom _ hρ').symm
      · exact WellDenotedV.hoist_lift (X := ta₁) hok₂
    · exact (weakenTop (Ba := ta₁) ht).2 l hl''

/-- **Opening a binder**, type first; no `fvarsBelow` argument because
`wScoped` supplies it. -/
theorem openS {d : Nat} {Δa : List AnnotTerm}
    {ty body : Expr} {ta : AnnotTerm}
    (ht : CtxOk m φ d Δa ty) (hb : CtxOk m φ d Δa body)
    (hty : denoteMeta m.acval env φ d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) :
    CtxOk m φ (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
  openCongC hb ht hty hok fun _ _ => rfl

end CtxOk

/-- **Opening a binder extends the context correspondence** — the
lemma the `.forallE`/`.lam`/`.letE` clauses of every quarter need to
reach their recursive call.  Stated outside the namespace because
`open` is not a namespace-relative identifier. -/
theorem CtxOk.open {d : Nat} {Δa : List AnnotTerm} {body ty : Expr}
    {ta : AnnotTerm}
    (hb : CtxOk m φ d Δa body) (ht : CtxOk m φ d Δa ty)
    (hty : denoteMeta m.acval env φ d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) :
    CtxOk m φ (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
  CtxOk.openS ht hb hty hok

end ConLeche.Model
