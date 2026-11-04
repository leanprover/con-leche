module

import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Denote.OpenRevDenote
public import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Denote.Depth
public section

/-!
# The `CtxOk` kit — restriction family (task #161, P3.4)

The context-discipline lemmas every threading clause of the P-tier
step proof reads, for the fuel-free `CtxOk`.  Going *down* is restriction
(`of_subset` at a `simp [Expr.fvarLeaves]`), spelled out per
`inferBody` branch so a consumer never reopens `fvarLeaves`.  Going
*up* through a binder (`open`/`openS`/`openCongC`/`weakenTop`) needs
the `denote` depth shift (`denote_shiftFrom`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V] {env : Env}
variable {m : EnvModel V env} {φ : Name → Nat}

namespace CtxOk

/-- No leaves, nothing to say. -/
theorem of_fvarLeaves_nil {d : Nat} {Δa : List Term} {e : Expr}
    (hlen : Δa.length = d) (h : e.fvarLeaves = []) :
    CtxOk m φ d Δa e := by
  refine ⟨hlen, fun l hl => ?_⟩
  rw [h] at hl
  exact nomatch hl

/-- Depth zero: the declaration-level shape. -/
theorem nil {e : Expr} (h : e.fvarLeaves = []) :
    CtxOk m φ 0 ([] : List Term) e :=
  of_fvarLeaves_nil rfl h

/-- Restriction along one expression — the only shape the threading
clauses need going down. -/
theorem of_subset {d : Nat} {Δa : List Term} {e e' : Expr}
    (hC : CtxOk m φ d Δa e)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    CtxOk m φ d Δa e' :=
  ⟨hC.1, fun l hl => hC.2 l (hsub l hl)⟩

/-! ### The projections, one per `inferBody` branch that recurses -/

theorem forallE_ty {d : Nat} {Δa : List Term}
    {ty body : Expr}
    (hC : CtxOk m φ d Δa (.forallE ty body)) :
    CtxOk m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem forallE_body {d : Nat} {Δa : List Term}
    {ty body : Expr}
    (hC : CtxOk m φ d Δa (.forallE ty body)) :
    CtxOk m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

end CtxOk

/-! ## The open family (task #161, P3 batch 2)

`CtxOk`'s upward kit:

1. **No fuel.**
2. **No `EnvWF`** in `weakenTop` and everything above it:
   `denote_weaken_top` has no sort runs and takes no `EnvWF`.  The
   *leaf* premise `hacl` is read out of the structure as
   `m.acval_closed`.
3. **The fourth conjunct rides `WellDenotedTy.hoist_lift`**, so every
   hoisted grading premise `hok` below is stated at `WellDenotedTy`.

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
  | lam ty b iht ihb =>
    intro d hfb h
    rw [ConLeche.Expr.WScoped]
    exact ⟨iht hfb.1
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl])),
      ihb hfb.2
        (fun l hl => h l (by simp [ConLeche.Expr.fvarLeaves, hl]))⟩
  | forallE ty b iht ihb =>
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
theorem wScoped {d : Nat} {Δa : List Term} {e : Expr}
    (hC : CtxOk m φ d Δa e) : Expr.WScoped d e :=
  wScoped_of_leaves e
    (Verify.Expr.fvarsBelow_of_fvarLeaves (e := e) (fun l hl => (hC.2 l hl).1))
    (fun l hl => (hC.2 l hl).2.1)

/-- **Weakening the context correspondence by one binder.**  Every
leaf of an already-scoped subject survives one more binder: its
annotation lifts (`denote_weaken_top`), its slot moves up by the new
head, `Sat_tail` carries the link, and `WellDenotedTy.hoist_lift` carries
the grading.

`henv` is **dropped** (see the section note): `denote_weaken_top`'s
only leaf premise is `hacl`, read here out of `m.acval_closed`.  No
`WScoped` premise either — `wScoped` above supplies it from the
package itself. -/
theorem weakenTop {d : Nat} {Δa : List Term} {Ba : Term} {e : Expr}
    (hC : CtxOk m φ d Δa e) : CtxOk m φ (d + 1) (Ba :: Δa) e := by
  have hw : Expr.WScoped d e := hC.wScoped
  refine ⟨by simp [hC.1], fun l hl => ?_⟩
  obtain ⟨hlt, hfb, tya, Aa, hden, hi, hlink, hok⟩ := hC.2 l hl
  have hwl : Expr.WScoped d l.2 :=
    (ConLeche.Expr.WScoped_leaves e hw l hl).2.mono (by omega)
  refine ⟨by omega, hfb, tya.liftN 1 0, Aa, ?_, ?_, ?_, ?_⟩
  · rw [denote_weaken_top m.acval_closed hwl, hden]
    rfl
  · rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
    simpa using hi
  · intro ρ hρ
    rw [show d + 1 - 1 - l.1 = d - 1 - l.1 + 1 from by omega,
      show Term.liftN 1 tya 0 = tya.lift from rfl,
      interp_lift (V := V) tya ρ, hlink _ (Sat_tail hρ)]
    congr 1
  · exact WellDenotedTy.hoist_lift (X := Ba) hok

/-- **Opening a binder congruence in the P currency.**
`hdom` is `DefEqClaim`'s conclusion partially applied, and `hok₂` is the
*opened variable's* grading, at `WellDenotedTy` because that is what
`CtxOk`'s leaf package carries. -/
theorem openCongC {d : Nat} {Δa : List Term} {body ty : Expr}
    {ta₁ ta₂ : Term}
    (hb : CtxOk m φ d Δa body) (ht : CtxOk m φ d Δa ty)
    (hty : denote m.acval env φ d ty = some ta₂)
    (hok₂ : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ ta₂)
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
      · rw [denote_weaken_top m.acval_closed hwt, hty]
        rfl
      · rw [show d + 1 - 1 - d = 0 from by omega]
        rfl
      · intro ρ hρ
        have hρ' : Sat V Δa (fun j => ρ (j + 1)) := Sat_tail hρ
        show interp V ρ (Term.liftN 1 ta₂ 0)
          = interp V (fun j => ρ (j + (d + 1 - 1 - d) + 1)) ta₁
        rw [show d + 1 - 1 - d = 0 from by omega,
          show Term.liftN 1 ta₂ 0 = ta₂.lift from rfl,
          interp_lift (V := V) ta₂ ρ]
        exact (hdom _ hρ').symm
      · exact WellDenotedTy.hoist_lift (X := ta₁) hok₂
    · exact (weakenTop (Ba := ta₁) ht).2 l hl''

/-- **Opening a binder**, type first; no `fvarsBelow` argument because
`wScoped` supplies it. -/
theorem openS {d : Nat} {Δa : List Term}
    {ty body : Expr} {ta : Term}
    (ht : CtxOk m φ d Δa ty) (hb : CtxOk m φ d Δa body)
    (hty : denote m.acval env φ d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ ta) :
    CtxOk m φ (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
  openCongC hb ht hty hok fun _ _ => rfl

end CtxOk

/-- **Opening a binder extends the context correspondence** — the
lemma the `.forallE`/`.lam`/`.letE` clauses of every quarter need to
reach their recursive call.  Stated outside the namespace because
`open` is not a namespace-relative identifier. -/
theorem CtxOk.open {d : Nat} {Δa : List Term} {body ty : Expr}
    {ta : Term}
    (hb : CtxOk m φ d Δa body) (ht : CtxOk m φ d Δa ty)
    (hty : denote m.acval env φ d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ ta) :
    CtxOk m φ (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
  CtxOk.openS ht hb hty hok

/-! ## The per-valuation discipline (task #342, L9)

`CtxOkS` is `CtxOk` without its grading conjunct, and `LeavesGr` is that
conjunct at one valuation.  The per-valuation motives
(`Model/Rules/Motive.lean`) carry the pair: opening a binder needs the
domain graded at the valuation in hand only, never at every satisfying
one. -/

/-- The full discipline gives the structural one. -/
theorem CtxOk.toS {d : Nat} {Δa : List Term} {e : Expr}
    (hC : CtxOk m φ d Δa e) : CtxOkS m φ d Δa e := by
  refine ⟨hC.1, fun l hl => ?_⟩
  obtain ⟨h1, h2, tya, Aa, h3, h4, h5, -⟩ := hC.2 l hl
  exact ⟨h1, h2, tya, Aa, h3, h4, h5⟩

/-- The full discipline grades the leaves at every satisfying valuation. -/
theorem CtxOk.leavesGr {d : Nat} {Δa : List Term} {e : Expr}
    (hC : CtxOk m φ d Δa e) {ρ : Nat → V} (hρ : Sat V Δa ρ) :
    LeavesGr m φ d e ρ := by
  intro l hl tya hden
  obtain ⟨-, -, tya', Aa, h3, -, -, h6⟩ := hC.2 l hl
  rw [h3] at hden
  cases hden
  exact h6 ρ hρ

namespace CtxOkS

theorem length {d : Nat} {Δa : List Term} {e : Expr}
    (h : CtxOkS m φ d Δa e) : Δa.length = d := h.1

/-- `CtxOkS` implies well-scopedness. -/
theorem wScoped {d : Nat} {Δa : List Term} {e : Expr}
    (hC : CtxOkS m φ d Δa e) : Expr.WScoped d e :=
  wScoped_of_leaves e
    (Verify.Expr.fvarsBelow_of_fvarLeaves (e := e) (fun l hl => (hC.2 l hl).1))
    (fun l hl => (hC.2 l hl).2.1)

theorem of_fvarLeaves_nil {d : Nat} {Δa : List Term} {e : Expr}
    (hlen : Δa.length = d) (h : e.fvarLeaves = []) :
    CtxOkS m φ d Δa e := by
  refine ⟨hlen, fun l hl => ?_⟩
  rw [h] at hl
  exact nomatch hl

theorem of_subset {d : Nat} {Δa : List Term} {e e' : Expr}
    (hC : CtxOkS m φ d Δa e)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    CtxOkS m φ d Δa e' :=
  ⟨hC.1, fun l hl => hC.2 l (hsub l hl)⟩

theorem app {d : Nat} {Δa : List Term} {f x : Expr}
    (hf : CtxOkS m φ d Δa f) (hx : CtxOkS m φ d Δa x) :
    CtxOkS m φ d Δa (.app f x) := by
  refine ⟨hf.1, fun l hl => ?_⟩
  rw [Expr.fvarLeaves] at hl
  rcases List.mem_append.mp hl with h | h
  · exact hf.2 l h
  · exact hx.2 l h

theorem app_fn {d : Nat} {Δa : List Term} {f x : Expr}
    (hC : CtxOkS m φ d Δa (.app f x)) : CtxOkS m φ d Δa f :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem app_arg {d : Nat} {Δa : List Term} {f x : Expr}
    (hC : CtxOkS m φ d Δa (.app f x)) : CtxOkS m φ d Δa x :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem forallE_ty {d : Nat} {Δa : List Term}
    {ty body : Expr}
    (hC : CtxOkS m φ d Δa (.forallE ty body)) :
    CtxOkS m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem forallE_body {d : Nat} {Δa : List Term}
    {ty body : Expr}
    (hC : CtxOkS m φ d Δa (.forallE ty body)) :
    CtxOkS m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem lam_ty {d : Nat} {Δa : List Term}
    {ty body : Expr}
    (hC : CtxOkS m φ d Δa (.lam ty body)) :
    CtxOkS m φ d Δa ty :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem lam_body {d : Nat} {Δa : List Term}
    {ty body : Expr}
    (hC : CtxOkS m φ d Δa (.lam ty body)) :
    CtxOkS m φ d Δa body :=
  hC.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem proj_arg {d : Nat} {Δa : List Term} {sn : Name}
    {i : Nat} {e : Expr}
    (hC : CtxOkS m φ d Δa (.proj sn i e)) :
    CtxOkS m φ d Δa e :=
  hC.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact hl

/-- Weakening by one binder. -/
theorem weakenTop {d : Nat} {Δa : List Term} {Ba : Term} {e : Expr}
    (hC : CtxOkS m φ d Δa e) : CtxOkS m φ (d + 1) (Ba :: Δa) e := by
  have hw : Expr.WScoped d e := hC.wScoped
  refine ⟨by simp [hC.1], fun l hl => ?_⟩
  obtain ⟨hlt, hfb, tya, Aa, hden, hi, hlink⟩ := hC.2 l hl
  have hwl : Expr.WScoped d l.2 :=
    (ConLeche.Expr.WScoped_leaves e hw l hl).2.mono (by omega)
  refine ⟨by omega, hfb, tya.liftN 1 0, Aa, ?_, ?_, ?_⟩
  · rw [denote_weaken_top m.acval_closed hwl, hden]
    rfl
  · rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 from by omega]
    simpa using hi
  · intro ρ hρ
    rw [show d + 1 - 1 - l.1 = d - 1 - l.1 + 1 from by omega,
      show Term.liftN 1 tya 0 = tya.lift from rfl,
      interp_lift (V := V) tya ρ, hlink _ (Sat_tail hρ)]
    congr 1

/-- **Opening a binder**, with no grading at all: the context's new
entry is the opened variable's own type reading. -/
theorem openS {d : Nat} {Δa : List Term} {body ty : Expr}
    {ta : Term}
    (ht : CtxOkS m φ d Δa ty) (hb : CtxOkS m φ d Δa body)
    (hty : denote m.acval env φ d ty = some ta) :
    CtxOkS m φ (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d ty)) := by
  have hwt : Expr.WScoped d ty := ht.wScoped
  refine ⟨by simp [hb.1], fun l hl => ?_⟩
  rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact (weakenTop (Ba := ta) hb).2 l hl'
  · rw [ConLeche.Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨by omega, hwt.fvarsBelow, ta.liftN 1 0, ta, ?_, ?_, ?_⟩
      · rw [denote_weaken_top m.acval_closed hwt, hty]
        rfl
      · rw [show d + 1 - 1 - d = 0 from by omega]
        rfl
      · intro ρ hρ
        show interp V ρ (Term.liftN 1 ta 0)
          = interp V (fun j => ρ (j + (d + 1 - 1 - d) + 1)) ta
        rw [show d + 1 - 1 - d = 0 from by omega,
          show Term.liftN 1 ta 0 = ta.lift from rfl,
          interp_lift (V := V) ta ρ]
    · exact (weakenTop (Ba := ta) ht).2 l hl''

end CtxOkS

namespace LeavesGr

theorem of_subset {d : Nat} {e e' : Expr} {ρ : Nat → V}
    (h : LeavesGr m φ d e ρ)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    LeavesGr m φ d e' ρ :=
  fun l hl => h l (hsub l hl)

theorem of_fvarLeaves_nil {d : Nat} {e : Expr} {ρ : Nat → V}
    (h : e.fvarLeaves = []) : LeavesGr m φ d e ρ := by
  intro l hl
  rw [h] at hl
  exact nomatch hl

theorem app {d : Nat} {f x : Expr} {ρ : Nat → V}
    (hf : LeavesGr m φ d f ρ) (hx : LeavesGr m φ d x ρ) :
    LeavesGr m φ d (.app f x) ρ := by
  intro l hl
  rw [Expr.fvarLeaves] at hl
  rcases List.mem_append.mp hl with h | h
  · exact hf l h
  · exact hx l h

theorem app_fn {d : Nat} {f x : Expr} {ρ : Nat → V}
    (h : LeavesGr m φ d (.app f x) ρ) : LeavesGr m φ d f ρ :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem app_arg {d : Nat} {f x : Expr} {ρ : Nat → V}
    (h : LeavesGr m φ d (.app f x) ρ) : LeavesGr m φ d x ρ :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem forallE_ty {d : Nat} {ty body : Expr}
    {ρ : Nat → V} (h : LeavesGr m φ d (.forallE ty body) ρ) :
    LeavesGr m φ d ty ρ :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem forallE_body {d : Nat} {ty body : Expr}
    {ρ : Nat → V} (h : LeavesGr m φ d (.forallE ty body) ρ) :
    LeavesGr m φ d body ρ :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem lam_ty {d : Nat} {ty body : Expr}
    {ρ : Nat → V} (h : LeavesGr m φ d (.lam ty body) ρ) :
    LeavesGr m φ d ty ρ :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem lam_body {d : Nat} {ty body : Expr}
    {ρ : Nat → V} (h : LeavesGr m φ d (.lam ty body) ρ) :
    LeavesGr m φ d body ρ :=
  h.of_subset fun _ hl => by
    rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

theorem proj_arg {d : Nat} {sn : Name} {i : Nat} {e : Expr} {ρ : Nat → V}
    (h : LeavesGr m φ d (.proj sn i e) ρ) : LeavesGr m φ d e ρ :=
  h.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact hl

/-- Weakening by one binder: the leaves' readings lift, the valuation
gains a head. -/
theorem weakenTop {d : Nat} {Δa : List Term} {e : Expr} {ρ : Nat → V}
    (hC : CtxOkS m φ d Δa e) (h : LeavesGr m φ d e (fun j => ρ (j + 1))) :
    LeavesGr m φ (d + 1) e ρ := by
  have hw : Expr.WScoped d e := hC.wScoped
  intro l hl tya hden
  have hlt : l.1 < d := (hC.2 l hl).1
  have hwl : Expr.WScoped d l.2 :=
    (ConLeche.Expr.WScoped_leaves e hw l hl).2.mono (by omega)
  rw [denote_weaken_top m.acval_closed hwl] at hden
  obtain ⟨tya₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hden
  refine (WellDenotedTy_liftN 1 tya₀ 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h l hl tya₀ h₀

/-- **Opening a binder at one valuation**: the opened variable's type is
graded at the outer valuation. -/
theorem «open» {d : Nat} {Δa : List Term} {body ty : Expr}
    {ta : Term} {ρ : Nat → V} {x : V}
    (hCt : CtxOkS m φ d Δa ty) (hCb : CtxOkS m φ d Δa body)
    (ht : LeavesGr m φ d ty ρ) (hb : LeavesGr m φ d body ρ)
    (hty : denote m.acval env φ d ty = some ta)
    (hok : WellDenotedTy V ρ ta) :
    LeavesGr m φ (d + 1) (body.instantiate1 (.fvar d ty)) (cons x ρ) := by
  have hwt : Expr.WScoped d ty := hCt.wScoped
  intro l hl tya hden
  rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact weakenTop (ρ := cons x ρ) hCb hb l hl' tya hden
  · rw [ConLeche.Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · rw [denote_weaken_top m.acval_closed hwt, hty] at hden
      cases hden
      refine (WellDenotedTy_liftN 1 ta 0 (cons x ρ)).mpr ?_
      rw [shiftE_zero]
      exact hok
    · exact weakenTop (ρ := cons x ρ) hCt ht l hl'' tya hden

end LeavesGr

end ConLeche.Model
