module

public import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Leaves
import ConLeche.Model.Annot.BitInst

public section

/-!
# The context discipline, PREFIX-intrinsic (lane CONTSEM)

`CtxOk` states each leaf's link to its context entry, and the grading of
its annotation, under every valuation satisfying the WHOLE context.  A
container frame's walk (`nestFrame`) sees the context TRUNCATED at its
key's depth and extended by its holes: a valuation of the truncated
context need not extend to the whole one (a later entry may be an empty
type), so `CtxOk`'s facts do not survive the truncation.

`CtxOkP` states them where they live: leaf `l`'s link and grading under
every valuation satisfying the context BELOW `l` (`Δa.drop (d - l.1)`),
the annotation read at its own depth `l.1`.  It implies `CtxOk`
(`CtxOkP.toCtxOk`), is kept by opening a binder whose domain is graded
under the context (`CtxOkP.openS` — the domain's grading is exactly a
prefix fact), and survives truncation (`CtxOkP.drop`) and extension by
new top entries (`CtxOkP.extend`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **The prefix-intrinsic context discipline** (see the module
docstring). -/
@[expose] def CtxOkP (m : EnvModel V env) (φ : Name → Nat) (d : Nat) (Δa : List AnnotTerm)
    (e : Expr) : Prop :=
  Δa.length = d ∧ ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.WScoped l.1 l.2 ∧ ∃ tl Aa,
    denoteMeta m.acval env φ l.1 l.2 = some tl ∧ Δa[d - 1 - l.1]? = some Aa ∧
    ∀ σ : Nat → V, Sat V (Δa.drop (d - l.1)) σ →
      interp V σ tl = interp V σ Aa ∧ WellDenotedV V σ tl

namespace CtxOkP

theorem Sat_drop {Δ : List AnnotTerm} {ρ : Nat → V} (h : Sat V Δ ρ)
    (n : Nat) : Sat V (Δ.drop n) (fun j => ρ (j + n)) := by
  intro i Aa hi
  rw [List.getElem?_drop] at hi
  have h1 := h (n + i) Aa hi
  show ρ (i + n) ∈ˢ interp V (fun j => ρ (j + i + 1 + n)) Aa
  have e : (fun j => ρ (j + i + 1 + n)) = fun j => ρ (j + (n + i) + 1) := by
    funext j; congr 1; omega
  rw [e, show i + n = n + i by omega]
  exact h1

/-- **The prefix discipline gives the whole-context one.** -/
theorem toCtxOk {d : Nat} {Δa : List AnnotTerm} {e : Expr} (h : CtxOkP m φ d Δa e) :
    CtxOk m φ d Δa e := by
  refine ⟨h.1, fun l hl => ?_⟩
  obtain ⟨hlt, hws, tl, Aa, htl, hA, hk⟩ := h.2 l hl
  refine ⟨hlt, hws.fvarsBelow, tl.liftN (d - l.1) 0, Aa, ?_, hA, fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · rw [denoteMeta_lift m.acval_closed hws d (Nat.le_of_lt hlt), htl]; rfl
  · have hs := Sat_drop hρ (d - l.1)
    rw [interp_liftN, show (fun j => ρ (j + (d - 1 - l.1) + 1)) = fun j => ρ (j + (d - l.1)) by
      funext j; congr 1; omega]
    have e : shiftE (d - l.1) 0 ρ = fun j => ρ (j + (d - l.1)) := by
      funext j; simp [shiftE]
    rw [e]
    exact (hk _ hs).1
  · have hs := Sat_drop hρ (d - l.1)
    refine (WellDenotedV_liftN V (d - l.1) tl 0 ρ).mpr ?_
    have e : shiftE (d - l.1) 0 ρ = fun j => ρ (j + (d - l.1)) := by
      funext j; simp [shiftE]
    rw [e]
    exact (hk _ hs).2

theorem of_subset {d : Nat} {Δa : List AnnotTerm} {e e' : Expr}
    (hC : CtxOkP m φ d Δa e) (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    CtxOkP m φ d Δa e' :=
  ⟨hC.1, fun l hl => hC.2 l (hsub l hl)⟩

theorem forallE_ty {d : Nat} {Δa : List AnnotTerm} {ty body : Expr} {mb : ConLeche.BinderMeta}
    (hC : CtxOkP m φ d Δa (.forallE ty body mb)) : CtxOkP m φ d Δa ty :=
  hC.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl

theorem forallE_body {d : Nat} {Δa : List AnnotTerm} {ty body : Expr} {mb : ConLeche.BinderMeta}
    (hC : CtxOkP m φ d Δa (.forallE ty body mb)) : CtxOkP m φ d Δa body :=
  hC.of_subset fun _ hl => by rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl

/-- **Opening a binder** whose domain reads graded under the context. -/
theorem openS {d : Nat} {Δa : List AnnotTerm} {ty body : Expr} {ta : AnnotTerm}
    (ht : CtxOkP m φ d Δa ty) (hb : CtxOkP m φ d Δa body)
    (hty : denoteMeta m.acval env φ d ty = some ta)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) :
    CtxOkP m φ (d + 1) (ta :: Δa) (body.instantiate1 (.fvar d ty)) := by
  have hwt : Expr.WScoped d ty := (toCtxOk ht).wScoped
  have hold : ∀ l : Nat × Expr, (l.1 < d ∧ Expr.WScoped l.1 l.2 ∧ ∃ tl Aa,
      denoteMeta m.acval env φ l.1 l.2 = some tl ∧ Δa[d - 1 - l.1]? = some Aa ∧
      ∀ σ : Nat → V, Sat V (Δa.drop (d - l.1)) σ →
        interp V σ tl = interp V σ Aa ∧ WellDenotedV V σ tl) →
      (l.1 < d + 1 ∧ Expr.WScoped l.1 l.2 ∧ ∃ tl Aa,
      denoteMeta m.acval env φ l.1 l.2 = some tl ∧ (ta :: Δa)[d + 1 - 1 - l.1]? = some Aa ∧
      ∀ σ : Nat → V, Sat V ((ta :: Δa).drop (d + 1 - l.1)) σ →
        interp V σ tl = interp V σ Aa ∧ WellDenotedV V σ tl) := by
    rintro l ⟨hlt, hws, tl, Aa, htl, hA, hk⟩
    refine ⟨by omega, hws, tl, Aa, htl, ?_, ?_⟩
    · rw [show d + 1 - 1 - l.1 = (d - 1 - l.1) + 1 by omega]; simpa using hA
    · rw [show d + 1 - l.1 = (d - l.1) + 1 by omega]; simpa using hk
  refine ⟨by simp [hb.1], fun l hl => ?_⟩
  rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
  · exact hold l (hb.2 l hl')
  · rw [Expr.fvarLeaves] at hl'
    rcases List.mem_cons.mp hl' with rfl | hl''
    · refine ⟨by simp, hwt, ta, ta, hty, by simp, fun σ hσ => ⟨rfl, ?_⟩⟩
      have : (ta :: Δa).drop (d + 1 - d) = Δa := by simp
      rw [this] at hσ
      exact hok σ hσ
    · exact hold l (ht.2 l hl'')

/-- **Truncation** at a depth `h` above every leaf of the subject. -/
theorem drop {d h : Nat} {Δa : List AnnotTerm} {e e' : Expr} (hC : CtxOkP m φ d Δa e)
    (hle : h ≤ d) (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves ∧ l.1 < h) :
    CtxOkP m φ h (Δa.drop (d - h)) e' := by
  refine ⟨by rw [List.length_drop, hC.1]; omega, fun l hl => ?_⟩
  obtain ⟨hle', hlt⟩ := hsub l hl
  obtain ⟨-, hws, tl, Aa, htl, hA, hk⟩ := hC.2 l hle'
  refine ⟨hlt, hws, tl, Aa, htl, ?_, ?_⟩
  · rw [List.getElem?_drop, show d - h + (h - 1 - l.1) = d - 1 - l.1 by omega]; exact hA
  · rw [List.drop_drop, show d - h + (h - l.1) = d - l.1 by omega]; exact hk

/-- **Extension by new top entries** `Ts` (innermost first): a leaf below
`h` keeps its package; a leaf at `h + p` is a new variable whose
annotation reads `tl`, which IS its entry and is graded below it. -/
theorem extend {h g : Nat} {Δ Ts : List AnnotTerm} {e : Expr} (hTs : Ts.length = g)
    (hΔ : Δ.length = h)
    (hleaf : ∀ l ∈ e.fvarLeaves,
      (l.1 < h ∧ Expr.WScoped l.1 l.2 ∧ ∃ tl Aa,
        denoteMeta m.acval env φ l.1 l.2 = some tl ∧ Δ[h - 1 - l.1]? = some Aa ∧
        ∀ σ : Nat → V, Sat V (Δ.drop (h - l.1)) σ →
          interp V σ tl = interp V σ Aa ∧ WellDenotedV V σ tl) ∨
      (∃ p, p < g ∧ l.1 = h + p ∧ Expr.WScoped l.1 l.2 ∧ ∃ tl,
        denoteMeta m.acval env φ l.1 l.2 = some tl ∧ Ts[g - 1 - p]? = some tl ∧
        ∀ σ : Nat → V, Sat V ((Ts ++ Δ).drop (g - p)) σ → WellDenotedV V σ tl)) :
    CtxOkP m φ (h + g) (Ts ++ Δ) e := by
  refine ⟨by rw [List.length_append, hTs, hΔ]; omega, fun l hl => ?_⟩
  rcases hleaf l hl with ⟨hlt, hws, tl, Aa, htl, hA, hk⟩ | ⟨p, hp, hl1, hws, tl, htl, hT, hk⟩
  · refine ⟨by omega, hws, tl, Aa, htl, ?_, ?_⟩
    · rw [List.getElem?_append_right (by omega), hTs,
        show h + g - 1 - l.1 - g = h - 1 - l.1 by omega]; exact hA
    · rw [show h + g - l.1 = Ts.length + (h - l.1) by omega, List.drop_append,
        List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]; exact hk
  · refine ⟨by omega, hws, tl, tl, htl, ?_, fun σ hσ => ⟨rfl, ?_⟩⟩
    · rw [List.getElem?_append_left (by omega), show h + g - 1 - l.1 = g - 1 - p by omega]; exact hT
    · rw [show h + g - l.1 = g - p by omega] at hσ; exact hk σ hσ

end CtxOkP

end ConLeche.Model

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **`CtxOkP` at an opened frame** (`ctxOk_of_openers`' prefix form): a
context whose entries at the touched indices are the frame's own-depth
annotation readings, each graded below itself. -/
theorem ctxOkP_of_openers {k : Nat} {fvs : List Expr} {Aa : Nat → AnnotTerm}
    {Δa : List AnnotTerm} (hΔlen : Δa.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x) = some (Aa i))
    {e : Expr} {n : Nat}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hltE : ∀ l ∈ e.fvarLeaves, l.1 < n)
    (hent : ∀ i, i < n → Δa[k - 1 - i]? = some (Aa i))
    (hokA : ∀ i, i < n → ∀ σ : Nat → V, Sat V (Δa.drop (k - i)) σ → WellDenotedV V σ (Aa i)) :
    CtxOkP m φ k Δa e := by
  refine ⟨hΔlen, fun l hl => ?_⟩
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem (hleaf l hl)
  obtain ⟨ty, hx⟩ := hshape pos _ hpos
  obtain ⟨h1, h2⟩ : l.1 = pos ∧ l.2 = ty := by
    injection hx with a b
    exact ⟨a, b⟩
  subst h1 h2
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2 := by simpa [Expr.WScoped] using hw
  refine ⟨hwty.1, hwty.2, Aa l.1, Aa l.1, ?_, hent l.1 (hltE l hl), fun σ hσ =>
    ⟨rfl, hokA l.1 (hltE l hl) σ hσ⟩⟩
  have hd1 := hdoms l.1 _ hpos
  rwa [show Expr.fvarTypeD (Expr.fvar l.1 l.2) = l.2 from rfl] at hd1

end ConLeche.Model
