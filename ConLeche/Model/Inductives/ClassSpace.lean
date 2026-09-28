module

public import ConLeche.Model.Inductives.ClassFieldAcc
public import ConLeche.Model.Annot.LfpAcc
public import ConLeche.Model.Annot.BlockLfpTup

public section

/-!
# The class facts' valuation space: one position per hole (P2d, DESIGN CLASSCHECK / P2D4)

The class check's holes are the variables `nP ..< hi` of one context: the
members' (`nP ..< hiAt 0`, each a family curried over the parameters and
its indices) and the container classes' (`hiAt 0 ..< hi`, ATOMIC: a
family over the class's indices, the parameters baked in).  The class
facts' valuation space has ONE POSITION PER HOLE (position `t` is the
variable `nP + t`), and a valuation `Z` is read at the holes as their
λ-towers of graphs — exactly an lfp datum's HOLE FRAME (`LfpDatum.frame`),
for the datum `classSpace` whose "members" are the holes: a member hole's
own telescope is the parameters then its indices, a class hole's only its
indices (`pars = []`).  So the hole order and the accessibility relation
of that datum (`tupRel`, `accRel`), with their laws (the holes grow at
their full arity, `holeOn_tupRel`; they are rich, `accRel_rich`), are the
class check's hole relations (`ClassHoleRel`, `ClassHoleRelA`) — T4
(`fieldD_mono`/`fieldD_acc`) applies at the hole frames of the space
(`classHoleRel_tupRel`, `classHoleRelA_accRel`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name NestCtx ClassInfo)

universe w

variable {V : Type w} [SetTheory V]

/-- **The class facts' valuation space** as an lfp datum over the holes:
`nh` holes at the level `w` over the parameter telescope `params`, hole
`t`'s own telescope `pars t ++ ids t` at the index sort `u t` (the
operator and constructors unused). -/
@[expose] noncomputable def classSpace (nh w : Nat) (params : List AnnotTerm) (pars ids : Nat → List AnnotTerm)
    (u : Nat → Nat) : LfpDatum V where
  names := []
  k := nh
  N := nh
  w := fun _ => w
  params := fun _ => params
  pars := fun t _ => pars t
  ids := fun t _ => ids t
  u := fun t _ => u t
  Φ := fun _ _ X => X
  inj := fun _ _ _ _ => pt
  nctors := fun _ => 0
  ctorName := fun _ _ => .anonymous
  fields := fun _ _ _ => []
  resIdx := fun _ _ _ => []

/-- Fewer admissible items keep richness. -/
theorem RichOn.mono' {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q' i n → Q i n) {R : FrameRel V}
    (h : RichOn Q R) : RichOn Q' R := by
  intro ρ ρ₀ hR i vs hq hpt
  obtain ⟨ρ'', hR'', hle, hz⟩ := h ρ ρ₀ hR i vs (hQ _ _ hq) hpt
  exact ⟨ρ'', hR'', fun o ho hH => hle o (hQ _ _ ho) hH, hz⟩

/-- Off the holes at the top of the class context: the positions at or
above the number of holes. -/
theorem not_holeP_top {nP nh hi j : Nat} (hhi : hi = nP + nh) (h : ¬ holeP hi nP hi j) :
    nh ≤ j := by
  unfold holeP at h
  omega

section Rel

variable {ctx : NestCtx} {cls : List ClassInfo} {hi : Nat} {Dv : LfpDatum V} {ψ : Name → Nat}
  {ρp : Nat → V} {Δa : List AnnotTerm}

/-- **The hole order of the space is the class check's hole relation**
(T4's `ClassHoleRel`) at the top of the class context, when the hole
context is satisfied at every hole frame of the space and every hole of
the class check is a hole of the space at the space's arity. -/
theorem classHoleRel_tupRel (hkN : Dv.k ≤ Dv.N) (hhi : hi = ctx.nP + Dv.k)
    (har : ∀ i n, ClassHoleAr ctx cls hi i n →
      n = (Dv.pars (i - ctx.nP) ψ).length + (Dv.ids (i - ctx.nP) ψ).length)
    (hsat : ∀ X, InTupleSpace (Dv.w ψ) Dv.N (Dv.idx ψ ρp) X → Sat V Δa (Dv.frame ψ ρp X)) :
    ClassHoleRel ctx cls hi hi Δa (Dv.tupRel ψ ρp) where
  dom := by
    rintro _ _ ⟨X, Y, hX, hY, -, rfl, rfl⟩
    exact ⟨hsat X hX, hsat Y hY⟩
  agree := fun σ σ' hr i hi' =>
    LfpDatum.tupRel_agreeOff hr i (not_holeP_top hhi hi')
  hole := by
    intro i n har'
    have hlo := har'.1
    have hlt := har'.2.1
    have hn := har i n har'
    have ht : i - ctx.nP < Dv.k := by omega
    have := LfpDatum.holeOn_tupRel (ψ := ψ) (ρp := ρp) hkN ht
    rw [show Dv.k - 1 - (i - ctx.nP) = hi - 1 - i by omega, ← hn] at this
    exact this

/-- **The accessibility relation of the space is the class check's
accessibility hole relation** (T4's `ClassHoleRelA`) at the top of the
class context, at a positive level. -/
theorem classHoleRelA_accRel (hkN : Dv.k ≤ Dv.N) (hw : Dv.w ψ ≠ 0) (hhi : hi = ctx.nP + Dv.k)
    (har : ∀ i n, ClassHoleAr ctx cls hi i n →
      n = (Dv.pars (i - ctx.nP) ψ).length + (Dv.ids (i - ctx.nP) ψ).length)
    (hsat : ∀ X, InTupleSpace (Dv.w ψ) Dv.N (Dv.idx ψ ρp) X → Sat V Δa (Dv.frame ψ ρp X)) :
    ClassHoleRelA ctx cls hi hi Δa (Dv.accRel ψ ρp) where
  dom := by
    rintro _ _ ⟨X, Y, hX, hY, rfl, rfl⟩
    exact ⟨hsat X hX, hsat Y hY⟩
  agree := fun σ σ' hr i hi' =>
    LfpDatum.accRel_agreeOff hr i (not_holeP_top hhi hi')
  symm := LfpDatum.accRel_symm
  rich := by
    refine RichOn.mono' (fun j n hq => ?_) (LfpDatum.accRel_rich hkN hw)
    obtain ⟨i, hi', rfl, har'⟩ := hq
    have hlo := har'.1
    have hlt := har'.2.1
    exact ⟨i - ctx.nP, by omega, by omega, har i n har'⟩

omit [SetTheory V] in
/-- The class check's admissible items are the space's. -/
theorem classHoleQ_memberQ (hhi : hi = ctx.nP + Dv.k)
    (har : ∀ i n, ClassHoleAr ctx cls hi i n →
      n = (Dv.pars (i - ctx.nP) ψ).length + (Dv.ids (i - ctx.nP) ψ).length) :
    ∀ j n, ClassHoleQ ctx cls hi hi j n → Dv.MemberQ ψ j n := by
  rintro j n ⟨i, hi', rfl, har'⟩
  have hlo := har'.1
  have hlt := har'.2.1
  exact ⟨i - ctx.nP, by omega, by omega, har i n har'⟩

end Rel

end ConLeche.Model
