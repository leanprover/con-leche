module

public import ConLeche.Model.Inductives.ClassSubst

public section

/-!
# The classes recognised inside a term (P2d, DESIGN CLASSCHECK / P2D4)

The class abstraction restricted to a set of holes (`classAbsF`) reads
only the classes it RECOGNISES inside its argument (`RecIn`: some
subterm is an occurrence of the class).  Two restrictions agreeing on
those classes are the same term (`classAbsSpec_restrict_congr`) — so a
coherent class's key read with the READER's stage classes abstracted is
its key read with its OWN free classes abstracted, when the two sets
agree inside the key (the demand).  A class recognised inside a key is
smaller than the key's class (`Expr.shape`, blind to levels and to the
free variables' annotations, `eqUpToLevels_shape`): the order in which a
reader fills its coherent classes.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche (Expr ClassInfo)

/-- `x` is a subterm of `e` (reflexively). -/
@[expose] def Expr.SubOf (x : Expr) : Expr → Prop
  | .app f a => x = .app f a ∨ Expr.SubOf x f ∨ Expr.SubOf x a
  | .lam t b m => x = .lam t b m ∨ Expr.SubOf x t ∨ Expr.SubOf x b
  | .forallE t b m => x = .forallE t b m ∨ Expr.SubOf x t ∨ Expr.SubOf x b
  | .letE t v b => x = .letE t v b ∨ Expr.SubOf x t ∨ Expr.SubOf x v ∨ Expr.SubOf x b
  | .proj s i y => x = .proj s i y ∨ Expr.SubOf x y
  | e => x = e

theorem Expr.SubOf.refl : ∀ e : Expr, Expr.SubOf e e := by
  intro e; cases e <;> simp [Expr.SubOf]

/-- **A hole recognised inside `e`**: some subterm is an occurrence of it. -/
@[expose] def RecIn (occ : Expr → Option (Expr × Nat)) (e h : Expr) : Prop :=
  ∃ x n, Expr.SubOf x e ∧ occ x = some (h, n)

theorem RecIn.appF {occ : Expr → Option (Expr × Nat)} {f a h : Expr} (hr : RecIn occ f h) :
    RecIn occ (.app f a) h := by
  obtain ⟨x, n, hs, ho⟩ := hr; exact ⟨x, n, Or.inr (Or.inl hs), ho⟩

theorem RecIn.appA {occ : Expr → Option (Expr × Nat)} {f a h : Expr} (hr : RecIn occ a h) :
    RecIn occ (.app f a) h := by
  obtain ⟨x, n, hs, ho⟩ := hr; exact ⟨x, n, Or.inr (Or.inr hs), ho⟩

/-- **Two restrictions agreeing on the recognised classes abstract alike.** -/
theorem classAbsSpec_restrict_congr (occ : Expr → Option (Expr × Nat)) {F F' : Expr → Bool} :
    ∀ (e : Expr) (m : Option (Expr × Nat)), (∀ h, RecIn occ e h → F h = F' h) →
      classAbsSpec (occRestrict occ F) m e = classAbsSpec (occRestrict occ F') m e := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro m hag
    have hf : ∀ h, RecIn occ f h → F h = F' h := fun h hr => hag h hr.appF
    have ha : ∀ h, RecIn occ a h → F h = F' h := fun h hr => hag h hr.appA
    have hocc : occRestrict occ F (.app f a) = occRestrict occ F' (.app f a) := by
      unfold occRestrict
      cases hx : occ (.app f a) with
      | none => rfl
      | some p =>
        obtain ⟨h, n⟩ := p
        simp only
        rw [hag h ⟨_, n, Expr.SubOf.refl _, hx⟩]
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [classAbsSpec, hocc]
      split
      · rfl
      · rw [ihf _ hf, iha _ ha]
      · rw [ihf _ hf, iha _ ha]
    · rfl
    · simp only [classAbsSpec]; rw [ihf _ hf, iha _ ha]
  | lam t b bm iht ihb =>
    intro m hag
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [classAbsSpec]
      rw [iht _ fun h ⟨x, n, hs, ho⟩ => hag h ⟨x, n, Or.inr (Or.inl hs), ho⟩,
        ihb _ fun h ⟨x, n, hs, ho⟩ => hag h ⟨x, n, Or.inr (Or.inr hs), ho⟩]
    · rfl
    · rfl
  | forallE t b bm iht ihb =>
    intro m hag
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [classAbsSpec]
      rw [iht _ fun h ⟨x, n, hs, ho⟩ => hag h ⟨x, n, Or.inr (Or.inl hs), ho⟩,
        ihb _ fun h ⟨x, n, hs, ho⟩ => hag h ⟨x, n, Or.inr (Or.inr hs), ho⟩]
    · rfl
    · rfl
  | letE t v b iht ihv ihb =>
    intro m hag
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [classAbsSpec]
      rw [iht _ fun h ⟨x, n, hs, ho⟩ => hag h ⟨x, n, Or.inr (Or.inl hs), ho⟩,
        ihv _ fun h ⟨x, n, hs, ho⟩ => hag h ⟨x, n, Or.inr (Or.inr (Or.inl hs)), ho⟩,
        ihb _ fun h ⟨x, n, hs, ho⟩ => hag h ⟨x, n, Or.inr (Or.inr (Or.inr hs)), ho⟩]
    · rfl
    · rfl
  | proj s i y ihy =>
    intro m hag
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [classAbsSpec]
      rw [ihy _ fun h ⟨x, n, hs, ho⟩ => hag h ⟨x, n, Or.inr hs, ho⟩]
    · rfl
    · rfl
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro m _
    rcases m with _ | ⟨h, _ | n⟩ <;> rfl

/-- `classAbsF` at two restrictions agreeing on the recognised classes. -/
theorem classAbsF_congr {cls : List ClassInfo} {F F' : Expr → Bool} {e : Expr}
    (hag : ∀ h, RecIn (ConLeche.classOcc? cls) e h → F h = F' h) :
    classAbsF cls F e = classAbsF cls F' e := by
  unfold classAbsF
  exact classAbsSpec_restrict_congr _ e none hag

/-! ## The shape of a term, blind to levels and annotations -/

/-- The number of nodes, levels and free variables' annotations not
counted. -/
@[expose] def Expr.shape : Expr → Nat
  | .app f a => Expr.shape f + Expr.shape a + 1
  | .lam t b _ => Expr.shape t + Expr.shape b + 1
  | .forallE t b _ => Expr.shape t + Expr.shape b + 1
  | .letE t v b => Expr.shape t + Expr.shape v + Expr.shape b + 1
  | .proj _ _ y => Expr.shape y + 1
  | _ => 1

theorem Expr.shape_pos : ∀ e : Expr, 0 < Expr.shape e := by
  intro e; cases e <;> simp [Expr.shape]

/-- **Spellings the same up to levels have one shape.** -/
theorem Expr.eqUpToLevels_shape : ∀ {a b : Expr}, ConLeche.Expr.eqUpToLevels a b = true →
    Expr.shape a = Expr.shape b := by
  intro a
  induction a with
  | app f x ihf ihx =>
    intro b h
    cases b <;> simp only [ConLeche.Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h
    simp only [Expr.shape, ihf h.1, ihx h.2]
  | lam t x m iht ihx =>
    intro b h
    cases b <;> simp only [ConLeche.Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h
    simp only [Expr.shape, iht h.1.2, ihx h.2]
  | forallE t x m iht ihx =>
    intro b h
    cases b <;> simp only [ConLeche.Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h
    simp only [Expr.shape, iht h.1.2, ihx h.2]
  | letE t v x iht ihv ihx =>
    intro b h
    cases b <;> simp only [ConLeche.Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h
    simp only [Expr.shape, iht h.1.1, ihv h.1.2, ihx h.2]
  | proj s i y ihy =>
    intro b h
    cases b <;> simp only [ConLeche.Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h
    simp only [Expr.shape, ihy h.2]
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro b h
    cases b <;> simp_all [ConLeche.Expr.eqUpToLevels, Expr.shape]

/-- A strict subterm is smaller. -/
theorem Expr.SubOf.shape_le : ∀ {x e : Expr}, Expr.SubOf x e → Expr.shape x ≤ Expr.shape e := by
  intro x e
  induction e with
  | app f a ihf iha =>
    rintro (rfl | h | h)
    · exact Nat.le_refl _
    · have := ihf h; simp [Expr.shape]; omega
    · have := iha h; simp [Expr.shape]; omega
  | lam t b m iht ihb =>
    rintro (rfl | h | h)
    · exact Nat.le_refl _
    · have := iht h; simp [Expr.shape]; omega
    · have := ihb h; simp [Expr.shape]; omega
  | forallE t b m iht ihb =>
    rintro (rfl | h | h)
    · exact Nat.le_refl _
    · have := iht h; simp [Expr.shape]; omega
    · have := ihb h; simp [Expr.shape]; omega
  | letE t v b iht ihv ihb =>
    rintro (rfl | h | h | h)
    · exact Nat.le_refl _
    · have := iht h; simp [Expr.shape]; omega
    · have := ihv h; simp [Expr.shape]; omega
    · have := ihb h; simp [Expr.shape]; omega
  | proj s i y ihy =>
    rintro (rfl | h)
    · exact Nat.le_refl _
    · have := ihy h; simp [Expr.shape]; omega
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro h; simp only [Expr.SubOf] at h; subst h; exact Nat.le_refl _

end ConLeche.Model
