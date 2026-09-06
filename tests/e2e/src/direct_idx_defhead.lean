--#export OfFn.mk OfFn.inv OfFn.of_eq Rel Rel.mk Rel.rec Rel.some_idx

/- End-to-end test (task #193): an indexed one-constructor family whose
   type former is declared AT A DEFINITION that only *unfolds* to a
   telescope — the shape of Mathlib's `CategoryTheory.Presieve.ofArrows`
   (`inductive ofArrows … : Presieve X` with `Presieve X := ∀ ⦃Y⦄, Set
   (Y ⟶ X)`), whose declared type ends in `Presieve C inst X` while the
   kernel counts two indices.  The direct routes read the former's
   declared type as a syntactic telescope (`stripPis (nP + nIdx)` ending
   in a `Sort`), so they do NOT take such a block; the preprocessor's
   predicate used to say `native` off `numIndices` alone, and the
   checker then had neither a model nor a direct install — a decline.
   With `lechFormerTelescope` in the predicate the block is modelled
   again and the stream ACCEPTS through the modelled path.  `Rel` is the
   control: the same family declared with its telescope spelled out,
   which the direct indexed route takes. -/

universe u

/-- The definition-headed family type: `Pred α` unfolds to `α → Prop`. -/
def Pred (α : Type u) : Type u := α → Prop

/-- `OfFn f a` holds iff `a` is in the image of `f`; the constructor's
index is the general term `f i`.  Declared at `Pred α`, so the stored
type former ends in a constant application, not in `Sort`. -/
inductive OfFn {α : Type u} (f : Nat → α) : Pred α where
  | mk (i : Nat) : OfFn f (f i)

theorem OfFn.inv {α : Type u} (f : Nat → α) (a : α) (h : OfFn f a) :
    ∃ i, f i = a :=
  OfFn.rec (motive := fun a _ => ∃ i, f i = a) (fun i => ⟨i, rfl⟩) h

theorem OfFn.of_eq {α : Type u} (f : Nat → α) (a : α) (i : Nat) (h : f i = a) :
    OfFn f a :=
  h ▸ OfFn.mk i

/-- The control: the same family with the telescope spelled out. -/
inductive Rel {α : Type u} (f : Nat → α) : α → Prop where
  | mk (i : Nat) : Rel f (f i)

theorem Rel.some_idx {α : Type u} (f : Nat → α) (a : α) (h : Rel f a) :
    ∃ i, f i = a :=
  Rel.rec (motive := fun a _ => ∃ i, f i = a) (fun i => ⟨i, rfl⟩) h
