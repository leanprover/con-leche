--#export Opt.getD_none Opt.getD_some Opt.map_some Sum'.swap_inl Sum'.swap_inr Sum'.elim_inr Dec.decide_true Dec.decide_false

/- End-to-end test: the **direct sum** install (task #175 sum-types) on
   parameterised sums with fields — an option-like type (two
   constructors, a dependent field), a universe-polymorphic sum, and a
   decidability-like type over a `Prop` parameter (`Dec p`, whose
   `isFalse` field mentions `False`, a zero-constructor `Prop`
   inductive that goes direct too).  Every recursor use is a `rfl`
   through iota on each constructor in turn. -/

universe u v

inductive Opt (α : Type u) : Type u where
  | none : Opt α
  | some (a : α) : Opt α

noncomputable def Opt.getD {α : Type u} (o : Opt α) (d : α) : α :=
  Opt.rec (motive := fun _ => α) d (fun a => a) o

theorem Opt.getD_none {α : Type u} (d : α) : Eq (Opt.getD (Opt.none : Opt α) d) d := rfl
theorem Opt.getD_some {α : Type u} (a d : α) : Eq (Opt.getD (Opt.some a) d) a := rfl

def Opt.map {α : Type u} {β : Type v} (f : α → β) : Opt α → Opt β
  | .none => .none
  | .some a => .some (f a)

theorem Opt.map_some {α : Type u} {β : Type v} (f : α → β) (a : α) :
    Eq (Opt.map f (Opt.some a)) (Opt.some (f a)) := rfl

inductive Sum' (α : Type u) (β : Type v) : Type (max u v) where
  | inl (a : α) : Sum' α β
  | inr (b : β) : Sum' α β

def Sum'.swap {α : Type u} {β : Type v} : Sum' α β → Sum' β α
  | .inl a => .inr a
  | .inr b => .inl b

theorem Sum'.swap_inl {α : Type u} {β : Type v} (a : α) :
    Eq (Sum'.swap (Sum'.inl (β := β) a)) (Sum'.inr a) := rfl
theorem Sum'.swap_inr {α : Type u} {β : Type v} (b : β) :
    Eq (Sum'.swap (Sum'.inr (α := α) b)) (Sum'.inl b) := rfl

noncomputable def Sum'.elim {α : Type u} {β : Type v} {γ : Sort w} (s : Sum' α β) (l : α → γ) (r : β → γ) : γ :=
  Sum'.rec (motive := fun _ => γ) l r s

theorem Sum'.elim_inr {α : Type u} {β : Type v} (b : β) (l : α → Nat) (r : β → Nat) :
    Eq (Sum'.elim (Sum'.inr b) l r) (r b) := rfl

inductive Dec (p : Prop) : Type where
  | isFalse (h : Not p) : Dec p
  | isTrue (h : p) : Dec p

noncomputable def Dec.decide (p : Prop) (d : Dec p) : Bool :=
  Dec.casesOn (motive := fun _ => Bool) d (fun _ => false) (fun _ => true)

theorem Dec.decide_true (p : Prop) (h : p) : Eq (Dec.decide p (Dec.isTrue h)) true := rfl
theorem Dec.decide_false (p : Prop) (h : Not p) : Eq (Dec.decide p (Dec.isFalse h)) false := rfl
