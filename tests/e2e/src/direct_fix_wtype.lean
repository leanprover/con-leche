--#export W'.elim_sup W'.size_sup W'.hd_sup PSet'.elim_mk PSet'.card_mk PSet'.hd_mk

/-! Task #202 Stage B: `Type`-valued REFLEXIVE blocks on the direct
fixed-point route — the W-type `W' α β` (a data field and a function-space
field into the block over a domain depending on the data field, one
constructor, large eliminator) and the `PSet`-shaped `PSet'` (a `Type 1`
block whose reflexive field's domain is a `Type` — the telescope domain's
universe bound at the family's regime).  Consumers eliminate into `Type`
and into `Prop` and fire iota by `rfl`. -/

inductive W' (α : Type) (β : α → Type) : Type where
  | sup (a : α) (f : β a → W' α β) : W' α β

/-- Large elimination with a dependent motive, the ih pointwise under
the field's telescope. -/
noncomputable def W'.elim {α : Type} {β : α → Type} {C : W' α β → Type}
    (F : ∀ a f, (∀ b, C (f b)) → C (W'.sup a f)) (w : W' α β) : C w :=
  W'.rec (motive := fun w => C w) (fun a f ih => F a f ih) w

theorem W'.elim_sup {α : Type} {β : α → Type} {C : W' α β → Type}
    (F : ∀ a f, (∀ b, C (f b)) → C (W'.sup a f)) (a : α) (f : β a → W' α β) :
    W'.elim F (W'.sup a f) = F a f (fun b => W'.elim F (f b)) := rfl

/-- A constant motive: the depth along a chosen branch. -/
noncomputable def W'.size {α : Type} {β : α → Type} (pick : ∀ a, β a) (w : W' α β) : Nat :=
  W'.rec (motive := fun _ => Nat) (fun a _ ih => Nat.succ (ih (pick a))) w

theorem W'.size_sup {α : Type} {β : α → Type} (pick : ∀ a, β a) (a : α) (f : β a → W' α β) :
    W'.size pick (W'.sup a f) = Nat.succ (W'.size pick (f (pick a))) := rfl

/-- Small elimination. -/
theorem W'.hd {α : Type} {β : α → Type} (w : W' α β) : ∃ a, ∃ f : β a → W' α β, w = W'.sup a f :=
  W'.rec (motive := fun w => ∃ a, ∃ f : β a → W' α β, w = W'.sup a f) (fun a f _ => ⟨a, f, rfl⟩) w

theorem W'.hd_sup {α : Type} {β : α → Type} (a : α) (f : β a → W' α β) :
    W'.hd (W'.sup a f) = ⟨a, f, rfl⟩ := rfl

inductive PSet' : Type 1 where
  | mk (α : Type) (f : α → PSet') : PSet'

noncomputable def PSet'.elim {C : PSet' → Type 1}
    (F : ∀ α f, (∀ a, C (f a)) → C (PSet'.mk α f)) (x : PSet') : C x :=
  PSet'.rec (motive := fun x => C x) (fun α f ih => F α f ih) x

theorem PSet'.elim_mk {C : PSet' → Type 1} (F : ∀ α f, (∀ a, C (f a)) → C (PSet'.mk α f))
    (α : Type) (f : α → PSet') : PSet'.elim F (PSet'.mk α f) = F α f (fun a => PSet'.elim F (f a)) := rfl

/-- The carrier type of the root: elimination into `Type 1` with a
constant motive. -/
noncomputable def PSet'.card (x : PSet') : Type := PSet'.rec (motive := fun _ => Type) (fun α _ _ => α) x

theorem PSet'.card_mk (α : Type) (f : α → PSet') : PSet'.card (PSet'.mk α f) = α := rfl

theorem PSet'.hd (x : PSet') : ∃ α, ∃ f : α → PSet', x = PSet'.mk α f :=
  PSet'.rec (motive := fun x => ∃ α, ∃ f : α → PSet', x = PSet'.mk α f) (fun α f _ => ⟨α, f, rfl⟩) x

theorem PSet'.hd_mk (α : Type) (f : α → PSet') : PSet'.hd (PSet'.mk α f) = ⟨α, f, rfl⟩ := rfl
