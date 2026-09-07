--#export Acc'.zero_intro Acc'.fix_intro Acc'.inv

/-! Task #202 Stage A2: an `Acc` clone — a `Prop`-valued reflexive block
with ONE constructor and the LARGE eliminator (official's subsingleton
elimination: the data field `x` is an index, the field `h` a
`Prop`-valued function), with consumers eliminating into `Type` and
firing iota by `rfl`. -/

inductive Acc' {α : Type} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : ∀ y, r y x → Acc' r y) : Acc' r x

/-- Large elimination into `Nat`: the constant motive, the minor
ignoring the hypotheses. -/
noncomputable def Acc'.zero {α : Type} {r : α → α → Prop} {x : α} (a : Acc' r x) : Nat :=
  Acc'.rec (motive := fun _ _ => Nat) (fun _ _ _ => 0) a

theorem Acc'.zero_intro {α : Type} {r : α → α → Prop} (x : α) (h : ∀ y, r y x → Acc' r y) :
    Acc'.zero (Acc'.intro x h) = 0 := rfl

/-- Well-founded recursion through the eliminator: `fix` over the
accessibility proof, the recursive calls at the hypotheses. -/
noncomputable def Acc'.fix {α : Type} {r : α → α → Prop} {C : α → Type}
    (F : ∀ x, (∀ y, r y x → C y) → C x) {x : α} (a : Acc' r x) : C x :=
  Acc'.rec (motive := fun x _ => C x) (fun x _ ih => F x ih) a

theorem Acc'.fix_intro {α : Type} {r : α → α → Prop} {C : α → Type}
    (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) (h : ∀ y, r y x → Acc' r y) :
    Acc'.fix F (Acc'.intro x h) = F x (fun y hy => Acc'.fix F (h y hy)) := rfl

/-- Small elimination too. -/
theorem Acc'.inv {α : Type} {r : α → α → Prop} {x y : α} (a : Acc' r x) (hy : r y x) : Acc' r y :=
  Acc'.rec (motive := fun x _ => ∀ y, r y x → Acc' r y) (fun _ h _ => h) a y hy
