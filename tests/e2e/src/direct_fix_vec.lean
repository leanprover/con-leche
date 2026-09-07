--#export Vec'.length_nil Vec'.length_cons Vec'.map_cons Vec'.map_nil Vec'.headD_cons Vec'.small_cons Tm.size_app Tm.size_var

/- End-to-end test (task #188 indexed): `Type`-valued INDEXED recursive
   families through the direct fixed-point install.

   * `Vec' α n` — the `Vector`-like family with a RECURSIVE `cons`
     whose index expression `Nat.succ n` reads an earlier data field;
     the consumers fire iota on `cons` reading the inductive hypothesis
     with a constant motive (`length`), with a motive that reads the
     index (`map : Vec' β n`), dropping the hypothesis (`headD`) and
     into `Prop` (`small`);
   * `Tm k n` — a parameter and an index, two recursive fields in one
     constructor at DIFFERENT index expressions (`n` and `Nat.add n k`,
     the second through the parameter), two hypotheses per minor. -/

universe u

inductive Vec' (α : Type u) : Nat → Type u where
  | nil : Vec' α Nat.zero
  | cons (n : Nat) (a : α) (v : Vec' α n) : Vec' α (Nat.succ n)

noncomputable def Vec'.length {α : Type u} {n : Nat} (v : Vec' α n) : Nat :=
  Vec'.rec (motive := fun _ _ => Nat) Nat.zero (fun _ _ _ ih => Nat.succ ih) v

theorem Vec'.length_nil {α : Type u} :
    Eq (Vec'.length (Vec'.nil : Vec' α Nat.zero)) Nat.zero := rfl
theorem Vec'.length_cons {α : Type u} (n : Nat) (a : α) (v : Vec' α n) :
    Eq (Vec'.length (Vec'.cons n a v)) (Nat.succ (Vec'.length v)) := rfl

noncomputable def Vec'.map {α β : Type u} (f : α → β) {n : Nat} (v : Vec' α n) : Vec' β n :=
  Vec'.rec (motive := fun n _ => Vec' β n) Vec'.nil (fun n a _ ih => Vec'.cons n (f a) ih) v

theorem Vec'.map_nil {α β : Type u} (f : α → β) :
    Eq (Vec'.map f (Vec'.nil : Vec' α Nat.zero)) Vec'.nil := rfl
theorem Vec'.map_cons {α β : Type u} (f : α → β) (n : Nat) (a : α) (v : Vec' α n) :
    Eq (Vec'.map f (Vec'.cons n a v)) (Vec'.cons n (f a) (Vec'.map f v)) := rfl

noncomputable def Vec'.headD {α : Type u} {n : Nat} (d : α) (v : Vec' α n) : α :=
  Vec'.rec (motive := fun _ _ => α) d (fun _ a _ _ => a) v

theorem Vec'.headD_cons {α : Type u} (d : α) (n : Nat) (a : α) (v : Vec' α n) :
    Eq (Vec'.headD d (Vec'.cons n a v)) a := rfl

theorem Vec'.small {α : Type u} {n : Nat} (v : Vec' α n) (p : Prop) (hp : p) : p :=
  Vec'.rec (motive := fun _ _ => p) hp (fun _ _ _ ih => ih) v

theorem Vec'.small_cons {α : Type u} (n : Nat) (a : α) (v : Vec' α n) (p : Prop) (hp : p) :
    Eq (Vec'.small (Vec'.cons n a v) p hp) hp := rfl

inductive Tm (k : Nat) : Nat → Type where
  | var : Tm k k
  | app (n : Nat) (f : Tm k n) (a : Tm k (Nat.add n k)) : Tm k n

noncomputable def Tm.size {k n : Nat} (t : Tm k n) : Nat :=
  Tm.rec (motive := fun _ _ => Nat) (Nat.succ Nat.zero)
    (fun _ _ _ ihf iha => Nat.succ (Nat.add ihf iha)) t

theorem Tm.size_var (k : Nat) : Eq (Tm.size (Tm.var : Tm k k)) (Nat.succ Nat.zero) := rfl
theorem Tm.size_app (k n : Nat) (f : Tm k n) (a : Tm k (Nat.add n k)) :
    Eq (Tm.size (Tm.app n f a)) (Nat.succ (Nat.add (Tm.size f) (Tm.size a))) := rfl
