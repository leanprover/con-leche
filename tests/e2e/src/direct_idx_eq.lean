--#export MyEq.subst MyEq.symm MyEq.trans MyEq.cast MyEq.iota MyEq.k_use MyEq.mp

/- End-to-end test (task #175 indexed): an `Eq`-clone through the
   direct INDEXED install — a `Prop` family with one constructor, no
   fields and one index.  Official gives it the LARGE eliminator
   (`elim_only_at_universe_zero`: one constructor whose every field is
   a proposition — there is none) and the K flag (`is_K_target`: `Prop`,
   one constructor, no fields), and so does the direct route: `MyEq.cast`
   eliminates into `Sort u`, `MyEq.iota` fires the rule on `MyEq.refl`,
   and `MyEq.k_use` reduces the recursor on a *neutral* major through
   the K rescue (`to_cnstr_when_K`).  The block is the pinned basis
   `Eq` block's shape at a fresh name. -/

universe u v

inductive MyEq {α : Sort u} (a : α) : α → Prop where
  | refl : MyEq a a

theorem MyEq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h : MyEq a b)
    (m : motive a) : motive b :=
  MyEq.rec (motive := fun x _ => motive x) m h

theorem MyEq.symm {α : Sort u} {a b : α} (h : MyEq a b) : MyEq b a :=
  MyEq.rec (motive := fun x _ => MyEq x a) MyEq.refl h

theorem MyEq.trans {α : Sort u} {a b c : α} (h₁ : MyEq a b) (h₂ : MyEq b c) : MyEq a c :=
  MyEq.rec (motive := fun x _ => MyEq a x) h₁ h₂

theorem MyEq.mp {p q : Prop} (h : MyEq p q) (hp : p) : q :=
  MyEq.rec (motive := fun x _ => x) hp h

noncomputable def MyEq.cast {α β : Sort v} (h : MyEq α β) (a : α) : β :=
  MyEq.rec (motive := fun x _ => x) a h

theorem MyEq.iota (a : Nat) :
    MyEq (MyEq.rec (motive := fun _ _ => Nat) Nat.zero (MyEq.refl (a := a))) Nat.zero :=
  MyEq.refl

theorem MyEq.k_use (n : Nat) (h : MyEq n n) :
    MyEq (MyEq.rec (motive := fun _ _ => Nat) Nat.zero h) Nat.zero :=
  MyEq.refl
