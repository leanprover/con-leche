--#export Vec'.first_nil Vec'.first_one Vec'.first_two Vec'.copy_two Vec'.copy_nil Par.toNat_odd Par.flip_even Vec'.small_two Vec'.small_nil

/- End-to-end test (task #175 indexed): `Type`-valued INDEXED families
   with several constructors through the direct install — the
   `Vector`-like non-recursive `Vec'` (three constructors at three
   index values, a universe-polymorphic parameter) and the
   two-constructor `Par : Nat → Type`.  Both get the LARGE eliminator
   (their sort is provably nonzero).  The consumers fire iota on every
   constructor, with a constant motive (`first`), with a motive that
   reads the index (`copy : Vec' α n`, `flip : Par (…)`) and — the small
   eliminator on a `Type` family — into `Prop` (`small`). -/

universe u

inductive Vec' (α : Type u) : Nat → Type u where
  | nil : Vec' α Nat.zero
  | one (a : α) : Vec' α (Nat.succ Nat.zero)
  | two (a b : α) : Vec' α (Nat.succ (Nat.succ Nat.zero))

noncomputable def Vec'.first {α : Type u} {n : Nat} (d : α) (v : Vec' α n) : α :=
  Vec'.rec (motive := fun _ _ => α) d (fun a => a) (fun a _ => a) v

theorem Vec'.first_nil {α : Type u} (d : α) : Eq (Vec'.first d (Vec'.nil : Vec' α Nat.zero)) d :=
  rfl
theorem Vec'.first_one {α : Type u} (d a : α) : Eq (Vec'.first d (Vec'.one a)) a := rfl
theorem Vec'.first_two {α : Type u} (d a b : α) : Eq (Vec'.first d (Vec'.two a b)) a := rfl

noncomputable def Vec'.copy {α : Type u} {n : Nat} (v : Vec' α n) : Vec' α n :=
  Vec'.rec (motive := fun n _ => Vec' α n) Vec'.nil (fun a => Vec'.one a) (fun a b => Vec'.two b a) v

theorem Vec'.copy_two {α : Type u} (a b : α) : Eq (Vec'.copy (Vec'.two a b)) (Vec'.two b a) := rfl
theorem Vec'.copy_nil {α : Type u} : Eq (Vec'.copy (Vec'.nil : Vec' α Nat.zero)) Vec'.nil := rfl

theorem Vec'.small {α : Type u} {n : Nat} (v : Vec' α n) (p : Prop) (hp : p) : p :=
  Vec'.rec (motive := fun _ _ => p) hp (fun _ => hp) (fun _ _ => hp) v

theorem Vec'.small_two {α : Type u} (a b : α) (p : Prop) (hp : p) :
    Eq (Vec'.small (Vec'.two a b) p hp) hp := rfl
theorem Vec'.small_nil {α : Type u} (p : Prop) (hp : p) :
    Eq (Vec'.small (Vec'.nil : Vec' α Nat.zero) p hp) hp := rfl

inductive Par : Nat → Type where
  | even : Par Nat.zero
  | odd : Par (Nat.succ Nat.zero)

noncomputable def Par.toNat {n : Nat} (p : Par n) : Nat :=
  Par.rec (motive := fun _ _ => Nat) Nat.zero (Nat.succ Nat.zero) p

theorem Par.toNat_odd : Eq (Par.toNat Par.odd) (Nat.succ Nat.zero) := rfl

noncomputable def Par.flip {n : Nat} (p : Par n) : Par (Par.toNat p) :=
  Par.rec (motive := fun _ p => Par (Par.toNat p)) Par.even Par.odd p

theorem Par.flip_even : Eq (Par.flip Par.even) Par.even := rfl
