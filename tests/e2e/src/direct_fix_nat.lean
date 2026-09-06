--#export Nat'.add_zero Nat'.add_succ Nat'.pred_succ Nat'.pred_zero Nat'.small_succ List'.length_nil List'.length_cons List'.append_cons List'.append_nil List'.map_cons

/- End-to-end test (task #188): RECURSIVE inductive types through the
   direct fixed-point install — `Nat'` (a `Nat` clone: one nullary and
   one recursive constructor) and the universe-polymorphic `List' α`
   (a parameter, a data field before the recursive one).  Both get the
   LARGE eliminator (their sort is provably nonzero); every consumer
   fires iota on a recursive constructor and reads the inductive
   hypothesis (`add`, `length`, `append`, `map`), on a nullary one
   (`add_zero`, `length_nil`, `append_nil`), drops the hypothesis
   (`pred`), and eliminates into `Prop` (`small`). -/

universe u v

inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'

noncomputable def Nat'.add (a b : Nat') : Nat' :=
  Nat'.rec (motive := fun _ => Nat') a (fun _ ih => Nat'.succ ih) b

theorem Nat'.add_zero (a : Nat') : Eq (Nat'.add a Nat'.zero) a := rfl
theorem Nat'.add_succ (a b : Nat') :
    Eq (Nat'.add a (Nat'.succ b)) (Nat'.succ (Nat'.add a b)) := rfl

noncomputable def Nat'.pred (a : Nat') : Nat' :=
  Nat'.rec (motive := fun _ => Nat') Nat'.zero (fun n _ => n) a

theorem Nat'.pred_succ (a : Nat') : Eq (Nat'.pred (Nat'.succ a)) a := rfl
theorem Nat'.pred_zero : Eq (Nat'.pred Nat'.zero) Nat'.zero := rfl

theorem Nat'.small (n : Nat') (p : Prop) (hp : p) : p :=
  Nat'.rec (motive := fun _ => p) hp (fun _ ih => ih) n

theorem Nat'.small_succ (n : Nat') (p : Prop) (hp : p) :
    Eq (Nat'.small (Nat'.succ n) p hp) (Nat'.small n p hp) := rfl

inductive List' (α : Type u) : Type u where
  | nil : List' α
  | cons (head : α) (tail : List' α) : List' α

noncomputable def List'.length {α : Type u} (l : List' α) : Nat' :=
  List'.rec (motive := fun _ => Nat') Nat'.zero (fun _ _ ih => Nat'.succ ih) l

theorem List'.length_nil {α : Type u} : Eq (List'.length (List'.nil : List' α)) Nat'.zero := rfl
theorem List'.length_cons {α : Type u} (a : α) (l : List' α) :
    Eq (List'.length (List'.cons a l)) (Nat'.succ (List'.length l)) := rfl

noncomputable def List'.append {α : Type u} (l m : List' α) : List' α :=
  List'.rec (motive := fun _ => List' α) m (fun a _ ih => List'.cons a ih) l

theorem List'.append_cons {α : Type u} (a : α) (l m : List' α) :
    Eq (List'.append (List'.cons a l) m) (List'.cons a (List'.append l m)) := rfl
theorem List'.append_nil {α : Type u} (m : List' α) : Eq (List'.append List'.nil m) m := rfl

noncomputable def List'.map {α : Type u} {β : Type v} (f : α → β) (l : List' α) : List' β :=
  List'.rec (motive := fun _ => List' β) List'.nil (fun a _ ih => List'.cons (f a) ih) l

theorem List'.map_cons {α : Type u} {β : Type v} (f : α → β) (a : α) (l : List' α) :
    Eq (List'.map f (List'.cons a l)) (List'.cons (f a) (List'.map f l)) := rfl
