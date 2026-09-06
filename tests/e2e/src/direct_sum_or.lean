--#export Or'.elim Or'.symm Or'.resolve_left Absurd.elim Nil.elim Nil.elim_eq

/- End-to-end test: the **direct sum** install (task #175 sum-types) on
   the propositional and the empty shapes.

   `Or'` is a two-constructor `Prop` inductive: the official kernel
   gives it the SMALL eliminator only (`elim_only_at_universe_zero`:
   more than one constructor, result sort not provably nonzero), and
   the direct sum install stores that recursor at the block's own
   level parameters; `Or'.elim`/`Or'.symm` eliminate into `Prop`
   through both rules.  `Absurd` is a zero-constructor `Prop` (a `False`
   twin) whose recursor is LARGE — admissible with no constructor — and
   `Nil` a zero-constructor `Type`; both eliminate vacuously.

   The bad twin `direct_sum_or_large_bad.ndjson` is this stream with
   `Or'.rec`'s motive patched to `Sort u` (a large eliminator on a
   two-constructor `Prop` inductive), which the install must reject as
   the official kernel does. -/

universe u

inductive Or' (a b : Prop) : Prop where
  | inl (h : a) : Or' a b
  | inr (h : b) : Or' a b

theorem Or'.elim {a b c : Prop} (h : Or' a b) (l : a → c) (r : b → c) : c :=
  Or'.rec l r h

theorem Or'.symm {a b : Prop} (h : Or' a b) : Or' b a :=
  Or'.rec (motive := fun _ => Or' b a) (fun ha => Or'.inr ha) (fun hb => Or'.inl hb) h

theorem Or'.resolve_left {a b : Prop} (h : Or' a b) (na : Not a) : b :=
  Or'.elim h (fun ha => absurd ha na) (fun hb => hb)

inductive Absurd : Prop where

theorem Absurd.elim {p : Prop} (h : Absurd) : p :=
  Absurd.rec (motive := fun _ => p) h

inductive Nil : Type where

noncomputable def Nil.elim {α : Sort u} (v : Nil) : α :=
  Nil.rec (motive := fun _ => α) v

theorem Nil.elim_eq (v : Nil) : Eq (Nil.elim v : Nat) (Nil.elim v) := rfl
