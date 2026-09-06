--#export Wrap.fst_mk Wrap.snd_mk Wrap.elim_mk Wrap.unit_eq

/- End-to-end test: the **direct** simple-structure install (task #82),
   exercised with NO preprocessor available.

   This fixture is committed as a *raw* lean4export result (regenerate
   with `LEAN_INDUCTIVE_MODELS_FILTER=0`), and `tests/arena.sh` runs it
   with `LECH_INDUCTIVE_MODELS=/nonexistent` (the `raw` marker in
   `tests/e2e-expected.txt`), so there is not a single `_model`
   declaration in the stream and not a single one produced at run time.
   Everything here is checked through `checkDirectStruct`.

   `Wrap` is the general shape of the class: two parameters, two
   *dependent* fields (`snd`'s type mentions `fst`), result sort
   `Sort (max (u+1) (v+1))` — provably nonzero, so the class applies.
   Its uses cover the three things the direct install has to get right:

   * the generated projection functions (`Wrap.fst`/`Wrap.snd`, the
     latter *dependently* typed, which is exactly what the Prop-style
     recursor-elimination fallback cannot express) and their iota rules
     — `fst_mk`/`snd_mk` are `rfl`s through those rules;
   * the recursor and its single rule — `elim_mk` is a `rfl` through
     `Wrap.rec`;
   * a field-free structure (`Unit'`), whose model is the singleton.
-/

universe u v

structure Wrap (α : Type u) (β : α → Type v) where
  fst : α
  snd : β fst

structure Unit' : Type where

def Wrap.mk2 {α : Type u} {β : α → Type v} (a : α) (b : β a) : Wrap α β :=
  Wrap.mk a b

theorem Wrap.fst_mk {α : Type u} {β : α → Type v} (a : α) (b : β a) :
    Eq (Wrap.mk2 a b).fst a :=
  rfl

theorem Wrap.snd_mk {α : Type u} {β : α → Type v} (a : α) (b : β a) :
    Eq (Wrap.mk2 a b).snd b :=
  rfl

noncomputable def Wrap.elim {α : Type u} {β : α → Type v} (w : Wrap α β) : α :=
  Wrap.rec (motive := fun _ => α) (fun a _ => a) w

theorem Wrap.elim_mk {α : Type u} {β : α → Type v} (a : α) (b : β a) :
    Eq (Wrap.elim (Wrap.mk2 a b)) a :=
  rfl

theorem Wrap.unit_eq : Eq (Unit'.rec (motive := fun _ => Unit') Unit'.mk Unit'.mk) Unit'.mk :=
  rfl
