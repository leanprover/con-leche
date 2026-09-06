--#export PEmpty'.elim Void.elim Void.elim_eq Bottom.elim Nada.elim absurd'

/- End-to-end test: **zero-constructor inductives at every level**
   (task #181).  Every block here has no constructors and is installed
   by the direct sum route at `n = 0` (task #175: the tagged union of
   zero towers, the empty set at every parameter instance), with the
   LARGE eliminator the official kernel grants a zero-constructor
   inductive whatever its sort:

   * `PEmpty'` — universe-polymorphic, `PEmpty`'s twin (`Sort u`, so
     it may be `Prop`; still eliminates into every `Sort v`);
   * `Void α n` — with a type parameter and a `Nat` parameter, in
     `Type u`;
   * `Bottom p` — a `Prop` with a `Prop` parameter;
   * `Nada` — in `Type`;

   and `absurd'` goes through the toolchain's `False`, which the
   checker installs as a pinned basis block (`Setlec/Kernel/Basis/
   False.lean`), so the stream's raw `False` block is matched against
   the pin rather than installed by the sum route.

   Its two bad twins are derived from this stream by `scripts/
   mk_zero_ctor_bad.py`: `zero_ctor_false_proof.ndjson` appends a
   theorem claiming `False` with an ill-typed value (REJECT), and
   `zero_ctor_bad_rec.ndjson` replaces `Nada.rec`'s type by `Type`
   (a recognised zero-constructor block whose recursor is not the
   generated one: REJECT). -/

universe u v

inductive PEmpty' : Sort u where

def PEmpty'.elim {α : Sort v} (h : PEmpty'.{u}) : α :=
  PEmpty'.rec (motive := fun _ => α) h

inductive Void (α : Type u) (n : Nat) : Type u where

def Void.elim {α : Type u} {β : Sort v} (x : Void α 3) : β :=
  Void.rec (motive := fun _ => β) x

theorem Void.elim_eq {α : Type u} (x : Void α 3) :
    Eq (Void.elim x : Nat) (Void.elim x) := rfl

inductive Bottom (p : Prop) : Prop where

theorem Bottom.elim {p q : Prop} (h : Bottom p) : q :=
  Bottom.rec (motive := fun _ => q) h

inductive Nada : Type where

def Nada.elim {α : Sort u} (x : Nada) : α :=
  Nada.rec (motive := fun _ => α) x

theorem absurd' {p : Prop} (h : False) : p := False.elim h
