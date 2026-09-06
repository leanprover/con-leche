--#export Color.toNat_red Color.toNat_green Color.toNat_blue Color.next_blue Color.next_cycle Color.isRed_red

/- End-to-end test: the **direct sum** install (task #175 sum-types) on
   an enumeration — three constructors, no fields, `Type`.

   Regenerate with `_tmp/lean-inductive-models/scripts/export-fixture.sh`
   pointed at this directory and at `setlec-preprocess` (the widened
   predicate leaves the block unmodelled: not a single `_model`
   declaration in the stream).  Everything here goes through
   `checkDirectSum`: the type former with no capability, the three
   constructors, the recursor with three minor premises and three
   rules.  The consumers exercise iota on every constructor (`rfl`
   through `Color.rec` and `Color.casesOn`), Lean's own auxiliaries on
   the block (`casesOn`, the `match` compiler's output), and a
   `Bool`-valued elimination (the exported `Bool` block goes direct as
   well). -/

inductive Color : Type where
  | red | green | blue

def Color.toNat : Color → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

theorem Color.toNat_red : Eq (Color.toNat .red) 0 := rfl
theorem Color.toNat_green : Eq (Color.toNat .green) 1 := rfl
theorem Color.toNat_blue : Eq (Color.toNat .blue) 2 := rfl

noncomputable def Color.next : Color → Color :=
  Color.rec (motive := fun _ => Color) .green .blue .red

theorem Color.next_blue : Eq (Color.next .blue) .red := rfl

theorem Color.next_cycle (c : Color) : Eq (Color.next (Color.next (Color.next c))) c :=
  Color.casesOn (motive := fun c => Eq (Color.next (Color.next (Color.next c))) c) c rfl rfl rfl

noncomputable def Color.isRed (c : Color) : Bool :=
  Color.casesOn (motive := fun _ => Bool) c true false false

theorem Color.isRed_red : Eq (Color.isRed .red) true := rfl
