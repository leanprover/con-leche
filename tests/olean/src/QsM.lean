module
prelude
-- Guards task #501: QsA's and QsB's `Quot.sound` meet (Lean merges the two axioms); QsB's
-- theorem, read into the context, reads QsB's copy, a proof pair with the context's (QsA's).
public import QsA
public import QsB
public section
universe u
theorem qsM {α : Sort u} {r : α → α → Prop} {a b : α} (h : r a b) : Eq (Quot.mk r a) (Quot.mk r b) :=
  qsB h
end
