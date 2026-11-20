--#export S.rec C.rec
/- Task #622: Lean's kernel builds a recursor's minor premises from its constructors' fields
   with `optParam`/`autoParam`/`outParam`/`semiOutParam` consumed (`consume_type_annotations`),
   and its parameters from the inductive's, consumed the same way.  `S.rec`'s minor premise reads
   `(x : Nat) → (h : x = x) → motive ⟨x, h⟩` while `S.mk`'s fields are `optParam Nat 0` and
   `autoParam (x = x) _`; `C.rec`'s parameter `β` is `Type` while `C`'s is `outParam Type`.  The
   checker reads the ι equations off the recursors' own types and accepts them: the annotations
   are stored as the identity (exit 0).  `iota_read_field_differs` is this stream with `S.rec`'s
   first field domain made `(fun α : Type => α) Nat` (definitionally `Nat`, so Lean accepts it): rejected (1),
   its minor premise no longer states `S.mk`'s field.  Built by scripts/mk_iota_read_fixtures.sh. -/
structure S where
  x : Nat := 0
  h : x = x := by rfl

class C (α : Type) (β : outParam Type) where
  f : α → β
