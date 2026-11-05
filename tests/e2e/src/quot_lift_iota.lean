--#export quotLiftIota quotIndIota

/- `Quot.lift`'s and `Quot.ind`'s reduction at a universe-polymorphic `α`,
   where the family may be `Prop`: the ι step compares the constructor's level
   with the rule's comparand.  `scripts/mk_basis_names_fixtures.py` derives the
   same stream with each quotient record at its own level-parameter names. -/

universe u v

theorem quotLiftIota {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
    (h : ∀ a b, r a b → f a = f b) (a : α) : Quot.lift f h (Quot.mk r a) = f a := rfl

theorem quotIndIota {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop}
    (mk : ∀ a, β (Quot.mk r a)) (a : α) : Quot.ind mk (Quot.mk r a) = mk a := rfl
