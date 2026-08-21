/- End-to-end test: the two standard axioms.

   `iffToEq` uses `propext` directly; `pickNat` forces
   `Classical.choice` (instantiated at `Nat`, universe 1); `pickProp`
   instantiates it at a `Prop` (universe 0), exercising the
   level-polymorphic model value on both sides of the `u = 0` split. -/

--#export iffToEq pickNat pickProp

theorem iffToEq (p q : Prop) (h : Iff p q) : Eq p q := propext h

noncomputable def pickNat (h : Nonempty Nat) : Nat := Classical.choice h

noncomputable def pickProp (p : Prop) (h : Nonempty p) : p :=
  Classical.choice h
