/- Task #480: a `Prop` structure is structure-like, as official's
   `is_non_rec_structure` has it: `IndCaps.eta` no longer asks for a sort.  A
   proof against its constructor application takes the same route as before,
   proof irrelevance first.  `And` keeps its own rescue (`and_rec_opaque`).

   official: 0 (Lean elaborated this).  con-leche: 0. -/

--#export etaProof

structure P (A : Prop) : Prop where
  x : A

theorem etaProof (A : Prop) (h : P A) : h = P.mk h.x := rfl
