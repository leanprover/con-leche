module

public import ConLeche.Frontend.ExportC

public section

/-!
# The parse result keeps every record (task #290)

`ParseResultD.ofState` is the built-in prelude's records followed by
the stream's, the latter reordered by the ground hoist
(`hoistNatOpGround`, `ConLeche/Frontend/NatOpGround.lean`) — a
permutation of the positions under a total order, sorted by
`Array.mergeSort`, so every record survives it.  That is all the file
theorem needs of the result: a record the parse pushed is in the
result's list.
-/

namespace ConLeche.Frontend

open ConLeche.Cached (DeclC)

/-- The hoist is a permutation: every record is still there. -/
theorem mem_hoistNatOpGround {ds : Array DeclC} {d : DeclC} (h : d ∈ ds) :
    d ∈ (hoistNatOpGround ds).1 := by
  unfold hoistNatOpGround
  dsimp only
  split
  · exact h
  · obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem h
    rw [Array.mem_map]
    refine ⟨k, ?_, ?_⟩
    · rw [Array.mem_mergeSort, Array.mem_range]; exact hk
    · exact getElem!_pos ds k hk

/-- A record the parse pushed is in the result. -/
theorem mem_ofState_decls {st : StateD} {d : DeclC} (h : d ∈ st.decls) :
    d ∈ (ParseResultD.ofState st).decls := by
  unfold ParseResultD.ofState
  simp only
  exact Array.mem_append.mpr (.inr (mem_hoistNatOpGround h))

/-- A prelude record is in the result. -/
theorem mem_ofState_prelude {st : StateD} {d : DeclC} (h : d ∈ st.prelude.decls) :
    d ∈ (ParseResultD.ofState st).decls := by
  unfold ParseResultD.ofState
  simp only
  exact Array.mem_append.mpr (.inl h)

theorem ofState_taintSkipped (st : StateD) :
    (ParseResultD.ofState st).taintSkipped = st.taintSkipped := rfl

end ConLeche.Frontend
