module

public import ConLeche.Frontend.Prepare

/- Proof code is private by default (CLAUDE.md): this module's `def`
bodies are the frontend's, and nothing here is unfolded elsewhere. -/
public section

/-!
# What `preparePrelude` does to the file's records (task #293)

The decoder emits the file's declaration records; `preparePrelude`
turns that list into the list the fold runs over
(`ConLeche/Frontend/Prepare.lean`).  The maintainer's ruling asked for
a spec simple enough to state in one line, and this is it:

    ∃ extra ⊆ prelude, (preparePrelude pre ds).Perm (ds ++ extra)

**every record of the file is in the prepared list, unchanged and
exactly once**, and what else is there is a prelude record the file did
not declare.  The two steps are both reorderings — the stream's own
prelude declarations are MOVED to the front rather than duplicated, and
the ground hoist moves a pinned operation's ground ahead of it — so
nothing is dropped, nothing is rewritten, and no verdict is decided
here.

The pass-through corollary `mem_preparePrelude` is what a statement
about the FILE composes with: a record the file declares is a record
the fold sees.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## Pulling the stream's own copy out -/

/-- The tail-recursive `pickGo` is `pickSpec`, with the accumulator in
front of the rest. -/
theorem pickGo_eq (n : Name) : ∀ (l : List Declaration) (acc : Array Declaration),
    pickGo n acc l = ((pickSpec n l).1, acc.toList ++ (pickSpec n l).2)
  | [], acc => by simp [pickGo, pickSpec]
  | d :: ds, acc => by
    simp only [pickGo, pickSpec]
    by_cases h : n ∈ d.names
    · simp [h]
    · simp only [h, if_false, List.contains_eq_mem, decide_false, Bool.false_eq_true]
      rw [pickGo_eq n ds (acc.push d)]
      simp

/-- What `pickSpec` removes and what it leaves is a permutation of what
it was given. -/
theorem pickSpec_perm (n : Name) : ∀ l : List Declaration,
    ((pickSpec n l).1.toList ++ (pickSpec n l).2).Perm l
  | [] => by simp [pickSpec]
  | d :: ds => by
    simp only [pickSpec]
    by_cases h : n ∈ d.names
    · simp [h]
    · simp only [h, if_false, List.contains_eq_mem, decide_false, Bool.false_eq_true]
      exact (List.perm_middle (a := d)
        (l₁ := (pickSpec n ds).1.toList) (l₂ := (pickSpec n ds).2)).trans
        ((pickSpec_perm n ds).cons d)

/-! ## The prelude's declarations, in front -/

/-- The implementation is its specification. -/
theorem frontOf_eq : ∀ (ps ds : List Declaration), frontOf ps ds = frontSpec ps ds
  | [], _ => rfl
  | p :: ps, ds => by
    simp only [frontOf, frontSpec, pickGo_eq, List.nil_append, frontOf_eq ps]

/-- **The front is the prelude's declarations, and what it took it took
from the stream.** -/
theorem frontSpec_perm : ∀ (ps ds : List Declaration),
    ∃ extra : List Declaration, (∀ d ∈ extra, d ∈ ps) ∧
      ((frontSpec ps ds).1 ++ (frontSpec ps ds).2).Perm (ds ++ extra)
  | [], ds => ⟨[], by simp, by simp [frontSpec]⟩
  | p :: ps, ds => by
    obtain ⟨extra, hextra, hperm⟩ := frontSpec_perm ps (pickSpec (preludeKey p) ds).2
    have hpick := pickSpec_perm (preludeKey p) ds
    simp only [frontSpec]
    cases hm : (pickSpec (preludeKey p) ds).1 with
    | some x =>
      refine ⟨extra, fun d hd => List.mem_cons_of_mem _ (hextra d hd), ?_⟩
      rw [hm] at hpick
      simp only [Option.getD_some, List.cons_append]
      refine (hperm.cons x).trans ?_
      have : (x :: ((pickSpec (preludeKey p) ds).2 ++ extra)) =
          (x :: (pickSpec (preludeKey p) ds).2) ++ extra := rfl
      rw [this]
      exact List.Perm.append_right extra (by simpa using hpick)
    | none =>
      refine ⟨p :: extra, ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hextra d hd')
      · rw [hm] at hpick
        simp only [Option.getD_none, List.cons_append]
        have hds : (pickSpec (preludeKey p) ds).2.Perm ds := by simpa using hpick
        exact ((hperm.cons p).trans ((hds.append_right extra).cons p)).trans
          List.perm_middle.symm

/-! ## The ground hoist -/

/-- The records of an array, read off by index, are the array. -/
theorem range_map_getElem! (a : Array Declaration) :
    (List.range a.size).map (fun k => a[k]!) = a.toList := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < a.size := by simpa using h₂
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    exact getElem!_pos a i hi

/-- **The reorder is a permutation.**  The sort is `List.mergeSort`
exactly so that this line exists (`List.mergeSort_perm`). -/
theorem applyHoist_perm (ds : Array Declaration) (target : Std.HashMap Nat Nat) :
    (applyHoist ds target).1.toList.Perm ds.toList := by
  simp only [applyHoist]
  rw [← range_map_getElem! ds]
  exact (List.mergeSort_perm _ _).map _

/-- **The hoist is a permutation**: it moves records, it never adds or
drops one. -/
theorem hoistNatOpGround_perm (ds : Array Declaration) :
    (hoistNatOpGround ds).1.toList.Perm ds.toList := by
  simp only [hoistNatOpGround]
  split
  · exact List.Perm.refl _
  · exact applyHoist_perm ds _

/-! ## The prepared list -/

/-- **THE SPEC** (maintainer, task #293): *"it is a permutation of the
input plus additional declarations, but nothing missing"* — and the
additional declarations are the built-in prelude's own records. -/
theorem preparePrelude_perm (pre : PreludeIx) (ds : List Declaration) :
    ∃ extra : List Declaration, (∀ d ∈ extra, d ∈ pre.decls.toList) ∧
      (preparePrelude pre ds).Perm (ds ++ extra) := by
  obtain ⟨extra, hextra, hperm⟩ := frontSpec_perm pre.decls.toList ds
  refine ⟨extra, hextra, ?_⟩
  simp only [preparePrelude, prepareD, frontOf_eq]
  refine (hoistNatOpGround_perm _).trans ?_
  simpa using hperm

/-- **The pass-through**: every record of the file is a record of the
fold's input, unchanged.  This is what a statement about the FILE
composes with. -/
theorem mem_preparePrelude {pre : PreludeIx} {ds : List Declaration}
    {pd : Declaration} (h : pd ∈ ds) : pd ∈ preparePrelude pre ds := by
  obtain ⟨extra, -, hperm⟩ := preparePrelude_perm pre ds
  exact hperm.mem_iff.mpr (List.mem_append_left _ h)

end ConLeche.Frontend
