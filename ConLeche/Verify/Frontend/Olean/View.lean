module

public import ConLeche.Frontend.Olean.Module
public import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv

/-!
# A module's views: the fast reads are the specification

`parseView_eq_spec`: one view, fast, is the specification, on every input.
`parseAllViews_eq`: all three, with one memo, are the three specifications, each
in the region of the files up to its view, so an importer holding `M.olean` alone
reads what the home read.

Where a view parses, the reads of a part of it succeed, and return that:
`readNamePositions_of_view`, `readEntry_of_view`, `readStmts_of_view`.
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

/-- **One view, fast, is the specification**, on every input. -/
theorem parseView_eq_spec (f : ModFiles) (level : OLeanLevel) :
    parseView f level = decodeModuleSpec f level := by
  simp only [parseView, decodeModuleSpec, parseAt_eq_spec]

/-- **All three views, with one memo, are the three specifications**, on every
input. -/
theorem parseAllViews_eq (f : ModFiles) :
    parseAllViews f = (do
      let e ← decodeModuleSpec f .exported
      let s ← decodeModuleSpec f .server
      let p ← decodeModuleSpec f .private
      pure ⟨e, s, p⟩) := by
  sorry

/-- The parts of a view. -/
theorem parseView_some {f : ModFiles} {level : OLeanLevel} {d : ModDecoded}
    (h : parseView f level = some d) :
    ∃ r a, f.viewRegion level = some (r, a) ∧ parseAt r a = some d ∧
      importsPre f.exported.bytes = some d.imports := by
  simp only [parseView] at h
  obtain ⟨⟨r, a⟩, hv, h⟩ := bind_some_left h
  obtain ⟨d', hd, h⟩ := bind_some_left h
  by_cases hi : (importsPre f.exported.bytes == some d'.imports) = true
  · simp only [hi, ite_true] at h
    replace h : some d' = some d := h
    cases h
    exact ⟨r, a, hv, hd, eq_of_beq hi⟩
  · simp [hi] at h

/-- **The name positions of a parsed view**: per constant the full parse holds, its
position, name, kind and filter; and the view's header. -/
theorem readNamePositions_of_view {f : ModFiles} {level : OLeanLevel} {d : ModDecoded}
    (h : parseView f level = some d) :
    ∃ ps, readNamePositions f level = some ps ∧ ps.header = ⟨d.isModule, d.imports⟩ ∧
      ps.consts.toList.map (·.name) = d.constants.toList.map (·.name) ∧
      ps.consts.toList.map (·.tag) = d.constants.toList.map (·.kind.tag) ∧
      ps.consts.toList.map (·.skipped) = d.constants.toList.map (·.kind.skipped) := by
  obtain ⟨r, a, hv, hp, -⟩ := parseView_some h
  obtain ⟨-, sk, hs, -, hc, -⟩ := parseAt_some hp
  have hlen : sk.consts.length = d.constants.toList.length := (mapM_length_opt hc).symm
  refine ⟨⟨⟨d.isModule, d.imports⟩,
      ((sk.consts.zip d.constants.toList).map fun p => NamePosition.ofEntry p.1 p.2).toArray⟩,
    ?_, rfl, ?_, ?_, ?_⟩
  · simp only [readNamePositions, hv, bind, Option.bind]
    exact namePositionsAt_of_full hp hs
  · simpa using namePositions_names hlen
  · simpa using namePositions_tags hlen
  · simpa using namePositions_skipped hlen

/-- **The constant at a position of a parsed view** is the full parse's constant
there. -/
theorem readEntry_of_view {f : ModFiles} {level : OLeanLevel} {d : ModDecoded} {ps : NamePositions}
    {i : Nat} {q : NamePosition} (h : parseView f level = some d)
    (hp : readNamePositions f level = some ps) (hq : ps.consts[i]? = some q) :
    readEntry f level q.loc = d.constants[i]? := by
  obtain ⟨r, a, hv, hf, -⟩ := parseView_some h
  obtain ⟨-, sk, hs, -, hc, -⟩ := parseAt_some hf
  simp only [readNamePositions, hv, bind, Option.bind, namePositionsAt_of_full hf hs,
    Option.some.injEq] at hp
  subst hp
  simp only [readEntry, hv, bind, Option.bind]
  have hlen : sk.consts.length = d.constants.toList.length := (mapM_length_opt hc).symm
  simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_zip_eq_some,
    Option.map_eq_some_iff] at hq
  obtain ⟨⟨c, e⟩, ⟨hc1, hc2⟩, rfl⟩ := hq
  exact entryAt_of_full hf hs hc1

/-- **The statements of any of a parsed view's constants**, at positions its name
positions hold. -/
theorem readStmts_of_view {f : ModFiles} {level : OLeanLevel} {d : ModDecoded} {ps : NamePositions}
    {cs : List Nat} (h : parseView f level = some d)
    (hp : readNamePositions f level = some ps) (hc : ∀ c ∈ cs, ∃ q ∈ ps.consts, q.loc = c) :
    ∃ es, cs.mapM (readEntry f level) = some es ∧
      readStmts f level cs = some (es.map CEntryF.stmt) ∧ ∀ e ∈ es, e ∈ d.constants := by
  obtain ⟨r, a, hv, hf, -⟩ := parseView_some h
  obtain ⟨-, sk, hs, -, hcs, -⟩ := parseAt_some hf
  simp only [readNamePositions, hv, bind, Option.bind, namePositionsAt_of_full hf hs,
    Option.some.injEq] at hp
  subst hp
  have hsub : ∀ c ∈ cs, c ∈ sk.consts := by
    intro c hm
    obtain ⟨q, hq, rfl⟩ := hc c hm
    simp only [List.mem_toArray, List.mem_map] at hq
    obtain ⟨⟨c', e⟩, hz, rfl⟩ := hq
    exact (List.of_mem_zip hz).1
  obtain ⟨es, h1, h2, h3⟩ := stmtsAt_of_full hf hs hsub
  have hre : readEntry f level = entryAt r := by
    funext c
    simp only [readEntry, hv, bind, Option.bind]
  refine ⟨es, ?_, ?_, h3⟩
  · rw [hre]; exact h1
  · simpa only [readStmts, hv, bind, Option.bind] using h2

end ConLeche.Frontend.Olean
