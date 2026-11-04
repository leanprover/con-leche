module

public import ConLeche.Frontend.Olean.View
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Prefix

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

/-- The check of a view against the start of `M.olean`. -/
def viewChk (pre : Option (Array ImportRec)) (d : ModDecoded) : Option ModDecoded :=
  if (pre == some d.imports) = true then some d else none

theorem decodeModuleSpec_at {f : ModFiles} {level : OLeanLevel} {r : Region} {a : UInt64}
    (h : f.viewRegion level = some (r, a)) :
    decodeModuleSpec f level = decodeAt r a >>= viewChk (importsPre f.exported.bytes) := by
  simp only [decodeModuleSpec, h]
  show (decodeAt r a >>= _) = _
  cases decodeAt r a with
  | none => rfl
  | some d =>
    show (if _ then _ else _) = viewChk _ d
    simp only [viewChk]
    split <;> rfl

theorem decodeModuleSpec_none {f : ModFiles} {level : OLeanLevel} (h : f.viewRegion level = none) :
    decodeModuleSpec f level = none := by
  simp only [decodeModuleSpec, h]
  rfl

theorem parseAllViews_parts {ex s p : Part} (hm : ModFiles.isModule ⟨ex, some s, some p⟩ = true) :
    parseAllViews ⟨ex, some s, some p⟩ =
      if ((Region.single ex).loc ex.moduleDataAddr).isSome = true then
        match Region.ofParts #[ex, s] with
        | .error _ => none
        | .ok r2 =>
          if (r2.loc s.moduleDataAddr).isSome = true then
            match Region.ofParts #[ex, s, p] with
            | .error _ => none
            | .ok r =>
              match parseMany r [ex.moduleDataAddr, s.moduleDataAddr, p.moduleDataAddr] with
              | some [de, ds, dp] =>
                if (importsPre ex.bytes == some de.imports && importsPre ex.bytes == some ds.imports &&
                    importsPre ex.bytes == some dp.imports) = true then some ⟨de, ds, dp⟩ else none
              | _ => none
          else none
      else none := by
  by_cases L1 : ((Region.single ex).loc ex.moduleDataAddr).isSome = true
  · cases hr2 : Region.ofParts #[ex, s] with
    | error e => simp [parseAllViews, hm, L1, hr2, Except.toOption]
    | ok r2 =>
      by_cases L2 : (r2.loc s.moduleDataAddr).isSome = true
      · cases hr3 : Region.ofParts #[ex, s, p] with
        | error e => simp [parseAllViews, hm, L1, hr2, L2, hr3, Except.toOption]
        | ok r =>
          simp only [parseAllViews, hm, L1, ↓reduceIte, bind, Option.bind, hr2, L2, hr3,
            Except.toOption]
          rfl
      · simp [parseAllViews, hm, L1, hr2, L2, Except.toOption]
  · simp [parseAllViews, hm, L1]

/-- **All three views, with one memo, are the three specifications**, on every
input. -/
theorem parseAllViews_eq (f : ModFiles) :
    parseAllViews f = (do
      let e ← decodeModuleSpec f .exported
      let s ← decodeModuleSpec f .server
      let p ← decodeModuleSpec f .private
      pure ⟨e, s, p⟩) := by
  cases hm : f.isModule with
  | false =>
    have hS : decodeModuleSpec f .server = decodeModuleSpec f .exported := by
      simp [decodeModuleSpec, ModFiles.viewRegion, hm]
    have hP : decodeModuleSpec f .private = decodeModuleSpec f .exported := by
      simp [decodeModuleSpec, ModFiles.viewRegion, hm]
    simp only [parseAllViews, hm, Bool.false_eq_true, ↓reduceIte, parseView_eq_spec, hS, hP]
    cases decodeModuleSpec f .exported <;> rfl
  | true =>
    cases hs : f.server with
    | none =>
      have hS : decodeModuleSpec f .server = none := by
        simp [decodeModuleSpec, ModFiles.viewRegion, hm, hs]
      simp only [parseAllViews, hm, ↓reduceIte, hs, hS]
      cases decodeModuleSpec f .exported <;> rfl
    | some s =>
      cases hp : f.private with
      | none =>
        have hP : decodeModuleSpec f .private = none := by
          simp [decodeModuleSpec, ModFiles.viewRegion, hm, hs, hp]
        simp only [parseAllViews, hm, ↓reduceIte, hs, hp, hP]
        cases decodeModuleSpec f .exported <;> cases decodeModuleSpec f .server <;> rfl
      | some p =>
        obtain ⟨ex, s', p'⟩ := f
        simp only at hs hp
        subst hs hp
        rw [parseAllViews_parts (by simpa using hm)]
        have hEv : ModFiles.viewRegion ⟨ex, some s, some p⟩ .exported =
            some (Region.single ex, ex.moduleDataAddr) := rfl
        rw [decodeModuleSpec_at hEv]
        by_cases L1 : ((Region.single ex).loc ex.moduleDataAddr).isSome = true
        · simp only [L1, ↓reduceIte]
          obtain ⟨g1, hg1⟩ := Option.isSome_iff_exists.mp L1
          cases hr2 : Region.ofParts #[ex, s] with
          | error e =>
            have hSv : ModFiles.viewRegion ⟨ex, some s, some p⟩ .server = none := by
              simp [ModFiles.viewRegion, hm, hr2, Except.toOption]
            rw [decodeModuleSpec_none hSv]
            cases decodeAt (Region.single ex) ex.moduleDataAddr <;> simp [viewChk]
          | ok r2 =>
            obtain ⟨hR2, ho1⟩ := ofParts_two hr2
            have hSv : ModFiles.viewRegion ⟨ex, some s, some p⟩ .server =
                some (r2, s.moduleDataAddr) := by
              simp [ModFiles.viewRegion, hm, hr2, Except.toOption, bind, Option.bind, pure]
            rw [decodeModuleSpec_at hSv]
            have hs12 : Region.Sub (Region.single ex) r2 ex.bytes.size := by
              rw [hR2]
              exact Region.Sub.single_two ex s ho1
            simp only
            by_cases L2 : (r2.loc s.moduleDataAddr).isSome = true
            · obtain ⟨g2, hg2⟩ := Option.isSome_iff_exists.mp L2
              simp only [L2, ↓reduceIte]
              cases hr3 : Region.ofParts #[ex, s, p] with
              | error e =>
                have hPv : ModFiles.viewRegion ⟨ex, some s, some p⟩ .private = none := by
                  simp [ModFiles.viewRegion, hm, hr3, Except.toOption, bind, Option.bind]
                rw [decodeModuleSpec_none hPv]
                cases decodeAt (Region.single ex) ex.moduleDataAddr <;>
                  cases decodeAt r2 s.moduleDataAddr <;> simp [viewChk]
                all_goals (split <;> simp [*])
              | ok r3 =>
                obtain ⟨hR3, -, ho2⟩ := ofParts_three hr3
                have hPv : ModFiles.viewRegion ⟨ex, some s, some p⟩ .private =
                    some (r3, p.moduleDataAddr) := by
                  simp [ModFiles.viewRegion, hm, hr3, Except.toOption, bind, Option.bind, pure]
                rw [decodeModuleSpec_at hPv]
                have hs23 : Region.Sub r2 r3 (ex.bytes ++ s.bytes).size := by
                  rw [hR2, hR3]
                  exact Region.Sub.two_three ex s p ho1 ho2
                have hs13 : Region.Sub (Region.single ex) r3 ex.bytes.size :=
                  Region.Sub.trans hs12 hs23 (by simp)
                simp only [parseMany_eq, List.mapM_cons, List.mapM_nil,
                  hs13.decodeAt_sub hg1, hs23.decodeAt_sub hg2]
                cases decodeAt (Region.single ex) ex.moduleDataAddr <;>
                  cases decodeAt r2 s.moduleDataAddr <;>
                  cases decodeAt r3 p.moduleDataAddr
                all_goals simp only [viewChk, bind, Option.bind, pure]
                all_goals (repeat' split)
                all_goals simp_all
            · have hn : r2.loc s.moduleDataAddr = none := by simpa using L2
              simp only [L2, Bool.false_eq_true, ↓reduceIte, decodeAt_of_loc hn]
              cases decodeAt (Region.single ex) ex.moduleDataAddr <;> simp [viewChk]
              all_goals (split <;> simp [*])
        · have hn : (Region.single ex).loc ex.moduleDataAddr = none := by simpa using L1
          simp only [L1, Bool.false_eq_true, ↓reduceIte, decodeAt_of_loc hn]
          rfl

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
