module

public import ConLeche.Frontend.Olean.Lazy
public import ConLeche.Verify.Frontend.Olean.Sparse
public import ConLeche.Verify.Frontend.Olean.Build
import ConLeche.Verify.Frontend.Olean.Engine
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Reads

public section

/-!
# A module's load is its specification, up to its theorems' values (task #481)

`loadAt_spec`: where the load of a module's private view succeeds, its constants are the
skeletons' (`lazyEntry`, at the specification's reads `nameP`, `exprP`), and its frontier
holds only the specification's values (`Frontier.Good`), which is all a read over it asks
(`frontierExpr_eq`).

`lazyEntry_of_spec` relates `lazyEntry` to the specification's constant: all its fields
agree except a theorem's value, which is a reference to the location the skeleton's
pointer stands for, where the specification reads the value (`lazy_thm_value`).

Nothing here is about what the walks return: what a constant mentions decides the order
of the records and nothing else, and `frontierOf` takes from the frontier walk only
slots the marks hold, whose values are the passes'.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## The frontier -/

/-- A table's two arrays have one size. -/
def Table.Sized {α : Type} (t : Table α) : Prop := t.keys.size = t.vals.size

theorem Table.add_good {α : Type} {spec : Nat → Option α} {t : Table α} {c : Nat} {v : α}
    (ht : t.Good spec) (hs : t.Sized) (hc : spec c = some v) :
    (t.add c v).Good spec ∧ (t.add c v).Sized := by
  obtain ⟨keys, vals⟩ := t
  simp only [Table.Sized] at hs
  refine ⟨?_, by simp [Table.add, Table.Sized, hs]⟩
  unfold Table.Good at ht ⊢
  intro i c' v' hk hv
  simp only [Table.add, Array.getElem?_push] at hk hv
  by_cases hi : i = keys.size
  · have hi' : i = vals.size := by omega
    simp only [hi, ↓reduceIte] at hk
    simp only [hi', ↓reduceIte] at hv
    cases hk; cases hv; exact hc
  · have hi' : i ≠ vals.size := by omega
    simp only [hi, ↓reduceIte] at hk
    simp only [hi', ↓reduceIte] at hv
    exact ht i c' v' hk hv

/-- A frontier's tables have their sizes. -/
structure Frontier.Sized (b : Frontier) : Prop where
  names : b.names.Sized
  levels : b.levels.Sized
  lists : b.lists.Sized
  exprs : b.exprs.Sized

theorem frontierStep_good {r : Region} {m fr : ByteArray} {st : DS} {n p : Nat} {b : Frontier}
    (hb : Built r m st n) (hp : p < n) (hB : b.Good r) (hS : b.Sized) :
    (frontierStep m fr st p b).Good r ∧ (frontierStep m fr st p b).Sized := by
  unfold frontierStep
  split
  · exact ⟨hB, hS⟩
  · obtain ⟨names, levels, lists, exprs⟩ := b
    obtain ⟨g1, g2, g3, g4⟩ := hB
    obtain ⟨s1, s2, s3, s4⟩ := hS
    simp only at g1 g2 g3 g4 s1 s2 s3 s4
    have hN : (if marked fr kName p && marked m kName p then names.add (8 * p) (st.nameV (8 * p))
        else names).Good (nameAt r) ∧ (if marked fr kName p && marked m kName p then
          names.add (8 * p) (st.nameV (8 * p)) else names).Sized := by
      split
      · rename_i hx
        simp only [Bool.and_eq_true] at hx
        exact Table.add_good g1 s1 ((hb p hp kName (Or.inl rfl) hx.2).1 rfl)
      · exact ⟨g1, s1⟩
    have hL : (if marked fr kLevel p && marked m kLevel p then levels.add (8 * p) (st.levelV (8 * p))
        else levels).Good (levelAt r) ∧ (if marked fr kLevel p && marked m kLevel p then
          levels.add (8 * p) (st.levelV (8 * p)) else levels).Sized := by
      split
      · rename_i hx
        simp only [Bool.and_eq_true] at hx
        exact Table.add_good g2 s2 ((hb p hp kLevel (Or.inr (Or.inl rfl)) hx.2).2.1 rfl)
      · exact ⟨g2, s2⟩
    have hS' : (if marked fr kLevels p && marked m kLevels p then lists.add (8 * p) (st.levelsV (8 * p))
        else lists).Good (levelsAt r) ∧ (if marked fr kLevels p && marked m kLevels p then
          lists.add (8 * p) (st.levelsV (8 * p)) else lists).Sized := by
      split
      · rename_i hx
        simp only [Bool.and_eq_true] at hx
        exact Table.add_good g3 s3 ((hb p hp kLevels (Or.inr (Or.inr (Or.inr rfl))) hx.2).2.2.1 rfl)
      · exact ⟨g3, s3⟩
    have hE : (if marked fr kExpr p && marked m kExpr p then exprs.add (8 * p) (st.exprV (8 * p))
        else exprs).Good (exprAt r) ∧ (if marked fr kExpr p && marked m kExpr p then
          exprs.add (8 * p) (st.exprV (8 * p)) else exprs).Sized := by
      split
      · rename_i hx
        simp only [Bool.and_eq_true] at hx
        exact Table.add_good g4 s4 ((hb p hp kExpr (Or.inr (Or.inr (Or.inl rfl))) hx.2).2.2.2 rfl)
      · exact ⟨g4, s4⟩
    exact ⟨⟨hN.1, hL.1, hS'.1, hE.1⟩, ⟨hN.2, hL.2, hS'.2, hE.2⟩⟩

/-- **The frontier holds only the specification's values**, whatever `fr` marks. -/
theorem frontierOf_good {r : Region} {m fr : ByteArray} {st : DS} {n : Nat}
    (hb : Built r m st n) : ∀ (p : Nat) (b : Frontier), b.Good r → b.Sized →
      (frontierOf m fr st n p b).Good r := by
  intro p
  induction hd : n - p generalizing p with
  | zero =>
    intro b hB _
    unfold frontierOf
    split
    · omega
    · exact hB
  | succ d ih =>
    intro b hB hS
    unfold frontierOf
    have hp : p < n := by omega
    split
    · obtain ⟨h1, h2⟩ := frontierStep_good (fr := fr) hb hp hB hS
      exact ih (p + 1) (by omega) _ h1 h2
    · omega

theorem Frontier.sized_empty : Frontier.Sized {} := ⟨rfl, rfl, rfl, rfl⟩

/-! ## A constant -/

theorem lazyEntry_congr {nm nm' : UInt64 → Option Name} {ex ex' : UInt64 → Option Expr}
    {r : Region} {i : Nat} (s : CEntryF UInt64 UInt64) (hn : ∀ x ∈ s.names, nm x = nm' x)
    (he : ∀ x ∈ lazyRoots s, ex x = ex' x) :
    lazyEntry nm ex r i s = lazyEntry nm' ex' r i s := by
  unfold lazyEntry
  rcases s with ⟨name, lps, type, kind⟩
  cases kind with
  | thm v all =>
    simp only
    rw [hn name (by simp [CEntryF.names]), he type (by simp [lazyRoots]),
      listMapM_congr lps (fun x hx => hn x (by simp [CEntryF.names, hx])),
      listMapM_congr all (fun x hx => hn x (by simp [CEntryF.names, hx]))]
  | _ => exact CEntryF.mapM_congr _ hn he

/-- **The constants of a load and the skeletons they read**: each skeleton read has its
constant, and each constant is a skeleton's. -/
structure LazyOf (r : Region) (i : Nat) (skels : List (CEntryF UInt64 UInt64))
    (es : List CEntry) : Prop where
  of_skel : ∀ s ∈ skels, ∃ e ∈ es, lazyEntry (nameP r) (exprP r) r i s = some e.toCEntryF
  to_skel : ∀ e ∈ es, ∃ s ∈ skels, lazyEntry (nameP r) (exprP r) r i s = some e.toCEntryF

theorem lazyEntries_spec {nm : UInt64 → Option Name} {ex : UInt64 → Option Expr}
    {r : Region} {i : Nat} {outs : Array (Array UInt64)} :
    ∀ {ss : List (CEntryF UInt64 UInt64)} {k : Nat} {es : List CEntry},
      (∀ s ∈ ss, (∀ x ∈ s.names, nm x = nameP r x) ∧ ∀ x ∈ lazyRoots s, ex x = exprP r x) →
      lazyEntries nm ex r i outs k ss = some es → LazyOf r i ss es
  | [], k, es, _, h => by
    simp only [lazyEntries, Option.some.injEq] at h
    subst h
    exact ⟨by simp, by simp⟩
  | s :: ss, k, es, hall, h => by
    unfold lazyEntries at h
    split at h
    · cases h
    · rename_i e he
      split at h
      · cases h
      · rename_i es' hes
        simp only [Option.some.injEq] at h
        subst h
        have h1 := hall s (by simp)
        have hE : lazyEntry (nameP r) (exprP r) r i s = some e := by
          rw [← lazyEntry_congr s h1.1 h1.2]
          exact he
        obtain ⟨t1, t2⟩ := lazyEntries_spec (fun s' hs' => hall s' (by simp [hs'])) hes
        refine ⟨fun s' hs' => ?_, fun e' he' => ?_⟩
        · rcases List.mem_cons.mp hs' with rfl | hs'
          · exact ⟨{ toCEntryF := e, uses := usesRead nm (outs.getD k #[]) }, by simp, hE⟩
          · obtain ⟨x, hx, h⟩ := t1 s' hs'
            exact ⟨x, by simp [hx], h⟩
        · rcases List.mem_cons.mp he' with rfl | he'
          · exact ⟨s, by simp, hE⟩
          · obtain ⟨x, hx, h⟩ := t2 e' he'
            exact ⟨x, by simp [hx], h⟩

/-! ## A module -/

/-- **The load is the specification, up to its theorems' values.** -/
theorem loadAt_spec {i : Nat} {m : Name} {f : ModFiles} {l : Loaded} (h : loadAt i m f = some l) :
    ∃ r a sk skels, f.viewRegion .private = some (r, a) ∧ constNamesOk r a = true ∧
      moduleSkel r a = some sk ∧ sk.consts.mapM (constSkel r) = some skels ∧
      l.name = m ∧ l.frontier.Good r ∧ LazyOf r i skels l.constants.toList := by
  unfold loadAt at h
  obtain ⟨⟨r, a⟩, hv, h⟩ := bind_some_left h
  simp only at h
  split at h
  rotate_left
  · cases h
  rename_i hcn
  obtain ⟨sk, hsk, h⟩ := bind_some_left h
  obtain ⟨skels, hskels, h⟩ := bind_some_left h
  obtain ⟨outs, -, h⟩ := bind_some_left h
  obtain ⟨⟨nm, ms, st⟩, hrun, h⟩ := bind_some_left h
  simp only at h
  obtain ⟨imports, -, h⟩ := bind_some_left h
  split at h
  rotate_left
  · cases h
  obtain ⟨cs, hcs, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  have hs := runMarked_spec r (sk.imports.map (·.module) ++ skels.flatMap CEntryF.names ++
    usesNames outs) (skels.flatMap lazyRoots)
  rw [hrun] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨r, a, sk, skels, hv, hcn, hsk, hskels, rfl, ?_, ?_⟩
  · exact frontierOf_good h3 0 {} (Frontier.good_empty r) Frontier.sized_empty
  · refine lazyEntries_spec (fun s hs => ⟨fun x hx => ?_, fun x hx => ?_⟩) hcs
    · exact h1 x (by simp only [List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inr ⟨s, hs, hx⟩))
    · exact h2 x (List.mem_flatMap.mpr ⟨s, hs, hx⟩)

/-! ## A constant against the specification's -/

/-- **`lazyEntry` is the specification's constant**, up to a theorem's value, which is a
reference to where the specification reads it. -/
theorem lazyEntry_of_spec {r : Region} {i : Nat} {s : CEntryF UInt64 UInt64}
    {c e : CEntryF Name Expr} (hc : s.mapM (nameP r) (exprP r) = some c)
    (he : lazyEntry (nameP r) (exprP r) r i s = some e) :
    e.name = c.name ∧ e.levelParams = c.levelParams ∧ e.type = c.type ∧
      ∀ v all, c.kind = .thm v all → ∃ p g all', s.kind = .thm p all' ∧
        e.kind = .thm (valueRef i g) all ∧ exprP r p = some v ∧ r.loc p = some g := by
  rcases s with ⟨name, lps, type, kind⟩
  cases kind with
  | thm p all' =>
    simp only [lazyEntry] at he
    split at he
    rotate_left
    · cases he
    obtain ⟨g, hg, he⟩ := bind_some_left he
    obtain ⟨n', hn', he⟩ := bind_some_left he
    obtain ⟨l', hl', he⟩ := bind_some_left he
    obtain ⟨t', ht', he⟩ := bind_some_left he
    obtain ⟨a', ha', he⟩ := bind_some_left he
    simp only [pure, Option.some.injEq] at he
    subst he
    simp only [CEntryF.mapM] at hc
    obtain ⟨n, hn, hc⟩ := bind_some_left hc
    obtain ⟨l, hl, hc⟩ := bind_some_left hc
    obtain ⟨t, ht, hc⟩ := bind_some_left hc
    obtain ⟨k, hk, hc⟩ := bind_some_left hc
    simp only [CKindF.mapM] at hk
    obtain ⟨v, hv, hk⟩ := bind_some_left hk
    obtain ⟨as, ha, hk⟩ := bind_some_left hk
    cases hk
    cases hc
    rw [hn] at hn'; cases hn'
    rw [hl] at hl'; cases hl'
    rw [ht] at ht'; cases ht'
    rw [ha] at ha'; cases ha'
    refine ⟨rfl, rfl, rfl, fun v' all h => ?_⟩
    simp only [CKindF.thm.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨p, g, all', rfl, rfl, hv, hg⟩
  | _ =>
    simp only [lazyEntry] at he
    rw [hc] at he
    cases he
    refine ⟨rfl, rfl, rfl, fun v all h => ?_⟩
    have := (CEntryF.mapM_parts hc).2.2.2.1
    rw [h] at this
    simp [CKindF.tag] at this

/-- **A theorem's entry and its skeleton**: the reference is to the location of the skeleton's
value, and its other fields are the specification's reads. -/
theorem lazyEntry_thm {r : Region} {i : Nat} {s : CEntryF UInt64 UInt64} {E : CEntryF Name Expr}
    {w : Expr} {all : List Name} (he : lazyEntry (nameP r) (exprP r) r i s = some E)
    (hk : E.kind = .thm w all) :
    ∃ p g all₀, s.kind = .thm p all₀ ∧ w = valueRef i g ∧ r.loc p = some g ∧ i < refBase ∧
      nameP r s.name = some E.name ∧ s.levelParams.mapM (nameP r) = some E.levelParams ∧
      exprP r s.type = some E.type ∧ all₀.mapM (nameP r) = some all := by
  rcases s with ⟨name, lps, type, kind⟩
  cases kind with
  | thm p all₀ =>
    simp only [lazyEntry] at he
    split at he
    rotate_left
    · cases he
    rename_i hi
    obtain ⟨g, hg, he⟩ := bind_some_left he
    obtain ⟨n', hn', he⟩ := bind_some_left he
    obtain ⟨l', hl', he⟩ := bind_some_left he
    obtain ⟨t', ht', he⟩ := bind_some_left he
    obtain ⟨a', ha', he⟩ := bind_some_left he
    simp only [pure, Option.some.injEq] at he
    subst he
    simp only [CKindF.thm.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨p, g, all₀, rfl, rfl, hg, hi, hn', hl', ht', ha'⟩
  | _ =>
    simp only [lazyEntry] at he
    have := (CEntryF.mapM_parts he).2.2.2.1
    rw [hk] at this
    simp [CKindF.tag] at this

/-- The two parts of a reference's code. -/
theorem refParts {i g : Nat} (hi : i < refBase) :
    refModule (g * refBase + i) = i ∧ refLoc (g * refBase + i) = g := by
  have hpos : 0 < refBase := by decide
  unfold refModule refLoc
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hi, Nat.zero_add]

end ConLeche.Frontend.Olean
