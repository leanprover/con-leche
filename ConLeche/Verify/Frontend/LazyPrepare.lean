module

public import ConLeche.Verify.Frontend.Prepare
public import ConLeche.Verify.Frontend.Lazy

public section

/-!
# The preparation of related records (task #329)

`preparePrelude` reads a record's names (to find the stream's copy of a
prelude declaration) and, through the hoist, its types and values — but
only when the hoist's names-only gate (`groundLate`) lets the hoist
run.  So on two record arrays related member by member by a relation
that keeps names and the pinned-operation test (`declShape`), with the
gate closed and every prelude record related to itself, the prepared
arrays are related member by member.  The lazy driver prepares records
whose theorem values are placeholders and checks the relation's other
side, the serial parse's records.
-/

namespace ConLeche.Frontend

open ConLeche

variable {R : Declaration → Declaration → Prop}

theorem pickSpec_rel (hR : ∀ d' d, R d' d → declShape d' = declShape d) (n : Name) :
    ∀ {a b : List Declaration}, Pw R a b →
      (match (pickSpec n a).1, (pickSpec n b).1 with
       | some x, some y => R x y
       | none, none => True
       | _, _ => False) ∧ Pw R (pickSpec n a).2 (pickSpec n b).2
  | [], [], _ => ⟨trivial, trivial⟩
  | d' :: a, d :: b, h => by
    have hn : declares n d' = declares n d := by
      have := congrArg Prod.fst (hR _ _ h.1)
      simp only [declShape] at this
      simp only [declares, this]
    by_cases hd : declares n d = true
    · simp only [pickSpec, hn, hd, ↓reduceIte]
      exact ⟨h.1, h.2⟩
    · simp only [pickSpec, hn, hd, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2⟩ := pickSpec_rel hR n h.2
      exact ⟨h1, ⟨h.1, h2⟩⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem frontSpec_rel (hR : ∀ d' d, R d' d → declShape d' = declShape d) :
    ∀ (ps : List Declaration), (∀ p ∈ ps, R p p) → ∀ {a b : List Declaration}, Pw R a b →
      Pw R (frontSpec ps a).1 (frontSpec ps b).1 ∧ Pw R (frontSpec ps a).2 (frontSpec ps b).2
  | [], _, _, _, h => ⟨trivial, h⟩
  | p :: ps, hp, a, b, h => by
    obtain ⟨hm, hr⟩ := pickSpec_rel hR (preludeKey p) h
    obtain ⟨h1, h2⟩ := frontSpec_rel hR ps (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hr
    simp only [frontSpec]
    refine ⟨⟨?_, h1⟩, h2⟩
    revert hm
    cases (pickSpec (preludeKey p) a).1 <;> cases (pickSpec (preludeKey p) b).1 <;> simp
    exact hp p List.mem_cons_self

theorem Pw.map_shape (hR : ∀ d' d, R d' d → declShape d' = declShape d) :
    ∀ {a b : List Declaration}, Pw R a b → a.map declShape = b.map declShape
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [hR _ _ h.1, Pw.map_shape hR h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem hoist_closed {ds : Array Declaration} (h : groundLate ds = false) :
    hoistNatOpGround ds = (ds, #[]) := by
  simp [hoistNatOpGround, hoistTargets, h]

/-- **The prepared arrays of related records are related**, the gate
closed. -/
theorem prepare_rel (hR : ∀ d' d, R d' d → declShape d' = declShape d) {pre : PreludeIx}
    (hpre : ∀ p ∈ pre.decls.toList, R p p) {ds' ds : Array Declaration}
    (h : Pw R ds'.toList ds.toList) (hl : (prepareD pre ds').late = false) :
    Pw R (preparePrelude pre ds').toList (preparePrelude pre ds).toList := by
  obtain ⟨a1, a2⟩ := frontOf_toList pre.decls.toList #[] ds'
  obtain ⟨b1, b2⟩ := frontOf_toList pre.decls.toList #[] ds
  obtain ⟨hf, hr⟩ := frontSpec_rel hR pre.decls.toList hpre h
  have hall : Pw R ((frontOf #[] pre.decls.toList ds').1 ++ (frontOf #[] pre.decls.toList ds').2).toList
      ((frontOf #[] pre.decls.toList ds).1 ++ (frontOf #[] pre.decls.toList ds).2).toList := by
    rw [Array.toList_append, Array.toList_append, a1, a2, b1, b2]
    simpa using Pw.append hf hr
  have hgl : groundLate ((frontOf #[] pre.decls.toList ds).1 ++ (frontOf #[] pre.decls.toList ds).2) =
      groundLate ((frontOf #[] pre.decls.toList ds').1 ++ (frontOf #[] pre.decls.toList ds').2) := by
    simp only [groundLate]
    congr 1
    apply Array.toList_inj.mp
    simp only [Array.toList_map]
    exact (Pw.map_shape hR hall).symm
  simp only [prepareD] at hl
  simp only [preparePrelude, prepareD]
  rw [hoist_closed hl, hoist_closed (hgl.trans hl)]
  exact hall

end ConLeche.Frontend
