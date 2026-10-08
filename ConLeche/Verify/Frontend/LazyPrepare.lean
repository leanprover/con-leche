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

/-! ## The hoist over known constants -/

/-- Every constant list `uc'` knows is `uc`'s. -/
@[expose] def UcMono (uc' uc : Nat → Option (Array Name)) : Prop :=
  ∀ k x, uc' k = some x → uc k = some x

theorem hoistWalk_mono {uc' uc : Nat → Option (Array Name)} (hu : UcMono uc' uc)
    (idx : Std.HashMap Name Nat) (i : Nat) :
    ∀ (fuel : Nat) (st : List Nat) (t r : Std.HashMap Nat Nat),
    hoistWalk idx uc' i fuel st t = some r → hoistWalk idx uc i fuel st t = some r := by
  intro fuel
  induction fuel with
  | zero => intro st t r h; simp [hoistWalk] at h
  | succ fuel ih =>
    intro st t r h
    cases st with
    | nil => exact h
    | cons k st =>
      simp only [hoistWalk] at h ⊢
      by_cases hc : movedBy t k i = true
      · simp only [hc, ↓reduceIte] at h ⊢; exact ih _ _ _ h
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hus : uc' k with
        | none => rw [hus] at h; simp at h
        | some us =>
          rw [hus] at h
          rw [hu k us hus]; exact ih _ _ _ h

theorem hoistDeps_mono {uc' uc : Nat → Option (Array Name)} (hu : UcMono uc' uc)
    (idx : Std.HashMap Name Nat) (i : Nat) :
    ∀ (gs : List Name) (t r : Std.HashMap Nat Nat),
    hoistDeps idx uc' i gs t = some r → hoistDeps idx uc i gs t = some r := by
  intro gs
  induction gs with
  | nil => intro t r h; exact h
  | cons g gs ih =>
    intro t r h
    simp only [hoistDeps] at h ⊢
    cases hj : idx[g]? with
    | none => rw [hj] at h; exact ih _ _ h
    | some j =>
      rw [hj] at h
      simp only at h ⊢
      by_cases hji : j > i
      · simp only [hji, ↓reduceIte] at h ⊢
        cases ht' : hoistWalk idx uc' i hoistFuel [j] t with
        | none => rw [ht'] at h; simp at h
        | some t' =>
          rw [ht'] at h
          rw [hoistWalk_mono hu idx i _ _ _ _ ht']; exact ih _ _ h
      · simp only [hji, ↓reduceIte] at h ⊢; exact ih _ _ h

theorem hoistOps_mono {uc' uc : Nat → Option (Array Name)} (hu : UcMono uc' uc)
    (sh : Array (List Name × Option Name)) (idx : Std.HashMap Name Nat) :
    ∀ (n i : Nat) (t r : Std.HashMap Nat Nat), sh.size - i = n →
    hoistOps sh idx uc' i t = some r → hoistOps sh idx uc i t = some r := by
  intro n
  induction n with
  | zero =>
    intro i t r hn h
    rw [hoistOps] at h ⊢
    rw [ite_eq_right (by omega)] at h ⊢
    exact h
  | succ n ih =>
    intro i t r hn h
    rw [hoistOps] at h ⊢
    rw [ite_eq_left (by omega)] at h ⊢
    cases hc : sh[i]!.2 with
    | none => rw [hc] at h; exact ih (i + 1) _ _ (by omega) h
    | some c =>
      rw [hc] at h
      simp only at h ⊢
      cases ht' : hoistDeps idx uc' i (natOpDeps c) t with
      | none => rw [ht'] at h; simp at h
      | some t' =>
        rw [ht'] at h
        rw [hoistDeps_mono hu idx i _ _ _ ht']
        exact ih (i + 1) _ _ (by omega) h

theorem hoistTargetsU_mono {uc' uc : Nat → Option (Array Name)} (hu : UcMono uc' uc)
    {sh : Array (List Name × Option Name)} {r : Std.HashMap Nat Nat}
    (h : hoistTargetsU sh uc' = some r) : hoistTargetsU sh uc = some r :=
  hoistOps_mono hu sh _ _ 0 _ _ rfl h

theorem Pw.map_getElem! [Inhabited α] [Inhabited β] {S : α → β → Prop} {a : Array α} {b : Array β}
    (h : Pw S a.toList b.toList) :
    ∀ (l : List Nat), (∀ k ∈ l, k < a.size) →
      Pw S (l.map (a[·]!)) (l.map (b[·]!))
  | [], _ => trivial
  | k :: l, hl => by
    have hk := hl k List.mem_cons_self
    have hb : k < b.size := by have := Pw.length h; simp at this; omega
    refine ⟨?_, Pw.map_getElem! h l (fun j hj => hl j (List.mem_cons_of_mem _ hj))⟩
    show S a[k]! b[k]!
    rw [getElem!_pos a k hk, getElem!_pos b k hb]
    have := Pw.getElem h k (by simpa using hk) (by simpa using hb)
    simpa using this

theorem applyHoist_rel {a b : Array Declaration} (h : Pw R a.toList b.toList)
    (t : Std.HashMap Nat Nat) : Pw R (applyHoist a t).1.toList (applyHoist b t).1.toList := by
  have hsz : a.size = b.size := by have := Pw.length h; simpa using this
  simp only [applyHoist, List.toList_toArray, hsz]
  apply Pw.map_getElem! h
  intro k hk
  have := (List.mergeSort_perm (List.range b.size) _).mem_iff.mp hk
  simp at this; omega

/-- **The lazy preparation of related records is related to the serial
one.** -/
theorem prepareLazy_rel (hR : ∀ d' d, R d' d → declShape d' = declShape d)
    (hR2 : ∀ d' d, R d' d → isThmDecl d' = false → d' = d) {pre : PreludeIx}
    (hpre : ∀ p ∈ pre.decls.toList, R p p) {ds' ds : Array Declaration}
    (h : Pw R ds'.toList ds.toList) {pr : Prepared} (hl : prepareLazy pre ds' = some pr) :
    Pw R pr.decls.toList (preparePrelude pre ds).toList := by
  obtain ⟨a1, a2⟩ := frontOf_toList pre.decls.toList #[] ds'
  obtain ⟨b1, b2⟩ := frontOf_toList pre.decls.toList #[] ds
  obtain ⟨hf, hr⟩ := frontSpec_rel hR pre.decls.toList hpre h
  generalize hA : (frontOf #[] pre.decls.toList ds').1 ++ (frontOf #[] pre.decls.toList ds').2 = A
    at *
  generalize hB : (frontOf #[] pre.decls.toList ds).1 ++ (frontOf #[] pre.decls.toList ds).2 = B
    at *
  have hall : Pw R A.toList B.toList := by
    rw [← hA, ← hB, Array.toList_append, Array.toList_append, a1, a2, b1, b2]
    simpa using Pw.append hf hr
  have hsh : A.map declShape = B.map declShape := by
    apply Array.toList_inj.mp
    simp only [Array.toList_map]
    exact Pw.map_shape hR hall
  have hgl : groundLate B = groundLate A := by simp only [groundLate, hsh]
  have hsz : A.size = B.size := by have := Pw.length hall; simpa using this
  simp only [prepareLazy, hA] at hl
  simp only [preparePrelude, prepareD, hB, hoistNatOpGround, hoistTargets, hgl]
  split at hl
  · rename_i hlate
    simp only [hlate, ↓reduceIte]
    split at hl
    · rename_i t ht
      have hmono : UcMono (fun k => match A[k]! with
          | .thmDecl .. => none
          | d => some d.usedConsts) (fun k => some B[k]!.usedConsts) := by
        intro k x hk
        simp only at hk ⊢
        by_cases hkA : k < A.size
        · have hrel : R A[k] B[k] := by
            have := Pw.getElem hall k (by simpa using hkA) (by simpa [← hsz] using hkA)
            simpa using this
          rw [getElem!_pos A k hkA] at hk
          rw [getElem!_pos B k (by omega)]
          cases hAk : A[k] with
          | thmDecl cv w => rw [hAk] at hk; simp at hk
          | _ =>
            rw [hAk] at hk hrel
            have := hR2 _ _ hrel rfl
            rw [← this]; exact hk
        · rw [getElem!_neg A k hkA] at hk
          rw [getElem!_neg B k (by omega)]
          revert hk
          cases (default : Declaration) <;> simp
      rw [← hsh, hoistTargetsU_mono hmono ht]
      simp only [Option.getD_some]
      simp only [Option.some.injEq] at hl
      subst hl
      split
      · exact hall
      · exact applyHoist_rel hall t
    · simp at hl
  · rename_i hlate
    simp only [hlate, Bool.false_eq_true, ↓reduceIte, Std.HashMap.isEmpty_empty]
    simp only [Option.some.injEq] at hl
    subst hl
    exact hall

end ConLeche.Frontend
