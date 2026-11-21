module

public import ConLeche.Frontend.Olean.Group
public import ConLeche.Verify.Frontend.Olean.Emit

/-!
# One inductive group's record comes from stored constants

`groupRecord_from`: where `groupRecord mg n` has a record, it is the stream reader's
builder applied to one `inductive` record whose every type, constructor and recursor
is a constant `mg` stores, of that kind (`RecFrom`), as `declsOf_from` says of the
whole emission; and `groupRecord_valid`: each of the group's names passed `blockStep`.
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

private theorem foldl_out {α : Type} {f : Emit × Array α → CEntry → Emit × Array α}
    (hf : ∀ st acc c, (f (st, acc) c).1.out = st.out) :
    ∀ (l : List CEntry) (st : Emit) (acc : Array α), (l.foldl f (st, acc)).1.out = st.out
  | [], _, _ => rfl
  | c :: l, st, acc => by
    simp only [List.foldl_cons]
    rw [show f (st, acc) c = ((f (st, acc) c).1, (f (st, acc) c).2) from rfl,
      foldl_out hf l, hf]

private theorem cv_out (st : Emit) (c : CEntry) : (st.cv c).1.out = st.out :=
  (Emit.cv_spec st c).2.2.2
private theorem names'_out (st : Emit) (ns : List Name) : (st.names' ns).1.out = st.out :=
  (Emit.names'_spec st ns).2.2
private theorem name_out (st : Emit) (n : Name) : (st.name n).1.out = st.out :=
  (Emit.name_spec st n).2.2.2
private theorem rules_out (st : Emit) (rules : List (Name × Nat × Expr)) :
    (rules.foldl Emit.ruleStep (st, #[])).1.out = st.out :=
  (ruleStep_fold rules st #[]).2.2

private theorem tyStep_out (st : Emit) (acc : Array IndTypeRec) (c : CEntry) :
    (Emit.tyStep (st, acc) c).1.out = st.out := by
  unfold Emit.tyStep
  split
  rename_i heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  split <;> simp [cv_out, names'_out]

private theorem ctorStep_out (st : Emit) (acc : Array IndCtorRec) (c : CEntry) :
    (Emit.ctorStep (st, acc) c).1.out = st.out := by
  unfold Emit.ctorStep
  split
  rename_i heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  split <;> simp [cv_out, name_out]

private theorem recStep_out (st : Emit) (acc : Array IndRecRec) (c : CEntry) :
    (Emit.recStep (st, acc) c).1.out = st.out := by
  unfold Emit.recStep
  split
  rename_i heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  split <;> simp [cv_out, rules_out]

/-- A block's emission pushes one `inductive` record. -/
theorem Emit.block_out (st : Emit) (tys ctors recs : List CEntry) :
    ∃ ts cts rs, (st.block tys ctors recs).out = st.out.push (.ind ts cts rs) := by
  simp only [Emit.block]
  exact ⟨_, _, _, by rw [(Emit.push_spec _ _).2.2, foldl_out recStep_out, foldl_out ctorStep_out,
    foldl_out tyStep_out]⟩

private theorem mem_filterMap_stored {mg : Merged}
    (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n) {ns : List Name} {c : CEntry}
    (h : c ∈ ns.filterMap (mg.map[·]?)) : Stored mg c := by
  obtain ⟨x, -, hx⟩ := List.mem_filterMap.mp h
  unfold Stored
  rw [hN x c hx]
  exact hx

/-- **The group's record is made of stored constants of the group's kinds.** -/
theorem groupRecord_from {mg : Merged} {n : Name} {d : Declaration}
    (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    (h : groupRecord mg n = .ok d) :
    ∃ tys ctors recs ts cts rcs, groupParts mg n = some (tys, ctors, recs) ∧
      RecFrom mg (groupEmit tys ctors recs) (.ind ts cts rcs) ∧
      declOfF (groupEmit tys ctors recs).nm (groupEmit tys ctors recs).lv
        (groupEmit tys ctors recs).ex (.ind ts cts rcs) = .ok (.inl d) := by
  unfold groupRecord at h
  split at h
  · cases h
  · rename_i tys ctors recs hp
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ds hds
        have hd : d ∈ ds := by
          split at h
          · rename_i d' hd'
            split at h
            · cases h; exact Array.mem_of_getElem? hd'
            · cases h
          · cases h
        have ht : ∀ c ∈ tys, Stored mg c := by
          unfold groupParts at hp
          split at hp <;> try cases hp
          split at hp <;> cases hp
          exact fun c hc => mem_filterMap_stored hN hc
        have hc : ∀ c ∈ ctors, Stored mg c := by
          unfold groupParts at hp
          split at hp <;> try cases hp
          split at hp <;> cases hp
          intro c hc
          simp only [blockCtors, List.mem_flatMap] at hc
          obtain ⟨t, -, ht⟩ := hc
          split at ht
          · exact mem_filterMap_stored hN ht
          · cases ht
        have hr : ∀ c ∈ recs, Stored mg c := by
          unfold groupParts at hp
          split at hp <;> try cases hp
          split at hp <;> cases hp
          intro c hc
          simp only [blockRecs] at hc
          exact mem_filterMap_stored hN hc
        obtain ⟨-, -, hfrom⟩ := Emit.block_spec mg {} tys ctors recs ht hc hr
        obtain ⟨r, hr', hdr⟩ := (declsOf_spec hds).2 d hd
        obtain ⟨ts, cts, rs, hout⟩ := Emit.block_out {} tys ctors recs
        have hr0 : r = .ind ts cts rs := by
          have : r ∈ (({} : Emit).out.push (.ind ts cts rs)) := by
            simpa [groupEmit, hout] using hr'
          simpa using this
        subst hr0
        rcases hfrom _ hr' with hx | hx
        · simp at hx
        · exact ⟨tys, ctors, recs, ts, cts, rs, hp, hx, hdr⟩

/-- **The group was validated**: `n` and each of its constants passed `blockStep`. -/
theorem groupRecord_valid {mg : Merged} {n : Name} {d : Declaration}
    (h : groupRecord mg n = .ok d) :
    ∃ tys ctors recs, groupParts mg n = some (tys, ctors, recs) ∧
      ∀ x ∈ n :: (tys ++ ctors ++ recs).map (·.name), blockStep mg x = .ok () := by
  unfold groupRecord at h
  split at h
  · cases h
  · rename_i tys ctors recs hp
    split at h
    · cases h
    · rename_i hf
      exact ⟨tys, ctors, recs, hp, forM_ok hf⟩

/-- `mergedOfList` holds each constant under its own name. -/
theorem mergedOfList_names (cs : List CEntry) :
    ∀ (n : Name) (c : CEntry), (mergedOfList cs).map[n]? = some c → c.name = n := by
  unfold mergedOfList
  suffices ∀ (mg : Merged), (∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n) →
      ∀ (n : Name) (c : CEntry), (cs.foldl (fun mg c =>
        if mg.map.contains c.name then mg
        else { map := mg.map.insert c.name c, order := mg.order.push c.name }) mg).map[n]? = some c →
        c.name = n from this {} (by simp)
  induction cs with
  | nil => intro mg h; exact h
  | cons x cs ih =>
    intro mg h
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · intro n c hc
      rw [Std.HashMap.getElem?_insert] at hc
      split at hc
      · rename_i he
        cases hc
        exact eq_of_beq he
      · exact h n c hc

/-- `mergedOfList`'s fold, from any merged state: its order lists what it holds, it holds only
constants allowed (`Q`), every constant of the list's name, and what it held. -/
theorem mergedOfList_fold (Q : CEntry → Prop) :
    ∀ (cs : List CEntry) (mg : Merged), (∀ n, n ∈ mg.order ↔ mg.map.contains n = true) →
      (∀ (n : Name) (c : CEntry), mg.map[n]? = some c → Q c) → (∀ c ∈ cs, Q c) →
      let mg' := cs.foldl (fun mg c =>
        if mg.map.contains c.name then mg
        else { map := mg.map.insert c.name c, order := mg.order.push c.name }) mg
      (∀ n, n ∈ mg'.order ↔ mg'.map.contains n = true) ∧
        (∀ (n : Name) (c : CEntry), mg'.map[n]? = some c → Q c) ∧
        (∀ c ∈ cs, mg'.map.contains c.name = true) ∧
        ∀ n, mg.map.contains n = true → mg'.map.contains n = true
  | [], mg, h1, h2, _ => ⟨h1, h2, by simp, fun _ h => h⟩
  | x :: cs, mg, h1, h2, hq => by
    simp only [List.foldl_cons]
    have hq' : ∀ c ∈ cs, Q c := fun c hc => hq c (List.mem_cons_of_mem _ hc)
    split
    · rename_i hx
      obtain ⟨a, b, c, d⟩ := mergedOfList_fold Q cs mg h1 h2 hq'
      refine ⟨a, b, fun c' hc' => ?_, d⟩
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact d _ hx
      · exact c c' hc'
    · rename_i hx
      have g1 : ∀ n, n ∈ (mg.order.push x.name) ↔ (mg.map.insert x.name x).contains n = true := by
        intro n
        simp only [Array.mem_push, Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, h1]
        constructor
        · rintro (h | rfl)
          · exact .inr h
          · exact .inl rfl
        · rintro (h | h)
          · exact .inr h.symm
          · exact .inl h
      have g2 : ∀ (n : Name) (c : CEntry), (mg.map.insert x.name x)[n]? = some c → Q c := by
        intro n c hc
        rw [Std.HashMap.getElem?_insert] at hc
        split at hc
        · cases hc
          exact hq _ List.mem_cons_self
        · exact h2 n c hc
      obtain ⟨a, b, c, d⟩ := mergedOfList_fold Q cs
        { map := mg.map.insert x.name x, order := mg.order.push x.name } g1 g2 hq'
      refine ⟨a, b, fun c' hc' => ?_, fun n hn => d n (by simp [Std.HashMap.contains_insert, hn])⟩
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact d _ (by simp [Std.HashMap.contains_insert])
      · exact c c' hc'

/-- **What `mergedOfList` holds**: its order lists exactly its names, it holds only constants of
the list, and every constant's name. -/
theorem mergedOfList_spec (cs : List CEntry) :
    (∀ n, n ∈ (mergedOfList cs).order ↔ (mergedOfList cs).map.contains n = true) ∧
    (∀ (n : Name) (c : CEntry), (mergedOfList cs).map[n]? = some c → c ∈ cs) ∧
    ∀ c ∈ cs, (mergedOfList cs).map.contains c.name = true := by
  obtain ⟨a, b, c, -⟩ := mergedOfList_fold (· ∈ cs) cs {} (by simp) (by simp) (fun _ h => h)
  exact ⟨a, b, c⟩

end ConLeche.Frontend.Olean
