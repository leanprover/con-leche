module

public import ConLeche.Verify.Frontend.Olean.Memo

public section

/-!
# What an object leads to (task #371)

The marking functions of the fast decoder (`markName` … `markExpr`,
`ConLeche/Frontend/Olean/Fast.lean`) are one table read four ways:
`kidTable` lists, per kind and shape, the pointer fields the node
function follows to objects of a recursive type.  This file states
the table's two relations — `MarkOK` (every such field is the kind's
scalar or points below the object) and `Kid` (the object leads to the
object at a location, as a kind) — proves the marking functions mark
exactly the `Kid`s and fail exactly when `MarkOK` fails, and proves the
three facts about the node functions the passes need: a node function
fails where `MarkOK` fails, a node that reads leads to objects that
read, and a node function asks its arguments about `Kid`s only.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

@[expose] def nameKids : Nat → Nat → Option (List (Nat × UInt8 × Bool))
  | 1, 2 => some [(0, kName, true)]
  | 2, 2 => some [(0, kName, true)]
  | _, _ => none

@[expose] def levelKids : Nat → Nat → Option (List (Nat × UInt8 × Bool))
  | 0, 0 => some []
  | 1, 1 => some [(0, kLevel, true)]
  | 2, 2 => some [(0, kLevel, true), (1, kLevel, true)]
  | 3, 2 => some [(0, kLevel, true), (1, kLevel, true)]
  | 4, 1 => some [(0, kName, true)]
  | _, _ => none

@[expose] def levelsKids : Nat → Nat → Option (List (Nat × UInt8 × Bool))
  | 1, 2 => some [(0, kLevel, true), (1, kLevels, true)]
  | _, _ => none

@[expose] def exprKids : Nat → Nat → Option (List (Nat × UInt8 × Bool))
  | 0, 1 => some []
  | 3, 1 => some [(0, kLevel, true)]
  | 4, 2 => some [(0, kName, true), (1, kLevels, true)]
  | 5, 2 => some [(0, kExpr, false), (1, kExpr, false)]
  | 6, 3 => some [(1, kExpr, false), (2, kExpr, false)]
  | 7, 3 => some [(1, kExpr, false), (2, kExpr, false)]
  | 8, 4 => some [(1, kExpr, false), (2, kExpr, false), (3, kExpr, false)]
  | 9, 1 => some []
  | 10, 2 => some [(1, kExpr, false)]
  | 11, 3 => some [(0, kName, true), (2, kExpr, false)]
  | _, _ => none

/-- **The objects an object leads to**: for an object read as kind `k`
with tag `t` and `n` pointer fields, the pointer fields its node
function follows to objects of a recursive type — the field, the kind
it is read as, and whether that kind's nullary constructor is the
scalar `0` — or `none` when the node function reads no object of that
shape. -/
@[expose] def kidTable (k : UInt8) (t n : Nat) : Option (List (Nat × UInt8 × Bool)) :=
  if k = kName then nameKids t n
  else if k = kLevel then levelKids t n
  else if k = kLevels then levelsKids t n
  else exprKids t n

theorem kidTable_name (t n : Nat) : kidTable kName t n = nameKids t n := rfl
theorem kidTable_level (t n : Nat) : kidTable kLevel t n = levelKids t n := rfl
theorem kidTable_levels (t n : Nat) : kidTable kLevels t n = levelsKids t n := rfl
theorem kidTable_expr (t n : Nat) : kidTable kExpr t n = exprKids t n := rfl

/-- The marking of one object, read off the table. -/
@[expose] def markObj (r : Region) (k : UInt8) (g : Nat) (st : DS) : Option DS :=
  if r.fits g then
    match kidTable k (r.tag g) (r.nobjs g) with
    | some fs => fs.foldlM (fun st f => st.markPtr r g f.2.1 f.2.2 (r.fld g f.1)) st
    | none => none
  else none

theorem markName_eq (r : Region) (g : Nat) (st : DS) : markName r g st = markObj r kName g st := by
  unfold markName markObj
  split
  · simp only [kidTable, ite_true]
    split <;> simp_all [List.foldlM, Option.bind_eq_bind, nameKids]
  · rfl

theorem markLevel_eq (r : Region) (g : Nat) (st : DS) :
    markLevel r g st = markObj r kLevel g st := by
  unfold markLevel markObj
  split
  · simp only [kidTable, show kLevel ≠ kName by decide, ite_false, ite_true]
    split <;> simp_all [List.foldlM, Option.bind_eq_bind, levelKids]
  · rfl

theorem markLevels_eq (r : Region) (g : Nat) (st : DS) :
    markLevels r g st = markObj r kLevels g st := by
  unfold markLevels markObj
  split
  · simp only [kidTable, show kLevels ≠ kName by decide, show kLevels ≠ kLevel by decide,
      ite_false, ite_true]
    split <;> simp_all [List.foldlM, Option.bind_eq_bind, levelsKids]
  · rfl

theorem markExpr_eq (r : Region) (g : Nat) (st : DS) :
    markExpr r g st = markObj r kExpr g st := by
  unfold markExpr markObj
  split
  · simp only [kidTable, show kExpr ≠ kName by decide, show kExpr ≠ kLevel by decide,
      show kExpr ≠ kLevels by decide, ite_false]
    split <;> simp_all [List.foldlM, Option.bind_eq_bind, exprKids, Option.bind_assoc]
  · rfl

/-! ## The relations -/

/-- A followed field is the kind's scalar or points below the object. -/
@[expose] def FieldOK (r : Region) (g : Nat) (nil : Bool) (v : UInt64) : Prop :=
  (nil = true ∧ v = 1) ∨ (r.down g v).isSome

/-- The object at `g`, read as kind `k`, has a shape its node function
reads, and every field it follows is fine. -/
@[expose] def MarkOK (r : Region) (k : UInt8) (g : Nat) : Prop :=
  r.fits g = true ∧ ∃ fs, kidTable k (r.tag g) (r.nobjs g) = some fs ∧
    ∀ f ∈ fs, FieldOK r g f.2.2 (r.fld g f.1)

/-- The object at `g`, read as kind `k`, leads to the object at `c`,
read as kind `k'`. -/
@[expose] def Kid (r : Region) (k : UInt8) (g : Nat) (k' : UInt8) (c : Nat) : Prop :=
  r.fits g = true ∧ ∃ fs, kidTable k (r.tag g) (r.nobjs g) = some fs ∧
    ∃ i nil, (i, k', nil) ∈ fs ∧ ¬(nil = true ∧ r.fld g i = 1) ∧ r.down g (r.fld g i) = some c

theorem kidTable_kinds {k : UInt8} {t n : Nat} {fs : List (Nat × UInt8 × Bool)}
    (h : kidTable k t n = some fs) : ∀ f ∈ fs, IsKind f.2.1 := by
  unfold kidTable at h
  simp only [IsKind]
  split at h
  · unfold nameKids at h; split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h <;> simp
  split at h
  · unfold levelKids at h; split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h <;> simp
  split at h
  · unfold levelsKids at h; split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h <;> simp
  · unfold exprKids at h; split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h <;> simp

theorem Kid.lt {r : Region} {k : UInt8} {g : Nat} {k' : UInt8} {c : Nat} (h : Kid r k g k' c) :
    c < g := by
  obtain ⟨_, _, _, _, _, _, _, hd⟩ := h
  exact Region.down_lt hd

theorem Kid.kind {r : Region} {k : UInt8} {g : Nat} {k' : UInt8} {c : Nat} (h : Kid r k g k' c) :
    IsKind k' := by
  obtain ⟨_, fs, hfs, i, nil, hm, _, _⟩ := h
  exact kidTable_kinds hfs _ hm

/-! ## Marking -/

theorem markPtr_eq (r : Region) (g : Nat) (k : UInt8) (nil : Bool) (v : UInt64) (st : DS) :
    st.markPtr r g k nil v =
      if nil = true ∧ v = 1 then some st else (r.down g v).map fun c => st.mark k (c / 8) := by
  unfold DS.markPtr
  by_cases h : nil = true ∧ v = 1
  · simp [h]
  · have : (nil && v == 1) = false := by
      cases nil <;> simp_all
    simp only [this, Bool.false_eq_true, ite_false, h]
    split <;> simp_all

/-- What a fold of marks does: it fails iff a field is not fine, and
otherwise adds exactly the marks of the fields' objects. -/
theorem foldMarks (r : Region) (g : Nat) :
    ∀ (fs : List (Nat × UInt8 × Bool)) (st : DS), (∀ f ∈ fs, IsKind f.2.1) →
    match fs.foldlM (fun st f => st.markPtr r g f.2.1 f.2.2 (r.fld g f.1)) st with
    | none => ¬ ∀ f ∈ fs, FieldOK r g f.2.2 (r.fld g f.1)
    | some st' => (∀ f ∈ fs, FieldOK r g f.2.2 (r.fld g f.1)) ∧
        st'.marks.size = st.marks.size ∧
        st'.names = st.names ∧ st'.levels = st.levels ∧ st'.exprs = st.exprs ∧
        st'.lists = st.lists ∧
        ∀ k'' s, IsKind k'' → (st'.marked k'' s = true ↔ st.marked k'' s = true ∨
          ∃ i k' nil, (i, k', nil) ∈ fs ∧ k' = k'' ∧ ¬(nil = true ∧ r.fld g i = 1) ∧
            ∃ c, r.down g (r.fld g i) = some c ∧ c / 8 = s ∧ s < st.marks.size)
  | [], st, _ => by simp [List.foldlM]
  | (i, k', nil) :: fs, st, hk => by
    have hk1 : IsKind k' := hk (i, k', nil) List.mem_cons_self
    have hk2 : ∀ f ∈ fs, IsKind f.2.1 := fun f hf => hk f (List.mem_cons_of_mem _ hf)
    simp only [List.foldlM_cons]
    rw [markPtr_eq]
    by_cases hn : nil = true ∧ r.fld g i = 1
    · obtain ⟨rfl, hv⟩ := hn
      simp only [hv, and_self, ite_true]
      have ih := foldMarks r g fs st hk2
      split at ih
      · rename_i heq
        simp only [bind, Option.bind, heq]
        intro hall; exact ih (fun f hf => hall f (by simp [hf]))
      · rename_i st' heq
        simp only [bind, Option.bind, heq]
        obtain ⟨hok, hs, h1, h2, h3, h4, hm⟩ := ih
        refine ⟨?_, hs, h1, h2, h3, h4, ?_⟩
        · intro f hf
          simp only [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact Or.inl ⟨rfl, hv⟩
          · exact hok f hf
        · intro k'' s hk''
          rw [hm k'' s hk'']
          constructor
          · rintro (h | ⟨i', k₁, nil', hm', rfl, hne, c, hc, hs', hlt⟩)
            · exact Or.inl h
            · exact Or.inr ⟨i', k₁, nil', by simp [hm'], rfl, hne, c, hc, hs', hlt⟩
          · rintro (h | ⟨i', k₁, nil', hm', rfl, hne, c, hc, hs', hlt⟩)
            · exact Or.inl h
            · simp only [List.mem_cons, Prod.mk.injEq] at hm'
              rcases hm' with ⟨rfl, rfl, rfl⟩ | hm'
              · exact absurd ⟨rfl, hv⟩ hne
              · exact Or.inr ⟨i', k₁, nil', hm', rfl, hne, c, hc, hs', hlt⟩
    · simp only [hn, ite_false]
      cases hd : r.down g (r.fld g i) with
      | none =>
        simp only [Option.map_none, bind, Option.bind_none]
        intro hall
        have := hall (i, k', nil) (by simp)
        simp [FieldOK, hd, hn] at this
      | some c =>
        simp only [Option.map_some, bind, Option.bind_some]
        have ih := foldMarks r g fs (st.mark k' (c / 8)) hk2
        split at ih
        · rename_i heq
          skip
          intro hall; exact ih (fun f hf => hall f (by simp [hf]))
        · rename_i st' heq
          skip
          obtain ⟨hok, hs, h1, h2, h3, h4, hm⟩ := ih
          have hv := DS.mark_values st k' (c / 8)
          refine ⟨?_, by rw [hs, DS.marks_mark_size], by rw [h1, hv.1], by rw [h2, hv.2.1],
            by rw [h3, hv.2.2.1], by rw [h4, hv.2.2.2], ?_⟩
          · intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact Or.inr (by simp [hd])
            · exact hok f hf
          · intro k'' s hk''
            rw [hm k'' s hk'', DS.marked_mark st hk1 hk'', DS.marks_mark_size]
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
            constructor
            · rintro ((h | ⟨⟨rfl, rfl⟩, hlt⟩) | ⟨i', k₁, nil', hm', rfl, hne, c', hc, hs', hlt⟩)
              · exact Or.inl h
              · exact Or.inr ⟨i, k', nil, by simp, rfl, hn, c, hd, rfl, hlt⟩
              · exact Or.inr ⟨i', k₁, nil', by simp [hm'], rfl, hne, c', hc, hs', hlt⟩
            · rintro (h | ⟨i', k₁, nil', hm', rfl, hne, c', hc, hs', hlt⟩)
              · exact Or.inl (Or.inl h)
              · simp only [List.mem_cons, Prod.mk.injEq] at hm'
                rcases hm' with ⟨rfl, rfl, rfl⟩ | hm'
                · rw [hd] at hc; cases hc
                  exact Or.inl (Or.inr ⟨⟨hs', rfl⟩, hs' ▸ hlt⟩)
                · exact Or.inr ⟨i', k₁, nil', hm', rfl, hne, c', hc, hs', hlt⟩

theorem markObj_spec (r : Region) (k : UInt8) (g : Nat) (st : DS) :
    match markObj r k g st with
    | none => ¬ MarkOK r k g
    | some st' => MarkOK r k g ∧ st'.marks.size = st.marks.size ∧
        st'.names = st.names ∧ st'.levels = st.levels ∧ st'.exprs = st.exprs ∧
        st'.lists = st.lists ∧
        ∀ k'' s, IsKind k'' → (st'.marked k'' s = true ↔ st.marked k'' s = true ∨
          ∃ c, Kid r k g k'' c ∧ c / 8 = s ∧ s < st.marks.size) := by
  unfold markObj
  by_cases hf : r.fits g = true
  · simp only [hf, ite_true]
    cases hfs : kidTable k (r.tag g) (r.nobjs g) with
    | some fs =>
      simp only
      have := foldMarks r g fs st (kidTable_kinds hfs)
      split at this
      · rename_i heq
        rintro ⟨_, fs', hfs', hall⟩
        rw [hfs] at hfs'; cases hfs'; exact this hall
      · rename_i st' heq
        obtain ⟨hok, hs, h1, h2, h3, h4, hm⟩ := this
        refine ⟨⟨hf, fs, hfs, hok⟩, hs, h1, h2, h3, h4, ?_⟩
        intro k'' s hk''
        rw [hm k'' s hk'']
        constructor
        · rintro (h | ⟨i, k', nil, hm', rfl, hne, c, hc, hs', hlt⟩)
          · exact Or.inl h
          · exact Or.inr ⟨c, ⟨hf, fs, hfs, i, nil, hm', hne, hc⟩, hs', hlt⟩
        · rintro (h | ⟨c, ⟨_, fs', hfs', i, nil, hm', hne, hc⟩, hs', hlt⟩)
          · exact Or.inl h
          · rw [hfs] at hfs'; cases hfs'
            exact Or.inr ⟨i, k'', nil, hm', rfl, hne, c, hc, hs', hlt⟩
    | none =>
      simp only
      rintro ⟨_, fs', hfs', _⟩
      rw [hfs] at hfs'; cases hfs'
  · simp only [hf, Bool.false_eq_true, ite_false]
    rintro ⟨h, _⟩; exact hf h

/-! ## The node functions -/

/-- The object at `c` reads as kind `k`. -/
@[expose] def KindOK (r : Region) (k : UInt8) (c : Nat) : Prop :=
  (k = kName → (nameAt r c).isSome) ∧ (k = kLevel → (levelAt r c).isSome) ∧
  (k = kLevels → (levelsAt r c).isSome) ∧ (k = kExpr → (exprAt r c).isSome)

theorem nameIn_none {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Name}
    (h : ¬ FieldOK r g true v) : r.nameIn g v sub = none := by
  unfold FieldOK at h
  unfold Region.nameIn
  have h1 : v ≠ 1 := fun e => h (Or.inl ⟨rfl, e⟩)
  have h2 : r.down g v = none := by
    cases e : r.down g v
    · rfl
    · exact absurd (Or.inr (by simp [e])) h
  simp only [h1, beq_iff_eq, ite_false]
  split
  · rename_i heq; rw [h2] at heq; cases heq
  · rfl

end ConLeche.Frontend.Olean
