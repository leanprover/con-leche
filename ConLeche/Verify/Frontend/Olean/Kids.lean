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
@[expose] def markObj (r : Region) (k : UInt8) (g : Nat) (m : ByteArray) : ByteArray :=
  if r.fits g then
    match kidTable k (r.tag g) (r.nobjs g) with
    | some fs => fs.foldl (fun m f => markPtr r m g f.2.1 f.2.2 (r.fld g f.1)) m
    | none => failM m
  else failM m

theorem markName_eq (r : Region) (g : Nat) (m : ByteArray) : markName r g m = markObj r kName g m := by
  unfold markName markObj
  split
  · simp only [kidTable, ite_true]
    split <;> simp_all [List.foldl, nameKids]
  · rfl

theorem markLevel_eq (r : Region) (g : Nat) (m : ByteArray) :
    markLevel r g m = markObj r kLevel g m := by
  unfold markLevel markObj
  split
  · simp only [kidTable, show kLevel ≠ kName by decide, ite_false, ite_true]
    split <;> simp_all [List.foldl, levelKids]
  · rfl

theorem markLevels_eq (r : Region) (g : Nat) (m : ByteArray) :
    markLevels r g m = markObj r kLevels g m := by
  unfold markLevels markObj
  split
  · simp only [kidTable, show kLevels ≠ kName by decide, show kLevels ≠ kLevel by decide,
      ite_false, ite_true]
    split <;> simp_all [List.foldl, levelsKids]
  · rfl

theorem markExpr_eq (r : Region) (g : Nat) (m : ByteArray) :
    markExpr r g m = markObj r kExpr g m := by
  unfold markExpr markObj
  split
  · simp only [kidTable, show kExpr ≠ kName by decide, show kExpr ≠ kLevel by decide,
      show kExpr ≠ kLevels by decide, ite_false]
    split <;> simp_all [List.foldl, exprKids]
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

theorem markPtr_eq (r : Region) (g : Nat) (k : UInt8) (nil : Bool) (v : UInt64)
    (m : ByteArray) :
    markPtr r m g k nil v =
      if nil = true ∧ v = 1 then m else
        match r.down g v with
        | some c => mark m k (c / 8)
        | none => failM m := by
  unfold markPtr
  by_cases h : nil = true ∧ v = 1
  · simp [h]
  · have : (nil && v == 1) = false := by
      cases nil <;> simp_all
    simp only [this, Bool.false_eq_true, ite_false, h]
    rfl

/-- A failed marking stays failed. -/
theorem foldMarks_failed (r : Region) (g : Nat) :
    ∀ (fs : List (Nat × UInt8 × Bool)) (st : ByteArray), (∀ f ∈ fs, IsKind f.2.1) →
    0 < st.size → failedM st = true →
    failedM (fs.foldl (fun m f => markPtr r m g f.2.1 f.2.2 (r.fld g f.1)) st) = true
  | [], _, _, _, h => h
  | (i, k', nil) :: fs, st, hk, hs, h => by
    have hk1 : IsKind k' := hk (i, k', nil) List.mem_cons_self
    have hk2 : ∀ f ∈ fs, IsKind f.2.1 := fun f hf => hk f (List.mem_cons_of_mem _ hf)
    simp only [List.foldl_cons]
    rw [markPtr_eq]
    split
    · exact foldMarks_failed r g fs st hk2 hs h
    · split
      · exact foldMarks_failed r g fs _ hk2 (by rw [size_mark]; exact hs)
          (by rw [failedM_mark _ hk1]; exact h)
      · exact foldMarks_failed r g fs _ hk2 (by rw [size_failM]; exact hs) (failedM_failM hs)

theorem size_foldMarks (r : Region) (g : Nat) :
    ∀ (fs : List (Nat × UInt8 × Bool)) (st : ByteArray),
    (fs.foldl (fun m f => markPtr r m g f.2.1 f.2.2 (r.fld g f.1)) st).size = st.size
  | [], _ => rfl
  | (i, k', nil) :: fs, st => by
    simp only [List.foldl_cons]
    rw [size_foldMarks r g fs, markPtr_eq]
    split
    · rfl
    · split
      · exact size_mark _ _ _
      · exact size_failM _

/-- What a fold of marks does: from a marking that has not failed, it
fails iff a field is not fine, and otherwise adds exactly the marks of
the fields' objects. -/
theorem foldMarks (r : Region) (g : Nat) :
    ∀ (fs : List (Nat × UInt8 × Bool)) (st : ByteArray), (∀ f ∈ fs, IsKind f.2.1) →
    0 < st.size → failedM st = false →
    let st' := fs.foldl (fun m f => markPtr r m g f.2.1 f.2.2 (r.fld g f.1)) st
    (failedM st' = true ↔ ¬ ∀ f ∈ fs, FieldOK r g f.2.2 (r.fld g f.1)) ∧
    (failedM st' = false →
        ∀ k'' s, IsKind k'' → (marked st' k'' s = true ↔ marked st k'' s = true ∨
          ∃ i k' nil, (i, k', nil) ∈ fs ∧ k' = k'' ∧ ¬(nil = true ∧ r.fld g i = 1) ∧
            ∃ c, r.down g (r.fld g i) = some c ∧ c / 8 = s ∧ s < st.size))
  | [], st, _, _, h => by simp [h]
  | (i, k', nil) :: fs, st, hk, hs, hf => by
    have hk1 : IsKind k' := hk (i, k', nil) List.mem_cons_self
    have hk2 : ∀ f ∈ fs, IsKind f.2.1 := fun f hf => hk f (List.mem_cons_of_mem _ hf)
    intro st'
    simp only [st', List.foldl_cons]
    rw [markPtr_eq]
    by_cases hn : nil = true ∧ r.fld g i = 1
    · obtain ⟨rfl, hv⟩ := hn
      simp only [hv, and_self, ite_true]
      obtain ⟨ih1, ih2⟩ := foldMarks r g fs st hk2 hs hf
      refine ⟨?_, ?_⟩
      · rw [ih1]
        constructor
        · intro h hall; exact h (fun f hf => hall f (List.mem_cons_of_mem _ hf))
        · intro h hall; apply h; intro f hf
          simp only [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact Or.inl ⟨rfl, hv⟩
          · exact hall f hf
      · intro hnf k'' s hk''
        rw [ih2 hnf k'' s hk'']
        constructor
        · rintro (h | ⟨i', k₁, nil', hm', rfl, hne, c, hc, hs', hlt⟩)
          · exact Or.inl h
          · exact Or.inr ⟨i', k₁, nil', List.mem_cons_of_mem _ hm', rfl, hne, c, hc, hs', hlt⟩
        · rintro (h | ⟨i', k₁, nil', hm', rfl, hne, c, hc, hs', hlt⟩)
          · exact Or.inl h
          · simp only [List.mem_cons, Prod.mk.injEq] at hm'
            rcases hm' with ⟨rfl, rfl, rfl⟩ | hm'
            · exact absurd ⟨rfl, hv⟩ hne
            · exact Or.inr ⟨i', k₁, nil', hm', rfl, hne, c, hc, hs', hlt⟩
    · simp only [hn, ite_false]
      cases hd : r.down g (r.fld g i) with
      | none =>
        simp only
        have hfail := foldMarks_failed r g fs (failM st) hk2 (by rw [size_failM]; exact hs)
          (failedM_failM hs)
        refine ⟨?_, fun h => by rw [hfail] at h; cases h⟩
        simp only [hfail, true_iff]
        intro hall
        have := hall (i, k', nil) List.mem_cons_self
        simp [FieldOK, hd, hn] at this
      | some c =>
        simp only
        have hs1 : 0 < (mark st k' (c / 8)).size := by rw [size_mark]; exact hs
        have hf1 : failedM (mark st k' (c / 8)) = false := by rw [failedM_mark _ hk1]; exact hf
        obtain ⟨ih1, ih2⟩ := foldMarks r g fs (mark st k' (c / 8)) hk2 hs1 hf1
        refine ⟨?_, ?_⟩
        · rw [ih1]
          constructor
          · intro h hall; exact h (fun f hf => hall f (List.mem_cons_of_mem _ hf))
          · intro h hall; apply h; intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | hf
            · exact Or.inr (by simp [hd])
            · exact hall f hf
        · intro hnf k'' s hk''
          rw [ih2 hnf k'' s hk'', marked_mark st hk1 hk'', size_mark]
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          constructor
          · rintro ((h | ⟨⟨rfl, rfl⟩, hlt⟩) | ⟨i', k₁, nil', hm', rfl, hne, c', hc, hs', hlt⟩)
            · exact Or.inl h
            · exact Or.inr ⟨i, k', nil, List.mem_cons_self, rfl, hn, c, hd, rfl, hlt⟩
            · exact Or.inr ⟨i', k₁, nil', List.mem_cons_of_mem _ hm', rfl, hne, c', hc, hs', hlt⟩
          · rintro (h | ⟨i', k₁, nil', hm', rfl, hne, c', hc, hs', hlt⟩)
            · exact Or.inl (Or.inl h)
            · simp only [List.mem_cons, Prod.mk.injEq] at hm'
              rcases hm' with ⟨rfl, rfl, rfl⟩ | hm'
              · rw [hd] at hc; cases hc
                exact Or.inl (Or.inr ⟨⟨hs', rfl⟩, hs' ▸ hlt⟩)
              · exact Or.inr ⟨i', k₁, nil', hm', rfl, hne, c', hc, hs', hlt⟩

theorem size_markObj (r : Region) (k : UInt8) (g : Nat) (st : ByteArray) :
    (markObj r k g st).size = st.size := by
  unfold markObj
  split
  · split
    · exact size_foldMarks r g _ st
    · exact size_failM st
  · exact size_failM st

theorem markObj_failed (r : Region) (k : UInt8) (g : Nat) (st : ByteArray) (hs : 0 < st.size)
    (hf : failedM st = true) : failedM (markObj r k g st) = true := by
  unfold markObj
  split
  · split
    · rename_i fs hfs; exact foldMarks_failed r g fs st (kidTable_kinds hfs) hs hf
    · exact failedM_failM hs
  · exact failedM_failM hs

theorem markObj_spec (r : Region) (k : UInt8) (g : Nat) (st : ByteArray) (hs : 0 < st.size)
    (hf : failedM st = false) :
    (failedM (markObj r k g st) = true ↔ ¬ MarkOK r k g) ∧
    (failedM (markObj r k g st) = false →
        ∀ k'' s, IsKind k'' → (marked (markObj r k g st) k'' s = true ↔ marked st k'' s = true ∨
          ∃ c, Kid r k g k'' c ∧ c / 8 = s ∧ s < st.size)) := by
  unfold markObj
  by_cases hfit : r.fits g = true
  · simp only [hfit, ite_true]
    cases hfs : kidTable k (r.tag g) (r.nobjs g) with
    | some fs =>
      simp only
      obtain ⟨h1, h2⟩ := foldMarks r g fs st (kidTable_kinds hfs) hs hf
      refine ⟨?_, ?_⟩
      · rw [h1]
        constructor
        · intro h ⟨_, fs', hfs', hall⟩
          rw [hfs] at hfs'; cases hfs'; exact h hall
        · intro h hall; exact h ⟨hfit, fs, hfs, hall⟩
      · intro hnf k'' s hk''
        rw [h2 hnf k'' s hk'']
        constructor
        · rintro (h | ⟨i, k', nil, hm', rfl, hne, c, hc, hs', hlt⟩)
          · exact Or.inl h
          · exact Or.inr ⟨c, ⟨hfit, fs, hfs, i, nil, hm', hne, hc⟩, hs', hlt⟩
        · rintro (h | ⟨c, ⟨_, fs', hfs', i, nil, hm', hne, hc⟩, hs', hlt⟩)
          · exact Or.inl h
          · rw [hfs] at hfs'; cases hfs'
            exact Or.inr ⟨i, k'', nil, hm', rfl, hne, c, hc, hs', hlt⟩
    | none =>
      simp only [failedM_failM hs, true_iff]
      refine ⟨?_, fun h => by cases h⟩
      rintro ⟨_, fs', hfs', _⟩
      rw [hfs] at hfs'; cases hfs'
  · simp only [hfit, Bool.false_eq_true, ite_false, failedM_failM hs, true_iff]
    refine ⟨?_, fun h => by cases h⟩
    rintro ⟨h, _⟩; exact hfit h

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
