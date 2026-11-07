module
public import ConLeche.Verify.Driver.Provenance
import ConLeche.Verify.Frontend.Olean.GroupSame
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Sparse
import ConLeche.Verify.Frontend.Olean.Group

public section
namespace ConLeche.Driver
open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean ConLeche.Cached

theorem lookTable_mem {t : NamePositions} {x : Name} {q : NamePosition}
    (h : (lookTable t)[x]? = some q) : q ∈ t.consts ∧ q.name = x := by
  unfold lookTable at h
  rw [← Array.foldl_toList] at h
  suffices H : ∀ (l : List NamePosition) (m : Std.HashMap Name NamePosition),
      (∀ x q, m[x]? = some q → q ∈ t.consts ∧ q.name = x) → (∀ q ∈ l, q ∈ t.consts) →
      ∀ x q, (l.foldl (fun (m : Std.HashMap Name NamePosition) q => m.insert q.name q) m)[x]? = some q →
        q ∈ t.consts ∧ q.name = x from
    H _ _ (fun x q h => by simp at h) (fun q hq => by simpa using hq) x q h
  intro l
  induction l with
  | nil => intro m h1 _; exact h1
  | cons p l ih =>
    intro m h1 h2
    simp only [List.foldl_cons]
    refine ih _ (fun x q hq => ?_) (fun q hq => h2 q (List.mem_cons_of_mem _ hq))
    rw [Std.HashMap.getElem?_insert] at hq
    split at hq
    · rename_i he
      cases hq
      exact ⟨h2 _ List.mem_cons_self, eq_of_beq he⟩
    · exact h1 x q hq

/-- The recursor of the block whose first member is `x` at location `l`, by its kind. -/
def recAt (x : Name) (l : Nat) : CKindF Name Unit → Option Nat
  | .recur (a :: _) .. => if a == x then some l else none
  | _ => none

theorem recBlocks_fold (x : Name)
    (F : Std.HashMap Name (Array Nat) → Nat × CKindF Name Unit → Std.HashMap Name (Array Nat))
    (hF : ∀ m p, (((F m p)[x]?).getD #[]).toList = ((m[x]?).getD #[]).toList ++ (recAt x p.1 p.2).toList) :
    ∀ (ks : List (Nat × CKindF Name Unit)) (m : Std.HashMap Name (Array Nat)),
    (((ks.foldl F m)[x]?).getD #[]).toList =
      ((m[x]?).getD #[]).toList ++ ks.filterMap (fun p => recAt x p.1 p.2)
  | [], m => by simp
  | p :: ks, m => by
    simp only [List.foldl_cons, List.filterMap_cons]
    rw [recBlocks_fold x F hF ks, hF]
    cases recAt x p.1 p.2 <;> simp

/-- **A part's recursors under `x`**: its recursor positions, in its order, whose block's first
member is `x`; every recursor position's kind read. -/
theorem recBlocksAt_spec {r : Region} {t : NamePositions} {rb : Std.HashMap Name (Array Nat)}
    (h : recBlocksAt r t = some rb) (x : Name) :
    (∀ l ∈ (t.consts.filter (·.tag == 7)).toList.map (·.loc), (kindNamesAt r l).isSome) ∧
    ((rb[x]?).getD #[]).toList = ((t.consts.filter (·.tag == 7)).toList.map (·.loc)).filterMap
      (fun l => (kindNamesAt r l).bind (recAt x l)) := by
  unfold recBlocksAt at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨ks, hks, rfl⟩ := h
  have hf := mapM_forall₂' hks
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨y, -, hy⟩ := Forall₂.mem_left hf l hl
    cases hk : kindNamesAt r l with
    | none => rw [hk] at hy; cases hy
    | some _ => rfl
  · rw [recBlocks_fold x _ (by
      rintro m ⟨l, k⟩
      cases k with
      | recur all np ni nmo nmi rules kk iu =>
        cases all with
        | nil => simp [recAt]
        | cons a rest =>
          simp only [recAt]
          rw [Std.HashMap.getElem?_alter]
          by_cases hax : a = x
          · subst hax
            simp only [beq_self_eq_true, ↓reduceIte]
            cases m[a]? <;> simp
          · have : (a == x) = false := beq_eq_false_iff_ne.2 hax
            simp [this]
      | _ => simp [recAt])]
    simp only [Std.HashMap.getElem?_empty, Option.getD_none, List.nil_append]
    rw [mapM_filterMap (fun p => recAt x p.1 p.2) hks]
    congr 1
    funext l
    cases kindNamesAt r l <;> rfl

theorem nodup_map_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: l, hnd, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (hab ▸ List.mem_map_of_mem hb') hnd.1
    · subst hb'; exact absurd (hab.symm ▸ List.mem_map_of_mem ha') hnd.1
    · exact nodup_map_inj hnd.2 ha' hb' hab

/-- **The constant at a name position**: its name, kind tag and filter the position's. -/
theorem entry_at_pos {r : Region} {a : UInt64} {t : NamePositions} (ht : namePositionsAt r a = some t)
    {q : NamePosition} (hq : q ∈ t.consts) {e : CEntryF Name Expr} (he : entryAt r q.loc = some e) :
    e.name = q.name ∧ e.kind.tag = q.tag ∧ e.kind.skipped = q.skipped := by
  obtain ⟨sk, -, -, hall⟩ := namePositionsAt_mem ht
  obtain ⟨-, s, hs, hn, htg, hsk⟩ := hall q hq
  rw [entryAt_eq] at he
  obtain ⟨s', hs', hm⟩ := constSpec_parts he
  rw [hs] at hs'
  cases hs'
  obtain ⟨h1, -, -, h4, h5⟩ := CEntryF.mapM_parts hm
  rw [hn] at h1
  exact ⟨(Option.some.inj h1).symm, by rw [htg, h4], by rw [hsk, h5]⟩

/-- A constant read at one of a part's name positions. -/
@[expose] def Here (r : Region) (t : NamePositions) (e : CEntryF Name Expr) : Prop :=
  ∃ q ∈ t.consts, entryAt r q.loc = some e

/-- **Constants of one name at a part's positions are one constant.** -/
theorem here_unique {r : Region} {a : UInt64} {t : NamePositions} (ht : namePositionsAt r a = some t)
    {e₁ e₂ : CEntryF Name Expr} (h₁ : Here r t e₁) (h₂ : Here r t e₂) (hn : e₁.name = e₂.name) :
    e₁ = e₂ := by
  obtain ⟨q₁, hq₁, he₁⟩ := h₁
  obtain ⟨q₂, hq₂, he₂⟩ := h₂
  obtain ⟨-, -, hnd, -⟩ := namePositionsAt_mem ht
  have hq : q₁ = q₂ := nodup_map_inj hnd (Array.mem_toList_iff.2 hq₁) (Array.mem_toList_iff.2 hq₂)
    (by rw [← (entry_at_pos ht hq₁ he₁).1, ← (entry_at_pos ht hq₂ he₂).1, hn])
  subst hq
  rw [he₁] at he₂
  exact Option.some.inj he₂
