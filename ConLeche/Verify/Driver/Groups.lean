module
public import ConLeche.Verify.Driver.Provenance
public import ConLeche.Verify.Frontend.Olean.GroupSame
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

/-- The home's private name table is its private view's. -/
theorem home_table {sp : SearchPath} {fs : FS} {h : Name} {f : ModFiles} {r : Region} {a : UInt64}
    (hf : (readFiles sp h .private : ModelIO _) fs (.ok (.ok f))) (hreg : f.viewRegion .private = some (r, a))
    {t : NamePositions} (ht : PartNames sp fs ⟨h, .private⟩ t) : namePositionsAt r a = some t := by
  have hnt := readPartNames_of_all hf ht
  simpa only [ModFiles.upTo, readNamePositions, hreg, Option.bind_eq_bind, Option.bind_some] using hnt

/-- **A constant at a home's private name position, not filtered out and no theorem, is the
constant its merge holds under its name.** -/
theorem home_lookup {w : WorkerRead} {r : Region} {a : UInt64} {sk : ModSkel} {t : NamePositions}
    (hsk : moduleSkel r a = some sk) (ht : namePositionsAt r a = some t)
    (hown : ∀ loc s, loc ∈ sk.consts → constSkel r loc = some s → s.kind.skipped = false →
        ∃ E e₁, lazyEntry (nameP r) (exprP r) r 0 s = some E ∧
          (homeMerged w).map[E.name]? = some e₁ ∧ e₁.toCEntryF = E)
    {e : CEntryF Name Expr} (he : Here r t e) (hsk0 : e.kind.skipped = false) (htag : e.kind.tag ≠ 2) :
    ∃ eH, (homeMerged w).map[e.name]? = some eH ∧ eH.toCEntryF = e := by
  obtain ⟨q, hq, hqe⟩ := he
  obtain ⟨sk', hsk', -, hall⟩ := namePositionsAt_mem ht
  rw [hsk] at hsk'; cases hsk'
  obtain ⟨hloc, s, hs, -, -, hskq⟩ := hall q hq
  have hskp : s.kind.skipped = false := by
    rw [← hskq, ← (entry_at_pos ht hq hqe).2.2, hsk0]
  obtain ⟨E, e₁, hE, he₁, hee⟩ := hown q.loc s hloc hs hskp
  obtain rfl := lazyEntry_entryAt hs hE hqe htag
  exact ⟨e₁, he₁, hee⟩

/-- A recursor read whole and read for its names only: one block. -/
theorem recur_kindNames {r : Region} {l : Nat} {s : CEntryF UInt64 UInt64} {E : CEntryF Name Expr}
    (hs : constSkel r l = some s) (hE : lazyEntry (nameP r) (exprP r) r 0 s = some E)
    {all : List Name} {np ni nmo nmi : Nat} {rules : List (Name × Nat × Expr)} {k iu : Bool}
    (hk : E.kind = .recur all np ni nmo nmi rules k iu) {k' : CKindF Name Unit}
    (hk' : kindNamesAt r l = some k') : ∃ rules', k' = .recur all np ni nmo nmi rules' k iu := by
  simp only [kindNamesAt, hs, Option.bind_eq_bind, Option.bind_some, show sparseNameP r = nameP r from
    funext (sparseNameP_eq r)] at hk'
  rcases s with ⟨sn, sl, st, sk0⟩
  cases sk0 with
  | recur allP np' ni' nmo' nmi' rulesP k0 iu0 =>
    simp only [lazyEntry, CEntryF.mapM, CKindF.mapM] at hE
    simp only [CKindF.mapM] at hk'
    obtain ⟨_, -, hE⟩ := bind_some_left hE
    obtain ⟨_, -, hE⟩ := bind_some_left hE
    obtain ⟨_, -, hE⟩ := bind_some_left hE
    obtain ⟨kk, hkk, hE⟩ := bind_some_left hE
    simp only [pure, Option.some.injEq] at hE
    subst hE
    simp only at hk
    subst hk
    obtain ⟨a1, ha1, hkk⟩ := bind_some_left hkk
    obtain ⟨_, -, hkk⟩ := bind_some_left hkk
    simp only [pure, Option.some.injEq, CKindF.recur.injEq] at hkk
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ := hkk
    obtain ⟨a2, ha2, hk'⟩ := bind_some_left hk'
    obtain ⟨r2, -, hk'⟩ := bind_some_left hk'
    simp only [pure, Option.some.injEq] at hk'
    rw [ha1] at ha2; cases ha2
    exact ⟨r2, hk'.symm⟩
  | thm v a0 =>
    simp only [lazyEntry] at hE
    split at hE
    rotate_left
    · cases hE
    repeat (obtain ⟨_, -, hE⟩ := bind_some_left hE)
    simp only [pure, Option.some.injEq] at hE
    subst hE
    cases hk
  | _ =>
    simp only [lazyEntry] at hE
    obtain ⟨-, -, -, h4, -⟩ := CEntryF.mapM_parts hE
    rw [hk] at h4
    simp [CKindF.tag] at h4

theorem filter_filter_map {α β : Type} (p q : α → Bool) (f : α → β) :
    ∀ l : List α, ((l.filter p).filter q).map f = l.filterMap (fun x => if p x && q x then some (f x) else none)
  | [] => rfl
  | x :: l => by
    have ih := filter_filter_map p q f l
    cases hp : p x <;> cases hq : q x <;>
      simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, Bool.and_self,
        Bool.and_false, Bool.false_and, List.map_cons, List.filterMap_cons, ih]

theorem filterMap_filter_map {α β γ : Type} (p : α → Bool) (g : α → β) (G : β → Option γ) :
    ∀ l : List α, ((l.filter p).map g).filterMap G = l.filterMap (fun x => if p x then G (g x) else none)
  | [] => rfl
  | x :: l => by
    simp only [List.filter_cons, List.filterMap_cons]
    by_cases hp : p x = true
    · simp only [hp, ↓reduceIte, List.map_cons, List.filterMap_cons, filterMap_filter_map p g G l]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, filterMap_filter_map p g G l]

/-- **A home's private name position and its constant**: the skeleton there, its kind's tag and
filter the position's, and the constant the load read off it. -/
@[expose] def RowOK (r : Region) (q : NamePosition) (e : CEntry) : Prop :=
  ∃ s, constSkel r q.loc = some s ∧ nameP r s.name = some q.name ∧ q.tag = s.kind.tag ∧
    q.skipped = s.kind.skipped ∧ lazyEntry (nameP r) (exprP r) r 0 s = some e.toCEntryF

/-- **A group's recursors, read from its home's private part, are its home's in its home's
order**: the recursor positions whose block's first member is the group's, of the group's block
(`P`), are, constant by constant, the home's constants not filtered out that are recursors of a
block listing `n`. -/
theorem recs_same {r : Region} {a : UInt64} {t : NamePositions} (ht : namePositionsAt r a = some t)
    {consts : List CEntry} (hrow : Forall₂ (RowOK r) t.consts.toList consts)
    {all : List Name} {n : Name} (hn : n ∈ all) {rb : Std.HashMap Name (Array Nat)}
    (hrb : recBlocksAt r t = some rb) {restR : List (CEntryF Name Expr)}
    (hrestR : (groupRecLocs rb all).mapM (entryAt r) = some restR) (P : CEntryF Name Expr → Bool)
    (hP : ∀ e : CEntryF Name Expr, ∀ all' np ni nmo nmi rules k iu,
      e.kind = .recur all' np ni nmo nmi rules k iu → P e = (all' == all))
    (hval : ∀ e ∈ restR.filter P, e.kind.skipped = false)
    (hhome : ∀ e ∈ consts, e.skipped = false → ∀ all' np ni nmo nmi rules k iu,
      e.kind = .recur all' np ni nmo nmi rules k iu → n ∈ all' → all' = all) :
    ((consts.filter (fun e => !e.skipped)).filter (recUnder n)).map (·.toCEntryF) = restR.filter P := by
  obtain ⟨a0, rest0, rfl⟩ : ∃ a0 rest0, all = a0 :: rest0 := by
    cases all with
    | nil => cases hn
    | cons a0 rest0 => exact ⟨a0, rest0, rfl⟩
  obtain ⟨hkn, hrbx⟩ := recBlocksAt_spec hrb a0
  have hlocs : groupRecLocs rb (a0 :: rest0) = t.consts.toList.filterMap (fun q =>
      if q.tag == 7 then (kindNamesAt r q.loc).bind (recAt a0 q.loc) else none) := by
    simp only [groupRecLocs, List.head?_cons, Option.bind_some]
    rw [hrbx, Array.toList_filter, filterMap_filter_map]
  have hent : ∀ l ∈ groupRecLocs rb (a0 :: rest0), (entryAt r l).isSome := by
    intro l hl
    obtain ⟨y, -, hy⟩ := mapM_mem hrestR hl
    rw [hy]; rfl
  have hR : restR.filter P = t.consts.toList.filterMap (fun q =>
      (((if q.tag == 7 then (kindNamesAt r q.loc).bind (recAt a0 q.loc) else none).bind
        (entryAt r)).filter P)) := by
    have e1 : restR = (groupRecLocs rb (a0 :: rest0)).filterMap (entryAt r) := by
      have := mapM_filterMap some hrestR
      simpa using this
    rw [e1, hlocs, List.filterMap_filterMap, List.filter_filterMap]
  have hH : ((consts.filter (fun e => !e.skipped)).filter (recUnder n)).map (·.toCEntryF) =
      consts.filterMap (fun e => if !e.skipped && recUnder n e then some e.toCEntryF else none) := by
    exact filter_filter_map _ _ _ consts
  rw [hH, hR]
  symm
  refine filterMap_forall₂ hrow (fun q e hq hec ⟨s, hs, hsn, htg, hskq, hE⟩ => ?_)
  have hEk := lazyEntry_kind hE
  by_cases h7 : q.tag = 7
  · have hq7 : q.loc ∈ (t.consts.filter (·.tag == 7)).toList.map (·.loc) :=
      List.mem_map.2 ⟨q, by simpa [h7] using hq, rfl⟩
    obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 (hkn q.loc hq7)
    have hek : e.kind.tag = 7 := by rw [show e.kind = e.toCEntryF.kind from rfl, hEk.2, ← htg, h7]
    rcases hke : e.kind with _ | _ | _ | _ | _ | _ | _ | ⟨all', np, ni, nmo, nmi, rules, kk, iu⟩
    all_goals try (rw [hke] at hek; simp [CKindF.tag] at hek)
    have hke' : e.toCEntryF.kind = .recur all' np ni nmo nmi rules kk iu := hke
    obtain ⟨rules', rfl⟩ := recur_kindNames hs hE hke' hk'
    simp only [h7, beq_self_eq_true, ↓reduceIte, hk', Option.bind_some, recAt]
    have hRU : recUnder n e = all'.contains n := by simp [recUnder, hke]
    by_cases hall : all' = a0 :: rest0
    · subst hall
      simp only [beq_self_eq_true, ↓reduceIte, Option.bind_some]
      have hsel : q.loc ∈ groupRecLocs rb (a0 :: rest0) := by
        rw [hlocs]
        exact List.mem_filterMap.2 ⟨q, hq, by simp [h7, hk', recAt]⟩
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 (hent q.loc hsel)
      have hee : e.toCEntryF = e' := lazyEntry_entryAt hs hE he' (by rw [(entry_at_pos ht (Array.mem_toList_iff.1 hq) he').2.1, h7]; decide)
      rw [he', ← hee]
      have hPe : P e.toCEntryF = true := by rw [hP _ _ _ _ _ _ _ _ _ hke']; simp
      have hmem : e.toCEntryF ∈ restR.filter P := by
        rw [hR]
        refine List.mem_filterMap.2 ⟨q, hq, ?_⟩
        simp [h7, hk', recAt, he', ← hee, hPe]
      have hsk := hval _ hmem
      have hsk' : e.skipped = false := hsk
      simp [Option.filter, hPe, hsk', hRU, hn]
    · have hH0 : (!e.skipped && recUnder n e) = false := by
        rw [hRU]
        cases hsk : e.skipped
        · cases hc : all'.contains n
          · rfl
          · exact absurd (hhome e hec hsk _ _ _ _ _ _ _ _ hke (by simpa using hc)) hall
        · rfl
      rw [hH0]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases all' with
      | nil => rfl
      | cons b rest' =>
        simp only
        by_cases hb : b = a0
        · subst hb
          simp only [beq_self_eq_true, ↓reduceIte, Option.bind_some]
          cases he' : entryAt r q.loc with
          | none => rfl
          | some e' =>
            have hee : e.toCEntryF = e' := lazyEntry_entryAt hs hE he' (by rw [(entry_at_pos ht (Array.mem_toList_iff.1 hq) he').2.1, h7]; decide)
            subst hee
            have hPe : P e.toCEntryF = false := by
              rw [hP _ _ _ _ _ _ _ _ _ hke']; simpa using hall
            simp [Option.filter, hPe]
        · have : (b == a0) = false := beq_eq_false_iff_ne.2 hb
          simp [this]
  · have hne : (q.tag == 7) = false := by simpa using h7
    simp only [hne, Bool.false_eq_true, ↓reduceIte, Option.bind_none, Option.filter_none]
    have hek : e.kind.tag ≠ 7 := by
      rw [show e.kind = e.toCEntryF.kind from rfl, hEk.2, ← htg]; exact h7
    have : recUnder n e = false := by
      unfold recUnder
      split
      · rename_i hke; rw [hke] at hek; exact absurd rfl hek
      · rfl
    simp [this]
