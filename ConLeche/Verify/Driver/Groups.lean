module

public import ConLeche.Verify.Driver.Provenance
public import ConLeche.Verify.Frontend.Olean.GroupSame
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Sparse
import ConLeche.Verify.Frontend.Olean.Group
import ConLeche.Verify.Frontend.Prepare

/-!
# An inductive group read from its home presents its home's record

Task #440, the step task #448 left open.  The reach reads a group from its home's private part
(`GroupRead`): `groupAt`'s reads, the group's members and constructors by name, its recursors
among the part's recursor positions by their block's first member, built alone (`groupRecord`).
Where the worker at the home accepted on the same snapshot, its emission holds the record of that
group (`home_group`), built of the members, constructors and recursors its merge holds; those are,
constant by constant and in order, the ones the reach read (`recs_same` for the recursors: the
private name table's order is the load's), and the builder makes one record of both
(`block_same`).  **`group_presents`**: the group's record is one of its home's own records.

With it, every context record of an accepted worker presents one of its home's own records
(`worker_presented`), and the local checks of the development follow (`interfaceOk_of_workers`,
`presented_of_worker`).
-/

public section

namespace ConLeche.Driver

variable {pins : List NatOpPinSet}

open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean ConLeche.Cached

/-! ## A part's name table and its recursors -/

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
  have hf := mapM_some_forall₂ hks
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

theorem recAt_loc {x : Name} {l l' : Nat} {k : CKindF Name Unit} (h : recAt x l k = some l') : l' = l := by
  unfold recAt at h
  split at h
  · split at h
    · exact (Option.some.inj h).symm
    · cases h
  · cases h

/-- A location `groupRecLocs` gives is a recursor position of the part. -/
theorem groupRecLocs_pos {r : Region} {t : NamePositions} {rb : Std.HashMap Name (Array Nat)}
    (hrb : recBlocksAt r t = some rb) {all : List Name} {l : Nat} (hl : l ∈ groupRecLocs rb all) :
    ∃ q ∈ t.consts, q.tag = 7 ∧ q.loc = l := by
  simp only [groupRecLocs] at hl
  cases hh : all.head? with
  | none => simp [hh] at hl
  | some a0 =>
    simp only [hh, Option.bind_some] at hl
    rw [(recBlocksAt_spec hrb a0).2] at hl
    obtain ⟨l', hl', hsel⟩ := List.mem_filterMap.1 hl
    obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.1 hsel
    obtain rfl := recAt_loc hk
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hl'
    obtain ⟨hq'', h7⟩ := Array.mem_filter.1 (Array.mem_toList_iff.1 hq')
    exact ⟨q', hq'', by simpa using h7, rfl⟩

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

/-! ## The home's private part -/

/-- The home's private name table is its private view's. -/
theorem home_table {sp : Roots} {fs : FS} {h : Name} {f : ModFiles} {r : Region} {a : UInt64}
    (hf : ModelIO.CanGive (readFiles sp h .private) fs (.ok f)) (hreg : f.viewRegion .private = some (r, a))
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

/-- **A home's private name position and its constant**: the skeleton there, its kind's tag and
filter the position's, and the constant the load read off it. -/
@[expose] def RowOK (r : Region) (q : NamePosition) (e : CEntry) : Prop :=
  ∃ s, constSkel r q.loc = some s ∧ nameP r s.name = some q.name ∧ q.tag = s.kind.tag ∧
    q.skipped = s.kind.skipped ∧ lazyEntry (nameP r) (exprP r) r 0 s = some e.toCEntryF

/-- **The home's load is its private name table, position by position.** -/
theorem home_rows {h : Name} {f : ModFiles} {l : Loaded} (hload : LoadOf 0 h f l)
    {r : Region} {a : UInt64} (hreg : f.viewRegion .private = some (r, a)) {t : NamePositions}
    (ht : namePositionsAt r a = some t) : Forall₂ (RowOK r) t.consts.toList l.constants.toList := by
  obtain ⟨r', a', sk, skels, hv', hsk, hskels, hl, hj⟩ := hload.2.1
  rw [hreg] at hv'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv')
  have h1 : Forall₂ (fun s (e : CEntry) => lazyEntry (nameP r) (exprP r) r 0 s = some e.toCEntryF)
      skels l.constants.toList :=
    forall₂_of_getElem (by simpa using hl) (fun j hj' => by simpa using hj j hj')
  have h2 := mapM_some_forall₂ hskels
  simp only [namePositionsAt] at ht
  obtain ⟨sk', hsk', ht⟩ := bind_some_left ht
  rw [hsk] at hsk'; cases hsk'
  obtain ⟨imps, -, ht⟩ := bind_some_left ht
  obtain ⟨cs, hcs, ht⟩ := bind_some_left ht
  split at ht
  rotate_left
  · cases ht
  simp only [pure, Option.some.injEq] at ht
  subst ht
  have h3 := mapM_some_forall₂ hcs
  refine Forall₂.imp (fun q e ⟨s, ⟨loc, hq, hs⟩, hE⟩ => ?_) (forall₂_comp (forall₂_meet_left h3 h2) h1)
  simp only [namePosition] at hq
  obtain ⟨s', hs', hq⟩ := bind_some_left hq
  rw [hs] at hs'; cases hs'
  obtain ⟨nm, hnm, hq⟩ := bind_some_left hq
  simp only [pure, Option.some.injEq] at hq
  subst hq
  exact ⟨s, hs, hnm, rfl, rfl, hE⟩

/-! ## A group's recursors -/

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

/-! ## A group's members and constructors -/

theorem filterMap_toF {l : List Name} {A B : Std.HashMap Name CEntry}
    (h : ∀ x ∈ l, (A[x]?).map (·.toCEntryF) = (B[x]?).map (·.toCEntryF)) :
    (l.filterMap (A[·]?)).map (·.toCEntryF) = (l.filterMap (B[·]?)).map (·.toCEntryF) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x List.mem_cons_self
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.filterMap_cons]
    cases ha : A[x]? <;> cases hb : B[x]? <;> rw [ha, hb] at hx <;> simp at hx
    · exact ih'
    · simp only [List.map_cons, ih', hx]

theorem blockCtors_toF {A B : Merged} :
    ∀ {tA tB : List CEntry}, tA.map (·.toCEntryF) = tB.map (·.toCEntryF) →
      (∀ b ∈ tB, ∀ y np ni all cs nn ir iu irf, b.kind = .induct np ni all cs nn ir iu irf → y ∈ cs →
        (A.map[y]?).map (·.toCEntryF) = (B.map[y]?).map (·.toCEntryF)) →
      (Olean.blockCtors A tA).map (·.toCEntryF) = (Olean.blockCtors B tB).map (·.toCEntryF)
  | [], [], _, _ => rfl
  | x :: tA, y :: tB, he, hc => by
    simp only [List.map_cons, List.cons.injEq] at he
    have ih := blockCtors_toF (A := A) (B := B) he.2
      (fun b hb => hc b (List.mem_cons_of_mem _ hb))
    simp only [Olean.blockCtors, List.flatMap_cons, List.map_append] at ih ⊢
    have hk : x.kind = y.kind := by rw [show x.kind = x.toCEntryF.kind from rfl, he.1]
    rw [ih, hk]
    congr 1
    cases hyk : y.kind with
    | induct np ni all cs nn ir iu irf =>
      exact filterMap_toF (fun z hz => hc y List.mem_cons_self z np ni all cs nn ir iu irf hyk hz)
    | _ => rfl
  | [], _ :: _, he, _ => by simp at he
  | _ :: _, [], he, _ => by simp at he

/-! ## A group read from its home -/

/-- **Every group read from module `h`'s private part presents one of `h`'s own records**: it
is, constant by constant and in the block's order, the record `h`'s emission built of that
group. -/
theorem group_presents {sp : Roots} {fs : FS} {h : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts pins sp fs h jobs w) {n : Name} {d : Declaration}
    (hgr : GroupRead sp fs ⟨h, .private⟩ n d) : ∃ p ∈ w.emitted, Presents d p := by
  obtain ⟨t, q, tE, np, ni, nn, all, cs, ir, iu, irf, mqs, cqs, tys, rest, t', rb, r₁, r₂, r₃, r₄,
    ht, hq, hr₁, htE, hk, hmqs, hr₂, htys, hcqs, ht', hr₃, hrb, hr₄, hrest, hd⟩ := hgr
  obtain ⟨f, r, a, sk, skels, hf, hreg, hsk, hskels, hcn, hcv, hload, hN, hO, hb, hem, hown⟩ :=
    home_records hw
  have hR : PartRegion sp fs ⟨h, .private⟩ r := ⟨f, a, hf, hreg⟩
  obtain rfl := partRegion_unique hf hR hr₁
  obtain rfl := partRegion_unique hf hR hr₂
  obtain rfl := partRegion_unique hf hR hr₃
  obtain rfl := partRegion_unique hf hR hr₄
  have hT := home_table hf hreg ht
  obtain rfl : t = t' := by
    have := home_table hf hreg ht'
    rw [hT] at this
    exact Option.some.inj this
  -- the positions read
  obtain ⟨hqt, hqn⟩ := lookTable_mem hq
  have hEn : tE.name = n := by rw [(entry_at_pos hT hqt htE).1, hqn]
  have hereLook : ∀ {l : List Name} {qs : List NamePosition}, l.mapM ((lookTable t)[·]?) = some qs →
      ∀ q' ∈ qs, q' ∈ t.consts ∧ q'.name ∈ l := by
    intro l qs h q' hq'
    obtain ⟨y, hy, hyq⟩ := mapM_mem_inv h hq'
    obtain ⟨h1, h2⟩ := lookTable_mem hyq
    exact ⟨h1, h2 ▸ hy⟩
  have hereTys : ∀ e ∈ tys, Here r t e ∧ e.name ∈ all := by
    intro e he
    obtain ⟨l, hl, hle⟩ := mapM_mem_inv htys he
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hl
    obtain ⟨h1, h2⟩ := hereLook hmqs q' hq'
    exact ⟨⟨q', h1, hle⟩, (entry_at_pos hT h1 hle).1 ▸ h2⟩
  obtain ⟨restC, restR, hrestC, hrestR, rfl⟩ := mapM_append_inv hrest
  have hereC : ∀ e ∈ restC, Here r t e ∧ e.name ∈ groupCtorNames tys := by
    intro e he
    obtain ⟨l, hl, hle⟩ := mapM_mem_inv hrestC he
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hl
    obtain ⟨h1, h2⟩ := hereLook hcqs q' hq'
    exact ⟨⟨q', h1, hle⟩, (entry_at_pos hT h1 hle).1 ▸ h2⟩
  have hereR : ∀ e ∈ restR, Here r t e ∧ e.kind.tag = 7 := by
    intro e he
    obtain ⟨l, hl, hle⟩ := mapM_mem_inv hrestR he
    obtain ⟨q', hq', h7, rfl⟩ := groupRecLocs_pos hrb hl
    exact ⟨⟨q', hq', hle⟩, by rw [(entry_at_pos hT hq' hle).2.1, h7]⟩
  -- the reach's merge
  obtain ⟨P, hgm, hP⟩ : ∃ P : CEntryF Name Expr → Bool,
      groupMerged tE tys (restC ++ restR) all =
        mergedOfList ((tE :: tys ++ (restC ++ restR).filter P).map CEntry.ofF) ∧
      ∀ e : CEntryF Name Expr, ∀ all' np ni nmo nmi rules k iu,
        e.kind = .recur all' np ni nmo nmi rules k iu → P e = (all' == all) :=
    ⟨_, rfl, fun e all' np ni nmo nmi rules k iu hk => by simp only [hk]⟩
  rw [hgm] at hd
  generalize hLR : (tE :: tys ++ (restC ++ restR).filter P).map CEntry.ofF = LR at hd
  have hLRmem : ∀ e ∈ LR, e = CEntry.ofF e.toCEntryF ∧ (e.toCEntryF = tE ∨ e.toCEntryF ∈ tys ∨
      (e.toCEntryF ∈ restC ∧ P e.toCEntryF = true) ∨ (e.toCEntryF ∈ restR ∧ P e.toCEntryF = true)) := by
    intro e he
    rw [← hLR] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    refine ⟨rfl, ?_⟩
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.filter_append,
      List.mem_filter] at he0
    rcases he0 with rfl | he0 | ⟨he0, hp⟩ | ⟨he0, hp⟩
    · exact .inl rfl
    · exact .inr (.inl he0)
    · exact .inr (.inr (.inl ⟨he0, hp⟩))
    · exact .inr (.inr (.inr ⟨he0, hp⟩))
  have hereLR : ∀ e ∈ LR, Here r t e.toCEntryF := by
    intro e he
    rcases (hLRmem e he).2 with h0 | h0 | ⟨h0, -⟩ | ⟨h0, -⟩
    · rw [h0]; exact ⟨q, hqt, htE⟩
    · exact (hereTys _ h0).1
    · exact (hereC _ h0).1
    · exact (hereR _ h0).1
  have uniqLR : ∀ a ∈ LR, ∀ b ∈ LR, a.name = b.name → a = b := by
    intro a ha b hb hab
    rw [(hLRmem a ha).1, (hLRmem b hb).1, here_unique hT (hereLR a ha) (hereLR b hb) hab]
  have hmapR : ∀ {x : Name} {m : CEntry}, (mergedOfList LR).map[x]? = some m → m ∈ LR ∧ m.name = x :=
    fun {x m} h => ⟨(mergedOfList_spec LR).2.1 x m h, mergedOfList_names LR x m h⟩
  have hstoreR : ∀ e ∈ LR, (mergedOfList LR).map[e.name]? = some e := by
    intro e he
    have hc := (mergedOfList_spec LR).2.2 e he
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hc
    obtain ⟨hm1, hm2⟩ := hmapR hm
    rw [hm, uniqLR m hm1 e he hm2]
  have hheadR : (mergedOfList LR).map[n]? = some (CEntry.ofF tE) := by
    rw [← hEn, ← hLR]
    exact mergedOfList_head _ _
  -- the reach's record, and what its validation says
  obtain ⟨tysR, ctorsR, recsR, ts, cts, rcs, hparts, hdR, g1, g2, g3⟩ := groupRecord_res hd
  obtain ⟨tysR', ctorsR', recsR', hparts', hval⟩ := groupRecord_valid hd
  rw [hparts] at hparts'
  obtain ⟨rfl, rfl, rfl⟩ : tysR = tysR' ∧ ctorsR = ctorsR' ∧ recsR = recsR' := by
    simpa using hparts'
  have hkE : (CEntry.ofF tE).kind = .induct np ni all cs nn ir iu irf := hk
  obtain ⟨rfl, rfl, rfl⟩ : tysR = blockTys (mergedOfList LR) all ∧
      ctorsR = Olean.blockCtors (mergedOfList LR) (blockTys (mergedOfList LR) all) ∧
      recsR = Olean.blockRecs (mergedOfList LR) (recMapOf (mergedOfList LR)) n := by
    simp only [groupParts, hheadR, hkE, Option.some.injEq, Prod.mk.injEq] at hparts
    exact ⟨hparts.1.symm, hparts.2.1.symm, hparts.2.2.symm⟩
  have hvalN := hval n List.mem_cons_self
  have hval' : ∀ e ∈ blockTys (mergedOfList LR) all ++
      Olean.blockCtors (mergedOfList LR) (blockTys (mergedOfList LR) all) ++
      Olean.blockRecs (mergedOfList LR) (recMapOf (mergedOfList LR)) n,
      blockStep (mergedOfList LR) e.name = .ok () :=
    fun e he => hval e.name (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
  obtain ⟨hnall, hmem, -⟩ := blockStep_ind hheadR ⟨_, _, _, _, _, _, hkE⟩ hvalN
  -- no unsafe type
  have hsafe : (CEntry.ofF tE).skipped = false := by
    have hin : CEntry.ofF tE ∈ (blockTys (mergedOfList LR) all).filter (·.kind.tag == 5) :=
      List.mem_filter.2 ⟨List.mem_filterMap.2 ⟨n, hnall, hheadR⟩, by simp [hkE, CKindF.tag]⟩
    obtain ⟨t0, ht0, ⟨-, ni', all', cs', nn', ir', irf', hk0, -⟩⟩ := Forall₂.mem_right g1 _ hin
    have hu : t0.isUnsafe = false := by
      have := declOfF_ind_safe hdR
      rw [List.any_eq_false] at this
      simpa using this t0 ht0
    rw [hkE] at hk0
    obtain ⟨-, -, -, -, -, -, rfl, -⟩ := CKindF.induct.inj hk0
    simp [CEntry.skipped, hkE, CKindF.skipped, hu]
  -- the members, and their constructors
  have hmemb : ∀ x ∈ all, ∃ m cs', (mergedOfList LR).map[x]? = some m ∧ IsInd m all cs' ∧
      m.skipped = false ∧ ∀ y ∈ cs', ∃ m', (mergedOfList LR).map[y]? = some m' ∧ IsCtor m' x ∧
        m'.skipped = false := by
    intro x hx
    obtain ⟨m, cs', hm, him, hms⟩ := hmem x hx
    have hmx := (hmapR hm).2
    have hs := hval' m (List.mem_append_left _ (List.mem_append_left _
      (List.mem_filterMap.2 ⟨x, hx, hm⟩)))
    rw [hmx] at hs
    obtain ⟨-, -, hc⟩ := blockStep_ind hm him hs
    refine ⟨m, cs', hm, him, hms.trans hsafe, fun y hy => ?_⟩
    obtain ⟨m', hm', hic, hs'⟩ := hc y hy
    exact ⟨m', hm', hic, hs'.trans (hms.trans hsafe)⟩
  have hndR : (mergedOfList LR).order.toList.Nodup := by
    obtain ⟨hoR, -⟩ := mergedOfList_firsts LR {} [] (by simp) (by simp)
    have hoR' : (mergedOfList LR).order.toList = (firstsGo [] LR).map (·.name) := hoR
    rw [hoR']
    exact firstsGo_nodup LR [] (by simp)
  -- the home's merge
  have hG := blocksOk_good hb hO
  have hrow := home_rows hload hreg hT
  have hcnames : t.consts.toList.map (·.name) = w.home.constants.toList.map (·.name) :=
    map_forall₂ (fun q e ⟨s, _, hsn, _, _, hE⟩ => by
      have := (lazyEntry_stmt hE).1
      rw [hsn] at this
      exact Option.some.inj this) hrow
  have hndC : (w.home.constants.toList.map (·.name)).Nodup := by
    obtain ⟨-, -, hnd, -⟩ := namePositionsAt_mem hT
    rw [← hcnames]; exact hnd
  have hndH : ((w.home.constants.toList.filter (!·.skipped)).map (·.name)).Nodup :=
    hndC.sublist ((List.filter_sublist).map _)
  have hfirstsH : firstsGo [] (w.home.constants.toList.filter (!·.skipped)) =
      w.home.constants.toList.filter (!·.skipped) := firstsGo_nodup_eq _ [] (by simpa using hndH)
  obtain ⟨hoH, hmH⟩ := mergedOfList_firsts (w.home.constants.toList.filter (!·.skipped)) {} []
    (by simp) (by simp)
  have hndO : (homeMerged w).order.toList.Nodup := by
    have : (homeMerged w).order.toList =
        (firstsGo [] (w.home.constants.toList.filter (!·.skipped))).map (·.name) := hoH
    rw [this, hfirstsH]; exact hndH
  have hstoreH : ∀ e ∈ w.home.constants.toList.filter (!·.skipped),
      (homeMerged w).map[e.name]? = some e := by
    intro e he
    have : (homeMerged w).map[e.name]? =
        (firstsGo [] (w.home.constants.toList.filter (!·.skipped))).find? (·.name == e.name) := hmH _
    rw [this, hfirstsH]
    exact find?_self hndH he
  have hlook : ∀ e ∈ LR, e.skipped = false → e.kind.tag ≠ 2 →
      ∃ eH, (homeMerged w).map[e.name]? = some eH ∧ eH.toCEntryF = e.toCEntryF :=
    fun e he hs ht2 => home_lookup hsk hT hown (hereLR e he) hs ht2
  obtain ⟨cH, hcH, hcHE⟩ := hlook _ (hmapR hheadR).1 hsafe (by simp [hkE, CKindF.tag])
  have hcHn : (homeMerged w).map[n]? = some cH := by rw [← (hmapR hheadR).2]; exact hcH
  have hcHk : cH.kind = .induct np ni all cs nn ir iu irf := by
    rw [show cH.kind = cH.toCEntryF.kind from rfl, hcHE]; exact hkE
  have hcHs : cH.skipped = false := by
    rw [show cH.skipped = cH.toCEntryF.kind.skipped from rfl, hcHE]; exact hsafe
  obtain ⟨p, hpmem, tsH, ctsH, rsH, hpd, h1, h2, h3⟩ :=
    home_group hG hN hO hndO hem hcHn ⟨_, _, _, _, _, _, hcHk⟩ hcHs
  -- the members and constructors, constant by constant
  have e1 : (blockTys (homeMerged w) all).map (·.toCEntryF) =
      (blockTys (mergedOfList LR) all).map (·.toCEntryF) := by
    refine filterMap_toF (fun x hx => ?_)
    obtain ⟨m, cs', hm, ⟨_, _, _, _, _, _, hmk⟩, hms, -⟩ := hmemb x hx
    obtain ⟨eH, heH, heHm⟩ := hlook m (hmapR hm).1 hms (by simp [hmk, CKindF.tag])
    rw [(hmapR hm).2] at heH
    rw [heH, hm]
    simp [heHm]
  have e2 : (Olean.blockCtors (homeMerged w) (blockTys (homeMerged w) all)).map (·.toCEntryF) =
      (Olean.blockCtors (mergedOfList LR) (blockTys (mergedOfList LR) all)).map (·.toCEntryF) := by
    refine blockCtors_toF e1 (fun b hb y np' ni' all' cs' nn' ir' iu' irf' hbk hy => ?_)
    obtain ⟨x, hx, hxb⟩ := List.mem_filterMap.1 hb
    obtain ⟨m, csm, hm, him, -, hctor⟩ := hmemb x hx
    rw [hxb] at hm; cases hm
    obtain ⟨-, rfl⟩ := IsInd.unique him ⟨_, _, _, _, _, _, hbk⟩
    obtain ⟨m', hm', ⟨_, _, _, _, hm'k⟩, hm's⟩ := hctor y hy
    obtain ⟨eH, heH, heHm⟩ := hlook m' (hmapR hm').1 hm's (by simp [hm'k, CKindF.tag])
    rw [(hmapR hm').2] at heH
    rw [heH, hm']
    simp [heHm]
  -- the recursors
  have hrecR : ∀ e ∈ restR.filter P, ∃ all' np ni nmo nmi rules k iu,
      e.kind = .recur all' np ni nmo nmi rules k iu ∧ all' = all := by
    intro e he
    obtain ⟨he, hp⟩ := List.mem_filter.1 he
    have h7 := (hereR e he).2
    rcases hke : e.kind with _ | _ | _ | _ | _ | _ | _ | ⟨all', np', ni', nmo, nmi, rules, kk, iu'⟩
    all_goals try (rw [hke] at h7; simp [CKindF.tag] at h7)
    refine ⟨all', np', ni', nmo, nmi, rules, kk, iu', rfl, ?_⟩
    rw [hP e _ _ _ _ _ _ _ _ hke] at hp
    simpa using hp
  have hvalR : ∀ e ∈ restR.filter P, e.kind.skipped = false := by
    intro e he
    obtain ⟨all', np', ni', nmo, nmi, rules, kk, iu', hke, hall'⟩ := hrecR e he
    rw [hall'] at hke
    have hLRe : CEntry.ofF e ∈ LR := by
      rw [← hLR]
      exact List.mem_map_of_mem (by simp [List.filter_append, he])
    have hst := hstoreR _ hLRe
    have hinR : CEntry.ofF e ∈ Olean.blockRecs (mergedOfList LR) (recMapOf (mergedOfList LR)) n := by
      rw [blockRecs_order _ hndR]
      refine List.mem_filterMap.2 ⟨e.name, List.mem_filter.2 ⟨?_, ?_⟩, hst⟩
      · exact Array.mem_toList_iff.2 (((mergedOfList_spec LR).1 _).2 ((mergedOfList_spec LR).2.2 _ hLRe))
      · have hk2 : (CEntry.ofF e).kind = .recur all np' ni' nmo nmi rules kk iu' := hke
        rw [show e.name = (CEntry.ofF e).name from rfl, hst]
        simp only [Option.any_some, recUnder, hk2]
        simpa using hnall
    have hs := hval' _ (List.mem_append_right _ hinR)
    obtain ⟨t0, rest0, m, csm, hall, hm, -, hms⟩ :=
      blockStep_recur hst ⟨_, _, _, _, _, _, _, hke⟩ hs
    obtain ⟨m', cs', hm', -, hm's, -⟩ := hmemb t0 (by rw [hall]; exact List.mem_cons_self)
    rw [hm] at hm'; cases hm'
    have : (CEntry.ofF e).skipped = false := hms ▸ hm's
    exact this
  have hhome : ∀ e ∈ w.home.constants.toList, e.skipped = false → ∀ all' np ni nmo nmi rules k iu,
      e.kind = .recur all' np ni nmo nmi rules k iu → n ∈ all' → all' = all := by
    intro e he hes all' np' ni' nmo nmi rules kk iu' hke hn
    have hst := hstoreH e (List.mem_filter.2 ⟨he, by simp [hes]⟩)
    obtain ⟨t0, rest0, m, csm, rfl, hm, him, -⟩ := hG.recur hst ⟨_, _, _, _, _, _, _, hke⟩
    obtain ⟨m', cs', hm', him', -⟩ := (hG.ind hm him).2.1 n hn
    rw [hcHn] at hm'; cases hm'
    exact (IsInd.unique him' ⟨_, _, _, _, _, _, hcHk⟩).1
  have hsame := recs_same hT hrow hnall hrb hrestR P hP hvalR hhome
  -- the reach's merge lists the recursors it read, in their order
  have hnotRec : ∀ y ∈ tE :: tys ++ restC.filter P, recUnder n (CEntry.ofF y) = false := by
    have ofInd : ∀ y : CEntryF Name Expr, ∀ np ni all cs nn ir iu irf,
        y.kind = .induct np ni all cs nn ir iu irf → recUnder n (CEntry.ofF y) = false := by
      intro y _ _ _ _ _ _ _ _ hy
      have : (CEntry.ofF y).kind = _ := hy
      simp only [recUnder, this]
    intro y hy
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_filter] at hy
    rcases hy with rfl | hy | ⟨hy, hp⟩
    · exact ofInd _ _ _ _ _ _ _ _ _ hk
    · obtain ⟨-, hya⟩ := hereTys y hy
      obtain ⟨m, csm, hm, ⟨_, _, _, _, _, _, hmk⟩, -, -⟩ := hmemb y.name hya
      have hLRy : CEntry.ofF y ∈ LR := by rw [← hLR]; exact List.mem_map_of_mem (by simp [hy])
      rw [show y.name = (CEntry.ofF y).name from rfl, hstoreR _ hLRy] at hm
      cases hm
      exact ofInd _ _ _ _ _ _ _ _ _ hmk
    · obtain ⟨-, hyc⟩ := hereC y hy
      obtain ⟨ty, hty, hyty⟩ := List.mem_flatMap.1 hyc
      split at hyty
      · rename_i np' ni' all' cst nn' ir' iu' irf' htyk
        obtain ⟨-, htya⟩ := hereTys ty hty
        obtain ⟨m, csm, hm, him, -, hctor⟩ := hmemb ty.name htya
        have hLRt : CEntry.ofF ty ∈ LR := by rw [← hLR]; exact List.mem_map_of_mem (by simp [hty])
        rw [show ty.name = (CEntry.ofF ty).name from rfl, hstoreR _ hLRt] at hm
        cases hm
        obtain ⟨-, rfl⟩ := IsInd.unique him ⟨_, _, _, _, _, _, htyk⟩
        obtain ⟨m', hm', ⟨_, _, _, _, hm'k⟩, -⟩ := hctor y.name hyty
        have hLRy : CEntry.ofF y ∈ LR := by
          rw [← hLR]; exact List.mem_map_of_mem (by simp [List.filter_append, hy, hp])
        rw [show y.name = (CEntry.ofF y).name from rfl, hstoreR _ hLRy] at hm'
        cases hm'
        simp only [recUnder, hm'k]
      · cases hyty
  have hLRrec : LR.filter (recUnder n) = (restR.filter P).map CEntry.ofF := by
    have hLRl : LR = ((tE :: tys ++ restC.filter P) ++ restR.filter P).map CEntry.ofF := by
      rw [← hLR, List.filter_append]; simp
    rw [hLRl, List.filter_map, List.filter_append, List.map_append]
    rw [List.filter_eq_nil_iff.2 (fun y hy => by simpa using hnotRec y hy), List.map_nil,
      List.nil_append, List.filter_eq_self.2 (fun y hy => by
        obtain ⟨all', np', ni', nmo, nmi, rules, kk, iu', hke, hall'⟩ := hrecR y hy
        have hk2 : (CEntry.ofF y).kind = .recur all' np' ni' nmo nmi rules kk iu' := hke
        simp only [Function.comp, recUnder, hk2, hall']
        simpa using hnall)]
  have hndHR : ((((w.home.constants.toList.filter (!·.skipped)).filter (recUnder n)).map
      (·.toCEntryF)).map (·.name)).Nodup := by
    rw [List.map_map]
    exact hndH.sublist ((List.filter_sublist).map _)
  have hRR : Olean.blockRecs (mergedOfList LR) (recMapOf (mergedOfList LR)) n =
      (restR.filter P).map CEntry.ofF := by
    rw [blockRecs_mergedOfList, firstsGo_filter _ LR [] (by simpa using uniqLR), List.filter_nil,
      hLRrec]
    refine firstsGo_nodup_eq _ [] ?_
    rw [List.nil_append, List.map_map]
    have : (restR.filter P).map ((·.name) ∘ CEntry.ofF) = (restR.filter P).map (·.name) := rfl
    rw [this, ← hsame]
    exact hndHR
  have hRH : Olean.blockRecs (homeMerged w) (recMapOf (homeMerged w)) n =
      (w.home.constants.toList.filter (!·.skipped)).filter (recUnder n) := by
    rw [show homeMerged w = mergedOfList _ from rfl, blockRecs_mergedOfList, hfirstsH]
  have e3 : (Olean.blockRecs (homeMerged w) (recMapOf (homeMerged w)) n).map (·.toCEntryF) =
      (Olean.blockRecs (mergedOfList LR) (recMapOf (mergedOfList LR)) n).map (·.toCEntryF) := by
    have hof : ∀ l : List (CEntryF Name Expr), (l.map CEntry.ofF).map (·.toCEntryF) = l := by
      intro l; induction l with
      | nil => rfl
      | cons x l ih => simp only [List.map_cons, ih]; rfl
    rw [hRH, hRR, hof, hsame]
  refine ⟨p, hpmem, ?_⟩
  rw [← block_same hpd h1 h2 h3 hdR g1 g2 g3 e1 e2 e3]
  exact Presents.refl _

/-! ## Every context record of a worker -/

/-- **A record read from module `h` presents one of `h`'s own records**, as the worker at `h`
emitted them on the same snapshot. -/
theorem recordFrom_presents {sp : Roots} {fs : FS} {d : Declaration} {h : Name} {jobs : Nat}
    {w : WorkerRead} (hd : RecordFrom sp fs d h) (hw : WorkerFacts pins sp fs h jobs w) :
    ∃ p ∈ w.emitted, Presents d p := by
  obtain ⟨hs, he, hq⟩ := recordFrom_presents_nongroup hw
  cases hd with
  | stmt hs' hl hr hst hsk hgk hqk _ hred => exact hs rfl hs' hl hr hst hsk hgk hqk hred
  | entry hs' hl hr he' hr₀ hst hk hsk hd' => exact he rfl hs' hl hr he' hr₀ hst hk hsk hd'
  | quot hs' hl hr hst hd' => exact hq rfl hs' hl hr hst hd'
  | group hgr => exact group_presents hw hgr

theorem Presents.fill {d p : Declaration} (F : Expr → Expr) (h : Presents d p) :
    Presents d (fillDecl F p) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨by rw [declConstants_fillDecl]; exact h1, by rw [declTables_fillDecl]; exact h2⟩
  · refine .inr ⟨?_, by rw [declConstants_fillDecl]; exact h2⟩
    rw [h1]
    cases p <;> rfl

/-- **Every context record of an accepted worker at `M` presents one of its home's own records**:
the record at position `i` of the context, read from module `h` (`homes[i]`), and, where the worker
at `h` accepted on the same snapshot, one of `h`'s own records with its theorems' values in place
(`h`'s `decls` in the development), presented by it (`Presents`).  What `h`'s check of its views
says of the copy read is `copy_behind`'s. -/
theorem worker_presented {sp sp' L : Roots} {fs : FS} {m : Name} {jobs : Nat} {w : WorkerRead}
    {x : Array ImportRec} (hsL : sp.Trims L) (hsL' : sp'.Trims L)
    (hw : WorkerFacts pins sp fs m jobs w x) {i : Nat} {d : Declaration} {h : Name}
    (hd : w.reach.ctx[i]? = some d) (hh : w.reach.homes[i]? = some h)
    {jobs' : Nat} {w' : WorkerRead} (hw' : WorkerFacts pins sp' fs h jobs' w') :
    ∃ p ∈ w'.own.toList.map (fillDecl (fillOf sp' fs #[⟨h, w'.home.frontier⟩])), Presents d p := by
  obtain ⟨_, _, hrd⟩ := hw.reads
  obtain ⟨_, _, _, _, hre⟩ := hw.reach
  obtain ⟨hparts, hindex⟩ := workerReads_index hrd
  obtain ⟨-, hfrom⟩ := reach_from hparts hindex hre
  obtain ⟨f, hf, -⟩ := hw'.home
  obtain ⟨lb, hlb⟩ := readFiles_found hf
  obtain ⟨p, hp, hpr⟩ := recordFrom_presents ((hfrom i d h hd hh).move hsL hsL' hlb) hw'
  refine ⟨_, List.mem_map.2 ⟨p, ?_, rfl⟩, Presents.fill _ hpr⟩
  rw [hw'.own]
  exact (Frontend.hoistNatOpGround_perm _ _).mem_iff.2 (Array.mem_toList_iff.2 hp)

/-- Every context record has its home. -/
theorem worker_home {sp : Roots} {fs : FS} {m : Name} {jobs : Nat} {w : WorkerRead} {x : Array ImportRec}
    (hw : WorkerFacts pins sp fs m jobs w x) {d : Declaration} (hd : d ∈ w.reach.ctx.toList) :
    ∃ (i : Nat) (h : Name), w.reach.ctx[i]? = some d ∧ w.reach.homes[i]? = some h := by
  obtain ⟨_, _, hrd⟩ := hw.reads
  obtain ⟨_, _, _, _, hre⟩ := hw.reach
  obtain ⟨hparts, hindex⟩ := workerReads_index hrd
  obtain ⟨hsz, -⟩ := reach_from hparts hindex hre
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have hi' : i < w.reach.homes.size := by rw [← hsz]; simpa using hi
  exact ⟨i, w.reach.homes[i], by simp, by simp⟩

/-! ## The local checks they give -/

/-- **`InterfaceOk` at a module**: in a development whose module `b` has the worker at `hb`'s own
records, theorems' values in place, as its `decls`, and presents only context records that
workers on the same snapshot read from `hb`, every presentation presents one of `b`'s own
records. -/
theorem interfaceOk_of_workers {sp L : Roots} {fs : FS} {hb : Name} {jobs : Nat}
    {w : WorkerRead} (hsL : sp.Trims L) (hw : WorkerFacts pins sp fs hb jobs w)
    (dev : Nat → Module) (b : Nat)
    (hdecls : (dev b).decls = w.own.toList.map (fillDecl (fillOf sp fs #[⟨hb, w.home.frontier⟩])))
    (hiface : ∀ e ∈ (dev b).iface, ∃ (a : Roots) (M : Name) (jM : Nat) (wM : WorkerRead)
      (xM : Array ImportRec) (i : Nat), a.Trims L ∧ WorkerFacts pins a fs M jM wM xM ∧
        wM.reach.ctx[i]? = some e ∧ wM.reach.homes[i]? = some hb) :
    InterfaceOk dev b := by
  refine ⟨fun e he => ?_⟩
  obtain ⟨a, M, jM, wM, xM, i, haL, hwM, hc, hh⟩ := hiface e he
  rw [hdecls]
  exact worker_presented haL hsL hwM hc hh hw

/-- **`ImportOk.presented` at a module**: in a development whose module `i` has the worker at `M`'s
context as its `ctx`, each context name read from the module its record's home is (`srcOf`,
`nameOf`), and whose modules present the context records workers read from them, every context
record is a presentation of the module its names are read from. -/
theorem presented_of_worker {sp L : Roots} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    {x : Array ImportRec} (hsL : sp.Trims L)
    (hw : WorkerFacts pins sp fs M jobs w x) (dev : Nat → Module) (i : Nat)
    (hctx : (dev i).ctx = w.reach.ctx.toList) (nameOf : Nat → Name)
    (hsrc : ∀ (j : Nat) (d : Declaration) (h : Name), w.reach.ctx[j]? = some d →
      w.reach.homes[j]? = some h → ∀ n ∈ declNames d, nameOf ((dev i).src n) = h)
    (hiface : ∀ (b : Nat) (e : Declaration), (∃ (a : Roots) (M' : Name) (j' : Nat) (w' : WorkerRead)
      (x' : Array ImportRec) (k : Nat), a.Trims L ∧ WorkerFacts pins a fs M' j' w' x' ∧
        w'.reach.ctx[k]? = some e ∧ w'.reach.homes[k]? = some (nameOf b)) →
      e ∈ (dev b).iface) :
    ∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, d ∈ (dev ((dev i).src n)).iface := by
  intro d hd n hn
  rw [hctx] at hd
  obtain ⟨j, h, hj, hh⟩ := worker_home hw hd
  refine hiface _ d ⟨sp, M, jobs, w, x, j, hsL, hw, hj, ?_⟩
  rw [hsrc j d h hj hh n hn]
  exact hh

end ConLeche.Driver
