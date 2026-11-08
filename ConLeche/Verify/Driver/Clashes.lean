module

-- `qsort`'s helpers are private in the toolchain: a proof that it permutes its input must see them
import all Init.Data.Array.QSort.Basic
public import ConLeche.Verify.Driver.ReachFrom
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Driver.Provenance
import ConLeche.Verify.Frontend.Olean.Files
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Sparse
import ConLeche.Verify.Driver.Loads

/-!
# A worker's name index and its clashes, on the snapshot

What an accepting `workerReads` (`ConLeche/Frontend/Olean/Index.lean`) read of the names it loads,
stated over the snapshot's parts (task #501, for the composition):

* `nameIndexOf_spec`, `workerIndex_copies` — **the index**: every name position of a loaded part
  is a copy, the name's first copy is at or before it in the load order, and every copy the index
  records is a position of its name;
* `workerClash_complete` — **two copies of one name make a clash**, listing both;
* `workerClash_stmt` — **a clash copy's statement and kind are its position's**, read off the
  part's skeleton (`StmtSkel`);
* `workerClash_same` — **a clash's copies share one statement**: Lean's merge rule compares
  names, types and level parameters;
* `clashCopiesOf_spec` — the reach's table of the clashes' copies, by name.

The spot of a copy is `spotOf`: the part its module is loaded at, and its name position there
(`importerSpot`'s and `clashAgree`'s).
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean

/-! ## A part's files, determined -/

theorem readPart_isDet (p : System.FilePath) (fs : FS) :
    (readPart p : ModelIO (Except CheckError Part)).Det fs := by
  simp only [readPart]
  exact ModelIO.det_bind ⟨fs.file p, fun hs => ⟨hs, rfl⟩⟩ fun _ => ModelIO.det_pure _ _

theorem readFilesAt_isDet (loc : Located) (m : Name) (level : OLeanLevel) (fs : FS) :
    (readFilesAt loc m level : ModelIO (Except CheckError ModFiles)).Det fs := by
  simp only [readFilesAt]
  refine ModelIO.det_bind (readPart_isDet _ fs) fun x => ?_
  rcases x with e | ex
  · exact ModelIO.det_pure _ _
  simp only
  split
  · exact ModelIO.det_pure _ _
  split
  · split
    · exact ModelIO.det_pure _ _
    · exact ModelIO.det_pure _ _
  split
  · exact ModelIO.det_pure _ _
  split
  · exact ModelIO.det_pure _ _
  refine ModelIO.det_bind (readPart_isDet _ fs) fun y => ?_
  rcases y with e | s
  · exact ModelIO.det_pure _ _
  simp only
  split
  · exact ModelIO.det_pure _ _
  refine ModelIO.det_bind (readPart_isDet _ fs) fun z => ?_
  rcases z with e | p
  · exact ModelIO.det_pure _ _
  · exact ModelIO.det_pure _ _

/-- The files of a read of a part: its module located, its files read there. -/
theorem readFiles_open {sp : SearchPath} {m : Name} {level : OLeanLevel} {fs : FS}
    {a : ModFiles} (ha : ModelIO.CanGive (readFiles sp m level) fs (.ok a)) :
    ∃ loc, ModelIO.Gives (findModule sp m) fs (.ok loc) ∧
      ModelIO.CanGive (readFilesAt loc m level) fs (.ok a) := by
  obtain ⟨hs, hs', h⟩ := ha
  simp only [readFiles, ModelIO.bind_ok] at h
  obtain ⟨y, hs₁, hy, h⟩ := h
  rcases y with e | loc
  · simp at h
  exact ⟨loc, findModule_ok hy, hs₁, hs', h⟩

/-- **A part's files are the snapshot's**, at every level. -/
theorem readFiles_unique_at {sp : SearchPath} {m : Name} {level : OLeanLevel} {fs : FS}
    {a b : ModFiles} (ha : ModelIO.CanGive (readFiles sp m level) fs (.ok a))
    (hb : ModelIO.CanGive (readFiles sp m level) fs (.ok b)) : a = b := by
  obtain ⟨loc, hl, ha⟩ := readFiles_open ha
  obtain ⟨loc', hl', hb⟩ := readFiles_open hb
  obtain rfl : loc' = loc := Except.ok.inj (hl.eq hl'.canGive)
  exact (Except.ok.inj (((readFilesAt_isDet _ m level fs).gives ha).eq hb)).symm

/-- **A part's name table is read off its files**: the table of the view its files' region
holds. -/
theorem partNames_region {sp : SearchPath} {fs : FS} {k : PartKey} {t : NamePositions}
    {f : ModFiles} (ht : PartNames sp fs k t) (hf : PartFiles sp fs k f) :
    readNamePositions f k.level = some t := by
  obtain ⟨hs, hs', h⟩ := ht
  simp only [readPartNames, ModelIO.bind_ok] at h
  obtain ⟨y, hs₁, hy, h⟩ := h
  rcases y with e | loc
  · simp at h
  simp only [readPartNamesAt, ModelIO.bind_ok] at h
  obtain ⟨z, hs₂, hz, h⟩ := h
  rcases z with e | g
  · simp at h
  have hg : PartFiles sp fs k g := by
    refine ⟨hs, hs₂, ?_⟩
    simp only [readFiles, ModelIO.bind_ok]
    exact ⟨.ok loc, hs₁, hy, hz⟩
  obtain rfl := readFiles_unique_at hg hf
  simp only at h
  cases hr : readNamePositions g k.level with
  | none => simp [hr] at h
  | some ps =>
    simp only [hr, ModelIO.pure_iff, Except.ok.injEq] at h
    rw [h.1]

/-- **A name position's statement names it**: at a copy, the statement the skeleton of the part's
region holds there is of the copy's name. -/
theorem copyAt_stmt_name {sp : SearchPath} {fs : FS} {s : Spot} {r : Region} {cv : ConstantVal}
    {k : CKindF Name Unit} (hs : CopyAt sp fs s) (hr : PartRegion sp fs s.part r)
    (hst : StmtSkel r s.pos.loc cv k) : cv.name = s.pos.name := by
  obtain ⟨t, ht, hq⟩ := hs
  obtain ⟨f, a, hf, hreg⟩ := hr
  have hn := partNames_region ht hf
  simp only [readNamePositions, hreg] at hn
  change namePositionsAt r a = some t at hn
  obtain ⟨_, _, _, hall⟩ := namePositionsAt_mem hn
  obtain ⟨_, sk, hsk, hnm, _, _⟩ := hall _ hq
  obtain ⟨sk', hsk', hnm', -⟩ := hst
  rw [hsk] at hsk'
  cases hsk'
  rw [hnm] at hnm'
  exact (Option.some.inj hnm').symm

/-! ## The name index -/

/-- The index's state: the first copies, the later ones, the position. -/
abbrev IdxSt := Std.HashMap Name Copy × Array (Name × Copy) × Nat

/-- `nameIndexOf`'s step at one name position of part `i`. -/
@[expose] def idxStep (i : Nat) (acc : IdxSt) (q : NamePosition) : IdxSt :=
  match acc with
  | (first, more, k) =>
    match first[q.name]? with
    | none => (first.insert q.name ⟨i, k⟩, more, k + 1)
    | some _ => (first, more.push (q.name, ⟨i, k⟩), k + 1)

/-- `nameIndexOf`'s step at one part. -/
@[expose] def idxPart (acc : IdxSt) (p : NamePositions) : IdxSt :=
  match acc with
  | (first, more, i) =>
    match p.consts.foldl (idxStep i) (first, more, 0) with
    | (first, more, _) => (first, more, i + 1)

theorem nameIndexOf_eq (parts : Array NamePositions) :
    nameIndexOf parts =
      { parts, first := (parts.foldl idxPart (Std.HashMap.emptyWithCapacity
          (parts.foldl (fun n p => n + p.consts.size) 0), #[], 0)).1,
        more := (parts.foldl idxPart (Std.HashMap.emptyWithCapacity
          (parts.foldl (fun n p => n + p.consts.size) 0), #[], 0)).2.1 } := by
  rfl

/-- A copy's name position, by the parts. -/
@[expose] def atP (parts : Array NamePositions) (c : Copy) : Option NamePosition :=
  (parts[c.mod]?).bind (·.consts[c.pos]?)

/-- A copy of `n`. -/
@[expose] def NamedAt (parts : Array NamePositions) (c : Copy) (n : Name) : Prop :=
  ∃ q, atP parts c = some q ∧ q.name = n

/-- The positions before part `i`'s position `k`. -/
@[expose] def Done (i k : Nat) (c : Copy) : Prop := c.mod < i ∨ (c.mod = i ∧ c.pos < k)

/-- **The index's invariant** before part `i`'s position `k`. -/
structure IdxInv (parts : Array NamePositions) (first : Std.HashMap Name Copy)
    (more : Array (Name × Copy)) (i k : Nat) : Prop where
  hfirst : ∀ n c, first[n]? = some c → Done i k c ∧ NamedAt parts c n
  hmore : ∀ n c, (n, c) ∈ more.toList → Done i k c ∧ NamedAt parts c n ∧
    ∃ c₀, first[n]? = some c₀ ∧ c₀ ≠ c
  hall : ∀ c q, Done i k c → atP parts c = some q →
    first[q.name]? = some c ∨ (q.name, c) ∈ more.toList
  hleast : ∀ n c₀ c, first[n]? = some c₀ → Done i k c → NamedAt parts c n → c₀.mod ≤ c.mod

theorem idxInv_step {parts : Array NamePositions} {first : Std.HashMap Name Copy}
    {more : Array (Name × Copy)} {i k : Nat} (hI : IdxInv parts first more i k)
    {p : NamePositions} (hp : parts[i]? = some p) {q : NamePosition} (hq : p.consts[k]? = some q) :
    IdxInv parts (idxStep i (first, more, k) q).1 (idxStep i (first, more, k) q).2.1 i (k + 1) ∧
      (idxStep i (first, more, k) q).2.2 = k + 1 := by
  have hat : atP parts ⟨i, k⟩ = some q := by simp [atP, hp, hq]
  have hD : ∀ c, Done i (k + 1) c ↔ Done i k c ∨ c = ⟨i, k⟩ := by
    intro ⟨cm, cp⟩
    simp only [Done, Copy.mk.injEq]
    omega
  have hnotD : ¬ Done i k ⟨i, k⟩ := by simp [Done]
  unfold idxStep
  cases hf : first[q.name]? with
  | none =>
    simp only [hf]
    refine ⟨⟨fun n c h => ?_, fun n c h => ?_, fun c q' hc ha => ?_, fun n c₀ c h hc hn => ?_⟩, by simp⟩
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        cases h
        exact ⟨(hD _).2 (.inr rfl), q, hat, eq_of_beq he⟩
      · obtain ⟨h1, h2⟩ := hI.hfirst n c h
        exact ⟨(hD _).2 (.inl h1), h2⟩
    · obtain ⟨h1, h2, c₀, h3, h4⟩ := hI.hmore n c h
      refine ⟨(hD _).2 (.inl h1), h2, c₀, ?_, h4⟩
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i he
        rw [← eq_of_beq he, hf] at h3; cases h3
      · exact h3
    · rcases (hD c).1 hc with hc | rfl
      · rcases hI.hall c q' hc ha with h | h
        · left
          rw [Std.HashMap.getElem?_insert]
          split
          · rename_i he; rw [← eq_of_beq he, hf] at h; cases h
          · exact h
        · exact .inr h
      · rw [hat] at ha; cases ha
        left; simp
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        cases h
        rcases (hD c).1 hc with hc | rfl
        · obtain ⟨q', ha, hn⟩ := hn
          rcases hI.hall c q' hc ha with h' | h'
          · rw [hn, ← eq_of_beq he, hf] at h'; cases h'
          · obtain ⟨-, -, c₁, h1, -⟩ := hI.hmore _ _ h'
            rw [hn, ← eq_of_beq he, hf] at h1; cases h1
        · exact Nat.le_refl _
      · rcases (hD c).1 hc with hc | rfl
        · exact hI.hleast n c₀ c h hc hn
        · obtain ⟨h1, -⟩ := hI.hfirst n c₀ h
          simp only [Done] at h1
          show c₀.mod ≤ i
          omega
  | some c₁ =>
    simp only [hf]
    refine ⟨⟨fun n c h => ?_, fun n c h => ?_, fun c q' hc ha => ?_, fun n c₀ c h hc hn => ?_⟩, by simp⟩
    · obtain ⟨h1, h2⟩ := hI.hfirst n c h
      exact ⟨(hD _).2 (.inl h1), h2⟩
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton, Prod.mk.injEq] at h
      rcases h with h | ⟨rfl, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := hI.hmore n c h
        exact ⟨(hD _).2 (.inl h1), h2, h3⟩
      · refine ⟨(hD _).2 (.inr rfl), ⟨q, hat, rfl⟩, c₁, hf, fun he => ?_⟩
        subst he
        exact hnotD (hI.hfirst _ _ hf).1
    · rcases (hD c).1 hc with hc | rfl
      · rcases hI.hall c q' hc ha with h | h
        · exact .inl h
        · right; simp [h]
      · rw [hat] at ha; cases ha
        right; simp
    · rcases (hD c).1 hc with hc | rfl
      · exact hI.hleast n c₀ c h hc hn
      · obtain ⟨h1, -⟩ := hI.hfirst n c₀ h
        simp only [Done] at h1
        show c₀.mod ≤ i
        omega

theorem idxInv_steps {parts : Array NamePositions} {i : Nat} {p : NamePositions}
    (hp : parts[i]? = some p) :
    ∀ (l : List NamePosition) (first : Std.HashMap Name Copy) (more : Array (Name × Copy)) (k : Nat),
      (∀ j (hj : j < l.length), p.consts[k + j]? = some l[j]) →
      IdxInv parts first more i k →
      IdxInv parts (l.foldl (idxStep i) (first, more, k)).1 (l.foldl (idxStep i) (first, more, k)).2.1
        i (k + l.length) ∧ (l.foldl (idxStep i) (first, more, k)).2.2 = k + l.length
  | [], first, more, k, _, hI => ⟨by simpa using hI, by simp⟩
  | q :: l, first, more, k, hl, hI => by
    have hq : p.consts[k]? = some q := hl 0 (by simp)
    obtain ⟨h1, h2⟩ := idxInv_step hI hp hq
    rw [List.foldl_cons]
    generalize hs : idxStep i (first, more, k) q = st at h1 h2
    obtain ⟨f', m', k'⟩ := st
    simp only at h1 h2
    subst h2
    have := idxInv_steps hp l f' m' (k + 1) (fun j hj => by
      have := hl (j + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this) h1
    simpa [Nat.add_assoc, Nat.add_comm 1 l.length] using this

theorem idxInv_parts (parts : Array NamePositions) :
    ∀ (l : List NamePositions) (first : Std.HashMap Name Copy) (more : Array (Name × Copy)) (i : Nat),
      (∀ j (hj : j < l.length), parts[i + j]? = some l[j]) →
      IdxInv parts first more i 0 →
      IdxInv parts (l.foldl idxPart (first, more, i)).1 (l.foldl idxPart (first, more, i)).2.1
        (i + l.length) 0
  | [], first, more, i, _, hI => by simpa using hI
  | p :: l, first, more, i, hl, hI => by
    have hp : parts[i]? = some p := hl 0 (by simp)
    have hin := idxInv_steps hp p.consts.toList first more 0 (fun j hj => by simp) hI
    rw [Array.foldl_toList] at hin
    rw [List.foldl_cons, show idxPart (first, more, i) p =
      ((p.consts.foldl (idxStep i) (first, more, 0)).1,
        (p.consts.foldl (idxStep i) (first, more, 0)).2.1, i + 1) from rfl]
    generalize hs : p.consts.foldl (idxStep i) (first, more, 0) = st at hin
    obtain ⟨f', m', k'⟩ := st
    simp only at hin ⊢
    obtain ⟨hI', -⟩ := hin
    have hI'' : IdxInv parts f' m' (i + 1) 0 := by
      have hD : ∀ c q, atP parts c = some q → (Done (i + 1) 0 c ↔ Done i (0 + p.consts.toList.length) c) := by
        intro ⟨cm, cpos⟩ q hc
        simp only [Done, Nat.zero_add, Array.length_toList]
        constructor
        · intro h
          by_cases hm : cm = i
          · subst hm
            simp only [atP, hp, Option.bind_some] at hc
            exact .inr ⟨rfl, (Array.getElem?_eq_some_iff.1 hc).1⟩
          · exact .inl (by omega)
        · rintro (h | ⟨h, -⟩) <;> omega
      have hfw : ∀ c, Done i (0 + p.consts.toList.length) c → Done (i + 1) 0 c := by
        intro c h; simp only [Done] at h ⊢; omega
      refine ⟨fun n c h => ?_, fun n c h => ?_, fun c q hc ha => ?_, fun n c₀ c h hc hn => ?_⟩
      · obtain ⟨h1, h2⟩ := hI'.hfirst n c h; exact ⟨hfw _ h1, h2⟩
      · obtain ⟨h1, h2⟩ := hI'.hmore n c h; exact ⟨hfw _ h1, h2⟩
      · exact hI'.hall c q ((hD c q ha).1 hc) ha
      · obtain ⟨q, ha, hq⟩ := hn
        exact hI'.hleast n c₀ c h ((hD c q ha).1 hc) ⟨q, ha, hq⟩
    have := idxInv_parts parts l f' m' (i + 1) (fun j hj => by
      have := hl (j + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this) hI''
    simpa [Nat.add_assoc, Nat.add_comm 1 l.length] using this

/-- **The name index's facts**: every copy the index records is a position of its name; every
name position is recorded, as the first copy of its name or a later one; a recorded later copy
is not the first; the first copy comes no later in the load order. -/
theorem nameIndexOf_spec (parts : Array NamePositions) :
    IdxInv parts (nameIndexOf parts).first (nameIndexOf parts).more parts.size 0 := by
  rw [nameIndexOf_eq]
  dsimp only
  have := idxInv_parts parts parts.toList (Std.HashMap.emptyWithCapacity
    (parts.foldl (fun n p => n + p.consts.size) 0)) #[] 0 (fun j hj => by simp)
    ⟨fun n c h => by simp at h,
      fun n c h => by simp at h, fun c q hc _ => by simp only [Done] at hc; omega,
      fun n c₀ c h => by simp at h⟩
  rw [Array.foldl_toList] at this
  simpa using this

theorem atP_eq (parts : Array NamePositions) (c : Copy) :
    (nameIndexOf parts).at c = atP parts c := by
  rw [nameIndexOf_eq]; rfl

/-- Every valid copy is done at the end. -/
theorem done_all {parts : Array NamePositions} {c : Copy} {q : NamePosition}
    (h : atP parts c = some q) : Done parts.size 0 c := by
  simp only [atP] at h
  cases hp : parts[c.mod]? with
  | none => simp [hp] at h
  | some p => exact .inl (Array.getElem?_eq_some_iff.1 hp).1

/-! ## The doubly held names -/

/-- `clashCopies`' step at one later copy. -/
@[expose] def ccStep (first : Std.HashMap Name Copy) (m : Std.HashMap Name (Array Copy))
    (x : Name × Copy) : Std.HashMap Name (Array Copy) :=
  match x with
  | (n, c) => m.alter n fun
      | none => some #[(first[n]?).getD c, c]
      | some a => some (a.push c)

theorem clashCopies_eq (ix : NameIndex) :
    clashCopies ix = (ix.more.foldl (ccStep ix.first) {}).toArray := rfl

theorem ccStep_fold (first : Std.HashMap Name Copy) :
    ∀ (l L : List (Name × Copy)) (m : Std.HashMap Name (Array Copy)),
      (∀ x ∈ L ++ l, (first[x.1]?).isSome = true) →
      (∀ n a, m[n]? = some a → ∀ c, c ∈ a.toList ↔ first[n]? = some c ∨ (n, c) ∈ L) →
      (∀ n c, (n, c) ∈ L → (m[n]?).isSome = true) →
      (∀ n a, (l.foldl (ccStep first) m)[n]? = some a →
        ∀ c, c ∈ a.toList ↔ first[n]? = some c ∨ (n, c) ∈ L ++ l) ∧
      (∀ n c, (n, c) ∈ L ++ l → ((l.foldl (ccStep first) m)[n]?).isSome = true)
  | [], L, m, _, h1, h2 => by simpa using And.intro h1 h2
  | (n, c) :: l, L, m, hf, h1, h2 => by
    rw [List.foldl_cons]
    have := ccStep_fold first l (L ++ [(n, c)]) (ccStep first m (n, c)) (by simpa using hf)
      (fun n' a h c' => by
        simp only [ccStep, Std.HashMap.getElem?_alter] at h
        split at h
        · rename_i he
          obtain rfl := eq_of_beq he
          cases hm : m[n]? with
          | none =>
            rw [hm] at h
            cases h
            obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.1 (hf (n, c) (by simp))
            simp only [hc₀, Option.getD_some, List.mem_append, List.mem_singleton, Prod.mk.injEq,
              true_and]
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (rfl | rfl)
              · exact .inl rfl
              · exact .inr (.inr rfl)
            · rintro (h | h | rfl)
              · exact .inl (Option.some.inj h).symm
              · exact absurd (h2 _ _ h) (by simp [hm])
              · exact .inr rfl
          | some a₀ =>
            rw [hm] at h
            cases h
            simp only [Array.toList_push, List.mem_append, List.mem_singleton, Prod.mk.injEq,
              true_and]
            rw [h1 n a₀ hm c']
            exact or_assoc
        · rename_i he
          rw [h1 n' a h c']
          simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro (h | h)
            · exact .inl h
            · exact .inr (.inl h)
          · rintro (h | h | ⟨rfl, rfl⟩)
            · exact .inl h
            · exact .inr h
            · simp at he)
      (fun n' c' h => by
        simp only [ccStep, Std.HashMap.getElem?_alter]
        split
        · split <;> simp
        · rename_i he
          simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at h
          rcases h with h | ⟨rfl, rfl⟩
          · exact h2 _ _ h
          · simp at he)
    simpa using this

/-- **`clashCopies`' table**: the copies listed for a doubly held name are its first copy and its
later ones, and every name with a later copy is listed. -/
theorem clashCopies_spec {ix : NameIndex}
    (hf : ∀ n c, (n, c) ∈ ix.more.toList → (ix.first[n]?).isSome = true) :
    (∀ n a, (n, a) ∈ clashCopies ix → ∀ c, c ∈ a.toList ↔ ix.first[n]? = some c ∨ (n, c) ∈ ix.more.toList) ∧
    (∀ n c, (n, c) ∈ ix.more.toList → ∃ a, (n, a) ∈ clashCopies ix) := by
  have := ccStep_fold ix.first ix.more.toList [] {} (fun x hx => hf x.1 x.2 (by simpa using hx))
    (fun n a h => by simp at h) (fun n c h => by simp at h)
  rw [Array.foldl_toList] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨fun n a h c => ?_, fun n c h => ?_⟩
  · rw [clashCopies_eq, Std.HashMap.mem_toArray_iff_getElem?_eq_some] at h
    simpa using h1 n a h c
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (h2 n c (by simpa using h))
    exact ⟨a, by rw [clashCopies_eq, Std.HashMap.mem_toArray_iff_getElem?_eq_some]; exact ha⟩

/-! ## `qsort` permutes -/

private theorem qloop_perm {α : Type} {n : Nat} (lt : α → α → Bool) (lo hi : Nat) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2.Perm as := by
  fun_induction Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w with
  | case1 as i k _ _ _ h hlt ih => exact ih.trans (Vector.swap_perm (by omega) (by omega))
  | case2 as i k _ _ _ h hlt ih => exact ih
  | case3 as i k _ _ _ h => exact Vector.swap_perm (by omega) (by omega)

theorem qpartition_perm {α : Type} {n : Nat} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qpartition as lt lo hi w hlo hhi).2.Perm as := by
  unfold Array.qpartition
  refine (qloop_perm _ _ _ _ _ _ _ _ _ _ _).trans ?_
  split <;> split <;> split <;>
    first
    | exact Vector.Perm.refl _
    | exact Vector.swap_perm (by omega) (by omega)
    | exact (Vector.swap_perm (by omega) (by omega)).trans (Vector.swap_perm (by omega) (by omega))
    | exact ((Vector.swap_perm (by omega) (by omega)).trans (Vector.swap_perm (by omega) (by omega))).trans
        (Vector.swap_perm (by omega) (by omega))

private theorem qsort_sort_perm {α : Type} (lt : α → α → Bool) {n : Nat} (as : Vector α n) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qsort.sort lt as lo hi w hlo hhi).Perm as := by
  fun_induction Array.qsort.sort lt as lo hi w hlo hhi with
  | case1 as lo hi w hlo hhi h mid hmid as' he hge =>
    have := qpartition_perm as lt lo hi w hlo hhi
    rw [he] at this; exact this
  | case2 as lo hi w hlo hhi h mid hmid as' he hlt ih1 ih2 ih3 =>
    have := qpartition_perm as lt lo hi w hlo hhi
    rw [he] at this
    exact (ih3.trans ih1).trans this
  | case3 => exact Vector.Perm.refl _

theorem qsort_mem {α : Type} (as : Array α) (lt : α → α → Bool) (x : α) :
    x ∈ as.qsort lt ↔ x ∈ as := by
  unfold Array.qsort
  split
  · exact Iff.rfl
  · exact ((qsort_sort_perm _ _ _ _ _ _ _).toArray.mem_iff).trans (by simp)

/-! ## The statements read for the doubly held names -/

theorem Copy.beq_iff (a b : Copy) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show (_ && _) = true ↔ _
  simp

instance : LawfulBEq Copy where
  eq_of_beq h := (Copy.beq_iff _ _).1 h
  rfl := (Copy.beq_iff _ _).2 rfl

/-- `byModule`'s step. -/
@[expose] def bmStep (m : Std.HashMap Nat (Array Copy)) (c : Copy) : Std.HashMap Nat (Array Copy) :=
  m.alter c.mod fun | none => some #[c] | some a => some (a.push c)

theorem byModule_eq (cs : Array Copy) :
    byModule cs = ((cs.foldl bmStep {}).toArray.qsort (·.1 < ·.1)) := rfl

theorem bmStep_fold :
    ∀ (l L : List Copy) (m : Std.HashMap Nat (Array Copy)),
      (∀ i g, m[i]? = some g → ∀ c ∈ g.toList, c.mod = i ∧ c ∈ L) →
      (∀ c ∈ L, ∃ g, m[c.mod]? = some g ∧ c ∈ g.toList) →
      (∀ i g, (l.foldl bmStep m)[i]? = some g → ∀ c ∈ g.toList, c.mod = i ∧ c ∈ L ++ l) ∧
      (∀ c ∈ L ++ l, ∃ g, (l.foldl bmStep m)[c.mod]? = some g ∧ c ∈ g.toList)
  | [], L, m, h1, h2 => by simpa using And.intro h1 h2
  | c :: l, L, m, h1, h2 => by
    rw [List.foldl_cons]
    have := bmStep_fold l (L ++ [c]) (bmStep m c)
      (fun i g h c' hc' => by
        simp only [bmStep, Std.HashMap.getElem?_alter] at h
        split at h
        · rename_i he
          obtain rfl := eq_of_beq he
          cases hm : m[c.mod]? with
          | none =>
            rw [hm] at h; cases h
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
            subst hc'; simp
          | some a =>
            rw [hm] at h; cases h
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hc'
            rcases hc' with hc' | rfl
            · obtain ⟨h3, h4⟩ := h1 _ _ hm c' hc'
              exact ⟨h3, by simp [h4]⟩
            · simp
        · obtain ⟨h3, h4⟩ := h1 _ _ h c' hc'
          exact ⟨h3, by simp [h4]⟩)
      (fun c' hc' => by
        simp only [bmStep, Std.HashMap.getElem?_alter]
        simp only [List.mem_append, List.mem_singleton] at hc'
        by_cases he : c.mod = c'.mod
        · simp only [he, BEq.rfl, ↓reduceIte]
          rw [← he]
          cases hm : m[c.mod]? with
          | none =>
            rcases hc' with hc' | rfl
            · obtain ⟨g, hg, -⟩ := h2 c' hc'; rw [← he, hm] at hg; cases hg
            · simp
          | some a =>
            simp only [Option.some.injEq, exists_eq_left', Array.toList_push, List.mem_append,
              List.mem_singleton]
            rcases hc' with hc' | rfl
            · obtain ⟨g, hg, hc⟩ := h2 c' hc'
              rw [← he, hm] at hg; cases hg; exact .inl hc
            · exact .inr rfl
        · have hne : (c.mod == c'.mod) = false := by simpa using he
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          rcases hc' with hc' | rfl
          · exact h2 c' hc'
          · exact absurd rfl he)
    simpa using this

/-- **`byModule`'s groups**: each holds copies of its module only, and every copy is in its
module's group. -/
theorem byModule_spec (cs : Array Copy) :
    (∀ i g, (i, g) ∈ byModule cs → ∀ c ∈ g.toList, c.mod = i ∧ c ∈ cs.toList) ∧
    (∀ c ∈ cs.toList, ∃ g, (c.mod, g) ∈ byModule cs ∧ c ∈ g.toList) := by
  obtain ⟨h1, h2⟩ := bmStep_fold cs.toList [] {} (by simp) (by simp)
  rw [Array.foldl_toList] at h1 h2
  refine ⟨fun i g h c hc => ?_, fun c hc => ?_⟩
  · rw [byModule_eq, qsort_mem, Std.HashMap.mem_toArray_iff_getElem?_eq_some] at h
    simpa using h1 i g h c hc
  · obtain ⟨g, hg, hcg⟩ := h2 c (by simpa using hc)
    exact ⟨g, by rw [byModule_eq, qsort_mem, Std.HashMap.mem_toArray_iff_getElem?_eq_some]; exact hg,
      hcg⟩

/-- A `filterMap` that keeps the length keeps every element. -/
theorem filterMap_length_eq {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (l.filterMap f).length = l.length → ∀ x ∈ l, (f x).isSome = true
  | [], _, x, hx => by simp at hx
  | a :: l, h, x, hx => by
    rw [List.filterMap_cons] at h
    cases ha : f a with
    | none =>
      rw [ha] at h
      have := List.length_filterMap_le f l
      simp at h; omega
    | some b =>
      rw [ha] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · simp [ha]
      · exact filterMap_length_eq h x hx

theorem filterMap_getElem? {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = true) → ∀ j : Nat,
      (l.filterMap f)[j]? = (l[j]?).bind f
  | [], _, j => by simp
  | a :: l, h, j => by
    have ha := h a List.mem_cons_self
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ha
    rw [List.filterMap_cons, hb]
    cases j with
    | zero => simp [hb]
    | succ j => simpa using filterMap_getElem? (fun x hx => h x (List.mem_cons_of_mem _ hx)) j

/-- **One module's statements read**: every entry is a requested copy with its position's
statement and kind, off the files of the part it is loaded at; every requested copy has one. -/
theorem readInfosOf_ok {sp : SearchPath} {fs : FS} {ld : Loads} {ix : NameIndex} {i : Nat}
    {cs : Array Copy} {arr : Array (Copy × ConstantVal × CKindF Name Unit)}
    (h : ModelIO.CanGive (readInfosOf (.ofPath sp) ld ix (i, cs)) fs (.ok arr)) :
    (∀ c cv k, (c, cv, k) ∈ arr.toList → c ∈ cs.toList ∧ ∃ q f r a, ix.at c = some q ∧
      ModelIO.CanGive (readFiles sp (ld.nameAt i) ((ld.flags[i]?).getD default).level) fs (.ok f) ∧
      f.viewRegion ((ld.flags[i]?).getD default).level = some (r, a) ∧ StmtSkel r q.loc cv k) ∧
    (∀ c ∈ cs.toList, ∃ cv k, (c, cv, k) ∈ arr.toList) := by
  obtain ⟨hs, hs', h⟩ := h
  simp only [readInfosOf, ModelIO.bind_ok] at h
  obtain ⟨x, hs₁, hx, h⟩ := h
  rcases x with e | f
  · simp at h
  simp only at h
  generalize hst : readStmts f _ _ = st at h
  generalize hkd : readKinds f _ _ = kd at h
  rcases st with _ | ss
  · simp at h
  rcases kd with _ | ks
  · simp at h
  simp only at h
  split at h
  rotate_left
  · simp at h
  rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq] at hlen
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hf : ModelIO.CanGive (readFiles sp (ld.nameAt i) ((ld.flags[i]?).getD default).level) fs
      (.ok f) := ⟨hs, hs₁, hx⟩
  -- the region and the reads
  simp only [readStmts] at hst
  cases hreg : f.viewRegion ((ld.flags[i]?).getD default).level with
  | none => simp [hreg] at hst
  | some ra =>
  obtain ⟨r, a⟩ := ra
  simp only [hreg, Option.bind_eq_bind, Option.bind_some] at hst
  change stmtsAt r _ = some ss at hst
  simp only [readKinds, hreg, Option.bind_eq_bind, Option.bind_some] at hkd
  change List.mapM (kindNamesAt r) _ = some ks at hkd
  rw [stmtsAt_eq] at hst
  generalize hlocs : cs.toList.filterMap (fun c => (ix.at c).map (·.loc)) = locs at hst hkd
  have hl1 := mapM_length_opt hst
  have hl2 := mapM_length_opt hkd
  have hall : ∀ c ∈ cs.toList, ((ix.at c).map (·.loc)).isSome = true :=
    filterMap_length_eq (by rw [hlocs, ← hl1, hlen.1]; simp)
  have hloc : ∀ j (hj : j < cs.size), ∃ q, ix.at cs[j] = some q ∧ locs[j]? = some q.loc := by
    intro j hj
    have := hall cs[j] (by simp)
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 this
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hl
    refine ⟨q, hq, ?_⟩
    rw [← hlocs, filterMap_getElem? hall j, Array.getElem?_toList, Array.getElem?_eq_getElem hj,
      Option.bind_some, hq]
    rfl
  have hent : ∀ j (hj : j < cs.size) (h1 : j < ss.length) (h2 : j < ks.length), ∃ q,
      ix.at cs[j] = some q ∧ StmtSkel r q.loc ss[j] ks[j] := by
    intro j hj hj1 hj2
    obtain ⟨q, hq, hl⟩ := hloc j hj
    refine ⟨q, hq, ?_⟩
    have h1 := mapM_getElem? hst j
    have h2 := mapM_getElem? hkd j
    rw [hl, Option.bind_some] at h1 h2
    rw [List.getElem?_eq_getElem hj1] at h1
    rw [List.getElem?_eq_getElem hj2] at h2
    obtain ⟨sk, hsk, h1⟩ := bind_some_left h1.symm
    simp only [kindNamesAt] at h2
    obtain ⟨sk', hsk', h2⟩ := bind_some_left h2.symm
    rw [hsk] at hsk'; cases hsk'
    simp only [stmtP] at h1
    obtain ⟨n, hn, h1⟩ := bind_some_left h1
    obtain ⟨lps, hlp, h1⟩ := bind_some_left h1
    obtain ⟨ty, hty, h1⟩ := bind_some_left h1
    simp only [pure, Option.some.injEq] at h1
    rw [← h1]
    refine ⟨sk, hsk, hn, hlp, hty, ?_⟩
    rw [← h2]
    congr 1
    funext v
    exact (sparseNameP_eq r v).symm
  refine ⟨fun c cv k hm => ?_, fun c hc => ?_⟩
  · rw [Array.toList_zip] at hm
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hm
    simp only [List.length_zip, Array.length_toList, List.length_zip] at hj
    have hjc : j < cs.size := by omega
    have hj1 : j < ss.length := by omega
    have hj2 : j < ks.length := by omega
    obtain ⟨q, hq, hsk⟩ := hent j hjc hj1 hj2
    simp only [List.getElem_zip, Array.getElem_toList] at hje
    simp only [Prod.mk.injEq] at hje
    obtain ⟨hc, hcv, hk⟩ := hje
    refine ⟨?_, q, f, r, a, ?_, hf, hreg, ?_⟩
    · rw [← hc]; simp
    · rw [← hc]; exact hq
    · rw [← hcv, ← hk]; exact hsk
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    have hjc : j < cs.size := by simpa using hj
    refine ⟨ss[j]'(by omega), ks[j]'(by omega), ?_⟩
    rw [Array.toList_zip]
    refine List.mem_iff_getElem.2 ⟨j, by simp; omega, ?_⟩
    simp

/-- The infos' insert of one entry. -/
@[expose] def insStep (m : Std.HashMap Copy (ConstantVal × CKindF Name Unit))
    (x : Copy × ConstantVal × CKindF Name Unit) : Std.HashMap Copy (ConstantVal × CKindF Name Unit) :=
  match x with
  | (c, s, k) => m.insert c (s, k)

theorem insStep_fold :
    ∀ (L : List (Copy × ConstantVal × CKindF Name Unit)) (m : Std.HashMap Copy (ConstantVal × CKindF Name Unit)),
      (∀ c v, (L.foldl insStep m)[c]? = some v → (c, v.1, v.2) ∈ L ∨ m[c]? = some v) ∧
      (∀ c, (∃ s k, (c, s, k) ∈ L) ∨ (m[c]?).isSome = true → ((L.foldl insStep m)[c]?).isSome = true)
  | [], m => by simp
  | (c₀, s₀, k₀) :: L, m => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := insStep_fold L (insStep m (c₀, s₀, k₀))
    refine ⟨fun c v h => ?_, fun c h => h2 c ?_⟩
    · rcases h1 c v h with hh | hh
      · exact .inl (List.mem_cons_of_mem _ hh)
      · simp only [insStep, Std.HashMap.getElem?_insert] at hh
        by_cases he : (c₀ == c) = true
        · rw [ite_eq_left he] at hh
          obtain rfl := eq_of_beq he
          rw [← Option.some.inj hh]
          exact .inl List.mem_cons_self
        · rw [ite_eq_right he] at hh
          exact .inr hh
    · simp only [insStep, Std.HashMap.getElem?_insert]
      rcases h with ⟨s, k, h⟩ | h
      · rcases List.mem_cons.1 h with h | h
        · cases h; right; simp
        · exact .inl ⟨s, k, h⟩
      · right
        split <;> simp_all

theorem infos_fold :
    ∀ (rs : List (Array (Copy × ConstantVal × CKindF Name Unit)))
      (m : Std.HashMap Copy (ConstantVal × CKindF Name Unit)),
      (∀ c v, (rs.foldl (fun m r => r.foldl insStep m) m)[c]? = some v →
        (∃ r ∈ rs, (c, v.1, v.2) ∈ r.toList) ∨ m[c]? = some v) ∧
      (∀ c, (∃ r ∈ rs, ∃ s k, (c, s, k) ∈ r.toList) ∨ (m[c]?).isSome = true →
        ((rs.foldl (fun m r => r.foldl insStep m) m)[c]?).isSome = true)
  | [], m => by simp
  | r :: rs, m => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := infos_fold rs (r.foldl insStep m)
    obtain ⟨g1, g2⟩ := insStep_fold r.toList m
    rw [Array.foldl_toList] at g1 g2
    refine ⟨fun c v h => ?_, fun c h => h2 c ?_⟩
    · rcases h1 c v h with ⟨r', hr', h⟩ | h
      · exact .inl ⟨r', List.mem_cons_of_mem _ hr', h⟩
      · rcases g1 c v h with h | h
        · exact .inl ⟨r, List.mem_cons_self, h⟩
        · exact .inr h
    · rcases h with ⟨r', hr', s, k, h⟩ | h
      · rcases List.mem_cons.1 hr' with rfl | hr'
        · exact .inr (g2 c (.inl ⟨s, k, h⟩))
        · exact .inl ⟨r', hr', s, k, h⟩
      · exact .inr (g2 c (.inr h))

/-- **The statements read for some copies**: every entry is its copy's position's statement and
kind, off the files of the part its module is loaded at; every requested copy has one. -/
theorem readInfos_ok {sp : SearchPath} {fs : FS} {ld : Loads} {ix : NameIndex} {jobs : Nat}
    {cs : Array Copy} {infos : Std.HashMap Copy (ConstantVal × CKindF Name Unit)}
    (h : ModelIO.CanGive (readInfos (.ofPath sp) ld ix jobs cs) fs (.ok infos)) :
    (∀ c v, infos[c]? = some v → ∃ q f r a, ix.at c = some q ∧
      ModelIO.CanGive (readFiles sp (ld.nameAt c.mod) ((ld.flags[c.mod]?).getD default).level) fs
        (.ok f) ∧
      f.viewRegion ((ld.flags[c.mod]?).getD default).level = some (r, a) ∧ StmtSkel r q.loc v.1 v.2) ∧
    (∀ c ∈ cs.toList, (infos[c]?).isSome = true) := by
  obtain ⟨hs, hs', h⟩ := h
  simp only [readInfos, ModelIO.bind_ok] at h
  obtain ⟨x, hs₁, hx, h⟩ := h
  rcases x with e | rs
  · simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hx' : (mapExcept (readInfosOf (.ofPath sp) ld ix) (byModule cs).toList : ModelIO _) fs hs
    (.ok (.ok rs)) hs₁ := hx
  obtain ⟨hlen, hget⟩ := mapExcept_getElem hx'
  obtain ⟨b1, b2⟩ := byModule_spec cs
  obtain ⟨f1, f2⟩ := infos_fold rs {}
  have hfold : (rs.foldl (fun m r => r.foldl (fun m (x : Copy × ConstantVal × CKindF Name Unit) =>
      match x with | (c, s, k) => m.insert c (s, k)) m) {}) =
      rs.foldl (fun m r => r.foldl insStep m) {} := rfl
  rw [hfold]
  refine ⟨fun c v hv => ?_, fun c hc => f2 c (.inl ?_)⟩
  · rcases f1 c v hv with ⟨r, hr, hm⟩ | hm
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
      obtain ⟨⟨i, g⟩, hxg, hcan⟩ := hget j _ (List.getElem?_eq_getElem hj)
      obtain ⟨ha, -⟩ := readInfosOf_ok hcan
      obtain ⟨hcg, q, f, r, a, hq, hf, hreg, hsk⟩ := ha c v.1 v.2 hm
      have hmod := (b1 i g (Array.mem_toList_iff.1 (List.mem_of_getElem? hxg)) c hcg).1
      subst hmod
      exact ⟨q, f, r, a, hq, hf, hreg, hsk⟩
    · simp at hm
  · obtain ⟨g, hg, hcg⟩ := b2 c hc
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (Array.mem_toList_iff.2 hg)
    have hj' : j < rs.length := by rw [hlen]; exact hj
    obtain ⟨x, hxg, hcan⟩ := hget j _ (List.getElem?_eq_getElem hj')
    rw [List.getElem?_eq_getElem hj, hje] at hxg
    cases hxg
    obtain ⟨-, hb⟩ := readInfosOf_ok hcan
    obtain ⟨s, k, hm⟩ := hb c hcg
    exact ⟨_, List.getElem_mem hj', s, k, hm⟩

/-! ## The worker's reads -/

/-- **What an accepting `workerReads` built**: the index of the loaded parts, the statements it
read for the doubly held names, the clashes from them, and Lean's merge rule passed on each. -/
theorem workerReads_open {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {wr : WorkerReads}
    {hs hs' : HS} (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs') :
    wr.index = nameIndexOf wr.index.parts ∧
    (∃ infos, ModelIO.CanGive (readInfos (.ofPath sp) wr.loads wr.index jobs
        ((clashCopies wr.index).flatMap (·.2))) fs (.ok infos) ∧
      wr.clashes = (clashCopies wr.index).map fun (n, cs) =>
        { name := n, copies := cs.filterMap fun c => (infos[c]?).map fun (s, k) => (c, s, k) }) ∧
    ∃ headTy, wr.clashes.toList.forM (clashOk wr.loads headTy) = .ok () := by
  simp only [workerReads, ModelIO.bind_ok] at h
  obtain ⟨a, _, -, h⟩ := h
  rcases a with e | own
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨b, _, hb, h⟩ := h
  rcases b with e | ld
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨c, _, hc, h⟩ := h
  rcases c with e | parts
  · simp at h
  simp only at h
  generalize importsModulesOk _ _ _ _ _ = z at h
  rcases z with e | u
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨d, hs₁, hd, h⟩ := h
  rcases d with e | infos
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨d, _, -, h⟩ := h
  rcases d with e | hinfos
  · simp at h
  simp only at h
  generalize hfm : (List.forM _ _ : Except CheckError Unit) = z at h
  rcases z with e | u
  · simp at h
  simp only at h
  generalize freshOk _ _ _ _ = z at h
  rcases z with e | u
  · simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  exact ⟨rfl, ⟨infos, ⟨_, _, hd⟩, rfl⟩, _, hfm⟩

/-- **A copy's spot**: the part its module is loaded at, and its name position there. -/
@[expose] def spotOf (wr : WorkerReads) (cp : Copy) (q : NamePosition) : Spot :=
  ⟨⟨wr.loads.nameAt cp.mod, ((wr.loads.flags[cp.mod]?).getD default).level⟩, q⟩

/-- **The worker's index, copy by copy** (`IdxInv` at the end of the parts): every copy the
index records is a position of its name; every name position of a loaded part is a copy, recorded
as its name's first copy or a later one; a later copy is not its name's first; the first copy's
module comes no later; and a copy is one on the snapshot (`CopyAt` at its spot). -/
theorem workerIndex_copies {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {wr : WorkerReads}
    {hs hs' : HS} (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs') :
    (∀ i t q, wr.index.parts[i]? = some t → q ∈ t.consts →
      ∃ cp, cp.mod = i ∧ wr.index.at cp = some q) ∧
    (∀ n cp, wr.index.first[n]? = some cp → ∃ q, wr.index.at cp = some q ∧ q.name = n) ∧
    (∀ n cp, (n, cp) ∈ wr.index.more.toList → (∃ q, wr.index.at cp = some q ∧ q.name = n) ∧
      ∃ cp₀, wr.index.first[n]? = some cp₀ ∧ cp₀ ≠ cp) ∧
    (∀ cp q, wr.index.at cp = some q →
      wr.index.first[q.name]? = some cp ∨ (q.name, cp) ∈ wr.index.more.toList) ∧
    (∀ n cp₀ cp q, wr.index.first[n]? = some cp₀ → wr.index.at cp = some q → q.name = n →
      cp₀.mod ≤ cp.mod) ∧
    (∀ cp q, wr.index.at cp = some q → CopyAt sp fs (spotOf wr cp q)) := by
  obtain ⟨hix, -⟩ := workerReads_open h
  obtain ⟨hparts, -⟩ := workerReads_index h
  have hI := nameIndexOf_spec wr.index.parts
  rw [← hix] at hI
  have hat : ∀ c, wr.index.at c = atP wr.index.parts c := by
    intro c; rw [hix, atP_eq]; rfl
  refine ⟨fun i t q ht hq => ?_, fun n cp hf => ?_, fun n cp hm => ?_, fun cp q ha => ?_,
    fun n cp₀ cp q hf ha hn => ?_, fun cp q ha => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hq
    exact ⟨⟨i, k⟩, rfl, by rw [hat]; simp [atP, ht, hk]⟩
  · obtain ⟨-, q, ha, hn⟩ := hI.hfirst n cp hf
    exact ⟨q, by rw [hat]; exact ha, hn⟩
  · obtain ⟨-, ⟨q, ha, hn⟩, h3⟩ := hI.hmore n cp hm
    exact ⟨⟨q, by rw [hat]; exact ha, hn⟩, h3⟩
  · rw [hat] at ha
    exact hI.hall cp q (done_all ha) ha
  · rw [hat] at ha
    exact hI.hleast n cp₀ cp hf (done_all ha) ⟨q, ha, hn⟩
  · rw [hat] at ha
    simp only [atP] at ha
    cases hp : wr.index.parts[cp.mod]? with
    | none => simp [hp] at ha
    | some t =>
      simp only [hp, Option.bind_some] at ha
      exact ⟨t, hparts cp.mod t hp, Array.mem_of_getElem? ha⟩

/-- **Two copies of one name make a clash**, listing both with their statements. -/
theorem workerClash_complete {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat}
    {wr : WorkerReads} {hs hs' : HS}
    (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs')
    {y : Name} {cp cp' : Copy} {q q' : NamePosition} (hne : cp ≠ cp')
    (hq : wr.index.at cp = some q) (hq' : wr.index.at cp' = some q') (hn : q.name = y)
    (hn' : q'.name = y) :
    ∃ cl ∈ wr.clashes.toList, cl.name = y ∧ (∃ cv kd, (cp, cv, kd) ∈ cl.copies.toList) ∧
      ∃ cv kd, (cp', cv, kd) ∈ cl.copies.toList := by
  obtain ⟨-, ⟨infos, hinf, hcl⟩, -⟩ := workerReads_open h
  obtain ⟨-, -, hmore, hall, -, -⟩ := workerIndex_copies h
  obtain ⟨c1, c2⟩ := clashCopies_spec (ix := wr.index) fun n c hm => by
    obtain ⟨-, cp₀, hf, -⟩ := hmore n c hm
    rw [hf]; rfl
  obtain ⟨-, hcomp⟩ := readInfos_ok hinf
  -- one of the two is a later copy
  have hsome : ∃ c, (y, c) ∈ wr.index.more.toList := by
    rcases hall cp q hq with h1 | h1
    · rcases hall cp' q' hq' with h2 | h2
      · rw [hn] at h1; rw [hn'] at h2
        rw [h1] at h2
        exact absurd (Option.some.inj h2) hne
      · exact ⟨cp', hn' ▸ h2⟩
    · exact ⟨cp, hn ▸ h1⟩
  obtain ⟨c, hc⟩ := hsome
  obtain ⟨a, ha⟩ := c2 y c hc
  have hmem : ∀ {d : Copy} {p : NamePosition}, wr.index.at d = some p → p.name = y →
      d ∈ a.toList := fun {d p} hd hp => by
    rw [c1 y a ha d, ← hp]
    rcases hall d p hd with h1 | h1
    · exact .inl h1
    · exact .inr h1
  have hentry : ∀ {d : Copy}, d ∈ a.toList → ∃ cv kd,
      (d, cv, kd) ∈ (a.filterMap fun c => (infos[c]?).map fun (s, k) => (c, s, k)).toList := by
    intro d hd
    have hreq : d ∈ ((clashCopies wr.index).flatMap (·.2)).toList := by
      simp only [Array.toList_flatMap, List.mem_flatMap]
      exact ⟨(y, a), Array.mem_toList_iff.2 ha, hd⟩
    obtain ⟨⟨cv, kd⟩, hv⟩ := Option.isSome_iff_exists.1 (hcomp d hreq)
    refine ⟨cv, kd, ?_⟩
    simp only [Array.toList_filterMap, List.mem_filterMap]
    exact ⟨d, hd, by simp [hv]⟩
  refine ⟨{ name := y, copies := a.filterMap fun c => (infos[c]?).map fun (s, k) => (c, s, k) },
    ?_, rfl, hentry (hmem hq hn), hentry (hmem hq' hn')⟩
  rw [hcl, Array.toList_map]
  exact List.mem_map.2 ⟨(y, a), Array.mem_toList_iff.2 ha, rfl⟩

/-- **A clash copy's statement and kind are its position's**, read off the skeleton of the part
its module is loaded at, and of the clash's name. -/
theorem workerClash_stmt {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {wr : WorkerReads}
    {hs hs' : HS} (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs')
    {cl : Clash} (hcl : cl ∈ wr.clashes.toList) {cp : Copy} {cv : ConstantVal}
    {kd : CKindF Name Unit} (he : (cp, cv, kd) ∈ cl.copies.toList) :
    ∃ q, wr.index.at cp = some q ∧ CopyAt sp fs (spotOf wr cp q) ∧
      (∃ rg, PartRegion sp fs (spotOf wr cp q).part rg ∧ StmtSkel rg q.loc cv kd) ∧
      q.name = cl.name ∧ cv.name = cl.name := by
  obtain ⟨-, ⟨infos, hinf, hcls⟩, -⟩ := workerReads_open h
  obtain ⟨-, hfirst, hmore, -, -, hcopy⟩ := workerIndex_copies h
  obtain ⟨c1, -⟩ := clashCopies_spec (ix := wr.index) fun n c hm => by
    obtain ⟨-, cp₀, hf, -⟩ := hmore n c hm
    rw [hf]; rfl
  obtain ⟨hsound, -⟩ := readInfos_ok hinf
  rw [hcls, Array.toList_map] at hcl
  obtain ⟨⟨n, a⟩, ha, rfl⟩ := List.mem_map.1 hcl
  simp only [Array.toList_filterMap, List.mem_filterMap] at he
  obtain ⟨d, hd, hdv⟩ := he
  cases hv : infos[d]? with
  | none => simp [hv] at hdv
  | some v =>
  simp only [hv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdv
  obtain ⟨rfl, hv1, hv2⟩ := hdv
  obtain ⟨q, f, r, a', hq, hf, hreg, hsk⟩ := hsound d v hv
  rw [hv1, hv2] at hsk
  have hqn : q.name = n := by
    rcases (c1 n a (Array.mem_toList_iff.1 ha) d).1 hd with h1 | h1
    · obtain ⟨q', hq', hn⟩ := hfirst n d h1
      rw [hq] at hq'; cases hq'; exact hn
    · obtain ⟨⟨q', hq', hn⟩, -⟩ := hmore n d h1
      rw [hq] at hq'; cases hq'; exact hn
  have hreg' : PartRegion sp fs (spotOf wr d q).part r := ⟨f, a', hf, hreg⟩
  have hcp := hcopy d q hq
  refine ⟨q, hq, hcp, ⟨r, hreg', hsk⟩, hqn, ?_⟩
  rw [copyAt_stmt_name hcp hreg' hsk]
  exact hqn

theorem forM_ok_all {α : Type} {f : α → Except CheckError Unit} :
    ∀ {l : List α}, l.forM f = .ok () → ∀ x ∈ l, f x = .ok ()
  | [], _, x, hx => by simp at hx
  | a :: l, h, x, hx => by
    simp only [List.forM] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok u =>
      rw [ha] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact forM_ok_all h x hx

/-- One statement: name, type and level parameters. -/
@[expose] def SameStmt (a b : ConstantVal) : Prop :=
  a.name = b.name ∧ a.type = b.type ∧ a.levelParams = b.levelParams

theorem subsumesF_same {E E' : Type} {headTy : Name → Option Expr} {cv₁ : ConstantVal}
    {k₁ : CKindF Name E} {cv₂ : ConstantVal} {k₂ : CKindF Name E'}
    (h : subsumesF headTy cv₁ k₁ cv₂ k₂ = true) : SameStmt cv₁ cv₂ := by
  simp only [subsumesF, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem SameStmt.trans {a b c : ConstantVal} (h₁ : SameStmt a b) (h₂ : SameStmt b c) :
    SameStmt a c := ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

theorem SameStmt.symm {a b : ConstantVal} (h : SameStmt a b) : SameStmt b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem clashOk_fold {X : Type} (stmt : X → ConstantVal) {g : X → X → Except CheckError X}
    (hg : ∀ a b r, g a b = .ok r → SameStmt (stmt b) (stmt a) ∧ (r = a ∨ r = b)) (k₀ : ConstantVal) :
    ∀ (rest : List X) (kept r : X), SameStmt (stmt kept) k₀ → rest.foldlM g kept = .ok r →
      ∀ x ∈ rest, SameStmt (stmt x) k₀
  | [], _, _, _, _, x, hx => by simp at hx
  | b :: rest, kept, r, hk, h, x, hx => by
    simp only [List.foldlM_cons] at h
    cases hb : g kept b with
    | error e => rw [hb] at h; cases h
    | ok r' =>
      rw [hb] at h
      obtain ⟨hs, hr'⟩ := hg kept b r' hb
      have hb' : SameStmt (stmt b) k₀ := hs.trans hk
      have hr'' : SameStmt (stmt r') k₀ := by rcases hr' with rfl | rfl <;> assumption
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hb'
      · exact clashOk_fold stmt hg k₀ rest r' r hr'' h x hx

/-- **A clash's copies share one statement**: Lean's merge rule passed on it, and it compares
names, types and level parameters. -/
theorem workerClash_same {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {wr : WorkerReads}
    {hs hs' : HS} (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs')
    {cl : Clash} (hcl : cl ∈ wr.clashes.toList) {e₁ e₂ : Copy × ConstantVal × CKindF Name Unit}
    (h₁ : e₁ ∈ cl.copies.toList) (h₂ : e₂ ∈ cl.copies.toList) : SameStmt e₁.2.1 e₂.2.1 := by
  obtain ⟨-, -, headTy, hfm⟩ := workerReads_open h
  have hok := forM_ok_all hfm cl hcl
  simp only [clashOk] at hok
  generalize hcs : cl.copies.toList = l at hok h₁ h₂
  rcases l with _ | ⟨k, rest⟩
  · simp at h₁
  simp only at hok
  generalize hr : List.foldlM (m := Except CheckError) _ k rest = res at hok
  rcases res with e | r
  · cases hok
  have hall := clashOk_fold (fun x : Copy × ConstantVal × CKindF Name Unit => x.2.1)
    (fun a b r hab => by
      obtain ⟨_, cv₂, k₂⟩ := a
      obtain ⟨_, cv₁, k₁⟩ := b
      simp only at hab ⊢
      split at hab
      · rename_i h1
        exact ⟨subsumesF_same h1, .inr (Except.ok.inj hab).symm⟩
      · split at hab
        · rename_i h2
          exact ⟨(subsumesF_same h2).symm, .inl (Except.ok.inj hab).symm⟩
        · cases hab) k.2.1 rest k r ⟨rfl, rfl, rfl⟩ hr
  have hk : ∀ x ∈ k :: rest, SameStmt x.2.1 k.2.1 := fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨rfl, rfl, rfl⟩
    · exact hall x hx
  obtain ⟨a1, a2, a3⟩ := hk e₁ h₁
  obtain ⟨b1, b2, b3⟩ := hk e₂ h₂
  exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩

/-- **The reach's table of the clashes' copies**: a name's entry lists the copies of a clash of
that name, each with its module and statement. -/
theorem clashCopiesOf_spec {wr : WorkerReads} {n : Name} {cs : Array (Name × ConstantVal)}
    (h : (clashCopiesOf wr)[n]? = some cs) {k : Name} {cv : ConstantVal} (hk : (k, cv) ∈ cs.toList) :
    ∃ cl ∈ wr.clashes.toList, cl.name = n ∧
      ∃ cp kd, (cp, cv, kd) ∈ cl.copies.toList ∧ k = wr.loads.nameAt cp.mod := by
  have key : ∀ (l : List Clash) (m : Std.HashMap Name (Array (Name × ConstantVal))),
      (l.foldl (fun (m : Std.HashMap Name (Array (Name × ConstantVal))) (cl : Clash) => m.insert cl.name
        (cl.copies.map fun (cp, cv, _) => (wr.loads.nameAt cp.mod, cv))) m)[n]? = some cs →
      (∃ cl ∈ l, cl.name = n ∧ cs = cl.copies.map fun (cp, cv, _) => (wr.loads.nameAt cp.mod, cv)) ∨
        m[n]? = some cs := by
    intro l
    induction l with
    | nil => intro m h; exact .inr h
    | cons cl l ih =>
      intro m h
      rw [List.foldl_cons] at h
      rcases ih _ h with ⟨cl', hcl', h1, h2⟩ | h
      · exact .inl ⟨cl', List.mem_cons_of_mem _ hcl', h1, h2⟩
      · rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i he
          exact .inl ⟨cl, List.mem_cons_self, eq_of_beq he, (Option.some.inj h).symm⟩
        · exact .inr h
  have h' : (wr.clashes.toList.foldl (fun (m : Std.HashMap Name (Array (Name × ConstantVal)))
      (cl : Clash) => m.insert cl.name
      (cl.copies.map fun (cp, cv, _) => (wr.loads.nameAt cp.mod, cv))) {})[n]? = some cs := by
    rw [Array.foldl_toList]; exact h
  rcases key _ _ h' with ⟨cl, hcl, hn, rfl⟩ | h
  · refine ⟨cl, hcl, hn, ?_⟩
    rw [Array.toList_map] at hk
    obtain ⟨⟨cp, cv', kd⟩, he, hkv⟩ := List.mem_map.1 hk
    simp only [Prod.mk.injEq] at hkv
    obtain ⟨rfl, rfl⟩ := hkv
    exact ⟨cp, kd, he, rfl⟩
  · simp at h

/-! ## The load order -/

/-- **What an accepting `workerReads` loaded**: its own private part's name table, the header
fixpoint from that part's header, the public-import closures of that load order, one loaded part
per module of the order, the own part's names fresh (none is a loaded name), and every clash copy
of a module of the order. -/
theorem workerReads_loads {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {wr : WorkerReads}
    {hs hs' : HS} (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs') :
    ∃ own, ModelIO.CanGive (readPartNames sp (m, .private)) fs (.ok own) ∧
      ModelIO.CanGive (headerFixpoint (moduleImports sp) own.header.isModule own.header.imports) fs
        (.ok wr.loads) ∧
      wr.pub = pubClosures wr.loads ∧ wr.index.parts.size = wr.loads.order.size ∧ wr.own = own ∧
      (∀ q ∈ own.consts, wr.index.first.contains q.name = false) ∧
      ∀ cl ∈ wr.clashes.toList, ∀ x ∈ cl.copies.toList, x.1.mod < wr.loads.order.size := by
  have hcl : ∀ (cl : Clash), cl ∈ wr.clashes.toList → ∀ (x : Copy × ConstantVal × CKindF Name Unit),
      x ∈ cl.copies.toList → ∃ q, wr.index.at x.1 = some q := by
    intro cl hcl' x hx
    obtain ⟨q, hq, -⟩ := workerClash_stmt h hcl' (cp := x.1) (cv := x.2.1) (kd := x.2.2) hx
    exact ⟨q, hq⟩
  have hix := (workerReads_open h).1
  simp only [workerReads, ModelIO.bind_ok] at h
  obtain ⟨a, hs₀, ha, h⟩ := h
  rcases a with e | own
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨b, _, hb, h⟩ := h
  rcases b with e | ld
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨c, _, hc, h⟩ := h
  rcases c with e | parts
  · simp at h
  simp only at h
  generalize importsModulesOk _ _ _ _ _ = z at h
  rcases z with e | u
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨d, _, -, h⟩ := h
  rcases d with e | infos
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨d, _, -, h⟩ := h
  rcases d with e | hinfos
  · simp at h
  simp only at h
  generalize (List.forM _ _ : Except CheckError Unit) = z at h
  rcases z with e | u
  · simp at h
  simp only at h
  generalize hfr : freshOk _ _ _ _ = z at h
  rcases z with e | u
  · simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  have hb' : ModelIO.CanGive (headerFixpoint (moduleImports sp) own.header.isModule
      own.header.imports) fs (.ok ld) := ⟨_, _, hb⟩
  obtain ⟨hfl, -⟩ := headerFixpoint_sound hb'
  have hc' : (mapExcept (readPartNames sp) ((ld.order.zip ld.flags).toList.map
      fun (n, fl) => (n, fl.level)) : ModelIO _) fs _ (.ok (.ok parts)) _ := hc
  obtain ⟨hlen, -⟩ := mapExcept_getElem hc'
  have hsize : parts.toArray.size = ld.order.size := by
    simp only [List.size_toArray, hlen, List.length_map, Array.toList_zip, List.length_zip,
      Array.length_toList, hfl, Nat.min_self]
  refine ⟨own, ⟨_, _, ha⟩, hb', rfl, hsize, rfl, fun q hq => ?_, fun cl hcl' x hx => ?_⟩
  · simp only [freshOk] at hfr
    split at hfr
    · rename_i hnone
      have := Array.find?_eq_none.1 hnone q hq
      simpa using this
    · cases hfr
  · obtain ⟨q, hq⟩ := hcl cl hcl' x hx
    rw [hix] at hq
    rw [atP_eq] at hq
    simp only [atP] at hq
    cases hp : (nameIndexOf parts.toArray).parts[x.1.mod]? with
    | none => simp [hp] at hq
    | some t =>
      have := (Array.getElem?_eq_some_iff.1 hp).1
      exact hsize ▸ this

end ConLeche.Driver
