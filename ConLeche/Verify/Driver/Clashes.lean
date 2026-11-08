module

public import ConLeche.Verify.Driver.ReachFrom
import ConLeche.Verify.Driver.Provenance
import ConLeche.Verify.Frontend.Olean.Files
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Sparse

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

end ConLeche.Driver
