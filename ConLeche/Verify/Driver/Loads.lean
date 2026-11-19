module

public import ConLeche.Verify.Frontend.ModelIO
public import ConLeche.Verify.Frontend.Olean.Roots
import ConLeche.Verify.Frontend.Olean.Files
import Std.Data.HashSet.Lemmas
import ConLeche.Verify.Frontend.Olean.Engine
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Reads
import Std.Data.HashMap.Lemmas
public import ConLeche.Frontend.Olean

/-!
# What the header fixpoint loads, on a snapshot

What the composition (task #501) reads off a worker's header fixpoint (`headerFixpoint`,
`ConLeche/Frontend/Olean/Levels.lean`) over the search path's header reads (`moduleImports`):

* `headerFixpoint_sound` — every loaded module is reached from the root's imports by import
  edges (`ImpReach`), with the imports its header read answers, each loaded once, and the
  index naming each module's position;
* `headerFixpoint_complete` — every module a path of public imports leads to from one of the
  root's imports (`PubReach`) is loaded: the root is loaded whole, and a public import is
  followed from every loaded module;
* `pubClosures_pubReach` — a module of a loaded module's public-import closure
  (`pubClosures`) is reached from it by a path of public imports;
* `headerFixpoint_unique` — the fixpoint is determined on a snapshot (`moduleImports_unique`);
* `readPartNames_header` — where a module's private view loads, its private part's name table
  holds the imports its header read answers: a worker's root imports are the graph's edges.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-! ## Paths of imports -/

/-- **A module reached from an import list** by import edges, each module's imports what its
header read answers on the snapshot. -/
inductive ImpReach (sp : Roots) (fs : FS) (imps0 : Array ImportRec) : Name → Prop
  | root {i : ImportRec} : i ∈ imps0 → ImpReach sp fs imps0 i.module
  | step {a : Name} {is : Array ImportRec} {i : ImportRec} : ImpReach sp fs imps0 a →
      ModelIO.CanGive (moduleImports sp a) fs (.ok is) → i ∈ is → ImpReach sp fs imps0 i.module

/-- **A path of public imports** from `a`, each module's imports what its header read answers on
the snapshot. -/
inductive PubReach (sp : Roots) (fs : FS) (a : Name) : Name → Prop
  | refl : PubReach sp fs a a
  | step {b : Name} {is : Array ImportRec} {i : ImportRec} : PubReach sp fs a b →
      ModelIO.CanGive (moduleImports sp b) fs (.ok is) → i ∈ is → i.isExported = true →
      PubReach sp fs a i.module

theorem PubReach.trans {sp : Roots} {fs : FS} {a b c : Name} (h₁ : PubReach sp fs a b)
    (h₂ : PubReach sp fs b c) : PubReach sp fs a c := by
  induction h₂ with
  | refl => exact h₁
  | step _ hi hm he ih => exact .step ih hi hm he

/-! ## The header read is determined -/

/-- **A module's imports, on a snapshot, are one list**: two value outcomes of its header read
agree. -/
theorem moduleImports_unique {sp : Roots} {m : Name} {fs : FS} {hs₁ hs₁' hs₂ hs₂' : HS}
    {a b : Array ImportRec} (ha : (moduleImports sp m : ModelIO _) fs hs₁ (.ok (.ok a)) hs₁')
    (hb : (moduleImports sp m : ModelIO _) fs hs₂ (.ok (.ok b)) hs₂') : a = b := by
  simp only [moduleImports, ModelIO.bind_ok] at ha hb
  obtain ⟨x, _, hx, ha⟩ := ha
  obtain ⟨y, _, hy, hb⟩ := hb
  rcases x with e | loc
  · simp at ha
  rcases y with e | loc'
  · simp at hb
  have hl : Except.ok loc' = (Except.ok loc : Except CheckError Located) :=
    (findModule_ok hx).ok hy
  cases hl
  obtain ⟨ba, hfa, hia⟩ := readImportsAt_ok ha
  obtain ⟨bb, hfb, hib⟩ := readImportsAt_ok hb
  rw [hfa] at hfb
  cases hfb
  rw [hia] at hib
  exact Option.some.inj hib

theorem moduleImports_canGive_unique {sp : Roots} {m : Name} {fs : FS}
    {a b : Array ImportRec} (ha : ModelIO.CanGive (moduleImports sp m) fs (.ok a))
    (hb : ModelIO.CanGive (moduleImports sp m) fs (.ok b)) : a = b :=
  let ⟨_, _, ha⟩ := ha
  let ⟨_, _, hb⟩ := hb
  moduleImports_unique ha hb

/-! ## Bits -/

theorem hasBit_testBit (b : UInt8) (q : Nat) (hq : q < 8) :
    ((b >>> q.toUInt8 &&& 1) == 1) = b.toNat.testBit q := by
  have h1 : ∀ x : UInt8, ((x &&& 1) == 1) = (x.toNat % 2 == 1) := by
    intro x
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← UInt8.toNat_inj, UInt8.toNat_and]
    simp [Nat.and_one_is_mod]
  rw [h1, UInt8.toNat_shiftRight, Nat.testBit_eq_decide_div_mod_eq]
  have : (q.toUInt8.toNat % 8) = q := by simp; omega
  rw [this, Nat.shiftRight_eq_div_pow]
  cases Nat.mod_two_eq_zero_or_one (b.toNat / 2 ^ q) <;> simp_all

theorem hasBit_or (b c : UInt8) (q : Nat) (hq : q < 8) :
    ((b ||| c) >>> q.toUInt8 &&& 1 == 1) =
      ((b >>> q.toUInt8 &&& 1 == 1) || (c >>> q.toUInt8 &&& 1 == 1)) := by
  rw [hasBit_testBit _ _ hq, hasBit_testBit _ _ hq, hasBit_testBit _ _ hq, UInt8.toNat_or,
    Nat.testBit_or]

theorem hasBit_one (r q : Nat) (hq : q < 8) (hr : r < 8) :
    (((1 : UInt8) <<< r.toUInt8) >>> q.toUInt8 &&& 1 == 1) = decide (r = q) := by
  rw [hasBit_testBit _ _ hq, UInt8.toNat_shiftLeft]
  have : (r.toUInt8.toNat % 8) = r := by simp; omega
  rw [this, UInt8.toNat_one, Nat.one_shiftLeft, Nat.mod_eq_of_lt (by
    have : 2 ^ r ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    simp at this ⊢; omega), Nat.testBit_two_pow]

theorem hasBit_zero (q : Nat) (hq : q < 8) : ((0 : UInt8) >>> q.toUInt8 &&& 1 == 1) = false := by
  rw [hasBit_testBit _ _ hq]; simp

/-! ## Sets of positions -/

theorem ByteArray.get!_eq (s : ByteArray) (k : Nat) : s.get! k = s.data[k]! := by
  cases s; rfl

theorem ByteArray.get!_set! (s : ByteArray) (k j : Nat) (v : UInt8) :
    (s.set! k v).get! j = if k = j ∧ k < s.size then v else s.get! j := by
  cases s with
  | mk d =>
  simp only [ByteArray.set!, ByteArray.get!_eq, ByteArray.size]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  split
  · next h =>
    obtain ⟨rfl, h⟩ := h
    rw [Array.getElem?_setIfInBounds_self_of_lt h]; rfl
  · next h =>
    by_cases hkj : k = j
    · subst hkj
      have : ¬ k < d.size := fun h' => h ⟨rfl, h'⟩
      simp only [Array.setIfInBounds, this, ↓reduceDIte]
    · rw [Array.getElem?_setIfInBounds_ne hkj]

theorem ModSet.has_mono {s : ModSet} {i : Nat} :
    s.has i = ((s.get! (i / 8) >>> (i % 8).toUInt8 &&& 1) == 1) := rfl

theorem ModSet.has_empty (n i : Nat) : (ModSet.empty n).has i = false := by
  have h0 : (ModSet.empty n).get! (i / 8) = 0 := by
    simp only [ModSet.empty, ByteArray.get!_eq, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    by_cases h : i / 8 < (n + 7) / 8
    · simp [h]
    · rw [Array.getElem?_eq_none (by simpa using h)]; rfl
  rw [ModSet.has_mono, h0]
  exact hasBit_zero _ (Nat.mod_lt _ (by decide))

theorem ModSet.has_add {s : ModSet} {i j : Nat} (h : (s.add i).has j = true) :
    s.has j = true ∨ j = i := by
  unfold ModSet.add at h
  split at h
  · rename_i hin
    rw [ModSet.has_mono, ByteArray.get!_set!] at h
    split at h
    · rename_i hk
      rw [hasBit_or _ _ _ (Nat.mod_lt _ (by decide)),
        hasBit_one _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))] at h
      rcases Bool.or_eq_true_iff.1 h with h | h
      · left; rw [ModSet.has_mono, ← hk.1]; exact h
      · right
        have := of_decide_eq_true h
        omega
    · left; exact h
  · left; exact h

theorem ModSet.has_union {s t : ModSet} {j : Nat} (h : (s.union t).has j = true) :
    s.has j = true ∨ t.has j = true := by
  unfold ModSet.union at h
  -- every byte of the fold is the start's, or'ed with `t`'s
  have key : ∀ n : Nat, ∀ k q, q < 8 →
      ((n.fold (fun k _ (x : ModSet) => x.set! k (x.get! k ||| t.get! k)) s).get! k >>> q.toUInt8
        &&& 1 == 1) = true →
      (s.get! k >>> q.toUInt8 &&& 1 == 1) = true ∨ (t.get! k >>> q.toUInt8 &&& 1 == 1) = true := by
    intro n
    induction n with
    | zero => intro k q _ h; rw [Nat.fold_zero] at h; exact .inl h
    | succ n ih =>
      intro k q hq h
      rw [Nat.fold_succ, ByteArray.get!_set!] at h
      split at h
      · rename_i hk
        obtain ⟨rfl, -⟩ := hk
        rw [hasBit_or _ _ _ hq] at h
        rcases Bool.or_eq_true_iff.1 h with h | h
        · exact ih _ _ hq h
        · exact .inr h
      · exact ih _ _ hq h
  rw [ModSet.has_mono] at h
  exact key _ _ _ (Nat.mod_lt _ (by decide)) h

/-! ## The public-import closures -/

/-- **A path of public imports between positions of a load order**, through its imports and its
index. -/
inductive PubPos (ld : Loads) : Nat → Nat → Prop
  | refl (a : Nat) : PubPos ld a a
  | cons {a b c : Nat} {imp : ImportRec} : imp ∈ (ld.imports[a]?).getD #[] →
      imp.isExported = true → ld.index[imp.module]? = some b → PubPos ld b c → PubPos ld a c

/-- One position's closure, as `pubClosures` builds it from the earlier ones. -/
theorem pubClosures_step (ld : Loads) (acc : Array ModSet) (i : Nat)
    (hacc : ∀ k (hk : k < acc.size), ∀ j, acc[k].has j = true → PubPos ld k j) :
    ∀ (l : List ImportRec) (s : ModSet), (∀ imp ∈ l, imp ∈ (ld.imports[i]?).getD #[]) →
      (∀ j, s.has j = true → PubPos ld i j) →
      ∀ j, (l.foldl (fun s imp =>
        if !imp.isExported then s else
        match ld.index[imp.module]? with
        | some j => if j < acc.size then s.union acc[j]! else s.add j
        | none => s) s).has j = true → PubPos ld i j
  | [], s, _, hs => hs
  | imp :: l, s, hl, hs => by
    simp only [List.foldl_cons]
    refine pubClosures_step ld acc i hacc l _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ?_
    have himp := hl imp List.mem_cons_self
    cases he : imp.isExported
    · simpa using hs
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i b hb
        split
        · rename_i hlt
          intro j hj
          rcases ModSet.has_union hj with hj | hj
          · exact hs j hj
          · rw [getElem!_pos acc b hlt] at hj
            exact .cons himp he hb (hacc b hlt j hj)
        · intro j hj
          rcases ModSet.has_add hj with hj | rfl
          · exact hs j hj
          · exact .cons himp he hb (.refl _)
      · exact hs

/-- One position's closure, as `pubClosures` builds it. -/
@[expose] def pubStep (ld : Loads) (acc : Array ModSet) (i : Nat) : ModSet :=
  ((ld.imports[i]?).getD #[]).foldl (fun s imp =>
    if !imp.isExported then s else
    match ld.index[imp.module]? with
    | some j => if j < acc.size then s.union acc[j]! else s.add j
    | none => s) ((ModSet.empty ld.order.size).add i)

theorem pubClosures_eq (ld : Loads) :
    pubClosures ld = (List.range ld.order.size).foldl (fun (acc : Array ModSet) i => acc.push (pubStep ld acc i))
      (Array.mkEmpty ld.order.size) := rfl

theorem pubClosures_range (ld : Loads) : ∀ n : Nat,
    ((List.range n).foldl (fun (acc : Array ModSet) i => acc.push (pubStep ld acc i))
      (Array.mkEmpty ld.order.size)).size = n ∧
    ∀ k (hk : k < ((List.range n).foldl (fun (acc : Array ModSet) i => acc.push (pubStep ld acc i))
      (Array.mkEmpty ld.order.size)).size), ∀ j,
      ((List.range n).foldl (fun (acc : Array ModSet) i => acc.push (pubStep ld acc i))
        (Array.mkEmpty ld.order.size))[k].has j = true → PubPos ld k j
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hsz, hacc⟩ := pubClosures_range ld n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun (acc : Array ModSet) i => acc.push (pubStep ld acc i))
      (Array.mkEmpty ld.order.size) = acc at hsz hacc
    refine ⟨by simp [hsz], fun k hk j hj => ?_⟩
    rw [Array.getElem_push] at hj
    split at hj
    · exact hacc k _ j hj
    · have hkn : k = n := by simp at hk; omega
      subst hkn
      unfold pubStep at hj
      rw [← Array.foldl_toList] at hj
      refine pubClosures_step ld acc k hacc _ _ (fun x hx => Array.mem_toList_iff.1 hx)
        (fun j hj => ?_) j hj
      rcases ModSet.has_add hj with hj | rfl
      · rw [ModSet.has_empty] at hj; cases hj
      · exact .refl _

theorem pubClosures_spec (ld : Loads) :
    (pubClosures ld).size = ld.order.size ∧
      ∀ k (hk : k < (pubClosures ld).size), ∀ j, (pubClosures ld)[k].has j = true →
        PubPos ld k j := by
  rw [pubClosures_eq]
  exact pubClosures_range ld ld.order.size

/-- **A set bit of a module's public-import closure is a public-import path**, between positions
in range. -/
theorem pubClosures_sound {ld : Loads}
    (hix : ∀ (m : Name) (k : Nat), ld.index[m]? = some k → ld.order[k]? = some m) {hi j : Nat}
    (h : (((pubClosures ld)[hi]?).map (·.has j)).getD false = true) :
    hi < ld.order.size ∧ j < ld.order.size ∧ PubPos ld hi j := by
  obtain ⟨hs, hspec⟩ := pubClosures_spec ld
  cases hg : (pubClosures ld)[hi]? with
  | none => simp [hg] at h
  | some s =>
    rw [hg] at h
    have hlt : hi < (pubClosures ld).size := by
      rcases Array.getElem?_eq_some_iff.1 hg with ⟨h1, -⟩; exact h1
    have hs' : (pubClosures ld)[hi] = s := by
      rcases Array.getElem?_eq_some_iff.1 hg with ⟨_, h2⟩; exact h2
    have hp := hspec hi hlt j (by rw [hs']; simpa using h)
    refine ⟨hs ▸ hlt, ?_, hp⟩
    -- the end of a path is in range: its last step is an index entry, or it is the start
    have : ∀ a b, PubPos ld a b → a < ld.order.size → b < ld.order.size := by
      intro a b hab
      induction hab with
      | refl => exact id
      | cons _ _ hb _ ih =>
        intro _
        apply ih
        obtain ⟨h1, -⟩ := Array.getElem?_eq_some_iff.1 (hix _ _ hb)
        exact h1
    exact this _ _ hp (hs ▸ hlt)

/-- A public-import path between positions, read as one between the modules there. -/
theorem PubPos.pubReach {sp : Roots} {fs : FS} {ld : Loads}
    (hix : ∀ (m : Name) (k : Nat), ld.index[m]? = some k → ld.order[k]? = some m)
    (himps : ∀ (k : Nat) (m : Name), ld.order[k]? = some m → ∀ is, ld.imports[k]? = some is →
      ModelIO.CanGive (moduleImports sp m) fs (.ok is)) {a b : Nat} (h : PubPos ld a b) :
    ∀ ma, ld.order[a]? = some ma → ∃ mb, ld.order[b]? = some mb ∧ PubReach sp fs ma mb := by
  induction h with
  | refl => exact fun ma h => ⟨ma, h, .refl⟩
  | @cons a b c imp himp he hb _ ih =>
    intro ma ha
    obtain ⟨mc, hc, hr⟩ := ih imp.module (hix _ _ hb)
    cases hia : ld.imports[a]? with
    | none => simp [hia] at himp
    | some is =>
      rw [hia] at himp
      exact ⟨mc, hc, (PubReach.step .refl (himps a ma ha is hia) himp he).trans hr⟩

/-! ## The fixpoint's worklist -/

/-- The module a work item places, if any. -/
@[expose] def LvWork.doneName : LvWork → Option Name
  | .done m _ => some m
  | .imp .. => none

/-- **An import is covered**: its module is placed or being expanded, or a work item for it that
will be followed is pending. -/
@[expose] def LvCovered (ws : List LvWork) (st : LvState) (j : ImportRec) : Prop :=
  (st.flags[j.module]?).isSome = true ∨ st.open_.contains j.module = true ∨
    ∃ pf, LvWork.imp pf j ∈ ws ∧ (j.isExported || pf.importAll) = true

/-- **The fixpoint's invariant**: every module whose imports were read is reached from the root's
imports, with the imports its header read answers; the order lists each placed module once;
each pending `done` item's module is open, unplaced and read, and each open module has one; and
every root import, and every public import of a read module, is covered. -/
structure LvInv (sp : Roots) (fs : FS) (imps0 : Array ImportRec) (ws : List LvWork)
    (st : LvState) : Prop where
  imps : ∀ (m : Name) (is : Array ImportRec), st.imports[m]? = some is →
    ImpReach sp fs imps0 m ∧ ModelIO.CanGive (moduleImports sp m) fs (.ok is)
  nodup : st.order.toList.Nodup
  flags : ∀ m : Name, (st.flags[m]?).isSome = true ↔ m ∈ st.order
  ordImps : ∀ m ∈ st.order, (st.imports[m]?).isSome = true
  done : ∀ (m : Name) (fl : LoadFlags), LvWork.done m fl ∈ ws →
    st.open_.contains m = true ∧ m ∉ st.order ∧ (st.imports[m]?).isSome = true
  doneNodup : (ws.filterMap LvWork.doneName).Nodup
  openDone : ∀ m : Name, st.open_.contains m = true → ∃ fl, LvWork.done m fl ∈ ws
  impR : ∀ pf i, LvWork.imp pf i ∈ ws → ImpReach sp fs imps0 i.module
  demand : ∀ (m : Name) (is : Array ImportRec), st.imports[m]? = some is → ∀ j ∈ is,
    j.isExported = true → LvCovered ws st j
  root : ∀ i ∈ imps0, LvCovered ws st i

theorem LvCovered.step {ws ws' : List LvWork} {st st' : LvState} {j : ImportRec}
    (hf : ∀ m : Name, (st.flags[m]?).isSome = true → (st'.flags[m]?).isSome = true)
    (ho : ∀ m : Name, st.open_.contains m = true →
      (st'.flags[m]?).isSome = true ∨ st'.open_.contains m = true)
    (hw : ∀ pf i, LvWork.imp pf i ∈ ws → (i.isExported || pf.importAll) = true →
      LvWork.imp pf i ∈ ws' ∨ (st'.flags[i.module]?).isSome = true ∨
        st'.open_.contains i.module = true)
    (h : LvCovered ws st j) : LvCovered ws' st' j := by
  rcases h with h | h | ⟨pf, hm, he⟩
  · exact .inl (hf _ h)
  · rcases ho _ h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · rcases hw pf j hm he with h | h | h
    · exact .inr (.inr ⟨pf, h, he⟩)
    · exact .inl h
    · exact .inr (.inl h)

theorem mem_ofImports {fl : LoadFlags} {is : Array ImportRec} {w : LvWork} :
    w ∈ LvWork.ofImports fl is ↔ ∃ j ∈ is, w = .imp fl j := by
  simp [LvWork.ofImports, eq_comm]

theorem filterMap_ofImports (fl : LoadFlags) (is : Array ImportRec) (l : List LvWork) :
    (LvWork.ofImports fl is ++ l).filterMap LvWork.doneName = l.filterMap LvWork.doneName := by
  simp only [LvWork.ofImports, List.filterMap_append, List.filterMap_map]
  have : (LvWork.doneName ∘ LvWork.imp fl) = fun _ => none := by funext x; rfl
  simp [this]

theorem lvInv_done {sp : Roots} {fs : FS} {imps0 : Array ImportRec} {m : Name}
    {fl : LoadFlags} {rest : List LvWork} {st : LvState}
    (hi : LvInv sp fs imps0 (.done m fl :: rest) st) :
    LvInv sp fs imps0 rest
      { flags := st.flags.insert m fl, open_ := st.open_.erase m, order := st.order.push m,
        imports := st.imports } := by
  obtain ⟨hoM, hnM, hiM⟩ := hi.done m fl List.mem_cons_self
  have hdn := hi.doneNodup
  simp only [List.filterMap_cons, LvWork.doneName, List.nodup_cons] at hdn
  have hne : ∀ x fl', LvWork.done x fl' ∈ rest → x ≠ m := by
    rintro x fl' hx rfl
    exact hdn.1 (List.mem_filterMap.2 ⟨_, hx, rfl⟩)
  refine ⟨hi.imps, ?_, fun x => ?_, fun x hx => ?_, fun x fl' hx => ?_, hdn.2, fun x hx => ?_,
    fun pf i hx => hi.impR pf i (List.mem_cons_of_mem _ hx), fun x is hx j hj he => ?_,
    fun i hi' => ?_⟩
  · simp only [Array.toList_push]
    refine List.nodup_append.2 ⟨hi.nodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact hnM (Array.mem_toList_iff.1 ha)
  · simp only [Std.HashMap.getElem?_insert, Array.mem_push]
    by_cases hx : m = x
    · subst hx; simp
    · have : (m == x) = false := by simpa using hx
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      rw [hi.flags x]
      constructor
      · exact .inl
      · rintro (h | h)
        · exact h
        · exact absurd h.symm hx
  · rcases Array.mem_push.1 hx with hx | rfl
    · exact hi.ordImps x hx
    · exact hiM
  · obtain ⟨h1, h2, h3⟩ := hi.done x fl' (List.mem_cons_of_mem _ hx)
    have hxm := hne x fl' hx
    refine ⟨?_, ?_, h3⟩
    · simp [Std.HashSet.contains_erase, h1, Ne.symm hxm]
    · simp only [Array.mem_push, not_or]
      exact ⟨h2, hxm⟩
  · simp only [Std.HashSet.contains_erase, Bool.and_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne] at hx
    obtain ⟨fl', hfl⟩ := hi.openDone x hx.2
    rcases List.mem_cons.1 hfl with h | h
    · cases h; exact absurd rfl hx.1
    · exact ⟨fl', h⟩
  all_goals
    refine LvCovered.step (st := st) (ws := .done m fl :: rest) (fun y hy => ?_) (fun y hy => ?_)
      (fun pf i hx _ => ?_) ?_
    · simp only [Std.HashMap.getElem?_insert]
      split
      · rfl
      · exact hy
    · by_cases hy' : m = y
      · subst hy'; left; simp
      · right; simp [Std.HashSet.contains_erase, hy, hy']
    · rcases List.mem_cons.1 hx with h | h
      · cases h
      · exact .inl h
  · exact hi.demand x is hx j hj he
  · exact hi.root i hi'

theorem lvInv_skip {sp : Roots} {fs : FS} {imps0 : Array ImportRec} {w : LvWork}
    {rest : List LvWork} {st : LvState} (hi : LvInv sp fs imps0 (w :: rest) st)
    (hw : LvWork.doneName w = none)
    (hcov : ∀ pf i, w = .imp pf i → (i.isExported || pf.importAll) = true →
      (st.flags[i.module]?).isSome = true) :
    LvInv sp fs imps0 rest st := by
  have hdn := hi.doneNodup
  rw [List.filterMap_cons, hw] at hdn
  have hcv : ∀ j, LvCovered (w :: rest) st j → LvCovered rest st j := fun j =>
    LvCovered.step (fun _ h => h) (fun _ h => .inr h) fun pf i hx he => by
      rcases List.mem_cons.1 hx with h | h
      · exact .inr (.inl (hcov pf i h.symm he))
      · exact .inl h
  refine ⟨hi.imps, hi.nodup, hi.flags, hi.ordImps,
    fun m fl hx => hi.done m fl (List.mem_cons_of_mem _ hx), hdn, fun m hm => ?_,
    fun pf i hx => hi.impR pf i (List.mem_cons_of_mem _ hx),
    fun m is hm j hj he => hcv _ (hi.demand m is hm j hj he), fun i hi' => hcv _ (hi.root i hi')⟩
  obtain ⟨fl, hfl⟩ := hi.openDone m hm
  rcases List.mem_cons.1 hfl with h | h
  · subst h; simp [LvWork.doneName] at hw
  · exact ⟨fl, h⟩

theorem lvInv_bump {sp : Roots} {fs : FS} {imps0 : Array ImportRec} {pf : LoadFlags}
    {i : ImportRec} {rest : List LvWork} {st : LvState} {old fl' : LoadFlags}
    (hi : LvInv sp fs imps0 (.imp pf i :: rest) st) (hold : st.flags[i.module]? = some old) :
    LvInv sp fs imps0 (LvWork.ofImports fl' ((st.imports[i.module]?).getD #[]) ++ rest)
      { st with flags := st.flags.insert i.module fl' } := by
  have hdn := hi.doneNodup
  simp only [List.filterMap_cons, LvWork.doneName] at hdn
  have hord : i.module ∈ st.order := (hi.flags _).1 (by simp [hold])
  obtain ⟨is, his⟩ := Option.isSome_iff_exists.1 (hi.ordImps _ hord)
  have hfl : ∀ x : Name, ((st.flags.insert i.module fl')[x]?).isSome = (st.flags[x]?).isSome := by
    intro x
    simp only [Std.HashMap.getElem?_insert]
    split
    · next h => have := beq_iff_eq.1 h; subst this; simp [hold]
    · rfl
  refine ⟨hi.imps, hi.nodup, fun x => by rw [hfl]; exact hi.flags x, hi.ordImps,
    fun m fl hx => ?_, by rw [filterMap_ofImports]; exact hdn, fun m hm => ?_,
    fun pf' j hx => ?_, fun m is' hm j hj he => ?_, fun j hj => ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨_, _, h⟩ := mem_ofImports.1 hx; cases h
    · exact hi.done m fl (List.mem_cons_of_mem _ hx)
  · obtain ⟨fl, hfl'⟩ := hi.openDone m hm
    rcases List.mem_cons.1 hfl' with h | h
    · cases h
    · exact ⟨fl, List.mem_append_right _ h⟩
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨j', hj', h⟩ := mem_ofImports.1 hx
      cases h
      rw [his] at hj'
      obtain ⟨hr, hc⟩ := hi.imps _ _ his
      exact .step hr hc hj'
    · exact hi.impR pf' j (List.mem_cons_of_mem _ hx)
  all_goals
    refine LvCovered.step (st := st) (ws := .imp pf i :: rest)
      (fun y hy => by
        show ((st.flags.insert i.module fl')[y]?).isSome = true
        rw [hfl]; exact hy)
      (fun _ h => .inr h) (fun pf' k hx _ => ?_) ?_
    · rcases List.mem_cons.1 hx with h | h
      · cases h; right; left; rw [hfl]; simp [hold]
      · exact .inl (List.mem_append_right _ h)
  · exact hi.demand m is' hm j hj he
  · exact hi.root j hj

theorem lvInv_open {sp : Roots} {fs : FS} {imps0 : Array ImportRec} {pf : LoadFlags}
    {i : ImportRec} {rest : List LvWork} {st : LvState} {fl : LoadFlags} {is : Array ImportRec}
    (hi : LvInv sp fs imps0 (.imp pf i :: rest) st) (hnone : st.flags[i.module]? = none)
    (hnot : st.open_.contains i.module = false)
    (his : ModelIO.CanGive (moduleImports sp i.module) fs (.ok is)) :
    LvInv sp fs imps0 (LvWork.ofImports fl is ++ .done i.module fl :: rest)
      { st with open_ := st.open_.insert i.module, imports := st.imports.insert i.module is } := by
  have hdn := hi.doneNodup
  simp only [List.filterMap_cons, LvWork.doneName] at hdn
  have hR := hi.impR pf i List.mem_cons_self
  have hnord : i.module ∉ st.order := fun h => by
    have := (hi.flags _).2 h; rw [hnone] at this; cases this
  have hrest : ∀ x fl', LvWork.done x fl' ∈ rest → x ≠ i.module := by
    rintro x fl' hx rfl
    have := (hi.done _ fl' (List.mem_cons_of_mem _ hx)).1
    rw [hnot] at this; cases this
  refine ⟨fun x is' hx => ?_, hi.nodup, hi.flags, fun x hx => ?_, fun x fl' hx => ?_, ?_,
    fun x hx => ?_, fun pf' j hx => ?_, fun x is' hx j hj he => ?_, fun j hj => ?_⟩
  · simp only [Std.HashMap.getElem?_insert] at hx
    split at hx
    · next h => have := beq_iff_eq.1 h; subst this; cases hx; exact ⟨hR, his⟩
    · exact hi.imps x is' hx
  · simp only [Std.HashMap.getElem?_insert]; split
    · rfl
    · exact hi.ordImps x hx
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨_, _, h⟩ := mem_ofImports.1 hx; cases h
    rcases List.mem_cons.1 hx with h | hx
    · cases h
      exact ⟨by simp, hnord, by simp⟩
    · obtain ⟨h1, h2, h3⟩ := hi.done x fl' (List.mem_cons_of_mem _ hx)
      refine ⟨by simp [h1], h2, ?_⟩
      simp only [Std.HashMap.getElem?_insert]; split
      · rfl
      · exact h3
  · rw [filterMap_ofImports, List.filterMap_cons]
    simp only [LvWork.doneName, List.nodup_cons]
    refine ⟨fun h => ?_, hdn⟩
    obtain ⟨w, hw, hw'⟩ := List.mem_filterMap.1 h
    cases w with
    | imp => cases hw'
    | done x fl' => cases hw'; exact hrest _ _ hw rfl
  · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with rfl | hx
    · exact ⟨fl, List.mem_append_right _ List.mem_cons_self⟩
    · obtain ⟨fl', hfl'⟩ := hi.openDone x hx
      rcases List.mem_cons.1 hfl' with h | h
      · cases h
      · exact ⟨fl', List.mem_append_right _ (List.mem_cons_of_mem _ h)⟩
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨j', hj', h⟩ := mem_ofImports.1 hx
      cases h
      exact .step hR his hj'
    rcases List.mem_cons.1 hx with h | hx
    · cases h
    · exact hi.impR pf' j (List.mem_cons_of_mem _ hx)
  · simp only [Std.HashMap.getElem?_insert] at hx
    split at hx
    · next h =>
      have := beq_iff_eq.1 h; subst this; cases hx
      exact .inr (.inr ⟨fl, List.mem_append_left _ (mem_ofImports.2 ⟨j, hj, rfl⟩), by simp [he]⟩)
    · refine LvCovered.step (st := st) (ws := LvWork.imp pf i :: rest) (fun _ h => h) (fun _ h => .inr (by simp [h]))
        (fun pf' k hx _ => ?_) (hi.demand x is' hx j hj he)
      rcases List.mem_cons.1 hx with h | h
      · cases h; right; right; simp
      · exact .inl (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  · refine LvCovered.step (st := st) (ws := LvWork.imp pf i :: rest) (fun _ h => h)
      (fun _ h => .inr (by simp [h])) (fun pf' k hx _ => ?_) (hi.root j hj)
    rcases List.mem_cons.1 hx with h | h
    · cases h; right; right; simp
    · exact .inl (List.mem_append_right _ (List.mem_cons_of_mem _ h))

/-- **The worklist keeps the invariant**, to its accepting outcome. -/
theorem levelsGo_inv {sp : Roots} {fs : FS} {imps0 : Array ImportRec} {gPriv : Bool} :
    ∀ (fuel : Nat) (ws : List LvWork) (st : LvState) {hs hs' : HS} {st' : LvState},
      (levelsGo (moduleImports sp) gPriv fuel ws st : ModelIO _) fs hs (.ok (.ok st')) hs' →
      LvInv sp fs imps0 ws st → LvInv sp fs imps0 [] st'
  | _, [], st, _, _, _, h, hi => by
    simp only [levelsGo, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hi
  | 0, _ :: _, _, _, _, _, h, _ => by
    simp [levelsGo] at h
  | fuel + 1, .done m fl :: rest, st, _, _, _, h, hi => by
    simp only [levelsGo] at h
    exact levelsGo_inv fuel _ _ h (lvInv_done hi)
  | fuel + 1, .imp pf i :: rest, st, _, _, _, h, hi => by
    rw [levelsGo] at h
    split at h
    · rename_i hc
      refine levelsGo_inv fuel _ _ h (lvInv_skip hi rfl fun pf' i' he hf => ?_)
      cases he
      simp [hf] at hc
    · dsimp only at h
      cases hold : st.flags[i.module]? with
      | some old =>
        simp only [hold] at h
        split at h
        · exact levelsGo_inv fuel _ _ h (lvInv_skip hi rfl fun pf' i' he _ => by
            cases he; simp [hold])
        · exact levelsGo_inv fuel _ _ h (lvInv_bump hi hold)
      | none =>
        simp only [hold] at h
        split at h
        · simp at h
        · rename_i hnot
          simp only [ModelIO.bind_ok] at h
          obtain ⟨r, _, hr, h⟩ := h
          rcases r with e | is
          · simp at h
          · exact levelsGo_inv fuel _ _ h
              (lvInv_open hi hold (by simpa using hnot) ⟨_, _, hr⟩)

theorem lvInv_init {sp : Roots} {fs : FS} (isM : Bool) (imps0 : Array ImportRec) :
    LvInv sp fs imps0 (LvWork.ofImports { importAll := true, isExported := isM } imps0) {} := by
  refine ⟨fun m is h => by simp at h, by simp, fun m => by simp, fun m h => by simp at h,
    fun m fl h => ?_, ?_, fun m h => by simp at h, fun pf i h => ?_, fun m is h => by simp at h,
    fun i hi => .inr (.inr ⟨_, mem_ofImports.2 ⟨i, hi, rfl⟩, by simp⟩)⟩
  · obtain ⟨_, _, h⟩ := mem_ofImports.1 h; cases h
  · have := filterMap_ofImports { importAll := true, isExported := isM } imps0 []
    simp only [List.append_nil] at this
    rw [this]; simp
  · obtain ⟨j, hj, h⟩ := mem_ofImports.1 h; cases h; exact .root hj

/-- The index a fold over a list without duplicates builds: each name's position. -/
theorem indexFold_get? :
    ∀ (l : List Name) (M : Std.HashMap Name Nat) (k0 : Nat), l.Nodup → ∀ x,
      (l.foldl (fun (acc : Std.HashMap Name Nat × Nat) m => (acc.1.insert m acc.2, acc.2 + 1))
        (M, k0)).1[x]? = if x ∈ l then some (k0 + l.idxOf x) else M[x]?
  | [], M, k0, _, x => by simp
  | a :: l, M, k0, hnd, x => by
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons, indexFold_get? l _ _ hnd.2 x]
    by_cases hx : x = a
    · subst hx
      simp [hnd.1]
    · have hax : (a == x) = false := by simpa using Ne.symm hx
      simp only [List.mem_cons, hx, false_or, List.idxOf_cons, hax, Bool.false_eq_true,
        ↓reduceIte, Std.HashMap.getElem?_insert]
      split <;> simp; omega

/-- **What the header fixpoint loads, on a snapshot** (`headerFixpoint` over the search path's
header reads): its flags and imports by position; its order without duplicates, the index naming
each module's position; every loaded module reached from the root's imports by import edges,
with the imports its header read answers. -/
theorem headerFixpoint_sound {sp : Roots} {fs : FS} {isM : Bool} {imps0 : Array ImportRec}
    {ld : Loads} (h : ModelIO.CanGive (headerFixpoint (moduleImports sp) isM imps0) fs (.ok ld)) :
    ld.flags.size = ld.order.size ∧ ld.imports.size = ld.order.size ∧ ld.order.toList.Nodup ∧
      (∀ (k : Nat) (m : Name), ld.order[k]? = some m →
        ImpReach sp fs imps0 m ∧ ld.index[m]? = some k ∧
        ∀ is, ld.imports[k]? = some is → ModelIO.CanGive (moduleImports sp m) fs (.ok is)) ∧
      (∀ (m : Name) (k : Nat), ld.index[m]? = some k → ld.order[k]? = some m) := by
  obtain ⟨_, _, h⟩ := h
  simp only [headerFixpoint, ModelIO.bind_ok] at h
  obtain ⟨r, _, hr, h⟩ := h
  rcases r with e | st
  · simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hi := levelsGo_inv _ _ _ hr (lvInv_init isM imps0)
  have hix := indexFold_get? st.order.toList {} 0 hi.nodup
  simp only [Array.foldl_toList] at hix
  refine ⟨by simp, by simp, hi.nodup, fun k m hk => ?_, fun m k hk => ?_⟩
  · have hm : m ∈ st.order := Array.mem_of_getElem? hk
    obtain ⟨is, his⟩ := Option.isSome_iff_exists.1 (hi.ordImps m hm)
    refine ⟨(hi.imps m is his).1, ?_, fun is' h' => ?_⟩
    · rw [hix m]; simp only [Array.mem_toList_iff, hm, ↓reduceIte]
      have hk' : st.order.toList[k]? = some m := by simpa using hk
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hk'
      rw [← hget, List.Nodup.idxOf_getElem hi.nodup k hlt]
      simp
    · simp only [Array.getElem?_map, hk, Option.map_some, his, Option.getD_some,
        Option.some.injEq] at h'
      subst h'
      exact (hi.imps m is his).2
  · rw [hix m] at hk
    split at hk
    · rename_i hm
      simp only [Nat.zero_add, Option.some.injEq] at hk
      subst hk
      have hlt := List.idxOf_lt_length_of_mem hm
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
    · simp at hk

/-- **The header fixpoint loads every module a path of public imports leads to from one of the
root's imports**: the root is loaded whole, so each of its imports is followed, and a public import
is followed from every loaded module. -/
theorem headerFixpoint_complete {sp : Roots} {fs : FS} {isM : Bool}
    {imps0 : Array ImportRec} {ld : Loads}
    (h : ModelIO.CanGive (headerFixpoint (moduleImports sp) isM imps0) fs (.ok ld))
    {i : ImportRec} (hi0 : i ∈ imps0) {m : Name} (hm : PubReach sp fs i.module m) :
    m ∈ ld.order := by
  obtain ⟨_, _, h⟩ := h
  simp only [headerFixpoint, ModelIO.bind_ok] at h
  obtain ⟨r, _, hr, h⟩ := h
  rcases r with e | st
  · simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hi := levelsGo_inv _ _ _ hr (lvInv_init isM imps0)
  have hcov : ∀ j, LvCovered [] st j → j.module ∈ st.order := by
    rintro j (h | h | ⟨_, h, _⟩)
    · exact (hi.flags _).1 h
    · obtain ⟨_, h'⟩ := hi.openDone _ h; cases h'
    · cases h
  show m ∈ st.order
  induction hm with
  | refl => exact hcov _ (hi.root i hi0)
  | @step b is j _ hc hj he ih =>
    obtain ⟨is', his⟩ := Option.isSome_iff_exists.1 (hi.ordImps b ih)
    have := moduleImports_canGive_unique hc (hi.imps b is' his).2
    subst this
    exact hcov _ (hi.demand b is his j hj he)

/-- **The worklist is determined on a snapshot**: two accepting outcomes agree. -/
theorem levelsGo_unique {sp : Roots} {fs : FS} {gPriv : Bool} :
    ∀ (fuel : Nat) (ws : List LvWork) (st : LvState) {hs₁ hs₁' hs₂ hs₂' : HS} {a b : LvState},
      (levelsGo (moduleImports sp) gPriv fuel ws st : ModelIO _) fs hs₁ (.ok (.ok a)) hs₁' →
      (levelsGo (moduleImports sp) gPriv fuel ws st : ModelIO _) fs hs₂ (.ok (.ok b)) hs₂' →
      a = b
  | _, [], st, _, _, _, _, _, _, h₁, h₂ => by
    simp only [levelsGo, ModelIO.pure_iff, Except.ok.injEq] at h₁ h₂
    rw [h₁.1, h₂.1]
  | 0, _ :: _, _, _, _, _, _, _, _, h₁, _ => by simp [levelsGo] at h₁
  | fuel + 1, .done m fl :: rest, st, _, _, _, _, _, _, h₁, h₂ => by
    simp only [levelsGo] at h₁ h₂
    exact levelsGo_unique fuel _ _ h₁ h₂
  | fuel + 1, .imp pf i :: rest, st, _, _, _, _, _, _, h₁, h₂ => by
    rw [levelsGo] at h₁ h₂
    split at h₁
    · rename_i hc
      simp only [hc, ↓reduceIte] at h₂
      exact levelsGo_unique fuel _ _ h₁ h₂
    · rename_i hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h₂
      dsimp only at h₁ h₂
      cases hold : st.flags[i.module]? with
      | some old =>
        simp only [hold] at h₁ h₂
        split at h₁
        · rename_i hf
          simp only [hf, ↓reduceIte] at h₂
          exact levelsGo_unique fuel _ _ h₁ h₂
        · rename_i hf
          simp only [hf, Bool.false_eq_true, ↓reduceIte] at h₂
          exact levelsGo_unique fuel _ _ h₁ h₂
      | none =>
        simp only [hold] at h₁ h₂
        split at h₁
        · simp at h₁
        · rename_i ho
          simp only [ho, Bool.false_eq_true, ↓reduceIte] at h₂
          simp only [ModelIO.bind_ok] at h₁ h₂
          obtain ⟨r₁, _, hr₁, h₁⟩ := h₁
          obtain ⟨r₂, _, hr₂, h₂⟩ := h₂
          rcases r₁ with e | is₁
          · simp at h₁
          rcases r₂ with e | is₂
          · simp at h₂
          obtain rfl := moduleImports_unique hr₁ hr₂
          exact levelsGo_unique fuel _ _ h₁ h₂

/-! ## Through a lookup and its trimmed copy (task #608) -/

/-- **The worklist through a trimmed lookup, accepted, is the full lookup's**, from the same
handles: every header it read, the full lookup reads alike. -/
theorem levelsGo_trims {a L : Roots} (ha : a.Trims L) {fs : FS} {gPriv : Bool} :
    ∀ (fuel : Nat) (ws : List LvWork) (st : LvState) {hs hs' : HS} {r : LvState},
      (levelsGo (moduleImports a) gPriv fuel ws st : ModelIO _) fs hs (.ok (.ok r)) hs' →
      (levelsGo (moduleImports L) gPriv fuel ws st : ModelIO _) fs hs (.ok (.ok r)) hs'
  | _, [], st, _, _, _, h => by
    simpa only [levelsGo] using h
  | 0, _ :: _, _, _, _, _, h => by simp [levelsGo] at h
  | fuel + 1, .done m fl :: rest, st, _, _, _, h => by
    simp only [levelsGo] at h ⊢
    exact levelsGo_trims ha fuel _ _ h
  | fuel + 1, .imp pf i :: rest, st, _, _, _, h => by
    rw [levelsGo] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      exact levelsGo_trims ha fuel _ _ h
    · rename_i hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      dsimp only at h ⊢
      cases hold : st.flags[i.module]? with
      | some old =>
        simp only [hold] at h ⊢
        split at h
        · rename_i hf
          simp only [hf, ↓reduceIte]
          exact levelsGo_trims ha fuel _ _ h
        · rename_i hf
          simp only [hf, Bool.false_eq_true, ↓reduceIte]
          exact levelsGo_trims ha fuel _ _ h
      | none =>
        simp only [hold] at h ⊢
        split at h
        · simp at h
        · rename_i ho
          simp only [ho, Bool.false_eq_true, ↓reduceIte]
          simp only [ModelIO.bind_ok] at h ⊢
          obtain ⟨r₁, hs₁, hr₁, h⟩ := h
          rcases r₁ with e | is₁
          · simp at h
          exact ⟨_, hs₁, atModule_trims (k := fun loc => readImportsAt loc i.module) ha hr₁,
            levelsGo_trims ha fuel _ _ h⟩

/-- **The header fixpoint through a trimmed lookup, accepted, is the full lookup's.** -/
theorem headerFixpoint_trims {a L : Roots} (ha : a.Trims L) {fs : FS} {isM : Bool}
    {imps0 : Array ImportRec} {ld : Loads}
    (h : ModelIO.CanGive (headerFixpoint (moduleImports a) isM imps0) fs (.ok ld)) :
    ModelIO.CanGive (headerFixpoint (moduleImports L) isM imps0) fs (.ok ld) := by
  obtain ⟨hs, hs', h⟩ := h
  refine ⟨hs, hs', ?_⟩
  simp only [headerFixpoint, ModelIO.bind_ok] at h ⊢
  obtain ⟨r₁, hs₁, hr₁, h⟩ := h
  rcases r₁ with e | st
  · simp at h
  exact ⟨_, hs₁, levelsGo_trims ha _ _ _ hr₁, h⟩

theorem ImpReach.trims {a L : Roots} (ha : a.Trims L) {fs : FS} {imps0 : Array ImportRec}
    {m : Name} (h : ImpReach a fs imps0 m) : ImpReach L fs imps0 m := by
  induction h with
  | root hi => exact .root hi
  | step _ hc hi ih => exact .step ih (moduleImports_trims ha hc) hi

theorem PubReach.trims {a L : Roots} (ha : a.Trims L) {fs : FS} {x m : Name}
    (h : PubReach a fs x m) : PubReach L fs x m := by
  induction h with
  | refl => exact .refl
  | step _ hc hi he ih => exact .step ih (moduleImports_trims ha hc) hi he

/-- **The header fixpoint is determined on a snapshot.** -/
theorem headerFixpoint_unique {sp : Roots} {fs : FS} {isM : Bool} {imps0 : Array ImportRec}
    {a b : Loads} (ha : ModelIO.CanGive (headerFixpoint (moduleImports sp) isM imps0) fs (.ok a))
    (hb : ModelIO.CanGive (headerFixpoint (moduleImports sp) isM imps0) fs (.ok b)) : a = b := by
  obtain ⟨_, _, ha⟩ := ha
  obtain ⟨_, _, hb⟩ := hb
  simp only [headerFixpoint, ModelIO.bind_ok] at ha hb
  obtain ⟨r₁, _, hr₁, ha⟩ := ha
  obtain ⟨r₂, _, hr₂, hb⟩ := hb
  rcases r₁ with e | st₁
  · simp at ha
  rcases r₂ with e | st₂
  · simp at hb
  obtain rfl := levelsGo_unique _ _ _ hr₁ hr₂
  simp only [ModelIO.pure_iff, Except.ok.injEq] at ha hb
  rw [ha.1, hb.1]

/-- **A module of a loaded module's public-import closure** (`pubClosures`, as `captureOne`
reads it) **is reached from it by a path of public imports**, both modules loaded. -/
theorem pubClosures_pubReach {sp : Roots} {fs : FS} {isM : Bool} {imps0 : Array ImportRec}
    {ld : Loads} (h : ModelIO.CanGive (headerFixpoint (moduleImports sp) isM imps0) fs (.ok ld))
    {hi j : Nat} (hp : (((pubClosures ld)[hi]?).map (·.has j)).getD false = true) :
    ∃ a b, ld.order[hi]? = some a ∧ ld.order[j]? = some b ∧ PubReach sp fs a b := by
  obtain ⟨-, -, -, hord, hix⟩ := headerFixpoint_sound h
  obtain ⟨hlt, -, hpp⟩ := pubClosures_sound hix hp
  obtain ⟨b, hb, hr⟩ := hpp.pubReach hix (fun k m hk is hi => (hord k m hk).2.2 is hi)
    ld.order[hi] (by simp [hlt])
  exact ⟨_, b, by simp [hlt], hb, hr⟩

/-! ## The root's imports -/

theorem importsMapM_congr {nm nm' : UInt64 → Option Name} :
    ∀ (l : List (ImportF UInt64)), (∀ i ∈ l, nm i.module = nm' i.module) →
      l.mapM (ImportF.mapM nm) = l.mapM (ImportF.mapM nm')
  | [], _ => rfl
  | i :: l, h => by
    simp only [List.mapM_cons, ImportF.mapM, h i List.mem_cons_self,
      importsMapM_congr l (fun j hj => h j (List.mem_cons_of_mem _ hj))]

/-- **The load of a module's private view holds its header's imports**: the imports its
skeleton names are those the start of its `M.olean` holds. -/
theorem loadAt_imports {i : Nat} {m : Name} {f : ModFiles} {l : Loaded}
    (h : loadAt i m f = some l) :
    ∃ r a sk imports, f.viewRegion .private = some (r, a) ∧ moduleSkel r a = some sk ∧
      sk.imports.mapM (ImportF.mapM (nameP r)) = some imports ∧
      importsPre f.exported.bytes = some imports.toArray := by
  unfold loadAt at h
  obtain ⟨⟨r, a⟩, hv, h⟩ := bind_some_left h
  simp only at h
  split at h
  rotate_left
  · cases h
  obtain ⟨sk, hsk, h⟩ := bind_some_left h
  obtain ⟨skels, -, h⟩ := bind_some_left h
  obtain ⟨outs, -, h⟩ := bind_some_left h
  obtain ⟨⟨nm, ms, st⟩, hrun, h⟩ := bind_some_left h
  simp only at h
  obtain ⟨imports, himp, h⟩ := bind_some_left h
  split at h
  rotate_left
  · cases h
  rename_i hpre
  have hs := runMarked_spec r (sk.imports.map (·.module) ++ skels.flatMap CEntryF.names ++
    usesNames outs) (skels.flatMap lazyRoots)
  rw [hrun] at hs
  obtain ⟨h1, -, -⟩ := hs
  refine ⟨r, a, sk, imports, hv, hsk, ?_, eq_of_beq hpre⟩
  rw [← himp]
  exact (importsMapM_congr _ fun i hi => h1 _ (by
    simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inl ⟨i, hi, rfl⟩))).symm

/-- **A module's private part's name table holds the imports its header read answers**, where
the module's private view loads (a worker's home read): the worker's root imports are the
graph's edges. -/
theorem readPartNames_header {sp : Roots} {fs : FS} {m : Name} {f : ModFiles} {i : Nat}
    {l : Loaded} {t : NamePositions}
    (hf : ModelIO.CanGive (readFiles sp m .private) fs (.ok f)) (hl : loadAt i m f = some l)
    (ht : ModelIO.CanGive (readPartNames sp (m, .private)) fs (.ok t)) :
    ModelIO.CanGive (moduleImports sp m) fs (.ok t.header.imports) := by
  -- the table is the one of the files' private view
  obtain ⟨hs₀, _, ht⟩ := ht
  simp only [readPartNames, ModelIO.bind_ok] at ht
  obtain ⟨y, hs₁, hy, ht⟩ := ht
  rcases y with e | loc
  · simp at ht
  simp only [readPartNamesAt, namesOf, ModelIO.bind_ok] at ht
  obtain ⟨z, hs₂, hz, ht⟩ := ht
  rcases z with e | f'
  · simp at ht
  have hf' : ModelIO.CanGive (readFiles sp m .private) fs (.ok f') := by
    refine ⟨hs₀, hs₂, ?_⟩
    simp only [readFiles, ModelIO.bind_ok]
    exact ⟨.ok loc, hs₁, hy, hz⟩
  obtain rfl := readFiles_unique hf' hf
  simp only at ht
  cases hr : readNamePositions f' .private with
  | none => simp [hr] at ht
  | some ps =>
  simp only [hr, ModelIO.pure_iff, Except.ok.injEq] at ht
  obtain ⟨rfl, -⟩ := ht
  obtain ⟨r, a, sk, imports, hv, hsk, himp, hpre⟩ := loadAt_imports hl
  have hhead : t.header.imports = imports.toArray := by
    simp only [readNamePositions, hv, bind, Option.bind] at hr
    unfold namePositionsAt at hr
    rw [hsk] at hr
    simp only [Option.bind_eq_bind, Option.bind_some, himp] at hr
    obtain ⟨cs, -, hr⟩ := bind_some_left hr
    split at hr
    · simp only [pure, Option.some.injEq] at hr
      rw [← hr]
    · cases hr
  rw [hhead]
  -- the header read at the module's location
  obtain ⟨_, _, hf2⟩ := hf
  obtain ⟨loc', b, ex, hloc, hb, hp, hex, -⟩ := readFiles_ok hf2
  rw [hex, Part.ofBytes_bytes hp] at hpre
  have hg : ModelIO.Gives (moduleImports sp m) fs (.ok imports.toArray) := by
    simp only [moduleImports]
    exact hloc.bind (readImportsAt_det hb hp hpre)
  exact hg.canGive

end ConLeche.Driver
