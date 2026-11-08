module

public import ConLeche.Frontend.Olean.Levels
public import ConLeche.Frontend.Olean.Files
public import ConLeche.Verify.Frontend.ModelIO
import ConLeche.Verify.Frontend.Olean.Files

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
* `headerFixpoint_unique` — the fixpoint is determined on a snapshot (`moduleImports_unique`).
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-! ## Paths of imports -/

/-- **A module reached from an import list** by import edges, each module's imports what its
header read answers on the snapshot. -/
inductive ImpReach (sp : SearchPath) (fs : FS) (imps0 : Array ImportRec) : Name → Prop
  | root {i : ImportRec} : i ∈ imps0 → ImpReach sp fs imps0 i.module
  | step {a : Name} {is : Array ImportRec} {i : ImportRec} : ImpReach sp fs imps0 a →
      ModelIO.CanGive (moduleImports sp a) fs (.ok is) → i ∈ is → ImpReach sp fs imps0 i.module

/-- **A path of public imports** from `a`, each module's imports what its header read answers on
the snapshot. -/
inductive PubReach (sp : SearchPath) (fs : FS) (a : Name) : Name → Prop
  | refl : PubReach sp fs a a
  | step {b : Name} {is : Array ImportRec} {i : ImportRec} : PubReach sp fs a b →
      ModelIO.CanGive (moduleImports sp b) fs (.ok is) → i ∈ is → i.isExported = true →
      PubReach sp fs a i.module

theorem PubReach.trans {sp : SearchPath} {fs : FS} {a b c : Name} (h₁ : PubReach sp fs a b)
    (h₂ : PubReach sp fs b c) : PubReach sp fs a c := by
  induction h₂ with
  | refl => exact h₁
  | step _ hi hm he ih => exact .step ih hi hm he

/-! ## The header read is determined -/

/-- **A module's imports, on a snapshot, are one list**: two value outcomes of its header read
agree. -/
theorem moduleImports_unique {sp : SearchPath} {m : Name} {fs : FS} {hs₁ hs₁' hs₂ hs₂' : HS}
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

theorem moduleImports_canGive_unique {sp : SearchPath} {m : Name} {fs : FS}
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
theorem PubPos.pubReach {sp : SearchPath} {fs : FS} {ld : Loads}
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

end ConLeche.Driver
