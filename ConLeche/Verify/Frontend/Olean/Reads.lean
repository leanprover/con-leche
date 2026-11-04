module

public import ConLeche.Frontend.Olean.Module
public import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Sparse
import Std.Data.HashSet.Lemmas

/-!
# Every read of a part of a file is a projection of its full parse

The full parse is `parseFull` (`ConLeche/Frontend/Olean/Reads.lean`), the
specification decoder behind the name table's check (`parseFull_eq`, from
the fast decoder's `decodeModuleFast_eq`).  **Where it succeeds, every other
read succeeds, and returns its part of the result**:

* `readHeader_of_full`, `readLight_of_full`: the header, and per stored
  constant its location, name, kind and filter;
* `readEntry_eq`, an equation on every region: the constant at a location is
  `constSpec`'s, so `readEntry_of_full` is the full parse's entry;
* `readStmts_of_full`: the statements of any of the module's constants;
* `full_names_nodup`: the names of its constants are distinct, the check
  `readLight` repeats.

The prefix read of a file's imports is related to the whole file in both
directions: `importsPre_extract` (a prefix's imports are the file's), and
`importsPre_prefix` (a file's imports are those of every prefix the walk
stops in).  `parseExported_full` and `parseModule_full` unfold the module
reads into the full parses they are made of, so the theorems here apply at
the regions and roots of a module's parts.

The file-system level is `ConLeche/Verify/Frontend/Olean/Files.lean`.
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

instance : LawfulBEq (ImportF Name) where
  rfl {a} := by
    show (a.module == a.module && a.importAll == a.importAll && a.isExported == a.isExported &&
      a.isMeta == a.isMeta) = true
    simp
  eq_of_beq {a b} h := by
    have h' : (a.module == b.module && a.importAll == b.importAll &&
      a.isExported == b.isExported && a.isMeta == b.isMeta) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
    cases a; cases b; simp_all

/-! ## The name table's check -/

/-- A loop in `Id` over consecutive numbers: what holds at the start and is
kept by every step that continues holds at the end, unless a step stops
it. -/
theorem forIn'_range'_id {β : Type} (I : Nat → β → Prop) :
    ∀ (l : List Nat) (s : Nat), l = List.range' s l.length →
      ∀ (f : (a : Nat) → a ∈ l → β → Id (ForInStep β)) (x : β), I s x →
      (∀ a hm y y', I a y → f a hm y = ForInStep.yield y' → I (a + 1) y') →
      I (s + l.length) (forIn' l x f).run ∨
        ∃ a hm y, I a y ∧ f a hm y = ForInStep.done (forIn' l x f).run
  | [], s, _, f, x, hx, _ => by simp only [List.forIn'_nil, List.length_nil, Nat.add_zero]; exact .inl hx
  | a :: l, s, hl, f, x, hx, hf => by
    simp only [List.length_cons, List.range'_succ, List.cons.injEq] at hl
    obtain ⟨rfl, hl⟩ := hl
    rw [List.forIn'_cons]
    cases hfa : f a List.mem_cons_self x with
    | done y => exact .inr ⟨a, _, x, hx, by rw [hfa]; rfl⟩
    | yield y =>
      have := forIn'_range'_id I l (a + 1) hl (fun b m y => f b (List.mem_cons_of_mem _ m) y) y
        (hf a _ x y hx hfa) (fun b hm y y' hy => hf b _ y y' hy)
      simp only [List.length_cons]
      rw [show a + (l.length + 1) = a + 1 + l.length by omega]
      rcases this with h | ⟨b, hm, z, hz, hb⟩
      · exact .inl h
      · exact .inr ⟨b, _, z, hz, hb⟩

/-- No file holds an object at the address `1` (the boxed `Name.anonymous`):
an object lies past a file's header. -/
theorem locGo_one (r : Region) : ∀ n, r.locGo 1 n = 0
  | 0 => rfl
  | i + 1 => by
    unfold Region.locGo
    split
    · rename_i hi
      dsimp only
      split
      · rename_i hb
        have hb' := Bool.and_eq_true _ _ ▸ hb
        obtain ⟨h1, -⟩ := hb'
        have : ((1 : UInt64) - r.segs[i].base).toNat ≤ 1 := by
          have h1' : r.segs[i].base ≤ 1 := by simpa using h1
          rw [UInt64.toNat_sub_of_le _ _ h1']
          simp
        have hd : ¬ dataStart ≤ ((1 : UInt64) - r.segs[i].base).toNat := by
          unfold dataStart; omega
        simp [hd]
      · exact locGo_one r i
    · rfl

theorem loc_one (r : Region) : r.loc 1 = none := by
  simp [Region.loc, locGo_one]

/-- `constNamesOk`'s loop: where it does not stop with `false`, its
invariant holds at the end. -/
theorem cn_loop {β : Type} {l : List Nat}
    {f : (a : Nat) → a ∈ l → Option Bool × β → Id (ForInStep (Option Bool × β))}
    {x : Option Bool × β} (I : Nat → Option Bool × β → Prop) (hl : l = List.range' 0 l.length) (hx : I 0 x)
    (hf : ∀ a hm y y', I a y → f a hm y = ForInStep.yield y' → I (a + 1) y')
    (hd : ∀ a hm y y', I a y → f a hm y = ForInStep.done y' → y'.1 = some false)
    {o : Option Bool} (hres : (forIn' l x f : Id _).1 = o) (h : o ≠ some false) :
    I l.length (forIn' l x f : Id _) := by
  subst hres
  rcases forIn'_range'_id I l 0 hl f x hx hf with k | ⟨a, hm, y, hy, hda⟩
  · simpa [Id.run] using k
  · exact absurd (hd a hm y _ hy hda) h

/-- The invariant of `constNamesOk`'s loop at index `a`. -/
def CNInv (r : Region) (cs : Array Nat) (a : Nat) (s : Option Bool × Std.HashSet Name) : Prop :=
  s.1 = none ∧ ∃ names : List Name, names.length = a ∧ names.Nodup ∧
    (∀ x, s.2.contains x = true ↔ x ∈ names) ∧
    ∀ k, k < a → ∃ sk, (cs[k]?).bind (constSkel r) = some sk ∧ nameP r sk.name = names[k]?

/-- A pointer at a location stands for the name stored there. -/
theorem nameP_of_loc {r : Region} {v : UInt64} {c : Nat} (h : r.loc v = some c) :
    nameP r v = nameAt r c := by
  unfold nameP
  have : (v == 1) = false := by
    cases hv : (v == 1)
    · rfl
    · have := beq_iff_eq.1 hv; subst this; rw [loc_one] at h; cases h
  rw [this, h]; rfl

/-- `constNamesOk`'s step that continues keeps its invariant. -/
theorem cn_yield {r : Region} {cs : Array Nat} {a : Nat} {y : Option Bool × Std.HashSet Name}
    {sk : CEntryF UInt64 UInt64} {a1 : Name} (hy : CNInv r cs a y)
    (hsk : (cs[a]?).bind (constSkel r) = some sk) (hn : nameP r sk.name = some a1)
    (hc : ¬ y.2.contains a1 = true) : CNInv r cs (a + 1) (none, y.2.insert a1) := by
  obtain ⟨-, names, hl, hnd, hcon, hk⟩ := hy
  refine ⟨rfl, names ++ [a1], by simp [hl], ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro x hx z hz
    simp only [List.mem_singleton] at hz; subst hz
    intro he; subst he
    exact hc ((hcon _).2 hx)
  · intro x
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_append,
      List.mem_singleton, hcon]
    constructor
    · rintro (h | h)
      · exact .inr h.symm
      · exact .inl h
    · rintro (h | h)
      · exact .inr h
      · exact .inl h.symm
  · intro k hk'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
    · obtain ⟨sk', h1, h2⟩ := hk k hk'
      refine ⟨sk', h1, ?_⟩
      rw [h2, List.getElem?_append_left (by omega)]
    · refine ⟨sk, hsk, ?_⟩
      rw [hn, List.getElem?_append_right (by omega), hl]
      simp

/-- **A name table that agrees names its constants, each once**
(`constNamesOk`). -/
theorem constNamesOk_spec {r : Region} {root : UInt64} (h : constNamesOk r root = true) :
    ∃ g cs, r.loc root = some g ∧ r.objArray g (r.fld g 2) = some cs ∧
      ∃ names : List Name, names.length = cs.size ∧ names.Nodup ∧
        ∀ k, k < cs.size → ∃ sk, (cs[k]?).bind (constSkel r) = some sk ∧
          nameP r sk.name = names[k]? := by
  unfold constNamesOk at h
  simp only [Id.run, bind, pure] at h
  split at h
  case h_2 => cases h
  rename_i g hg
  split at h
  case isFalse => cases h
  split at h
  case h_2 => cases h
  rename_i ns hns
  split at h
  case h_2 => cases h
  rename_i cs hcs
  split at h
  case isFalse => cases h
  rename_i hsz
  have hsz' : ns.size = cs.size := by simpa using hsz
  refine ⟨g, cs, hg, hcs, ?_⟩
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at h
  have h0 : CNInv r cs 0 (none, Std.HashSet.emptyWithCapacity ns.size) :=
    ⟨rfl, [], rfl, List.nodup_nil, fun x => by simp [Std.HashSet.contains_emptyWithCapacity],
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  split at h
  all_goals rename_i heq
  all_goals
    have key := cn_loop (CNInv r cs) (by simp [Std.Legacy.Range.size]) h0 ?_ ?_ heq
      (by first | (intro he; cases he; simp at h) | simp)
  all_goals first
    | (obtain ⟨-, names, hl, hnd, -, hk⟩ := key
       simp only [Std.Legacy.Range.size, List.length_range', Nat.sub_zero,
         Nat.add_sub_cancel, Nat.div_one] at hl hk
       exact ⟨names, by omega, hnd, fun k hk' => hk k (by omega)⟩)
    | (intro a hm y y' hy hf
       try dsimp only at hf
       repeat' split at hf
       all_goals first
         | (cases hf; done)
         | (cases hf; rfl)
         | (cases hf
            refine cn_yield hy ‹_› ?_ ‹_›
            first
              | (rw [nameP_of_loc (by simpa using ‹(r.loc _ == some _) = true›)]; assumption)
              | (rw [‹nameP r _ = some _›]; congr 1; exact (beq_iff_eq.1 ‹(_ == _) = true›).symm)))

/-- The module skeleton's constants are the root's constants array. -/
theorem moduleSkel_consts {r : Region} {root : UInt64} {sk : ModSkel} {g : Nat} {cs : Array Nat}
    (hs : moduleSkel r root = some sk) (hg : r.loc root = some g)
    (hcs : r.objArray g (r.fld g 2) = some cs) : sk.consts = cs.toList := by
  unfold moduleSkel at hs
  rw [hg] at hs
  simp only [bind, Option.bind_some] at hs
  split at hs
  · simp only [Option.bind_eq_some_iff, hcs, Option.some.injEq, pure] at hs
    obtain ⟨_, _, _, _, _, _, _, rfl, rfl⟩ := hs
    rfl
  · simp at hs

/-- An `Option`-valued `mapM` that succeeds keeps the length. -/
theorem mapM_length_opt {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : xs.mapM f with
      | none => simp [hx, hr] at h
      | some ys' =>
        have h' : y :: ys' = ys := by simpa [hx, hr] using h
        subst h'
        simp [mapM_length_opt hr]

/-! ## `mapM` in `Option` -/

theorem mapM_getElem? {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ i : Nat, ys[i]? = xs[i]?.bind f
  | [], ys, h, i => by simp at h; subst h; simp
  | x :: xs, ys, h, i => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_some_left h
    obtain ⟨ys', hys, h⟩ := bind_some_left h
    cases h
    cases i with
    | zero => simp [hy]
    | succ i => simpa using mapM_getElem? hys i

theorem mapM_mem {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, f x = some y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := mapM_getElem? h i
  rw [List.getElem?_eq_getElem hi, Option.bind_some] at this
  cases hf : f xs[i] with
  | none => rw [hf] at this; have := mapM_length_opt h; have := (List.getElem?_eq_none_iff.1 ‹_›); omega
  | some y => exact ⟨y, List.mem_of_getElem? (by rw [‹ys[i]? = _›, hf]), rfl⟩

/-- A `mapM` of a function defined on every element. -/
theorem mapM_of_forall {α β : Type} {f : α → Option β} {P : β → Prop} :
    ∀ {xs : List α}, (∀ x ∈ xs, ∃ y, f x = some y ∧ P y) →
      ∃ ys, xs.mapM f = some ys ∧ ∀ y ∈ ys, P y
  | [], _ => ⟨[], rfl, by simp⟩
  | x :: xs, h => by
    obtain ⟨y, hy, hP⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys, hPs⟩ := mapM_of_forall (xs := xs) fun z hz => h z (List.mem_cons_of_mem _ hz)
    refine ⟨y :: ys, by simp [List.mapM_cons, hy, hys], ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨hP, hPs⟩

/-- A function that reads part of what `f` reads succeeds where `f` does. -/
theorem mapM_project {α β γ : Type} {f : α → Option β} {g : α → Option γ} {k : β → γ}
    (hg : ∀ x y, f x = some y → g x = some (k y)) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.mapM g = some (ys.map k)
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_some_left h
    obtain ⟨ys', hys, h⟩ := bind_some_left h
    cases h
    simp [List.mapM_cons, hg x y hy, mapM_project hg hys]

/-- The same, the result depending on the element too. -/
theorem mapM_project_zip {α β γ : Type} {f : α → Option β} {g : α → Option γ} {k : α → β → γ}
    (hg : ∀ x y, f x = some y → g x = some (k x y)) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      xs.mapM g = some ((xs.zip ys).map fun p => k p.1 p.2)
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_some_left h
    obtain ⟨ys', hys, h⟩ := bind_some_left h
    cases h
    simp [List.mapM_cons, hg x y hy, mapM_project_zip hg hys]

/-! ## The full parse -/

/-- **The full parse is the specification** behind the name table's check,
so it succeeds exactly where they both do. -/
theorem parseFull_eq (r : Region) (root : UInt64) :
    parseFull r root = if constNamesOk r root then decodeModuleSpec r root else none := by
  unfold parseFull
  rw [decodeModuleFast_eq]
  cases constNamesOk r root <;> simp

theorem decodeModuleSpec_some {r : Region} {root : UInt64} {d : ModDecoded}
    (h : decodeModuleSpec r root = some d) :
    ∃ sk, moduleSkel r root = some sk ∧
      sk.imports.mapM (ImportF.mapM (nameP r)) = some d.imports.toList ∧
      sk.consts.mapM (constSpec r) = some d.constants.toList ∧ d.isModule = sk.isModule := by
  unfold decodeModuleSpec at h
  obtain ⟨sk, hs, h⟩ := bind_some_left h
  obtain ⟨is, hi, h⟩ := bind_some_left h
  obtain ⟨cs, hc, h⟩ := bind_some_left h
  cases h
  exact ⟨sk, hs, by simpa using hi, by simpa using hc, rfl⟩

/-- The parts of a full parse. -/
theorem parseFull_some {r : Region} {root : UInt64} {d : ModDecoded}
    (h : parseFull r root = some d) :
    constNamesOk r root = true ∧ ∃ sk, moduleSkel r root = some sk ∧
      sk.imports.mapM (ImportF.mapM (nameP r)) = some d.imports.toList ∧
      sk.consts.mapM (constSpec r) = some d.constants.toList ∧ d.isModule = sk.isModule := by
  rw [parseFull_eq] at h
  cases hn : constNamesOk r root with
  | false => simp [hn] at h
  | true =>
    simp only [hn, ite_true] at h
    exact ⟨rfl, decodeModuleSpec_some h⟩

/-! ## A constant's skeleton and its decode -/

theorem CKindF.mapM_tag {N E N' E' : Type} {fn : N → Option N'} {fe : E → Option E'}
    {k : CKindF N E} {k' : CKindF N' E'} (h : k.mapM fn fe = some k') :
    k.tag = k'.tag ∧ k.skipped = k'.skipped := by
  cases k <;> simp only [CKindF.mapM] at h
  all_goals first
    | (cases h; exact ⟨rfl, rfl⟩)
    | (repeat' (obtain ⟨_, _, h⟩ := bind_some_left h)
       cases h; exact ⟨rfl, rfl⟩)

/-- What a decoded constant holds of its skeleton. -/
theorem CEntryF.mapM_parts {fn : UInt64 → Option Name} {fe : UInt64 → Option Expr}
    {s : CEntryF UInt64 UInt64} {e : CEntryF Name Expr} (h : s.mapM fn fe = some e) :
    fn s.name = some e.name ∧ s.levelParams.mapM fn = some e.levelParams ∧
      fe s.type = some e.type ∧ s.kind.tag = e.kind.tag ∧ s.kind.skipped = e.kind.skipped := by
  simp only [CEntryF.mapM] at h
  obtain ⟨n, hn, h⟩ := bind_some_left h
  obtain ⟨l, hl, h⟩ := bind_some_left h
  obtain ⟨t, ht, h⟩ := bind_some_left h
  obtain ⟨k, hk, h⟩ := bind_some_left h
  cases h
  exact ⟨hn, hl, ht, CKindF.mapM_tag hk⟩

/-- **A constant read with a memo of its own is the specification's**, on
every region and at every location. -/
theorem readEntry_eq (r : Region) (c : Nat) : readEntry r c = constSpec r c := by
  simp only [readEntry, constSpec]
  cases constSkel r c with
  | none => rfl
  | some s => exact sparseEntry_eq r s

theorem constSpec_parts {r : Region} {c : Nat} {e : CEntryF Name Expr}
    (h : constSpec r c = some e) :
    ∃ s, constSkel r c = some s ∧ s.mapM (nameP r) (exprP r) = some e := by
  simpa [constSpec] using bind_some_left h

theorem stmtP_of_entry {r : Region} {s : CEntryF UInt64 UInt64} {e : CEntryF Name Expr}
    (h : s.mapM (nameP r) (exprP r) = some e) : stmtP r s = some e.stmt := by
  obtain ⟨hn, hl, ht, -⟩ := CEntryF.mapM_parts h
  simp [stmtP, hn, hl, ht, CEntryF.stmt, bind, Option.bind, pure]

/-! ## The reads, of a full parse -/

/-- **The header read of a parsed module** is its full parse's. -/
theorem readHeader_of_full {r : Region} {root : UInt64} {d : ModDecoded}
    (h : parseFull r root = some d) : readHeader r root = some ⟨d.isModule, d.imports⟩ := by
  obtain ⟨-, sk, hs, hi, -, hm⟩ := parseFull_some h
  simp [readHeader, hs, hi, hm, bind, Option.bind, pure]

/-- The names in a parsed module's name table are its constants', each
once. -/
theorem full_names_nodup {r : Region} {root : UInt64} {d : ModDecoded}
    (h : parseFull r root = some d) : (d.constants.toList.map (·.name)).Nodup := by
  obtain ⟨hn, sk, hs, -, hc, -⟩ := parseFull_some h
  obtain ⟨g, cs, hg, hcs, names, hl, hnd, hk⟩ := constNamesOk_spec hn
  rw [moduleSkel_consts hs hg hcs] at hc
  have hlen : d.constants.toList.length = cs.size := by simpa using mapM_length_opt hc
  have : names = d.constants.toList.map (·.name) := by
    apply List.ext_getElem?
    intro k
    by_cases hk' : k < cs.size
    · obtain ⟨s, hsk, hnm⟩ := hk k hk'
      have hk2 : cs.toList[k]? = some cs[k] := by simp [hk']
      have hd := mapM_getElem? hc k
      rw [hk2, Option.bind_some] at hd
      have hcs' : cs[k]? = some cs[k] := by simp [hk']
      rw [hcs', Option.bind_some] at hsk
      have hlt : k < d.constants.toList.length := by omega
      rw [List.getElem?_eq_getElem hlt] at hd
      obtain ⟨s', hs', hm⟩ := constSpec_parts hd.symm
      obtain rfl : s = s' := Option.some.inj (hsk.symm.trans hs')
      rw [← hnm, List.getElem?_map, List.getElem?_eq_getElem hlt, (CEntryF.mapM_parts hm).1]
      rfl
    · have hlen' : d.constants.size = cs.size := by simpa using hlen
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  rw [← this]
  exact hnd

/-- No two the same, by the set of the ones before. -/
theorem distinctGo_iff {α : Type} [BEq α] [LawfulBEq α] [Hashable α] :
    ∀ (xs : List α) (s : Std.HashSet α),
      distinctGo xs s = true ↔ xs.Nodup ∧ ∀ x ∈ xs, s.contains x = false
  | [], s => by simp [distinctGo]
  | x :: xs, s => by
    simp only [distinctGo, Std.HashSet.containsThenInsert_fst, Std.HashSet.containsThenInsert_snd,
      Bool.and_eq_true, Bool.not_eq_true', distinctGo_iff xs, List.nodup_cons,
      List.mem_cons, forall_eq_or_imp, Std.HashSet.contains_insert, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq]
    constructor
    · rintro ⟨hx, hnd, hall⟩
      exact ⟨⟨fun hm => (hall x hm).1 rfl, hnd⟩, hx, fun y hy => (hall y hy).2⟩
    · rintro ⟨⟨hm, hnd⟩, hx, hall⟩
      refine ⟨hx, hnd, fun y hy => ⟨fun he => hm (he ▸ hy), hall y hy⟩⟩

/-- A stored constant as a light read has it. -/
@[expose] def LightConst.ofEntry (c : Nat) (e : CEntryF Name Expr) : LightConst :=
  ⟨c, e.name, e.kind.tag, e.kind.skipped⟩

theorem lightConst_of_spec {r : Region} {c : Nat} {e : CEntryF Name Expr}
    (h : constSpec r c = some e) : lightConst r c = some (LightConst.ofEntry c e) := by
  obtain ⟨s, hs, hm⟩ := constSpec_parts h
  obtain ⟨hn, -, -, ht, hsk⟩ := CEntryF.mapM_parts hm
  simp [lightConst, hs, hn, ht, hsk, LightConst.ofEntry, bind, Option.bind, pure]

/-- The names of the light constants made of some entries are theirs. -/
theorem lightOf_names {locs : List Nat} {es : List (CEntryF Name Expr)}
    (h : locs.length = es.length) :
    ((locs.zip es).map fun p => LightConst.ofEntry p.1 p.2).map (·.name) = es.map (·.name) := by
  simp only [List.map_map]
  have : (LightConst.name ∘ fun p : Nat × CEntryF Name Expr => LightConst.ofEntry p.1 p.2) =
      (·.name) ∘ Prod.snd := rfl
  rw [this, ← List.map_map, List.map_snd_zip (by omega)]

/-- **The light read of a parsed module** is its full parse's: the header,
and per stored constant its location (`moduleSkel`'s) with the name, kind
and filter of the constant the full parse decoded there. -/
theorem readLight_of_full {r : Region} {root : UInt64} {d : ModDecoded} {sk : ModSkel}
    (h : parseFull r root = some d) (hs : moduleSkel r root = some sk) :
    readLight r root = some ⟨⟨d.isModule, d.imports⟩,
      ((sk.consts.zip d.constants.toList).map fun p => LightConst.ofEntry p.1 p.2).toArray⟩ := by
  obtain ⟨-, sk', hs', hi, hc, hm⟩ := parseFull_some h
  obtain rfl : sk = sk' := Option.some.inj (hs.symm.trans hs')
  have hl := mapM_project_zip (k := LightConst.ofEntry) (fun _ _ hx => lightConst_of_spec hx) hc
  have hlen : sk.consts.length = d.constants.toList.length := (mapM_length_opt hc).symm
  have hnames := lightOf_names hlen
  have hd : distinctGo (((sk.consts.zip d.constants.toList).map
      fun p => LightConst.ofEntry p.1 p.2).map (·.name))
      (Std.HashSet.emptyWithCapacity
        ((sk.consts.zip d.constants.toList).map fun p => LightConst.ofEntry p.1 p.2).length) = true := by
    rw [distinctGo_iff, hnames]
    exact ⟨full_names_nodup h, fun x _ => by simp [Std.HashSet.contains_emptyWithCapacity]⟩
  simp only [readLight, hs, hi, hl, hm, bind, Option.bind, hd]
  rfl

/-- **The constant at the `i`-th location of a parsed module** is its full
parse's `i`-th. -/
theorem readEntry_of_full {r : Region} {root : UInt64} {d : ModDecoded} {sk : ModSkel} {i c : Nat}
    (h : parseFull r root = some d) (hs : moduleSkel r root = some sk)
    (hi : sk.consts[i]? = some c) : readEntry r c = d.constants[i]? := by
  obtain ⟨-, sk', hs', -, hc, -⟩ := parseFull_some h
  obtain rfl : sk = sk' := Option.some.inj (hs.symm.trans hs')
  have := mapM_getElem? hc i
  rw [hi, Option.bind_some] at this
  rw [readEntry_eq, ← this]
  simp

/-- The statement read is the part of the constant read it reads. -/
theorem readStmts_eq (r : Region) (cs : List Nat) :
    readStmts r cs = cs.mapM fun c => constSkel r c >>= stmtP r := by
  have hf : stmtsFast r = List.mapM (stmtP r) := funext (stmtsFast_eq r)
  simp only [readStmts, hf]
  exact (mapM_bind (constSkel r) (stmtP r) cs).symm

/-- **The statements of any of a parsed module's constants** are those of
the constants its full parse holds at those locations. -/
theorem readStmts_of_full {r : Region} {root : UInt64} {d : ModDecoded} {sk : ModSkel}
    {cs : List Nat} (h : parseFull r root = some d) (hs : moduleSkel r root = some sk)
    (hsub : ∀ c ∈ cs, c ∈ sk.consts) :
    ∃ es, cs.mapM (readEntry r) = some es ∧ readStmts r cs = some (es.map CEntryF.stmt) ∧
      ∀ e ∈ es, e ∈ d.constants := by
  obtain ⟨-, sk', hs', -, hc, -⟩ := parseFull_some h
  obtain rfl : sk = sk' := Option.some.inj (hs.symm.trans hs')
  obtain ⟨es, hes, hin⟩ := mapM_of_forall (f := readEntry r) (P := (· ∈ d.constants)) (xs := cs)
    fun c hm => by
      obtain ⟨e, he, hx⟩ := mapM_mem hc (hsub c hm)
      exact ⟨e, by rw [readEntry_eq, hx], by simpa using he⟩
  refine ⟨es, hes, ?_, hin⟩
  rw [readStmts_eq]
  refine mapM_project (f := readEntry r) (fun c e he => ?_) hes
  rw [readEntry_eq] at he
  obtain ⟨s, hsk, hm⟩ := constSpec_parts he
  simp [hsk, stmtP_of_entry hm]

/-! ## The prefix read -/

theorem rdU8_extract {b : ByteArray} {k i : Nat} (h : i < (b.extract 0 k).size) :
    rdU8 (b.extract 0 k) i = rdU8 b i := by
  have h' : i < b.size := by simp at h; omega
  simp only [rdU8, h, h', dite_true]
  rw [ByteArray.getElem_extract]
  simp

theorem rdU64_extract {b : ByteArray} {k i : Nat} (h : i + 8 ≤ (b.extract 0 k).size) :
    rdU64 (b.extract 0 k) i = rdU64 b i := by
  have h' : i + 8 ≤ b.size := by simp at h; omega
  simp only [rdU64, h, h', dite_true]
  simp only [ByteArray.getElem_extract, Nat.zero_add]

theorem hdrAdv_extract {b : ByteArray} {k g : Nat} (h : g + 16 ≤ (b.extract 0 k).size) :
    hdrAdv (b.extract 0 k) g = hdrAdv b g := by
  unfold hdrAdv
  rw [rdU8_extract (by omega), rdU64_extract (by omega), rdU8_extract (by omega),
    rdU8_extract (by omega)]

/-- **The walk reads inside what it walks over**: where the walk over a
prefix does not run off it, the walk over the bytes has its outcome, and an
array found ends inside the prefix. -/
theorem hdrWalk_extract (b : ByteArray) (k : Nat) :
    ∀ g, (∀ c e, hdrWalk (b.extract 0 k) g = .found c e →
        hdrWalk b g = .found c e ∧ e ≤ (b.extract 0 k).size) ∧
      (hdrWalk (b.extract 0 k) g = .bad → hdrWalk b g = .bad) := by
  intro g
  induction g using hdrWalk.induct (b := b.extract 0 k) with
  | case1 g h hA hE =>
    refine ⟨?_, ?_⟩
    · intro c e hw
      rw [hdrWalk.eq_1] at hw
      simp only [h, hA, hE, dite_true, ite_true, HdrWalk.found.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hs : g + 16 ≤ b.size := by simp at h; omega
      rw [rdU8_extract (by omega)] at hA
      rw [rdU64_extract (by omega)] at hE ⊢
      have hE' : g + 24 + 8 * (rdU64 b (g + 8)).toNat ≤ b.size := by simp at hE; omega
      rw [hdrWalk.eq_1]
      simp only [hs, hA, hE', dite_true, ite_true]
      exact ⟨trivial, hE⟩
    · intro hw
      rw [hdrWalk.eq_1] at hw
      simp only [h, hA, hE, dite_true, ite_true] at hw
      cases hw
  | case2 g h hA hE =>
    refine ⟨?_, ?_⟩ <;> intros <;> rename_i hw <;> rw [hdrWalk.eq_1] at hw <;>
      simp only [h, hA, hE, dite_true, ite_true, ite_false] at hw <;> cases hw
  | case3 g h hA hK hs ih =>
    have hs' : g + 16 ≤ b.size := by simp at h; omega
    have hA' := hA
    have hK' := hK
    rw [rdU8_extract (by omega)] at hA' hK'
    have hs2 := hs
    rw [hdrAdv_extract h] at hs2
    have hrw : hdrWalk b g = hdrWalk b (g + hdrAdv b g) := by
      rw [hdrWalk.eq_1]
      simp only [hs', hA', hK', hs2, dite_true, ite_true, ite_false]
    have hrw' : hdrWalk (b.extract 0 k) g =
        hdrWalk (b.extract 0 k) (g + hdrAdv (b.extract 0 k) g) := by
      rw [hdrWalk.eq_1]
      simp only [h, hA, hK, hs, dite_true, ite_true, ite_false]
    rw [hrw, hrw']
    rw [hdrAdv_extract h] at ih ⊢
    exact ih
  | case4 g h hA hK hs =>
    have hs' : g + 16 ≤ b.size := by simp at h; omega
    have hw' : hdrWalk (b.extract 0 k) g = .bad := by
      rw [hdrWalk.eq_1]
      simp only [h, hA, hK, hs, dite_true, dite_false, ite_true, ite_false]
    refine ⟨fun c e hw => (by rw [hw'] at hw; cases hw), fun _ => ?_⟩
    rw [rdU8_extract (by omega)] at hA hK
    rw [hdrAdv_extract h] at hs
    rw [hdrWalk.eq_1]
    simp only [hs', hA, hK, hs, dite_true, dite_false, ite_true, ite_false]
  | case5 g h hA hK =>
    have hs' : g + 16 ≤ b.size := by simp at h; omega
    have hw' : hdrWalk (b.extract 0 k) g = .bad := by
      rw [hdrWalk.eq_1]
      simp only [h, hA, hK, dite_true, ite_false]
    refine ⟨fun c e hw => (by rw [hw'] at hw; cases hw), fun _ => ?_⟩
    rw [rdU8_extract (by omega)] at hA hK
    rw [hdrWalk.eq_1]
    simp only [hs', hA, hK, dite_true, ite_false]
  | case6 g h =>
    refine ⟨?_, ?_⟩ <;> intros <;> rename_i hw <;> rw [hdrWalk.eq_1] at hw <;>
      simp only [h, dite_false] at hw <;> cases hw

theorem extract_extract_found {b : ByteArray} {k e : Nat} (he : e ≤ (b.extract 0 k).size) :
    (b.extract 0 k).extract 0 e = b.extract 0 e := by
  rw [ByteArray.extract_extract]
  simp at he
  congr 1
  omega

/-- **The imports of the header prefix are a function of the start of the
file**: where a prefix gives imports, the bytes give the same. -/
theorem importsPre_extract {b : ByteArray} {k : Nat} {x : Array ImportRec}
    (h : importsPre (b.extract 0 k) = some x) : importsPre b = some x := by
  unfold importsPre at h ⊢
  split at h
  · rename_i c e hw
    obtain ⟨hw', he⟩ := (hdrWalk_extract b k _).1 c e hw
    rw [hw']
    simpa only [extract_extract_found he] using h
  · cases h

/-- **And conversely**: where the bytes give imports, so does every prefix
the walk does not run off. -/
theorem importsPre_prefix {b : ByteArray} {k : Nat} {x : Array ImportRec}
    (hw : hdrWalk (b.extract 0 k) dataStart ≠ .short) (h : importsPre b = some x) :
    importsPre (b.extract 0 k) = some x := by
  cases hwk : hdrWalk (b.extract 0 k) dataStart with
  | found c e =>
    obtain ⟨hw', he⟩ := (hdrWalk_extract b k _).1 c e hwk
    unfold importsPre at h ⊢
    rw [hwk]
    rw [hw'] at h
    simpa only [extract_extract_found he] using h
  | short => exact absurd hwk hw
  | bad =>
    have := (hdrWalk_extract b k _).2 hwk
    unfold importsPre at h
    rw [this] at h
    cases h

/-- A walk that does not run off the bytes has seen an object's header. -/
theorem hdrWalk_size {b : ByteArray} {g : Nat} (h : hdrWalk b g ≠ .short) : g + 16 ≤ b.size := by
  rw [hdrWalk.eq_1] at h
  by_cases hs : g + 16 ≤ b.size
  · exact hs
  · rw [dite_eq_right hs] at h
    exact absurd rfl h

/-! ## The validation of a file's start -/

theorem Part.ofBytes_bytes {p : String} {b : ByteArray} {ex : Part}
    (h : Part.ofBytes p b = .ok ex) : ex.bytes = b := by
  unfold Part.ofBytes at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | (cases h; rfl)

/-- **What a file's validation checks.** -/
theorem Part.ofBytes_checks {p : String} {b : ByteArray} {ex : Part}
    (h : Part.ofBytes p b = .ok ex) :
    dataStart ≤ b.size ∧ (b.extract 0 5 == "olean".toUTF8) = true ∧ (rdU8 b 5 == 2) = true ∧
      (rdU8 b 6 &&& 1 == 1) = true ∧ (b.size % 8 == 0) = true ∧
      (rdU64 b 80 % 8 == 0 && decide ((rdU64 b 80).toNat + b.size < 2 ^ 64)) = true := by
  unfold Part.ofBytes at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rename_i h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **A file's validation holds of a prefix** of a whole number of words
holding the header. -/
theorem Part.ofBytes_prefix {p : String} {b : ByteArray} {ex : Part} {k : Nat}
    (h : Part.ofBytes p b = .ok ex) (hk : dataStart ≤ (b.extract 0 k).size)
    (h8 : (b.extract 0 k).size % 8 = 0) : ∃ ex', Part.ofBytes p (b.extract 0 k) = .ok ex' := by
  obtain ⟨-, h1, h2, h3, -, h5⟩ := Part.ofBytes_checks h
  have hsz : (b.extract 0 k).size ≤ b.size := by simp [ByteArray.size_extract]; omega
  have hd : (96 : Nat) ≤ (b.extract 0 k).size := hk
  have hm : (b.extract 0 k).extract 0 5 = b.extract 0 5 := extract_extract_found (by omega)
  refine ⟨⟨rdU64 b 80, b.extract 0 k⟩, ?_⟩
  unfold Part.ofBytes
  simp only [hm, rdU8_extract (show 5 < (b.extract 0 k).size by omega),
    rdU8_extract (show 6 < (b.extract 0 k).size by omega),
    rdU64_extract (show 80 + 8 ≤ (b.extract 0 k).size by omega)]
  have h8' : ((b.extract 0 k).size % 8 == 0) = true := by simpa using h8
  have h5' : (rdU64 b 80 % 8 == 0 &&
      decide ((rdU64 b 80).toNat + (b.extract 0 k).size < 2 ^ 64)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h5 ⊢
    exact ⟨h5.1, by omega⟩
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  rw [ite_eq_left hk, ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, ite_eq_left h8',
    ite_eq_left h5']

/-! ## The module reads -/

/-- **A module's exported read** is the full parse of that file alone, whose
imports the file's prefix holds. -/
theorem parseExported_full {m : Name} {ex : Part} {d : ModDecoded}
    (h : parseExported m ex = .ok d) :
    parseFull (Region.single ex) ex.root = some d ∧ importsPre ex.bytes = some d.imports := by
  unfold parseExported parseFullE at h
  cases hf : parseFull (Region.single ex) ex.root with
  | none => simp [hf, bind, Except.bind] at h
  | some d' =>
    simp only [hf, bind, Except.bind] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rename_i hb
      exact ⟨rfl, by simpa using hb⟩
    · cases h

/-- A part of a module's read is its full parse, with the exported part's
imports. -/
theorem parsePart_ok {m : Name} {er : ModDecoded} {part : String} {r : Region} {root : UInt64}
    {d : ModDecoded} (h : parsePart m er part r root = .ok d) :
    parseFull r root = some d ∧ d.isModule = true ∧ d.imports = er.imports := by
  unfold parsePart parseFullE at h
  cases hp : parseFull r root with
  | none => simp [hp, bind, Except.bind] at h
  | some d' =>
    simp only [hp, bind, Except.bind, pure, Except.pure] at h
    by_cases hm : d'.isModule = true
    · by_cases hi : (d'.imports == er.imports) = true
      · simp only [hm, hi, ite_true] at h
        cases h
        exact ⟨rfl, hm, eq_of_beq hi⟩
      · simp [hm, hi] at h
    · simp [hm] at h

/-- **A module's full read** is the full parses of its server and private
parts in the region of its files; the read's imports are the exported
part's and the parts' are the same, and its constants the private part's,
its exported constants the exported read's. -/
theorem parseModule_full {m : Name} {er : ModDecoded} {ex s p : Part} {mr : ModRead}
    (h : parseModule m er ex s p = .ok mr) :
    ∃ r ds dp, Region.ofParts #[ex, s, p] = .ok r ∧
      parseFull r s.root = some ds ∧ parseFull r p.root = some dp ∧
      ds.imports = er.imports ∧ dp.imports = er.imports ∧
      mr.name = m ∧ mr.isModule = true ∧ mr.imports = er.imports ∧
      mr.constants = dp.constants ∧ mr.exported = er.constants := by
  unfold parseModule at h
  cases hr : Region.ofParts #[ex, s, p] with
  | error e => simp [hr, bind, Except.bind] at h
  | ok r =>
    simp only [hr, bind, Except.bind] at h
    cases hs : parsePart m er "server" r s.root with
    | error e => simp [hs] at h
    | ok ds =>
      simp only [hs] at h
      cases hp : parsePart m er "private" r p.root with
      | error e => simp [hp] at h
      | ok dp =>
        simp only [hp] at h
        obtain ⟨hs1, -, hs3⟩ := parsePart_ok hs
        obtain ⟨hp1, -, hp3⟩ := parsePart_ok hp
        split at h
        · cases h
          exact ⟨r, ds, dp, rfl, hs1, hp1, hs3, hp3, rfl, rfl, rfl, rfl, rfl⟩
        · cases h
        · cases h

end ConLeche.Frontend.Olean
