module

public import ConLeche.Frontend.Olean.Reads
public import ConLeche.Frontend.Olean.Header
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Sparse
import Std.Data.HashSet.Lemmas

/-!
# Every read of a part of a `ModuleData` is a projection of it

At a region and an address: `parseAt` is the specification `decodeAt`
(`parseAt_eq_spec`).  **Where it succeeds, every other read succeeds, and returns
its part of the result** (`namePositionsAt_of_full`, `entryAt_of_full`,
`stmtsAt_of_full`; `entryAt_eq` on every region).

The prefix read of a file's imports is related to the whole file in both
directions: `importsPre_extract` (a prefix's imports are the file's), and
`importsPre_prefix` (a file's imports are those of every prefix the walk stops in).

The interface's reads, at a level, are `ConLeche/Verify/Frontend/Olean/View.lean`;
on a snapshot, `ConLeche/Verify/Frontend/Olean/Files.lean`.
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

/-- `constNamesOk`'s walk: the names it saw are the constants', each once, and none
of those seen before. -/
theorem constNamesGo_spec {r : Region} :
    ∀ {ns cs : List Nat} {seen : Std.HashSet Name}, constNamesGo r ns cs seen = true →
      ∃ names : List Name, names.length = cs.length ∧ names.Nodup ∧
        (∀ x ∈ names, seen.contains x = false) ∧
        ∀ k, k < cs.length → ∃ sk, (cs[k]?).bind (constSkel r) = some sk ∧
          nameP r sk.name = names[k]?
  | [], [], seen, _ => ⟨[], rfl, List.nodup_nil, by simp, by simp⟩
  | [], _ :: _, seen, h => by simp [constNamesGo] at h
  | _ :: _, [], seen, h => by simp [constNamesGo] at h
  | n :: ns, c :: cs, seen, h => by
    unfold constNamesGo at h
    split at h
    · rename_i sk a hsk hna
      simp only [Bool.and_eq_true, Bool.or_eq_true, Std.HashSet.containsThenInsert_fst,
        Std.HashSet.containsThenInsert_snd, Bool.not_eq_true'] at h
      obtain ⟨hnm, hb, ht⟩ := h
      obtain ⟨names, hl, hnd, hseen, hk⟩ := constNamesGo_spec ht
      have hname : nameP r sk.name = some a := by
        rcases hnm with h1 | h1
        · have h1' := beq_iff_eq.1 h1
          unfold nameP
          have hv : (sk.name == 1) = false := by
            cases hv : (sk.name == 1)
            · rfl
            · exfalso
              have h2 : sk.name = 1 := beq_iff_eq.1 hv
              rw [h2] at h1'
              revert h1'
              simp [Region.loc, isScalar]
          rw [hv]
          simp only [Bool.false_eq_true, ite_false, h1']
          exact hna
        · exact beq_iff_eq.1 h1
      refine ⟨a :: names, by simp [hl], ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨fun hm => ?_, hnd⟩
        have := hseen a hm
        simp [Std.HashSet.contains_insert] at this
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hb
        · have := hseen x hx
          simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
          exact this.2
      · intro k hk'
        cases k with
        | zero => exact ⟨sk, by simpa using hsk, by simpa using hname⟩
        | succ k =>
          obtain ⟨s, h1, h2⟩ := hk k (by simpa using hk')
          exact ⟨s, by simpa using h1, by simpa using h2⟩
    · cases h

/-- **A name table that agrees names its constants, each once**
(`constNamesOk`). -/
theorem constNamesOk_spec {r : Region} {root : UInt64} (h : constNamesOk r root = true) :
    ∃ g cs, r.loc root = some g ∧ r.objArray g (r.fld g 2) = some cs ∧
      ∃ names : List Name, names.length = cs.size ∧ names.Nodup ∧
        ∀ k, k < cs.size → ∃ sk, (cs[k]?).bind (constSkel r) = some sk ∧
          nameP r sk.name = names[k]? := by
  unfold constNamesOk at h
  split at h
  · cases h
  rename_i g hg
  split at h
  · split at h
    · rename_i ns cs hns hcs
      simp only [Bool.and_eq_true] at h
      obtain ⟨-, hgo⟩ := h
      obtain ⟨names, hl, hnd, -, hk⟩ := constNamesGo_spec hgo
      refine ⟨g, cs, hg, hcs, names, by simpa using hl, hnd, fun k hk' => ?_⟩
      obtain ⟨s, h1, h2⟩ := hk k (by simpa using hk')
      exact ⟨s, by simpa using h1, h2⟩
    · cases h
  · cases h

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

/-- An element of a `mapM`'s result comes from one of the list. -/
theorem mapM_mem_inv {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ {y : β}, y ∈ ys → ∃ x ∈ xs, f x = some y
  | [], ys, h, y, hy => by simp at h; subst h; simp at hy
  | x :: xs, ys, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨y', hy', h⟩ := bind_some_left h
    obtain ⟨ys', hys, h⟩ := bind_some_left h
    cases h
    rcases List.mem_cons.mp hy with rfl | hm
    · exact ⟨x, List.mem_cons_self, hy'⟩
    · obtain ⟨x', hx', hf⟩ := mapM_mem_inv hys hm
      exact ⟨x', List.mem_cons_of_mem _ hx', hf⟩

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

/-- **The parts of a full parse.** -/
theorem parseAt_some {r : Region} {root : UInt64} {d : ModDecoded}
    (h : parseAt r root = some d) :
    constNamesOk r root = true ∧ ∃ sk, moduleSkel r root = some sk ∧
      sk.imports.mapM (ImportF.mapM (nameP r)) = some d.imports.toList ∧
      sk.consts.mapM (constSpec r) = some d.constants.toList ∧ d.isModule = sk.isModule := by
  rw [parseAt_eq_spec] at h
  unfold decodeAt at h
  cases hn : constNamesOk r root with
  | false =>
    rw [hn] at h
    cases h
  | true =>
    rw [hn] at h
    replace h : (do
      let sk ← moduleSkel r root
      let imports ← sk.imports.mapM (ImportF.mapM (nameP r))
      let constants ← sk.consts.mapM (constSpec r)
      pure (ModDecoded.mk sk.isModule imports.toArray constants.toArray)) = some d := h
    obtain ⟨sk, hs, h⟩ := bind_some_left h
    obtain ⟨is, hi, h⟩ := bind_some_left h
    obtain ⟨cs, hc, h⟩ := bind_some_left h
    cases h
    exact ⟨rfl, sk, hs, by simpa using hi, by simpa using hc, rfl⟩

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
theorem entryAt_eq (r : Region) (c : Nat) : entryAt r c = constSpec r c := by
  simp only [entryAt, constSpec]
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

/-- The names in a parsed module's name table are its constants', each
once. -/
theorem full_names_nodup {r : Region} {root : UInt64} {d : ModDecoded}
    (h : parseAt r root = some d) : (d.constants.toList.map (·.name)).Nodup := by
  obtain ⟨hn, sk, hs, -, hc, -⟩ := parseAt_some h
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

/-- A stored constant as `namePositionsAt` has it. -/
@[expose] def NamePosition.ofEntry (c : Nat) (e : CEntryF Name Expr) : NamePosition :=
  ⟨c, e.name, e.kind.tag, e.kind.skipped⟩

theorem namePosition_of_spec {r : Region} {c : Nat} {e : CEntryF Name Expr}
    (h : constSpec r c = some e) : namePosition r c = some (NamePosition.ofEntry c e) := by
  obtain ⟨s, hs, hm⟩ := constSpec_parts h
  obtain ⟨hn, -, -, ht, hsk⟩ := CEntryF.mapM_parts hm
  simp [namePosition, hs, hn, ht, hsk, NamePosition.ofEntry, bind, Option.bind, pure]

/-- The names of the positions made of some entries are theirs. -/
theorem namePositions_names {locs : List Nat} {es : List (CEntryF Name Expr)}
    (h : locs.length = es.length) :
    ((locs.zip es).map fun p => NamePosition.ofEntry p.1 p.2).map (·.name) = es.map (·.name) := by
  simp only [List.map_map]
  have : (NamePosition.name ∘ fun p : Nat × CEntryF Name Expr => NamePosition.ofEntry p.1 p.2) =
      (·.name) ∘ Prod.snd := rfl
  rw [this, ← List.map_map, List.map_snd_zip (by omega)]

theorem namePositions_tags {locs : List Nat} {es : List (CEntryF Name Expr)}
    (h : locs.length = es.length) :
    ((locs.zip es).map fun p => NamePosition.ofEntry p.1 p.2).map (·.tag) = es.map (·.kind.tag) := by
  simp only [List.map_map]
  have : (NamePosition.tag ∘ fun p : Nat × CEntryF Name Expr => NamePosition.ofEntry p.1 p.2) =
      (·.kind.tag) ∘ Prod.snd := rfl
  rw [this, ← List.map_map, List.map_snd_zip (by omega)]

theorem namePositions_skipped {locs : List Nat} {es : List (CEntryF Name Expr)}
    (h : locs.length = es.length) :
    ((locs.zip es).map fun p => NamePosition.ofEntry p.1 p.2).map (·.skipped) =
      es.map (·.kind.skipped) := by
  simp only [List.map_map]
  have : (NamePosition.skipped ∘ fun p : Nat × CEntryF Name Expr => NamePosition.ofEntry p.1 p.2) =
      (·.kind.skipped) ∘ Prod.snd := rfl
  rw [this, ← List.map_map, List.map_snd_zip (by omega)]

/-- **The name positions of a parsed module** is its full parse's: the header,
and per stored constant its location (`moduleSkel`'s) with the name, kind
and filter of the constant the full parse decoded there. -/
theorem namePositionsAt_of_full {r : Region} {root : UInt64} {d : ModDecoded} {sk : ModSkel}
    (h : parseAt r root = some d) (hs : moduleSkel r root = some sk) :
    namePositionsAt r root = some ⟨⟨d.isModule, d.imports⟩,
      ((sk.consts.zip d.constants.toList).map fun p => NamePosition.ofEntry p.1 p.2).toArray⟩ := by
  obtain ⟨-, sk', hs', hi, hc, hm⟩ := parseAt_some h
  obtain rfl : sk = sk' := Option.some.inj (hs.symm.trans hs')
  have hl := mapM_project_zip (k := NamePosition.ofEntry) (fun _ _ hx => namePosition_of_spec hx) hc
  have hlen : sk.consts.length = d.constants.toList.length := (mapM_length_opt hc).symm
  have hnames := namePositions_names hlen
  have hd : distinctGo (((sk.consts.zip d.constants.toList).map
      fun p => NamePosition.ofEntry p.1 p.2).map (·.name))
      (Std.HashSet.emptyWithCapacity
        ((sk.consts.zip d.constants.toList).map fun p => NamePosition.ofEntry p.1 p.2).length) = true := by
    rw [distinctGo_iff, hnames]
    exact ⟨full_names_nodup h, fun x _ => by simp [Std.HashSet.contains_emptyWithCapacity]⟩
  simp only [namePositionsAt, hs, hi, hl, hm, bind, Option.bind, hd]
  rfl

/-- **The constant at the `i`-th location of a parsed module** is its full
parse's `i`-th. -/
theorem entryAt_of_full {r : Region} {root : UInt64} {d : ModDecoded} {sk : ModSkel} {i c : Nat}
    (h : parseAt r root = some d) (hs : moduleSkel r root = some sk)
    (hi : sk.consts[i]? = some c) : entryAt r c = d.constants[i]? := by
  obtain ⟨-, sk', hs', -, hc, -⟩ := parseAt_some h
  obtain rfl : sk = sk' := Option.some.inj (hs.symm.trans hs')
  have := mapM_getElem? hc i
  rw [hi, Option.bind_some] at this
  rw [entryAt_eq, ← this]
  simp

/-- The statement read is the part of the constant read it reads. -/
theorem stmtsAt_eq (r : Region) (cs : List Nat) :
    stmtsAt r cs = cs.mapM fun c => constSkel r c >>= stmtP r := by
  have hf : stmtsFast r = List.mapM (stmtP r) := funext (stmtsFast_eq r)
  simp only [stmtsAt, hf]
  exact (mapM_bind (constSkel r) (stmtP r) cs).symm

/-- **The statements of any of a parsed module's constants** are those of
the constants its full parse holds at those locations. -/
theorem stmtsAt_of_full {r : Region} {root : UInt64} {d : ModDecoded} {sk : ModSkel}
    {cs : List Nat} (h : parseAt r root = some d) (hs : moduleSkel r root = some sk)
    (hsub : ∀ c ∈ cs, c ∈ sk.consts) :
    ∃ es, cs.mapM (entryAt r) = some es ∧ stmtsAt r cs = some (es.map CEntryF.stmt) ∧
      ∀ e ∈ es, e ∈ d.constants := by
  obtain ⟨-, sk', hs', -, hc, -⟩ := parseAt_some h
  obtain rfl : sk = sk' := Option.some.inj (hs.symm.trans hs')
  obtain ⟨es, hes, hin⟩ := mapM_of_forall (f := entryAt r) (P := (· ∈ d.constants)) (xs := cs)
    fun c hm => by
      obtain ⟨e, he, hx⟩ := mapM_mem hc (hsub c hm)
      exact ⟨e, by rw [entryAt_eq, hx], by simpa using he⟩
  refine ⟨es, hes, ?_, hin⟩
  rw [stmtsAt_eq]
  refine mapM_project (f := entryAt r) (fun c e he => ?_) hes
  rw [entryAt_eq] at he
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

end ConLeche.Frontend.Olean
