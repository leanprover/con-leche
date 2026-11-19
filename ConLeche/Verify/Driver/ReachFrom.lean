module

public import ConLeche.Driver.Reach
public import ConLeche.Verify.Frontend.ModelIO
public import ConLeche.Verify.Frontend.Olean.Roots
import ConLeche.Verify.Frontend.Olean.Present
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Files
public import ConLeche.Verify.Frontend.Olean.Sparse

/-!
# Where the reach read its records

What `ConLeche/Driver/Reach.lean`'s reach read, on a snapshot (task #448): every context
record is read from the files of one module, its **source**, at a name position its name
table holds on the snapshot (`RecordFrom`):

* **a statement** (`.axiomDecl cv`) read at a copy: the skeleton at the position, its name,
  level parameters and type as the specification reads them (`StmtSkel`); at a
  compiler-trust name only where the source's private part declares an opaque constant or
  an axiom of that name;
* **a whole constant** (a definition with its value) read at a copy, through the stream
  reader's builder (`recordOfEntry`), or a quotient constant;
* **an inductive group** read from the source's private part (`GroupRead`): the group's
  constants at the positions its name table gives, through `groupRecord`.

A copy is the importer's (the name index's first copy, at the level its module is loaded
at: `EnvOk`) or a completion's located copy, at its module's private part.  The reads go
through the reach's caches, whose invariant (`CacheOk`) says that every cached table, memo,
recursor map, view and located copy is the snapshot's.

* `readRecord_from` — **one record read**;
* `reachGo_from` — **the worklist**: every context record and its home, `RecordFrom`;
* `reach_from` — at every accepting outcome of `reach` on the search path's reads.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend.Olean

theorem PartKey.beq_iff (a b : PartKey) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show (_ && _) = true ↔ _
  simp

instance : LawfulBEq PartKey where
  eq_of_beq h := (PartKey.beq_iff _ _).1 h
  rfl := (PartKey.beq_iff _ _).2 rfl

/-! ## What the snapshot holds -/

/-- **A part's files** on the snapshot. -/
@[expose] def PartFiles (sp : Roots) (fs : FS) (k : PartKey) (f : ModFiles) : Prop :=
  ModelIO.CanGive (readFiles sp k.mod k.level) fs (.ok f)

/-- **A part's name table** on the snapshot. -/
@[expose] def PartNames (sp : Roots) (fs : FS) (k : PartKey) (t : NamePositions) : Prop :=
  ModelIO.CanGive (readPartNames sp (k.mod, k.level)) fs (.ok t)

/-- **A copy of a name**: a name position its part's name table holds on the snapshot. -/
@[expose] def CopyAt (sp : Roots) (fs : FS) (s : Spot) : Prop :=
  ∃ t, PartNames sp fs s.part t ∧ s.pos ∈ t.consts

/-- **Module `h`'s view on the snapshot** (`viewOf`'s, by the specification): the parts of
`viewKeys` over `h`'s header fixpoint, read from `h`'s private part's header, each part's name
table the snapshot's, folded in order with the first copy of each name kept. -/
@[expose] def HomeView (sp : Roots) (fs : FS) (h : Name) (v : Std.HashMap Name Spot) : Prop :=
  ∃ (own : NamePositions) (ld : Loads) (ts : List NamePositions),
    PartNames sp fs ⟨h, .private⟩ own ∧
    ModelIO.CanGive (headerFixpoint (moduleImports sp) own.header.isModule own.header.imports) fs
      (.ok ld) ∧
    ts.length = (viewKeys h ld).length ∧
    (∀ k t, (k, t) ∈ (viewKeys h ld).zip ts → PartNames sp fs k t) ∧
    v = ((viewKeys h ld).zip ts).foldl (fun v kt => viewStep v kt.1 kt.2) {}

/-- **A loaded copy's spot**: the part its module is loaded at, and its name position there
(`importerSpot`'s, `clashAgree`'s). -/
@[expose] def spotOf (wr : WorkerReads) (cp : Copy) (q : NamePosition) : Spot :=
  ⟨⟨wr.loads.nameAt cp.mod, ((wr.loads.flags[cp.mod]?).getD default).level⟩, q⟩

/-- **A part's region** on the snapshot. -/
@[expose] def PartRegion (sp : Roots) (fs : FS) (k : PartKey) (r : Region) : Prop :=
  ∃ f a, PartFiles sp fs k f ∧ f.viewRegion k.level = some (r, a)

/-- **The statement and kind at a location**, as the specification reads them off its
skeleton (a theorem's value is no part of it). -/
@[expose] def StmtSkel (r : Region) (loc : Nat) (cv : ConstantVal) (k : CKindF Name Unit) :
    Prop :=
  ∃ s, constSkel r loc = some s ∧ nameP r s.name = some cv.name ∧
    s.levelParams.mapM (nameP r) = some cv.levelParams ∧ exprP r s.type = some cv.type ∧
    s.kind.mapM (nameP r) (fun _ => some ()) = some k

/-- A part's name lookup, as `lookOf` builds it. -/
@[expose] def lookTable (t : NamePositions) : Std.HashMap Name NamePosition :=
  t.consts.foldl (fun (l : Std.HashMap Name NamePosition) q => l.insert q.name q)
    (Std.HashMap.emptyWithCapacity t.consts.size)

/-- **An inductive group read from a part** (`groupAt`'s reads, on the snapshot): `n`'s
position in the part's name table, the constant there an inductive type of block `all`, the
block's members' and their constructors' positions, the part's recursors by their block's
first member, the constants at those positions, and the group's record built from them. -/
@[expose] def GroupRead (sp : Roots) (fs : FS) (k : PartKey) (n : Name) (d : Declaration) :
    Prop :=
  ∃ (t : NamePositions) (q : NamePosition) (tE : CEntryF Name Expr) (np ni nn : Nat)
    (all cs : List Name) (ir iu irf : Bool) (mqs cqs : List NamePosition)
    (tys rest : List (CEntryF Name Expr)) (t' : NamePositions) (rb : Std.HashMap Name (Array Nat))
    (r₁ r₂ r₃ r₄ : Region),
    PartNames sp fs k t ∧ (lookTable t)[n]? = some q ∧
    PartRegion sp fs k r₁ ∧ entryAt r₁ q.loc = some tE ∧
    tE.kind = .induct np ni all cs nn ir iu irf ∧
    all.mapM ((lookTable t)[·]?) = some mqs ∧
    PartRegion sp fs k r₂ ∧ (mqs.map (·.loc)).mapM (entryAt r₂) = some tys ∧
    (groupCtorNames tys).mapM ((lookTable t)[·]?) = some cqs ∧
    PartNames sp fs k t' ∧ PartRegion sp fs k r₃ ∧ recBlocksAt r₃ t' = some rb ∧
    PartRegion sp fs k r₄ ∧ (cqs.map (·.loc) ++ groupRecLocs rb all).mapM (entryAt r₄) = some rest ∧
    groupRecord (groupMerged tE tys rest all) n = .ok d

/-- **Where a context record was read, and how** (see the module docstring): the record and
its source module. -/
inductive RecordFrom (sp : Roots) (fs : FS) : Declaration → Name → Prop
  /-- a copy's statement, at a part of its source: the skeleton's statement; a definition only
  at a private part (a completion's located copy); at a compiler-trust name only where the
  source's private part declares an opaque constant or an axiom of the copy's name -/
  | stmt {x : Name} {s : Spot} {r : Region} {cv : ConstantVal} {k : CKindF Name Unit}
      (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server) (hr : PartRegion sp fs s.part r)
      (hst : StmtSkel r s.pos.loc cv k) (hsk : s.pos.skipped = false)
      (hg : groupOfKind x k = none) (hq : k.tag ≠ 4) (hd : k.tag = 1 → s.part.level = .private)
      (hred : reduceOpNames.contains cv.name = true → ∃ q : Spot, CopyAt sp fs q ∧
        q.part = ⟨s.part.mod, .private⟩ ∧ q.pos.name = s.pos.name ∧ (q.pos.tag = 0 ∨ q.pos.tag = 3)) :
      RecordFrom sp fs (.axiomDecl cv) s.part.mod
  /-- a definition with its value, read whole at a copy -/
  | entry {s : Spot} {r r₀ : Region} {e : CEntryF Name Expr} {d : Declaration} {cv : ConstantVal}
      {k : CKindF Name Unit}
      (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server) (hr : PartRegion sp fs s.part r)
      (he : entryAt r s.pos.loc = some e) (hr₀ : PartRegion sp fs s.part r₀)
      (hst : StmtSkel r₀ s.pos.loc cv k) (hk : k.tag = 1) (hsk : s.pos.skipped = false)
      (hd : recordOfEntry e = .ok d) :
      RecordFrom sp fs d s.part.mod
  /-- a quotient constant, its statement and kind read at a copy -/
  | quot {s : Spot} {r : Region} {cv : ConstantVal} {q : String} {d : Declaration}
      (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server) (hr : PartRegion sp fs s.part r)
      (hst : StmtSkel r s.pos.loc cv (.quot q))
      (hd : recordOfEntry ⟨cv.name, cv.levelParams, cv.type, .quot q⟩ = .ok d) :
      RecordFrom sp fs d s.part.mod
  /-- an inductive group, read from the source's private part -/
  | group {h n : Name} {d : Declaration} (hg : GroupRead sp fs ⟨h, .private⟩ n d) :
      RecordFrom sp fs d h

/-! ## Moving reads of one module between two lookups (task #608)

A compared modular run reads some modules through a lookup and others through it without its
fallback (`Roots.Trims`).  What one lookup read of a module's files, the other reads alike
wherever it finds the module (`readPartNames_move`, …). -/

section Move

variable {a b L : Roots} {fs : FS} {lb : Located}

theorem PartNames.move (ha : a.Trims L) (hb : b.Trims L) {k : PartKey} {t : NamePositions}
    (hfb : ModelIO.CanGive (findModule b k.mod) fs (.ok lb)) (h : PartNames a fs k t) :
    PartNames b fs k t :=
  readPartNames_move (x := (k.mod, k.level)) ha hb hfb h

theorem PartNames.trims (ha : a.Trims L) {k : PartKey} {t : NamePositions}
    (h : PartNames a fs k t) : PartNames L fs k t :=
  readPartNames_trims (x := (k.mod, k.level)) ha h

theorem PartFiles.move (ha : a.Trims L) (hb : b.Trims L) {k : PartKey} {f : ModFiles}
    (hfb : ModelIO.CanGive (findModule b k.mod) fs (.ok lb)) (h : PartFiles a fs k f) :
    PartFiles b fs k f :=
  readFiles_move ha hb hfb h

theorem CopyAt.move (ha : a.Trims L) (hb : b.Trims L) {s : Spot}
    (hfb : ModelIO.CanGive (findModule b s.part.mod) fs (.ok lb)) (h : CopyAt a fs s) :
    CopyAt b fs s :=
  let ⟨t, ht, hq⟩ := h
  ⟨t, ht.move ha hb hfb, hq⟩

theorem PartRegion.move (ha : a.Trims L) (hb : b.Trims L) {k : PartKey} {r : Region}
    (hfb : ModelIO.CanGive (findModule b k.mod) fs (.ok lb)) (h : PartRegion a fs k r) :
    PartRegion b fs k r :=
  let ⟨f, x, hf, hr⟩ := h
  ⟨f, x, hf.move ha hb hfb, hr⟩

theorem GroupRead.move (ha : a.Trims L) (hb : b.Trims L) {k : PartKey} {n : Name}
    {d : Declaration} (hfb : ModelIO.CanGive (findModule b k.mod) fs (.ok lb))
    (h : GroupRead a fs k n d) : GroupRead b fs k n d := by
  obtain ⟨t, q, tE, np, ni, nn, all, cs, ir, iu, irf, mqs, cqs, tys, rest, t', rb, r₁, r₂, r₃, r₄,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨t, q, tE, np, ni, nn, all, cs, ir, iu, irf, mqs, cqs, tys, rest, t', rb, r₁, r₂, r₃, r₄,
    h1.move ha hb hfb, h2, h3.move ha hb hfb, h4, h5, h6, h7.move ha hb hfb, h8, h9,
    h10.move ha hb hfb, h11.move ha hb hfb, h12, h13.move ha hb hfb, h14, h15⟩

/-- A part whose table a lookup reads, it finds the module of. -/
theorem PartNames.found {k : PartKey} {t : NamePositions} (h : PartNames a fs k t) :
    ∃ loc, ModelIO.CanGive (findModule a k.mod) fs (.ok loc) := by
  obtain ⟨hs, hs', h⟩ := h
  simp only [readPartNames, ModelIO.bind_ok] at h
  obtain ⟨x, hs₁, hx, hk⟩ := h
  rcases x with e | loc
  · simp at hk
  exact ⟨loc, hs, hs₁, hx⟩

/-- **A record read from module `h` through one lookup is read alike through the other**, where
that one finds `h`. -/
theorem RecordFrom.move (ha : a.Trims L) (hb : b.Trims L) {d : Declaration} {h : Name}
    (hfb : ModelIO.CanGive (findModule b h) fs (.ok lb)) (hd : RecordFrom a fs d h) :
    RecordFrom b fs d h := by
  cases hd with
  | stmt hs hl hr hst hsk hg hq hd hred =>
    exact .stmt (hs.move ha hb hfb) hl (hr.move ha hb hfb) hst hsk hg hq hd fun hc =>
      let ⟨q, hq, hp, hn, ht⟩ := hred hc
      ⟨q, hq.move ha hb (by rw [hp]; exact hfb), hp, hn, ht⟩
  | entry hs hl hr he hr₀ hst hk hsk hd =>
    exact .entry (hs.move ha hb hfb) hl (hr.move ha hb hfb) he (hr₀.move ha hb hfb) hst hk hsk hd
  | quot hs hl hr hst hd => exact .quot (hs.move ha hb hfb) hl (hr.move ha hb hfb) hst hd
  | group hg => exact .group (hg.move ha hb hfb)

end Move

/-! ## The reach's environment and caches -/

/-- **The reach's environment on the search path**: its reads are the search path's, and its
name index holds each loaded module's part's table, a module's position in the load order
naming it. -/
structure EnvOk (sp : Roots) (fs : FS) (env : ReachEnv ModelIO) : Prop where
  rd : env.rd = .ofPath sp
  parts : ∀ i t, env.wr.index.parts[i]? = some t →
    PartNames sp fs ⟨env.wr.loads.nameAt i, ((env.wr.loads.flags[i]?).getD default).level⟩ t
  index : ∀ m i, env.wr.loads.index[m]? = some i → env.wr.loads.nameAt i = m

/-- **The reach's caches hold the snapshot's**: tables, lookups, regions with good memos,
recursor maps, views' copies and located copies (the latter at private parts). -/
structure CacheOk (sp : Roots) (fs : FS) (c : ReachCache) : Prop where
  tables : ∀ k t, c.tables[k]? = some t → PartNames sp fs k t
  looks : ∀ k l, c.looks[k]? = some l → ∃ t, PartNames sp fs k t ∧ l = lookTable t
  parts : ∀ k r st, c.parts[k]? = some (r, st) → PartRegion sp fs k r ∧ st.Good r
  recBlocks : ∀ k m, c.recBlocks[k]? = some m →
    ∃ t r, PartNames sp fs k t ∧ PartRegion sp fs k r ∧ recBlocksAt r t = some m
  views : ∀ (h : Name) (v : Std.HashMap Name Spot), c.views[h]? = some v →
    ∀ (y : Name) (s : Spot), v[y]? = some s → CopyAt sp fs s
  located : ∀ (y : Name) (s : Spot), c.located[y]? = some s → s.part.level = .private ∧ CopyAt sp fs s

theorem CacheOk.searches {sp : Roots} {fs : FS} {c : ReachCache} (hc : CacheOk sp fs c) (n : Nat) :
    CacheOk sp fs { c with searches := n } :=
  ⟨hc.tables, hc.looks, hc.parts, hc.recBlocks, hc.views, hc.located⟩

theorem CacheOk.pending {sp : Roots} {fs : FS} {c : ReachCache} (hc : CacheOk sp fs c)
    (p : Array (String × Name × ConstantVal)) : CacheOk sp fs { c with pending := p } :=
  ⟨hc.tables, hc.looks, hc.parts, hc.recBlocks, hc.views, hc.located⟩

theorem CacheOk.partners {sp : Roots} {fs : FS} {c : ReachCache} (hc : CacheOk sp fs c)
    (p : Array (Name × Name)) : CacheOk sp fs { c with partners := p } :=
  ⟨hc.tables, hc.looks, hc.parts, hc.recBlocks, hc.views, hc.located⟩

theorem CacheOk.empty (sp : Roots) (fs : FS) : CacheOk sp fs {} :=
  ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- **A skeleton's statement and the whole constant there**: one statement, one kind
constructor. -/
theorem StmtSkel.entry {r : Region} {loc : Nat} {cv : ConstantVal} {k : CKindF Name Unit}
    {e : CEntryF Name Expr} (h : StmtSkel r loc cv k) (he : entryAt r loc = some e) :
    e.stmt = cv ∧ e.kind.tag = k.tag := by
  obtain ⟨s, hs, hn, hl, ht, hk⟩ := h
  rw [entryAt_eq] at he
  obtain ⟨s', hs', hm⟩ := constSpec_parts he
  rw [hs] at hs'
  cases hs'
  obtain ⟨hn', hl', ht', htag, -⟩ := CEntryF.mapM_parts hm
  rw [hn] at hn'; rw [hl] at hl'; rw [ht] at ht'
  refine ⟨?_, htag.symm.trans (CKindF.mapM_tag hk).1⟩
  obtain ⟨n, l, ty⟩ := cv
  simp only [Option.some.injEq] at hn' hl' ht'
  simp [CEntryF.stmt, hn', hl', ht']

/-! ## The lookup's entries -/

theorem lookTable_spec (t : NamePositions) {n : Name} {q : NamePosition}
    (h : (lookTable t)[n]? = some q) : q ∈ t.consts ∧ q.name = n := by
  unfold lookTable at h
  rw [← Array.foldl_toList] at h
  suffices H : ∀ (l : List NamePosition) (m : Std.HashMap Name NamePosition),
      (∀ n q, m[n]? = some q → q ∈ t.consts ∧ q.name = n) → (∀ q ∈ l, q ∈ t.consts) →
      ∀ n q, (l.foldl (fun (l : Std.HashMap Name NamePosition) q => l.insert q.name q) m)[n]? =
        some q → q ∈ t.consts ∧ q.name = n from
    H _ _ (by simp) (fun q hq => Array.mem_toList_iff.1 hq) n q h
  intro l
  induction l with
  | nil => intro m hm _; exact hm
  | cons x l ih =>
    intro m hm hl
    simp only [List.foldl_cons]
    refine ih _ (fun n q hq => ?_) (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    rw [Std.HashMap.getElem?_insert] at hq
    split at hq
    · rename_i he
      cases hq
      exact ⟨hl _ List.mem_cons_self, eq_of_beq he⟩
    · exact hm n q hq

/-! ## The parts -/

section
variable {sp : Roots} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

theorem CacheOk.insert_tables {c : ReachCache} (hc : CacheOk sp fs c) {k : PartKey}
    {t : NamePositions} (ht : PartNames sp fs k t) :
    CacheOk sp fs { c with tables := c.tables.insert k t } := by
  refine { hc with tables := fun k' t' h => ?_ }
  simp only [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i he; cases h; exact eq_of_beq he ▸ ht
  · exact hc.tables k' t' h

/-- **A part's name table** is the snapshot's. -/
theorem tableOf_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (k : PartKey) :
    ModelIO.AllOk (tableOf env c k) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ t, p.2 = .ok t → PartNames sp fs k t := by
  unfold tableOf
  split
  · rename_i t ht
    simp only [ModelIO.allOk_pure]
    exact ⟨hc, fun t' h => by cases h; exact hc.tables k t ht⟩
  · simp only []
    have jp : ∀ (x : Except CheckError NamePositions) {hs₁ hs₂ : HS},
        (readPartNames sp (k.mod, k.level) : ModelIO _) fs hs₁ (.ok x) hs₂ →
        CacheOk sp fs (match x with
          | .error _ => c | .ok t => { c with tables := c.tables.insert k t }) ∧
        ∀ t, x = .ok t → PartNames sp fs k t := by
      intro x _ _ hx
      cases x with
      | error e => exact ⟨hc, fun t h => by cases h⟩
      | ok t => exact ⟨hc.insert_tables ⟨_, _, hx⟩, fun t' h => by cases h; exact ⟨_, _, hx⟩⟩
    split
    · rename_i i hi
      split
      · rename_i hl
        split
        · rename_i t ht
          simp only [ModelIO.allOk_pure]
          refine ⟨hc, fun t' h => ?_⟩
          cases h
          have h1 := he.parts i t ht
          rw [he.index _ _ hi, eq_of_beq hl] at h1
          exact h1
        all_goals (simp only [ModelIO.allOk_bind]; intro x _ hx; rw [he.rd] at hx; obtain ⟨h1, h2⟩ := jp x hx; cases x <;> simp only [ModelIO.allOk_pure] <;> exact ⟨h1, h2⟩)
      all_goals (simp only [ModelIO.allOk_bind]; intro x _ hx; rw [he.rd] at hx; obtain ⟨h1, h2⟩ := jp x hx; cases x <;> simp only [ModelIO.allOk_pure] <;> exact ⟨h1, h2⟩)
    all_goals (simp only [ModelIO.allOk_bind]; intro x _ hx; rw [he.rd] at hx; obtain ⟨h1, h2⟩ := jp x hx; cases x <;> simp only [ModelIO.allOk_pure] <;> exact ⟨h1, h2⟩)


theorem CacheOk.insert_looks {c : ReachCache} (hc : CacheOk sp fs c) {k : PartKey}
    {t : NamePositions} (ht : PartNames sp fs k t) :
    CacheOk sp fs { c with looks := c.looks.insert k (lookTable t) } := by
  refine { hc with looks := fun k' l h => ?_ }
  simp only [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i he; cases h; exact ⟨t, eq_of_beq he ▸ ht, rfl⟩
  · exact hc.looks k' l h

/-- **A part's name lookup** is its snapshot table's. -/
theorem lookOf_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (k : PartKey) :
    ModelIO.AllOk (lookOf env c k) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ l, p.2 = .ok l → ∃ t, PartNames sp fs k t ∧ l = lookTable t := by
  unfold lookOf
  split
  · rename_i l hl
    simp only [ModelIO.allOk_pure]
    exact ⟨hc, fun l' h => by cases h; exact hc.looks k l hl⟩
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, h2⟩ := tableOf_ok he hc k x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e =>
      simp only [ModelIO.allOk_pure]
      exact ⟨h1, fun l h => by cases h⟩
    | ok t =>
      simp only [ModelIO.allOk_pure]
      exact ⟨h1.insert_looks (h2 t rfl), fun l h => by cases h; exact ⟨t, h2 t rfl, rfl⟩⟩

theorem CacheOk.insert_parts {c : ReachCache} (hc : CacheOk sp fs c) {k : PartKey} {r : Region}
    {st : SM} (hr : PartRegion sp fs k r) (hg : st.Good r) :
    CacheOk sp fs { c with parts := (c.parts.erase k).insert k (r, st) } := by
  refine { hc with parts := fun k' r' st' h => ?_ }
  by_cases hk : k = k'
  · subst hk
    simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hr, hg⟩
  · have hk' : (k == k') = false := by simpa using hk
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hk', Bool.false_eq_true,
      ↓reduceIte] at h
    exact hc.parts k' r' st' h

/-- **A read of a part with its memo**: where the read keeps the memo good and says `Q` of
what it reads, its value is read in the part's region on the snapshot. -/
theorem withPart_ok {α : Type} (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (k : PartKey) {f : Region → SM → Option (SM × α)} {Q : Region → α → Prop}
    (hf : ∀ r st st' a, st.Good r → f r st = some (st', a) → st'.Good r ∧ Q r a) :
    ModelIO.AllOk (withPart env c k f) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ a, p.2 = .ok a → ∃ r, PartRegion sp fs k r ∧ Q r a := by
  unfold withPart
  split
  · rename_i p hp
    obtain ⟨r, st⟩ := p
    obtain ⟨hr, hst⟩ := hc.parts k r st hp
    simp only [pure_bind]
    split
    · rename_i st' a hfa
      obtain ⟨hst', hq⟩ := hf r st st' a hst hfa
      simp only [ModelIO.allOk_pure]
      exact ⟨hc.insert_parts hr hst', fun a' h => by cases h; exact ⟨r, hr, hq⟩⟩
    · simp only [ModelIO.allOk_pure]
      exact ⟨hc.insert_parts hr (SM.good_empty r), fun a' h => by cases h⟩
  · simp only [ModelIO.allOk_bind]
    intro y _ hy
    rw [he.rd] at hy
    split
    · simp only [pure_bind, ModelIO.allOk_pure]
      exact ⟨hc, fun a h => by cases h⟩
    · rename_i fl
      split
      · rename_i r a' hra
        have hr : PartRegion sp fs k r := ⟨fl, a', ⟨_, _, hy⟩, hra⟩
        simp only [pure_bind]
        split
        · rename_i st' a hfa
          obtain ⟨hst', hq⟩ := hf r {} st' a (SM.good_empty r) hfa
          simp only [ModelIO.allOk_pure]
          exact ⟨hc.insert_parts hr hst', fun a' h => by cases h; exact ⟨r, hr, hq⟩⟩
        · simp only [ModelIO.allOk_pure]
          exact ⟨hc.insert_parts hr (SM.good_empty r), fun a' h => by cases h⟩
      · simp only [pure_bind, ModelIO.allOk_pure]
        exact ⟨hc, fun a h => by cases h⟩

/-- `stmtWith`'s read is the skeleton's statement and kind, and keeps the memo good. -/
theorem stmtWith_skel {r : Region} {st st' : SM} {c : Nat} {cv : ConstantVal}
    {k : CKindF Name Unit} (hG : st.Good r) (h : stmtWith r st c = some (st', cv, k)) :
    st'.Good r ∧ StmtSkel r c cv k := by
  simp only [stmtWith] at h
  obtain ⟨sk, hsk, h⟩ := bind_some_left h
  have hG' : (memoAdd r kExpr ((sk.name :: sk.levelParams).foldl (memoAdd r kName) st)
      sk.type).Good r :=
    memoAdd_good isKind_expr (foldl_memoAdd_good isKind_name _ _ hG) _
  rw [memoName_eq hG', memoExpr_eq hG'] at h
  obtain ⟨n, hn, h⟩ := bind_some_left h
  obtain ⟨lps, hl, h⟩ := bind_some_left h
  obtain ⟨ty, ht, h⟩ := bind_some_left h
  obtain ⟨k', hk, h⟩ := bind_some_left h
  cases h
  exact ⟨hG', sk, hsk, hn, hl, ht, hk⟩

/-- **A copy's statement and kind** are its skeleton's on the snapshot. -/
theorem stmtAt_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (s : Spot) :
    ModelIO.AllOk (stmtAt env c s) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ cv k, p.2 = .ok (cv, k) →
        ∃ r, PartRegion sp fs s.part r ∧ StmtSkel r s.pos.loc cv k := by
  unfold stmtAt
  intro p _ hp
  obtain ⟨h1, h2⟩ := withPart_ok (Q := fun r (x : ConstantVal × CKindF Name Unit) =>
    StmtSkel r s.pos.loc x.1 x.2) he hc s.part
    (fun r st st' a hG hf => by
      obtain ⟨cv, k⟩ := a
      exact stmtWith_skel hG hf) p _ hp
  exact ⟨h1, fun cv k h => h2 (cv, k) h⟩

/-- **A copy in its module's private part**: of its part's module and name, at the private
level, and a copy where the given one is. -/
theorem privSpot_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (s : Spot) :
    ModelIO.AllOk (privSpot env c s) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ q, p.2 = .ok q →
        q.part = ⟨s.part.mod, .private⟩ ∧ q.pos.name = s.pos.name ∧
        (CopyAt sp fs s → CopyAt sp fs q) ∧ (s.part.level = .private → q = s) := by
  unfold privSpot
  split
  · rename_i hl
    simp only [ModelIO.allOk_pure]
    refine ⟨hc, fun q h => ?_⟩
    cases h
    have hl' : s.part.level = .private := eq_of_beq hl
    refine ⟨?_, rfl, id, fun _ => rfl⟩
    rw [← hl']
  · rename_i hl
    simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, h2⟩ := lookOf_ok he hc ⟨s.part.mod, .private⟩ x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e =>
      simp only [ModelIO.allOk_pure]
      exact ⟨h1, fun q h => by cases h⟩
    | ok l =>
      obtain ⟨t, ht, rfl⟩ := h2 _ rfl
      simp only []
      split
      · rename_i q hq
        simp only [ModelIO.allOk_pure]
        obtain ⟨hqm, hqn⟩ := lookTable_spec t hq
        refine ⟨h1, fun q' h => ?_⟩
        cases h
        refine ⟨rfl, hqn, fun _ => ⟨t, ht, hqm⟩, fun h => ?_⟩
        simp [h] at hl
      · simp only [ModelIO.allOk_pure]
        exact ⟨h1, fun q h => by cases h⟩

/-! ## A home's view, and a search in it -/

theorem CacheOk.insert_views {c : ReachCache} (hc : CacheOk sp fs c) {h : Name}
    {v : Std.HashMap Name Spot} (hv : ∀ (y : Name) (s : Spot), v[y]? = some s → CopyAt sp fs s) :
    CacheOk sp fs { c with views := c.views.insert h v } := by
  refine { hc with views := fun h' v' hh y s hs => ?_ }
  simp only [Std.HashMap.getElem?_insert] at hh
  split at hh
  · cases hh; exact hv y s hs
  · exact hc.views h' v' hh y s hs

theorem viewAdd_fold (k : PartKey) (t : NamePositions) :
    ∀ (l : List NamePosition) (v : Std.HashMap Name Spot),
      (∀ (y : Name) (s : Spot), v[y]? = some s → CopyAt sp fs s) → PartNames sp fs k t → (∀ q ∈ l, q ∈ t.consts) →
      ∀ (y : Name) (s : Spot), (l.foldl (fun (v : Std.HashMap Name Spot) q =>
        if v.contains q.name then v else v.insert q.name ⟨k, q⟩) v)[y]? = some s → CopyAt sp fs s
  | [], v, hv, _, _ => hv
  | q :: l, v, hv, ht, hl => by
    simp only [List.foldl_cons]
    refine viewAdd_fold k t l _ ?_ ht (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq'))
    split
    · exact hv
    · intro y s hs
      rw [Std.HashMap.getElem?_insert] at hs
      split at hs
      · cases hs; exact ⟨t, ht, hl q List.mem_cons_self⟩
      · exact hv y s hs

theorem viewAdd_ok (he : EnvOk sp fs env) :
    ∀ (c : ReachCache) (v : Std.HashMap Name Spot) (ks : List PartKey), CacheOk sp fs c →
      (∀ (y : Name) (s : Spot), v[y]? = some s → CopyAt sp fs s) → ∀ {hs₀ : HS},
      ModelIO.AllOk (viewAdd env c v ks) fs hs₀ fun p =>
        CacheOk sp fs p.1 ∧ ∀ v', p.2 = .ok v' → ∀ (y : Name) (s : Spot), v'[y]? = some s → CopyAt sp fs s
  | c, v, [], hc, hv => by
    simp only [viewAdd, ModelIO.allOk_pure]
    exact ⟨hc, fun v' h => by cases h; exact hv⟩
  | c, v, k :: ks, hc, hv => by
    simp only [viewAdd, ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, h2⟩ := tableOf_ok he hc k x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e =>
      simp only [ModelIO.allOk_pure]
      exact ⟨h1, fun v' h => by cases h⟩
    | ok t =>
      simp only []
      refine viewAdd_ok he c' _ ks h1 ?_
      rw [viewStep, ← Array.foldl_toList]
      exact viewAdd_fold k t _ v hv (h2 t rfl) (fun q hq => Array.mem_toList_iff.1 hq)

theorem viewOf_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (h : Name) :
    ModelIO.AllOk (viewOf env c h) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ v, p.2 = .ok v → ∀ (y : Name) (s : Spot), v[y]? = some s → CopyAt sp fs s := by
  unfold viewOf
  split
  · rename_i v hv
    simp only [ModelIO.allOk_pure]
    exact ⟨hc, fun v' h' => by cases h'; exact hc.views h v hv⟩
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, -⟩ := tableOf_ok he hc _ x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e =>
      simp only [ModelIO.allOk_pure]
      exact ⟨h1, fun v' h => by cases h⟩
    | ok t =>
      simp only [ModelIO.allOk_bind]
      intro y _ _
      cases y with
      | error e =>
        simp only [ModelIO.allOk_pure]
        exact ⟨h1, fun v' h => by cases h⟩
      | ok ld =>
        simp only [ModelIO.allOk_bind]
        intro z _ hz
        obtain ⟨h3, h4⟩ := viewAdd_ok he c' {} _ h1 (by simp) z _ hz
        obtain ⟨c'', r⟩ := z
        cases r with
        | error e =>
          simp only [ModelIO.allOk_pure]
          exact ⟨h3, fun v' h => by cases h⟩
        | ok v =>
          simp only [ModelIO.allOk_pure]
          exact ⟨h3.insert_views (h4 v rfl), fun v' h => by cases h; exact h4 v rfl⟩

theorem locate_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (h y : Name) :
    ModelIO.AllOk (locate env c h y) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ s, p.2 = .ok (some s) → CopyAt sp fs s := by
  unfold locate
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h1, h2⟩ := viewOf_ok he hc h x _ hx
  obtain ⟨c', r⟩ := x
  cases r with
  | error e =>
    simp only [ModelIO.allOk_pure]
    exact ⟨h1, fun s h => by cases h⟩
  | ok v =>
    simp only [ModelIO.allOk_pure]
    exact ⟨h1.searches _, fun s h => h2 v rfl y s (Except.ok.inj h)⟩


/-! ## Keys, the clash rule's and the capture check's: the caches stay the snapshot's -/

theorem proofStatus_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (s : Spot)
    (k : CKindF Name Unit) :
    ModelIO.AllOk (proofStatus env c s k) fs ho fun p => CacheOk sp fs p.1 := by
  unfold proofStatus
  split
  · simpa using hc
  · simpa using hc
  · simpa using hc
  · split
    · simpa using hc
    · simp only [ModelIO.allOk_bind]
      intro x _ hx
      obtain ⟨h1, -⟩ := privSpot_ok he hc s x _ hx
      obtain ⟨c', r⟩ := x
      cases r <;> simpa using h1
  · simpa using hc

theorem agreeCheck_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (h y : Name)
    (s₁ s₂ : Spot) :
    ModelIO.AllOk (agreeCheck env c h y s₁ s₂) fs ho fun p => CacheOk sp fs p.1 := by
  unfold agreeCheck
  split
  · simpa using hc
  split
  · simpa using hc
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h1, -⟩ := stmtAt_ok he hc s₁ x _ hx
  obtain ⟨c₁, r₁⟩ := x
  cases r₁ with
  | error e => simpa using h1
  | ok p₁ =>
  obtain ⟨cv₁, k₁⟩ := p₁
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h2, -⟩ := stmtAt_ok he h1 s₂ x _ hx
  obtain ⟨c₂, r₂⟩ := x
  cases r₂ with
  | error e => simpa using h2
  | ok p₂ =>
  obtain ⟨cv₂, k₂⟩ := p₂
  simp only []
  split
  · simpa using h2
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  have h3 := proofStatus_ok he h2 s₁ k₁ x _ hx
  obtain ⟨c₃, r₃⟩ := x
  cases r₃ with
  | error e => simpa using h3
  | ok q₁ =>
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  have h4 := proofStatus_ok he h3 s₂ k₂ x _ hx
  obtain ⟨c₄, r₄⟩ := x
  cases r₄ with
  | error e => simpa using h4
  | ok q₂ =>
  simp only []
  split
  · simpa using h4
  · split
    · simpa using h4.partners _
    · simpa using (h4.partners _).pending _

theorem statuses_ok (he : EnvOk sp fs env) :
    ∀ (c : ReachCache) (xs : List (Spot × ConstantVal × CKindF Name Unit)) (acc : List ProofStatus),
      CacheOk sp fs c → ∀ {hs₀ : HS},
        ModelIO.AllOk (clashAgree.statuses env c xs acc) fs hs₀ fun p => CacheOk sp fs p.1
  | c, [], acc, hc => by simpa [clashAgree.statuses] using hc
  | c, (s, _, k) :: rest, acc, hc => by
    simp only [clashAgree.statuses, ModelIO.allOk_bind]
    intro x _ hx
    have h1 := proofStatus_ok he hc s k x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok p => exact statuses_ok he c' rest _ h1

theorem clashAgree_ok (he : EnvOk sp fs env) :
    ∀ (c : ReachCache) (cls : List Clash) (acc : Array Name), CacheOk sp fs c → ∀ {hs₀ : HS},
      ModelIO.AllOk (clashAgree env c cls acc) fs hs₀ fun p => CacheOk sp fs p.1
  | c, [], acc, hc => by simpa [clashAgree] using hc
  | c, cl :: cls, acc, hc => by
    simp only [clashAgree, ModelIO.allOk_bind]
    intro x _ hx
    have h1 := statuses_ok he c _ [] hc x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok ps =>
      simp only []
      split
      · simpa using h1
      · split
        · exact clashAgree_ok he _ cls _ h1
        · split
          · exact clashAgree_ok he _ cls _ (h1.pending _)
          · exact clashAgree_ok he _ cls _ h1

theorem inExported_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (m : Name)
    (level : OLeanLevel) (y : Name) :
    ModelIO.AllOk (inExported env c m level y) fs ho fun p => CacheOk sp fs p.1 := by
  unfold inExported
  split
  · simpa using hc
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, -⟩ := lookOf_ok he hc _ x _ hx
    obtain ⟨c', r⟩ := x
    cases r <;> simpa using h1


theorem CacheOk.insert_located {c : ReachCache} (hc : CacheOk sp fs c) {y : Name} {s : Spot}
    (hl : s.part.level = .private) (hs : CopyAt sp fs s) (x : Array (Name × Name)) :
    CacheOk sp fs { c with located := c.located.insert y s, completed := x } := by
  refine ⟨hc.tables, hc.looks, hc.parts, hc.recBlocks, hc.views, fun y' s' h => ?_⟩
  simp only [Std.HashMap.getElem?_insert] at h
  split at h
  · cases h; exact ⟨hl, hs⟩
  · exact hc.located y' s' h

theorem locate_agreeCheck_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (h y : Name) (s₁ : Spot) :
    ModelIO.AllOk (do
      match ← locate env c h y with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok none) => pure (c, .error (.invalid s!"module {h} reads {y}, which its view \
          does not hold"))
      | (c, .ok (some s₂)) => agreeCheck env c h y s₁ s₂ : ModelIO _) fs ho
      fun p => CacheOk sp fs p.1 := by
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h1, -⟩ := locate_ok he hc h y x _ hx
  obtain ⟨c', r⟩ := x
  cases r with
  | error e => simpa using h1
  | ok o =>
    cases o with
    | none => simpa using h1
    | some s₂ => exact agreeCheck_ok he h1 h y s₁ s₂

theorem captureOne_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (h y : Name) :
    ModelIO.AllOk (captureOne env c h y) fs ho fun p => CacheOk sp fs p.1 := by
  unfold captureOne
  split
  · simpa using hc
  split
  · rename_i i s₁ _
    split
    · simpa using hc
    have tail : ∀ (x : ReachCache × Except CheckError Bool) {hs₀ : HS}, CacheOk sp fs x.1 →
        ModelIO.AllOk (match x with
          | (c, Except.error e) => pure (c, Except.error e)
          | (c, Except.ok true) => pure (c, Except.ok ())
          | (c, Except.ok false) => do
            let __do_lift ← locate env c h y
            match __do_lift with
              | (c, Except.error e) => pure (c, Except.error e)
              | (c, Except.ok none) =>
                pure (c, Except.error (CheckError.invalid
                  (toString "module " ++ toString h ++ toString " reads " ++ toString y ++
                    toString ", which its view does not hold")))
              | (c, Except.ok (some s₂)) => agreeCheck env c h y s₁ s₂ : ModelIO _) fs hs₀
          fun p => CacheOk sp fs p.1 := by
      intro x _ h1
      obtain ⟨c', r⟩ := x
      cases r with
      | error e => simpa using h1
      | ok b =>
        cases b with
        | true => simpa using h1
        | false => exact locate_agreeCheck_ok he h1 h y s₁
    simp only []
    split <;> split
    all_goals
      simp only [ModelIO.allOk_bind]
      intro x _ hx
      first
        | exact tail x (inExported_ok he hc _ _ y x _ hx)
        | (simp only [ModelIO.pure_iff, Except.ok.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx; exact tail (c, .ok false) hc)
  · split
    · split
      · simpa using hc
      · exact locate_agreeCheck_ok he hc h y _
    · simp only [ModelIO.allOk_bind]
      intro x _ hx
      obtain ⟨h1, h2⟩ := locate_ok he hc h y x _ hx
      obtain ⟨c', r⟩ := x
      cases r with
      | error e => simpa using h1
      | ok o =>
        cases o with
        | none => simpa using h1
        | some s =>
          simp only [ModelIO.allOk_bind]
          intro z _ hz
          obtain ⟨h3, h4⟩ := privSpot_ok he h1 s z _ hz
          obtain ⟨c'', r⟩ := z
          cases r with
          | error e => simpa using h3
          | ok q =>
            obtain ⟨hq1, -, hq3, -⟩ := h4 q rfl
            simp only [ModelIO.allOk_pure]
            exact h3.insert_located (by rw [hq1]) (hq3 (h2 s rfl)) _

theorem captureAll_ok (he : EnvOk sp fs env) (h : Name) :
    ∀ (c : ReachCache) (ys : List Name), CacheOk sp fs c → ∀ {hs₀ : HS},
      ModelIO.AllOk (captureAll env h c ys) fs hs₀ fun p => CacheOk sp fs p.1
  | c, [], hc => by simpa [captureAll] using hc
  | c, y :: ys, hc => by
    simp only [captureAll, ModelIO.allOk_bind]
    intro x _ hx
    have h1 := captureOne_ok he hc h y x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok u => exact captureAll_ok he h c' ys h1

theorem capturePairs_ok (he : EnvOk sp fs env) :
    ∀ (c : ReachCache) (ps : List (Name × Name)), CacheOk sp fs c → ∀ {hs₀ : HS},
      ModelIO.AllOk (capturePairs env c ps) fs hs₀ fun p => CacheOk sp fs p.1
  | c, [], hc => by simpa [capturePairs] using hc
  | c, (h, y) :: ps, hc => by
    simp only [capturePairs, ModelIO.allOk_bind]
    intro x _ hx
    have h1 := captureOne_ok he hc h y x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok u => exact capturePairs_ok he c' ps h1


theorem CacheOk.insert_located' {c : ReachCache} (hc : CacheOk sp fs c) {y : Name} {s : Spot}
    (hl : s.part.level = .private) (hs : CopyAt sp fs s) :
    CacheOk sp fs { c with located := c.located.insert y s } :=
  hc.insert_located hl hs c.completed

theorem storedNamesOk_ok (he : EnvOk sp fs env) (h : Name) :
    ∀ (c : ReachCache) (ns : List Name), CacheOk sp fs c → ∀ {hs₀ : HS},
      ModelIO.AllOk (storedNamesOk env c h ns) fs hs₀ fun p => CacheOk sp fs p.1
  | c, [], hc => by simpa [storedNamesOk] using hc
  | c, n :: ns, hc => by
    unfold storedNamesOk
    split
    · split
      · exact storedNamesOk_ok he h c ns hc
      · simpa using hc
    · split
      · split
        · exact storedNamesOk_ok he h c ns hc
        · simpa using hc
      · simp only [ModelIO.allOk_bind]
        intro x _ hx
        obtain ⟨h1, h2⟩ := lookOf_ok he hc _ x _ hx
        obtain ⟨c', r⟩ := x
        cases r with
        | error e => simpa using h1
        | ok l =>
          obtain ⟨t, ht, hl⟩ := h2 l rfl
          simp only []
          split
          · rename_i q hq
            have hq' : (lookTable t)[n]? = some q := hl ▸ hq
            have hc' : CacheOk sp fs { c' with located := c'.located.insert n ⟨⟨h, .private⟩, q⟩ } :=
              h1.insert_located' rfl ⟨t, ht, (lookTable_spec t hq').1⟩
            exact storedNamesOk_ok he h _ ns hc'
          · simpa using h1

/-! ## A record read -/

theorem entriesWith_spec {r : Region} :
    ∀ {st st' : SM} {ls : List Nat} {es : List (CEntryF Name Expr)}, st.Good r →
      entriesWith r st ls = some (st', es) → st'.Good r ∧ ls.mapM (entryAt r) = some es
  | st, st', [], es, hG, h => by
    simp only [entriesWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hG, rfl⟩
  | st, st', l :: ls, es, hG, h => by
    simp only [entriesWith] at h
    obtain ⟨⟨st₁, e⟩, h1, h⟩ := bind_some_left h
    obtain ⟨⟨st₂, es'⟩, h2, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨g1, e1⟩ := entryWith_spec hG h1
    obtain ⟨g2, e2⟩ := entriesWith_spec g1 h2
    refine ⟨g2, ?_⟩
    simp only [List.mapM_cons, e1, e2]
    rfl

theorem CacheOk.insert_recBlocks {c : ReachCache} (hc : CacheOk sp fs c) {k : PartKey}
    {m : Std.HashMap Name (Array Nat)} {t : NamePositions} {r : Region}
    (ht : PartNames sp fs k t) (hr : PartRegion sp fs k r) (hm : recBlocksAt r t = some m) :
    CacheOk sp fs { c with recBlocks := c.recBlocks.insert k m } := by
  refine { hc with recBlocks := fun k' m' h => ?_ }
  simp only [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i he; cases h; exact eq_of_beq he ▸ ⟨t, r, ht, hr, hm⟩
  · exact hc.recBlocks k' m' h

theorem recBlocksOf_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (k : PartKey) :
    ModelIO.AllOk (recBlocksOf env c k) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ m, p.2 = .ok m →
        ∃ t r, PartNames sp fs k t ∧ PartRegion sp fs k r ∧ recBlocksAt r t = some m := by
  unfold recBlocksOf
  split
  · rename_i m hm
    simp only [ModelIO.allOk_pure]
    exact ⟨hc, fun m' h => by cases h; exact hc.recBlocks k m hm⟩
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, h2⟩ := tableOf_ok he hc k x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok t =>
      simp only [ModelIO.allOk_bind]
      intro z _ hz
      obtain ⟨h3, h4⟩ := withPart_ok (Q := fun r m => recBlocksAt r t = some m) he h1 k
        (fun r st st' a hG hf => by
          cases hm : recBlocksAt r t with
          | none => simp [hm] at hf
          | some m =>
            simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            exact ⟨hG, rfl⟩) z _ hz
      obtain ⟨c'', r⟩ := z
      cases r with
      | error e => simpa using h3
      | ok m =>
        obtain ⟨r, hr, hm⟩ := h4 m rfl
        simp only [ModelIO.allOk_pure]
        exact ⟨h3.insert_recBlocks (h2 t rfl) hr hm, fun m' h => by
          cases h; exact ⟨t, r, h2 t rfl, hr, hm⟩⟩


/-- `withPart` of `entryWith`: the constant at the location, in the part's region. -/
theorem withPart_entry (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (k : PartKey) (l : Nat) :
    ModelIO.AllOk (withPart env c k fun r st => entryWith r st l) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ e, p.2 = .ok e → ∃ r, PartRegion sp fs k r ∧ entryAt r l = some e :=
  withPart_ok (Q := fun r e => entryAt r l = some e) he hc k
    (fun _ _ _ _ hG hf => entryWith_spec hG hf)

/-- `withPart` of `entriesWith`: the constants at the locations, in the part's region. -/
theorem withPart_entries (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (k : PartKey) (ls : List Nat) :
    ModelIO.AllOk (withPart env c k fun r st => entriesWith r st ls) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ es, p.2 = .ok es →
        ∃ r, PartRegion sp fs k r ∧ ls.mapM (entryAt r) = some es :=
  withPart_ok (Q := fun r es => ls.mapM (entryAt r) = some es) he hc k
    (fun _ _ _ _ hG hf => entriesWith_spec hG hf)

/-- **A part's region and table off one read** keep the caches the snapshot's: the region is
the files' view region, the table the names the search path's read gives off the same files. -/
theorem loadPart_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (k : PartKey) :
    ModelIO.AllOk (loadPart env c k) fs ho fun p => CacheOk sp fs p.1 := by
  unfold loadPart
  split
  · simpa using hc
  simp only [ModelIO.allOk_bind]
  intro y _ hy
  rw [he.rd] at hy
  rcases y with e | fl
  · simpa using hc
  simp only []
  split
  · simpa using hc
  rename_i r a hra
  have hr : PartRegion sp fs k r := ⟨fl, a, ⟨_, _, hy⟩, hra⟩
  have hc' : CacheOk sp fs { c with parts := c.parts.insert k (r, {}) } := by
    refine { hc with parts := fun k' r' st' h => ?_ }
    simp only [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨eq_of_beq hk ▸ hr, SM.good_empty r⟩
    · exact hc.parts k' r' st' h
  split
  · simpa using hc'
  split
  · rename_i t ht
    simp only [ModelIO.allOk_pure]
    refine hc'.insert_tables ?_
    have hn := readPartNames_of_files (⟨_, _, hy⟩ : ModelIO.CanGive (readFiles sp k.mod k.level) fs (.ok fl))
    simp only [namesOf, readNamePositions, hra, Option.bind_eq_bind, Option.bind_some, ht] at hn
    exact hn
  · simpa using hc'

/-- **A group read from a part** is `GroupRead`. -/
theorem groupAt_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (k : PartKey)
    (n : Name) :
    ModelIO.AllOk (groupAt env c k n) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ d, p.2 = .ok (some d) → GroupRead sp fs k n d := by
  unfold groupAt
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  have h0 := loadPart_ok he hc k x _ hx
  obtain ⟨c₀, r⟩ := x
  cases r with
  | error e => simpa using h0
  | ok u =>
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h1, h2⟩ := lookOf_ok he h0 k x _ hx
  obtain ⟨c₁, r⟩ := x
  cases r with
  | error e => simpa using h1
  | ok look =>
  obtain ⟨t, ht, rfl⟩ := h2 _ rfl
  simp only []
  split
  · simpa using h1
  rename_i q hq
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h3, h4⟩ := withPart_entry he h1 k q.loc x _ hx
  obtain ⟨c₂, r⟩ := x
  cases r with
  | error e => simpa using h3
  | ok tE =>
  obtain ⟨r₁, hr₁, htE⟩ := h4 tE rfl
  simp only []
  split
  · rename_i np ni all cs nn ir iu irf hk
    split
    · simpa using h3
    rename_i mqs hmqs
    simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h5, h6⟩ := withPart_entries he h3 k _ x _ hx
    obtain ⟨c₃, r⟩ := x
    cases r with
    | error e => simpa using h5
    | ok tys =>
    obtain ⟨r₂, hr₂, htys⟩ := h6 tys rfl
    simp only []
    split
    · simpa using h5
    rename_i cqs hcqs
    simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h7, h8⟩ := recBlocksOf_ok he h5 k x _ hx
    obtain ⟨c₄, r⟩ := x
    cases r with
    | error e => simpa using h7
    | ok rb =>
    obtain ⟨t', r₃, ht', hr₃, hrb⟩ := h8 rb rfl
    simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h9, h10⟩ := withPart_entries he h7 k _ x _ hx
    obtain ⟨c₅, r⟩ := x
    cases r with
    | error e => simpa using h9
    | ok rest =>
    obtain ⟨r₄, hr₄, hrest⟩ := h10 rest rfl
    simp only []
    split
    · rename_i d hd
      simp only [ModelIO.allOk_pure]
      refine ⟨h9, fun d' h => ?_⟩
      cases h
      exact ⟨t, q, tE, np, ni, nn, all, cs, ir, iu, irf, mqs, cqs, tys, rest, t', rb, r₁, r₂, r₃, r₄,
        ht, hq, hr₁, htE, hk, hmqs, hr₂, htys, hcqs, ht', hr₃, hrb, hr₄, hrest, hd⟩
    · simpa using h9
  · simpa using h3


theorem stmtRecord_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (s : Spot)
    (cv : ConstantVal) (hs : CopyAt sp fs s) :
    ModelIO.AllOk (stmtRecord env c s cv) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ d h, p.2 = .ok (d, h) → d = .axiomDecl cv ∧ h = s.part.mod ∧
        (reduceOpNames.contains cv.name = true → ∃ q : Spot, CopyAt sp fs q ∧
          q.part = ⟨s.part.mod, .private⟩ ∧ q.pos.name = s.pos.name ∧
          (q.pos.tag = 0 ∨ q.pos.tag = 3)) := by
  unfold stmtRecord
  split
  · rename_i hn
    simp only [ModelIO.allOk_pure]
    refine ⟨hc, fun d h e => ?_⟩
    cases e
    exact ⟨rfl, rfl, fun hr => absurd (by simpa using hr) (by simpa using hn)⟩
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, h2⟩ := privSpot_ok he hc s x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok q =>
      obtain ⟨hq1, hq2, hq3, -⟩ := h2 q rfl
      simp only []
      split
      · rename_i htag
        simp only [ModelIO.allOk_pure]
        refine ⟨h1, fun d h e => ?_⟩
        cases e
        refine ⟨rfl, rfl, fun _ => ⟨q, hq3 hs, hq1, hq2, ?_⟩⟩
        simpa using htag
      · simpa using h1

theorem importerSpot_copy (he : EnvOk sp fs env) {x : Name} {i : Nat} {s : Spot}
    (h : importerSpot env x = some (i, s)) : CopyAt sp fs s ∧ s.part.level ≠ .server := by
  unfold importerSpot at h
  obtain ⟨cp, hcp, h⟩ := bind_some_left h
  obtain ⟨q, hq, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [NameIndex.at] at hq
  obtain ⟨t, ht, hq⟩ := bind_some_left hq
  refine ⟨⟨t, he.parts _ t ht, Array.mem_of_getElem? hq⟩, ?_⟩
  simp only [LoadFlags.level]
  split <;> simp

/-- **A record read** is `RecordFrom`, and the caches stay the snapshot's. -/
theorem readRecord_ok (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (x : Name) :
    ModelIO.AllOk (readRecord env c x) fs ho fun p =>
      CacheOk sp fs p.1 ∧ ∀ d h, p.2 = .ok (d, h) → RecordFrom sp fs d h := by
  unfold readRecord
  split
  rotate_left
  · simpa using hc
  rename_i s completed hsc
  have hcopy : CopyAt sp fs s ∧ s.part.level ≠ .server ∧
      (completed = true → s.part.level = .private) := by
    split at hsc
    · rename_i i s' hi
      cases hsc
      obtain ⟨a, b⟩ := importerSpot_copy he hi
      exact ⟨a, b, by simp⟩
    · cases hl : c.located[x]? with
      | none => simp [hl] at hsc
      | some s' =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsc
        obtain ⟨rfl, rfl⟩ := hsc
        obtain ⟨a, b⟩ := hc.located x _ hl
        exact ⟨b, by simp [a], fun _ => a⟩
  obtain ⟨hs, hls, hcomp⟩ := hcopy
  simp only []
  split
  · simpa using hc
  rename_i hskip
  have hsk : s.pos.skipped = false := by simpa using hskip
  simp only [ModelIO.allOk_bind]
  intro z _ hz
  obtain ⟨h1, h2⟩ := stmtAt_ok he hc s z _ hz
  obtain ⟨c₁, r⟩ := z
  cases r with
  | error e => simpa using h1
  | ok p =>
  obtain ⟨cv, k⟩ := p
  obtain ⟨r, hr, hst⟩ := h2 cv k rfl
  simp only []
  split
  · rename_i n hn
    simp only [ModelIO.allOk_bind]
    intro z _ hz
    obtain ⟨h3, h4⟩ := groupAt_ok he h1 _ n z _ hz
    obtain ⟨c₂, r⟩ := z
    cases r with
    | error e => simpa using h3
    | ok o =>
      cases o with
      | none => simpa using h3
      | some d =>
        simp only [ModelIO.allOk_pure]
        refine ⟨h3, fun d' h' e => ?_⟩
        cases e
        exact .group (h4 d rfl)
  · rename_i hn
    have stmtCase : k.tag ≠ 4 → (k.tag = 1 → s.part.level = .private) →
        ∀ {hs₁ : HS}, ModelIO.AllOk (stmtRecord env c₁ s cv) fs hs₁ fun p =>
          CacheOk sp fs p.1 ∧ ∀ d h, p.2 = .ok (d, h) → RecordFrom sp fs d h := by
      intro hq hd _ p _ hp
      obtain ⟨h5, h6⟩ := stmtRecord_ok he h1 s cv hs p _ hp
      refine ⟨h5, fun d h e => ?_⟩
      obtain ⟨rfl, rfl, hred⟩ := h6 d h e
      exact .stmt hs hls hr hst hsk hn hq hd hred
    split
    · rename_i v hints safety
      split
      · rename_i hcomp'
        exact stmtCase (by simp [CKindF.tag]) (fun _ => hcomp hcomp')
      · simp only [ModelIO.allOk_bind]
        intro z _ hz
        obtain ⟨h5, h6⟩ := withPart_entry he h1 s.part s.pos.loc z _ hz
        obtain ⟨c₂, r⟩ := z
        cases r with
        | error e => simpa using h5
        | ok e =>
          obtain ⟨r', hr', he'⟩ := h6 e rfl
          simp only []
          split
          · rename_i d hd
            simp only [ModelIO.allOk_pure]
            refine ⟨h5, fun d' h' eq => ?_⟩
            cases eq
            exact .entry hs hls hr' he' hr hst rfl hsk hd
          · simpa using h5
    · rename_i q
      split
      · rename_i d hd
        simp only [ModelIO.allOk_pure]
        refine ⟨h1, fun d' h' eq => ?_⟩
        cases eq
        exact .quot hs hls hr hst hd
      · simpa using h1
    · rename_i hnd hnq
      refine stmtCase ?_ ?_
      · intro h4; cases k <;> simp_all [CKindF.tag]
      · intro h4; cases k <;> simp_all [CKindF.tag]


/-! ## The worklist -/

/-- **Every record of the worklist so far, read from its home**. -/
@[expose] def FromInv (sp : Roots) (fs : FS) (L : ReachLog) : Prop :=
  L.ctx.size = L.homes.size ∧
    ∀ (i : Nat) (d : Declaration) (h : Name), L.ctx[i]? = some d → L.homes[i]? = some h →
      RecordFrom sp fs d h

theorem FromInv.add {L : ReachLog} (hL : FromInv sp fs L) {d : Declaration} {h : Name}
    (hd : RecordFrom sp fs d h) (rd rest : List Name) : FromInv sp fs (L.add d h rd rest) := by
  obtain ⟨hsz, hi⟩ := hL
  simp only [ReachLog.add]
  refine ⟨by simp [hsz], fun i d' h' h1 h2 => ?_⟩
  rw [Array.getElem?_push] at h1 h2
  by_cases hi' : i = L.ctx.size
  · subst hi'
    simp only [↓reduceIte, Option.some.injEq] at h1
    rw [hsz] at h2
    simp only [↓reduceIte, Option.some.injEq] at h2
    subst h1; subst h2; exact hd
  · have hi'' : i ≠ L.homes.size := hsz ▸ hi'
    simp only [hi', hi'', ↓reduceIte] at h1 h2
    exact hi i d' h' h1 h2

/-- **The worklist reads every record from its home**, keeping the caches the snapshot's. -/
theorem reachGo_from (he : EnvOk sp fs env) :
    ∀ (fuel : Nat) (L : ReachLog) (c : ReachCache), CacheOk sp fs c → FromInv sp fs L →
      ∀ {hs₀ : HS}, ModelIO.AllOk (reachGo env fuel L c) fs hs₀ fun r =>
        ∀ L' c', r = .ok (L', c') → FromInv sp fs L' := by
  intro fuel
  induction fuel with
  | zero =>
    intro L c hc hL _
    rw [reachGo]
    split
    · split
      · simp only [ModelIO.allOk_pure]
        intro L' c' h; cases h; exact hL
      · simp
    · simp
  | succ fuel ih =>
    intro L c hc hL _
    rw [reachGo]
    split
    · split
      · simp only [ModelIO.allOk_pure]
        intro L' c' h; cases h; exact hL
      · simp only [ModelIO.allOk_bind]
        intro z _ hz
        have h1 := capturePairs_ok he _ _ (hc.partners #[]) z _ hz
        obtain ⟨c₁, r⟩ := z
        cases r with
        | error e => simp
        | ok u => apply ih _ c₁ h1; exact hL
    · rename_i x rest hs
      simp only []
      split
      · apply ih _ c hc; exact ⟨hL.1, hL.2⟩
      · simp only [ModelIO.allOk_bind]
        intro z _ hz
        obtain ⟨h1, h2⟩ := readRecord_ok he hc x z _ hz
        obtain ⟨c₁, r⟩ := z
        cases r with
        | error e => simp
        | ok p =>
          obtain ⟨d, h⟩ := p
          have hd := h2 d h rfl
          simp only []
          split
          · simp
          · split
            · simp
            · simp only [ModelIO.allOk_bind]
              intro z _ hz
              have h3 := captureAll_ok he h c₁ _ h1 z _ hz
              obtain ⟨c₂, r⟩ := z
              cases r with
              | error e => simp
              | ok u =>
                simp only [ModelIO.allOk_bind]
                intro z _ hz
                have h4 := storedNamesOk_ok he h c₂ _ h3 z _ hz
                obtain ⟨c₃, r⟩ := z
                cases r with
                | error e => simp
                | ok u => exact ih _ _ (h4.partners _) (hL.add hd _ _)

/-- **What the reach read, from where**: at every accepting outcome of `reach` on the search
path's reads, from a name index whose parts are the snapshot's tables, every context record
is read from its home (`RecordFrom`). -/
theorem reach_from {sp : Roots} {fs : FS} {m : Name} {wr : WorkerReads}
    {own : Std.HashSet Name} {roots : Array Name} {r : Reach}
    (hparts : ∀ i t, wr.index.parts[i]? = some t →
      PartNames sp fs ⟨wr.loads.nameAt i, ((wr.loads.flags[i]?).getD default).level⟩ t)
    (hindex : ∀ m i, wr.loads.index[m]? = some i → wr.loads.nameAt i = m)
    {hs hs' : HS} (h : (reach (.ofPath sp) m wr own roots : ModelIO _) fs hs (.ok (.ok r)) hs') :
    r.ctx.size = r.homes.size ∧
      ∀ (i : Nat) (d : Declaration) (hm : Name), r.ctx[i]? = some d → r.homes[i]? = some hm →
        RecordFrom sp fs d hm := by
  have he : EnvOk sp fs { rd := .ofPath sp, mod := m, wr, own, copies := clashCopiesOf wr } :=
    ⟨rfl, hparts, hindex⟩
  unfold reach at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨⟨c, x⟩, _, hx, h⟩ := h
  have hc := clashAgree_ok he {} _ #[] (CacheOk.empty sp fs) _ _ hx
  rcases x with e | extra
  · simp at h
  simp only at h
  generalize List.find? _ _ = q at h
  cases q with
  | some x => simp at h
  | none =>
    simp only [ModelIO.bind_ok] at h
    obtain ⟨y, _, hy, h⟩ := h
    have hL := reachGo_from he _ _ c hc (by
      refine ⟨by simp [ReachLog.init], fun i d h' h1 _ => ?_⟩
      simp [ReachLog.init] at h1) y _ hy
    rcases y with e | ⟨L, c'⟩
    · simp at h
    simp only at h
    cases ho : readOrder L.ctx L.reads with
    | error e => simp [ho] at h
    | ok o =>
    simp only [ho] at h
    cases hv : validateCtx (o.map (L.ctx.getD · default)) (o.map (L.homes.getD · default)) with
    | error e => rw [hv] at h; simp at h
    | ok u =>
    cases hf : inferFlags (o.map (L.ctx.getD · default)).toList
      c'.pending.toList with
    | error e => rw [hv] at h; simp only at h; rw [hf] at h; simp at h
    | ok u' =>
    simp only [hv, hf, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h
    obtain ⟨hsz, hfrom⟩ := hL L c' rfl
    refine ⟨by simp, fun i d hm h1 h2 => ?_⟩
    simp only [Array.getElem?_map] at h1 h2
    cases hoi : o[i]? with
    | none => simp [hoi] at h1
    | some j =>
    simp only [hoi, Option.map_some, Option.some.injEq] at h1 h2
    have hj : j < L.ctx.size := List.mem_range.1 ((readOrder_spec ho).1.mem_iff.1
      (Array.mem_toList_iff.2 (Array.mem_of_getElem? hoi)))
    refine hfrom j d hm ?_ ?_
    · rw [← h1, Array.getElem?_eq_getElem hj]; simp [hj]
    · rw [← h2, Array.getElem?_eq_getElem (hsz ▸ hj)]; simp [hsz ▸ hj]

end

end ConLeche.Driver
