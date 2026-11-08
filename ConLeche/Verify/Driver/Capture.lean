module

public import ConLeche.Verify.Driver.ReachFrom
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Frontend.Olean.Equiv

/-!
# The capture check's outcome, on the snapshot

What `ConLeche/Driver/Reach.lean`'s worklist checked of every read (task #501): for every
read of every context record, and every partner read (`agreeCheck`'s and `clashPartners`'),
which branch of `captureOne` passed, stated on the snapshot and over the reach's final
completions (`reach_capture`).

* `copyOf`: the context's copy of a name, the importer's (the name index's first) or a
  completion's located copy;
* `Passed h y`: the read of `y` by a record of home `h` passed (`captureOne`): the context's
  copy is `h`'s own, or comes from a module of `h`'s public-import closure that exports `y`
  (`PubRoute`), or agrees with the first copy of `h`'s view (`HomeView`, `AgreeOk`): one
  module, or two proofs of one statement (`StatusOk`, `proofStatus`'s meaning), the partner
  copy's statement's names read again as reads of its module, an inference recorded where a
  status asks it;
* `Reached`: the modules the reach read from, from the loaded ones through views.

The reads of the caches change only the parts, tables, lookups and recursor maps (`Fr`); the
completions only grow (`Step`), so every fact stated over one state holds over every later one.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend.Olean

/-! ## What the check says -/

/-- **The context's copy of a name**: the importer's, else the located one. -/
@[expose] def copyOf (env : ReachEnv ModelIO) (loc : Std.HashMap Name Spot) (y : Name) :
    Option Spot :=
  match importerSpot env y with
  | some (_, s) => some s
  | none => loc[y]?

/-- **The modules the reach reads from**: the loaded ones, and those of a reached module's
view. -/
inductive Reached (sp : SearchPath) (fs : FS) (wr : WorkerReads) : Name → Prop
  | loaded {j : Nat} (hj : j < wr.loads.order.size) : Reached sp fs wr (wr.loads.nameAt j)
  | view {h : Name} {v : Std.HashMap Name Spot} {y : Name} {s : Spot} :
      Reached sp fs wr h → HomeView sp fs h v → v[y]? = some s → Reached sp fs wr s.part.mod

/-- **`proofStatus`'s meaning** at a copy `s` of kind `k`: a theorem, or an exported axiom
whose module's private part has a theorem there, is a proof outright; a definition, opaque
constant or axiom is one by inference; any other kind is none. -/
@[expose] def StatusOk (sp : SearchPath) (fs : FS) (s : Spot) (k : CKindF Name Unit)
    (p : ProofStatus) : Prop :=
  (p ≠ .no → k.tag < 4) ∧
  (p = .yes → k.tag = 2 ∨ (k.tag = 0 ∧ s.part.level ≠ .private ∧ ∃ q : Spot, CopyAt sp fs q ∧
    q.part = ⟨s.part.mod, .private⟩ ∧ q.pos.name = s.pos.name ∧ q.pos.tag = 2)) ∧
  (p = .infer → k.tag ≠ 2)

/-- **The public-import route** of a read of `y` by a record of home `h`, the context's copy
`s₁`: the importer's copy, of a module of `h`'s public-import closure whose exported part
holds `y`. -/
@[expose] def PubRoute (sp : SearchPath) (fs : FS) (env : ReachEnv ModelIO) (h y : Name)
    (s₁ : Spot) : Prop :=
  ∃ i hi, importerSpot env y = some (i, s₁) ∧ env.wr.loads.index[h]? = some hi ∧
    ((env.wr.pub[hi]?).map (·.has i)).getD false = true ∧
    (s₁.part.level = .exported ∨
      ∃ t, PartNames sp fs ⟨s₁.part.mod, .exported⟩ t ∧ ∃ q ∈ t.consts, q.name = y)

/-- **Two copies of `y` agree** (`agreeCheck`'s outcome): the context's `s₁` and `s₂`, one
module, or both proofs of one statement, `s₂` neither unsafe nor partial, the names of `s₂`'s
statement read as reads of its module (`P`), an inference recorded (`pend`) where a status asks
it. -/
@[expose] def AgreeOk (sp : SearchPath) (fs : FS) (pend : String × Name × ConstantVal → Prop)
    (P : Name × Name → Prop) (y : Name) (s₁ s₂ : Spot) : Prop :=
  s₁.part.mod = s₂.part.mod ∨
    ∃ (r₁ : Region) (cv₁ : ConstantVal) (k₁ : CKindF Name Unit) (r₂ : Region) (cv₂ : ConstantVal)
      (k₂ : CKindF Name Unit) (p₁ p₂ : ProofStatus),
      PartRegion sp fs s₁.part r₁ ∧ StmtSkel r₁ s₁.pos.loc cv₁ k₁ ∧
      PartRegion sp fs s₂.part r₂ ∧ StmtSkel r₂ s₂.pos.loc cv₂ k₂ ∧ s₂.pos.skipped = false ∧
      cv₁.levelParams = cv₂.levelParams ∧ cv₁.type = cv₂.type ∧
      StatusOk sp fs s₁ k₁ p₁ ∧ StatusOk sp fs s₂ k₂ p₂ ∧ p₁ ≠ .no ∧ p₂ ≠ .no ∧
      (∀ c ∈ (needsGo {} #[] cv₂.type).2, P (s₂.part.mod, c)) ∧
      ((p₁ = .infer ∨ p₂ = .infer) → ∃ w, pend (w, y, cv₁))

/-- **The read of `y` by a record of home `h` passed** (`captureOne`; see the module
docstring), over the completions `loc`, the recorded inferences `pend` and the reads `P`. -/
@[expose] def Passed (sp : SearchPath) (fs : FS) (env : ReachEnv ModelIO)
    (loc : Std.HashMap Name Spot) (pend : String × Name × ConstantVal → Prop)
    (P : Name × Name → Prop) (h y : Name) : Prop :=
  ∃ s₁, copyOf env loc y = some s₁ ∧
    (s₁.part.mod = h ∨ PubRoute sp fs env h y s₁ ∨
      ∃ v s₂, HomeView sp fs h v ∧ v[y]? = some s₂ ∧ AgreeOk sp fs pend P y s₁ s₂)

/-- One map's entries kept by another. -/
@[expose] def LocSub (a b : Std.HashMap Name Spot) : Prop :=
  ∀ (y : Name) (s : Spot), a[y]? = some s → b[y]? = some s

theorem copyOf_mono {env : ReachEnv ModelIO} {a b : Std.HashMap Name Spot} (hab : LocSub a b)
    {y : Name} {s : Spot} (h : copyOf env a y = some s) : copyOf env b y = some s := by
  unfold copyOf at h ⊢
  split at h
  · exact h
  · exact hab y s h

theorem AgreeOk.mono {sp : SearchPath} {fs : FS} {pend pend' : String × Name × ConstantVal → Prop}
    {P P' : Name × Name → Prop} (hp : ∀ x, pend x → pend' x) (hP : ∀ x, P x → P' x)
    {y : Name} {s₁ s₂ : Spot} (h : AgreeOk sp fs pend P y s₁ s₂) : AgreeOk sp fs pend' P' y s₁ s₂ := by
  rcases h with h | ⟨r₁, cv₁, k₁, r₂, cv₂, k₂, p₁, p₂, a1, a2, a3, a4, a0, a5, a6, a7, a8, a9,
    a10, a11, a12⟩
  · exact .inl h
  · exact .inr ⟨r₁, cv₁, k₁, r₂, cv₂, k₂, p₁, p₂, a1, a2, a3, a4, a0, a5, a6, a7, a8, a9, a10,
      fun c hc => hP _ (a11 c hc), fun hi => (a12 hi).imp fun _ h => hp _ h⟩

theorem Passed.mono {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO}
    {loc loc' : Std.HashMap Name Spot} {pend pend' : String × Name × ConstantVal → Prop}
    {P P' : Name × Name → Prop} (hl : LocSub loc loc') (hp : ∀ x, pend x → pend' x)
    (hP : ∀ x, P x → P' x) {h y : Name} (H : Passed sp fs env loc pend P h y) :
    Passed sp fs env loc' pend' P' h y := by
  obtain ⟨s₁, h1, h2⟩ := H
  refine ⟨s₁, copyOf_mono hl h1, ?_⟩
  rcases h2 with h2 | h2 | ⟨v, s₂, a, b, c⟩
  · exact .inl h2
  · exact .inr (.inl h2)
  · exact .inr (.inr ⟨v, s₂, a, b, c.mono hp hP⟩)

/-! ## How the caches change -/

/-- **A home's views in the cache are the snapshot's.** -/
@[expose] def VOk (sp : SearchPath) (fs : FS) (c : ReachCache) : Prop :=
  ∀ h v, c.views[h]? = some v → HomeView sp fs h v

/-- **A read that leaves the completions, inferences, partner reads and views alone.** -/
@[expose] def Fr (c c' : ReachCache) : Prop :=
  c'.located = c.located ∧ c'.pending = c.pending ∧ c'.partners = c.partners ∧
    c'.views = c.views

theorem Fr.rfl {c : ReachCache} : Fr c c := ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩

theorem Fr.trans {a b c : ReachCache} (h₁ : Fr a b) (h₂ : Fr b c) : Fr a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

/-- **A step of the check**: the completions kept and the new ones `NL`'s, the inferences
kept, the partner reads kept and the new ones `NP`'s, the views kept the snapshot's. -/
structure Step (sp : SearchPath) (fs : FS) (NL : Name → Spot → Prop) (NP : Name × Name → Prop)
    (c c' : ReachCache) : Prop where
  loc_keep : LocSub c.located c'.located
  loc_new : ∀ y s, c'.located[y]? = some s → c.located[y]? = some s ∨ NL y s
  pend : ∀ x ∈ c.pending, x ∈ c'.pending
  part_keep : ∀ x ∈ c.partners, x ∈ c'.partners
  part_new : ∀ x ∈ c'.partners, x ∈ c.partners ∨ NP x
  views : VOk sp fs c → VOk sp fs c'

theorem Step.ofFr {sp : SearchPath} {fs : FS} {NL : Name → Spot → Prop} {NP : Name × Name → Prop}
    {c c' : ReachCache} (h : Fr c c') : Step sp fs NL NP c c' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun y s hs => by rw [h1]; exact hs, fun y s hs => .inl (h1 ▸ hs), fun x hx => h2 ▸ hx,
    fun x hx => h3 ▸ hx, fun x hx => .inl (h3 ▸ hx), fun hv h v hh => hv h v (h4 ▸ hh)⟩

theorem Step.rfl {sp : SearchPath} {fs : FS} {NL : Name → Spot → Prop} {NP : Name × Name → Prop}
    {c : ReachCache} : Step sp fs NL NP c c := Step.ofFr Fr.rfl

theorem Step.trans {sp : SearchPath} {fs : FS} {NL : Name → Spot → Prop} {NP : Name × Name → Prop}
    {a b c : ReachCache} (h₁ : Step sp fs NL NP a b) (h₂ : Step sp fs NL NP b c) :
    Step sp fs NL NP a c where
  loc_keep y s h := h₂.loc_keep y s (h₁.loc_keep y s h)
  loc_new y s h := (h₂.loc_new y s h).elim (fun h => h₁.loc_new y s h) .inr
  pend x h := h₂.pend x (h₁.pend x h)
  part_keep x h := h₂.part_keep x (h₁.part_keep x h)
  part_new x h := (h₂.part_new x h).elim (fun h => h₁.part_new x h) .inr
  views h := h₂.views (h₁.views h)

theorem Step.mono {sp : SearchPath} {fs : FS} {NL NL' : Name → Spot → Prop}
    {NP NP' : Name × Name → Prop} {c c' : ReachCache} (h : Step sp fs NL NP c c')
    (hl : ∀ y s, NL y s → NL' y s) (hp : ∀ x, NP x → NP' x) : Step sp fs NL' NP' c c' where
  loc_keep := h.loc_keep
  loc_new y s hs := (h.loc_new y s hs).imp id (hl y s)
  pend := h.pend
  part_keep := h.part_keep
  part_new x hx := (h.part_new x hx).imp id (hp x)
  views := h.views

/-- Every value outcome of an action satisfies both of two properties. -/
theorem ModelIO.AllOk.and {α : Type} {x : ModelIO α} {fs : FS} {hs : HS} {P Q : α → Prop}
    (hP : ModelIO.AllOk x fs hs P) (hQ : ModelIO.AllOk x fs hs Q) :
    ModelIO.AllOk x fs hs fun a => P a ∧ Q a :=
  fun v hs' h => ⟨hP v hs' h, hQ v hs' h⟩

/-! ## The reads that change none of it -/

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

theorem tableOf_fr (c : ReachCache) (k : PartKey) :
    ModelIO.AllOk (tableOf env c k) fs ho fun p => Fr c p.1 := by
  unfold tableOf
  split
  · simp only [ModelIO.allOk_pure]; exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only []
    split
    · split
      · split
        · simp only [ModelIO.allOk_pure]; exact ⟨rfl, rfl, rfl, rfl⟩
        all_goals (simp only [ModelIO.allOk_bind]; intro x _ _; cases x <;>
          simp only [ModelIO.allOk_pure] <;> exact ⟨rfl, rfl, rfl, rfl⟩)
      all_goals (simp only [ModelIO.allOk_bind]; intro x _ _; cases x <;>
        simp only [ModelIO.allOk_pure] <;> exact ⟨rfl, rfl, rfl, rfl⟩)
    all_goals (simp only [ModelIO.allOk_bind]; intro x _ _; cases x <;>
      simp only [ModelIO.allOk_pure] <;> exact ⟨rfl, rfl, rfl, rfl⟩)

theorem lookOf_fr (c : ReachCache) (k : PartKey) :
    ModelIO.AllOk (lookOf env c k) fs ho fun p => Fr c p.1 := by
  unfold lookOf
  split
  · simp only [ModelIO.allOk_pure]; exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    have h1 := tableOf_fr c k x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok t =>
      simp only [ModelIO.allOk_pure]
      exact Fr.trans h1 ⟨rfl, rfl, rfl, rfl⟩

theorem withPart_fr {α : Type} (c : ReachCache) (k : PartKey) (f : Region → SM → Option (SM × α)) :
    ModelIO.AllOk (withPart env c k f) fs ho fun p => Fr c p.1 := by
  unfold withPart
  split
  · simp only [pure_bind]
    split <;> (simp only [ModelIO.allOk_pure]; exact ⟨rfl, rfl, rfl, rfl⟩)
  · simp only [ModelIO.allOk_bind]
    intro y _ _
    split
    · simp only [pure_bind, ModelIO.allOk_pure]; exact ⟨rfl, rfl, rfl, rfl⟩
    · split
      · simp only [pure_bind]
        split <;> (simp only [ModelIO.allOk_pure]; exact ⟨rfl, rfl, rfl, rfl⟩)
      · simp only [pure_bind, ModelIO.allOk_pure]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem stmtAt_fr (c : ReachCache) (s : Spot) :
    ModelIO.AllOk (stmtAt env c s) fs ho fun p => Fr c p.1 := withPart_fr c s.part _

theorem privSpot_fr (c : ReachCache) (s : Spot) :
    ModelIO.AllOk (privSpot env c s) fs ho fun p => Fr c p.1 := by
  unfold privSpot
  split
  · simp only [ModelIO.allOk_pure]; exact Fr.rfl
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    have h1 := lookOf_fr c _ x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok l =>
      simp only []
      split <;> (simp only [ModelIO.allOk_pure]; exact h1)

theorem inExported_fr (c : ReachCache) (m : Name) (level : OLeanLevel) (y : Name) :
    ModelIO.AllOk (inExported env c m level y) fs ho fun p => Fr c p.1 := by
  unfold inExported
  split
  · simp only [ModelIO.allOk_pure]; exact Fr.rfl
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    have h1 := lookOf_fr c _ x _ hx
    obtain ⟨c', r⟩ := x
    cases r <;> simpa using h1

theorem recBlocksOf_fr (c : ReachCache) (k : PartKey) :
    ModelIO.AllOk (recBlocksOf env c k) fs ho fun p => Fr c p.1 := by
  unfold recBlocksOf
  split
  · simp only [ModelIO.allOk_pure]; exact Fr.rfl
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    have h1 := tableOf_fr c k x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok t =>
      simp only [ModelIO.allOk_bind]
      intro z _ hz
      have h3 := withPart_fr c' k _ z _ hz
      obtain ⟨c'', r⟩ := z
      cases r with
      | error e => simpa using h1.trans h3
      | ok m =>
        simp only [ModelIO.allOk_pure]
        exact (h1.trans h3).trans ⟨rfl, rfl, rfl, rfl⟩

theorem groupAt_fr (c : ReachCache) (k : PartKey) (n : Name) :
    ModelIO.AllOk (groupAt env c k n) fs ho fun p => Fr c p.1 := by
  unfold groupAt
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  have h1 := lookOf_fr c k x _ hx
  obtain ⟨c₁, r⟩ := x
  cases r with
  | error e => simpa using h1
  | ok look =>
  simp only []
  split
  · simpa using h1
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  have h3 := h1.trans (withPart_fr c₁ k _ x _ hx)
  obtain ⟨c₂, r⟩ := x
  cases r with
  | error e => simpa using h3
  | ok tE =>
  simp only []
  split
  · split
    · simpa using h3
    simp only [ModelIO.allOk_bind]
    intro x _ hx
    have h5 := h3.trans (withPart_fr c₂ k _ x _ hx)
    obtain ⟨c₃, r⟩ := x
    cases r with
    | error e => simpa using h5
    | ok tys =>
    simp only []
    split
    · simpa using h5
    simp only [ModelIO.allOk_bind]
    intro x _ hx
    have h7 := h5.trans (recBlocksOf_fr c₃ k x _ hx)
    obtain ⟨c₄, r⟩ := x
    cases r with
    | error e => simpa using h7
    | ok rb =>
    simp only [ModelIO.allOk_bind]
    intro x _ hx
    have h9 := h7.trans (withPart_fr c₄ k _ x _ hx)
    obtain ⟨c₅, r⟩ := x
    cases r with
    | error e => simpa using h9
    | ok rest =>
    simp only []
    split <;> simpa using h9
  · simpa using h3

theorem stmtRecord_fr (c : ReachCache) (s : Spot) (cv : ConstantVal) :
    ModelIO.AllOk (stmtRecord env c s cv) fs ho fun p => Fr c p.1 := by
  unfold stmtRecord
  split
  · simp only [ModelIO.allOk_pure]; exact Fr.rfl
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    have h1 := privSpot_fr c s x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simpa using h1
    | ok q =>
      simp only []
      split <;> simpa using h1

end

/-! ## A record read, at its copy -/

/-- **A context record read at a copy `s`** (`RecordFrom`'s arms, the copy named): its
statement, the definition there whole, the quotient constant there, or the group of `s`'s
module's private part. -/
inductive ReadAt (sp : SearchPath) (fs : FS) : Declaration → Spot → Prop
  | stmt {x : Name} {s : Spot} {r : Region} {cv : ConstantVal} {k : CKindF Name Unit}
      (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server) (hr : PartRegion sp fs s.part r)
      (hst : StmtSkel r s.pos.loc cv k) (hsk : s.pos.skipped = false)
      (hg : groupOfKind x k = none) (hq : k.tag ≠ 4) (hd : k.tag = 1 → s.part.level = .private)
      (hred : reduceOpNames.contains cv.name = true → ∃ q : Spot, CopyAt sp fs q ∧
        q.part = ⟨s.part.mod, .private⟩ ∧ q.pos.name = s.pos.name ∧ (q.pos.tag = 0 ∨ q.pos.tag = 3)) :
      ReadAt sp fs (.axiomDecl cv) s
  | entry {s : Spot} {r r₀ : Region} {e : CEntryF Name Expr} {d : Declaration} {cv : ConstantVal}
      {k : CKindF Name Unit}
      (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server) (hr : PartRegion sp fs s.part r)
      (he : entryAt r s.pos.loc = some e) (hr₀ : PartRegion sp fs s.part r₀)
      (hst : StmtSkel r₀ s.pos.loc cv k) (hk : k.tag = 1) (hsk : s.pos.skipped = false)
      (hd : recordOfEntry e = .ok d) :
      ReadAt sp fs d s
  | quot {s : Spot} {r : Region} {cv : ConstantVal} {q : String} {d : Declaration}
      (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server) (hr : PartRegion sp fs s.part r)
      (hst : StmtSkel r s.pos.loc cv (.quot q))
      (hd : recordOfEntry ⟨cv.name, cv.levelParams, cv.type, .quot q⟩ = .ok d) :
      ReadAt sp fs d s
  | group {s : Spot} {n : Name} {d : Declaration} (hg : GroupRead sp fs ⟨s.part.mod, .private⟩ n d) :
      ReadAt sp fs d s

theorem ReadAt.recordFrom {sp : SearchPath} {fs : FS} {d : Declaration} {s : Spot}
    (h : ReadAt sp fs d s) : RecordFrom sp fs d s.part.mod := by
  cases h with
  | stmt hs hl hr hst hsk hg hq hd hred => exact .stmt hs hl hr hst hsk hg hq hd hred
  | entry hs hl hr he hr₀ hst hk hsk hd => exact .entry hs hl hr he hr₀ hst hk hsk hd
  | quot hs hl hr hst hd => exact .quot hs hl hr hst hd
  | group hg => exact .group hg

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

/-- **A record read at the copy of `x`**: the context's copy (`copyOf`), whose module is the
record's home. -/
theorem readRecord_at (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (x : Name) :
    ModelIO.AllOk (readRecord env c x) fs ho fun p =>
      Fr c p.1 ∧ ∀ d h, p.2 = .ok (d, h) →
        ∃ s, copyOf env c.located x = some s ∧ h = s.part.mod ∧ ReadAt sp fs d s := by
  unfold readRecord
  split
  rotate_left
  · simp only [ModelIO.allOk_pure]; exact ⟨Fr.rfl, fun d h e => by cases e⟩
  rename_i s completed hsc
  have hcopy : CopyAt sp fs s ∧ s.part.level ≠ .server ∧
      (completed = true → s.part.level = .private) ∧ copyOf env c.located x = some s := by
    unfold copyOf
    split at hsc
    · rename_i i s' hi
      cases hsc
      obtain ⟨a, b⟩ := importerSpot_copy he hi
      exact ⟨a, b, by simp, by rw [hi]⟩
    · rename_i hi
      cases hl : c.located[x]? with
      | none => simp [hl] at hsc
      | some s' =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsc
        obtain ⟨rfl, rfl⟩ := hsc
        obtain ⟨a, b⟩ := hc.located x _ hl
        refine ⟨b, by simp [a], fun _ => a, ?_⟩
        rw [hi]
  obtain ⟨hs, hls, hcomp, hcp⟩ := hcopy
  simp only []
  split
  · simp only [ModelIO.allOk_pure]; exact ⟨Fr.rfl, fun d h e => by cases e⟩
  rename_i hskip
  have hsk : s.pos.skipped = false := by simpa using hskip
  simp only [ModelIO.allOk_bind]
  intro z _ hz
  obtain ⟨h1, h2⟩ := stmtAt_ok he hc s z _ hz
  have f1 := stmtAt_fr (env := env) c s z _ hz
  obtain ⟨c₁, r⟩ := z
  cases r with
  | error e => simp only [ModelIO.allOk_pure]; exact ⟨f1, fun d h e => by cases e⟩
  | ok p =>
  obtain ⟨cv, k⟩ := p
  obtain ⟨r, hr, hst⟩ := h2 cv k rfl
  simp only []
  split
  · rename_i n hn
    simp only [ModelIO.allOk_bind]
    intro z _ hz
    obtain ⟨h3, h4⟩ := groupAt_ok he h1 _ n z _ hz
    have f3 := f1.trans (groupAt_fr (env := env) c₁ _ n z _ hz)
    obtain ⟨c₂, r⟩ := z
    cases r with
    | error e => simp only [ModelIO.allOk_pure]; exact ⟨f3, fun d h e => by cases e⟩
    | ok o =>
      cases o with
      | none => simp only [ModelIO.allOk_pure]; exact ⟨f3, fun d h e => by cases e⟩
      | some d =>
        simp only [ModelIO.allOk_pure]
        refine ⟨f3, fun d' h' e => ?_⟩
        cases e
        exact ⟨s, hcp, rfl, .group (h4 d rfl)⟩
  · rename_i hn
    have stmtCase : k.tag ≠ 4 → (k.tag = 1 → s.part.level = .private) →
        ∀ {hs₁ : HS}, ModelIO.AllOk (stmtRecord env c₁ s cv) fs hs₁ fun p =>
          Fr c p.1 ∧ ∀ d h, p.2 = .ok (d, h) →
            ∃ s', copyOf env c.located x = some s' ∧ h = s'.part.mod ∧ ReadAt sp fs d s' := by
      intro hq hd _ p _ hp
      obtain ⟨h5, h6⟩ := stmtRecord_ok he h1 s cv hs p _ hp
      have f5 := f1.trans (stmtRecord_fr (env := env) c₁ s cv p _ hp)
      refine ⟨f5, fun d h e => ?_⟩
      obtain ⟨rfl, rfl, hred⟩ := h6 d h e
      exact ⟨s, hcp, rfl, .stmt hs hls hr hst hsk hn hq hd hred⟩
    split
    · rename_i v hints safety
      split
      · rename_i hcomp'
        exact stmtCase (by simp [CKindF.tag]) (fun _ => hcomp hcomp')
      · simp only [ModelIO.allOk_bind]
        intro z _ hz
        obtain ⟨h5, h6⟩ := withPart_entry he h1 s.part s.pos.loc z _ hz
        have f5 := f1.trans (withPart_fr (env := env) c₁ s.part _ z _ hz)
        obtain ⟨c₂, r⟩ := z
        cases r with
        | error e => simp only [ModelIO.allOk_pure]; exact ⟨f5, fun d h e => by cases e⟩
        | ok e =>
          obtain ⟨r', hr', he'⟩ := h6 e rfl
          simp only []
          split
          · rename_i d hd
            simp only [ModelIO.allOk_pure]
            refine ⟨f5, fun d' h' eq => ?_⟩
            cases eq
            exact ⟨s, hcp, rfl, .entry hs hls hr' he' hr hst rfl hsk hd⟩
          · simp only [ModelIO.allOk_pure]; exact ⟨f5, fun d h e => by cases e⟩
    · rename_i q
      split
      · rename_i d hd
        simp only [ModelIO.allOk_pure]
        refine ⟨f1, fun d' h' eq => ?_⟩
        cases eq
        exact ⟨s, hcp, rfl, .quot hs hls hr hst hd⟩
      · simp only [ModelIO.allOk_pure]; exact ⟨f1, fun d h e => by cases e⟩
    · rename_i hnd hnq
      refine stmtCase ?_ ?_
      · intro h4; cases k <;> simp_all [CKindF.tag]
      · intro h4; cases k <;> simp_all [CKindF.tag]

end

/-! ## A home's view, and the statuses -/

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

theorem viewAdd_hv (he : EnvOk sp fs env) :
    ∀ (c : ReachCache) (v₀ : Std.HashMap Name Spot) (ks : List PartKey), CacheOk sp fs c →
      ∀ {hs₀ : HS}, ModelIO.AllOk (viewAdd env c v₀ ks) fs hs₀ fun p =>
        Fr c p.1 ∧ ∀ v, p.2 = .ok v → ∃ ts : List NamePositions, ts.length = ks.length ∧
          (∀ k t, (k, t) ∈ ks.zip ts → PartNames sp fs k t) ∧
          v = (ks.zip ts).foldl (fun v kt => viewStep v kt.1 kt.2) v₀
  | c, v₀, [], hc => by
    simp only [viewAdd, ModelIO.allOk_pure]
    exact ⟨Fr.rfl, fun v h => by cases h; exact ⟨[], rfl, by simp, rfl⟩⟩
  | c, v₀, k :: ks, hc => by
    simp only [viewAdd, ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, h2⟩ := tableOf_ok he hc k x _ hx
    have f1 := tableOf_fr (env := env) c k x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e =>
      simp only [ModelIO.allOk_pure]
      exact ⟨f1, fun v h => by cases h⟩
    | ok t =>
      simp only []
      intro p hs' hp
      obtain ⟨f2, h3⟩ := viewAdd_hv he c' _ ks h1 p hs' hp
      refine ⟨f1.trans f2, fun v hv => ?_⟩
      obtain ⟨ts, hl, hts, rfl⟩ := h3 v hv
      refine ⟨t :: ts, by simp [hl], fun k' t' hm => ?_, rfl⟩
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm
      · exact h2 _ rfl
      · exact hts k' t' hm

theorem VOk.insert {c : ReachCache} (hc : VOk sp fs c) {h : Name} {v : Std.HashMap Name Spot}
    (hv : HomeView sp fs h v) : VOk sp fs { c with views := c.views.insert h v } := by
  intro h' v' hh
  simp only [Std.HashMap.getElem?_insert] at hh
  split at hh
  · rename_i heq; cases hh; exact eq_of_beq heq ▸ hv
  · exact hc h' v' hh

theorem Step.insert_views {NL : Name → Spot → Prop} {NP : Name × Name → Prop} {c : ReachCache}
    {h : Name} {v : Std.HashMap Name Spot} (hV : HomeView sp fs h v) :
    Step sp fs NL NP c { c with views := c.views.insert h v } :=
  ⟨fun _ _ h => h, fun _ _ h => .inl h, fun _ h => h, fun _ h => h, fun _ h => .inl h,
    fun hv => hv.insert hV⟩

theorem statusOk_infer {s : Spot} {k : CKindF Name Unit} (h4 : k.tag < 4) (h2 : k.tag ≠ 2) :
    StatusOk sp fs s k .infer :=
  ⟨fun _ => h4, ⟨fun h => (nomatch h), fun _ => h2⟩⟩

theorem statusOk_no {s : Spot} {k : CKindF Name Unit} : StatusOk sp fs s k .no :=
  ⟨fun h => absurd rfl h, ⟨fun h => (nomatch h), fun h => nomatch h⟩⟩

/-- **A home's view, read or cached, is the snapshot's** (`HomeView`). -/
theorem viewOf_hv (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (hvc : VOk sp fs c) (h : Name) :
    ModelIO.AllOk (viewOf env c h) fs ho fun p =>
      Step sp fs (fun _ _ => False) (fun _ => False) c p.1 ∧ VOk sp fs p.1 ∧
        ∀ v, p.2 = .ok v → HomeView sp fs h v := by
  unfold viewOf
  split
  · rename_i v hv
    simp only [ModelIO.allOk_pure]
    exact ⟨Step.rfl, hvc, fun v' h' => by cases h'; exact hvc h v hv⟩
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨h1, h2⟩ := tableOf_ok he hc _ x _ hx
    have f1 := tableOf_fr (env := env) c ⟨h, .private⟩ x _ hx
    have v1 : VOk sp fs x.1 := fun h' v' hh => hvc h' v' (f1.2.2.2 ▸ hh)
    obtain ⟨c', r⟩ := x
    cases r with
    | error e =>
      simp only [ModelIO.allOk_pure]
      exact ⟨Step.ofFr f1, v1, fun v' h => by cases h⟩
    | ok t =>
      simp only [ModelIO.allOk_bind]
      intro y _ hy
      rw [he.rd] at hy
      cases y with
      | error e =>
        simp only [ModelIO.allOk_pure]
        exact ⟨Step.ofFr f1, v1, fun v' h => by cases h⟩
      | ok ld =>
        simp only [ModelIO.allOk_bind]
        intro z _ hz
        obtain ⟨f3, h4⟩ := viewAdd_hv he c' {} _ h1 z _ hz
        have v3 : VOk sp fs z.1 := fun h' v' hh => v1 h' v' (f3.2.2.2 ▸ hh)
        obtain ⟨c'', r⟩ := z
        cases r with
        | error e =>
          simp only [ModelIO.allOk_pure]
          exact ⟨Step.ofFr (f1.trans f3), v3, fun v' h => by cases h⟩
        | ok v =>
          have hV : HomeView sp fs h v := by
            obtain ⟨ts, hl, hts, rfl⟩ := h4 v rfl
            exact ⟨t, ld, ts, h2 t rfl, ⟨_, _, hy⟩, hl, hts, rfl⟩
          simp only [ModelIO.allOk_pure]
          refine ⟨?_, v3.insert hV, fun v' h' => by cases h'; exact hV⟩
          exact (Step.ofFr (f1.trans f3)).trans (Step.insert_views hV)

/-- **A search in a home's view**: the snapshot's view's entry. -/
theorem locate_hv (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (hvc : VOk sp fs c) (h y : Name) :
    ModelIO.AllOk (locate env c h y) fs ho fun p =>
      Step sp fs (fun _ _ => False) (fun _ => False) c p.1 ∧ VOk sp fs p.1 ∧
        ∀ o, p.2 = .ok o → ∃ v, HomeView sp fs h v ∧ o = v[y]? := by
  unfold locate
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h1, h2, h3⟩ := viewOf_hv he hc hvc h x _ hx
  obtain ⟨c', r⟩ := x
  cases r with
  | error e =>
    simp only [ModelIO.allOk_pure]
    exact ⟨h1, h2, fun o h => by cases h⟩
  | ok v =>
    simp only [ModelIO.allOk_pure]
    refine ⟨h1.trans (Step.ofFr ⟨rfl, rfl, rfl, rfl⟩), h2, fun o ho' => ?_⟩
    cases ho'
    exact ⟨v, h3 v rfl, rfl⟩

/-- **A copy's proof status** means what `StatusOk` says. -/
theorem proofStatus_st (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (s : Spot)
    (k : CKindF Name Unit) (hs : CopyAt sp fs s) :
    ModelIO.AllOk (proofStatus env c s k) fs ho fun p =>
      Fr c p.1 ∧ ∀ q, p.2 = .ok q → StatusOk sp fs s k q := by
  unfold proofStatus
  split
  · simp only [ModelIO.allOk_pure]
    refine ⟨Fr.rfl, fun q h => ?_⟩
    cases h
    exact ⟨fun _ => by simp [CKindF.tag], ⟨fun _ => .inl rfl, fun h => nomatch h⟩⟩
  · simp only [ModelIO.allOk_pure]
    refine ⟨Fr.rfl, fun q h => ?_⟩
    cases h
    exact statusOk_infer (by simp [CKindF.tag]) (by simp [CKindF.tag])
  · simp only [ModelIO.allOk_pure]
    refine ⟨Fr.rfl, fun q h => ?_⟩
    cases h
    exact statusOk_infer (by simp [CKindF.tag]) (by simp [CKindF.tag])
  · split
    · simp only [ModelIO.allOk_pure]
      refine ⟨Fr.rfl, fun q h => ?_⟩
      cases h
      exact statusOk_infer (by simp [CKindF.tag]) (by simp [CKindF.tag])
    · rename_i u hl
      simp only [ModelIO.allOk_bind]
      intro x _ hx
      obtain ⟨-, h2⟩ := privSpot_ok he hc s x _ hx
      have f1 := privSpot_fr (env := env) c s x _ hx
      obtain ⟨c', r⟩ := x
      cases r with
      | error e => simp only [ModelIO.allOk_pure]; exact ⟨f1, fun q h => by cases h⟩
      | ok p =>
        obtain ⟨hp1, hp2, hp3, -⟩ := h2 p rfl
        simp only [ModelIO.allOk_pure]
        refine ⟨f1, fun q h => ?_⟩
        cases h
        refine ⟨fun _ => by simp [CKindF.tag], ⟨fun hy => ?_, fun hi => by simp [CKindF.tag]⟩⟩
        refine .inr ⟨rfl, by simpa using hl, p, hp3 hs, hp1, hp2, ?_⟩
        split at hy
        · assumption
        all_goals cases hy
  · simp only [ModelIO.allOk_pure]
    refine ⟨Fr.rfl, fun q h => ?_⟩
    cases h
    exact statusOk_no

end

/-! ## Agreement -/

/-- **A partner read `agreeCheck` records**: a name of the statement of the copy `s₂`, as a read
of `s₂`'s module. -/
@[expose] def AgreeNew (sp : SearchPath) (fs : FS) (s₂ : Spot) (x : Name × Name) : Prop :=
  x.1 = s₂.part.mod ∧ s₂.pos.skipped = false ∧ ∃ rg cv₂ k₂, PartRegion sp fs s₂.part rg ∧
    StmtSkel rg s₂.pos.loc cv₂ k₂ ∧ k₂.tag < 4 ∧ x.2 ∈ (needsGo {} #[] cv₂.type).2

theorem ps_no {p₁ p₂ : ProofStatus} (h : ¬(p₁ == .no || p₂ == .no) = true) :
    p₁ ≠ .no ∧ p₂ ≠ .no := by
  cases p₁ <;> cases p₂ <;>
    first | exact absurd (by decide) h | exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem ps_inf {p₁ p₂ : ProofStatus} (h : ¬(p₁ == .infer || p₂ == .infer) = true) :
    ¬(p₁ = .infer ∨ p₂ = .infer) := by
  cases p₁ <;> cases p₂ <;>
    first | exact absurd (by decide) h | (rintro (h | h) <;> exact (nomatch h))

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

theorem Step.partners_append {NL : Name → Spot → Prop} {NP : Name × Name → Prop} {c : ReachCache}
    {a : Array (Name × Name)} (ha : ∀ x ∈ a, NP x) :
    Step sp fs NL NP c { c with partners := c.partners ++ a } :=
  ⟨fun _ _ h => h, fun _ _ h => .inl h, fun _ h => h,
    fun _ h => Array.mem_append.2 (.inl h),
    fun x h => (Array.mem_append.1 h).imp id (ha x), fun hv => hv⟩

theorem Step.pending_push {NL : Name → Spot → Prop} {NP : Name × Name → Prop} {c : ReachCache}
    (x : String × Name × ConstantVal) :
    Step sp fs NL NP c { c with pending := c.pending.push x } :=
  ⟨fun _ _ h => h, fun _ _ h => .inl h, fun _ h => Array.mem_push.2 (.inl h),
    fun _ h => h, fun _ h => .inl h, fun hv => hv⟩

theorem mem_partnerReads {m : Name} {ty : Expr} {x : Name × Name} :
    x ∈ partnerReads m ty ↔ x.1 = m ∧ x.2 ∈ (needsGo {} #[] ty).2 := by
  obtain ⟨a, b⟩ := x
  simp only [partnerReads, Array.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩; cases h; exact ⟨rfl, hy⟩
  · rintro ⟨rfl, h⟩; exact ⟨b, h, rfl⟩

/-- **Two copies' agreement** is `AgreeOk`, over the inferences and partner reads it
records. -/
theorem agreeCheck_st (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (h y : Name) (s₁ s₂ : Spot) (hs₁ : CopyAt sp fs s₁) (hs₂ : CopyAt sp fs s₂) :
    ModelIO.AllOk (agreeCheck env c h y s₁ s₂) fs ho fun p =>
      Step sp fs (fun _ _ => False) (AgreeNew sp fs s₂) c p.1 ∧
        (p.2 = .ok () → AgreeOk sp fs (· ∈ p.1.pending) (· ∈ p.1.partners) y s₁ s₂) := by
  unfold agreeCheck
  split
  · rename_i hm
    simp only [ModelIO.allOk_pure]
    exact ⟨Step.rfl, fun _ => .inl (eq_of_beq hm)⟩
  split
  · simp only [ModelIO.allOk_pure]; exact ⟨Step.rfl, fun h => by cases h⟩
  rename_i hsk
  have hsk : s₂.pos.skipped = false := by simpa using hsk
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h1, h2⟩ := stmtAt_ok he hc s₁ x _ hx
  have f1 := stmtAt_fr (env := env) c s₁ x _ hx
  obtain ⟨c₁, r₁⟩ := x
  cases r₁ with
  | error e => simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f1, fun h => by cases h⟩
  | ok q₁ =>
  obtain ⟨cv₁, k₁⟩ := q₁
  obtain ⟨rg₁, hr₁, hst₁⟩ := h2 cv₁ k₁ rfl
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨h3, h4⟩ := stmtAt_ok he h1 s₂ x _ hx
  have f2 := f1.trans (stmtAt_fr (env := env) c₁ s₂ x _ hx)
  obtain ⟨c₂, r₂⟩ := x
  cases r₂ with
  | error e => simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f2, fun h => by cases h⟩
  | ok q₂ =>
  obtain ⟨cv₂, k₂⟩ := q₂
  obtain ⟨rg₂, hr₂, hst₂⟩ := h4 cv₂ k₂ rfl
  simp only []
  split
  · simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f2, fun h => by cases h⟩
  rename_i heq
  have heq' : cv₁.levelParams = cv₂.levelParams ∧ cv₁.type = cv₂.type := by
    simpa using heq
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨f3', h5⟩ := proofStatus_st he h3 s₁ k₁ hs₁ x _ hx
  have h3' := proofStatus_ok he h3 s₁ k₁ x _ hx
  have f3 := f2.trans f3'
  obtain ⟨c₃, r₃⟩ := x
  cases r₃ with
  | error e => simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f3, fun h => by cases h⟩
  | ok p₁ =>
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨f4', h6⟩ := proofStatus_st he h3' s₂ k₂ hs₂ x _ hx
  have f4 := f3.trans f4'
  obtain ⟨c₄, r₄⟩ := x
  cases r₄ with
  | error e => simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f4, fun h => by cases h⟩
  | ok p₂ =>
  simp only []
  have hP : ∀ c' ∈ (needsGo {} #[] cv₂.type).2,
      (s₂.part.mod, c') ∈ c₄.partners ++ partnerReads s₂.part.mod cv₂.type :=
    fun c' hc' => Array.mem_append.2 (.inr (mem_partnerReads.2 ⟨rfl, hc'⟩))
  split
  · simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f4, fun h => by cases h⟩
  rename_i hno
  obtain ⟨hn₁, hn₂⟩ := ps_no hno
  have hN : ∀ x ∈ partnerReads s₂.part.mod cv₂.type, AgreeNew sp fs s₂ x := fun x hx => by
    obtain ⟨a, b⟩ := mem_partnerReads.1 hx
    exact ⟨a, hsk, rg₂, cv₂, k₂, hr₂, hst₂, (h6 p₂ rfl).1 hn₂, b⟩
  have st5 : Step sp fs (fun _ _ => False) (AgreeNew sp fs s₂) c
      { c₄ with partners := c₄.partners ++ partnerReads s₂.part.mod cv₂.type } :=
    (Step.ofFr f4).trans (Step.partners_append hN)
  split
  · simp only [ModelIO.allOk_pure]
    refine ⟨st5.trans (Step.pending_push _), fun _ => .inr ⟨rg₁, cv₁, k₁, rg₂, cv₂, k₂, p₁, p₂,
      hr₁, hst₁, hr₂, hst₂, hsk, heq'.1, heq'.2, h5 p₁ rfl, h6 p₂ rfl, hn₁, hn₂, hP,
      fun _ => ⟨_, Array.mem_push.2 (.inr rfl)⟩⟩⟩
  · rename_i hinf
    simp only [ModelIO.allOk_pure]
    exact ⟨st5, fun _ => .inr ⟨rg₁, cv₁, k₁, rg₂, cv₂, k₂, p₁, p₂,
      hr₁, hst₁, hr₂, hst₂, hsk, heq'.1, heq'.2, h5 p₁ rfl, h6 p₂ rfl, hn₁, hn₂, hP,
      fun hi => absurd hi (ps_inf hinf)⟩⟩

end

/-! ## The capture check of one read -/

theorem viewStep_name {v : Std.HashMap Name Spot} {k : PartKey} {t : NamePositions}
    (hv : ∀ (y : Name) (s : Spot), v[y]? = some s → s.pos.name = y) :
    ∀ (y : Name) (s : Spot), (viewStep v k t)[y]? = some s → s.pos.name = y := by
  unfold viewStep
  rw [← Array.foldl_toList]
  generalize t.consts.toList = l
  induction l generalizing v with
  | nil => exact hv
  | cons q l ih =>
    simp only [List.foldl_cons]
    refine ih ?_
    split
    · exact hv
    · intro y s hs
      rw [Std.HashMap.getElem?_insert] at hs
      split at hs
      · cases hs; exact eq_of_beq (by assumption)
      · exact hv y s hs

/-- **A view's copy of a name is of that name.** -/
theorem homeView_name {sp : SearchPath} {fs : FS} {h : Name} {v : Std.HashMap Name Spot} (hv : HomeView sp fs h v) {y : Name}
    {s : Spot} (hs : v[y]? = some s) : s.pos.name = y := by
  obtain ⟨-, ld, ts, -, -, -, -, rfl⟩ := hv
  have key : ∀ (l : List (PartKey × NamePositions)) (v : Std.HashMap Name Spot),
      (∀ (y : Name) (s : Spot), v[y]? = some s → s.pos.name = y) →
      ∀ (y : Name) (s : Spot), (l.foldl (fun v kt => viewStep v kt.1 kt.2) v)[y]? = some s →
        s.pos.name = y := by
    intro l
    induction l with
    | nil => intro v hv; exact hv
    | cons kt l ih => intro v hv; exact ih _ (viewStep_name hv)
  exact key _ {} (fun y s h => by simp at h) y s hs

/-- **A completion `captureOne` makes** at a read of home `h`: a name with no importer copy, at
the private part of the module of `h`'s view's copy. -/
@[expose] def CapNL (sp : SearchPath) (fs : FS) (env : ReachEnv ModelIO) (h y : Name) (s : Spot) :
    Prop :=
  importerSpot env y = none ∧
    ∃ v t, HomeView sp fs h v ∧ v[y]? = some t ∧ s.part = ⟨t.part.mod, .private⟩ ∧ s.pos.name = y

/-- **A partner read `captureOne` records** at a read of home `h`: `agreeCheck`'s, at a copy of
`h`'s view. -/
@[expose] def CapNP (sp : SearchPath) (fs : FS) (h : Name) (x : Name × Name) : Prop :=
  ∃ (v : Std.HashMap Name Spot) (y : Name) (s₂ : Spot), HomeView sp fs h v ∧ v[y]? = some s₂ ∧
    AgreeNew sp fs s₂ x

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

theorem inExported_st (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c) (m : Name)
    (level : OLeanLevel) (y : Name) :
    ModelIO.AllOk (inExported env c m level y) fs ho fun p =>
      Fr c p.1 ∧ (p.2 = .ok true → level = .exported ∨
        ∃ t, PartNames sp fs ⟨m, .exported⟩ t ∧ ∃ q ∈ t.consts, q.name = y) := by
  unfold inExported
  split
  · rename_i hl
    simp only [ModelIO.allOk_pure]
    exact ⟨Fr.rfl, fun _ => .inl (eq_of_beq hl)⟩
  · simp only [ModelIO.allOk_bind]
    intro x _ hx
    obtain ⟨-, h2⟩ := lookOf_ok he hc _ x _ hx
    have f1 := lookOf_fr (env := env) c _ x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simp only [ModelIO.allOk_pure]; exact ⟨f1, fun h => by cases h⟩
    | ok l =>
      obtain ⟨t, ht, rfl⟩ := h2 _ rfl
      simp only [ModelIO.allOk_pure]
      refine ⟨f1, fun hy => .inr ⟨t, ht, ?_⟩⟩
      have hy' : (lookTable t).contains y = true := by simpa using hy
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hy'
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hy'
      obtain ⟨a, b⟩ := lookTable_spec t hq
      exact ⟨q, a, b⟩

theorem CapNP.of {h : Name} {v : Std.HashMap Name Spot} {y : Name} {s₂ : Spot}
    (hv : HomeView sp fs h v) (hs : v[y]? = some s₂) {x : Name × Name}
    (hx : AgreeNew sp fs s₂ x) : CapNP sp fs h x := ⟨v, y, s₂, hv, hs, hx⟩

/-- A read located in `h`'s view and compared with the context's copy `s₁`. -/
theorem locate_agree_st (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (hvc : VOk sp fs c) (h y : Name) (s₁ : Spot) (hs₁ : CopyAt sp fs s₁) :
    ModelIO.AllOk (do
      match ← locate env c h y with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok none) => pure (c, .error (.invalid s!"module {h} reads {y}, which its view \
          does not hold"))
      | (c, .ok (some s₂)) => agreeCheck env c h y s₁ s₂ : ModelIO _) fs ho
      fun p => Step sp fs (CapNL sp fs env h) (CapNP sp fs h) c p.1 ∧
        (p.2 = .ok () → ∃ v s₂, HomeView sp fs h v ∧ v[y]? = some s₂ ∧
          AgreeOk sp fs (· ∈ p.1.pending) (· ∈ p.1.partners) y s₁ s₂) := by
  simp only [ModelIO.allOk_bind]
  intro x _ hx
  obtain ⟨st1, -, h3⟩ := locate_hv he hc hvc h y x _ hx
  obtain ⟨h1, h2⟩ := locate_ok he hc h y x _ hx
  have st1' := st1.mono (NL' := CapNL sp fs env h) (NP' := CapNP sp fs h) (fun _ _ h => h.elim)
    (fun _ h => h.elim)
  obtain ⟨c', r⟩ := x
  cases r with
  | error e => simp only [ModelIO.allOk_pure]; exact ⟨st1', fun h => by cases h⟩
  | ok o =>
    obtain ⟨v, hv, ho'⟩ := h3 o rfl
    cases o with
    | none => simp only [ModelIO.allOk_pure]; exact ⟨st1', fun h => by cases h⟩
    | some s₂ =>
      intro p hs' hp
      obtain ⟨st2, h4⟩ := agreeCheck_st he h1 h y s₁ s₂ hs₁ (h2 s₂ rfl) p hs' hp
      exact ⟨st1'.trans (st2.mono (fun _ _ h => h.elim) (fun x hx => CapNP.of hv ho'.symm hx)),
        fun hok => ⟨v, s₂, hv, ho'.symm, h4 hok⟩⟩

/-- **The capture check of one read**: the read passed (`Passed`), over the completions,
inferences and partner reads after it. -/
theorem captureOne_st (he : EnvOk sp fs env) {c : ReachCache} (hc : CacheOk sp fs c)
    (hvc : VOk sp fs c) (h y : Name) :
    ModelIO.AllOk (captureOne env c h y) fs ho fun p =>
      Step sp fs (CapNL sp fs env h) (CapNP sp fs h) c p.1 ∧
        (p.2 = .ok () → Passed sp fs env p.1.located (· ∈ p.1.pending) (· ∈ p.1.partners) h y) := by
  unfold captureOne
  split
  · simp only [ModelIO.allOk_pure]; exact ⟨Step.rfl, fun h => by cases h⟩
  split
  · rename_i i s₁ hi
    have hcp : ∀ loc, copyOf env loc y = some s₁ := fun loc => by
      unfold copyOf; rw [hi]
    have hs₁ := (importerSpot_copy he hi).1
    split
    · rename_i hm
      simp only [ModelIO.allOk_pure]
      exact ⟨Step.rfl, fun _ => ⟨s₁, hcp _, .inl (eq_of_beq hm)⟩⟩
    have tail : ∀ (x : ReachCache × Except CheckError Bool) {hs₀ : HS}, CacheOk sp fs x.1 →
        Fr c x.1 → (x.2 = .ok true → PubRoute sp fs env h y s₁) →
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
          fun p => Step sp fs (CapNL sp fs env h) (CapNP sp fs h) c p.1 ∧
            (p.2 = .ok () → Passed sp fs env p.1.located (· ∈ p.1.pending) (· ∈ p.1.partners)
              h y) := by
      intro x _ h1 f1 hpub
      have hv1 : VOk sp fs x.1 := fun h' v' hh => hvc h' v' (f1.2.2.2 ▸ hh)
      obtain ⟨c', r⟩ := x
      cases r with
      | error e => simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f1, fun h => by cases h⟩
      | ok b =>
        cases b with
        | true =>
          simp only [ModelIO.allOk_pure]
          exact ⟨Step.ofFr f1, fun _ => ⟨s₁, hcp _, .inr (.inl (hpub rfl))⟩⟩
        | false =>
          intro p hs' hp
          obtain ⟨st, hok⟩ := locate_agree_st he h1 hv1 h y s₁ hs₁ p hs' hp
          refine ⟨(Step.ofFr f1).trans st, fun hp' => ?_⟩
          obtain ⟨v, s₂, hv, hs₂, hag⟩ := hok hp'
          exact ⟨s₁, hcp _, .inr (.inr ⟨v, s₂, hv, hs₂, hag⟩)⟩
    simp only []
    split
    · rename_i hi' hix
      split
      · rename_i hpub
        simp only [ModelIO.allOk_bind]
        intro x _ hx
        obtain ⟨f1, hex⟩ := inExported_st he hc s₁.part.mod s₁.part.level y x _ hx
        exact tail x (inExported_ok he hc _ _ y x _ hx) f1
          (fun ht => ⟨i, hi', hi, hix, by simpa using hpub, hex ht⟩)
      · simp only [ModelIO.allOk_bind]
        intro x _ hx
        simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact tail (c, .ok false) hc Fr.rfl (fun h => by cases h)
    · split
      · rename_i hpub
        simp at hpub
      · simp only [ModelIO.allOk_bind]
        intro x _ hx
        simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact tail (c, .ok false) hc Fr.rfl (fun h => by cases h)
  · rename_i hi
    split
    · rename_i s₁ hl
      have hcp : ∀ loc, LocSub c.located loc → copyOf env loc y = some s₁ := fun loc hsub => by
        unfold copyOf; rw [hi]; exact hsub y s₁ hl
      split
      · rename_i hm
        simp only [ModelIO.allOk_pure]
        exact ⟨Step.rfl, fun _ => ⟨s₁, hcp _ (fun _ _ h => h), .inl (eq_of_beq hm)⟩⟩
      · intro p hs' hp
        obtain ⟨st, hok⟩ := locate_agree_st he hc hvc h y s₁ (hc.located y s₁ hl).2 p hs' hp
        refine ⟨st, fun hp' => ?_⟩
        obtain ⟨v, s₂, hv, hs₂, hag⟩ := hok hp'
        exact ⟨s₁, hcp _ st.loc_keep, .inr (.inr ⟨v, s₂, hv, hs₂, hag⟩)⟩
    · rename_i hl
      simp only [ModelIO.allOk_bind]
      intro x _ hx
      obtain ⟨st1, -, h3⟩ := locate_hv he hc hvc h y x _ hx
      obtain ⟨h1, -⟩ := locate_ok he hc h y x _ hx
      have st1' := st1.mono (NL' := CapNL sp fs env h) (NP' := CapNP sp fs h)
        (fun _ _ h => h.elim) (fun _ h => h.elim)
      obtain ⟨c', r⟩ := x
      cases r with
      | error e => simp only [ModelIO.allOk_pure]; exact ⟨st1', fun h => by cases h⟩
      | ok o =>
        obtain ⟨v, hv, ho'⟩ := h3 o rfl
        cases o with
        | none => simp only [ModelIO.allOk_pure]; exact ⟨st1', fun h => by cases h⟩
        | some s =>
          simp only [ModelIO.allOk_bind]
          intro z _ hz
          obtain ⟨-, h4⟩ := privSpot_ok he h1 s z _ hz
          have f2 := privSpot_fr (env := env) c' s z _ hz
          have hsn : s.pos.name = y := homeView_name hv ho'.symm
          obtain ⟨c'', r⟩ := z
          cases r with
          | error e =>
            simp only [ModelIO.allOk_pure]; exact ⟨st1'.trans (Step.ofFr f2), fun h => by cases h⟩
          | ok q =>
            obtain ⟨hq1, hq2, -, -⟩ := h4 q rfl
            simp only [ModelIO.allOk_pure]
            have hl' : c''.located[y]? = none := by
              rw [f2.1]
              cases h5 : c'.located[y]? with
              | none => rfl
              | some s' =>
                rcases st1.loc_new y s' h5 with h6 | h6
                · rw [hl] at h6; cases h6
                · exact h6.elim
            refine ⟨st1'.trans ((Step.ofFr f2).trans ⟨fun y' s' hs' => ?_, fun y' s' hs' => ?_,
              fun _ h => h, fun _ h => h, fun _ h => .inl h, fun hv => hv⟩), fun _ => ?_⟩
            · simp only [Std.HashMap.getElem?_insert]
              split
              · rename_i hyy
                rw [← eq_of_beq hyy, hl'] at hs'; cases hs'
              · exact hs'
            · simp only [Std.HashMap.getElem?_insert] at hs'
              split at hs'
              · rename_i hyy
                cases hs'
                obtain rfl := eq_of_beq hyy
                exact .inr ⟨hi, v, s, hv, ho'.symm, hq1, hq2.trans hsn⟩
              · exact .inl hs'
            · refine ⟨q, ?_, .inr (.inr ⟨v, s, hv, ho'.symm, .inl ?_⟩)⟩
              · unfold copyOf; rw [hi]; simp
              · rw [hq1]

end

/-! ## Every read of a record, the partners' reads, the stored names, the clashes -/

/-- **A completion `storedNamesOk` makes**: a name with no importer copy, at the home's private
part. -/
@[expose] def StoredNL (env : ReachEnv ModelIO) (h n : Name) (s : Spot) : Prop :=
  importerSpot env n = none ∧ s.part = ⟨h, .private⟩ ∧ s.pos.name = n

/-- **The clash rule passed at a clash** (`clashAgree`): every loaded copy has a status other
than `.no`, and where it is `.infer`, an inference of a copy's statement is recorded. -/
@[expose] def ClashOk (sp : SearchPath) (fs : FS) (wr : WorkerReads)
    (pend : String × Name × ConstantVal → Prop) (cl : Clash) : Prop :=
  ∀ x ∈ cl.copies, ∀ q, wr.index.at x.1 = some q →
    ∃ p, StatusOk sp fs (spotOf wr x.1 q) x.2.2 p ∧ p ≠ .no ∧
      (p = .infer → ∃ w cv', pend (w, cl.name, cv') ∧ ∃ x' ∈ cl.copies, x'.2.1 = cv')

theorem ClashOk.mono {sp : SearchPath} {fs : FS} {wr : WorkerReads}
    {pend pend' : String × Name × ConstantVal → Prop} (hp : ∀ x, pend x → pend' x) {cl : Clash}
    (h : ClashOk sp fs wr pend cl) : ClashOk sp fs wr pend' cl := fun x hx q hq => by
  obtain ⟨p, a, b, c⟩ := h x hx q hq
  exact ⟨p, a, b, fun hi => by
    obtain ⟨w, cv', h1, h2⟩ := c hi
    exact ⟨w, cv', hp _ h1, h2⟩⟩

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

theorem captureAll_st (he : EnvOk sp fs env) (h : Name) :
    ∀ (c : ReachCache) (ys : List Name), CacheOk sp fs c → VOk sp fs c → ∀ {hs₀ : HS},
      ModelIO.AllOk (captureAll env h c ys) fs hs₀ fun p =>
        CacheOk sp fs p.1 ∧ Step sp fs (CapNL sp fs env h) (CapNP sp fs h) c p.1 ∧
          (p.2 = .ok () → ∀ y ∈ ys,
            Passed sp fs env p.1.located (· ∈ p.1.pending) (· ∈ p.1.partners) h y)
  | c, [], hc, hv => by
    simp only [captureAll, ModelIO.allOk_pure]
    exact ⟨hc, Step.rfl, fun _ y hy => by cases hy⟩
  | c, y :: ys, hc, hv => by
    simp only [captureAll, ModelIO.allOk_bind]
    intro x _ hx
    have h1 := captureOne_ok he hc h y x _ hx
    obtain ⟨st, hP⟩ := captureOne_st he hc hv h y x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simp only [ModelIO.allOk_pure]; exact ⟨h1, st, fun h => by cases h⟩
    | ok u =>
      intro p hs' hp
      obtain ⟨h2, st2, hP2⟩ := captureAll_st he h c' ys h1 (st.views hv) p hs' hp
      refine ⟨h2, st.trans st2, fun hok y' hy' => ?_⟩
      rcases List.mem_cons.1 hy' with rfl | hy'
      · exact (hP rfl).mono st2.loc_keep st2.pend st2.part_keep
      · exact hP2 hok y' hy'

theorem capturePairs_st (he : EnvOk sp fs env) :
    ∀ (c : ReachCache) (ps : List (Name × Name)), CacheOk sp fs c → VOk sp fs c → ∀ {hs₀ : HS},
      ModelIO.AllOk (capturePairs env c ps) fs hs₀ fun p =>
        CacheOk sp fs p.1 ∧
          Step sp fs (fun y s => ∃ x ∈ ps, CapNL sp fs env x.1 y s)
            (fun z => ∃ x ∈ ps, CapNP sp fs x.1 z) c p.1 ∧
          (p.2 = .ok () → ∀ x ∈ ps,
            Passed sp fs env p.1.located (· ∈ p.1.pending) (· ∈ p.1.partners) x.1 x.2)
  | c, [], hc, hv => by
    simp only [capturePairs, ModelIO.allOk_pure]
    exact ⟨hc, Step.rfl, fun _ y hy => by cases hy⟩
  | c, (h, y) :: ps, hc, hv => by
    simp only [capturePairs, ModelIO.allOk_bind]
    intro x _ hx
    have h1 := captureOne_ok he hc h y x _ hx
    obtain ⟨st, hP⟩ := captureOne_st he hc hv h y x _ hx
    have st' := st.mono (NL' := fun a b => ∃ x ∈ (h, y) :: ps, CapNL sp fs env x.1 a b)
      (NP' := fun z => ∃ x ∈ (h, y) :: ps, CapNP sp fs x.1 z)
      (fun _ _ hn => ⟨(h, y), List.mem_cons_self, hn⟩) (fun _ hn => ⟨(h, y), List.mem_cons_self, hn⟩)
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simp only [ModelIO.allOk_pure]; exact ⟨h1, st', fun h => by cases h⟩
    | ok u =>
      intro p hs' hp
      obtain ⟨h2, st2, hP2⟩ := capturePairs_st he c' ps h1 (st.views hv) p hs' hp
      refine ⟨h2, st'.trans (st2.mono (fun _ _ ⟨x, hx, hn⟩ => ⟨x, List.mem_cons_of_mem _ hx, hn⟩)
        (fun z ⟨x, hx, hn⟩ => ⟨x, List.mem_cons_of_mem _ hx, hn⟩)), fun hok x' hx' => ?_⟩
      rcases List.mem_cons.1 hx' with rfl | hx'
      · exact (hP rfl).mono st2.loc_keep st2.pend st2.part_keep
      · exact hP2 hok x' hx'

theorem storedNamesOk_st (he : EnvOk sp fs env) (h : Name) :
    ∀ (c : ReachCache) (ns : List Name), CacheOk sp fs c → ∀ {hs₀ : HS},
      ModelIO.AllOk (storedNamesOk env c h ns) fs hs₀ fun p =>
        Step sp fs (StoredNL env h) (fun _ => False) c p.1 ∧
          (p.2 = .ok () → ∀ n ∈ ns, ∃ s, copyOf env p.1.located n = some s ∧ s.part.mod = h)
  | c, [], hc => by
    simp only [storedNamesOk, ModelIO.allOk_pure]
    exact ⟨Step.rfl, fun _ n hn => by cases hn⟩
  | c, n :: ns, hc => by
    unfold storedNamesOk
    split
    · rename_i i s hi
      split
      · rename_i hm
        intro p hs' hp
        obtain ⟨st, hok⟩ := storedNamesOk_st he h c ns hc p hs' hp
        refine ⟨st, fun hp' n' hn' => ?_⟩
        rcases List.mem_cons.1 hn' with rfl | hn'
        · exact ⟨s, by unfold copyOf; rw [hi], eq_of_beq hm⟩
        · exact hok hp' n' hn'
      · simp only [ModelIO.allOk_pure]; exact ⟨Step.rfl, fun h => by cases h⟩
    · rename_i hi
      split
      · rename_i s hl
        split
        · rename_i hm
          intro p hs' hp
          obtain ⟨st, hok⟩ := storedNamesOk_st he h c ns hc p hs' hp
          refine ⟨st, fun hp' n' hn' => ?_⟩
          rcases List.mem_cons.1 hn' with rfl | hn'
          · exact ⟨s, by unfold copyOf; rw [hi]; exact st.loc_keep _ _ hl, eq_of_beq hm⟩
          · exact hok hp' n' hn'
        · simp only [ModelIO.allOk_pure]; exact ⟨Step.rfl, fun h => by cases h⟩
      · rename_i hl
        simp only [ModelIO.allOk_bind]
        intro x _ hx
        obtain ⟨h1, h2⟩ := lookOf_ok he hc _ x _ hx
        have f1 := lookOf_fr (env := env) c _ x _ hx
        obtain ⟨c', r⟩ := x
        cases r with
        | error e => simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f1, fun h => by cases h⟩
        | ok l =>
          obtain ⟨t, ht, hlt⟩ := h2 l rfl
          simp only []
          split
          · rename_i q hq
            have hq' : (lookTable t)[n]? = some q := hlt ▸ hq
            have hc' : CacheOk sp fs { c' with located := c'.located.insert n ⟨⟨h, .private⟩, q⟩ } :=
              h1.insert_located' rfl ⟨t, ht, (lookTable_spec t hq').1⟩
            have hl' : c'.located[n]? = none := by rw [f1.1]; exact hl
            have st1 : Step sp fs (StoredNL env h) (fun _ => False) c
                { c' with located := c'.located.insert n ⟨⟨h, .private⟩, q⟩ } :=
              (Step.ofFr f1).trans ⟨fun y' s' hs' => by
                  simp only [Std.HashMap.getElem?_insert]
                  split
                  · rename_i hyy; rw [← eq_of_beq hyy, hl'] at hs'; cases hs'
                  · exact hs',
                fun y' s' hs' => by
                  simp only [Std.HashMap.getElem?_insert] at hs'
                  split at hs'
                  · rename_i hyy
                    cases hs'
                    obtain rfl := eq_of_beq hyy
                    exact .inr ⟨hi, rfl, (lookTable_spec t hq').2⟩
                  · exact .inl hs',
                fun _ h => h, fun _ h => h, fun _ h => .inl h, fun hv => hv⟩
            intro p hs' hp
            obtain ⟨st, hok⟩ := storedNamesOk_st he h _ ns hc' p hs' hp
            refine ⟨st1.trans st, fun hp' n' hn' => ?_⟩
            rcases List.mem_cons.1 hn' with rfl | hn'
            · refine ⟨⟨⟨h, .private⟩, q⟩, ?_, rfl⟩
              unfold copyOf; rw [hi]
              exact st.loc_keep _ _ (by simp)
            · exact hok hp' n' hn'
          · simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f1, fun h => by cases h⟩

theorem spotOf_copy (he : EnvOk sp fs env) {cp : Copy} {q : NamePosition}
    (h : env.wr.index.at cp = some q) : CopyAt sp fs (spotOf env.wr cp q) := by
  simp only [NameIndex.at] at h
  obtain ⟨t, ht, hq⟩ := bind_some_left h
  exact ⟨t, he.parts _ t ht, Array.mem_of_getElem? hq⟩

instance : LawfulBEq ProofStatus where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

theorem statuses_st (he : EnvOk sp fs env) (xs : List (Spot × ConstantVal × CKindF Name Unit)) :
    ∀ (c : ReachCache) (acc : List ProofStatus),
      CacheOk sp fs c → (∀ x ∈ xs, CopyAt sp fs x.1) → ∀ {hs₀ : HS},
        ModelIO.AllOk (clashAgree.statuses env c xs acc) fs hs₀ fun p =>
          Fr c p.1 ∧ ∀ ps, p.2 = .ok ps → ps.length = acc.length + xs.length ∧
            (∀ a ∈ acc, a ∈ ps) ∧ ∀ x ∈ xs, ∃ q ∈ ps, StatusOk sp fs x.1 x.2.2 q := by
  induction xs with
  | nil =>
    intro c acc hc _ _
    simp only [clashAgree.statuses, ModelIO.allOk_pure]
    exact ⟨Fr.rfl, fun ps h => by
      cases h; exact ⟨by simp, fun a ha => ha, fun x hx => by cases hx⟩⟩
  | cons y rest ih =>
    obtain ⟨s, cv, k⟩ := y
    intro c acc hc hcs _
    simp only [clashAgree.statuses, ModelIO.allOk_bind]
    intro x _ hx
    have h1 := proofStatus_ok he hc s k x _ hx
    obtain ⟨f1, h2⟩ := proofStatus_st he hc s k (hcs (s, cv, k) List.mem_cons_self) x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simp only [ModelIO.allOk_pure]; exact ⟨f1, fun ps h => by cases h⟩
    | ok p =>
      intro z hs' hz
      obtain ⟨f2, h3⟩ := ih c' _ h1 (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) z hs' hz
      refine ⟨f1.trans f2, fun ps hps => ?_⟩
      obtain ⟨a0, a1, a2⟩ := h3 ps hps
      refine ⟨by simp only [List.length_cons] at a0 ⊢; omega,
        fun a ha => a1 a (List.mem_cons_of_mem _ ha), fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨p, a1 p List.mem_cons_self, h2 p rfl⟩
      · exact a2 x hx

theorem mem_clashSpots {wr : WorkerReads} {cl : Clash} {x : Spot × ConstantVal × CKindF Name Unit} :
    x ∈ cl.copies.toList.filterMap (fun (cp, cv, k) =>
      (wr.index.at cp).map fun q =>
        ((⟨⟨wr.loads.nameAt cp.mod, ((wr.loads.flags[cp.mod]?).getD default).level⟩, q⟩ : Spot), cv, k)) ↔
      ∃ y ∈ cl.copies, ∃ q, wr.index.at y.1 = some q ∧ x = (spotOf wr y.1 q, y.2.1, y.2.2) := by
  simp only [List.mem_filterMap, Array.mem_toList_iff]
  constructor
  · rintro ⟨⟨cp, cv, k⟩, hy, h⟩
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨_, hy, q, hq, rfl⟩
  · rintro ⟨⟨cp, cv, k⟩, hy, q, hq, rfl⟩
    exact ⟨_, hy, by simp [hq, spotOf]⟩

/-- **The clash rule's outcome** (`ClashOk` at every clash). -/
theorem clashAgree_st (he : EnvOk sp fs env) :
    ∀ (c : ReachCache) (cls : List Clash) (acc : Array Name), CacheOk sp fs c → ∀ {hs₀ : HS},
      ModelIO.AllOk (clashAgree env c cls acc) fs hs₀ fun p =>
        Step sp fs (fun _ _ => False) (fun _ => False) c p.1 ∧
          ∀ e, p.2 = .ok e → ∀ cl ∈ cls, ClashOk sp fs env.wr (· ∈ p.1.pending) cl
  | c, [], acc, hc => by
    simp only [clashAgree, ModelIO.allOk_pure]
    exact ⟨Step.rfl, fun _ _ cl h => by cases h⟩
  | c, cl :: cls, acc, hc => by
    simp only [clashAgree, ModelIO.allOk_bind]
    intro x _ hx
    have h1 := statuses_ok he c _ [] hc x _ hx
    obtain ⟨f1, h2⟩ := statuses_st he _ c [] hc (fun y hy => by
      obtain ⟨z, -, q, hq, rfl⟩ := mem_clashSpots.1 hy
      exact spotOf_copy he hq) x _ hx
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f1, fun _ h => by cases h⟩
    | ok ps =>
      obtain ⟨hlen, -, hps⟩ := h2 ps rfl
      have hcl : ∀ (pend : String × Name × ConstantVal → Prop),
          (ps.contains .infer = true → ∃ w cv', pend (w, cl.name, cv') ∧ ∃ x' ∈ cl.copies, x'.2.1 = cv') →
          ps.contains .no = false → ClashOk sp fs env.wr pend cl := by
        intro pend hinf hno y hy q hq
        obtain ⟨p, hp, hst⟩ := hps _ (mem_clashSpots.2 ⟨y, hy, q, hq, rfl⟩)
        refine ⟨p, hst, fun h => ?_, fun h => hinf ?_⟩
        · subst h
          have := List.contains_iff_mem.2 hp
          rw [hno] at this; cases this
        · subst h; exact List.contains_iff_mem.2 hp
      simp only []
      split
      · simp only [ModelIO.allOk_pure]; exact ⟨Step.ofFr f1, fun _ h => by cases h⟩
      rename_i hno
      have hno' : ps.contains .no = false := by simpa using hno
      split
      · rename_i hinf
        split
        · rename_i s₀ cv₀ k₀ rest hsp
          intro p hs' hp
          obtain ⟨st, hok⟩ := clashAgree_st he _ cls _ (h1.pending _) p hs' hp
          refine ⟨(Step.ofFr f1).trans ((Step.pending_push _).trans st), fun e he' cl' hcl' => ?_⟩
          rcases List.mem_cons.1 hcl' with rfl | hcl'
          · refine hcl _ (fun _ => ⟨_, cv₀, st.pend _ (Array.mem_push.2 (.inr rfl)), ?_⟩) hno'
            have : (s₀, cv₀, k₀) ∈ cl'.copies.toList.filterMap (fun (cp, cv, k) =>
                (env.wr.index.at cp).map fun q =>
                  ((⟨⟨env.wr.loads.nameAt cp.mod, ((env.wr.loads.flags[cp.mod]?).getD default).level⟩,
                    q⟩ : Spot), cv, k)) := by rw [hsp]; exact List.mem_cons_self
            obtain ⟨y, hy, q, -, hyq⟩ := mem_clashSpots.1 this
            exact ⟨y, hy, by simp only [Prod.mk.injEq] at hyq; exact hyq.2.1.symm⟩
          · exact hok e he' cl' hcl'
        · rename_i hsp
          intro p hs' hp
          obtain ⟨st, hok⟩ := clashAgree_st he _ cls _ h1 p hs' hp
          refine ⟨(Step.ofFr f1).trans st, fun e he' cl' hcl' => ?_⟩
          rcases List.mem_cons.1 hcl' with rfl | hcl'
          · refine hcl _ (fun _ => ?_) hno'
            -- no spot: no status, so none is `.infer`
            rw [hsp] at hlen
            simp only [List.length_nil] at hlen
            rw [List.length_eq_zero_iff.1 hlen] at hinf
            simp at hinf
          · exact hok e he' cl' hcl'
      · rename_i hinf
        intro p hs' hp
        obtain ⟨st, hok⟩ := clashAgree_st he _ cls _ h1 p hs' hp
        refine ⟨(Step.ofFr f1).trans st, fun e he' cl' hcl' => ?_⟩
        rcases List.mem_cons.1 hcl' with rfl | hcl'
        · exact hcl _ (fun h => absurd h hinf) hno'
        · exact hok e he' cl' hcl'

end

/-! ## The worklist -/

/-- **Where a checked read comes from**: a record's read (its home the reader), a partner read
of `agreeCheck` at a copy of a reader's view, or a partner read of a clash name a record
stores. -/
@[expose] def Origin (sp : SearchPath) (fs : FS) (env : ReachEnv ModelIO) (ctx : Array Declaration)
    (homes : Array Name) (z : Name × Name) : Prop :=
  (∃ (k : Nat) (d : Declaration), ctx[k]? = some d ∧ homes[k]? = some z.1 ∧ z.2 ∈ recordReads d) ∨
  (∃ h, CapNP sp fs h z) ∨
  (∃ (k : Nat) (d : Declaration), ctx[k]? = some d ∧ ∃ n ∈ declNames d, ∃ cs, env.copies[n]? = some cs ∧
    ∃ kc ∈ cs, z.1 = kc.1 ∧ z.2 ∈ (needsGo {} #[] kc.2.type).2)

/-- **The worklist's invariant** (see the module docstring), `D` the reads checked so far. -/
structure CapInv (sp : SearchPath) (fs : FS) (env : ReachEnv ModelIO) (L : ReachLog)
    (c : ReachCache) (D : List (Name × Name)) : Prop where
  cache : CacheOk sp fs c
  views : VOk sp fs c
  size : L.ctx.size = L.homes.size
  passed : ∀ x ∈ D,
    Passed sp fs env c.located (· ∈ c.pending) (fun z => z ∈ D ∨ z ∈ c.partners) x.1 x.2
  records : ∀ (k : Nat) (d : Declaration) (h : Name), L.ctx[k]? = some d → L.homes[k]? = some h →
    (∀ y ∈ recordReads d, (h, y) ∈ D) ∧
    (∃ x ∈ declNames d, ∃ s, copyOf env c.located x = some s ∧ s.part.mod = h ∧ ReadAt sp fs d s) ∧
    (∀ n ∈ declNames d, ∃ s, copyOf env c.located n = some s ∧ s.part.mod = h) ∧
    (∀ n ∈ declNames d, ∀ cs, env.copies[n]? = some cs → ∀ kc ∈ cs,
      ∀ y ∈ (needsGo {} #[] kc.2.type).2, (kc.1, y) ∈ D ∨ (kc.1, y) ∈ c.partners)
  located : ∀ (y : Name) (s : Spot), c.located[y]? = some s →
    importerSpot env y = none ∧ Reached sp fs env.wr s.part.mod ∧ s.pos.name = y
  reads : ∀ z, z ∈ D ∨ z ∈ c.partners → Reached sp fs env.wr z.1 ∧ Origin sp fs env L.ctx L.homes z
  clashes : ∀ cl ∈ env.wr.clashes, ClashOk sp fs env.wr (· ∈ c.pending) cl

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

theorem importerSpot_reached (hsize : env.wr.index.parts.size ≤ env.wr.loads.order.size)
    {y : Name} {i : Nat} {s : Spot} (h : importerSpot env y = some (i, s)) :
    Reached sp fs env.wr s.part.mod := by
  unfold importerSpot at h
  obtain ⟨cp, -, h⟩ := bind_some_left h
  obtain ⟨q, hq, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [NameIndex.at] at hq
  obtain ⟨t, ht, -⟩ := bind_some_left hq
  have : cp.mod < env.wr.index.parts.size := (Array.getElem?_eq_some_iff.1 ht).1
  exact .loaded (by omega)

theorem copyOf_reached (hsize : env.wr.index.parts.size ≤ env.wr.loads.order.size)
    {loc : Std.HashMap Name Spot}
    (hloc : ∀ (y : Name) (s : Spot), loc[y]? = some s → Reached sp fs env.wr s.part.mod)
    {y : Name} {s : Spot} (h : copyOf env loc y = some s) : Reached sp fs env.wr s.part.mod := by
  unfold copyOf at h
  split at h
  · rename_i i s' hi
    cases h
    exact importerSpot_reached hsize hi
  · exact hloc y s h

theorem mem_foldl_partnerReads {z : Name × Name} :
    ∀ (cs : List (Name × ConstantVal)) (acc : Array (Name × Name)),
      z ∈ cs.foldl (fun acc (kc : Name × ConstantVal) => acc ++ partnerReads kc.1 kc.2.type) acc ↔
        z ∈ acc ∨ ∃ kc ∈ cs, z.1 = kc.1 ∧ z.2 ∈ (needsGo {} #[] kc.2.type).2
  | [], acc => by simp
  | kc :: cs, acc => by
    rw [List.foldl_cons, mem_foldl_partnerReads cs, Array.mem_append, mem_partnerReads]
    constructor
    · rintro ((h | h) | ⟨kc', hk, h⟩)
      · exact .inl h
      · exact .inr ⟨kc, List.mem_cons_self, h⟩
      · exact .inr ⟨kc', List.mem_cons_of_mem _ hk, h⟩
    · rintro (h | ⟨kc', hk, h⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.1 hk with rfl | hk
        · exact .inl (.inr h)
        · exact .inr ⟨kc', hk, h⟩

theorem mem_clashPartners {z : Name × Name} :
    ∀ (ns : List Name) (acc : Array (Name × Name)),
      z ∈ ns.foldl (fun acc n => match env.copies[n]? with
        | some cs => cs.foldl (fun acc (k, cv) => acc ++ partnerReads k cv.type) acc
        | none => acc) acc ↔
        z ∈ acc ∨ ∃ n ∈ ns, ∃ cs, env.copies[n]? = some cs ∧
          ∃ kc ∈ cs, z.1 = kc.1 ∧ z.2 ∈ (needsGo {} #[] kc.2.type).2
  | [], acc => by simp
  | n :: ns, acc => by
    rw [List.foldl_cons, mem_clashPartners ns]
    constructor
    · rintro (h | ⟨n', hn, cs, hcs, h⟩)
      · split at h
        · rename_i cs hcs
          rw [← Array.foldl_toList, mem_foldl_partnerReads] at h
          rcases h with h | ⟨kc, hk, h⟩
          · exact .inl h
          · exact .inr ⟨n, List.mem_cons_self, cs, hcs, kc, Array.mem_toList_iff.1 hk, h⟩
        · exact .inl h
      · exact .inr ⟨n', List.mem_cons_of_mem _ hn, cs, hcs, h⟩
    · rintro (h | ⟨n', hn, cs, hcs, kc, hk, h⟩)
      · refine .inl ?_
        split
        · rw [← Array.foldl_toList, mem_foldl_partnerReads]; exact .inl h
        · exact h
      · rcases List.mem_cons.1 hn with rfl | hn
        · refine .inl ?_
          rw [hcs]
          simp only []
          rw [← Array.foldl_toList, mem_foldl_partnerReads]
          exact .inr ⟨kc, Array.mem_toList_iff.2 hk, h⟩
        · exact .inr ⟨n', hn, cs, hcs, kc, hk, h⟩

theorem mem_clashCopiesOf {wr : WorkerReads} {n : Name} {cs : Array (Name × ConstantVal)}
    (h : (clashCopiesOf wr)[n]? = some cs) {kc : Name × ConstantVal} (hk : kc ∈ cs) :
    ∃ cl ∈ wr.clashes, ∃ x ∈ cl.copies, kc = (wr.loads.nameAt x.1.mod, x.2.1) := by
  unfold clashCopiesOf at h
  rw [← Array.foldl_toList] at h
  suffices H : ∀ (l : List Clash) (m : Std.HashMap Name (Array (Name × ConstantVal))),
      (∀ cl ∈ l, cl ∈ wr.clashes) →
      (∀ (n : Name) (cs : Array (Name × ConstantVal)), m[n]? = some cs → ∀ kc ∈ cs,
        ∃ cl ∈ wr.clashes, ∃ x ∈ cl.copies, kc = (wr.loads.nameAt x.1.mod, x.2.1)) →
      ∀ n cs, (l.foldl (fun m cl => m.insert cl.name
        (cl.copies.map fun (cp, cv, _) => (wr.loads.nameAt cp.mod, cv))) m)[n]? = some cs →
        ∀ kc ∈ cs, ∃ cl ∈ wr.clashes, ∃ x ∈ cl.copies, kc = (wr.loads.nameAt x.1.mod, x.2.1) from
    H _ {} (fun cl h => Array.mem_toList_iff.1 h) (by simp) n cs h kc hk
  intro l
  induction l with
  | nil => intro m _ hm; exact hm
  | cons cl l ih =>
    intro m hl hm
    simp only [List.foldl_cons]
    refine ih _ (fun c hc => hl c (List.mem_cons_of_mem _ hc)) (fun n' cs' h' kc' hk' => ?_)
    rw [Std.HashMap.getElem?_insert] at h'
    split at h'
    · cases h'
      obtain ⟨⟨cp, cv, k⟩, hx, rfl⟩ := Array.mem_map.1 hk'
      exact ⟨cl, hl cl List.mem_cons_self, _, hx, rfl⟩
    · exact hm n' cs' h' kc' hk'

theorem Origin.push {ctx : Array Declaration} {homes : Array Name} (hsz : ctx.size = homes.size)
    {d : Declaration} {h : Name} {z : Name × Name} (ho : Origin sp fs env ctx homes z) :
    Origin sp fs env (ctx.push d) (homes.push h) z := by
  have hk : ∀ {k : Nat} {e : Declaration}, ctx[k]? = some e → (ctx.push d)[k]? = some e ∧
      ∀ {g : Name}, homes[k]? = some g → (homes.push h)[k]? = some g := by
    intro k e he
    have hlt := (Array.getElem?_eq_some_iff.1 he).1
    refine ⟨by rw [Array.getElem?_push]; simp only [show k ≠ ctx.size by omega, ↓reduceIte]; exact he, fun {g} hg => ?_⟩
    rw [Array.getElem?_push]; simp only [show k ≠ homes.size by omega, ↓reduceIte]; exact hg
  rcases ho with ⟨k, e, he, hh, hr⟩ | ho | ⟨k, e, he, hrest⟩
  · exact .inl ⟨k, e, (hk he).1, (hk he).2 hh, hr⟩
  · exact .inr (.inl ho)
  · exact .inr (.inr ⟨k, e, (hk he).1, hrest⟩)

end

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO} {ho : HS}

theorem copies_reached (hcop : env.copies = clashCopiesOf env.wr)
    (hcm : ∀ cl ∈ env.wr.clashes, ∀ x ∈ cl.copies, x.1.mod < env.wr.loads.order.size)
    {n : Name} {cs : Array (Name × ConstantVal)} (h : env.copies[n]? = some cs)
    {kc : Name × ConstantVal} (hk : kc ∈ cs) : Reached sp fs env.wr kc.1 := by
  rw [hcop] at h
  obtain ⟨cl, hcl, x, hx, rfl⟩ := mem_clashCopiesOf h hk
  exact .loaded (hcm cl hcl x hx)

/-- The partners' reads checked: the invariant kept. -/
theorem CapInv.pairs {L L' : ReachLog} {c c₁ : ReachCache} {D : List (Name × Name)}
    (hI : CapInv sp fs env L c D) (hctx : L'.ctx = L.ctx) (hhomes : L'.homes = L.homes)
    (h1 : CacheOk sp fs c₁)
    (st : Step sp fs (fun y s => ∃ x ∈ c.partners.toList, CapNL sp fs env x.1 y s)
      (fun z => ∃ x ∈ c.partners.toList, CapNP sp fs x.1 z) { c with partners := #[] } c₁)
    (hP : ∀ x ∈ c.partners.toList,
      Passed sp fs env c₁.located (· ∈ c₁.pending) (· ∈ c₁.partners) x.1 x.2) :
    CapInv sp fs env L' c₁ (D ++ c.partners.toList) := by
  have hreach : ∀ x ∈ c.partners.toList, Reached sp fs env.wr x.1 := fun x hx =>
    (hI.reads x (.inr (Array.mem_toList_iff.1 hx))).1
  refine ⟨h1, st.views hI.views, by rw [hctx, hhomes]; exact hI.size, fun x hx => ?_,
    fun k d h hd hh => ?_, fun y s hs => ?_, fun z hz => ?_,
    fun cl hcl => (hI.clashes cl hcl).mono st.pend⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact (hI.passed x hx).mono st.loc_keep st.pend fun z hz =>
        hz.elim (fun h => .inl (List.mem_append_left _ h))
          (fun h => .inl (List.mem_append_right _ (Array.mem_toList_iff.2 h)))
    · exact (hP x hx).mono (fun _ _ h => h) (fun _ h => h) fun z hz => .inr hz
  · rw [hctx] at hd; rw [hhomes] at hh
    obtain ⟨a, ⟨x, hx, s, hs, hm, hra⟩, b, e⟩ := hI.records k d h hd hh
    refine ⟨fun y hy => List.mem_append_left _ (a y hy),
      ⟨x, hx, s, copyOf_mono st.loc_keep hs, hm, hra⟩,
      fun n hn => (b n hn).imp fun s hs => ⟨copyOf_mono st.loc_keep hs.1, hs.2⟩,
      fun n hn cs hcs kc hk y hy => .inl ?_⟩
    rcases e n hn cs hcs kc hk y hy with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (Array.mem_toList_iff.2 h)
  · rcases st.loc_new y s hs with h | ⟨x, hx, himp, v, t, hv, ht, hst, hnm⟩
    · exact hI.located y s h
    · refine ⟨himp, ?_, hnm⟩
      rw [show s.part.mod = t.part.mod by rw [hst]]
      exact .view (hreach x hx) hv ht
  · rcases hz with hz | hz
    · rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨a, b⟩ := hI.reads z (.inl hz)
        exact ⟨a, by rw [hctx, hhomes]; exact b⟩
      · obtain ⟨a, b⟩ := hI.reads z (.inr (Array.mem_toList_iff.1 hz))
        exact ⟨a, by rw [hctx, hhomes]; exact b⟩
    · rcases st.part_new z hz with h | ⟨x, hx, v, y, s₂, hv, hs, hnew⟩
      · simp at h
      · refine ⟨?_, .inr (.inl ⟨x.1, v, y, s₂, hv, hs, hnew⟩)⟩
        rw [hnew.1]
        exact .view (hreach x hx) hv hs

/-- A record added: the invariant kept. -/
theorem CapInv.add (hsize : env.wr.index.parts.size ≤ env.wr.loads.order.size)
    (hcop : env.copies = clashCopiesOf env.wr)
    (hcm : ∀ cl ∈ env.wr.clashes, ∀ x ∈ cl.copies, x.1.mod < env.wr.loads.order.size)
    {L L' : ReachLog} {c c₁ c₂ c₃ : ReachCache} {D : List (Name × Name)}
    {d : Declaration} {h x : Name} {s : Spot}
    (hI : CapInv sp fs env L c D) (hctx : L'.ctx = L.ctx.push d) (hhomes : L'.homes = L.homes.push h)
    (f1 : Fr c c₁) (hx : x ∈ declNames d) (hcp : copyOf env c.located x = some s)
    (hh : h = s.part.mod) (hra : ReadAt sp fs d s)
    (st2 : Step sp fs (CapNL sp fs env h) (CapNP sp fs h) c₁ c₂)
    (hP2 : ∀ y ∈ (recordReads d).toList,
      Passed sp fs env c₂.located (· ∈ c₂.pending) (· ∈ c₂.partners) h y)
    (h3 : CacheOk sp fs c₃) (st3 : Step sp fs (StoredNL env h) (fun _ => False) c₂ c₃)
    (hS : ∀ n ∈ declNames d, ∃ s, copyOf env c₃.located n = some s ∧ s.part.mod = h) :
    CapInv sp fs env L' { c₃ with partners := c₃.partners ++ clashPartners env (declNames d) }
      (D ++ (recordReads d).toList.map (h, ·)) := by
  let NL : Name → Spot → Prop := fun y s => CapNL sp fs env h y s ∨ StoredNL env h y s
  let NP : Name × Name → Prop := fun z => CapNP sp fs h z ∨ z ∈ clashPartners env (declNames d)
  have T3 : Step sp fs NL NP c₂ { c₃ with partners := c₃.partners ++ clashPartners env (declNames d) } :=
    (st3.mono (fun _ _ h => .inr h) (fun _ h => h.elim)).trans
      (Step.partners_append fun z hz => .inr hz)
  have T : Step sp fs NL NP c { c₃ with partners := c₃.partners ++ clashPartners env (declNames d) } :=
    (Step.ofFr f1).trans ((st2.mono (fun _ _ h => .inl h) (fun _ h => .inl h)).trans T3)
  have hRh : Reached sp fs env.wr h := hh ▸ copyOf_reached hsize (fun y s h => (hI.located y s h).2.1) hcp
  have hk : ∀ {k : Nat} {e : Declaration} {g : Name}, L'.ctx[k]? = some e → L'.homes[k]? = some g →
      (L.ctx[k]? = some e ∧ L.homes[k]? = some g) ∨ (k = L.ctx.size ∧ e = d ∧ g = h) := by
    intro k e g he hg
    rw [hctx, Array.getElem?_push] at he
    rw [hhomes, Array.getElem?_push] at hg
    by_cases hks : k = L.ctx.size
    · simp only [hks, ↓reduceIte, Option.some.injEq] at he
      simp only [hks, hI.size, ↓reduceIte, Option.some.injEq] at hg
      exact .inr ⟨hks, he.symm, hg.symm⟩
    · simp only [hks, ↓reduceIte] at he
      simp only [show k ≠ L.homes.size by rw [← hI.size]; exact hks, ↓reduceIte] at hg
      exact .inl ⟨he, hg⟩
  have hnew : L'.ctx[L.ctx.size]? = some d ∧ L'.homes[L.ctx.size]? = some h := by
    rw [hctx, hhomes, Array.getElem?_push, Array.getElem?_push]
    simp [hI.size]
  have horig : ∀ {z}, Origin sp fs env L.ctx L.homes z → Origin sp fs env L'.ctx L'.homes z := by
    intro z o; rw [hctx, hhomes]; exact o.push hI.size
  have hmemP : ∀ {z}, z ∈ D ∨ z ∈ c.partners →
      z ∈ D ++ (recordReads d).toList.map (h, ·) ∨
        z ∈ c₃.partners ++ clashPartners env (declNames d) := fun hz =>
    hz.elim (fun h => .inl (List.mem_append_left _ h)) (fun h => .inr (T.part_keep _ h))
  refine ⟨h3.partners _, T.views hI.views, by rw [hctx, hhomes]; simp [hI.size],
    fun z hz => ?_, fun k e g he hg => ?_, fun y s' hs' => ?_, fun z hz => ?_,
    fun cl hcl => (hI.clashes cl hcl).mono T.pend⟩
  · rcases List.mem_append.1 hz with hz | hz
    · exact (hI.passed z hz).mono T.loc_keep T.pend fun _ h => hmemP h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      exact (hP2 y hy).mono T3.loc_keep T3.pend fun _ h => .inr (T3.part_keep _ h)
  · rcases hk he hg with ⟨he', hg'⟩ | ⟨-, rfl, rfl⟩
    · obtain ⟨a, ⟨x', hx', s'', hs'', hm, hra'⟩, b, e'⟩ := hI.records k e g he' hg'
      refine ⟨fun y hy => List.mem_append_left _ (a y hy),
        ⟨x', hx', s'', copyOf_mono T.loc_keep hs'', hm, hra'⟩,
        fun n hn => (b n hn).imp fun s hs => ⟨copyOf_mono T.loc_keep hs.1, hs.2⟩,
        fun n hn cs hcs kc hk' y hy => hmemP (e' n hn cs hcs kc hk' y hy)⟩
    · refine ⟨fun y hy => List.mem_append_right _
          (List.mem_map.2 ⟨y, Array.mem_toList_iff.2 hy, rfl⟩),
        ⟨x, hx, s, copyOf_mono T.loc_keep hcp, hh.symm, hra⟩, hS,
        fun n hn cs hcs kc hk' y hy => .inr ?_⟩
      refine Array.mem_append.2 (.inr ?_)
      unfold clashPartners
      exact (mem_clashPartners (env := env) _ #[]).2 (.inr ⟨n, hn, cs, hcs, kc, hk', rfl, hy⟩)
  · rcases T.loc_new y s' hs' with h' | h' | ⟨himp, hp⟩
    · exact hI.located y s' h'
    · obtain ⟨himp, v, t, hv, ht, hst, hnm⟩ := h'
      refine ⟨himp, ?_, hnm⟩
      rw [show s'.part.mod = t.part.mod by rw [hst]]
      exact .view hRh hv ht
    · refine ⟨himp, ?_, hp.2⟩
      rw [show s'.part.mod = h by rw [hp.1]]
      exact hRh
  · rcases hz with hz | hz
    · rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨a, b⟩ := hI.reads z (.inl hz)
        exact ⟨a, horig b⟩
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
        exact ⟨hRh, .inl ⟨L.ctx.size, d, hnew.1, hnew.2, Array.mem_toList_iff.1 hy⟩⟩
    · rcases T.part_new z hz with h' | h' | h'
      · obtain ⟨a, b⟩ := hI.reads z (.inr h')
        exact ⟨a, horig b⟩
      · obtain ⟨v, y, s₂, hv, hs, hnw⟩ := h'
        refine ⟨?_, .inr (.inl ⟨h, v, y, s₂, hv, hs, hnw⟩)⟩
        rw [hnw.1]
        exact .view hRh hv hs
      · unfold clashPartners at h'
        rcases (mem_clashPartners (env := env) _ #[]).1 h' with h' | ⟨n, hn, cs, hcs, kc, hk', h1, h2⟩
        · simp at h'
        · refine ⟨h1 ▸ copies_reached hcop hcm hcs hk',
            .inr (.inr ⟨L.ctx.size, d, hnew.1, n, hn, cs, hcs, kc, hk', h1, h2⟩)⟩

end

section
variable {sp : SearchPath} {fs : FS} {env : ReachEnv ModelIO}

/-- **The worklist keeps the capture invariant**, and ends with every partner read checked. -/
theorem reachGo_capture (he : EnvOk sp fs env)
    (hsize : env.wr.index.parts.size ≤ env.wr.loads.order.size)
    (hcop : env.copies = clashCopiesOf env.wr)
    (hcm : ∀ cl ∈ env.wr.clashes, ∀ x ∈ cl.copies, x.1.mod < env.wr.loads.order.size) :
    ∀ (fuel : Nat) (L : ReachLog) (c : ReachCache) (D : List (Name × Name)),
      CapInv sp fs env L c D → ∀ {hs₀ : HS},
      ModelIO.AllOk (reachGo env fuel L c) fs hs₀ fun r =>
        ∀ L' c', r = .ok (L', c') → ∃ D', CapInv sp fs env L' c' D' ∧ c'.partners = #[] := by
  intro fuel
  induction fuel with
  | zero =>
    intro L c D hI _
    rw [reachGo]
    split
    · split
      · rename_i _ hemp
        simp only [ModelIO.allOk_pure]
        intro L' c' h; cases h
        exact ⟨D, hI, by simpa using hemp⟩
      · simp
    · simp
  | succ fuel ih =>
    intro L c D hI _
    rw [reachGo]
    split
    · split
      · rename_i _ hemp
        simp only [ModelIO.allOk_pure]
        intro L' c' h; cases h
        exact ⟨D, hI, by simpa using hemp⟩
      · simp only [ModelIO.allOk_bind]
        intro z _ hz
        obtain ⟨h1, st, hP⟩ := capturePairs_st he { c with partners := #[] } c.partners.toList
          (hI.cache.partners #[]) hI.views z _ hz
        obtain ⟨c₁, r⟩ := z
        cases r with
        | error e => simp
        | ok u =>
          simp only []
          apply ih
          exact hI.pairs rfl rfl h1 st (hP rfl)
    · rename_i x rest hs
      simp only []
      split
      · apply ih (D := D)
        exact ⟨hI.cache, hI.views, hI.size, hI.passed, hI.records, hI.located, hI.reads,
          hI.clashes⟩
      · simp only [ModelIO.allOk_bind]
        intro z _ hz
        obtain ⟨f1, hrd⟩ := readRecord_at he hI.cache x z _ hz
        have hc1 := (readRecord_ok he hI.cache x z _ hz).1
        obtain ⟨c₁, r⟩ := z
        cases r with
        | error e => simp
        | ok p =>
          obtain ⟨d, h⟩ := p
          obtain ⟨s, hcp, hh, hra⟩ := hrd d h rfl
          simp only []
          split
          · simp
          · rename_i hxn
            split
            · simp
            · simp only [ModelIO.allOk_bind]
              intro z _ hz
              obtain ⟨h2, st2, hP2⟩ := captureAll_st he h c₁ _ hc1
                (fun h v hh => hI.views h v (f1.2.2.2 ▸ hh)) z _ hz
              obtain ⟨c₂, r⟩ := z
              cases r with
              | error e => simp
              | ok u =>
                simp only [ModelIO.allOk_bind]
                intro z _ hz
                have h3 := storedNamesOk_ok he h c₂ _ h2 z _ hz
                obtain ⟨st3, hS⟩ := storedNamesOk_st he h c₂ _ h2 z _ hz
                obtain ⟨c₃, r⟩ := z
                cases r with
                | error e => simp
                | ok u =>
                  apply ih
                  exact hI.add hsize hcop hcm rfl rfl f1 (by simpa using hxn) hcp hh hra st2
                    (hP2 rfl) h3 st3 (hS rfl)

end

/-! ## The reach -/

/-- **What the capture check established, at an accepting outcome of the reach** (see the module
docstring): over the final completions `loc`, the recorded inferences `pend` and the checked
reads `P`, every context record is read at its copy, which is its home's, and so is every name it
stores (C1); every read of it is checked (C2); every checked read passed (C3); the clash names'
copies' statements are read as their modules read them (C4); the clash rule passed (C5); the
inferences hold at the context (C6); every completion is a private copy of a reached module
with no importer copy (C7); and every checked read is a reached module's, from a record's read, a
partner copy of a reached module's view, or a clash name's copy (C8). -/
theorem reach_capture {sp : SearchPath} {fs : FS} {m : Name} {wr : WorkerReads}
    {own : Std.HashSet Name} {roots : Array Name} {r : Reach}
    (hparts : ∀ i t, wr.index.parts[i]? = some t →
      PartNames sp fs ⟨wr.loads.nameAt i, ((wr.loads.flags[i]?).getD default).level⟩ t)
    (hindex : ∀ m i, wr.loads.index[m]? = some i → wr.loads.nameAt i = m)
    (hsize : wr.index.parts.size ≤ wr.loads.order.size)
    (hcm : ∀ cl ∈ wr.clashes, ∀ x ∈ cl.copies, x.1.mod < wr.loads.order.size)
    {hs hs' : HS} (h : (reach (.ofPath sp) m wr own roots : ModelIO _) fs hs (.ok (.ok r)) hs') :
    let env : ReachEnv ModelIO := { rd := .ofPath sp, mod := m, wr, own, copies := clashCopiesOf wr }
    ∃ (loc : Std.HashMap Name Spot) (pend : List (String × Name × ConstantVal))
      (P : List (Name × Name)),
      r.ctx.size = r.homes.size ∧
      (∀ (k : Nat) (d : Declaration) (hm : Name), r.ctx[k]? = some d → r.homes[k]? = some hm →
        (∃ x ∈ declNames d, ∃ s, copyOf env loc x = some s ∧ s.part.mod = hm ∧ ReadAt sp fs d s) ∧
        (∀ n ∈ declNames d, ∃ s, copyOf env loc n = some s ∧ s.part.mod = hm) ∧
        (∀ y ∈ recordReads d, (hm, y) ∈ P) ∧
        (∀ n ∈ declNames d, ∀ cs, env.copies[n]? = some cs → ∀ kc ∈ cs,
          ∀ y ∈ (needsGo {} #[] kc.2.type).2, (kc.1, y) ∈ P)) ∧
      (∀ x ∈ P, Passed sp fs env loc (· ∈ pend) (· ∈ P) x.1 x.2) ∧
      (∀ cl ∈ wr.clashes, ClashOk sp fs wr (· ∈ pend) cl) ∧
      inferFlags r.ctx.toList pend = .ok () ∧
      (∀ (y : Name) (s : Spot), loc[y]? = some s → importerSpot env y = none ∧ s.part.level = .private ∧
        CopyAt sp fs s ∧ Reached sp fs wr s.part.mod ∧ s.pos.name = y) ∧
      (∀ x ∈ P, Reached sp fs wr x.1 ∧ Origin sp fs env r.ctx r.homes x) := by
  intro env
  have he : EnvOk sp fs env := ⟨rfl, hparts, hindex⟩
  unfold reach at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨⟨c, x⟩, _, hx, h⟩ := h
  have hc := clashAgree_ok he {} _ #[] (CacheOk.empty sp fs) _ _ hx
  obtain ⟨st0, hcl0⟩ := clashAgree_st he {} wr.clashes.toList #[] (CacheOk.empty sp fs) _ _ hx
  rcases x with e | extra
  · simp at h
  have hcl := hcl0 extra rfl
  simp only at h
  generalize List.find? _ _ = q at h
  cases q with
  | some x => simp at h
  | none =>
    simp only [ModelIO.bind_ok] at h
    obtain ⟨y, _, hy, h⟩ := h
    have hI0 : ∀ rs, CapInv sp fs env (ReachLog.init rs) c [] := by
      intro rs
      refine ⟨hc, st0.views (fun h v hh => by simp at hh), by simp [ReachLog.init],
        fun x hx => (by cases hx), fun k d h hd _ => (by simp [ReachLog.init] at hd),
        fun y s hs => ?_, fun z hz => ?_,
        fun cl hcl' => hcl cl (Array.mem_toList_iff.2 hcl')⟩
      · rcases st0.loc_new y s hs with h | h
        · simp at h
        · exact h.elim
      · rcases hz with hz | hz
        · cases hz
        · rcases st0.part_new z hz with h | h
          · simp at h
          · exact h.elim
    have hG := reachGo_capture he hsize rfl hcm _ _ c [] (hI0 _) y _ hy
    rcases y with e | ⟨L, c'⟩
    · simp at h
    obtain ⟨D, hI, hpe⟩ := hG L c' rfl
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
    have hperm := (readOrder_spec ho).1
    -- a context position is a position of the worklist's records
    have hfwd : ∀ (k : Nat) (d : Declaration) (hm : Name), (o.map (L.ctx.getD · default))[k]? = some d →
        (o.map (L.homes.getD · default))[k]? = some hm →
        L.ctx[o[k]!]? = some d ∧ L.homes[o[k]!]? = some hm := by
      intro k d hm h1 h2
      simp only [Array.getElem?_map] at h1 h2
      cases hoi : o[k]? with
      | none => simp [hoi] at h1
      | some j =>
      simp only [hoi, Option.map_some, Option.some.injEq] at h1 h2
      have hj : j < L.ctx.size := List.mem_range.1 (hperm.mem_iff.1
        (Array.mem_toList_iff.2 (Array.mem_of_getElem? hoi)))
      have hok : o[k]! = j := by
        rw [getElem!_pos o k (Array.getElem?_eq_some_iff.1 hoi).1]
        exact (Array.getElem?_eq_some_iff.1 hoi).2
      rw [hok]
      refine ⟨?_, ?_⟩
      · rw [← h1, Array.getElem?_eq_getElem hj]; simp [hj]
      · rw [← h2, Array.getElem?_eq_getElem (hI.size ▸ hj)]; simp [hI.size ▸ hj]
    have hback : ∀ (j : Nat) (d : Declaration) (hm : Name), L.ctx[j]? = some d → L.homes[j]? = some hm →
        ∃ k : Nat, (o.map (L.ctx.getD · default))[k]? = some d ∧
          (o.map (L.homes.getD · default))[k]? = some hm := by
      intro j d hm h1 h2
      have hj : j < L.ctx.size := (Array.getElem?_eq_some_iff.1 h1).1
      obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 hj))
      have hk' : k < o.size := by simpa using hk
      have hoi : o[k]? = some j := by
        rw [Array.getElem?_eq_getElem hk']; simpa using hkj
      refine ⟨k, ?_, ?_⟩
      · simp only [Array.getElem?_map, hoi, Option.map_some]
        rw [Array.getD_eq_getD_getElem?, h1]; rfl
      · simp only [Array.getElem?_map, hoi, Option.map_some]
        rw [Array.getD_eq_getD_getElem?, h2]; rfl
    have horig : ∀ z, Origin sp fs env L.ctx L.homes z →
        Origin sp fs env (o.map (L.ctx.getD · default)) (o.map (L.homes.getD · default)) z := by
      intro z hz
      rcases hz with ⟨j, d, h1, h2, h3⟩ | hz | ⟨j, d, h1, n, hn, cs, hcs, kc, hk, h4, h5⟩
      · obtain ⟨k, hk1, hk2⟩ := hback j d _ h1 h2
        exact .inl ⟨k, d, hk1, hk2, h3⟩
      · exact .inr (.inl hz)
      · have h2 : L.homes[j]? = some (L.homes.getD j default) := by
          have hj : j < L.homes.size := hI.size ▸ (Array.getElem?_eq_some_iff.1 h1).1
          rw [Array.getElem?_eq_getElem hj]; simp [hj]
        obtain ⟨k, hk1, -⟩ := hback j d _ h1 h2
        exact .inr (.inr ⟨k, d, hk1, n, hn, cs, hcs, kc, hk, h4, h5⟩)
    have hmemD : ∀ {z}, z ∈ D ∨ z ∈ c'.partners → z ∈ D := fun hz =>
      hz.elim id fun h => by rw [hpe] at h; simp at h
    refine ⟨c'.located, c'.pending.toList, D, by simp, fun k d hm h1 h2 => ?_,
      fun x hx => (hI.passed x hx).mono (fun _ _ h => h) (fun _ h => Array.mem_toList_iff.2 h)
        (fun _ h => hmemD h),
      fun cl hcl' => (hI.clashes cl hcl').mono fun _ h => Array.mem_toList_iff.2 h, by cases u'; exact hf,
      fun y s hs => ?_, fun x hx => ?_⟩
    · obtain ⟨h1', h2'⟩ := hfwd k d hm h1 h2
      obtain ⟨a, b, c₁, e⟩ := hI.records _ d hm h1' h2'
      exact ⟨b, c₁, a, fun n hn cs hcs kc hk y hy => hmemD (e n hn cs hcs kc hk y hy)⟩
    · obtain ⟨a, b, nm⟩ := hI.located y s hs
      obtain ⟨c₁, d₁⟩ := hI.cache.located y s hs
      exact ⟨a, c₁, d₁, b, nm⟩
    · obtain ⟨a, b⟩ := hI.reads x (.inl hx)
      exact ⟨a, horig x b⟩

end ConLeche.Driver
