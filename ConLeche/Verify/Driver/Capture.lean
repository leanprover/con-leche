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
module, or both proofs of one statement, the names of `s₂`'s statement read as reads of its
module (`P`), an inference recorded (`pend`) where a status asks it. -/
@[expose] def AgreeOk (sp : SearchPath) (fs : FS) (pend : String × Name × ConstantVal → Prop)
    (P : Name × Name → Prop) (y : Name) (s₁ s₂ : Spot) : Prop :=
  s₁.part.mod = s₂.part.mod ∨
    ∃ (r₁ : Region) (cv₁ : ConstantVal) (k₁ : CKindF Name Unit) (r₂ : Region) (cv₂ : ConstantVal)
      (k₂ : CKindF Name Unit) (p₁ p₂ : ProofStatus),
      PartRegion sp fs s₁.part r₁ ∧ StmtSkel r₁ s₁.pos.loc cv₁ k₁ ∧
      PartRegion sp fs s₂.part r₂ ∧ StmtSkel r₂ s₂.pos.loc cv₂ k₂ ∧
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
  rcases h with h | ⟨r₁, cv₁, k₁, r₂, cv₂, k₂, p₁, p₂, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12⟩
  · exact .inl h
  · exact .inr ⟨r₁, cv₁, k₁, r₂, cv₂, k₂, p₁, p₂, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
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

end ConLeche.Driver
