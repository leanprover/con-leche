module

public import ConLeche.Driver.Reach

/-!
# Reads answered from tables, in the model

A worker's reads of the files go through `OleanReads` (`ConLeche/Frontend/Olean/Files.lean`): a
module's imports, a view's files, a part's name positions.  The worker reads them on the search
path (`OleanReads.ofPath sp`); the one-process mode (`ConLeche/Driver/Modular.lean`) answers them
from tables it read once up front, and where a table has nothing, by the same read.

**Refinement** (`ModelIO.Within fs a b`): every outcome of `a` on the snapshot `fs` is one of `b`.
The reads `rd` refine the search path's (`OleanReads.Within fs rd sp`) when each of their three
operations does.  Then every phase of the worker written over `rd` refines the same phase over
the search path (`headerFixpoint_within`, `workerReads_within`, `readHome_within`,
`reach_within`), because each is built from the reads by binds, matches and the parallel map,
all of which keep refinement (`Within.bind`, `mapExcept_within`).  So whatever a phase over the
tables accepts, the same phase over the files accepts too, and what is proved of the worker's
accepting outcomes holds of the one-process mode's (`ConLeche/Verify/Driver/Worker.lean`).
-/

public section

namespace ConLeche

/-- **`a` refines `b` on the snapshot `fs`**: every outcome of `a` there is one of `b`. -/
@[expose] def ModelIO.Within {α : Type} (fs : FS) (a b : ModelIO α) : Prop := ∀ o, a fs o → b fs o

namespace ModelIO.Within

variable {fs : FS}

theorem refl {α : Type} (a : ModelIO α) : Within fs a a := fun _ h => h

theorem trans {α : Type} {a b c : ModelIO α} (h₁ : Within fs a b) (h₂ : Within fs b c) :
    Within fs a c := fun o h => h₂ o (h₁ o h)

theorem bind {α β : Type} {a b : ModelIO α} {f g : α → ModelIO β} (ha : Within fs a b)
    (hf : ∀ x, Within fs (f x) (g x)) : Within fs (a >>= f) (b >>= g) := by
  intro o h
  rcases h with ⟨x, hx, h⟩ | ⟨e, rfl, he⟩
  · exact Or.inl ⟨x, ha _ hx, hf x _ h⟩
  · exact Or.inr ⟨e, rfl, ha _ he⟩

theorem bind_left {α β : Type} {a b : ModelIO α} (f : α → ModelIO β) (ha : Within fs a b) :
    Within fs (a >>= f) (b >>= f) := bind ha fun _ => refl _

theorem ite {α : Type} {c : Prop} [Decidable c] {a a' b b' : ModelIO α}
    (h₁ : c → Within fs a a') (h₂ : ¬c → Within fs b b') :
    Within fs (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h₁ hc
  · simp only [hc, ↓reduceIte]; exact h₂ hc

theorem ok_of {α : Type} {a b : ModelIO α} (h : Within fs a b) {v : α} (hv : a fs (.ok v)) :
    b fs (.ok v) := h _ hv

end ModelIO.Within

/-- The sequential map with a stop keeps refinement. -/
theorem mapExcept_within {fs : FS} {α β ε : Type} {f g : α → ModelIO (Except ε β)}
    (h : ∀ x, ModelIO.Within fs (f x) (g x)) :
    ∀ xs, ModelIO.Within fs (mapExcept f xs) (mapExcept g xs)
  | [] => ModelIO.Within.refl _
  | x :: xs => by
    simp only [mapExcept]
    refine ModelIO.Within.bind (h x) fun r => ?_
    rcases r with e | b
    · exact ModelIO.Within.refl _
    · exact ModelIO.Within.bind (mapExcept_within h xs) fun r => ModelIO.Within.refl _

/-- The parallel map with a stop keeps refinement (in the model it is the sequential map). -/
theorem parMapExcept_within {fs : FS} {α β ε : Type} {f g : α → ModelIO (Except ε β)}
    (h : ∀ x, ModelIO.Within fs (f x) (g x)) (jobs jobs' : Nat) (xs : List α) :
    ModelIO.Within fs (CheckerIO.parMapExcept jobs f xs) (CheckerIO.parMapExcept jobs' g xs) :=
  mapExcept_within h xs

namespace Frontend.Olean

/-- **Reads that refine the search path's**: each of the three operations' outcomes, on the
snapshot, is one of the read of the files on `sp`. -/
structure OleanReads.Within (fs : FS) (rd : OleanReads ModelIO) (sp : SearchPath) : Prop where
  imports : ∀ m, ModelIO.Within fs (rd.imports m) (moduleImports sp m)
  files : ∀ m level, ModelIO.Within fs (rd.files m level) (readFiles sp m level)
  names : ∀ x, ModelIO.Within fs (rd.names x) (readPartNames sp x)

/-- The search path's reads refine themselves. -/
theorem OleanReads.Within.ofPath (fs : FS) (sp : SearchPath) :
    OleanReads.Within fs (OleanReads.ofPath sp) sp :=
  ⟨fun _ => ModelIO.Within.refl _, fun _ _ => ModelIO.Within.refl _,
    fun _ => ModelIO.Within.refl _⟩

/-! ## The header fixpoint -/

theorem levelsGo_within {fs : FS} {imps imps' : Name → ModelIO (Except CheckError (Array ImportRec))}
    (h : ∀ m, ModelIO.Within fs (imps m) (imps' m)) (gPriv : Bool) :
    ∀ fuel ws st, ModelIO.Within fs (levelsGo imps gPriv fuel ws st)
      (levelsGo imps' gPriv fuel ws st)
  | _, [], st => by simp only [levelsGo]; exact ModelIO.Within.refl _
  | 0, _ :: _, _ => by simp only [levelsGo]; exact ModelIO.Within.refl _
  | fuel + 1, .done m fl :: rest, st => by
    simp only [levelsGo]
    exact levelsGo_within h gPriv fuel _ _
  | fuel + 1, .imp pf i :: rest, st => by
    simp only [levelsGo]
    split
    · exact levelsGo_within h gPriv fuel _ _
    · split
      · split
        · exact levelsGo_within h gPriv fuel _ _
        · exact levelsGo_within h gPriv fuel _ _
      · split
        · exact ModelIO.Within.refl _
        · refine ModelIO.Within.bind (h _) fun r => ?_
          rcases r with e | is
          · exact ModelIO.Within.refl _
          · exact levelsGo_within h gPriv fuel _ _

theorem headerFixpoint_within {fs : FS}
    {imps imps' : Name → ModelIO (Except CheckError (Array ImportRec))}
    (h : ∀ m, ModelIO.Within fs (imps m) (imps' m)) (isModule : Bool) (imports : Array ImportRec) :
    ModelIO.Within fs (headerFixpoint imps isModule imports)
      (headerFixpoint imps' isModule imports) := by
  simp only [headerFixpoint]
  exact ModelIO.Within.bind_left _ (levelsGo_within h _ _ _ _)

/-! ## The worker's reads and its home -/

theorem readInfosOf_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (ld : Loads) (ix : NameIndex) (x : Nat × Array Copy) :
    ModelIO.Within fs (readInfosOf rd ld ix x) (readInfosOf (.ofPath sp) ld ix x) := by
  simp only [readInfosOf]
  exact ModelIO.Within.bind_left _ (h.files _ _)

theorem readInfos_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (ld : Loads) (ix : NameIndex) (jobs : Nat) (cs : Array Copy) :
    ModelIO.Within fs (readInfos rd ld ix jobs cs) (readInfos (.ofPath sp) ld ix jobs cs) := by
  simp only [readInfos]
  exact ModelIO.Within.bind_left _ (parMapExcept_within (readInfosOf_within h ld ix) _ _ _)

theorem workerReads_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (m : Name) (jobs : Nat) :
    ModelIO.Within fs (workerReads rd m jobs) (workerReads (.ofPath sp) m jobs) := by
  simp only [workerReads]
  refine ModelIO.Within.bind (h.names _) fun r => ?_
  rcases r with e | own
  · exact ModelIO.Within.refl _
  refine ModelIO.Within.bind (headerFixpoint_within h.imports _ _) fun r => ?_
  rcases r with e | ld
  · exact ModelIO.Within.refl _
  refine ModelIO.Within.bind (parMapExcept_within h.names _ _ _) fun r => ?_
  rcases r with e | parts
  · exact ModelIO.Within.refl _
  simp only
  split
  · exact ModelIO.Within.refl _
  refine ModelIO.Within.bind (readInfos_within h _ _ _ _) fun r => ?_
  rcases r with e | infos
  · exact ModelIO.Within.refl _
  exact ModelIO.Within.bind (readInfos_within h _ _ _ _) fun r => ModelIO.Within.refl _

theorem readHome_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (m : Name) (i : Nat) :
    ModelIO.Within fs (readHome rd m i) (readHome (.ofPath sp) m i) := by
  simp only [readHome]
  exact ModelIO.Within.bind_left _ (h.files _ _)

end Frontend.Olean


namespace Driver

open Frontend.Olean

/-- The reach's environment with its reads on the search path. -/
@[expose] def ReachEnv.onPath (env : ReachEnv ModelIO) (sp : SearchPath) : ReachEnv ModelIO :=
  { env with rd := .ofPath sp }

/-- Peel a phase written over the reads: a callee's refinement (the terms given), the same
action on both sides, a bind, a match or an `if` on one value. -/
local syntax "within_tac" "[" term,* "]" : tactic
macro_rules
  | `(tactic| within_tac [$ts,*]) => `(tactic| repeat' (first
      $[| apply $ts:term]*
      | exact ModelIO.Within.refl _
      | (refine ModelIO.Within.bind ?_ fun _ => ?_)
      | (refine ModelIO.Within.ite (fun _ => ?_) (fun _ => ?_))
      | split))

section
variable {fs : FS} {env : ReachEnv ModelIO} {sp : SearchPath}

theorem tableOf_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (k : PartKey) :
    ModelIO.Within fs (tableOf env c k) (tableOf (env.onPath sp) c k) := by
  simp only [tableOf, ReachEnv.onPath]
  within_tac [h.names]

theorem lookOf_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (k : PartKey) :
    ModelIO.Within fs (lookOf env c k) (lookOf (env.onPath sp) c k) := by
  simp only [lookOf]
  within_tac [tableOf_within h]

theorem withPart_within (h : OleanReads.Within fs env.rd sp) {α : Type} (c : ReachCache)
    (k : PartKey) (f : Region → SM → Option (SM × α)) :
    ModelIO.Within fs (withPart env c k f) (withPart (env.onPath sp) c k f) := by
  simp only [withPart, ReachEnv.onPath]
  within_tac [h.files]

theorem stmtAt_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (s : Spot) :
    ModelIO.Within fs (stmtAt env c s) (stmtAt (env.onPath sp) c s) := by
  simp only [stmtAt]
  exact withPart_within h _ _ _

theorem privSpot_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (s : Spot) :
    ModelIO.Within fs (privSpot env c s) (privSpot (env.onPath sp) c s) := by
  simp only [privSpot]
  within_tac [lookOf_within h]

theorem viewAdd_within (h : OleanReads.Within fs env.rd sp) :
    ∀ (c : ReachCache) (v : Std.HashMap Name Spot) (ks : List PartKey),
      ModelIO.Within fs (viewAdd env c v ks) (viewAdd (env.onPath sp) c v ks)
  | c, v, [] => by simp only [viewAdd]; exact ModelIO.Within.refl _
  | c, v, k :: ks => by
    simp only [viewAdd]
    within_tac [tableOf_within h, viewAdd_within h]

theorem viewOf_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (m : Name) :
    ModelIO.Within fs (viewOf env c m) (viewOf (env.onPath sp) c m) := by
  simp only [viewOf]
  within_tac [tableOf_within h, viewAdd_within h, headerFixpoint_within h.imports]

theorem locate_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (m y : Name) :
    ModelIO.Within fs (locate env c m y) (locate (env.onPath sp) c m y) := by
  simp only [locate]
  within_tac [viewOf_within h]

theorem proofStatus_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (s : Spot)
    (k : CKindF Name Unit) :
    ModelIO.Within fs (proofStatus env c s k) (proofStatus (env.onPath sp) c s k) := by
  simp only [proofStatus]
  within_tac [privSpot_within h]

theorem keyCheck_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (m y : Name)
    (s₁ s₂ : Spot) :
    ModelIO.Within fs (keyCheck env c m y s₁ s₂) (keyCheck (env.onPath sp) c m y s₁ s₂) := by
  simp only [keyCheck]
  within_tac [stmtAt_within h, proofStatus_within h]

theorem statuses_within (h : OleanReads.Within fs env.rd sp) :
    ∀ (c : ReachCache) (xs : List (Spot × ConstantVal × CKindF Name Unit)) (acc : List ProofStatus),
      ModelIO.Within fs (clashKeys.statuses env c xs acc)
        (clashKeys.statuses (env.onPath sp) c xs acc)
  | c, [], acc => by simp only [clashKeys.statuses]; exact ModelIO.Within.refl _
  | c, x :: xs, acc => by
    simp only [clashKeys.statuses]
    within_tac [proofStatus_within h, statuses_within h]

theorem clashKeys_within (h : OleanReads.Within fs env.rd sp) :
    ∀ (c : ReachCache) (cls : List Clash) (acc : Array Name),
      ModelIO.Within fs (clashKeys env c cls acc) (clashKeys (env.onPath sp) c cls acc)
  | c, [], acc => by simp only [clashKeys]; exact ModelIO.Within.refl _
  | c, cl :: cls, acc => by
    simp only [clashKeys]
    simp only [ReachEnv.onPath]
    within_tac [statuses_within h, clashKeys_within h]

theorem inExported_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (m : Name)
    (level : OLeanLevel) (y : Name) :
    ModelIO.Within fs (inExported env c m level y) (inExported (env.onPath sp) c m level y) := by
  simp only [inExported]
  within_tac [lookOf_within h]

theorem captureOne_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (m y : Name) :
    ModelIO.Within fs (captureOne env c m y) (captureOne (env.onPath sp) c m y) := by
  simp only [captureOne]
  have he : importerSpot (env.onPath sp) y = importerSpot env y := rfl
  have hw : (env.onPath sp).wr = env.wr := rfl
  have ho : (env.onPath sp).own = env.own := rfl
  have hm : (env.onPath sp).mod = env.mod := rfl
  rw [he, hw, ho, hm]
  within_tac [inExported_within h, locate_within h, keyCheck_within h, privSpot_within h]

theorem captureAll_within (h : OleanReads.Within fs env.rd sp) (m : Name) :
    ∀ (c : ReachCache) (ys : List Name),
      ModelIO.Within fs (captureAll env m c ys) (captureAll (env.onPath sp) m c ys)
  | c, [] => by simp only [captureAll]; exact ModelIO.Within.refl _
  | c, y :: ys => by
    simp only [captureAll]
    within_tac [captureOne_within h, captureAll_within h]

theorem recBlocksOf_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (k : PartKey) :
    ModelIO.Within fs (recBlocksOf env c k) (recBlocksOf (env.onPath sp) c k) := by
  simp only [recBlocksOf]
  within_tac [tableOf_within h, withPart_within h]

theorem groupAt_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (k : PartKey)
    (n : Name) :
    ModelIO.Within fs (groupAt env c k n) (groupAt (env.onPath sp) c k n) := by
  simp only [groupAt]
  within_tac [lookOf_within h, withPart_within h, recBlocksOf_within h]

theorem readRecord_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (x : Name) :
    ModelIO.Within fs (readRecord env c x) (readRecord (env.onPath sp) c x) := by
  simp only [readRecord]
  have he : importerSpot (env.onPath sp) x = importerSpot env x := rfl
  rw [he]
  within_tac [stmtAt_within h, groupAt_within h, withPart_within h]

theorem reachGo_within (h : OleanReads.Within fs env.rd sp) :
    ∀ (fuel : Nat) (L : ReachLog) (c : ReachCache),
      ModelIO.Within fs (reachGo env fuel L c) (reachGo (env.onPath sp) fuel L c) := by
  intro fuel
  induction fuel with
  | zero => intro L c; rw [reachGo, reachGo]; within_tac []
  | succ fuel ih => intro L c; rw [reachGo, reachGo]; within_tac [readRecord_within h,
      captureAll_within h, ih]

end

theorem reach_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (m : Name) (wr : WorkerReads) (own : Std.HashSet Name)
    (roots : Array Name) :
    ModelIO.Within fs (reach rd m wr own roots) (reach (.ofPath sp) m wr own roots) := by
  simp only [reach]
  have hc := clashKeys_within (env := { rd, mod := m, wr, own }) (sp := sp) h {} wr.clashes.toList #[]
  have hg := reachGo_within (env := { rd, mod := m, wr, own }) (sp := sp) h
  simp only [ReachEnv.onPath] at hc hg
  within_tac [hc, hg]

end Driver
end ConLeche
