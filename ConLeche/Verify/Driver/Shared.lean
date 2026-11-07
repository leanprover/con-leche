module

public import ConLeche.Driver.Reach
public import ConLeche.Verify.Frontend.ModelIO
import ConLeche.Verify.Frontend.Olean.Files

/-!
# Reads answered from tables, in the model

A worker's reads of the files go through `OleanReads` (`ConLeche/Frontend/Olean/Files.lean`): a
module's imports, a view's files, a part's name positions.  The worker reads them on the search
path (`OleanReads.ofPath sp`); the one-process mode (`ConLeche/Driver/Modular.lean`) answers them
from tables it read once up front, and where a table has nothing, by the same read.

**Refinement** (`ModelIO.Within fs a b`): every outcome of `a` on the snapshot `fs`, from any open
handles, is one of `b` from every open handles; the handles are not compared, since a table
answers a read without opening a file.  The reads of the files have the same outcomes from any
open handles (`findModule_within`, `moduleImports_within`, `readFiles_within`,
`readPartNames_within`): locating a module opens no file, and the header read is determined.
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

/-- **`a` refines `b` on the snapshot `fs`**: every outcome of `a` there, from any open handles,
is one of `b` from every open handles.  The handles are not compared: the tables answer a read
without opening a file, the files' read opens one. -/
@[expose] def ModelIO.Within {α : Type} (fs : FS) (a b : ModelIO α) : Prop :=
  ∀ hs o hs', a fs hs o hs' → ∀ hs₀, ∃ hs₁, b fs hs₀ o hs₁

namespace ModelIO.Within

variable {fs : FS}

/-- An action whose outcomes are the same from any open handles refines itself: one that uses
no handle, or a determined one. -/
theorem of_noHandles {α : Type} {a : ModelIO α} (h : ModelIO.NoHandles a) : Within fs a a :=
  fun hs o hs' ha hs₀ => ⟨hs₀, (h fs hs₀ o hs₀).2 ⟨((h fs hs o hs').1 ha).1, rfl⟩⟩

theorem of_det {α : Type} {a : ModelIO α} (h : ModelIO.Det a fs) : Within fs a a := by
  intro hs o hs' ha hs₀
  obtain ⟨x, hx⟩ := h
  obtain ⟨hs₁, h1⟩ := hx hs
  obtain ⟨hs₂, h2⟩ := hx hs₀
  rw [h1] at ha
  exact ⟨hs₂, by rw [h2]; exact ⟨ha.1, rfl⟩⟩

theorem pure {α : Type} (v : α) : Within fs (Pure.pure v) (Pure.pure v) :=
  of_noHandles (ModelIO.noHandles_pure v)

theorem liftIO {α : Type} (a : IO α) : Within fs (CheckerIO.liftIO a) (CheckerIO.liftIO a) :=
  of_noHandles (ModelIO.noHandles_liftIO a)

theorem trans {α : Type} {a b c : ModelIO α} (h₁ : Within fs a b) (h₂ : Within fs b c) :
    Within fs a c := fun hs o hs' h hs₀ =>
  let ⟨hs₁, hb⟩ := h₁ hs o hs' h hs₀
  h₂ hs₀ o hs₁ hb hs₀

theorem bind {α β : Type} {a b : ModelIO α} {f g : α → ModelIO β} (ha : Within fs a b)
    (hf : ∀ x, Within fs (f x) (g x)) : Within fs (a >>= f) (b >>= g) := by
  intro hs o hs' h hs₀
  rcases h with ⟨x, hs₁, hx, h⟩ | ⟨e, rfl, he⟩
  · obtain ⟨hs₂, hb⟩ := ha hs _ hs₁ hx hs₀
    obtain ⟨hs₃, hg⟩ := hf x hs₁ o hs' h hs₂
    exact ⟨hs₃, Or.inl ⟨x, hs₂, hb, hg⟩⟩
  · obtain ⟨hs₂, hb⟩ := ha hs _ hs' he hs₀
    exact ⟨hs₂, Or.inr ⟨e, rfl, hb⟩⟩

theorem ite {α : Type} {c : Prop} [Decidable c] {a a' b b' : ModelIO α}
    (h₁ : c → Within fs a a') (h₂ : ¬c → Within fs b b') :
    Within fs (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h₁ hc
  · simp only [hc, ↓reduceIte]; exact h₂ hc

/-- A value `a` can give is one `b` can give, from any open handles. -/
theorem ok_of {α : Type} {a b : ModelIO α} (h : Within fs a b) {hs hs' : HS} {v : α}
    (hv : a fs hs (.ok v) hs') (hs₀ : HS) : ∃ hs₁, b fs hs₀ (.ok v) hs₁ := h _ _ _ hv hs₀

theorem canGive {α : Type} {a b : ModelIO α} (h : Within fs a b) {v : α}
    (hv : ModelIO.CanGive a fs v) : ModelIO.CanGive b fs v :=
  let ⟨_, _, hv⟩ := hv
  let ⟨hs₁, hb⟩ := h.ok_of hv #[]
  ⟨#[], hs₁, hb⟩

theorem throw {α : Type} (e : IO.Error) :
    Within fs (throwThe IO.Error e : ModelIO α) (throwThe IO.Error e) :=
  fun _ _ _ h hs₀ => ⟨hs₀, ⟨h.1, rfl⟩⟩

theorem map {α β : Type} {a b : ModelIO α} (g : α → β) (h : Within fs a b) :
    Within fs (g <$> a) (g <$> b) := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  exact bind h fun _ => pure _

theorem tryCatch {α : Type} {a b : ModelIO α} {f g : IO.Error → ModelIO α} (ha : Within fs a b)
    (hf : ∀ e, Within fs (f e) (g e)) :
    Within fs (tryCatchThe IO.Error a f) (tryCatchThe IO.Error b g) := by
  intro hs o hs' h hs₀
  rcases h with ⟨v, rfl, hv⟩ | ⟨e, hs₁, he, h⟩
  · obtain ⟨hs₁, hb⟩ := ha hs _ hs' hv hs₀
    exact ⟨hs₁, Or.inl ⟨v, rfl, hb⟩⟩
  · obtain ⟨hs₂, hb⟩ := ha hs _ hs₁ he hs₀
    obtain ⟨hs₃, hg⟩ := hf e hs₁ o hs' h hs₂
    exact ⟨hs₃, Or.inr ⟨e, hs₂, hb, hg⟩⟩

end ModelIO.Within

/-- The sequential map with a stop keeps refinement. -/
theorem mapExcept_within {fs : FS} {α β ε : Type} {f g : α → ModelIO (Except ε β)}
    (h : ∀ x, ModelIO.Within fs (f x) (g x)) :
    ∀ xs, ModelIO.Within fs (mapExcept f xs) (mapExcept g xs)
  | [] => ModelIO.Within.pure _
  | x :: xs => by
    simp only [mapExcept]
    refine ModelIO.Within.bind (h x) fun r => ?_
    rcases r with e | b
    · exact ModelIO.Within.pure _
    · refine ModelIO.Within.bind (mapExcept_within h xs) fun r => ?_
      rcases r with e | bs <;> exact ModelIO.Within.pure _

/-- The parallel map with a stop keeps refinement (in the model it is the sequential map). -/
theorem parMapExcept_within {fs : FS} {α β ε : Type} {f g : α → ModelIO (Except ε β)}
    (h : ∀ x, ModelIO.Within fs (f x) (g x)) (jobs jobs' : Nat) (xs : List α) :
    ModelIO.Within fs (CheckerIO.parMapExcept jobs f xs) (CheckerIO.parMapExcept jobs' g xs) :=
  mapExcept_within h xs

/-- Peel a phase written over the reads: a callee's refinement (the terms given), the same
`pure`, `throw` or `liftIO` on both sides, a bind, a match or an `if` on one value. -/
local syntax "within_tac" "[" term,* "]" : tactic
macro_rules
  | `(tactic| within_tac [$ts,*]) => `(tactic| repeat' (first
      $[| apply $ts:term]*
      | exact ModelIO.Within.pure _
      | exact ModelIO.Within.throw _
      | exact ModelIO.Within.liftIO _
      | (refine ModelIO.Within.bind ?_ fun _ => ?_)
      | (refine ModelIO.Within.ite (fun _ => ?_) (fun _ => ?_))
      | split))

namespace Frontend.Olean

/-- **Reads that refine the search path's**: each of the three operations' outcomes, on the
snapshot, is one of the read of the files on `sp`. -/
structure OleanReads.Within (fs : FS) (rd : OleanReads ModelIO) (sp : SearchPath) : Prop where
  imports : ∀ m, ModelIO.Within fs (rd.imports m) (moduleImports sp m)
  files : ∀ m level, ModelIO.Within fs (rd.files m level) (readFiles sp m level)
  names : ∀ x, ModelIO.Within fs (rd.names x) (readPartNames sp x)

/-! ## The reads of the files: the same outcomes from any open handles -/

theorem findModule_within (fs : FS) (sp : SearchPath) (m : Name) :
    ModelIO.Within fs (findModule sp m) (findModule sp m) := by
  simp only [findModule]
  refine ModelIO.Within.bind (ModelIO.Within.tryCatch
    (ModelIO.Within.map _ (ModelIO.Within.of_det (locateHits_det sp m fs)))
    fun _ => ModelIO.Within.pure _) fun _ => ?_
  within_tac []

theorem readPart_within (fs : FS) (p : System.FilePath) :
    ModelIO.Within fs (readPart p) (readPart p) := by
  simp only [readPart]
  exact ModelIO.Within.bind (ModelIO.Within.of_det ⟨fs.file p, fun hs => ⟨hs, rfl⟩⟩)
    fun _ => ModelIO.Within.pure _

theorem readImportsAt_within (fs : FS) (loc : Located) (m : Name) :
    ModelIO.Within fs (readImportsAt loc m) (readImportsAt loc m) := by
  simp only [readImportsAt]
  refine ModelIO.Within.bind (ModelIO.Within.of_det (foldChunks_isDet _ _ _ _ _ fs)) fun _ => ?_
  within_tac []

theorem moduleImports_within (fs : FS) (sp : SearchPath) (m : Name) :
    ModelIO.Within fs (moduleImports sp m) (moduleImports sp m) := by
  simp only [moduleImports]
  within_tac [findModule_within fs sp m, readImportsAt_within fs _ m]

theorem readFilesAt_within (fs : FS) (loc : Located) (m : Name) (level : OLeanLevel) :
    ModelIO.Within fs (readFilesAt loc m level) (readFilesAt loc m level) := by
  simp only [readFilesAt]
  within_tac [readPart_within fs _]

theorem readFiles_within (fs : FS) (sp : SearchPath) (m : Name) (level : OLeanLevel) :
    ModelIO.Within fs (readFiles sp m level) (readFiles sp m level) := by
  simp only [readFiles]
  within_tac [findModule_within fs sp m, readFilesAt_within fs _ m level]

theorem readPartNames_within (fs : FS) (sp : SearchPath) (x : Name × OLeanLevel) :
    ModelIO.Within fs (readPartNames sp x) (readPartNames sp x) := by
  simp only [readPartNames, readPartNamesAt]
  within_tac [findModule_within fs sp x.1, readFilesAt_within fs _ x.1 x.2]

/-- The search path's reads refine themselves. -/
theorem OleanReads.Within.ofPath (fs : FS) (sp : SearchPath) :
    OleanReads.Within fs (OleanReads.ofPath sp) sp :=
  ⟨moduleImports_within fs sp, readFiles_within fs sp, readPartNames_within fs sp⟩

/-! ## The header fixpoint -/

theorem levelsGo_within {fs : FS} {imps imps' : Name → ModelIO (Except CheckError (Array ImportRec))}
    (h : ∀ m, ModelIO.Within fs (imps m) (imps' m)) (gPriv : Bool) :
    ∀ fuel ws st, ModelIO.Within fs (levelsGo imps gPriv fuel ws st)
      (levelsGo imps' gPriv fuel ws st)
  | _, [], st => by simp only [levelsGo]; exact ModelIO.Within.pure _
  | 0, _ :: _, _ => by simp only [levelsGo]; exact ModelIO.Within.pure _
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
        · exact ModelIO.Within.pure _
        · refine ModelIO.Within.bind (h _) fun r => ?_
          rcases r with e | is
          · exact ModelIO.Within.pure _
          · exact levelsGo_within h gPriv fuel _ _

theorem headerFixpoint_within {fs : FS}
    {imps imps' : Name → ModelIO (Except CheckError (Array ImportRec))}
    (h : ∀ m, ModelIO.Within fs (imps m) (imps' m)) (isModule : Bool) (imports : Array ImportRec) :
    ModelIO.Within fs (headerFixpoint imps isModule imports)
      (headerFixpoint imps' isModule imports) := by
  simp only [headerFixpoint]
  refine ModelIO.Within.bind (levelsGo_within h _ _ _ _) fun _ => ?_
  within_tac []

/-! ## The worker's reads and its home -/

theorem readInfosOf_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (ld : Loads) (ix : NameIndex) (x : Nat × Array Copy) :
    ModelIO.Within fs (readInfosOf rd ld ix x) (readInfosOf (.ofPath sp) ld ix x) := by
  simp only [readInfosOf]
  refine ModelIO.Within.bind (h.files _ _) fun _ => ?_
  within_tac []

theorem readInfos_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (ld : Loads) (ix : NameIndex) (jobs : Nat) (cs : Array Copy) :
    ModelIO.Within fs (readInfos rd ld ix jobs cs) (readInfos (.ofPath sp) ld ix jobs cs) := by
  simp only [readInfos]
  refine ModelIO.Within.bind (parMapExcept_within (readInfosOf_within h ld ix) _ _ _) fun _ => ?_
  within_tac []

theorem workerReads_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (m : Name) (jobs : Nat) :
    ModelIO.Within fs (workerReads rd m jobs) (workerReads (.ofPath sp) m jobs) := by
  simp only [workerReads]
  refine ModelIO.Within.bind (h.names _) fun r => ?_
  rcases r with e | own
  · exact ModelIO.Within.pure _
  refine ModelIO.Within.bind (headerFixpoint_within h.imports _ _) fun r => ?_
  rcases r with e | ld
  · exact ModelIO.Within.pure _
  refine ModelIO.Within.bind (parMapExcept_within h.names _ _ _) fun r => ?_
  rcases r with e | parts
  · exact ModelIO.Within.pure _
  simp only
  split
  · exact ModelIO.Within.pure _
  refine ModelIO.Within.bind (readInfos_within h _ _ _ _) fun r => ?_
  rcases r with e | infos
  · exact ModelIO.Within.pure _
  refine ModelIO.Within.bind (readInfos_within h _ _ _ _) fun _ => ?_
  within_tac []

theorem readHome_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (m : Name) (i : Nat) :
    ModelIO.Within fs (readHome rd m i) (readHome (.ofPath sp) m i) := by
  simp only [readHome]
  refine ModelIO.Within.bind (h.files _ _) fun _ => ?_
  within_tac []

end Frontend.Olean


namespace Driver

open Frontend.Olean

/-- The reach's environment with its reads on the search path. -/
@[expose] def ReachEnv.onPath (env : ReachEnv ModelIO) (sp : SearchPath) : ReachEnv ModelIO :=
  { env with rd := .ofPath sp }

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
  | c, v, [] => by simp only [viewAdd]; exact ModelIO.Within.pure _
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

theorem agreeCheck_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (m y : Name)
    (s₁ s₂ : Spot) :
    ModelIO.Within fs (agreeCheck env c m y s₁ s₂) (agreeCheck (env.onPath sp) c m y s₁ s₂) := by
  simp only [agreeCheck]
  within_tac [stmtAt_within h, proofStatus_within h]

theorem statuses_within (h : OleanReads.Within fs env.rd sp) :
    ∀ (c : ReachCache) (xs : List (Spot × ConstantVal × CKindF Name Unit)) (acc : List ProofStatus),
      ModelIO.Within fs (clashAgree.statuses env c xs acc)
        (clashAgree.statuses (env.onPath sp) c xs acc)
  | c, [], acc => by simp only [clashAgree.statuses]; exact ModelIO.Within.pure _
  | c, x :: xs, acc => by
    simp only [clashAgree.statuses]
    within_tac [proofStatus_within h, statuses_within h]

theorem clashAgree_within (h : OleanReads.Within fs env.rd sp) :
    ∀ (c : ReachCache) (cls : List Clash) (acc : Array Name),
      ModelIO.Within fs (clashAgree env c cls acc) (clashAgree (env.onPath sp) c cls acc)
  | c, [], acc => by simp only [clashAgree]; exact ModelIO.Within.pure _
  | c, cl :: cls, acc => by
    simp only [clashAgree]
    simp only [ReachEnv.onPath]
    within_tac [statuses_within h, clashAgree_within h]

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
  within_tac [inExported_within h, locate_within h, agreeCheck_within h, privSpot_within h]

theorem captureAll_within (h : OleanReads.Within fs env.rd sp) (m : Name) :
    ∀ (c : ReachCache) (ys : List Name),
      ModelIO.Within fs (captureAll env m c ys) (captureAll (env.onPath sp) m c ys)
  | c, [] => by simp only [captureAll]; exact ModelIO.Within.pure _
  | c, y :: ys => by
    simp only [captureAll]
    within_tac [captureOne_within h, captureAll_within h]

theorem capturePairs_within (h : OleanReads.Within fs env.rd sp) :
    ∀ (c : ReachCache) (ps : List (Name × Name)),
      ModelIO.Within fs (capturePairs env c ps) (capturePairs (env.onPath sp) c ps)
  | c, [] => by simp only [capturePairs]; exact ModelIO.Within.pure _
  | c, (m, y) :: ps => by
    simp only [capturePairs]
    within_tac [captureOne_within h, capturePairs_within h]

theorem recBlocksOf_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (k : PartKey) :
    ModelIO.Within fs (recBlocksOf env c k) (recBlocksOf (env.onPath sp) c k) := by
  simp only [recBlocksOf]
  within_tac [tableOf_within h, withPart_within h]

theorem groupAt_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (k : PartKey)
    (n : Name) :
    ModelIO.Within fs (groupAt env c k n) (groupAt (env.onPath sp) c k n) := by
  simp only [groupAt]
  within_tac [lookOf_within h, withPart_within h, recBlocksOf_within h]

theorem stmtRecord_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (s : Spot)
    (cv : ConstantVal) :
    ModelIO.Within fs (stmtRecord env c s cv) (stmtRecord (env.onPath sp) c s cv) := by
  simp only [stmtRecord]
  within_tac [privSpot_within h]

theorem readRecord_within (h : OleanReads.Within fs env.rd sp) (c : ReachCache) (x : Name) :
    ModelIO.Within fs (readRecord env c x) (readRecord (env.onPath sp) c x) := by
  simp only [readRecord]
  have he : importerSpot (env.onPath sp) x = importerSpot env x := rfl
  rw [he]
  within_tac [stmtAt_within h, groupAt_within h, withPart_within h, stmtRecord_within h]

theorem reachGo_within (h : OleanReads.Within fs env.rd sp) :
    ∀ (fuel : Nat) (L : ReachLog) (c : ReachCache),
      ModelIO.Within fs (reachGo env fuel L c) (reachGo (env.onPath sp) fuel L c) := by
  intro fuel
  induction fuel with
  | zero => intro L c; rw [reachGo, reachGo]; within_tac []
  | succ fuel ih => intro L c; rw [reachGo, reachGo]; within_tac [readRecord_within h,
      captureAll_within h, capturePairs_within h, ih]

end

theorem reach_within {fs : FS} {rd : OleanReads ModelIO} {sp : SearchPath}
    (h : OleanReads.Within fs rd sp) (m : Name) (wr : WorkerReads) (own : Std.HashSet Name)
    (roots : Array Name) :
    ModelIO.Within fs (reach rd m wr own roots) (reach (.ofPath sp) m wr own roots) := by
  simp only [reach]
  have hc := clashAgree_within (env := { rd, mod := m, wr, own }) (sp := sp) h {} wr.clashes.toList #[]
  have hg := reachGo_within (env := { rd, mod := m, wr, own }) (sp := sp) h
  simp only [ReachEnv.onPath] at hc hg
  within_tac [hc, hg]

end Driver
end ConLeche
