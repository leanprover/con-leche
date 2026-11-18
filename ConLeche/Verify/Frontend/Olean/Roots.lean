module

public import ConLeche.Frontend.Olean.Files
public import ConLeche.Verify.Frontend.ModelIO
import Std.Data.HashMap.Lemmas

/-!
# Where a module is, in the model (task #511)

A module is located by its root (`findModule`, `ConLeche/Frontend/Olean/Files.lean`): where the
root is on the search path (`rootAt`), from the run's map of the roots it resolved (`Roots`) or
looked up.  On a snapshot:

* the lookup uses no handle (`rootAt_noHandles`, `findModule_noHandles`), and where its answer
  is not an exception's, the snapshot determines it (`rootAt_ok`, `findModule_ok`);
* **a map read off the snapshot** (`Roots.Ok`: each resolved root's answer one the lookup can
  give) stays one when a root is resolved (`Roots.resolve_ok`), and every read through it has
  only outcomes the read on the bare search path has, from the same handles
  (`ModelIO.Sub`: `findModule_sub`, `moduleImports_sub`, `readFiles_sub`, `readPartNames_sub`,
  `readView_sub`).  So whatever is proved of every outcome of the reads on the search path
  holds of the reads through the map.
-/

public section

namespace ConLeche

/-! ## Outcomes from the same handles -/

/-- **Every outcome of `a` is one of `b`, from the same handles.** -/
@[expose] def ModelIO.Sub {α : Type} (fs : FS) (a b : ModelIO α) : Prop :=
  ∀ hs o hs', a fs hs o hs' → b fs hs o hs'

theorem ModelIO.Sub.refl {α : Type} {fs : FS} (a : ModelIO α) : ModelIO.Sub fs a a :=
  fun _ _ _ h => h

theorem ModelIO.Sub.bind {α β : Type} {fs : FS} {a b : ModelIO α} {f g : α → ModelIO β}
    (ha : ModelIO.Sub fs a b) (hf : ∀ x, ModelIO.Sub fs (f x) (g x)) :
    ModelIO.Sub fs (a >>= f) (b >>= g) := by
  intro hs o hs'' h
  rcases h with ⟨x, hs₁, hx, h⟩ | ⟨e, rfl, he⟩
  · exact Or.inl ⟨x, hs₁, ha _ _ _ hx, hf x _ _ _ h⟩
  · exact Or.inr ⟨e, rfl, ha _ _ _ he⟩

theorem ModelIO.Sub.map {α β : Type} {fs : FS} {a b : ModelIO α} (g : α → β)
    (ha : ModelIO.Sub fs a b) : ModelIO.Sub fs (g <$> a) (g <$> b) := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  exact ha.bind fun _ => ModelIO.Sub.refl _

theorem ModelIO.Sub.canGive {α : Type} {fs : FS} {a b : ModelIO α} {v : α}
    (h : ModelIO.Sub fs a b) (hv : ModelIO.CanGive a fs v) : ModelIO.CanGive b fs v :=
  let ⟨hs, hs', hv⟩ := hv
  ⟨hs, hs', h _ _ _ hv⟩

/-! ## Actions that use no handle -/

/-- An operation whose answer is the snapshot's, the handles left as they were. -/
theorem ModelIO.noHandles_of_ret {α : Type} {x : ModelIO α} (f : FS → Option α)
    (h : ∀ fs hs, x fs hs = ModelIO.ret (f fs) hs) : x.NoHandles := by
  intro fs hs o hs'
  rw [h, h]
  simp only [ModelIO.ret, and_true]

theorem ModelIO.noHandles_mapM {α β : Type} {f : α → ModelIO β} (hf : ∀ a, (f a).NoHandles) :
    ∀ xs : List α, (xs.mapM f).NoHandles
  | [] => ModelIO.noHandles_pure _
  | x :: xs => by
    rw [List.mapM_cons]
    exact ModelIO.noHandles_bind (hf x) fun _ =>
      ModelIO.noHandles_bind (ModelIO.noHandles_mapM hf xs) fun _ => ModelIO.noHandles_pure _

theorem ModelIO.noHandles_tryCatch {α : Type} {x : ModelIO α} {h : IO.Error → ModelIO α}
    (hx : x.NoHandles) (hh : ∀ e, (h e).NoHandles) :
    (tryCatchThe IO.Error x h : ModelIO α).NoHandles := by
  intro fs hs o hs'
  show ((∃ a, o = .ok a ∧ x fs hs (.ok a) hs') ∨
      (∃ e hs₁, x fs hs (.error e) hs₁ ∧ h e fs hs₁ o hs')) ↔
    ((∃ a, o = .ok a ∧ x fs #[] (.ok a) #[]) ∨
      (∃ e hs₁, x fs #[] (.error e) hs₁ ∧ h e fs hs₁ o #[])) ∧ hs' = hs
  constructor
  · rintro (⟨a, rfl, ha⟩ | ⟨e, hs₁, he, hk⟩)
    · have h1 := (hx fs hs _ hs').1 ha
      exact ⟨Or.inl ⟨a, rfl, h1.1⟩, h1.2⟩
    · have h1 := (hx fs hs _ hs₁).1 he
      have h2 := (hh e fs hs₁ o hs').1 hk
      exact ⟨Or.inr ⟨e, #[], h1.1, h2.1⟩, h2.2.trans h1.2⟩
  · rintro ⟨(⟨a, rfl, ha⟩ | ⟨e, hs₁, he, hk⟩), hh'⟩
    · exact Or.inl ⟨a, rfl, (hx fs hs _ hs').2 ⟨ha, hh'⟩⟩
    · have h1 := (hx fs #[] _ hs₁).1 he
      have h2 := (hh e fs hs₁ o #[]).1 hk
      exact Or.inr ⟨e, hs, (hx fs hs _ hs).2 ⟨h1.1, rfl⟩, (hh e fs hs o hs').2 ⟨h2.1, hh'⟩⟩

theorem ModelIO.noHandles_map {α β : Type} {x : ModelIO α} (g : α → β) (hx : x.NoHandles) :
    (g <$> x : ModelIO β).NoHandles := by
  rw [map_eq_pure_bind]
  exact ModelIO.noHandles_bind hx fun _ => ModelIO.noHandles_pure _

/-- An action that uses no handle has an outcome it can give from any handles. -/
theorem ModelIO.NoHandles.canGive {α : Type} {x : ModelIO α} (hx : x.NoHandles) {fs : FS}
    {v : α} (h : ModelIO.CanGive x fs v) (hs : HS) : x fs hs (.ok v) hs :=
  let ⟨_, _, h⟩ := h
  (hx fs hs _ hs).2 ⟨hx.at h, rfl⟩

/-- **A determined action, caught by a determined handler that does not look at the
exception**, is determined. -/
theorem ModelIO.det_tryCatch {α : Type} {fs : FS} {x g : ModelIO α} {h : IO.Error → ModelIO α}
    (hx : x.Det fs) (hh : ∀ e, h e = g) (hg : g.Det fs) :
    (tryCatchThe IO.Error x h : ModelIO α).Det fs := by
  obtain ⟨a, ha⟩ := hx
  cases a with
  | some v =>
    exact ⟨some v, fun hs => let ⟨hs₁, h1⟩ := ha hs; ⟨hs₁, ModelIO.tryCatch_det h1⟩⟩
  | none =>
    obtain ⟨b, hb⟩ := hg
    refine ⟨b, fun hs => ?_⟩
    obtain ⟨hs₁, h1⟩ := ha hs
    obtain ⟨hs₂, h2⟩ := hb hs₁
    refine ⟨hs₂, ?_⟩
    rw [← h2]
    funext o hs'
    show ((∃ a', o = .ok a' ∧ x fs hs (.ok a') hs') ∨
      (∃ e hs₃, x fs hs (.error e) hs₃ ∧ h e fs hs₃ o hs')) = g fs hs₁ o hs'
    rw [h1]
    simp only [ModelIO.ret, ModelIO.answer, hh, eq_iff_iff]
    constructor
    · rintro (⟨a', -, ⟨e, he⟩, -⟩ | ⟨e, hs₃, ⟨-, rfl⟩, hg'⟩)
      · cases he
      · exact hg'
    · intro hg'
      exact Or.inr ⟨IO.userError "", hs₁, ⟨⟨_, rfl⟩, rfl⟩, hg'⟩

namespace Frontend.Olean

/-! ## The file operations -/

theorem pathExists_det (p : System.FilePath) (fs : FS) :
    (CheckerIO.pathExists p : ModelIO Bool).Det fs := ⟨some (fs.real p).isSome, fun hs => ⟨hs, rfl⟩⟩

theorem isDir_det (p : System.FilePath) (fs : FS) :
    (CheckerIO.isDir p : ModelIO Bool).Det fs := ⟨some (fs.dir p), fun hs => ⟨hs, rfl⟩⟩

theorem realPath_det (p : System.FilePath) (fs : FS) :
    (CheckerIO.realPath p : ModelIO System.FilePath).Det fs := ⟨fs.real p, fun hs => ⟨hs, rfl⟩⟩

theorem pathExists_noHandles (p : System.FilePath) :
    (CheckerIO.pathExists p : ModelIO Bool).NoHandles :=
  ModelIO.noHandles_of_ret (fun fs => some (fs.real p).isSome) fun _ _ => rfl

theorem isDir_noHandles (p : System.FilePath) : (CheckerIO.isDir p : ModelIO Bool).NoHandles :=
  ModelIO.noHandles_of_ret (fun fs => some (fs.dir p)) fun _ _ => rfl

theorem realPath_noHandles (p : System.FilePath) :
    (CheckerIO.realPath p : ModelIO System.FilePath).NoHandles :=
  ModelIO.noHandles_of_ret (fun fs => fs.real p) fun _ _ => rfl

/-! ## Where a root is -/

theorem holdsRoot_det (r : Name) (d : System.FilePath) (fs : FS) :
    (holdsRoot r d : ModelIO Bool).Det fs := by
  simp only [holdsRoot]
  refine ModelIO.det_bind (isDir_det _ fs) fun b => ?_
  split
  · exact ModelIO.det_pure _ _
  · exact pathExists_det _ fs

theorem holdsRoot_noHandles (r : Name) (d : System.FilePath) :
    (holdsRoot r d : ModelIO Bool).NoHandles := by
  simp only [holdsRoot]
  refine ModelIO.noHandles_bind (isDir_noHandles _) fun b => ?_
  split
  · exact ModelIO.noHandles_pure _
  · exact pathExists_noHandles _

theorem rootHits_det (sp : SearchPath) (r : Name) (fs : FS) :
    (rootHits sp r : ModelIO RootAt).Det fs := by
  simp only [rootHits]
  refine ModelIO.det_bind (ModelIO.det_mapM fun d _ =>
    ModelIO.det_bind (holdsRoot_det r d fs) fun _ => ModelIO.det_pure _ _) fun held => ?_
  split
  · exact ModelIO.det_pure _ _
  · exact ModelIO.det_pure _ _
  · refine ModelIO.det_bind (ModelIO.det_mapM fun d _ =>
      ModelIO.det_bind (realPath_det d fs) fun _ => ModelIO.det_pure _ _) fun _ => ?_
    split <;> exact ModelIO.det_pure _ _

theorem rootHits_noHandles (sp : SearchPath) (r : Name) :
    (rootHits sp r : ModelIO RootAt).NoHandles := by
  simp only [rootHits]
  refine ModelIO.noHandles_bind (ModelIO.noHandles_mapM (fun d =>
    ModelIO.noHandles_bind (holdsRoot_noHandles r d) fun _ => ModelIO.noHandles_pure _) _)
    fun held => ?_
  split
  · exact ModelIO.noHandles_pure _
  · exact ModelIO.noHandles_pure _
  · refine ModelIO.noHandles_bind (ModelIO.noHandles_mapM (fun d =>
      ModelIO.noHandles_bind (realPath_noHandles d) fun _ => ModelIO.noHandles_pure _) _)
      fun _ => ?_
    split <;> exact ModelIO.noHandles_pure _

theorem rootAt_noHandles (sp : SearchPath) (r : Name) :
    (rootAt sp r : ModelIO RootAt).NoHandles :=
  ModelIO.noHandles_tryCatch (rootHits_noHandles sp r) fun _ => ModelIO.noHandles_pure _

/-- **A root's place, where no exception gave it, is determined.** -/
theorem rootAt_ok {sp : SearchPath} {r : Name} {fs : FS} {hs hs' : HS} {a : RootAt}
    (h : (rootAt sp r : ModelIO RootAt) fs hs (.ok a) hs') :
    (∃ s, a = .failed s) ∨ (rootAt sp r : ModelIO RootAt).Gives fs a := by
  simp only [rootAt, ModelIO.tryCatch_ok] at h
  rcases h with h | ⟨e, _, -, h⟩
  · exact Or.inr ((rootHits_det sp r fs).of_ok h).tryCatch
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
    exact Or.inl ⟨_, h.1⟩

/-! ## A path and its fallback (task #607) -/

theorem lookAt_noHandles (path fallback : SearchPath) (r : Name) :
    (lookAt path fallback r : ModelIO RootAt).NoHandles := by
  simp only [lookAt]
  refine ModelIO.noHandles_bind (rootAt_noHandles _ _) fun a => ?_
  cases a
  · exact ModelIO.noHandles_pure _
  · exact rootAt_noHandles _ _
  all_goals exact ModelIO.noHandles_pure _

/-- **A root's place on a path and its fallback, where no exception gave it, is determined.** -/
theorem lookAt_ok {path fallback : SearchPath} {r : Name} {fs : FS} {hs hs' : HS} {a : RootAt}
    (h : (lookAt path fallback r : ModelIO RootAt) fs hs (.ok a) hs') :
    (∃ s, a = .failed s) ∨ (lookAt path fallback r : ModelIO RootAt).Gives fs a := by
  simp only [lookAt, ModelIO.bind_ok] at h
  obtain ⟨b, hs₁, hb, h⟩ := h
  rcases rootAt_ok hb with ⟨s, rfl⟩ | hg
  · simp only [lookNext, ModelIO.pure_iff, Except.ok.injEq] at h
    exact Or.inl ⟨s, h.1⟩
  · cases b with
    | missing =>
      rcases rootAt_ok h with ⟨s, rfl⟩ | hg'
      · exact Or.inl ⟨s, rfl⟩
      · exact Or.inr (hg.bind hg')
    | failed e =>
      simp only [lookNext, ModelIO.pure_iff, Except.ok.injEq] at h
      exact Or.inl ⟨e, h.1⟩
    | dir d =>
      simp only [lookNext, ModelIO.pure_iff, Except.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inr (hg.bind (ModelIO.gives_pure _ _))
    | twice ds =>
      simp only [lookNext, ModelIO.pure_iff, Except.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inr (hg.bind (ModelIO.gives_pure _ _))

/-! ## The roots a run resolved -/

/-- **The lookup of a resolved map**: its path and fallback, nothing resolved. -/
@[expose] def Roots.bare (R : Roots) : Roots := { path := R.path, fallback := R.fallback }

/-- **Roots read off the snapshot**: each resolved root's place is one the lookup can give. -/
@[expose] def Roots.Ok (fs : FS) (R : Roots) : Prop :=
  ∀ r a, R.map[r]? = some a → ModelIO.CanGive (lookAt R.path R.fallback r) fs a

/-- A search path with no root resolved. -/
theorem Roots.ok_coe (fs : FS) (sp : SearchPath) : Roots.Ok fs (sp : Roots) := by
  intro r a h
  simp at h

/-- A lookup with no root resolved. -/
theorem Roots.ok_bare (fs : FS) (R : Roots) : Roots.Ok fs R.bare := by
  intro r a h
  simp [Roots.bare] at h

theorem Roots.bare_bare (R : Roots) : R.bare.bare = R.bare := rfl

theorem Roots.bare_coe (sp : SearchPath) : (sp : Roots).bare = (sp : Roots) := rfl

theorem Roots.rootOf_bare (R : Roots) (r : Name) :
    (R.bare.rootOf r : ModelIO RootAt) = lookAt R.path R.fallback r := by
  simp [Roots.rootOf, Roots.bare]

theorem Roots.rootOf_noHandles (R : Roots) (r : Name) :
    (R.rootOf r : ModelIO RootAt).NoHandles := by
  simp only [Roots.rootOf]
  split
  · exact ModelIO.noHandles_pure _
  · exact lookAt_noHandles _ _ _

/-- **A root's place through the map is one the lookup gives, from the same handles.** -/
theorem Roots.rootOf_sub {fs : FS} {R : Roots} (hR : R.Ok fs) (r : Name) :
    ModelIO.Sub fs (R.rootOf r) (lookAt R.path R.fallback r) := by
  simp only [Roots.rootOf]
  split
  · rename_i a ha
    intro hs o hs' h
    simp only [ModelIO.pure_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (lookAt_noHandles _ _ _).canGive (hR r a ha) _
  · exact ModelIO.Sub.refl _

/-- **Resolving a root keeps the map read off the snapshot.** -/
theorem Roots.resolve_ok {fs : FS} {R R' : Roots} {m : Name} {hs hs' : HS} (hR : R.Ok fs)
    (h : (R.resolve m : ModelIO Roots) fs hs (.ok R') hs') : R'.Ok fs ∧ R'.bare = R.bare := by
  simp only [Roots.resolve] at h
  split at h
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hR, rfl⟩
  · simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨a, hs₁, ha, rfl, -⟩ := h
    refine ⟨fun r b hb => ?_, rfl⟩
    simp only [Std.HashMap.getElem?_insert] at hb
    split at hb
    · rename_i heq
      cases hb
      have : m.root = r := by simpa using heq
      subst this
      exact ⟨_, _, ha⟩
    · exact hR r b hb

/-- `resolve`, folded over a list, keeps the map read off the snapshot. -/
theorem Roots.foldResolve_ok {fs : FS} :
    ∀ (ms : List Name) {R R' : Roots} {hs hs' : HS}, R.Ok fs →
      (ms.foldlM Roots.resolve R : ModelIO Roots) fs hs (.ok R') hs' →
      R'.Ok fs ∧ R'.bare = R.bare
  | [], R, R', hs, hs', hR, h => by
    simp only [List.foldlM_nil, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hR, rfl⟩
  | m :: ms, R, R', hs, hs', hR, h => by
    simp only [List.foldlM_cons, ModelIO.bind_ok] at h
    obtain ⟨R₁, hs₁, h1, h2⟩ := h
    obtain ⟨hR₁, hp₁⟩ := Roots.resolve_ok hR h1
    obtain ⟨hR', hp'⟩ := Roots.foldResolve_ok ms hR₁ h2
    exact ⟨hR', hp'.trans hp₁⟩

/-! ## A module's location -/

theorem locatedOf_ok {m : Name} {a : RootAt} {loc : Located} (h : locatedOf m a = .ok loc) :
    a = .dir loc.dir := by
  cases a <;> simp [locatedOf] at h
  subst h
  rfl

theorem findModule_noHandles (R : Roots) (m : Name) :
    (findModule R m : ModelIO (Except CheckError Located)).NoHandles :=
  ModelIO.noHandles_map _ (Roots.rootOf_noHandles R _)

/-- A root's place through the map, where no exception gave it, is determined. -/
theorem Roots.rootOf_ok {R : Roots} {r : Name} {fs : FS} {hs hs' : HS} {a : RootAt}
    (h : (R.rootOf r : ModelIO RootAt) fs hs (.ok a) hs') :
    (∃ s, a = .failed s) ∨ (R.rootOf r : ModelIO RootAt).Gives fs a := by
  unfold Roots.rootOf at h ⊢
  split
  · rename_i b hb
    rw [hb] at h
    simp only [ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inr (ModelIO.gives_pure _ _)
  · rename_i hb
    rw [hb] at h
    exact lookAt_ok h

/-- **A module found: the snapshot determines the location.** -/
theorem findModule_ok {sp : Roots} {m : Name} {fs : FS} {hs : HS} {loc : Located} {hs' : HS}
    (h : (findModule sp m : ModelIO _) fs hs (.ok (.ok loc)) hs') :
    ModelIO.Gives (findModule sp m) fs (.ok loc) := by
  simp only [findModule, ModelIO.map_ok] at h
  obtain ⟨a, ha, hl⟩ := h
  have ha' := locatedOf_ok hl
  subst ha'
  simp only [findModule]
  rw [← hl]
  rcases Roots.rootOf_ok ha with ⟨s, hs⟩ | hg
  · cases hs
  · exact hg.map

/-- **A module's location through the map is one the search path gives.** -/
theorem findModule_sub {fs : FS} {R : Roots} (hR : R.Ok fs) (m : Name) :
    ModelIO.Sub fs (findModule R m) (findModule R.bare m) := by
  simp only [findModule]
  rw [Roots.rootOf_bare]
  exact (Roots.rootOf_sub hR _).map _

theorem moduleImports_sub {fs : FS} {R : Roots} (hR : R.Ok fs) (m : Name) :
    ModelIO.Sub fs (moduleImports R m) (moduleImports R.bare m) := by
  simp only [moduleImports]
  exact (findModule_sub hR m).bind fun _ => ModelIO.Sub.refl _

theorem readFiles_sub {fs : FS} {R : Roots} (hR : R.Ok fs) (m : Name) (level : OLeanLevel) :
    ModelIO.Sub fs (readFiles R m level) (readFiles R.bare m level) := by
  simp only [readFiles]
  exact (findModule_sub hR m).bind fun _ => ModelIO.Sub.refl _

theorem readView_sub {fs : FS} {R : Roots} (hR : R.Ok fs) (m : Name) (level : OLeanLevel) :
    ModelIO.Sub fs (readView R m level) (readView R.bare m level) := by
  simp only [readView]
  exact (readFiles_sub hR m level).bind fun _ => ModelIO.Sub.refl _

theorem readPartNames_sub {fs : FS} {R : Roots} (hR : R.Ok fs) (x : Name × OLeanLevel) :
    ModelIO.Sub fs (readPartNames R x) (readPartNames R.bare x) := by
  simp only [readPartNames]
  exact (findModule_sub hR x.1).bind fun _ => ModelIO.Sub.refl _

/-- The reads through the map, against a lookup equal to the map's. -/
theorem moduleImports_sub' {fs : FS} {R S : Roots} (hR : R.Ok fs) (hb : R.bare = S) (m : Name) :
    ModelIO.Sub fs (moduleImports R m) (moduleImports S m) := hb ▸ moduleImports_sub hR m

theorem readFiles_sub' {fs : FS} {R S : Roots} (hR : R.Ok fs) (hb : R.bare = S) (m : Name)
    (level : OLeanLevel) : ModelIO.Sub fs (readFiles R m level) (readFiles S m level) :=
  hb ▸ readFiles_sub hR m level

theorem readPartNames_sub' {fs : FS} {R S : Roots} (hR : R.Ok fs) (hb : R.bare = S)
    (x : Name × OLeanLevel) : ModelIO.Sub fs (readPartNames R x) (readPartNames S x) :=
  hb ▸ readPartNames_sub hR x

/-- **A module located on the search path is located there through the map too.** -/
theorem findModule_rev {fs : FS} {R : Roots} (hR : R.Ok fs) {m : Name} {loc : Located}
    {hs hs' : HS} (h : (findModule R.bare m : ModelIO _) fs hs (.ok (.ok loc)) hs') :
    (findModule R m : ModelIO _) fs hs (.ok (.ok loc)) hs' := by
  simp only [findModule, ModelIO.map_ok] at h ⊢
  rw [Roots.rootOf_bare] at h
  obtain ⟨a, ha, hl⟩ := h
  refine ⟨a, ?_, hl⟩
  have ha' := locatedOf_ok hl
  subst ha'
  have hhs : hs' = hs := ((lookAt_noHandles _ _ _) fs hs _ hs').1 ha |>.2
  subst hhs
  unfold Roots.rootOf
  cases hb : R.map[m.root]? with
  | some b =>
    show (pure b : ModelIO RootAt) fs hs' _ hs'
    rcases lookAt_ok ha with ⟨s, hs⟩ | hg
    · cases hs
    · have := hg.eq (hR _ b hb)
      subst this
      exact ⟨rfl, rfl⟩
  | none => exact ha

/-- **A view's files on the search path are its files through the map too.** -/
theorem readFiles_rev {fs : FS} {R : Roots} (hR : R.Ok fs) {m : Name} {level : OLeanLevel}
    {f : ModFiles} (h : ModelIO.CanGive (readFiles R.bare m level) fs (.ok f)) :
    ModelIO.CanGive (readFiles R m level) fs (.ok f) := by
  obtain ⟨hs, hs', h⟩ := h
  refine ⟨hs, hs', ?_⟩
  simp only [readFiles, ModelIO.bind_ok] at h ⊢
  obtain ⟨x, hs₁, hx, h⟩ := h
  rcases x with e | loc
  · simp at h
  exact ⟨_, hs₁, findModule_rev hR hx, h⟩

end Frontend.Olean

end ConLeche
