module

public import ConLeche.Frontend.Olean.Records
public import ConLeche.Verify.Frontend.Olean.Roots
import Std.Data.HashMap.Lemmas

/-!
# The challenge's read sees only the trusted directories (task #607, T1)

A compared run reads the challenge's closure through the trusted directories alone
(`Driver.CmpReq.chalRoots`).  `challenge_local`: on two snapshots that agree on every path the
reader can form under those directories (`FS.AgreeUnder`), the read has the same outcomes,
failure included (`challengeView`).  So whatever an accepted run says of the challenge's read
is a property of the trusted files alone, whatever else either snapshot holds.

The paths the reader forms under a directory `d` are `modDir d m` (a module's directory, and
`d` itself at `m = .anonymous`) and `modFile d m ext` (`Under`).  Locality is a property of an
action (`ModelIO.LocalTo`): it is the same function of the handles on the two snapshots; every
ok value of it also satisfies a post-condition, what the next action needs (that a root is found
in one of the directories, `RootsIn`).  It is closed under `bind`, `tryCatch` and the list
traversals; its leaves are the file operations on paths `Under` the directories, a read from an
open handle (the handle holds its bytes), and `liftIO`, which may answer anything on both.
-/

public section

namespace ConLeche

/-! ## Agreement under directories -/

/-- **A path the reader forms under the directories**: a module's directory, the directory
itself included, or a module's file. -/
@[expose] def Under (dirs : List System.FilePath) (p : System.FilePath) : Prop :=
  ∃ d ∈ dirs, ∃ m, p = Frontend.Olean.modDir d m ∨ ∃ ext, p = Frontend.Olean.modFile d m ext

/-- **Two snapshots agree under the directories**: every path the reader forms there has the
same real path, is a directory on both or on neither, and names the same bytes. -/
@[expose] def FS.AgreeUnder (dirs : List System.FilePath) (fs₁ fs₂ : FS) : Prop :=
  ∀ p, Under dirs p → fs₁.real p = fs₂.real p ∧ fs₁.dir p = fs₂.dir p ∧ fs₁.file p = fs₂.file p

/-! ## Local actions -/

/-- **An action local to a relation of snapshots**, with a post-condition: on two related
snapshots it is the same function of the handles, and every value it gives satisfies `Q`. -/
@[expose] def ModelIO.LocalTo {α : Type} (P : FS → FS → Prop) (Q : α → Prop) (x : ModelIO α) :
    Prop :=
  (∀ fs₁ fs₂, P fs₁ fs₂ → x fs₁ = x fs₂) ∧ ∀ fs hs a hs', x fs hs (.ok a) hs' → Q a

variable {P : FS → FS → Prop}

theorem ModelIO.LocalTo.weaken {α : Type} {Q Q' : α → Prop} {x : ModelIO α}
    (hx : x.LocalTo P Q) (h : ∀ a, Q a → Q' a) : x.LocalTo P Q' :=
  ⟨hx.1, fun fs hs a hs' ha => h a (hx.2 fs hs a hs' ha)⟩

theorem ModelIO.localTo_pure {α : Type} {Q : α → Prop} {a : α} (h : Q a) :
    (pure a : ModelIO α).LocalTo P Q :=
  ⟨fun _ _ _ => rfl, fun _ _ b _ hb => by
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hb
    exact hb.1 ▸ h⟩

theorem ModelIO.localTo_pure_true {α : Type} {a : α} :
    (pure a : ModelIO α).LocalTo P (fun _ => True) :=
  ModelIO.localTo_pure trivial

theorem ModelIO.localTo_liftIO {α : Type} (a : IO α) :
    (CheckerIO.liftIO a : ModelIO α).LocalTo P (fun _ => True) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => trivial⟩

theorem ModelIO.LocalTo.bind {α β : Type} {Q : α → Prop} {R : β → Prop} {x : ModelIO α}
    {f : α → ModelIO β} (hx : x.LocalTo P Q) (hf : ∀ a, Q a → (f a).LocalTo P R) :
    (x >>= f).LocalTo P R := by
  refine ⟨fun fs₁ fs₂ h => ?_, fun fs hs b hs'' hb => ?_⟩
  · funext hs o hs''
    show ((∃ a hs', x fs₁ hs (.ok a) hs' ∧ f a fs₁ hs' o hs'') ∨
        (∃ e, o = .error e ∧ x fs₁ hs (.error e) hs'')) =
      ((∃ a hs', x fs₂ hs (.ok a) hs' ∧ f a fs₂ hs' o hs'') ∨
        (∃ e, o = .error e ∧ x fs₂ hs (.error e) hs''))
    rw [hx.1 fs₁ fs₂ h]
    apply propext
    constructor <;> rintro (⟨a, hs', ha, hb⟩ | he)
    · have e := (hf a (hx.2 _ _ _ _ ha)).1 fs₁ fs₂ h
      exact .inl ⟨a, hs', ha, e ▸ hb⟩
    · exact .inr he
    · have e := (hf a (hx.2 _ _ _ _ ha)).1 fs₁ fs₂ h
      exact .inl ⟨a, hs', ha, e ▸ hb⟩
    · exact .inr he
  · obtain ⟨a, hs', ha, hb⟩ := (ModelIO.bind_ok _ _ _ _ _ _).1 hb
    exact (hf a (hx.2 _ _ _ _ ha)).2 _ _ _ _ hb

theorem ModelIO.LocalTo.map {α β : Type} {Q : α → Prop} {R : β → Prop} {x : ModelIO α}
    (g : α → β) (hx : x.LocalTo P Q) (hg : ∀ a, Q a → R (g a)) :
    (g <$> x : ModelIO β).LocalTo P R := by
  rw [map_eq_pure_bind]
  exact hx.bind fun a ha => ModelIO.localTo_pure (hg a ha)

theorem ModelIO.LocalTo.tryCatch {α : Type} {Q : α → Prop} {x : ModelIO α}
    {h : IO.Error → ModelIO α} (hx : x.LocalTo P Q) (hh : ∀ e, (h e).LocalTo P Q) :
    (tryCatchThe IO.Error x h : ModelIO α).LocalTo P Q := by
  refine ⟨fun fs₁ fs₂ hP => ?_, fun fs hs a hs' ha => ?_⟩
  · funext hs o hs'
    have hh' : ∀ e, h e fs₁ = h e fs₂ := fun e => (hh e).1 _ _ hP
    show ((∃ a, o = .ok a ∧ x fs₁ hs (.ok a) hs') ∨
        (∃ e hs₁, x fs₁ hs (.error e) hs₁ ∧ h e fs₁ hs₁ o hs')) =
      ((∃ a, o = .ok a ∧ x fs₂ hs (.ok a) hs') ∨
        (∃ e hs₁, x fs₂ hs (.error e) hs₁ ∧ h e fs₂ hs₁ o hs'))
    rw [hx.1 _ _ hP]
    simp only [hh']
  · rcases (ModelIO.tryCatch_ok x h fs hs a hs').1 ha with ha | ⟨e, hs₁, -, ha⟩
    · exact hx.2 _ _ _ _ ha
    · exact (hh e).2 _ _ _ _ ha

theorem ModelIO.localTo_mapM {α β : Type} {f : α → ModelIO β} {Q : α → β → Prop} :
    ∀ {xs : List α}, (∀ a ∈ xs, (f a).LocalTo P (Q a)) →
      (xs.mapM f).LocalTo P (fun ys => ∀ y ∈ ys, ∃ a ∈ xs, Q a y)
  | [], _ => ModelIO.localTo_pure (by simp)
  | x :: xs, h => by
    rw [List.mapM_cons]
    refine (h x List.mem_cons_self).bind fun b hb => ?_
    refine (ModelIO.localTo_mapM fun a ha => h a (List.mem_cons_of_mem _ ha)).bind
      fun bs hbs => ModelIO.localTo_pure ?_
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, hb⟩
    · obtain ⟨a, ha, hq⟩ := hbs y hy
      exact ⟨a, List.mem_cons_of_mem _ ha, hq⟩

theorem ModelIO.localTo_mapExcept {α β ε : Type} {f : α → ModelIO (Except ε β)} :
    ∀ {xs : List α}, (∀ a ∈ xs, (f a).LocalTo P (fun _ => True)) →
      (mapExcept f xs : ModelIO _).LocalTo P (fun _ => True)
  | [], _ => ModelIO.localTo_pure_true
  | x :: xs, h => by
    simp only [mapExcept]
    refine (h x List.mem_cons_self).bind fun r _ => ?_
    split
    · exact ModelIO.localTo_pure_true
    · refine (ModelIO.localTo_mapExcept fun a ha => h a (List.mem_cons_of_mem _ ha)).bind
        fun _ _ => ?_
      split <;> exact ModelIO.localTo_pure_true

theorem ModelIO.localTo_foldReads {σ ρ : Type} {rd : ModelIO ByteArray} {csz size : Nat}
    {step : σ → ByteArray → ModelIO (Except ρ σ)} {fin : σ → ModelIO ρ}
    (hrd : rd.LocalTo P (fun _ => True)) (hstep : ∀ s c, (step s c).LocalTo P (fun _ => True))
    (hfin : ∀ s, (fin s).LocalTo P (fun _ => True)) (off : Nat) (s : σ) :
    (foldReads rd csz size step fin off s).LocalTo P (fun _ => True) := by
  rw [foldReads]
  split
  · refine hrd.bind fun c _ => (hstep s c).bind fun r _ => ?_
    split
    · exact ModelIO.localTo_pure_true
    · exact ModelIO.localTo_foldReads hrd hstep hfin _ _
  · exact hfin s
termination_by size - off
decreasing_by omega

/-! ## The file operations under the directories -/

variable {dirs : List System.FilePath}

theorem ModelIO.localTo_pathExists {p : System.FilePath} (hp : Under dirs p) :
    (CheckerIO.pathExists p : ModelIO Bool).LocalTo (FS.AgreeUnder dirs) (fun _ => True) :=
  ⟨fun fs₁ fs₂ h => by
    show (fun hs => ModelIO.ret (some (fs₁.real p).isSome) hs) =
      (fun hs => ModelIO.ret (some (fs₂.real p).isSome) hs)
    rw [(h p hp).1], fun _ _ _ _ _ => trivial⟩

theorem ModelIO.localTo_isDir {p : System.FilePath} (hp : Under dirs p) :
    (CheckerIO.isDir p : ModelIO Bool).LocalTo (FS.AgreeUnder dirs) (fun _ => True) :=
  ⟨fun fs₁ fs₂ h => by
    show (fun hs => ModelIO.ret (some (fs₁.dir p)) hs) = (fun hs => ModelIO.ret (some (fs₂.dir p)) hs)
    rw [(h p hp).2.1], fun _ _ _ _ _ => trivial⟩

theorem ModelIO.localTo_realPath {p : System.FilePath} (hp : Under dirs p) :
    (CheckerIO.realPath p : ModelIO System.FilePath).LocalTo (FS.AgreeUnder dirs)
      (fun _ => True) :=
  ⟨fun fs₁ fs₂ h => by
    show (fun hs => ModelIO.ret (fs₁.real p) hs) = (fun hs => ModelIO.ret (fs₂.real p) hs)
    rw [(h p hp).1], fun _ _ _ _ _ => trivial⟩

theorem ModelIO.localTo_readBinFile {p : System.FilePath} (hp : Under dirs p) :
    (CheckerIO.readBinFile p : ModelIO ByteArray).LocalTo (FS.AgreeUnder dirs) (fun _ => True) :=
  ⟨fun fs₁ fs₂ h => by
    show (fun hs => ModelIO.ret (fs₁.file p) hs) = (fun hs => ModelIO.ret (fs₂.file p) hs)
    rw [(h p hp).2.2], fun _ _ _ _ _ => trivial⟩

theorem ModelIO.localTo_fileSize {p : System.FilePath} (hp : Under dirs p) :
    (CheckerIO.fileSize p : ModelIO Nat).LocalTo (FS.AgreeUnder dirs) (fun _ => True) :=
  ⟨fun fs₁ fs₂ h => by
    show (fun hs => ModelIO.ret ((fs₁.file p).map (·.size)) hs) =
      (fun hs => ModelIO.ret ((fs₂.file p).map (·.size)) hs)
    rw [(h p hp).2.2], fun _ _ _ _ _ => trivial⟩

theorem ModelIO.localTo_openRead {p : System.FilePath} (hp : Under dirs p) :
    (CheckerIO.openRead (m := ModelIO) p).LocalTo (FS.AgreeUnder dirs) (fun _ => True) :=
  ⟨fun fs₁ fs₂ h => by
    show ModelIO.openRead p fs₁ = ModelIO.openRead p fs₂
    unfold ModelIO.openRead
    rw [(h p hp).2.2], fun _ _ _ _ _ => trivial⟩

theorem ModelIO.localTo_read (h : Nat) (n : USize) :
    (CheckerIO.read (m := ModelIO) h n).LocalTo P (fun _ => True) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => trivial⟩

namespace Frontend.Olean

/-- **A lookup inside the directories**: its path and fallback among them, and every root it
resolved found in one of them. -/
@[expose] def RootsIn (dirs : List System.FilePath) (R : Roots) : Prop :=
  (∀ d ∈ R.path, d ∈ dirs) ∧ (∀ d ∈ R.fallback, d ∈ dirs) ∧
    ∀ (r : Name) d, R.map[r]? = some (RootAt.dir d) → d ∈ dirs

theorem under_modDir {d : System.FilePath} (hd : d ∈ dirs) (m : Name) : Under dirs (modDir d m) :=
  ⟨d, hd, m, .inl rfl⟩

theorem under_modFile {d : System.FilePath} (hd : d ∈ dirs) (m : Name) (ext : String) :
    Under dirs (modFile d m ext) :=
  ⟨d, hd, m, .inr ⟨ext, rfl⟩⟩

theorem under_dir {d : System.FilePath} (hd : d ∈ dirs) : Under dirs d :=
  ⟨d, hd, .anonymous, .inl rfl⟩

theorem holdsRoot_local {d : System.FilePath} (hd : d ∈ dirs) (r : Name) :
    (holdsRoot r d : ModelIO Bool).LocalTo (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [holdsRoot]
  refine (ModelIO.localTo_isDir (under_modDir hd r)).bind fun b _ => ?_
  split
  · exact ModelIO.localTo_pure_true
  · exact ModelIO.localTo_pathExists (under_modFile hd r "olean")

theorem rootHits_local {sp : SearchPath} (hsp : ∀ d ∈ sp, d ∈ dirs) (r : Name) :
    (rootHits sp r : ModelIO RootAt).LocalTo (FS.AgreeUnder dirs)
      (fun a => ∀ d, a = RootAt.dir d → d ∈ sp) := by
  simp only [rootHits]
  refine (ModelIO.localTo_mapM (Q := fun d (y : System.FilePath × Bool) => y.1 = d)
    fun d hd => (holdsRoot_local (hsp d hd) r).bind fun b _ => ModelIO.localTo_pure rfl).bind
    fun held hheld => ?_
  have hmem : ∀ d ∈ (held.filter (·.2)).map (·.1), d ∈ sp := by
    intro d hd
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
    obtain ⟨a, ha, he⟩ := hheld y (List.mem_filter.mp hy).1
    exact he ▸ ha
  split
  · exact ModelIO.localTo_pure (by simp)
  · rename_i d heq
    exact ModelIO.localTo_pure (by rintro _ ⟨⟩; exact hmem d (by rw [heq]; simp))
  · rename_i d tl _ heq
    have hd : d ∈ sp := hmem d (by rw [heq]; simp)
    have htl : ∀ x ∈ d :: tl, x ∈ dirs := fun x hx => hsp x (hmem x (by rw [heq]; exact hx))
    refine (ModelIO.localTo_mapM (Q := fun _ _ => True) fun x hx =>
      (ModelIO.localTo_realPath (under_dir (htl x hx))).bind fun _ _ =>
        ModelIO.localTo_pure_true).bind fun _ _ => ?_
    split
    · exact ModelIO.localTo_pure (by rintro _ ⟨⟩; exact hd)
    · exact ModelIO.localTo_pure (by rintro _ ⟨⟩)

theorem rootAt_local {sp : SearchPath} (hsp : ∀ d ∈ sp, d ∈ dirs) (r : Name) :
    (rootAt sp r : ModelIO RootAt).LocalTo (FS.AgreeUnder dirs)
      (fun a => ∀ d, a = RootAt.dir d → d ∈ dirs) :=
  ((rootHits_local hsp r).weaken fun _ h d hd => hsp d (h d hd)).tryCatch fun _ =>
    ModelIO.localTo_pure (by rintro _ ⟨⟩)

theorem lookAt_local {path fallback : SearchPath} (hp : ∀ d ∈ path, d ∈ dirs)
    (hf : ∀ d ∈ fallback, d ∈ dirs) (r : Name) :
    (lookAt path fallback r : ModelIO RootAt).LocalTo (FS.AgreeUnder dirs)
      (fun a => ∀ d, a = RootAt.dir d → d ∈ dirs) := by
  simp only [lookAt]
  refine (rootAt_local hp r).bind fun a ha => ?_
  cases a with
  | missing => exact rootAt_local hf r
  | _ => exact ModelIO.localTo_pure ha

theorem Roots.rootOf_local {R : Roots} (hR : RootsIn dirs R) (r : Name) :
    (R.rootOf r : ModelIO RootAt).LocalTo (FS.AgreeUnder dirs)
      (fun a => ∀ d, a = RootAt.dir d → d ∈ dirs) := by
  simp only [Roots.rootOf]
  split
  · rename_i a ha
    exact ModelIO.localTo_pure fun d hd => hR.2.2 r d (hd ▸ ha)
  · exact lookAt_local hR.1 hR.2.1 r

theorem Roots.resolve_local {R : Roots} (hR : RootsIn dirs R) (m : Name) :
    (R.resolve m : ModelIO Roots).LocalTo (FS.AgreeUnder dirs) (RootsIn dirs) := by
  simp only [Roots.resolve]
  split
  · exact ModelIO.localTo_pure hR
  · refine (lookAt_local hR.1 hR.2.1 m.root).bind fun a ha => ModelIO.localTo_pure ?_
    refine ⟨hR.1, hR.2.1, fun r d hd => ?_⟩
    simp only [Std.HashMap.getElem?_insert] at hd
    split at hd
    · exact ha d (Option.some.inj hd)
    · exact hR.2.2 r d hd

theorem findModule_local {R : Roots} (hR : RootsIn dirs R) (m : Name) :
    (findModule R m : ModelIO (Except CheckError Located)).LocalTo (FS.AgreeUnder dirs)
      (fun x => ∀ loc, x = .ok loc → loc.dir ∈ dirs) := by
  simp only [findModule]
  refine (Roots.rootOf_local hR m.root).map _ fun a ha loc hl => ?_
  cases a <;> simp only [locatedOf, reduceCtorEq, Except.ok.injEq] at hl
  subst hl
  exact ha _ rfl

theorem oleanFailed_local {loc : Located} (hd : loc.dir ∈ dirs) (m : Name) (e : IO.Error) :
    (oleanFailed loc m e : ModelIO CheckError).LocalTo (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [oleanFailed]
  refine (ModelIO.localTo_pathExists (under_modFile hd m "olean")).bind fun b _ => ?_
  split
  · exact ModelIO.localTo_pure_true
  · refine (ModelIO.localTo_pathExists (under_modFile hd m "olean.server")).bind fun _ _ =>
      (ModelIO.localTo_pathExists (under_modFile hd m "olean.private")).bind fun _ _ => ?_
    repeat' split
    all_goals exact ModelIO.localTo_pure_true

theorem partFailed_local {loc : Located} (hd : loc.dir ∈ dirs) (m : Name) (ext : String)
    (e : IO.Error) :
    (partFailed loc m ext e : ModelIO CheckError).LocalTo (FS.AgreeUnder dirs)
      (fun _ => True) := by
  simp only [partFailed]
  refine (ModelIO.localTo_pathExists (under_modFile hd m ext)).bind fun b _ => ?_
  split <;> exact ModelIO.localTo_pure_true

theorem readPartOr_local {p : System.FilePath} (hp : Under dirs p)
    {absent : IO.Error → ModelIO CheckError}
    (ha : ∀ e, (absent e).LocalTo (FS.AgreeUnder dirs) (fun _ => True)) :
    (readPartOr p absent : ModelIO (Except CheckError Part)).LocalTo (FS.AgreeUnder dirs)
      (fun _ => True) := by
  simp only [readPartOr, readPart]
  exact ((ModelIO.localTo_readBinFile hp).bind fun _ _ =>
    ModelIO.localTo_pure_true).tryCatch
      fun e => (ha e).map (R := fun _ => True) _ fun _ _ => trivial

theorem foldChunks_local {σ ρ : Type} {p : System.FilePath} (hp : Under dirs p) (csz : USize)
    (init : σ) (step : σ → ByteArray → Except ρ σ) (fin : σ → ρ) :
    (foldChunks p csz init step fin : ModelIO ρ).LocalTo (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [foldChunks]
  exact (ModelIO.localTo_fileSize hp).bind fun _ _ => (ModelIO.localTo_openRead hp).bind
    fun h _ => ModelIO.localTo_foldReads (ModelIO.localTo_read h csz)
      (fun _ _ => ModelIO.localTo_pure_true) (fun _ => ModelIO.localTo_pure_true) _ _

theorem readImportsAt_local {loc : Located} (hd : loc.dir ∈ dirs) (m : Name) :
    (readImportsAt loc m : ModelIO (Except CheckError (Array ImportRec))).LocalTo
      (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [readImportsAt]
  refine (((foldChunks_local (under_modFile hd m "olean") _ _ _ _).map (R := fun _ => True) _
    fun _ _ => trivial).tryCatch fun e => (oleanFailed_local hd m e).map (R := fun _ => True) _
      fun _ _ => trivial).bind fun x _ => ?_
  split <;> exact ModelIO.localTo_pure_true

theorem moduleImports_local {R : Roots} (hR : RootsIn dirs R) (m : Name) :
    (moduleImports R m : ModelIO (Except CheckError (Array ImportRec))).LocalTo
      (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [moduleImports]
  refine (findModule_local hR m).bind fun x hx => ?_
  split
  · exact ModelIO.localTo_pure_true
  · exact readImportsAt_local (hx _ rfl) m

theorem readFilesAt_local {loc : Located} (hd : loc.dir ∈ dirs) (m : Name) (level : OLeanLevel) :
    (readFilesAt loc m level : ModelIO (Except CheckError ModFiles)).LocalTo
      (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [readFilesAt]
  refine (readPartOr_local (under_modFile hd m "olean") (oleanFailed_local hd m)).bind
    fun x _ => ?_
  split
  · exact ModelIO.localTo_pure_true
  · split
    · exact ModelIO.localTo_pure_true
    split
    · refine (ModelIO.localTo_pathExists (under_modFile hd m "olean.server")).bind fun _ _ =>
        (ModelIO.localTo_pathExists (under_modFile hd m "olean.private")).bind fun _ _ => ?_
      split <;> exact ModelIO.localTo_pure_true
    refine (readPartOr_local (under_modFile hd m "olean.server")
      (partFailed_local hd m "olean.server")).bind fun y _ => ?_
    split
    · exact ModelIO.localTo_pure_true
    · split
      · refine (ModelIO.localTo_pathExists (under_modFile hd m "olean.private")).bind
          fun _ _ => ?_
        split <;> exact ModelIO.localTo_pure_true
      refine (readPartOr_local (under_modFile hd m "olean.private")
        (partFailed_local hd m "olean.private")).bind fun z _ => ?_
      split <;> exact ModelIO.localTo_pure_true

theorem readFiles_local {R : Roots} (hR : RootsIn dirs R) (m : Name) (level : OLeanLevel) :
    (readFiles R m level : ModelIO (Except CheckError ModFiles)).LocalTo
      (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [readFiles]
  refine (findModule_local hR m).bind fun x hx => ?_
  split
  · exact ModelIO.localTo_pure_true
  · exact readFilesAt_local (hx _ rfl) m level

theorem closureGo_local : ∀ (fuel : Nat) (sp : Roots) (stack : List (Name × Bool))
    (seen done : Std.HashSet Name) (out : Array Name), RootsIn dirs sp →
    (closureGo sp fuel stack seen done out : ModelIO _).LocalTo (FS.AgreeUnder dirs)
      (fun x => ∀ o T, x = .ok (o, T) → RootsIn dirs T)
  | _, sp, [], _, _, _, hR => by
    simp only [closureGo]
    exact ModelIO.localTo_pure fun o T h => by cases h; exact hR
  | 0, sp, _ :: _, _, _, _, hR => by
    simp only [closureGo]
    exact ModelIO.localTo_pure fun o T h => by cases h
  | fuel + 1, sp, (m, true) :: rest, seen, done, out, hR => by
    simp only [closureGo]
    exact closureGo_local fuel sp rest _ _ _ hR
  | fuel + 1, sp, (m, false) :: rest, seen, done, out, hR => by
    simp only [closureGo]
    split
    · exact closureGo_local fuel sp rest _ _ _ hR
    · refine (Roots.resolve_local hR m).bind fun sp' hR' =>
        (moduleImports_local hR' m).bind fun x _ => ?_
      split
      · exact ModelIO.localTo_pure fun o T h => by cases h
      · split
        · exact ModelIO.localTo_pure fun o T h => by cases h
        · exact closureGo_local fuel sp' _ _ _ _ hR'

theorem closureOrder_local {sp : Roots} (hR : RootsIn dirs sp) (roots : Array Name) :
    (closureOrder sp roots : ModelIO _).LocalTo (FS.AgreeUnder dirs)
      (fun x => ∀ o T, x = .ok (o, T) → RootsIn dirs T) :=
  closureGo_local _ sp _ _ _ _ hR

theorem loadModule_local {sp : Roots} (hR : RootsIn dirs sp) (n : ReadNotes) (total : Nat)
    (x : Name × Nat) :
    (loadModule sp n total x : ModelIO _).LocalTo (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [loadModule]
  refine (readFiles_local hR x.1 .private).bind fun y _ => ?_
  split
  · exact (ModelIO.localTo_liftIO _).bind fun _ _ => ModelIO.localTo_pure_true
  · exact ModelIO.localTo_pure_true

theorem loadClosure_local {sp : Roots} (hR : RootsIn dirs sp) (n : ReadNotes)
    (roots : Array Name) (jobs : Nat) :
    (loadClosure sp n roots jobs : ModelIO _).LocalTo (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [loadClosure]
  refine (ModelIO.localTo_liftIO _).bind fun _ _ => (closureOrder_local hR roots).bind
    fun x hx => ?_
  split
  · exact ModelIO.localTo_pure_true
  · have hT := hx _ _ rfl
    refine (ModelIO.localTo_liftIO _).bind fun _ _ => ?_
    exact (ModelIO.localTo_mapExcept fun y _ => loadModule_local hT n _ y).map _
      fun _ _ => trivial

/-- **The whole read, through a lookup inside the directories, is local to them.** -/
theorem readOleansAt_local {R : Roots} (hR : RootsIn dirs R) (roots : Array Name)
    (constants : Option (Array Name)) (jobs : Nat) (pace : Pace) (lenient homes : Bool) :
    (readOleansAt R roots constants jobs pace lenient homes : ModelIO _).LocalTo
      (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [readOleansAt]
  refine (ModelIO.localTo_liftIO _).bind fun n _ => (loadClosure_local hR n roots jobs).bind
    fun x _ => ?_
  repeat' (first
    | exact ModelIO.localTo_pure_true
    | refine (ModelIO.localTo_liftIO _).bind fun _ _ => ?_
    | split)

/-! ## T1 -/

/-- **The challenge's view of a snapshot**: the outcomes of its read through the directories
`dirs` alone (`Driver.CmpReq.chalRoots`), from the module `C`, of the constants `cs` (`--constant`)
or all of its closure, failure included.  The job count and the heartbeat's pace do not change
the outcomes in the model; the view fixes them at one job and no heartbeat. -/
@[expose] def challengeView (dirs : SearchPath) (C : Name) (cs : Option (Array Name)) (fs : FS) :
    Except IO.Error (Except (CheckError × Nat) OleanRead) → Prop :=
  fun o => ∃ hs hs', (readOleansAt { path := dirs } #[C] cs 1 .off true true : ModelIO _) fs hs o hs'

/-- **T1, the challenge is local to the trusted directories**: on two snapshots that agree on
every path the reader can form under `dirs`, the challenge's read has the same outcomes,
failure included. -/
theorem challenge_local {dirs : SearchPath} {C : Name} {cs : Option (Array Name)} {fs₁ fs₂ : FS}
    (h : FS.AgreeUnder dirs fs₁ fs₂) :
    challengeView dirs C cs fs₁ = challengeView dirs C cs fs₂ := by
  have hl := (readOleansAt_local (dirs := dirs) (R := { path := dirs })
    ⟨fun _ h => h, fun _ h => by simp at h, fun _ _ h => by simp at h⟩ #[C] cs 1 .off true
      true).1 fs₁ fs₂ h
  unfold challengeView
  rw [hl]

end Frontend.Olean

end ConLeche
