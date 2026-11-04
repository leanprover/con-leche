module

public import ConLeche.Frontend.Olean.Records
public import ConLeche.Verify.Frontend.ModelIO
public import ConLeche.Verify.Frontend.Olean.Reads

/-!
# The `.olean` reads on a file system snapshot

The reads of `ConLeche/Frontend/Olean/Files.lean` in the model `ModelIO`,
where they use the file operations alone, so that a snapshot determines each
(`ModelIO.Det`).

**A module's full read at its home settles its other reads** on the same
snapshot, in one process or in two: where `readModule` has a value,

* the exported file is the one it decoded (`readModule_ok`), so that an
  importer's read (`readExported_of_home`), a light read
  (`readExportedLight_of_home`) and the read of the imports off the file's
  start (`readImports_of_home`, `moduleImports_of_home`) cannot fail, and
  return what the home has;
* the reads of a part of the module, pure functions of the region and the
  root the full parses have run on, are `ConLeche/Verify/Frontend/Olean/Reads.lean`.

`foldList_hdr` and `foldList_hdr_complete` are the two directions of the
forward read of a file's start: what it finds is `importsPre` of the whole
file, and it finds that wherever the file is valid and has such imports.

`readOleans_ok`: the records of a run are made of modules each read by
`readModule` on the snapshot.
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## Locating a module -/

theorem pathExists_det (p : System.FilePath) (fs : FS) :
    (CheckerIO.pathExists p : ModelIO Bool).Det fs := ⟨some (fs.real p).isSome, rfl⟩

theorem realPath_det (p : System.FilePath) (fs : FS) :
    (CheckerIO.realPath p : ModelIO System.FilePath).Det fs := ⟨fs.real p, rfl⟩

theorem locateIn_det (m : Name) (d : System.FilePath) (fs : FS) :
    (locateIn m d : ModelIO _).Det fs := by
  refine ModelIO.det_bind (ModelIO.det_mapM fun e _ => ?_) fun _ => ModelIO.det_pure _ _
  refine ModelIO.det_bind (pathExists_det _ _) fun x => ?_
  cases x
  · exact ModelIO.det_pure _ _
  · exact ModelIO.det_bind (realPath_det _ _) fun _ => ModelIO.det_pure _ _

theorem locateHits_det (sp : SearchPath) (m : Name) (fs : FS) :
    (locateHits sp m : ModelIO _).Det fs :=
  ModelIO.det_bind (ModelIO.det_mapM fun d _ => locateIn_det m d fs) fun _ => ModelIO.det_pure _ _

/-- A module located: the directories' answers were values. -/
theorem locateModule_ok {sp : SearchPath} {m : Name} {fs : FS} {l : Option Located}
    (h : (locateModule sp m : ModelIO _) fs (.ok (.ok l))) :
    (locateModule sp m : ModelIO _) fs = ModelIO.answer (some (.ok l)) := by
  have key : ∀ hits, (locateHits sp m : ModelIO _) fs = ModelIO.answer (some hits) →
      (locateModule sp m : ModelIO _) fs = ModelIO.answer (some (locateOf m hits)) := by
    intro hits hh
    simp only [locateModule]
    rw [ModelIO.bind_det (ModelIO.tryCatch_det (ModelIO.map_det hh))]
    rfl
  simp only [locateModule, ModelIO.bind_ok, ModelIO.tryCatch_ok] at h
  obtain ⟨x, hx, hr⟩ := h
  rcases hx with hx | ⟨e, -, hx⟩
  · simp only [ModelIO.map_ok] at hx
    obtain ⟨hits, hh, rfl⟩ := hx
    have hd := (locateHits_det sp m fs).of_ok hh
    rw [key hits hd]
    simp only at hr
    have : locateOf m hits = .ok l := by simpa [eq_comm] using hr
    rw [this]
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
    subst hx
    simp at hr

/-- A module found: the snapshot determines the location. -/
theorem findModule_locate {sp : SearchPath} {m : Name} {fs : FS} {loc : Located}
    (h : (findModule sp m : ModelIO _) fs (.ok (.ok loc))) :
    (locateModule sp m : ModelIO _) fs = ModelIO.answer (some (.ok (some loc))) := by
  simp only [findModule, ModelIO.bind_ok] at h
  obtain ⟨x, hx, hr⟩ := h
  rcases x with e | _ | l
  · simp at hr
  · simp at hr
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at hr
    cases hr
    exact locateModule_ok hx

theorem findModule_ok {sp : SearchPath} {m : Name} {fs : FS} {loc : Located}
    (h : (findModule sp m : ModelIO _) fs (.ok (.ok loc))) :
    (findModule sp m : ModelIO _) fs = ModelIO.answer (some (.ok loc)) := by
  simp only [findModule]
  rw [ModelIO.bind_det (findModule_locate h)]
  rfl

/-! ## A file -/

theorem readBinFile_ok {p : System.FilePath} {fs : FS} {b : ByteArray} :
    (CheckerIO.readBinFile p : ModelIO ByteArray) fs (.ok b) ↔ fs.file p = some b :=
  ModelIO.answer_ok _ _

theorem readBinFile_det {p : System.FilePath} {fs : FS} {b : ByteArray}
    (h : fs.file p = some b) :
    (CheckerIO.readBinFile p : ModelIO ByteArray) fs = ModelIO.answer (some b) := by
  show ModelIO.answer (fs.file p) = _
  rw [h]

/-- **A part read off the snapshot** is the validation of its bytes. -/
theorem readPart_ok {p : System.FilePath} {fs : FS} {x : Except CheckError Part}
    (h : (readPart p : ModelIO _) fs (.ok x)) :
    ∃ b, fs.file p = some b ∧ x = Part.ofBytes p.toString b := by
  simp only [readPart, ModelIO.bind_ok, readBinFile_ok, ModelIO.pure_iff, Except.ok.injEq] at h
  exact h

theorem readPart_det {p : System.FilePath} {fs : FS} {b : ByteArray} (h : fs.file p = some b) :
    (readPart p : ModelIO _) fs = ModelIO.answer (some (Part.ofBytes p.toString b)) := by
  simp only [readPart]
  rw [ModelIO.bind_det (readBinFile_det h)]
  rfl

/-! ## The forward read of a file's start -/

theorem except_map_ok {ε α β : Type} {e : Except ε α} {f : α → β} {y : β}
    (h : e.map f = .ok y) : ∃ a, e = .ok a ∧ f a = y := by
  cases e with
  | error x => cases h
  | ok a => exact ⟨a, rfl, by simpa [Except.map] using h⟩

theorem extract_step {b : ByteArray} {off csz : Nat} (ho : off ≤ b.size) (hc : 0 < csz) :
    b.extract 0 off ++ b.extract off (min (off + csz) b.size) =
      b.extract 0 (min (off + csz) b.size) := by
  rw [ByteArray.extract_append_extract]
  congr 1 <;> omega

/-- **The forward read finds what the file holds**: from the bytes before
`off`, the reads from `off` on, folded by the header read's step, give
imports only where the file's bytes give them. -/
theorem foldList_hdr (path : String) (csz : Nat) (b : ByteArray) (x : Array ImportRec) :
    ∀ off acc, off ≤ b.size → acc = b.extract 0 off →
      foldList (hdrStep path) (hdrFin path) acc (readsFrom csz b off) = .ok (some x) →
      importsPre b = some x := by
  intro off
  induction off using readsFrom.induct (csz := csz) (b := b) with
  | case1 off hc ih =>
    intro acc ho hacc h
    rw [readsFrom.eq_1] at h
    simp only [hc, and_self, dite_true] at h
    simp only [foldList] at h
    have happ := extract_step (b := b) ho hc.1
    rw [← hacc] at happ
    cases hs : hdrStep path acc (b.extract off (min (off + csz) b.size)) with
    | ok s =>
      simp only [hs] at h
      unfold hdrStep at hs
      rw [happ] at hs
      dsimp only at hs
      split at hs
      · simp only [Except.ok.injEq] at hs
        exact ih s (by omega) hs.symm h
      · cases hs
    | error r =>
      simp only [hs] at h
      subst h
      unfold hdrStep at hs
      rw [happ] at hs
      dsimp only at hs
      split at hs
      · cases hs
      · simp only [Except.error.injEq] at hs
        obtain ⟨_, -, hx⟩ := except_map_ok hs
        exact importsPre_extract hx
  | case2 off hc =>
    intro acc _ hacc h
    rw [readsFrom.eq_1] at h
    simp only [hc, dite_false, foldList, hdrFin] at h
    obtain ⟨_, -, hx⟩ := except_map_ok h
    rw [hacc] at hx
    exact importsPre_extract hx

/-- **And it finds it wherever it is**: on a valid file whose bytes give
imports, read in whole words, the forward read gives them. -/
theorem foldList_hdr_complete {path : String} {csz : Nat} {b : ByteArray} {ex : Part}
    {x : Array ImportRec} (hp : Part.ofBytes path b = .ok ex) (hi : importsPre b = some x)
    (h0 : 0 < csz) (h8 : csz % 8 = 0) :
    ∀ off acc, off ≤ b.size → off % 8 = 0 → acc = b.extract 0 off →
      foldList (hdrStep path) (hdrFin path) acc (readsFrom csz b off) = .ok (some x) := by
  have hb8 : b.size % 8 = 0 := by
    have := (Part.ofBytes_checks hp).2.2.2.2.1
    simpa using this
  intro off
  induction off using readsFrom.induct (csz := csz) (b := b) with
  | case1 off hc ih =>
    intro acc ho ho8 hacc
    rw [readsFrom.eq_1]
    simp only [hc, and_self, dite_true, foldList]
    have happ := extract_step (b := b) ho hc.1
    rw [← hacc] at happ
    have hk8 : (min (off + csz) b.size) % 8 = 0 := by omega
    have hstep : hdrStep path acc (b.extract off (min (off + csz) b.size)) =
        (match hdrWalk (b.extract 0 (min (off + csz) b.size)) dataStart with
         | .short => .ok (b.extract 0 (min (off + csz) b.size))
         | _ => .error ((Part.ofBytes path (b.extract 0 (min (off + csz) b.size))).map
             fun _ => importsPre (b.extract 0 (min (off + csz) b.size)))) := by
      simp only [hdrStep, happ]
      cases hdrWalk (b.extract 0 (min (off + csz) b.size)) dataStart <;> rfl
    rw [hstep]
    by_cases hw : hdrWalk (b.extract 0 (min (off + csz) b.size)) dataStart = .short
    · simp only [hw]
      exact ih _ (by omega) hk8 rfl
    · have hsz := hdrWalk_size hw
      have hsz8 : (b.extract 0 (min (off + csz) b.size)).size % 8 = 0 := by
        simp only [ByteArray.size_extract]
        omega
      obtain ⟨ex', hx'⟩ := Part.ofBytes_prefix hp (by unfold dataStart at *; omega) hsz8
      cases hwk : hdrWalk (b.extract 0 (min (off + csz) b.size)) dataStart with
      | short => exact absurd hwk hw
      | found c e => simp only [hx', Except.map, importsPre_prefix hw hi]
      | bad => simp only [hx', Except.map, importsPre_prefix hw hi]
  | case2 off hc =>
    intro acc ho _ hacc
    rw [readsFrom.eq_1]
    have hoff : off = b.size := by
      have : ¬ off < b.size := fun h => hc ⟨h0, h⟩
      omega
    have hacc' : acc = b := by rw [hacc, hoff]; simp
    simp only [hc, dite_false, foldList, hdrFin, hacc', hp, Except.map, hi]

theorem hdrChunk_toNat : hdrChunk.toNat = 4096 := by
  simp [hdrChunk]

/-- **The header read's value** is `importsPre` of the file's bytes. -/
theorem readImportsAt_ok {loc : Located} {m : Name} {fs : FS} {imps : Array ImportRec}
    (h : (readImportsAt loc m : ModelIO _) fs (.ok (.ok imps))) :
    ∃ b, fs.file (modFile loc.dir m "olean") = some b ∧ importsPre b = some imps := by
  simp only [readImportsAt, ModelIO.bind_ok] at h
  obtain ⟨x, hx, hr⟩ := h
  obtain ⟨b, hb, rfl⟩ := foldChunks_model hx
  refine ⟨b, hb, ?_⟩
  cases hf : foldList (hdrStep (modFile loc.dir m "olean").toString)
      (hdrFin (modFile loc.dir m "olean").toString) ByteArray.empty
      (readsFrom hdrChunk.toNat b 0) with
  | error e => simp [hf] at hr
  | ok o =>
    rw [hf] at hr
    cases o with
    | none => simp at hr
    | some i =>
      simp only [ModelIO.pure_iff, Except.ok.injEq] at hr
      cases hr
      exact foldList_hdr _ _ b imps 0 ByteArray.empty (by simp) (by simp) hf

/-- **The header read of a valid file with imports** is determined. -/
theorem readImportsAt_det {loc : Located} {m : Name} {fs : FS} {b : ByteArray} {ex : Part}
    {imps : Array ImportRec} (hb : fs.file (modFile loc.dir m "olean") = some b)
    (hp : Part.ofBytes (modFile loc.dir m "olean").toString b = .ok ex)
    (hi : importsPre b = some imps) :
    (readImportsAt loc m : ModelIO _) fs = ModelIO.answer (some (.ok imps)) := by
  simp only [readImportsAt]
  rw [ModelIO.bind_det (foldChunks_det _ _ _ _ hb), hdrChunk_toNat,
    foldList_hdr_complete hp hi (by decide) (by decide) 0 _ (by simp) (by simp) (by simp)]
  rfl

/-! ## The home's full read -/

/-- **A module's full read at its location**, unfolded: its exported file
read in full, and for a module of the module system, its other two files
read with it. -/
theorem readModuleAt_ok {loc : Located} {m : Name} {fs : FS} {r : ModRead}
    (h : (readModuleAt loc m : ModelIO _) fs (.ok (.ok r))) :
    ∃ b ex er, fs.file (modFile loc.dir m "olean") = some b ∧
      Part.ofBytes (modFile loc.dir m "olean").toString b = .ok ex ∧
      parseExported m ex = .ok er ∧
      ((er.isModule = false ∧ r = classicModule m er) ∨
        ∃ bs bp s p, fs.file (modFile loc.dir m "olean.server") = some bs ∧
          fs.file (modFile loc.dir m "olean.private") = some bp ∧
          Part.ofBytes (modFile loc.dir m "olean.server").toString bs = .ok s ∧
          Part.ofBytes (modFile loc.dir m "olean.private").toString bp = .ok p ∧
          er.isModule = true ∧ parseModule m er ex s p = .ok r) := by
  simp only [readModuleAt, readExpAt, ModelIO.bind_ok] at h
  obtain ⟨x, hx, h⟩ := h
  obtain ⟨b, hb, rfl⟩ := readPart_ok hx
  cases hp : Part.ofBytes (modFile loc.dir m "olean").toString b with
  | error e => simp [hp] at h
  | ok ex =>
    simp only [hp] at h
    cases he : parseExported m ex with
    | error e => simp [he] at h
    | ok er =>
      simp only [he] at h
      refine ⟨b, ex, er, hb, hp, he, ?_⟩
      cases hm : er.isModule with
      | false =>
        refine .inl ⟨rfl, ?_⟩
        simp only [hm, Bool.not_false, ite_true] at h
        split at h
        · simp at h
        · simpa [eq_comm] using h
      | true =>
        refine .inr ?_
        simp only [hm, Bool.not_true, Bool.false_eq_true, ite_false] at h
        by_cases hs : loc.hasServer = true
        · by_cases hq : loc.hasPrivate = true
          · simp only [hs, hq, Bool.not_true, Bool.false_eq_true, ite_false, ModelIO.bind_ok] at h
            obtain ⟨xs, hxs, xp, hxp, h⟩ := h
            obtain ⟨bs, hbs, rfl⟩ := readPart_ok hxs
            obtain ⟨bp, hbp, rfl⟩ := readPart_ok hxp
            cases ho : Part.ofBytes (modFile loc.dir m "olean.server").toString bs with
            | error e => simp [ho] at h
            | ok s =>
              cases hr : Part.ofBytes (modFile loc.dir m "olean.private").toString bp with
              | error e => simp [ho, hr] at h
              | ok p =>
                simp only [ho, hr, ModelIO.pure_iff, Except.ok.injEq] at h
                exact ⟨bs, bp, s, p, hbs, hbp, ho, hr, rfl, h.symm⟩
          · simp [hs, hq] at h
        · simp [hs] at h

/-- **A module's full read**, unfolded: its location is determined, and
the read at it is `readModuleAt_ok`'s. -/
theorem readModule_ok {sp : SearchPath} {m : Name} {fs : FS} {r : ModRead}
    (h : (readModule sp m : ModelIO _) fs (.ok (.ok r))) :
    ∃ loc, (findModule sp m : ModelIO _) fs = ModelIO.answer (some (.ok loc)) ∧
      (readModuleAt loc m : ModelIO _) fs (.ok (.ok r)) := by
  simp only [readModule, ModelIO.bind_ok] at h
  obtain ⟨x, hx, h⟩ := h
  rcases x with e | loc
  · simp at h
  · exact ⟨loc, findModule_ok hx, h⟩

/-- What the home's read holds of the exported part. -/
theorem readModuleAt_exported {m : Name} {er : ModDecoded} {r : ModRead}
    (h : (er.isModule = false ∧ r = classicModule m er) ∨
        ∃ ex s p, er.isModule = true ∧ parseModule m er ex s p = .ok r) :
    r.exported = er.constants ∧ r.imports = er.imports := by
  rcases h with ⟨-, rfl⟩ | ⟨ex, s, p, -, hm⟩
  · exact ⟨rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hi, _, he⟩ := parseModule_full hm
    exact ⟨he, hi⟩

/-! ## What the home's read settles -/

/-- **The home's read settles its exported part** on the snapshot: the
location and the file are determined, the exported part is valid and its full
read succeeds, with the home's imports and exported constants. -/
theorem home_exported {sp : SearchPath} {m : Name} {fs : FS} {r : ModRead}
    (h : (readModule sp m : ModelIO _) fs (.ok (.ok r))) :
    ∃ loc b ex er, (findModule sp m : ModelIO _) fs = ModelIO.answer (some (.ok loc)) ∧
      fs.file (modFile loc.dir m "olean") = some b ∧
      Part.ofBytes (modFile loc.dir m "olean").toString b = .ok ex ∧
      parseExported m ex = .ok er ∧ r.exported = er.constants ∧ r.imports = er.imports := by
  obtain ⟨loc, hf, hr⟩ := readModule_ok h
  obtain ⟨b, ex, er, hb, hp, he, hc⟩ := readModuleAt_ok hr
  refine ⟨loc, b, ex, er, hf, hb, hp, he, readModuleAt_exported (m := m) ?_⟩
  rcases hc with hc | ⟨_, _, s, p, _, _, _, _, hm, hq⟩
  · exact .inl hc
  · exact .inr ⟨ex, s, p, hm, hq⟩

/-- **An importer's read of a module with a home's read**: determined, the
same constants. -/
theorem readExported_of_home {sp : SearchPath} {m : Name} {fs : FS} {r : ModRead}
    (h : (readModule sp m : ModelIO _) fs (.ok (.ok r))) :
    ∃ er, (readExported sp m : ModelIO _) fs = ModelIO.answer (some (.ok er)) ∧
      r.exported = er.constants ∧ r.imports = er.imports := by
  obtain ⟨loc, b, ex, er, hf, hb, hp, he, hc, hi⟩ := home_exported h
  refine ⟨er, ?_, hc, hi⟩
  simp only [readExported]
  rw [ModelIO.bind_det hf]
  simp only [readExpAt]
  rw [ModelIO.bind_det (readPart_det hb), hp]
  simp only [he]
  rfl

/-- **The read of a module's imports off its file's start, with a home's
read**: determined, the home's imports. -/
theorem readImports_of_home {sp : SearchPath} {m : Name} {fs : FS} {r : ModRead}
    (h : (readModule sp m : ModelIO _) fs (.ok (.ok r))) :
    (readImports sp m : ModelIO _) fs = ModelIO.answer (some (.ok (some r.imports))) := by
  obtain ⟨loc, b, ex, er, hf, hb, hp, he, -, hi⟩ := home_exported h
  have hl := findModule_locate (sp := sp) (m := m) (fs := fs) (loc := loc)
    (by rw [hf]; exact (ModelIO.answer_ok _ _).2 rfl)
  have himp : importsPre b = some r.imports := by
    have := (parseExported_full he).2
    rwa [Part.ofBytes_bytes hp, ← hi] at this
  simp only [readImports]
  rw [ModelIO.bind_det hl]
  simp only
  rw [ModelIO.bind_det (readImportsAt_det hb hp himp)]
  rfl

/-- **The closure's read of a module's imports, with a home's read**:
determined, the names of the home's imports. -/
theorem moduleImports_of_home {sp : SearchPath} {m : Name} {fs : FS} {r : ModRead}
    (h : (readModule sp m : ModelIO _) fs (.ok (.ok r))) :
    (moduleImports sp m : ModelIO _) fs =
      ModelIO.answer (some (.ok (r.imports.map (·.module)))) := by
  obtain ⟨loc, b, ex, er, hf, hb, hp, he, -, hi⟩ := home_exported h
  have himp : importsPre b = some r.imports := by
    have := (parseExported_full he).2
    rwa [Part.ofBytes_bytes hp, ← hi] at this
  simp only [moduleImports]
  rw [ModelIO.bind_det hf]
  simp only
  rw [ModelIO.bind_det (readImportsAt_det hb hp himp)]
  rfl

/-- **A light read of a module with a home's read**: determined, the exported
part's: its header, and per stored constant its location with the name, kind
and filter of the constant the exported read holds there. -/
theorem readExportedLight_of_home {sp : SearchPath} {m : Name} {fs : FS} {r : ModRead}
    (h : (readModule sp m : ModelIO _) fs (.ok (.ok r))) :
    ∃ ex er sk, parseExported m ex = .ok er ∧
      moduleSkel (Region.single ex) ex.root = some sk ∧
      (readExportedLight sp m : ModelIO _) fs = ModelIO.answer (some (.ok (ex,
        ⟨⟨er.isModule, er.imports⟩,
          ((sk.consts.zip er.constants.toList).map fun p => LightConst.ofEntry p.1 p.2).toArray⟩))) ∧
      r.exported = er.constants ∧ r.imports = er.imports := by
  obtain ⟨loc, b, ex, er, hf, hb, hp, he, hc, hi⟩ := home_exported h
  have hfull := (parseExported_full he).1
  obtain ⟨-, sk, hs, -, -, -⟩ := parseFull_some hfull
  refine ⟨ex, er, sk, he, hs, ?_, hc, hi⟩
  simp only [readExportedLight]
  rw [ModelIO.bind_det hf]
  simp only [readExpAt]
  rw [ModelIO.bind_det (readPart_det hb), hp]
  simp only [readLight_of_full hfull hs]
  rfl

/-! ## The whole read -/

/-- The sequential map's value: one value of each element's action, here
each saying which element it is of. -/
theorem mapExcept_ok {α β ε : Type} {f : α → ModelIO (Except ε β)} {fs : FS} {g : β → α}
    {Q : β → Prop} (hk : ∀ x y, f x fs (.ok (.ok y)) → g y = x ∧ Q y) :
    ∀ {xs : List α} {ys : List β}, (mapExcept f xs : ModelIO _) fs (.ok (.ok ys)) →
      ys.map g = xs ∧ ∀ y ∈ ys, Q y
  | [], ys, h => by
    simp only [mapExcept, ModelIO.pure_iff, Except.ok.injEq] at h
    cases h
    simp
  | x :: xs, ys, h => by
    simp only [mapExcept, ModelIO.bind_ok] at h
    obtain ⟨a, ha, h⟩ := h
    rcases a with e | b
    · simp at h
    · simp only [ModelIO.bind_ok] at h
      obtain ⟨c, hc, h⟩ := h
      rcases c with e | bs
      · simp at h
      · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
        cases h
        obtain ⟨h1, h2⟩ := hk _ _ ha
        obtain ⟨h3, h4⟩ := mapExcept_ok hk hc
        simp only [List.map_cons, h1, h3, List.mem_cons, forall_eq_or_imp, true_and]
        exact ⟨h2, h4⟩

/-- **The records of a run** are made of the import closure's modules, each
read by `readModule` on the snapshot, whatever the job count. -/
theorem readOleans_ok {sp : SearchPath} {roots : Array Name} {jobs : Nat} {fs : FS}
    {ds : Array Declaration}
    (h : (readOleans sp roots jobs : ModelIO _) fs (.ok (.ok ds))) :
    ∃ (order : Array Name) (ls : List Loaded) (mg : Merged),
      (closureOrder sp roots : ModelIO _) fs (.ok (.ok order)) ∧
      ls.map (·.name) = order.toList ∧
      (∀ l ∈ ls, ∃ r, (readModule sp l.name : ModelIO _) fs (.ok (.ok r)) ∧
        l.constants = r.constants.map CEntry.ofRead) ∧
      mergeAll ls.toArray = .ok mg ∧ coverageOk mg (emitAll mg) = .ok () ∧
      declsOf (emitAll mg) = .ok ds := by
  simp only [readOleans, loadClosure, ModelIO.bind_ok] at h
  obtain ⟨x, ⟨o, ho, hx⟩, h⟩ := h
  rcases o with e | order
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
    subst hx
    simp at h
  · simp only [ModelIO.bind_ok] at hx
    obtain ⟨y, hy, hx⟩ := hx
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
    subst hx
    rcases y with e | ls
    · simp [Except.map] at h
    · simp only [Except.map] at h
      cases hm : mergeAll ls.toArray with
      | error e => simp [hm] at h
      | ok mg =>
        simp only [hm] at h
        cases hc : coverageOk mg (emitAll mg) with
        | error e => simp [hc] at h
        | ok u =>
          simp only [hc, ModelIO.pure_iff, Except.ok.injEq] at h
          have hF : (mapExcept (loadModule sp) order.toList : ModelIO _) fs (.ok (.ok ls)) := hy
          obtain ⟨h1, h2⟩ := mapExcept_ok (g := Loaded.name) (Q := fun l => ∃ r,
              (readModule sp l.name : ModelIO _) fs (.ok (.ok r)) ∧
                l.constants = r.constants.map CEntry.ofRead) (fun m l hl => by
            simp only [loadModule, ModelIO.bind_ok] at hl
            obtain ⟨z, hz, hl⟩ := hl
            rcases z with e | r
            · simp at hl
            · simp only [ModelIO.pure_iff, Except.ok.injEq] at hl
              subst hl
              exact ⟨rfl, r, hz, rfl⟩) hF
          exact ⟨order, ls, mg, ho, h1, h2, hm, by cases u; exact hc, h.symm⟩

end ConLeche.Frontend.Olean
