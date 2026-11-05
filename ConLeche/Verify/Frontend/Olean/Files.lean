module

public import ConLeche.Frontend.Olean.Records
public import ConLeche.Verify.Frontend.Olean.Closure
public import ConLeche.Verify.Frontend.Olean.Merge
import ConLeche.Verify.Frontend.Olean.Emit
import ConLeche.Verify.Frontend.Olean.View
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Reads
public import ConLeche.Verify.Frontend.ModelIO

/-!
# The `.olean` reads on a file system snapshot

The reads of `ConLeche/Frontend/Olean/Files.lean` in the model `ModelIO`, where they
use the file operations alone, so that a snapshot determines each (`ModelIO.Det`).

**A module's home read settles its other reads** on the same snapshot, in one
process or in two.  Where `readAllViews` has a value:

* every view's read is determined and returns that view (`readView_of_all`), and the
  files any view reads are the home's (`readFiles_of_all`), so that an importer's
  read of the exported view, holding `M.olean` alone, is the home's;
* where a view reads, the imports off the file's start are determined and are its
  imports (`moduleImports_of_view`);
* the reads of a part of a view are pure functions of those files:
  `ConLeche/Verify/Frontend/Olean/View.lean`.

`foldList_hdr` and `foldList_hdr_complete` are the two directions of the forward
read of a file's start: what it finds is `importsPre` of the whole file, and it
finds that wherever the file is valid and has such imports.

`readOleans_thm`: a theorem of the private view of a module of the closure (`InClosure`) is
among a run's records, with its statement.  `readOleans_ok`: the records of a run are made of
the private view of each module of the
closure, each read by `readView` on the snapshot: the order holds the roots and has every
module after its imports (`closureOrder_ok`, `ClosedOrder.view_imports`), and every constant
of those views stands in the merge (`mergeAll_ok`); the emission is
`ConLeche/Verify/Frontend/Olean/Emit.lean`.
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

/-- A module found: the snapshot determines the location. -/
theorem findModule_ok {sp : SearchPath} {m : Name} {fs : FS} {loc : Located}
    (h : (findModule sp m : ModelIO _) fs (.ok (.ok loc))) :
    (findModule sp m : ModelIO _) fs = ModelIO.answer (some (.ok loc)) := by
  have key : ∀ hits, (locateHits sp m : ModelIO _) fs = ModelIO.answer (some hits) →
      (findModule sp m : ModelIO _) fs = ModelIO.answer (some (locateOf m hits)) := by
    intro hits hh
    simp only [findModule]
    rw [ModelIO.bind_det (ModelIO.tryCatch_det (ModelIO.map_det hh))]
    rfl
  simp only [findModule, ModelIO.bind_ok, ModelIO.tryCatch_ok] at h
  obtain ⟨x, hx, hr⟩ := h
  rcases hx with hx | ⟨e, -, hx⟩
  · simp only [ModelIO.map_ok] at hx
    obtain ⟨hits, hh, rfl⟩ := hx
    have hd := (locateHits_det sp m fs).of_ok hh
    rw [key hits hd]
    simp only at hr
    have : locateOf m hits = .ok loc := by simpa [eq_comm] using hr
    rw [this]
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
    subst hx
    simp at hr

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

/-- **The files of a view**, unfolded: the location is determined, `M.olean` read, and
the rest as its flag and the level ask. -/
theorem readFiles_ok {sp : SearchPath} {m : Name} {level : OLeanLevel} {fs : FS} {f : ModFiles}
    (h : (readFiles sp m level : ModelIO _) fs (.ok (.ok f))) :
    ∃ loc b ex, (findModule sp m : ModelIO _) fs = ModelIO.answer (some (.ok loc)) ∧
      fs.file (modFile loc.dir m "olean") = some b ∧
      Part.ofBytes (modFile loc.dir m "olean").toString b = .ok ex ∧ f.exported = ex ∧
      (level = .private → ModFiles.isModule { exported := ex } = true →
        ∃ bs bp s p, loc.hasServer = true ∧ loc.hasPrivate = true ∧
          fs.file (modFile loc.dir m "olean.server") = some bs ∧
          fs.file (modFile loc.dir m "olean.private") = some bp ∧
          Part.ofBytes (modFile loc.dir m "olean.server").toString bs = .ok s ∧
          Part.ofBytes (modFile loc.dir m "olean.private").toString bp = .ok p ∧
          f = { exported := ex, server := some s, «private» := some p }) ∧
      (level = .private → ModFiles.isModule { exported := ex } = false →
        loc.hasServer = false ∧ loc.hasPrivate = false ∧ f = { exported := ex }) := by
  simp only [readFiles, ModelIO.bind_ok] at h
  obtain ⟨y, hy, h⟩ := h
  rcases y with e | loc
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨x, hx, h⟩ := h
  obtain ⟨b, hb, rfl⟩ := readPart_ok hx
  cases hp : Part.ofBytes (modFile loc.dir m "olean").toString b with
  | error e => simp [hp] at h
  | ok ex =>
    simp only [hp] at h
    cases level with
    | exported =>
      simp at h
      subst h
      exact ⟨loc, b, ex, findModule_ok hy, hb, hp, rfl, by simp, by simp⟩
    | server =>
      have hne : (OLeanLevel.server == .exported) = false := by decide
      simp only [hne, Bool.false_eq_true, ite_false] at h
      refine ⟨loc, b, ex, findModule_ok hy, hb, hp, ?_, by simp, by simp⟩
      cases hm : ModFiles.isModule { exported := ex } with
      | false =>
        simp only [hm, Bool.not_false, ite_true] at h
        by_cases hs1 : (loc.hasServer || loc.hasPrivate) = true
        · simp [hs1] at h
        · simp [hs1] at h
          subst h
          rfl
      | true =>
        simp only [hm, Bool.not_true, Bool.false_eq_true, ite_false] at h
        by_cases hs : loc.hasServer = true
        · by_cases hq : loc.hasPrivate = true
          · have hsq : (OLeanLevel.server == .server) = true := by decide
            simp only [hs, hq, Bool.not_true, Bool.false_eq_true, ite_false, hsq, ite_true,
              ModelIO.bind_ok] at h
            obtain ⟨xs, -, h⟩ := h
            rcases xs with e | s
            · simp at h
            · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
              subst h
              rfl
          · simp [hs, hq] at h
        · simp [hs] at h
    | «private» =>
      have hne : (OLeanLevel.private == .exported) = false := by decide
      simp only [hne, Bool.false_eq_true, ite_false] at h
      cases hm : ModFiles.isModule { exported := ex } with
      | false =>
        simp only [hm, Bool.not_false, ite_true] at h
        by_cases hs1 : (loc.hasServer || loc.hasPrivate) = true
        · simp [hs1] at h
        · simp [hs1] at h
          subst h
          have hl : loc.hasServer = false ∧ loc.hasPrivate = false := by
            simpa using hs1
          exact ⟨loc, b, ex, findModule_ok hy, hb, hp, rfl,
            fun _ h' => (by rw [hm] at h'; cases h'), fun _ _ => ⟨hl.1, hl.2, rfl⟩⟩
      | true =>
        simp only [hm, Bool.not_true, Bool.false_eq_true, ite_false] at h
        by_cases hs : loc.hasServer = true
        · by_cases hq : loc.hasPrivate = true
          · have hsq : (OLeanLevel.private == .server) = false := by decide
            simp only [hs, hq, Bool.not_true, Bool.false_eq_true, ite_false, hsq,
              ModelIO.bind_ok] at h
            obtain ⟨xs, hxs, h⟩ := h
            obtain ⟨bs, hbs, rfl⟩ := readPart_ok hxs
            cases ho : Part.ofBytes (modFile loc.dir m "olean.server").toString bs with
            | error e => simp [ho] at h
            | ok s' =>
              simp only [ho, ModelIO.bind_ok] at h
              obtain ⟨xp, hxp, h⟩ := h
              obtain ⟨bp, hbp, rfl⟩ := readPart_ok hxp
              cases hr : Part.ofBytes (modFile loc.dir m "olean.private").toString bp with
              | error e => simp [hr] at h
              | ok p' =>
                simp only [hr, ModelIO.pure_iff, Except.ok.injEq] at h
                subst h
                exact ⟨loc, b, ex, findModule_ok hy, hb, hp, rfl,
                  fun _ _ => ⟨bs, bp, s', p', hs, hq, hbs, hbp, ho, hr, rfl⟩,
                  fun _ h' => by rw [hm] at h'; cases h'⟩
          · simp [hs, hq] at h
        · simp [hs] at h

/-- **The files a view reads, from a home's**: determined, those of the home's it
reads. -/
theorem readFiles_of_all {sp : SearchPath} {m : Name} {fs : FS} {f : ModFiles} (level : OLeanLevel)
    (h : (readFiles sp m .private : ModelIO _) fs (.ok (.ok f))) :
    (readFiles sp m level : ModelIO _) fs = ModelIO.answer (some (.ok (f.upTo level))) := by
  obtain ⟨loc, b, ex, hf, hb, hp, rfl, hmod, hcl⟩ := readFiles_ok h
  simp only [readFiles]
  rw [ModelIO.bind_det hf]
  simp only
  rw [ModelIO.bind_det (readPart_det hb), hp]
  simp only
  cases level with
  | exported => rfl
  | server =>
    have hne : (OLeanLevel.server == .exported) = false := by decide
    simp only [hne, Bool.false_eq_true, ite_false]
    cases hm : ModFiles.isModule { exported := f.exported } with
    | false =>
      obtain ⟨h1, h2, h3⟩ := hcl rfl hm
      simp only [Bool.not_false, ite_true, h1, h2, Bool.or_self, Bool.false_eq_true, ite_false]
      rw [h3]
      rfl
    | true =>
      obtain ⟨bs, bp, s, p, h1, h2, hbs, hbp, ho, hr, h3⟩ := hmod rfl hm
      have hsq : (OLeanLevel.server == .server) = true := by decide
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, h1, h2]
      rw [ModelIO.bind_det (readPart_det hbs), ho]
      simp only [hsq, ite_true]
      rw [h3]
      rfl
  | «private» =>
    have hne : (OLeanLevel.private == .exported) = false := by decide
    simp only [hne, Bool.false_eq_true, ite_false]
    cases hm : ModFiles.isModule { exported := f.exported } with
    | false =>
      obtain ⟨h1, h2, h3⟩ := hcl rfl hm
      simp only [Bool.not_false, ite_true, h1, h2, Bool.or_self, Bool.false_eq_true, ite_false]
      rw [h3]
      rfl
    | true =>
      obtain ⟨bs, bp, s, p, h1, h2, hbs, hbp, ho, hr, h3⟩ := hmod rfl hm
      have hsq : (OLeanLevel.private == .server) = false := by decide
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, h1, h2]
      rw [ModelIO.bind_det (readPart_det hbs), ho]
      simp only [hsq, Bool.false_eq_true, ite_false]
      rw [ModelIO.bind_det (readPart_det hbp), hr, h3]
      rfl

/-- A view of a module's files is a view of those it reads. -/
theorem decodeModuleSpec_upTo (f : ModFiles) (level : OLeanLevel) :
    decodeModuleSpec (f.upTo level) level = decodeModuleSpec f level := by
  cases level <;> rfl

/-- **A home's read settles each view**: determined, the home's. -/
theorem readView_of_all {sp : SearchPath} {m : Name} {fs : FS} {v : AllViews} {e : Array Expo}
    (level : OLeanLevel) (h : (readAllViews sp m : ModelIO _) fs (.ok (.ok (v, e)))) :
    (readView sp m level : ModelIO _) fs = ModelIO.answer (some (.ok (v.at level))) := by
  simp only [readAllViews, ModelIO.bind_ok] at h
  obtain ⟨y, hy, h⟩ := h
  rcases y with x | f
  · simp at h
  cases hv : parseAllViews f with
  | none => simp [hv] at h
  | some v' =>
    simp only [hv] at h
    cases hc : checkViews m f v' with
    | error x => simp [hc] at h
    | ok expo =>
      simp only [hc, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hp : parseView (f.upTo level) level = some (v.at level) := by
        rw [parseView_eq_spec, decodeModuleSpec_upTo]
        rw [parseAllViews_eq] at hv
        obtain ⟨d1, h1, hv⟩ := bind_some_left hv
        obtain ⟨d2, h2, hv⟩ := bind_some_left hv
        obtain ⟨d3, h3, hv⟩ := bind_some_left hv
        cases hv
        cases level
        · exact h1
        · exact h2
        · exact h3
      simp only [readView]
      rw [ModelIO.bind_det (readFiles_of_all level hy)]
      simp only [hp]
      rfl

/-- **A view read says what the file's start holds**: the read of the imports is
determined, and is the view's. -/
theorem moduleImports_of_view {sp : SearchPath} {m : Name} {level : OLeanLevel} {fs : FS}
    {d : ModDecoded} (h : (readView sp m level : ModelIO _) fs (.ok (.ok d))) :
    (moduleImports sp m : ModelIO _) fs = ModelIO.answer (some (.ok d.imports)) := by
  simp only [readView, ModelIO.bind_ok] at h
  obtain ⟨y, hy, h⟩ := h
  rcases y with x | f
  · simp at h
  cases hv : parseView f level with
  | none => simp [hv] at h
  | some d' =>
    simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
    cases h
    obtain ⟨loc, b, ex, hf, hb, hp, rfl, -, -⟩ := readFiles_ok hy
    obtain ⟨-, -, -, -, himp⟩ := parseView_some hv
    rw [Part.ofBytes_bytes hp] at himp
    simp only [moduleImports]
    rw [ModelIO.bind_det hf]
    exact readImportsAt_det hb hp himp

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

/-- **A module of the order has its view's imports before it**: the imports the walk read
off the file's start are its private view's. -/
theorem ClosedOrder.view_imports {sp : SearchPath} {fs : FS} {order : Array Name}
    (hc : ClosedOrder sp fs order) {k : Nat} (hk : k < order.size) {d : ModDecoded}
    (hv : (readView sp order[k] .private : ModelIO _) fs (.ok (.ok d))) :
    ∀ i ∈ d.imports, i.module ∈ order.toList.take k := by
  obtain ⟨imps, h1, h2⟩ := hc k hk
  rw [moduleImports_of_view hv] at h1
  have : d.imports = imps := by simpa using (ModelIO.answer_ok _ _).1 h1
  rw [this]
  exact h2

/-- **The records of a run** are made of the import closure's modules, each
private view read by `readView` on the snapshot, whatever the job count. -/
theorem readOleans_ok {sp : SearchPath} {roots : Array Name} {constants : Option (Array Name)}
    {jobs : Nat} {fs : FS} {ds : Array Declaration}
    (h : (readOleans sp roots constants jobs : ModelIO _) fs (.ok (.ok ds))) :
    ∃ (order : Array Name) (ls : List Loaded) (mg : Merged) (rs : Array Name),
      (closureOrder sp roots : ModelIO _) fs (.ok (.ok order)) ∧
      ls.map (·.name) = order.toList ∧
      (∀ l ∈ ls, ∃ d, (readView sp l.name .private : ModelIO _) fs (.ok (.ok d)) ∧
        l.constants = d.constants.map CEntry.ofRead) ∧
      ClosedOrder sp fs order ∧ (∀ r ∈ roots, r ∈ order) ∧
      (∀ l ∈ ls, ∀ c ∈ l.constants, ∃ c', mg.map[c.name]? = some c' ∧ Stands c' c) ∧
      mergeAll ls.toArray = .ok mg ∧ rootConstants mg constants = .ok rs ∧
      coverageOk mg (emitAll mg rs) = .ok () ∧ declsOf (emitAll mg rs) = .ok ds := by
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
        cases hr : rootConstants mg constants with
        | error e => simp [hr] at h
        | ok rs =>
        simp only [hr] at h
        cases hc : coverageOk mg (emitAll mg rs) with
        | error e => simp [hc] at h
        | ok u =>
          simp only [hc, ModelIO.pure_iff, Except.ok.injEq] at h
          have hF : (mapExcept (loadModule sp) order.toList : ModelIO _) fs (.ok (.ok ls)) := hy
          obtain ⟨h1, h2⟩ := mapExcept_ok (g := Loaded.name) (Q := fun l => ∃ d,
              (readView sp l.name .private : ModelIO _) fs (.ok (.ok d)) ∧
                l.constants = d.constants.map CEntry.ofRead) (fun m l hl => by
            simp only [loadModule, ModelIO.bind_ok] at hl
            obtain ⟨z, hz, hl⟩ := hl
            rcases z with e | r
            · simp at hl
            · simp only [ModelIO.pure_iff, Except.ok.injEq] at hl
              subst hl
              exact ⟨rfl, r, hz, rfl⟩) hF
          obtain ⟨hk, -⟩ := mergeAll_ok hm
          obtain ⟨hc1, hc2⟩ := closureOrder_ok ho
          exact ⟨order, ls, mg, rs, ho, h1, h2, hc1, hc2, fun l hl => hk l (by simpa using hl), hm, hr,
            by cases u; exact hc, h.symm⟩

/-- **The private view of a module on a snapshot**, by the specification: the module's files
on the search path, and what `decodeModuleSpec` says they hold at that level. -/
@[expose] def ViewOf (sp : SearchPath) (fs : FS) (m : Name) (d : ModDecoded) : Prop :=
  ∃ f, (readFiles sp m .private : ModelIO _) fs (.ok (.ok f)) ∧ decodeModuleSpec f .private = some d

/-- **The read of a module's private view is the view.** -/
theorem readView_of_viewOf {sp : SearchPath} {fs : FS} {m : Name} {d : ModDecoded}
    (h : ViewOf sp fs m d) : (readView sp m .private : ModelIO _) fs (.ok (.ok d)) := by
  obtain ⟨f, h1, h2⟩ := h
  simp only [readView, ModelIO.bind_ok]
  refine ⟨.ok f, h1, ?_⟩
  simp only [parseView_eq_spec, h2]
  exact rfl

/-- **The modules of the closure of some roots**, on a snapshot: a root, or an import of the
private view of one. -/
inductive InClosure (sp : SearchPath) (fs : FS) (roots : Array Name) : Name → Prop
  | root {r : Name} : r ∈ roots → InClosure sp fs roots r
  | step {m : Name} {d : ModDecoded} {i : ImportRec} : InClosure sp fs roots m →
      ViewOf sp fs m d → i ∈ d.imports → InClosure sp fs roots i.module

/-- The order holds the closure. -/
theorem InClosure.mem_order {sp : SearchPath} {fs : FS} {roots order : Array Name} {m : Name}
    (hc : ClosedOrder sp fs order) (hr : ∀ r ∈ roots, r ∈ order) (h : InClosure sp fs roots m) :
    m ∈ order := by
  induction h with
  | root hm => exact hr _ hm
  | @step m d i _ hv hi ih =>
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem ih
    have := hc.view_imports hk (readView_of_viewOf hv) i hi
    exact Array.mem_toList_iff.mp (List.mem_of_mem_take this)

/-- A private view read off a snapshot is the snapshot's. -/
theorem readView_unique {sp : SearchPath} {m : Name} {fs : FS} {a b : ModDecoded}
    (ha : (readView sp m .private : ModelIO _) fs (.ok (.ok a)))
    (hb : (readView sp m .private : ModelIO _) fs (.ok (.ok b))) : a = b := by
  simp only [readView, ModelIO.bind_ok] at ha hb
  obtain ⟨y, hy, ha⟩ := ha
  obtain ⟨y', hy', hb⟩ := hb
  rcases y with x | f
  · simp at ha
  rcases y' with x | f'
  · simp at hb
  have hdet := readFiles_of_all .private hy
  rw [hdet] at hy'
  have hff : f = f' := by
    have := (ModelIO.answer_ok _ _).1 hy'
    simpa [ModFiles.upTo] using this
  subst hff
  cases hv : parseView f .private with
  | none => simp [hv] at ha
  | some x =>
    simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at ha hb
    exact ha.trans hb.symm

/-- **A theorem of a module of the closure is among the records**, with its statement, whichever
of the proofs Lean's rule keeps. -/
theorem readOleans_thm {sp : SearchPath} {roots : Array Name} {jobs : Nat} {fs : FS}
    {ds : Array Declaration} {m : Name} {d : ModDecoded} {c : CEntryF Name Expr} {v : Expr}
    {all : List Name}
    (h : (readOleans sp roots none jobs : ModelIO _) fs (.ok (.ok ds)))
    (hcl : InClosure sp fs roots m) (hv : ViewOf sp fs m d)
    (hc : c ∈ d.constants) (hk : c.kind = .thm v all) :
    ∃ v', Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ v' ∈ ds := by
  obtain ⟨order, ls, mg, rs, ho, h1, h2, hco, hcr, hstand, hm, hr, hcov, hds⟩ := readOleans_ok h
  have hrs : rs = mg.order := by
    simp only [rootConstants] at hr
    cases hr
    rfl
  subst hrs
  have hmo := hcl.mem_order hco hcr
  have : m ∈ ls.map (·.name) := by
    rw [h1]
    simpa using hmo
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp this
  obtain ⟨d', hv', hconst⟩ := h2 l hl
  obtain rfl := readView_unique (readView_of_viewOf hv) hv'
  have hcl' : CEntry.ofRead c ∈ l.constants := by
    rw [hconst]
    exact Array.mem_map.mpr ⟨c, hc, rfl⟩
  obtain ⟨c', hc', hs⟩ := hstand l hl _ hcl'
  obtain ⟨hk1, hk2, hk3, hk4⟩ := mergeAll_ok hm
  have hN : ∀ (n : Name) (x : CEntry), mg.map[n]? = some x → x.name = n := fun n x hx => (hk2 n x hx).1
  have hord : (CEntry.ofRead c).name ∈ mg.order := (hk3 _).2 (contains_of_getElem hc')
  have hkind : (CEntry.ofRead c).kind = .thm v all := hk
  have hst : ∃ v' all', c'.kind = .thm v' all' ∧ c'.name = c.name ∧ c'.levelParams = c.levelParams ∧
      c'.type = c.type := by
    rcases hs with rfl | ⟨n1, t1, l1, k1⟩
    · exact ⟨v, all, hkind, rfl, rfl, rfl⟩
    · rw [hkind] at k1
      cases hk' : c'.kind with
      | thm v' all' => exact ⟨v', all', rfl, n1, l1, t1⟩
      | ax _ => rw [hk'] at k1; exact k1.elim
      | defn _ _ _ => rw [hk'] at k1; exact k1.elim
      | opaq _ _ => rw [hk'] at k1; exact k1.elim
      | quot _ => rw [hk'] at k1; exact k1.elim
      | induct _ _ _ _ _ _ _ _ => rw [hk'] at k1; exact k1.elim
      | ctor _ _ _ _ _ => rw [hk'] at k1; exact k1.elim
      | recur _ _ _ _ _ _ _ _ => rw [hk'] at k1; exact k1.elim
  obtain ⟨v', all', hk5, hn, hlp, hty⟩ := hst
  have := declsOf_thm hN hds hcov hord hord hc' hk5
  rw [hn, hlp, hty] at this
  exact ⟨v', this⟩

end ConLeche.Frontend.Olean
