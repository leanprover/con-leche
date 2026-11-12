module

public import ConLeche.Frontend.Olean.Records
public import ConLeche.Verify.Frontend.Olean.Closure
public import ConLeche.Verify.Frontend.Olean.Merge
public import ConLeche.Verify.Frontend.Olean.Sparse
public import ConLeche.Verify.Frontend.ModelIO
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Emit
import ConLeche.Verify.Frontend.Olean.View
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Reads

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

`readOleans_filled`: a theorem's record, with what its reference stands for on the snapshot
(`ValueAt`) in place, is the constant the specification reads off that module's files.
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
    (CheckerIO.pathExists p : ModelIO Bool).Det fs := ⟨some (fs.real p).isSome, fun hs => ⟨hs, rfl⟩⟩

theorem realPath_det (p : System.FilePath) (fs : FS) :
    (CheckerIO.realPath p : ModelIO System.FilePath).Det fs := ⟨fs.real p, fun hs => ⟨hs, rfl⟩⟩

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
theorem findModule_ok {sp : SearchPath} {m : Name} {fs : FS} {hs : HS} {loc : Located} {hs' : HS}
    (h : (findModule sp m : ModelIO _) fs hs (.ok (.ok loc)) hs') :
    ModelIO.Gives (findModule sp m) fs (.ok loc) := by
  have key : ∀ hits, ModelIO.Gives (locateHits sp m) fs hits →
      ModelIO.Gives (findModule sp m) fs (locateOf m hits) := by
    intro hits hh
    simp only [findModule]
    exact hh.map.tryCatch.bind (ModelIO.gives_pure _ _)
  simp only [findModule, ModelIO.bind_ok, ModelIO.tryCatch_ok] at h
  obtain ⟨x, _, hx, hr⟩ := h
  rcases hx with hx | ⟨e, _, -, hx⟩
  · simp only [ModelIO.map_ok] at hx
    obtain ⟨hits, hh, rfl⟩ := hx
    have hk := key hits ((locateHits_det sp m fs).of_ok hh)
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hr
    rw [← hr.1] at hk
    exact hk
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    simp at hr

/-! ## A file -/

theorem readBinFile_ok {p : System.FilePath} {fs : FS} {hs : HS} {b : ByteArray} {hs' : HS} :
    (CheckerIO.readBinFile p : ModelIO ByteArray) fs hs (.ok b) hs' ↔
      fs.file p = some b ∧ hs' = hs :=
  ModelIO.ret_ok _ _ _ _

theorem readBinFile_det {p : System.FilePath} {fs : FS} {b : ByteArray}
    (h : fs.file p = some b) :
    ModelIO.Gives (CheckerIO.readBinFile p : ModelIO ByteArray) fs b := fun hs =>
  ⟨hs, by show ModelIO.ret (fs.file p) hs = _; rw [h]⟩

/-- **A part read off the snapshot** is the validation of its bytes. -/
theorem readPart_ok {p : System.FilePath} {fs : FS} {hs : HS} {x : Except CheckError Part}
    {hs' : HS} (h : (readPart p : ModelIO _) fs hs (.ok x) hs') :
    ∃ b, fs.file p = some b ∧ x = Part.ofBytes p.toString b := by
  simp only [readPart, ModelIO.bind_ok, readBinFile_ok, ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨b, _, ⟨hb, -⟩, hx, -⟩ := h
  exact ⟨b, hb, hx⟩

theorem readPart_det {p : System.FilePath} {fs : FS} {b : ByteArray} (h : fs.file p = some b) :
    ModelIO.Gives (readPart p) fs (Part.ofBytes p.toString b) := by
  simp only [readPart]
  exact (readBinFile_det h).bind (ModelIO.gives_pure _ _)

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
theorem readImportsAt_ok {loc : Located} {m : Name} {fs : FS} {hs : HS} {imps : Array ImportRec}
    {hs' : HS} (h : (readImportsAt loc m : ModelIO _) fs hs (.ok (.ok imps)) hs') :
    ∃ b, fs.file (modFile loc.dir m "olean") = some b ∧ importsPre b = some imps := by
  simp only [readImportsAt, ModelIO.bind_ok] at h
  obtain ⟨x, _, hx, hr⟩ := h
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
      obtain ⟨hr, -⟩ := hr
      cases hr
      exact foldList_hdr _ _ b imps 0 ByteArray.empty (by simp) (by simp) hf

/-- **The header read of a valid file with imports** is determined. -/
theorem readImportsAt_det {loc : Located} {m : Name} {fs : FS} {b : ByteArray} {ex : Part}
    {imps : Array ImportRec} (hb : fs.file (modFile loc.dir m "olean") = some b)
    (hp : Part.ofBytes (modFile loc.dir m "olean").toString b = .ok ex)
    (hi : importsPre b = some imps) :
    ModelIO.Gives (readImportsAt loc m) fs (.ok imps) := by
  simp only [readImportsAt]
  refine (foldChunks_det _ _ _ _ hb).bind ?_
  simp only [hdrChunk_toNat]
  rw [foldList_hdr_complete hp hi (by decide) (by decide) 0 _ (by simp) (by simp) (by simp)]
  exact ModelIO.gives_pure _ _

/-! ## The home's full read -/

/-- **The files of a view**, unfolded: the location is determined, `M.olean` read, and
the rest as its flag and the level ask. -/
theorem readFiles_ok {sp : SearchPath} {m : Name} {level : OLeanLevel} {fs : FS} {hs : HS}
    {f : ModFiles} {hs' : HS} (h : (readFiles sp m level : ModelIO _) fs hs (.ok (.ok f)) hs') :
    ∃ loc b ex, ModelIO.Gives (findModule sp m) fs (.ok loc) ∧
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
  obtain ⟨y, _, hy, h⟩ := h
  rcases y with e | loc
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨x, _, hx, h⟩ := h
  obtain ⟨b, hb, rfl⟩ := readPart_ok hx
  cases hp : Part.ofBytes (modFile loc.dir m "olean").toString b with
  | error e => simp [hp] at h
  | ok ex =>
    simp only [hp] at h
    cases level with
    | exported =>
      simp at h
      obtain ⟨rfl, -⟩ := h
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
          obtain ⟨rfl, -⟩ := h
          rfl
      | true =>
        simp only [hm, Bool.not_true, Bool.false_eq_true, ite_false] at h
        by_cases hs : loc.hasServer = true
        · by_cases hq : loc.hasPrivate = true
          · have hsq : (OLeanLevel.server == .server) = true := by decide
            simp only [hs, hq, Bool.not_true, Bool.false_eq_true, ite_false, hsq, ite_true,
              ModelIO.bind_ok] at h
            obtain ⟨xs, _, -, h⟩ := h
            rcases xs with e | s
            · simp at h
            · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
              obtain ⟨rfl, -⟩ := h
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
          obtain ⟨rfl, -⟩ := h
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
            obtain ⟨xs, _, hxs, h⟩ := h
            obtain ⟨bs, hbs, rfl⟩ := readPart_ok hxs
            cases ho : Part.ofBytes (modFile loc.dir m "olean.server").toString bs with
            | error e => simp [ho] at h
            | ok s' =>
              simp only [ho, ModelIO.bind_ok] at h
              obtain ⟨xp, _, hxp, h⟩ := h
              obtain ⟨bp, hbp, rfl⟩ := readPart_ok hxp
              cases hr : Part.ofBytes (modFile loc.dir m "olean.private").toString bp with
              | error e => simp [hr] at h
              | ok p' =>
                simp only [hr, ModelIO.pure_iff, Except.ok.injEq] at h
                obtain ⟨rfl, -⟩ := h
                exact ⟨loc, b, ex, findModule_ok hy, hb, hp, rfl,
                  fun _ _ => ⟨bs, bp, s', p', hs, hq, hbs, hbp, ho, hr, rfl⟩,
                  fun _ h' => by rw [hm] at h'; cases h'⟩
          · simp [hs, hq] at h
        · simp [hs] at h

/-- **The files a view reads, from a home's**: determined, those of the home's it
reads. -/
theorem readFiles_of_all {sp : SearchPath} {m : Name} {fs : FS} {hs : HS} {f : ModFiles} {hs' : HS}
    (level : OLeanLevel) (h : (readFiles sp m .private : ModelIO _) fs hs (.ok (.ok f)) hs') :
    ModelIO.Gives (readFiles sp m level) fs (.ok (f.upTo level)) := by
  obtain ⟨loc, b, ex, hf, hb, hp, rfl, hmod, hcl⟩ := readFiles_ok h
  simp only [readFiles]
  refine hf.bind ?_
  simp only
  refine (readPart_det hb).bind ?_
  simp only [hp]
  cases level with
  | exported => exact ModelIO.gives_pure _ _
  | server =>
    have hne : (OLeanLevel.server == .exported) = false := by decide
    simp only [hne, Bool.false_eq_true, ite_false]
    cases hm : ModFiles.isModule { exported := f.exported } with
    | false =>
      obtain ⟨h1, h2, h3⟩ := hcl rfl hm
      simp only [Bool.not_false, ite_true, h1, h2, Bool.or_self, Bool.false_eq_true, ite_false]
      rw [h3]
      exact ModelIO.gives_pure _ _
    | true =>
      obtain ⟨bs, bp, s, p, h1, h2, hbs, hbp, ho, hr, h3⟩ := hmod rfl hm
      have hsq : (OLeanLevel.server == .server) = true := by decide
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, h1, h2]
      refine (readPart_det hbs).bind ?_
      simp only [ho, hsq, ite_true]
      rw [h3]
      exact ModelIO.gives_pure _ _
  | «private» =>
    have hne : (OLeanLevel.private == .exported) = false := by decide
    simp only [hne, Bool.false_eq_true, ite_false]
    cases hm : ModFiles.isModule { exported := f.exported } with
    | false =>
      obtain ⟨h1, h2, h3⟩ := hcl rfl hm
      simp only [Bool.not_false, ite_true, h1, h2, Bool.or_self, Bool.false_eq_true, ite_false]
      rw [h3]
      exact ModelIO.gives_pure _ _
    | true =>
      obtain ⟨bs, bp, s, p, h1, h2, hbs, hbp, ho, hr, h3⟩ := hmod rfl hm
      have hsq : (OLeanLevel.private == .server) = false := by decide
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, h1, h2]
      refine (readPart_det hbs).bind ?_
      simp only [ho, hsq, Bool.false_eq_true, ite_false]
      refine (readPart_det hbp).bind ?_
      simp only [hr]
      rw [h3]
      exact ModelIO.gives_pure _ _

/-- A view of a module's files is a view of those it reads. -/
theorem decodeModuleSpec_upTo (f : ModFiles) (level : OLeanLevel) :
    decodeModuleSpec (f.upTo level) level = decodeModuleSpec f level := by
  cases level <;> rfl

/-- **A home's read settles each view**: determined, the home's. -/
theorem readView_of_all {sp : SearchPath} {m : Name} {fs : FS} {hs : HS} {v : AllViews}
    {e : Array Expo} {hs' : HS}
    (level : OLeanLevel) (h : (readAllViews sp m : ModelIO _) fs hs (.ok (.ok (v, e))) hs') :
    ModelIO.Gives (readView sp m level) fs (.ok (v.at level)) := by
  simp only [readAllViews, ModelIO.bind_ok] at h
  obtain ⟨y, _, hy, h⟩ := h
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
      obtain ⟨⟨rfl, -⟩, -⟩ := h
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
      refine (readFiles_of_all level hy).bind ?_
      simp only [hp]
      exact ModelIO.gives_pure _ _

/-- **A view read says what the file's start holds**: the read of the imports is
determined, and is the view's. -/
theorem moduleImports_of_view {sp : SearchPath} {m : Name} {level : OLeanLevel} {fs : FS}
    {hs : HS} {d : ModDecoded} {hs' : HS}
    (h : (readView sp m level : ModelIO _) fs hs (.ok (.ok d)) hs') :
    ModelIO.Gives (moduleImports sp m) fs (.ok d.imports) := by
  simp only [readView, ModelIO.bind_ok] at h
  obtain ⟨y, _, hy, h⟩ := h
  rcases y with x | f
  · simp at h
  cases hv : parseView f level with
  | none => simp [hv] at h
  | some d' =>
    simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    cases h
    obtain ⟨loc, b, ex, hf, hb, hp, rfl, -, -⟩ := readFiles_ok hy
    obtain ⟨-, -, -, -, himp⟩ := parseView_some hv
    rw [Part.ofBytes_bytes hp] at himp
    simp only [moduleImports]
    exact hf.bind (readImportsAt_det hb hp himp)

/-! ## The whole read -/

/-- The sequential map's value: one value of each element's action, here
each saying which element it is of. -/
theorem mapExcept_ok {α β ε : Type} {f : α → ModelIO (Except ε β)} {fs : FS} {g : β → α}
    {Q : β → Prop} (hk : ∀ x y hs hs', f x fs hs (.ok (.ok y)) hs' → g y = x ∧ Q y) :
    ∀ {xs : List α} {ys : List β} {hs hs' : HS},
      (mapExcept f xs : ModelIO _) fs hs (.ok (.ok ys)) hs' →
      ys.map g = xs ∧ ∀ y ∈ ys, Q y
  | [], ys, _, _, h => by
    simp only [mapExcept, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    cases h
    simp
  | x :: xs, ys, _, _, h => by
    simp only [mapExcept, ModelIO.bind_ok] at h
    obtain ⟨a, _, ha, h⟩ := h
    rcases a with e | b
    · simp at h
    · simp only [ModelIO.bind_ok] at h
      obtain ⟨c, _, hc, h⟩ := h
      rcases c with e | bs
      · simp at h
      · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
        obtain ⟨h, -⟩ := h
        cases h
        obtain ⟨h1, h2⟩ := hk _ _ _ _ ha
        obtain ⟨h3, h4⟩ := mapExcept_ok hk hc
        simp only [List.map_cons, h1, h3, List.mem_cons, forall_eq_or_imp, true_and]
        exact ⟨h2, h4⟩

/-- **A module of the order has its view's imports before it**: the imports the walk read
off the file's start are its private view's. -/
theorem ClosedOrder.view_imports {sp : SearchPath} {fs : FS} {order : Array Name}
    (hc : ClosedOrder sp fs order) {k : Nat} (hk : k < order.size) {d : ModDecoded}
    (hv : ModelIO.CanGive (readView sp order[k] .private) fs (.ok d)) :
    ∀ i ∈ d.imports, i.module ∈ order.toList.take k := by
  obtain ⟨imps, h1, h2⟩ := hc k hk
  obtain ⟨_, _, hv⟩ := hv
  have : d.imports = imps := by simpa using ((moduleImports_of_view hv).eq h1).symm
  rw [this]
  exact h2

/-- The sequential map's value, in terms of each element's: for each result, an element it
comes from, and the results' `g` are the elements' `g'`. -/
theorem mapExcept_ok₂ {α β ε γ : Type} {f : α → ModelIO (Except ε β)} {fs : FS} {g : β → γ}
    {g' : α → γ} {Q : α → β → Prop} (hk : ∀ x y hs hs', f x fs hs (.ok (.ok y)) hs' → g y = g' x ∧ Q x y) :
    ∀ {xs : List α} {ys : List β} {hs hs' : HS},
      (mapExcept f xs : ModelIO _) fs hs (.ok (.ok ys)) hs' →
      ys.map g = xs.map g' ∧ ∀ y ∈ ys, ∃ x ∈ xs, Q x y
  | [], ys, _, _, h => by
    simp only [mapExcept, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    cases h
    simp
  | x :: xs, ys, _, _, h => by
    simp only [mapExcept, ModelIO.bind_ok] at h
    obtain ⟨a, _, ha, h⟩ := h
    rcases a with e | b
    · simp at h
    · simp only [ModelIO.bind_ok] at h
      obtain ⟨c, _, hc, h⟩ := h
      rcases c with e | bs
      · simp at h
      · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
        obtain ⟨h, -⟩ := h
        cases h
        obtain ⟨h1, h2⟩ := hk _ _ _ _ ha
        obtain ⟨h3, h4⟩ := mapExcept_ok₂ hk hc
        refine ⟨by simp [h1, h3], fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, by simp, h2⟩
        · obtain ⟨x', hx', hq⟩ := h4 y hy
          exact ⟨x', by simp [hx'], hq⟩

/-- **The records of a run** are made of the import closure's modules, each private view
loaded (`loadAt`) from the files on the snapshot, whatever the job count: what a theorem's
check reads comes from those files too. -/
theorem readOleans_ok {sp : SearchPath} {roots : Array Name} {constants : Option (Array Name)}
    {pace : Pace} {jobs : Nat} {fs : FS} {hs : HS} {rd : OleanRead} {hs' : HS}
    (h : (readOleans sp roots constants jobs pace : ModelIO _) fs hs (.ok (.ok rd)) hs') :
    ∃ (order : Array Name) (ls : List Loaded) (mg : Merged) (rs : Array Name),
      ModelIO.CanGive (closureOrder sp roots) fs (.ok order) ∧
      ls.map (·.name) = order.toList ∧
      (∀ l ∈ ls, ∃ i f, (l.name, i) ∈ order.toList.zipIdx ∧
        ModelIO.CanGive (readFiles sp l.name .private) fs (.ok f) ∧ loadAt i l.name f = some l) ∧
      ClosedOrder sp fs order ∧ (∀ r ∈ roots, r ∈ order) ∧
      (∀ l ∈ ls, ∀ c ∈ l.constants, ∃ c', mg.map[c.name]? = some c' ∧ Stands c' c) ∧
      mergeAll ls.toArray = .ok mg ∧ blocksOk mg = .ok () ∧ rootConstants mg constants = .ok rs ∧
      declsOf (emitAll mg rs) = .ok rd.decls ∧
      rd.values = ls.toArray.map (fun l => ⟨l.name, l.frontier⟩) ∧ rd.merged = mg := by
  simp only [readOleans, loadClosure, ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at h
  obtain ⟨n, x, _, ⟨_, o, _, ho, hx⟩, h⟩ := h
  rcases o with e | order
  · simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
    obtain ⟨hx, -⟩ := hx
    subst hx
    simp at h
  · simp only [ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at hx
    obtain ⟨_, y, _, hy, hx⟩ := hx
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
    obtain ⟨hx, -⟩ := hx
    subst hx
    rcases y with e | ls
    · simp [Except.map] at h
    · simp only [Except.map, ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at h
      obtain ⟨_, h⟩ := h
      cases hm : mergeAll ls.toArray with
      | error e => simp [hm] at h
      | ok mg =>
        simp only [hm, ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at h
        obtain ⟨_, h⟩ := h
        cases hc : blocksOk mg with
        | error e => simp [hc] at h
        | ok u =>
        simp only [hc] at h
        cases hr : rootConstants mg constants with
        | error e => simp [hr] at h
        | ok rs =>
          simp only [hr, ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at h
          obtain ⟨_, h⟩ := h
          cases hd : declsOf (emitAll mg rs) with
          | error e => simp [hd] at h
          | ok ds =>
          simp only [hd, ModelIO.pure_iff, Except.ok.injEq] at h
          obtain ⟨h, -⟩ := h
          have hF : (mapExcept (loadModule sp n order.size) order.toList.zipIdx : ModelIO _) fs _
              (.ok (.ok ls)) _ := hy
          obtain ⟨h1, h2⟩ := mapExcept_ok₂ (g := Loaded.name) (g' := Prod.fst)
            (Q := fun x l => x.1 = l.name ∧ ∃ f, ModelIO.CanGive (readFiles sp x.1 .private) fs (.ok f) ∧
                loadAt x.2 x.1 f = some l) (fun x l _ _ hl => by
            simp only [loadModule, ModelIO.bind_ok] at hl
            obtain ⟨z, _, hz, hl⟩ := hl
            rcases z with e | f
            · simp at hl
            · simp only [ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at hl
              obtain ⟨_, hl⟩ := hl
              simp only [loadView, ModelIO.pure_iff, Except.ok.injEq] at hl
              obtain ⟨hl, -⟩ := hl
              split at hl
              · rename_i l' hl'
                cases hl
                have hn := (loadAt_spec hl').choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.1
                exact ⟨hn, hn.symm, f, ⟨_, _, hz⟩, hl'⟩
              · cases hl) hF
          obtain ⟨hk, -⟩ := mergeAll_ok hm
          obtain ⟨hc1, hc2⟩ := closureOrder_ok ho
          refine ⟨order, ls, mg, rs, ⟨_, _, ho⟩, by simpa using h1, fun l hl => ?_, hc1, hc2,
            fun l hl => hk l (by simpa using hl), hm, by cases u; exact hc, hr, ?_, ?_, ?_⟩
          · obtain ⟨⟨m, i⟩, hx, hn, f, hf, ha⟩ := h2 l hl
            simp only at hn hf ha
            subst hn
            exact ⟨i, f, hx, hf, ha⟩
          · subst h; exact hd
          · subst h; rfl
          · subst h; rfl

/-- **The private view of a module on a snapshot**, by the specification: the module's files
on the search path, and what `decodeModuleSpec` says they hold at that level. -/
@[expose] def ViewOf (sp : SearchPath) (fs : FS) (m : Name) (d : ModDecoded) : Prop :=
  ∃ f, ModelIO.CanGive (readFiles sp m .private) fs (.ok f) ∧ decodeModuleSpec f .private = some d

/-- **The read of a module's private view is the view.** -/
theorem readView_of_viewOf {sp : SearchPath} {fs : FS} {m : Name} {d : ModDecoded}
    (h : ViewOf sp fs m d) : ModelIO.CanGive (readView sp m .private) fs (.ok d) := by
  obtain ⟨f, ⟨hs, hs', h1⟩, h2⟩ := h
  refine ⟨hs, hs', ?_⟩
  simp only [readView, ModelIO.bind_ok]
  refine ⟨.ok f, hs', h1, ?_⟩
  simp only [parseView_eq_spec, h2]
  exact ⟨rfl, rfl⟩

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
    (ha : ModelIO.CanGive (readView sp m .private) fs (.ok a))
    (hb : ModelIO.CanGive (readView sp m .private) fs (.ok b)) : a = b := by
  obtain ⟨_, _, ha⟩ := ha
  obtain ⟨_, _, hb⟩ := hb
  simp only [readView, ModelIO.bind_ok] at ha hb
  obtain ⟨y, _, hy, ha⟩ := ha
  obtain ⟨y', _, hy', hb⟩ := hb
  rcases y with x | f
  · simp at ha
  rcases y' with x | f'
  · simp at hb
  have hff : f = f' := by
    have := (readFiles_of_all .private hy).ok hy'
    simpa [ModFiles.upTo, eq_comm] using this
  subst hff
  cases hv : parseView f .private with
  | none => simp [hv] at ha
  | some x =>
    simp only [hv, ModelIO.pure_iff, Except.ok.injEq] at ha hb
    exact ha.1.trans hb.1.symm

/-- A module's files are the snapshot's. -/
theorem readFiles_unique {sp : SearchPath} {m : Name} {fs : FS} {a b : ModFiles}
    (ha : ModelIO.CanGive (readFiles sp m .private) fs (.ok a))
    (hb : ModelIO.CanGive (readFiles sp m .private) fs (.ok b)) : a = b := by
  obtain ⟨_, _, ha⟩ := ha
  have := (readFiles_of_all .private ha).eq hb
  simpa [ModFiles.upTo, eq_comm] using this

/-- The parts of a load, at the view it read, of a module whose view reads in full. -/
theorem view_parts {f : ModFiles} {r : Region} {a : UInt64} {d : ModDecoded}
    (hr : f.viewRegion .private = some (r, a)) (hd : decodeModuleSpec f .private = some d) :
    ∃ sk, moduleSkel r a = some sk ∧ sk.consts.mapM (constSpec r) = some d.constants.toList := by
  rw [← parseView_eq_spec] at hd
  simp only [parseView, hr] at hd
  obtain ⟨x, hx, hd⟩ := bind_some_left hd
  cases hx
  obtain ⟨d', hp, hd⟩ := bind_some_left hd
  split at hd
  · cases hd
    obtain ⟨-, sk, h1, -, h2, -⟩ := parseAt_some hp
    exact ⟨sk, h1, h2⟩
  · cases hd

/-- **A theorem of a module of the closure is among the records**, with its statement, whichever
of the proofs Lean's rule keeps. -/
theorem readOleans_thm {sp : SearchPath} {roots : Array Name} {jobs : Nat} {fs : FS}
    {rd : OleanRead} {m : Name} {d : ModDecoded} {c : CEntryF Name Expr} {v : Expr}
    {all : List Name}
    {hs hs' : HS} (h : (readOleans sp roots none jobs : ModelIO _) fs hs (.ok (.ok rd)) hs')
    (hcl : InClosure sp fs roots m) (hv : ViewOf sp fs m d)
    (hc : c ∈ d.constants) (hk : c.kind = .thm v all) :
    ∃ v', Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ v' ∈ rd.decls := by
  obtain ⟨order, ls, mg, rs, ho, h1, h2, hco, hcr, hstand, hm, hb, hr, hds, -, -⟩ := readOleans_ok h
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
  obtain ⟨i, f, -, hf, hload⟩ := h2 l hl
  obtain ⟨f', hf', hview⟩ := hv
  obtain rfl := readFiles_unique hf hf'
  obtain ⟨r, a, sk, skels, hreg, -, hsk, hskels, -, -, hlazy⟩ := loadAt_spec hload
  obtain ⟨sk', hsk', hspec⟩ := view_parts hreg hview
  rw [hsk] at hsk'
  cases hsk'
  obtain ⟨loc, hloc, hcs⟩ := mapM_mem_inv hspec (by simpa using hc)
  obtain ⟨s, hs1, hs2⟩ := constSpec_parts hcs
  obtain ⟨s', hs'mem, hs'⟩ := mapM_mem hskels hloc
  rw [hs1] at hs'
  cases hs'
  obtain ⟨e, he, hent⟩ := hlazy.of_skel _ hs'mem
  obtain ⟨hn, hlp, hty, hth⟩ := lazyEntry_of_spec hs2 hent
  obtain ⟨_, g, _, _, hkind, _, _⟩ := hth v all hk
  obtain ⟨c', hc', hs⟩ := hstand l hl e (by simpa using he)
  obtain ⟨hk1, hk2, hk3, hk4⟩ := mergeAll_ok hm
  have hN : ∀ (n : Name) (x : CEntry), mg.map[n]? = some x → x.name = n := fun n x hx => (hk2 n x hx).1
  have hst : ∃ v' all', c'.kind = .thm v' all' ∧ c'.name = e.name ∧ c'.levelParams = e.levelParams ∧
      c'.type = e.type := by
    rcases hs with rfl | ⟨n1, t1, l1, k1⟩
    · exact ⟨_, all, hkind, rfl, rfl, rfl⟩
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
  obtain ⟨v', all', hk5, hn', hlp', hty'⟩ := hst
  have := declsOf_thm hN hk3 hds hb ((hk3 _).2 (contains_of_getElem hc')) hc' hk5
  rw [hn', hlp', hty', show e.name = c.name from hn, show e.levelParams = c.levelParams from hlp,
    show e.type = c.type from hty] at this
  exact ⟨v', this⟩

/-! ## A theorem's value on a snapshot -/

/-- **What a reference's code stands for on a snapshot**: the value the specification reads at
its location, in the files of its module. -/
@[expose] def ValueAt (sp : SearchPath) (fs : FS) (values : Array ModRef) (code : Nat) (e : Expr) :
    Prop :=
  ∃ md f r a, values[refModule code]? = some md ∧
    ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
    f.viewRegion .private = some (r, a) ∧ exprAt r (refLoc code) = some e

/-- A snapshot has one value at a reference. -/
theorem ValueAt.unique {sp : SearchPath} {fs : FS} {values : Array ModRef} {code : Nat} {a b : Expr}
    (ha : ValueAt sp fs values code a) (hb : ValueAt sp fs values code b) : a = b := by
  obtain ⟨md, f, r, x, h1, h2, h3, h4⟩ := ha
  obtain ⟨md', f', r', x', h1', h2', h3', h4'⟩ := hb
  rw [h1] at h1'
  cases h1'
  obtain rfl := readFiles_unique h2 h2'
  rw [h3] at h3'
  cases h3'
  rw [h4] at h4'
  cases h4'
  rfl

/-- **Every module's frontier holds only the specification's values**, of the files on the
snapshot. -/
theorem readOleans_good {sp : SearchPath} {roots : Array Name} {constants : Option (Array Name)}
    {jobs : Nat} {fs : FS} {hs : HS} {rd : OleanRead} {hs' : HS}
    (h : (readOleans sp roots constants jobs : ModelIO _) fs hs (.ok (.ok rd)) hs') :
    ∀ md ∈ rd.values, ∃ f r a, ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r := by
  obtain ⟨order, ls, mg, rs, -, -, h2, -, -, -, -, -, -, -, hv, -⟩ := readOleans_ok h
  intro md hmd
  rw [hv] at hmd
  obtain ⟨l, hl, rfl⟩ := Array.mem_map.mp hmd
  obtain ⟨i, f, -, hf, hload⟩ := h2 l (by simpa using hl)
  obtain ⟨r, a, sk, skels, hreg, -, -, -, -, hgood, -⟩ := loadAt_spec hload
  exact ⟨f, r, a, hf, hreg, hgood⟩

/-- An inductive record is an `indDecl`. -/
theorem indBlockOfF_ind {nm : Nat → M Name} {lv : Nat → M Level} {ex : Nat → M Expr}
    {tys : List IndTypeRec} {cts : List (IndCtorRec × Name)} {rcs : List IndRecRec} {n : Nat} {d : Declaration}
    (h : indBlockOfF nm lv ex tys cts rcs n = .ok d) : ∃ b, d = .indDecl b n := by
  have ebind : ∀ {α β : Type} {x : M α} {f : α → M β} {y : β}, (x >>= f) = .ok y →
      ∃ a, f a = .ok y := by
    intro α β x f y hb
    cases x with
    | error e => cases hb
    | ok a => exact ⟨a, hb⟩
  unfold indBlockOfF at h
  obtain ⟨_, h⟩ := ebind h
  obtain ⟨_, h⟩ := ebind h
  obtain ⟨_, h⟩ := ebind h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨_, h.symm⟩

/-- An inductive record is no theorem's. -/
theorem declOfF_ind_thm {nm : Nat → M Name} {lv : Nat → M Level} {ex : Nat → M Expr}
    {tys : List IndTypeRec} {cts : List IndCtorRec} {rcs : List IndRecRec} {cv : ConstantVal} {v : Expr}
    (h : declOfF nm lv ex (.ind tys cts rcs) = .ok (.inl (.thmDecl cv v))) : False := by
  simp only [declOfF, bind, Except.bind, pure, Except.pure] at h
  cases hv : validateIndF nm lv ex tys cts rcs with
  | error e => simp only [hv] at h; cases h
  | ok x =>
    simp only [hv] at h
    rcases x with x | ⟨c, n⟩
    · simp at h
    · simp only at h
      cases hb : indBlockOfF nm lv ex tys c rcs n with
      | error e => simp only [hb] at h; cases h
      | ok d =>
        simp only [hb, Except.ok.injEq, Sum.inl.injEq] at h
        subst h
        obtain ⟨b, hb'⟩ := indBlockOfF_ind hb
        cases hb'

/-- **A theorem's record, with its value in place, is the specification's constant**: the
reference in a record of the run stands, on the snapshot, for the value of the theorem the
specification reads off the files of the reference's module (`constSpec`), and the record's
statement is that theorem's.  Whichever of a name's copies Lean's rule keeps, this is the
kept one's: nothing is read from anywhere else. -/
theorem readOleans_filled {sp : SearchPath} {roots : Array Name} {constants : Option (Array Name)}
    {jobs : Nat} {fs : FS} {hs : HS} {rd : OleanRead} {hs' : HS} {cv : ConstantVal} {code : Nat}
    {e : Expr} (h : (readOleans sp roots constants jobs : ModelIO _) fs hs (.ok (.ok rd)) hs')
    (hd : Declaration.thmDecl cv (.bvar code) ∈ rd.decls)
    (hv : ValueAt sp fs rd.values code e) :
    ∃ md f r a sk loc c all, rd.values[refModule code]? = some md ∧
      ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ moduleSkel r a = some sk ∧ loc ∈ sk.consts ∧
      constSpec r loc = some c ∧ c.kind = .thm e all ∧ cv = ⟨c.name, c.levelParams, c.type⟩ := by
  obtain ⟨order, ls, mg, rs, -, h1, h2, -, -, -, hm, -, -, hds, hvals, -⟩ := readOleans_ok h
  obtain ⟨hk1, hk2, hk3, hk4⟩ := mergeAll_ok hm
  have hN : ∀ (n : Name) (x : CEntry), mg.map[n]? = some x → x.name = n := fun n x hx => (hk2 n x hx).1
  -- the record's constant
  obtain ⟨E, hS, hE⟩ : ∃ E, Stored mg E ∧ entryDecl E = some (.thmDecl cv (.bvar code)) := by
    rcases declsOf_from hN hds hd with h' | ⟨ts, cts, rcs, -, hb⟩
    · exact h'
    · exact (declOfF_ind_thm hb).elim
  obtain ⟨all, hkE, hcv⟩ : ∃ all, E.kind = .thm (.bvar code) all ∧
      cv = ⟨E.name, E.levelParams, E.type⟩ := by
    unfold entryDecl at hE
    cases hk : E.kind with
    | thm v all =>
      simp only [hk, Option.some.injEq, Declaration.thmDecl.injEq] at hE
      obtain ⟨rfl, rfl⟩ := hE
      exact ⟨all, rfl, rfl⟩
    | ax u => simp [hk] at hE
    | defn v h s =>
      simp only [hk] at hE
      split at hE <;> first | contradiction | simp at hE
    | opaq v u => simp [hk] at hE
    | quot k =>
      simp only [hk] at hE
      split at hE <;> first | contradiction | simp at hE
    | induct _ _ _ _ _ _ _ _ => simp [hk] at hE
    | ctor _ _ _ _ _ => simp [hk] at hE
    | recur _ _ _ _ _ _ _ _ => simp [hk] at hE
  -- its module and its skeleton
  obtain ⟨-, l, hl, hEl⟩ := hk2 _ _ hS
  have hl' : l ∈ ls := by simpa using hl
  obtain ⟨i, f, hzip, hf, hload⟩ := h2 l hl'
  obtain ⟨r, a, sk, skels, hreg, -, hsk, hskels, -, -, hlazy⟩ := loadAt_spec hload
  obtain ⟨s, hs, hent⟩ := hlazy.to_skel E (by simpa using hEl)
  obtain ⟨p, g, all₀, hsk1, hw, hloc, hi, hn, hlp, hty, hall⟩ := lazyEntry_thm hent hkE
  obtain ⟨hm1, hm2⟩ := refParts (g := g) hi
  have hcode : code = g * refBase + i := by
    simp only [valueRef, Expr.bvar.injEq] at hw
    exact hw
  subst hcode
  -- the module the reference names is this one
  have hzi : order.toList[i]? = some l.name := List.mem_zipIdx_iff_getElem?.mp hzip
  rw [← h1] at hzi
  obtain ⟨md, f', r', a', hmd, hf', hreg', hval⟩ := hv
  rw [hm1] at hmd
  rw [hm2] at hval
  have hname : md.name = l.name := by
    rw [hvals] at hmd
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hzi
    obtain ⟨y, hy, hyn⟩ := hzi
    simp only [Array.getElem?_map, List.getElem?_toArray, hy, Option.map_some,
      Option.some.injEq] at hmd
    rw [← hmd]
    exact hyn
  rw [hname] at hf'
  obtain rfl := readFiles_unique hf hf'
  rw [hreg] at hreg'
  cases hreg'
  obtain ⟨loc, hlocm, hcs⟩ := mapM_mem_inv hskels hs
  have hep : exprP r p = some e := by
    simp only [exprP, hloc]
    exact hval
  have hspec : constSpec r loc = some ⟨E.name, E.levelParams, E.type, .thm e all⟩ := by
    unfold constSpec
    rcases s with ⟨sn, sl, st, sk'⟩
    simp only at hsk1 hn hlp hty
    subst hsk1
    simp only [hcs, bind, Option.bind, CEntryF.mapM, CKindF.mapM, hn, hlp, hty, hep, hall, pure]
  refine ⟨md, f, r, a, sk, loc, _, all, ?_, by rw [hname]; exact hf, hreg, hsk, hlocm, hspec, rfl, hcv⟩
  rw [hm1, hmd]

end ConLeche.Frontend.Olean
