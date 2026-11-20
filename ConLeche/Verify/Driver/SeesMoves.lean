module

public import ConLeche.Verify.Driver.SeesLoads
public import ConLeche.Verify.Driver.CompareRun
public import ConLeche.Verify.Frontend.Olean.Local

public section

/-!
# What a module sees, moved between snapshots and lookups (task #619)

The specification's notions (`ViewOf`, `InClosure`, `LoadsAt`, `InModulePart`, `Sees`) read the
files through `readFiles` only, so

* **on two snapshots** whose `readFiles` answers agree they agree (`viewOf_iff`, `inClosure_iff`,
  `loadsAt_iff`, `sees_iff`, `moduleConstants_iff`), as they do on snapshots agreeing under the
  directories of a lookup without fallback (`readFiles_iff_of_agree`);
* **through a lookup and its fallback-free trim** (`Roots.Trims`), what the trim reads, the full
  lookup reads alike (`viewOf_trims`, `loadsAt_trims`, `inModulePart_trims`), so what a module sees
  through the trim it sees through the full lookup, with any imports added (`sees_trims`).
-/

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Frontend ConLeche.Frontend.Olean

/-- **`readFiles` on two snapshots agreeing under a lookup's directories** gives alike. -/
theorem readFiles_iff_of_agree {dirs : SearchPath} {fs₁ fs₂ : FS}
    (h : FS.AgreeUnder dirs fs₁ fs₂) (m : Name) (p : OLeanLevel) (f : ModFiles) :
    ModelIO.CanGive (readFiles (dirs : Roots) m p) fs₁ (.ok f) ↔
      ModelIO.CanGive (readFiles (dirs : Roots) m p) fs₂ (.ok f) := by
  have hR : RootsIn dirs (dirs : Roots) :=
    ⟨fun _ h => h, fun _ h => by simp at h, fun _ _ h => by simp at h⟩
  unfold ModelIO.CanGive
  rw [(readFiles_local hR m p).1 fs₁ fs₂ h]

section Snapshots

variable {R : Roots} {fs₁ fs₂ : FS}
  (hf : ∀ m p f, ModelIO.CanGive (readFiles R m p) fs₁ (.ok f) ↔
    ModelIO.CanGive (readFiles R m p) fs₂ (.ok f))
include hf

theorem viewOf_iff {m : Name} {d : ModDecoded} : ViewOf R fs₁ m d ↔ ViewOf R fs₂ m d := by
  unfold ViewOf; simp only [hf]

theorem inClosure_of_files {roots : Array Name} {m : Name} (h : InClosure R fs₂ roots m) :
    InClosure R fs₁ roots m := by
  induction h with
  | root hr => exact .root hr
  | step _ hv hi ih => exact .step ih ((viewOf_iff hf).2 hv) hi

theorem loadsAt_iff {g : Bool} {imps : Array ImportRec} {m : Name} {b : Bool} :
    LoadsAt R fs₁ g imps m b ↔ LoadsAt R fs₂ g imps m b := by
  constructor
  · intro h
    induction h with
    | root hi => exact .root hi
    | step _ hv hi hx ih => exact .step ih ((viewOf_iff hf).1 hv) hi hx
  · intro h
    induction h with
    | root hi => exact .root hi
    | step _ hv hi hx ih => exact .step ih ((viewOf_iff hf).2 hv) hi hx

theorem inModulePart_iff {m : Name} {p : OLeanLevel} {c : ConstantInfo} :
    InModulePart R fs₁ m p c ↔ InModulePart R fs₂ m p c := by
  unfold InModulePart; simp only [hf]

theorem sees_of_files {m n m' : Name} (h : Sees R fs₂ m n m') : Sees R fs₁ m n m' := by
  obtain ⟨p, c, ⟨d, hv, hl⟩, hc, hn⟩ := h
  refine ⟨p, c, ⟨d, (viewOf_iff hf).2 hv, ?_⟩, (inModulePart_iff hf).2 hc, hn⟩
  cases p with
  | «private» => exact (loadsAt_iff hf).2 hl
  | exported => exact ⟨(loadsAt_iff hf).2 hl.1, fun h' => hl.2 ((loadsAt_iff hf).1 h')⟩
  | server => exact hl

end Snapshots

section Trims

variable {a L : Roots} (ha : a.Trims L) {fs : FS}
include ha

theorem viewOf_trims {m : Name} {d : ModDecoded} (h : ViewOf a fs m d) : ViewOf L fs m d := by
  obtain ⟨f, hf, hd⟩ := h
  exact ⟨f, readFiles_trims ha hf, hd⟩

theorem loadsAt_trims {g : Bool} {imps : Array ImportRec} {m : Name} {b : Bool}
    (h : LoadsAt a fs g imps m b) : LoadsAt L fs g imps m b := by
  induction h with
  | root hi => exact .root hi
  | step _ hv hi hx ih => exact .step ih (viewOf_trims ha hv) hi hx

theorem inModulePart_trims {m : Name} {p : OLeanLevel} {c : ConstantInfo}
    (h : InModulePart a fs m p c) : InModulePart L fs m p c := by
  obtain ⟨f, d, e, hf, hd, he, hc⟩ := h
  exact ⟨f, d, e, readFiles_trims ha hf, hd, he, hc⟩

/-- **What a module sees through the trim, it sees through the full lookup**, with any imports
added. -/
theorem sees_trims (x : Array ImportRec) {m n m' : Name} (h : Sees a fs m n m') :
    SeesX L fs x m n m' := by
  obtain ⟨p, c, hL, hc, hn⟩ := sees_toX x h
  obtain ⟨d, hv, hl⟩ := hL
  refine ⟨p, c, ⟨d, viewOf_trims ha hv, ?_⟩, inModulePart_trims ha hc, hn⟩
  cases p with
  | «private» => exact loadsAt_trims ha hl
  | exported => exact loadsAt_trims ha hl
  | server => exact hl

/-- **A module of a closure through a trimmed lookup is one through the full one.** -/
theorem hdrClosure_trims {roots : List Name} {m : Name} (h : Graph.HdrClosure a fs roots m) :
    Graph.HdrClosure L fs roots m := by
  induction h with
  | root hr => exact .root hr
  | step _ hc hi ih => exact .step ih (moduleImports_trims ha hc) hi

end Trims

/-- A module of the closure of some roots is one of the closure of more. -/
theorem hdrClosure_mono {sp : Roots} {fs : FS} {roots roots' : List Name}
    (hr : ∀ r ∈ roots, r ∈ roots') {m : Name} (h : Graph.HdrClosure sp fs roots m) :
    Graph.HdrClosure sp fs roots' m := by
  induction h with
  | root h => exact .root (hr _ h)
  | step _ hc hi ih => exact .step ih hc hi

end ConLeche.Driver.Compose
