module

import ConLeche.Verify.OleanInput
public import ConLeche.OleanInput
public import ConLeche.Verify.IsModelRecords
import ConLeche.Verify.Driver.Main
public import ConLeche.Verify.Driver.CompareRun
public import ConLeche.Driver.Cli
import ConLeche.Verify.IsModelSide
public import ConLeche.Verify.Frontend.Olean.Local
import Std.Data.HashMap.Lemmas

/-!
# A compared run's challenge, as the specification reads it (task #619)

`runArgs_compare_stored`: an exit 0 of `--olean --compare --trusted-search-path=<T>
--search-path=<D> -- <c> <s>` checked a solution stream (`checkDecls … = .ok envS`), and the fold
with `envS` as the solution has an accepting run whose environment stores every constant of the
closure of `C` through `T` (`Olean.closureConstants`).  Every record of the challenge's read
stands in that run as itself, or a theorem or a hole as the axiom of its statement
(`holeRecord`, `sideRecord`), and `StoredAs` compares a statement kind by its statement alone.
Where `T` names no directory the challenge is read through `D`, and the closure through `T` is
empty (`closureConstants_nil`: nothing resolves on the empty path).

`closureConstants_local`: the closure's constants through a search path are the same on two
snapshots that agree on every path the reader forms under it.
-/

public section

namespace ConLeche

open Frontend Olean Cached

/-! ## A record as the challenge's check reads it -/

/-- **A theorem read as a hole has the hole's constant**: `holeRecord` keeps a record's
constants, or reads a theorem's statement as an axiom's. -/
theorem holeRecord_constants (uses : Declaration → Array Name) (d : Declaration) :
    (Driver.holeRecord uses d).constants = d.constants ∨
      ∃ cv v, d = .thmDecl cv v ∧ (Driver.holeRecord uses d).constants = [.axiomInfo cv] := by
  cases d with
  | thmDecl cv v =>
    by_cases hc : (!builtinAxiomName cv.name && (uses (.thmDecl cv v)).contains sorryAxName) = true
    · right
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      have h1 : cv.name ≠ quotSoundName := fun e => by simp [builtinAxiomName, e] at hc
      have h2 : cv.name ≠ sorryAxName := fun e => by simp [builtinAxiomName, e] at hc
      refine ⟨cv, v, rfl, ?_⟩
      have e : Driver.holeRecord uses (.thmDecl cv v) = .axiomDecl cv := by
        simp only [Driver.holeRecord, hc.1, hc.2, Bool.not_false, Bool.and_self, ↓reduceIte]
      rw [e]
      simp [Declaration.constants, h1, h2]
    · left
      simp only [Driver.holeRecord, hc, Bool.false_eq_true, ↓reduceIte]
  | _ => left; rfl

/-- An axiom at a name no built-in axiom has passes the reserved names' check as a definition,
theorem or opaque constant of its statement does. -/
theorem basisNamesOk_axiom {cv : ConstantVal} (h : builtinAxiomName cv.name = false) :
    basisNamesOk (.axiomDecl cv) = !reservedBasisNames.contains cv.name := by
  have h1 : cv.name ≠ quotSoundName := fun e => by simp [builtinAxiomName, e] at h
  simp [basisNamesOk, h1]

theorem basisNamesOk_holeRecord (uses : Declaration → Array Name) (d : Declaration) :
    basisNamesOk (Driver.holeRecord uses d) = basisNamesOk d := by
  cases d with
  | thmDecl cv v =>
    simp only [Driver.holeRecord]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      rw [basisNamesOk_axiom hc.1]; rfl
    · rfl
  | _ => rfl

theorem basisNamesOk_sideRecord (d : Declaration) :
    basisNamesOk (sideRecord d) = basisNamesOk d := by
  cases d with
  | defnDecl cv v h | thmDecl cv v | opaqueDecl cv v =>
    simp only [sideRecord]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      rw [basisNamesOk_axiom hc.1]; rfl
    · rfl
  | _ => rfl

/-- **A record that keeps its constants, or reads a theorem's statement as an axiom's, stores
every constant of the record** (`StoredAs` reads a statement kind by its statement). -/
theorem covers_stmt {d d' : Declaration}
    (h : d'.constants = d.constants ∨ ∃ cv v, d = .thmDecl cv v ∧ d'.constants = [.axiomInfo cv]) :
    ∀ c ∈ d.constants, ∃ c' ∈ d'.constants, StoredAs c' c := by
  rcases h with h | ⟨cv, v, rfl, h⟩
  · intro c hc
    exact ⟨c, h ▸ hc, StoredAs.refl c⟩
  · intro c hc
    simp only [Declaration.constants, List.mem_singleton] at hc
    subst hc
    have hst : StoredAs (.axiomInfo cv) (.thmInfo cv) := by
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> intros <;> simp_all
    exact ⟨.axiomInfo cv, by simp [h], hst⟩

theorem StoredAs.covers_trans {d d' d'' : Declaration}
    (h₁ : ∀ c ∈ d.constants, ∃ c' ∈ d'.constants, StoredAs c' c)
    (h₂ : ∀ c ∈ d'.constants, ∃ c' ∈ d''.constants, StoredAs c' c) :
    ∀ c ∈ d.constants, ∃ c' ∈ d''.constants, StoredAs c' c := fun c hc =>
  let ⟨c', hc', hs'⟩ := h₁ c hc
  let ⟨c'', hc'', hs''⟩ := h₂ c' hc'
  ⟨c'', hc'', hs''.trans hs'⟩

/-- **The challenge's closure is stored by the run over its records** (`Driver.chalChecked`). -/
theorem chalChecked_inputStored {R : Roots} (hR : R.bare = R) {C : Name} {jobs : Nat} {pace : Pace}
    {lenient homes : Bool} {fs : FS} {rd : OleanRead} {hs hs' : HS}
    (h : (readOleansAt R #[C] none jobs pace lenient homes : ModelIO _) fs hs (.ok (.ok rd)) hs')
    {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat} {pre : PreludeIx}
    {envS : Env} {J : Option Solution} {n : Nat} {fe : FEnv}
    (run : DeclsRun mode pins maxNatSize J (Driver.chalChecked pre envS R fs rd).toList
      (0, mkFEnv Env.empty) (n, fe)) :
    RecordsStored (closureConstants R fs #[C]) fe.env := by
  have hfill : ∀ (F : Expr → Expr) d, (fillDecl F d).constants = d.constants := by
    intro F d; cases d <;> rfl
  refine inputStored_of hR h (pre := pre) (used := Driver.usedOf (some (R.path, rd)))
    (g := fun d => fillDecl (Driver.fillOf R fs rd.values)
      (sideRecord (Driver.holeRecord (Driver.usedOf (some (R.path, rd))) d)))
    (declsRun_recordsStored run) (fun d hd => ?_) (declsRun_basisNamesOk run) (fun d => ?_)
    (fun d => ?_)
  · exact Array.mem_toList_iff.mpr
      (Array.mem_map_of_mem (Array.mem_map_of_mem (Array.mem_map_of_mem hd)))
  · rw [show ∀ x, basisNamesOk (fillDecl (Driver.fillOf R fs rd.values) x) = basisNamesOk x by
      intro x; cases x <;> rfl, basisNamesOk_sideRecord, basisNamesOk_holeRecord]
  · refine StoredAs.covers_trans
      (covers_stmt (holeRecord_constants (Driver.usedOf (some (R.path, rd))) d)) ?_
    rw [hfill]
    exact covers_stmt (constants_sideRecord _)

/-! ## The closure through a path -/

/-- **Nothing resolves on the empty path**: the closure through it has no constant. -/
theorem closureConstants_nil {fs : FS} {roots : Array Name} {c : ConstantInfo} :
    ¬ closureConstants ({ path := [] } : Roots) fs roots c := by
  rintro ⟨m, -, f, d, e, ⟨hs, hs', hf⟩, -⟩
  obtain ⟨loc, -, -, hfind, -⟩ := readFiles_ok hf
  obtain ⟨hs₁, h1⟩ := hfind hs
  have hR : RootsIn [] ({ path := [] } : Roots) :=
    ⟨fun _ h => h, fun _ h => by simp at h, fun _ _ h => by simp at h⟩
  have hx : (findModule ({ path := [] } : Roots) m : ModelIO _) fs hs (.ok (.ok loc)) hs₁ := by
    rw [h1]; exact ⟨rfl, rfl⟩
  exact absurd ((findModule_local hR m).2 fs hs _ hs₁ hx loc rfl) (by simp)

/-- **The closure's constants through a path are local to it**: the same on two snapshots that
agree on every path the reader forms under it. -/
theorem closureConstants_local {dirs : SearchPath} {fs₁ fs₂ : FS}
    (h : FS.AgreeUnder dirs fs₁ fs₂) (roots : Array Name) :
    closureConstants (dirs : Roots) fs₁ roots = closureConstants (dirs : Roots) fs₂ roots := by
  have hR : RootsIn dirs (dirs : Roots) :=
    ⟨fun _ h => h, fun _ h => by simp at h, fun _ _ h => by simp at h⟩
  have hf : ∀ m p f, ModelIO.CanGive (readFiles (dirs : Roots) m p) fs₁ (.ok f) ↔
      ModelIO.CanGive (readFiles (dirs : Roots) m p) fs₂ (.ok f) := by
    intro m p f
    unfold ModelIO.CanGive
    rw [(readFiles_local hR m p).1 fs₁ fs₂ h]
  have hv : ∀ m d, ViewOf dirs fs₁ m d ↔ ViewOf dirs fs₂ m d := fun m d => by
    unfold ViewOf
    simp only [hf]
  have hcl : ∀ m, InClosure dirs fs₁ roots m ↔ InClosure dirs fs₂ roots m := by
    intro m
    constructor
    · intro hm
      induction hm with
      | root hr => exact .root hr
      | step _ hv' hi ih => exact .step ih ((hv _ _).1 hv') hi
    · intro hm
      induction hm with
      | root hr => exact .root hr
      | step _ hv' hi ih => exact .step ih ((hv _ _).2 hv') hi
  funext c
  apply propext
  unfold closureConstants moduleConstants InModulePart
  simp only [hcl, hf]

/-! ## The compared run -/

/-- **An accepted compared run stores the challenge's closure through the trusted path** (see the
module docstring). -/
theorem Driver.runArgs_compare_stored {T D c s : String} {C S : Name} {fs : FS} {hs hs' : HS}
    (hc : parseModName c = some C) (hsol : parseModName s = some S)
    (h : (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ (dsS : Array Declaration) (envS : Env) (rs : Array Declaration) (n : Nat) (fe : FEnv),
      checkDecls .verified natOpPinSets maxNatSizeDefault dsS = .ok envS ∧
      DeclsRun .verified natOpPinSets maxNatSizeDefault (solutionOf (some envS) rs) rs.toList
        (0, mkFEnv Env.empty) (n, fe) ∧
      RecordsStored (closureConstants (Driver.searchPathOf T) fs #[C]) fe.env := by
  obtain ⟨pre, rdC, rdS, n, fe, -, ⟨hs₁, hs₂, hrd⟩, -, hS, hrun⟩ :=
    Driver.runArgs_compare_accept hc hsol h
  refine ⟨_, _, _, n, fe, hS, hrun, ?_⟩
  by_cases ht : (Driver.searchPathOf T).isEmpty = true
  · rw [List.isEmpty_iff.mp ht]
    exact fun c hc => (closureConstants_nil hc).elim
  · have e : (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).chalRoots
        = (Driver.searchPathOf T : Roots) := by
      simp [Driver.CmpReq.chalRoots, ht]
    have hb := Driver.CmpReq.chalRoots_bare ⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩
    rw [e] at hrd hrun hb
    exact chalChecked_inputStored hb hrd hrun

end ConLeche
