module

public import ConLeche.Driver.Compare
public import ConLeche.Verify.Driver.Oleans

/-!
# A compared run, in the model (tasks #607, #619)

`compareG_accept`: every outcome of `compareG` that is an exit 0 read the challenge's closure
through the challenge's lookup (`CmpReq.chalRoots`, the trusted path alone) and the solution's
through the solution's (`CmpReq.solRoots`, the trusted path, then the search path); every
`--constant` name is a declaration of the challenge module; `checkDecls` accepts the solution's
prepared records with its theorems' values in place (`solChecked`), at the environment they
denote (the solution `envS`); and the fold with `envS` as the solution has an accepting run over
the challenge's records as its check reads them (`chalChecked`: every hole the axiom of its
statement, the theorems' values in place).  The run, not `checkDeclsWith`: a theorem the
challenge's file does not mark as a hole is checked as a theorem whatever its value, and the
model needs only the run (`Model.Solution.solution_envModel_run`).
-/

public section

namespace ConLeche.Driver

open ConLeche Frontend.Olean Cached

/-- **The solution's records, as its check reads them**: its prepared records, its theorems'
values in place. -/
@[expose] noncomputable def solChecked (pre : Frontend.PreludeIx) (R : Roots) (fs : FS)
    (rd : OleanRead) : Array Declaration :=
  (Frontend.prepareD pre rd.decls (usedOf (some (R.path, rd)))).decls.map
    (fillDecl (fillOf R fs rd.values))

/-- **The challenge's records, as its check reads them** with the solution's environment `envS`
(`chalRecords`: every hole the axiom of its statement), its theorems' values in place. -/
@[expose] noncomputable def chalChecked (pre : Frontend.PreludeIx) (envS : Env) (R : Roots)
    (fs : FS) (rd : OleanRead) : Array Declaration :=
  (chalRecords envS (usedOf (some (R.path, rd)))
    (Frontend.prepareD pre rd.decls (usedOf (some (R.path, rd)))).decls).map
    (fillDecl (fillOf R fs rd.values))

theorem CmpReq.chalRoots_bare (r : CmpReq) : r.chalRoots.bare = r.chalRoots := by
  unfold CmpReq.chalRoots
  split <;> rfl

theorem CmpReq.chalRoots_eta (r : CmpReq) : r.chalRoots = { path := r.chalRoots.path } := by
  unfold CmpReq.chalRoots
  split <;> rfl

theorem CmpReq.solRoots_bare (r : CmpReq) : r.solRoots.bare = r.solRoots := by
  unfold CmpReq.solRoots
  split <;> rfl

/-- **The challenge's lookup is the solution's without its fallback** (task #608). -/
theorem CmpReq.chal_trims (r : CmpReq) : r.chalRoots.Trims r.solRoots := by
  unfold CmpReq.chalRoots CmpReq.solRoots
  split
  · exact Roots.Trims.refl _
  · exact Or.inr ⟨rfl, rfl⟩

/-- A failed read's verdict is no exit 0. -/
theorem readFailed_ne {modeTag label : String} {x : CheckError × Nat} {fs : FS} {hs : HS} :
    ModelIO.AllOk (readFailed modeTag label x) fs hs (fun c => c ≠ 0) := by
  obtain ⟨e, line⟩ := x
  cases e <;> simp [readFailed, diagLine]

/-- No `--constant` fault: every name is a declaration of the challenge module. -/
theorem foreignConstant_none {r : CmpReq} {homes : Std.HashMap Name Name}
    (h : foreignConstant r homes = none) :
    ∀ cs, r.constants = some cs → ∀ c ∈ cs, homes[c]? = some r.challenge := by
  intro cs hcs c hc
  cases hf : cs.find? (homes[·]? != some r.challenge) with
  | some c' => simp [foreignConstant, hcs, hf, bind, Option.bind] at h
  | none =>
    have := Array.find?_eq_none.mp hf c hc
    simpa using this

/-- The good regions of a read's modules, for its check phase. -/
theorem readOleansAt_goodRoots {R : Roots} (hR : R.bare = R) {roots : Array Name}
    {cs : Option (Array Name)} {jobs : Nat} {pace : Pace} {lenient homes : Bool} {fs : FS}
    {rd : OleanRead} {hs hs' : HS}
    (h : (readOleansAt R roots cs jobs pace lenient homes : ModelIO _) fs hs (.ok (.ok rd)) hs') :
    (∀ md ∈ rd.values, ∃ f r a,
      ModelIO.CanGive (readFiles rd.roots md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r) ∧
    fillOf rd.roots fs rd.values = fillOf R fs rd.values := by
  obtain ⟨-, -, -, -, ⟨T, -, hrT, hT, hTp⟩, -⟩ := readOleansAt_ok hR h
  refine ⟨fun md hmd => ?_, ?_⟩
  · obtain ⟨f, r', a, h1, h2, h3⟩ := readOleansAt_good hR h md hmd
    exact ⟨f, r', a, readFiles_rev (hrT ▸ hT) (hrT ▸ hTp ▸ h1), h2, h3⟩
  · rw [hrT, fillOf_roots hT, hTp]

/-- **An exit 0 of a compared run** (see the module docstring). -/
theorem compareG_accept {r : CmpReq} {mode : CheckMode} {maxNatSize : Nat} {pace : Pace}
    {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (compareG r mode maxNatSize pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre rdC rdS n fe, Frontend.builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (readOleansAt r.chalRoots #[r.challenge] r.constants (lenient := true)
        (homes := true)) fs (.ok rdC) ∧
      (∀ cs, r.constants = some cs → ∀ c ∈ cs, rdC.homes[c]? = some r.challenge) ∧
      ModelIO.CanGive (readOleansAt r.solRoots #[r.solution]
        (r.constants.map fun _ => (Frontend.prepareD pre rdC.decls
          (usedOf (some (r.chalRoots.path, rdC)))).decls.map recKey) (lenient := true))
        fs (.ok rdS) ∧
      checkDecls mode natOpPinSets maxNatSize (solChecked pre r.solRoots fs rdS)
        = .ok (streamEnv (solChecked pre r.solRoots fs rdS).toList) ∧
      DeclsRun mode natOpPinSets maxNatSize
        (solutionOf (some (streamEnv (solChecked pre r.solRoots fs rdS).toList))
          (chalChecked pre (streamEnv (solChecked pre r.solRoots fs rdS).toList) r.chalRoots fs rdC))
        (chalChecked pre (streamEnv (solChecked pre r.solRoots fs rdS).toList) r.chalRoots fs
          rdC).toList (0, mkFEnv Env.empty) (n, fe) := by
  suffices H : ModelIO.AllOk (compareG r mode maxNatSize pace jobs) fs hs (fun c => c = 0 → _) from
    H 0 hs' h rfl
  cases hp : Frontend.builtinPreludeE with
  | error x =>
    rcases x with ⟨_ | _ | _, _⟩ <;>
      simp [compareG, hp, clockMs, diagLine]
  | ok pre =>
    simp only [compareG, hp, clockMs, diagLine, outLine, ModelIO.allOk_bind,
      ModelIO.liftIO_iff, forall_eq]
    intro t0 pre' hs1 hpre
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hpre
    obtain ⟨rfl, rfl⟩ := hpre
    intro _ x hs2 hx
    rcases x with e | rdC
    · simp only [ModelIO.allOk_bind]
      intro w hs3 _
      split
      · simp
      · exact fun c hs4 hc h0 => (readFailed_ne c hs4 hc h0).elim
    simp only
    cases hfc : foreignConstant r rdC.homes with
    | some why => simp
    | none =>
    have hcs := foreignConstant_none hfc
    simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq]
    intro _ y hs3 hy
    rcases y with e | rdS
    · exact fun c hs4 hc h0 => (readFailed_ne c hs4 hc h0).elim
    simp only
    cases hin : rdS.values.any (·.name == r.challenge) with
    | true => simp
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq]
    intro _ _ _ _ _ _ vS hs5 hvS
    rcases vS with e | u
    · exact fun c hs6 hc h0 => absurd (verdictG_ok hc h0) (by simp)
    simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq]
    intro _ _ _ _ _ _ vC hs7 hvC
    rcases vC with e | u'
    · exact fun c hs8 hc h0 => absurd (verdictG_ok hc h0) (by simp)
    intro _ _ _ _
    have hx' : (readOleansAt r.chalRoots #[r.challenge] r.constants (lenient := true)
        (homes := true) : ModelIO _) fs _ (.ok (.ok rdC)) _ := hx
    obtain ⟨hgoodC, hfC⟩ := readOleansAt_goodRoots r.chalRoots_bare hx'
    obtain ⟨hgoodS, hfS⟩ := readOleansAt_goodRoots r.solRoots_bare hy
    obtain ⟨envS, henvS⟩ := checkOleansG_accept hgoodS hvS
    rw [hfS] at henvS
    have hS : checkDecls mode natOpPinSets maxNatSize (solChecked pre' r.solRoots fs rdS)
        = .ok (streamEnv (solChecked pre' r.solRoots fs rdS).toList) := by
      rw [solChecked, henvS, checkDecls_env henvS]; rfl
    obtain ⟨n, fe, hrun⟩ := checkOleansG_run hgoodC hvC
    rw [hfC] at hrun
    refine ⟨pre', rdC, rdS, n, fe, rfl, ⟨_, _, hx⟩, hcs, ⟨_, _, hy⟩, hS, ?_⟩
    rw [solChecked, Array.toList_map, streamEnv_fill]
    exact hrun

end ConLeche.Driver
