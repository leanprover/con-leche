module

public import ConLeche.Driver.Compare
public import ConLeche.Verify.Driver.Oleans

/-!
# A compared run, in the model (task #607)

`compareG_accept`: every outcome of `compareG` that is an exit 0 read the challenge's closure
through the challenge's lookup (`CmpReq.chalRoots`, the trusted path alone) and the solution's
through the solution's (`CmpReq.solRoots`, the trusted path, then the search path); every
`--constant` name is a declaration of the challenge module; the comparison of the two sets of
prepared records (`cmpRecs`) passed, with what each challenge record stands for (`ctx`); those
read only what the records before them install (`ctxScoped`); and `checkDecls` accepts the
solution's prepared records with its theorems' values in place.  The model-tier half is
`Model.Compare.compare_models`; the two together are `ConLeche.compare_solves`
(`ConLeche/MainTheorem.lean`).
-/

public section

namespace ConLeche.Driver

open ConLeche Frontend.Olean Cached

/-- **A read's prepared records**, as the compared run prepares them. -/
@[expose] def cmpRecs (pre : Frontend.PreludeIx) (R : Roots) (rd : OleanRead) :
    Array Declaration :=
  (Frontend.prepareD pre rd.decls (usedOf (some (R.path, rd)))).decls

/-- **The challenge's environment**: its prepared records installed in order, every hole of the
challenge module `C` (`isHole`) as the axiom of its statement (`chalRecord`), at the challenge's
own level-parameter names. -/
@[expose] def challengeEnv (pre : Frontend.PreludeIx) (C : Name) (R : Roots) (rd : OleanRead) :
    Env :=
  streamEnv ((cmpRecs pre R rd).toList.map (chalRecord C (usedOf (some (R.path, rd))) rd.homes))

/-- **The solution's environment**: its prepared records, its theorems' values in place. -/
@[expose] noncomputable def solutionEnv (pre : Frontend.PreludeIx) (R : Roots) (fs : FS)
    (rd : OleanRead) : Env :=
  streamEnv ((cmpRecs pre R rd).map (fillDecl (fillOf R fs rd.values))).toList

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

/-- **An exit 0 of a compared run** (see the module docstring). -/
theorem compareG_accept {r : CmpReq} {mode : CheckMode} {maxNatSize : Nat} {pace : Pace}
    {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (compareG r mode maxNatSize pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre rdC rdS ctx filled env, Frontend.builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (readOleansAt r.chalRoots #[r.challenge] r.constants (lenient := true)
        (homes := true)) fs (.ok rdC) ∧
      (∀ cs, r.constants = some cs → ∀ c ∈ cs, rdC.homes[c]? = some r.challenge) ∧
      ModelIO.CanGive (readOleansAt r.solRoots #[r.solution]
        (r.constants.map fun _ => rdC.decls.map recKey) (lenient := true) (homes := true)) fs
        (.ok rdS) ∧
      compareRecords r.challenge (usedOf (some (r.chalRoots.path, rdC))) rdC.homes rdS.homes
        (cmpRecs pre r.solRoots rdS) (recIndex (cmpRecs pre r.solRoots rdS))
        (cmpRecs pre r.chalRoots rdC) = .ok (ctx, filled) ∧
      ctxScoped ctx = none ∧
      checkDecls mode natOpPinSets maxNatSize
        ((cmpRecs pre r.solRoots rdS).map (fillDecl (fillOf r.solRoots fs rdS.values)))
        = .ok env := by
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
    simp only [ModelIO.allOk_bind]
    intro x hs3 hy
    rcases x with e | rdS
    · exact fun c hs4 hc h0 => (readFailed_ne c hs4 hc h0).elim
    simp only
    cases hin : rdS.values.any (·.name == r.challenge) with
    | true => simp
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hcmp : compareRecords r.challenge (usedOf (some (r.chalRoots.path, rdC))) rdC.homes
      rdS.homes (cmpRecs pre' r.solRoots rdS) (recIndex (cmpRecs pre' r.solRoots rdS))
      (cmpRecs pre' r.chalRoots rdC) with
    | error why =>
      simp only [cmpRecs] at hcmp
      rw [hcmp]
      simp only
      split <;> simp
    | ok p =>
      obtain ⟨ctx, filled⟩ := p
      have hcmp' := hcmp
      simp only [cmpRecs] at hcmp'
      rw [hcmp']
      simp only
      cases hsc : ctxScoped ctx with
      | some why => simp
      | none =>
      simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq]
      intro _ hs4 _ _ _ _ v hs5 hv
      rcases v with e | u
      · exact fun c hs6 hc h0 => absurd (verdictG_ok hc h0) (by simp)
      intro _ _ _ _
      have hy' : (readOleansAt r.solRoots #[r.solution]
          (r.constants.map fun _ => rdC.decls.map recKey) (lenient := true) (homes := true) :
            ModelIO _) fs hs2 (.ok (.ok rdS)) hs3 := hy
      obtain ⟨-, -, -, -, ⟨T, -, hrT, hT, hTp⟩, -⟩ := readOleansAt_ok r.solRoots_bare hy'
      have hgood : ∀ md ∈ rdS.values, ∃ f r a,
          ModelIO.CanGive (readFiles rdS.roots md.name .private) fs (.ok f) ∧
          f.viewRegion .private = some (r, a) ∧ md.frontier.Good r := fun md hmd => by
        obtain ⟨f, r', a, h1, h2, h3⟩ := readOleansAt_good r.solRoots_bare hy' md hmd
        exact ⟨f, r', a, readFiles_rev (hrT ▸ hT) (hrT ▸ hTp ▸ h1), h2, h3⟩
      obtain ⟨env, henv⟩ := checkOleansG_accept hgood hv
      rw [hrT, fillOf_roots hT, hTp] at henv
      exact ⟨pre', rdC, rdS, ctx, filled, env, rfl, ⟨_, _, hx⟩, hcs, ⟨_, _, hy'⟩, hcmp, hsc, henv⟩

end ConLeche.Driver
