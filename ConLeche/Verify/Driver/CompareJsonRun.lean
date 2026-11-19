module

public import ConLeche.Driver.CompareJson
public import ConLeche.Verify.Driver.CompareRun
public import ConLeche.Driver.Cli

/-!
# A compared run of two lean4export files, in the model (task #612)

`compareJsonG_accept`: every outcome of `compareJsonG` that is an exit 0 found the challenge
file's bytes `bC` and the solution file's bytes `bS` in the snapshot, each parsing as one chunk;
the comparison of the challenge's records (`jsonRecs`: prepared with the built-in prelude, the
placeholder axiom's left out) with the solution's prepared records passed, with what each
challenge record stands for (`ctx`); those read only what the records before them install
(`ctxScoped`); and `checkDecls` accepts the solution's prepared records.  The model-tier half is
`Model.Compare.compare_solved`; the two together are `ConLeche.main_compare_json_solves`
(`ConLeche/MainTheorem.lean`).
-/

public section

namespace ConLeche.Driver

open ConLeche Frontend Cached

/-- **The challenge's environment**, of a challenge file's records `ds`: its records
(`jsonRecs`) installed in order, every hole as the axiom of its statement (`chalRecord`), at
the challenge's own level-parameter names. -/
@[expose] def jsonChallengeEnv (pre : PreludeIx) (ds : Array Declaration) : Env :=
  streamEnv ((jsonRecs pre ds).toList.map
    (chalRecord jsonOwn Declaration.usedConsts (jsonHomes (jsonRecs pre ds))))

/-- **An exit 0 of a compared run of two lean4export files** (see the module docstring). -/
theorem compareJsonG_accept {r : JCmpReq} {mode : CheckMode} {maxNatSize : Nat} {pace : Pace}
    {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (compareJsonG r mode maxNatSize pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre bC rC bS rS ctx filled env, builtinPreludeE = .ok pre ∧
      fs.file r.challenge = some bC ∧ parseChunks [bC] = .ok rC ∧
      fs.file r.solution = some bS ∧ parseChunks [bS] = .ok rS ∧
      compareRecords jsonOwn Declaration.usedConsts (jsonHomes (jsonRecs pre rC.decls)) {}
        (preparePrelude pre rS.decls) (recIndex (preparePrelude pre rS.decls))
        (jsonRecs pre rC.decls) = .ok (ctx, filled) ∧
      ctxScoped ctx = none ∧
      checkDecls mode natOpPinSets maxNatSize (preparePrelude pre rS.decls) = .ok env := by
  suffices H : ModelIO.AllOk (compareJsonG r mode maxNatSize pace jobs) fs hs
      (fun c => c = 0 → _) from H 0 hs' h rfl
  cases hp : Frontend.builtinPreludeE with
  | error x =>
    rcases x with ⟨_ | _ | _, _⟩ <;>
      simp [compareJsonG, hp, clockMs, diagLine]
  | ok pre =>
    simp only [compareJsonG, hp, clockMs, diagLine, outLine, ModelIO.allOk_bind,
      ModelIO.liftIO_iff, forall_eq]
    intro t0 pre' hs1 hpre
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hpre
    obtain ⟨rfl, rfl⟩ := hpre
    intro _ x hs2 hx
    rcases x with e | rC
    · exact fun c hs3 hc h0 => (readFailed_ne c hs3 hc h0).elim
    obtain ⟨bC, hbC, hpC⟩ := parseStreamG_model hx
    simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq]
    intro _ y hs3 hy
    rcases y with e | rS
    · exact fun c hs4 hc h0 => (readFailed_ne c hs4 hc h0).elim
    obtain ⟨bS, hbS, hpS⟩ := parseStreamG_model hy
    simp only
    cases hcmp : compareRecords jsonOwn Declaration.usedConsts
      (jsonHomes (jsonRecs pre' rC.decls)) {} (preparePrelude pre' rS.decls)
      (recIndex (preparePrelude pre' rS.decls)) (jsonRecs pre' rC.decls) with
    | error why =>
      simp only [preparePrelude] at hcmp
      rw [hcmp]
      simp only
      split <;> simp
    | ok p =>
      obtain ⟨ctx, filled⟩ := p
      have hcmp' := hcmp
      simp only [preparePrelude] at hcmp'
      rw [hcmp']
      simp only
      cases hsc : ctxScoped ctx with
      | some why => simp
      | none =>
      simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq]
      intro _ _ _ _ _ _ v
      rcases v with e | ⟨⟨env, henv⟩⟩
      · exact fun c hs6 hc h0 => absurd (verdictG_ok hc h0) (by simp)
      intro _ _ _ _
      exact ⟨pre', bC, rC, bS, rS, ctx, filled, env, rfl, hbC, hpC, hbS, hpS, hcmp, hsc, henv⟩

/-- The arguments `--compare -- <c> <s>`: those two files, every other setting at its default
(the mode `.verified`). -/
theorem parseArgs_compare_json (c s : String) :
    parseArgs ["--compare", "--", c, s] {} = { compare := true, files := #[c, s] } := by
  simp [parseArgs]

/-- The flags of the JSON compare arguments ask for no help. -/
theorem helpWanted_compare_json (c s : String) :
    helpWanted ["--compare", "--", c, s] = false := by
  simp [helpWanted]

/-- **`runArgs` on `--compare -- <c> <s>`, in the model**: every outcome that is an exit 0 is one
of `compareJsonG` on the two files, at the default mode `.verified` and maximum `Nat` size. -/
theorem runArgs_compare_json_run {c s : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--compare", "--", c, s] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ jobs, ModelIO.CanGive (compareJsonG ⟨c, s⟩ .verified Cached.maxNatSizeDefault .off jobs)
      fs 0 := by
  suffices H : ModelIO.AllOk (runArgs ["--compare", "--", c, s]) fs hs
      (fun x => x = 0 → ∃ jobs, ModelIO.CanGive
        (compareJsonG ⟨c, s⟩ .verified Cached.maxNatSizeDefault .off jobs) fs 0) from
    H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [helpWanted_compare_json, parseArgs_compare_json]
    intro x hs₂ hx h0
    subst h0
    simp only [Bool.false_eq_true, ↓reduceIte, Array.isEmpty, List.isEmpty, Bool.not_true,
      Array.size_empty, decide_true, Bool.or_false] at hx
    split at hx
    · simp [eprintln] at hx
    · exact ⟨_, _, _, hx⟩
  · simp

/-- **`runArgs` on `--compare -- <c> <s>`, in the model**: every outcome that is an exit 0 found
the challenge file's bytes and the solution file's in the snapshot, each parsing as one chunk;
the comparison and its order check passed; and `checkDecls .verified` accepts the solution's
records prepared with the built-in prelude. -/
theorem runArgs_compare_json_accept {c s : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--compare", "--", c, s] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre bC rC bS rS ctx filled env, builtinPreludeE = .ok pre ∧
      fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      fs.file s = some bS ∧ parseChunks [bS] = .ok rS ∧
      compareRecords jsonOwn Declaration.usedConsts (jsonHomes (jsonRecs pre rC.decls)) {}
        (preparePrelude pre rS.decls) (recIndex (preparePrelude pre rS.decls))
        (jsonRecs pre rC.decls) = .ok (ctx, filled) ∧
      ctxScoped ctx = none ∧
      checkDecls .verified natOpPinSets Cached.maxNatSizeDefault (preparePrelude pre rS.decls)
        = .ok env := by
  obtain ⟨jobs, _, _, hg⟩ := runArgs_compare_json_run h
  exact compareJsonG_accept hg

end ConLeche.Driver
