module

import ConLeche.Verify.Driver.CompareRun
public import ConLeche.Driver.Cli
import ConLeche.Verify.Cached.DeclPushes

/-!
# A lean4export file checked with a solution, in the model

`compareJsonG_accept`: every outcome of `compareJsonG` that is an exit 0 found the challenge
file's bytes `bC` and the solution file's bytes `bS` in the snapshot, each parsing as one chunk;
`checkDecls` accepts the solution's prepared records, at the environment they denote (the
solution `envS`), and the challenge's prepared records with `envS` as their solution.
-/

public section

namespace ConLeche.Driver

open ConLeche Frontend Cached

/-- **An exit 0 of a run with a solution** (see the module docstring). -/
theorem compareJsonG_accept {r : JCmpReq} {mode : CheckMode} {maxNatSize : Nat} {pace : Pace}
    {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (compareJsonG r mode maxNatSize pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre bC rC bS rS env, builtinPreludeE = .ok pre ∧
      fs.file r.challenge = some bC ∧ parseChunks [bC] = .ok rC ∧
      fs.file r.solution = some bS ∧ parseChunks [bS] = .ok rS ∧
      checkDecls mode natOpPinSets maxNatSize (preparePrelude pre rS.decls)
        = .ok (streamEnv (preparePrelude pre rS.decls).toList) ∧
      checkChallenge mode natOpPinSets maxNatSize (preparePrelude pre rS.decls)
        (preparePrelude pre rC.decls) = .ok env := by
  suffices H : ModelIO.AllOk (compareJsonG r mode maxNatSize pace jobs) fs hs
      (fun c => c = 0 → _) from H 0 hs' h rfl
  cases hp : Frontend.builtinPreludeE with
  | error x =>
    rcases x with ⟨_ | _ | _, _⟩ <;>
      simp [compareJsonG, hp, clockMs, diagLine]
  | ok pre =>
    simp only [compareJsonG, hp, clockMs, outLine, ModelIO.allOk_bind,
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
    simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq]
    intro _ _ _ _ _ _ vS
    rcases vS with e | ⟨⟨envS', henvS⟩⟩
    · exact fun c hs6 hc h0 => absurd (verdictG_ok hc h0) (by simp)
    have hS : checkDecls mode natOpPinSets maxNatSize (prepareD pre' rS.decls).decls
        = .ok (streamEnv (prepareD pre' rS.decls).decls.toList) := by
      rw [checkDecls, henvS, checkDecls_env henvS]; rfl
    dsimp only
    simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq]
    intro _ _ _ _ _ _ vC
    rcases vC with e | ⟨⟨envC, henvC⟩⟩
    · exact fun c hs6 hc h0 => absurd (verdictG_ok hc h0) (by simp)
    intro _ _ _ _
    rw [checkDecls_sideRecords] at henvC
    exact ⟨pre', bC, rC, bS, rS, envC, rfl, hbC, hpC, hbS, hpS, hS, henvC⟩

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
`checkDecls .verified` accepts the solution's records prepared with the built-in prelude, at the
environment they denote, and the challenge's with that environment as their solution. -/
theorem runArgs_compare_json_accept {c s : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--compare", "--", c, s] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre bC rC bS rS env, builtinPreludeE = .ok pre ∧
      fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      fs.file s = some bS ∧ parseChunks [bS] = .ok rS ∧
      checkDecls .verified natOpPinSets Cached.maxNatSizeDefault (preparePrelude pre rS.decls)
        = .ok (streamEnv (preparePrelude pre rS.decls).toList) ∧
      checkChallenge .verified natOpPinSets Cached.maxNatSizeDefault
        (preparePrelude pre rS.decls) (preparePrelude pre rC.decls) = .ok env := by
  obtain ⟨jobs, _, _, hg⟩ := runArgs_compare_json_run h
  exact compareJsonG_accept hg

end ConLeche.Driver
