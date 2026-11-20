module

public import ConLeche.Model.Solution.Fold
import ConLeche.IsModel
import ConLeche.Model.Modular.Step
import ConLeche.Model.Modular.Valid
import ConLeche.Model.IsModelBridge
import ConLeche.Verify.IsModelSide
import ConLeche.Verify.IsModelRecords
import ConLeche.Verify.Cached.Mates
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.DeclPushes

public section

/-!
# A stream checked with a solution has a model

The solution's accepted fold carries a covered model with the canonical proofs' leaves
(`declsRun_proofs`); renamed to the input's level-parameter names (`renEnv`), it is a model of the
renamed solution (`EnvModelM.copyStmt`).  The input's fold with the solution then carries a model
(`sideFold`), and the records the fold checked have a model (`isModel_of_envModelM`), which is a
model of the input (`isModel_sideRecords`).
-/

namespace ConLeche.Model.Solution

open ConLeche ConLeche.Cached ConLeche.Model ConLeche.Model.Modular ConLeche.Verify
open ConLeche.Semantics SetTheory

universe w

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet} {maxNatSize : Nat}

/-- **The input's environment, checked with a solution, carries a model.** -/
theorem solution_envModel {dsS ds : Array Declaration} {envS env : Env}
    (hS : checkDecls .verified pins maxNatSize dsS = .ok envS)
    (hC : checkDeclsWith .verified pins maxNatSize ds (some envS) = .ok env) :
    Nonempty (EnvModelM V env) := by
  -- the solution's model
  obtain ⟨nS, feS, runS, hfeS⟩ := checkDecls_run .verified hS
  have runS' : DeclsRun .verified pins maxNatSize none (sideRecords none dsS).toList
      (0, mkFEnv Env.empty) (nS, feS) := runS
  obtain ⟨mS₀, -, hcovS₀, hNS₀, hPLS₀⟩ := declsRun_proofs (V := V) runS' rfl (EnvModelM.empty V)
    lfpCover_empty (EnvModelOk.empty (V := V)).2 (ProofLeaves.empty (V := V) _)
  subst hfeS
  have hchS := declsRun_chain .verified runS (PushChain.refl Env.empty)
  have hndS : NodupNames feS.env := hchS.2.2.1 List.nodup_nil
  have hfeS.env : feS.env = streamEnv (sideRecords none dsS).toList := by
    rw [declsRun_env .verified runS]; rfl
  have htS : ∀ t ∈ feS.env.tables, feS.env.findTable? t.structName = some t ∧
      ∃ cv caps, feS.env.find? t.structName = some (.indInfo cv caps) := by
    rw [hfeS.env]; exact fun t ht => stream_tables_mem (hfeS.env ▸ hndS) ht
  -- the input's run
  obtain ⟨n, fe, run, hfe⟩ := checkDecls_run .verified hC
  let rs := sideRecords (some feS.env) ds
  let JS : Solution := ⟨mkFEnv feS.env, recordMates rs⟩
  have run' : DeclsRun .verified pins maxNatSize (some JS) rs.toList (0, mkFEnv Env.empty) (n, fe) :=
    run
  -- the renamed solution's model
  obtain ⟨mS, hac, hcovS⟩ := EnvModelM.copyStmt mS₀ hcovS₀ (renEnv_copies (Ef := env) hndS)
    (renEnv_stmt env feS.env)
  have hNS : NatFacts (renEnv env feS.env) := NatFacts.copies (renEnv_copies hndS) hNS₀
  have hPLS : ProofLeaves V (renEnv env feS.env) mS.base2.acval := by
    rw [hac]; exact ProofLeaves.copies mS₀ (renEnv_copies hndS) hPLS₀
  obtain ⟨mq, -⟩ := sideFold (JS := JS) (envS := feS.env) (Ef := env) rfl mS hcovS hNS hPLS htS
    run' hfe (fun pd hpd block nP he b hb b' hb' => by
      subst he; exact recordMates_spec hpd hb hb') (L := []) rfl rfl List.nodup_nil Scoped.empty
    (EnvModelM.empty V) lfpCover_empty (EnvModelOk.empty (V := V)).2 (fun x hx => nomatch hx)
  exact ⟨mq⟩

/-- **A stream checked with a solution has a model.** -/
theorem solution_isModel {dsS ds : Array Declaration} {envS env : Env}
    (hS : checkDecls .verified pins maxNatSize dsS = .ok envS)
    (hC : checkDeclsWith .verified pins maxNatSize ds (some envS) = .ok env) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) := by
  obtain ⟨m⟩ := solution_envModel (V := V) hS hC
  exact ⟨_, (isModel_sideRecords _ (some envS) ds).mp
    (isModel_of_envModelM m (checkDecls_recordsStored hC))⟩

/-- **A challenge checked with an accepted solution has a model** (`checkChallenge`). -/
theorem challenge_isModel {dsS ds : Array Declaration}
    (solution : (checkDecls .verified pins maxNatSize dsS).isOk)
    (challenge : (checkChallenge .verified pins maxNatSize dsS ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) := by
  cases hS : checkDecls .verified pins maxNatSize dsS with
  | error e => rw [hS] at solution; cases solution
  | ok envS =>
    cases hC : checkChallenge .verified pins maxNatSize dsS ds with
    | error e => rw [hC] at challenge; cases challenge
    | ok env =>
      have henv : envS = streamEnv dsS.toList := checkDecls_env hS
      subst henv
      exact solution_isModel hS hC

end ConLeche.Model.Solution
