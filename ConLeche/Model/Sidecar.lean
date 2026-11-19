module

public import ConLeche.Model.Sidecar.Fold
public import ConLeche.IsModel
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
# A stream checked with a sidecar has a model

The sidecar's accepted fold carries a covered model with the canonical proofs' leaves
(`declsRun_proofs`); renamed to the input's level-parameter names (`renEnv`), it is a model of the
renamed sidecar (`EnvModelM.copyStmt`).  The input's fold with the sidecar then carries a model
(`sideFold`), and the records the fold checked have a model (`isModel_of_envModelM`), which is a
model of the input (`isModel_sideRecords`).
-/

namespace ConLeche.Model.Sidecar

open ConLeche ConLeche.Cached ConLeche.Model ConLeche.Model.Modular ConLeche.Verify
open ConLeche.Semantics SetTheory

universe w

variable {V : Type w} [SetTheory V] {pins : List NatOpPinSet} {maxNatSize : Nat}

/-- **The input's environment, checked with a sidecar, carries a model.** -/
theorem sidecar_envModel {dsS ds : Array Declaration} {envS env : Env}
    (hS : checkDecls .verified pins maxNatSize dsS = .ok envS)
    (hC : checkDecls .verified pins maxNatSize ds (some envS) = .ok env)
    (hsc : ∀ {J : Sidecar} {pd : Declaration} {p q : Nat × FEnv},
      declStep .verified pins maxNatSize (some J) p pd = .ok q →
      p.2 = mkFEnv p.2.env → EnvWF p.2.env → ScopedE p.2.env → ScopedE q.2.env)
    (hsc0 : ScopedE Env.empty) :
    Nonempty (EnvModelM V env) := by
  -- the sidecar's model
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
  let JS : Sidecar := ⟨mkFEnv feS.env, recordMates rs⟩
  have run' : DeclsRun .verified pins maxNatSize (some JS) rs.toList (0, mkFEnv Env.empty) (n, fe) :=
    run
  -- the renamed sidecar's model
  obtain ⟨mS, hac, hcovS⟩ := EnvModelM.copyStmt mS₀ hcovS₀ (renEnv_copies (Ef := env) hndS)
    (renEnv_stmt env feS.env)
  have hNS : NatFacts (renEnv env feS.env) := NatFacts.copies (renEnv_copies hndS) hNS₀
  have hPLS : ProofLeaves V (renEnv env feS.env) mS.base2.acval := by
    rw [hac]; exact ProofLeaves.copies mS₀ (renEnv_copies hndS) hPLS₀
  obtain ⟨mq, -⟩ := sideFold (JS := JS) (envS := feS.env) (Ef := env) rfl mS hcovS hNS hPLS htS
    hsc run' hfe (fun pd hpd block nP he b hb b' hb' => by
      subst he; exact recordMates_spec hpd hb hb') (L := []) rfl rfl List.nodup_nil hsc0
    (EnvModelM.empty V) lfpCover_empty (EnvModelOk.empty (V := V)).2 (fun x hx => nomatch hx)
  exact ⟨mq⟩

/-- **A stream checked with a sidecar has a model**, and declares `False` and `Eq`, where it
declares them at all, as the prelude's. -/
theorem sidecar_isModel {dsS ds : Array Declaration} {envS env : Env}
    (hS : checkDecls .verified pins maxNatSize dsS = .ok envS)
    (hC : checkDecls .verified pins maxNatSize ds (some envS) = .ok env)
    (hsc : ∀ {J : Sidecar} {pd : Declaration} {p q : Nat × FEnv},
      declStep .verified pins maxNatSize (some J) p pd = .ok q →
      p.2 = mkFEnv p.2.env → EnvWF p.2.env → ScopedE p.2.env → ScopedE q.2.env)
    (hsc0 : ScopedE Env.empty) :
    (∃ model, IsModel V model ds.toList) ∧
      (DeclaresName ds.toList falseName → DeclaresFalse ds.toList) ∧
      (DeclaresName ds.toList eqName → DeclaresEq ds.toList) := by
  obtain ⟨m⟩ := sidecar_envModel (V := V) hS hC hsc hsc0
  have hrec := checkDecls_recordsStored hC
  have hstored : ∀ n, DeclaresName ds.toList n → (env.find? n).isSome = true := by
    rintro n ⟨d, hd, c, hc, rfl⟩
    have hd' : sideRecord d ∈ (sideRecords (some envS) ds).toList := by
      simp only [sideRecords, Array.toList_map]; exact List.mem_map_of_mem hd
    obtain ⟨c', hc', hn⟩ : ∃ c' ∈ (sideRecord d).records, c'.name = c.name := by
      rcases records_sideRecord d with h | ⟨cv, v, rfl, h⟩
      · exact ⟨c, h ▸ hc, rfl⟩
      · simp only [Declaration.records, List.mem_singleton] at hc
        subst hc
        exact ⟨.axiomInfo cv, by rw [h]; exact List.mem_singleton_self _, rfl⟩
    obtain ⟨ci, hf, -⟩ := hrec _ hd' c' hc'
    rw [← hn, hf]; rfl
  exact ⟨⟨_, (isModel_sideRecords _ (some envS) ds).mp (isModel_of_envModelM m hrec)⟩,
    fun h => checkDecls_declaresFalse hC (hstored _ h),
    fun h => checkDecls_declaresEq hC (hstored _ h)⟩

end ConLeche.Model.Sidecar
