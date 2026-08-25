import Setlec.Model.ConsistencyS
import Setlec.Verify.BracketB4

/-!
# Consistency of the parsed-index executable checker (task #78)

The binary runs `checkDeclsSP`: the frontend parses the export tables
directly into an arena (`Setlec/Frontend/Export.lean`), declarations
arrive as `DeclP` records carrying arena indices, and the whole
declaration fold shares one interned state seeded from the parse store.

The seam to the spec: the parse arena arrives *well-formed by
construction* (`WFStore`, task #103 — canonicity `EStore.WF` is the
bundle's `wf` field, established per record by the frontend's checked
interns), each declaration's indices are
validated in range (denotations then exist, `denoteDeclP_total`), and
the per-declaration walk (`checkDeclSP_sim`, `Setlec/Verify/BridgeP.lean`
for the non-inductive branches; the inductive/basis branches are the
shared drivers verbatim, `checkIndDeclSF_run`) reproduces a successful
step by the pure fueled `checkDecl` **on the denoted declaration** —
the identification of the parsed input with the spec object the
consistency statements quantify over.  The fold then interleaves
exactly as in `Setlec/Model/ConsistencyS.lean`: the current model
supplies `EnvWF`, the bridge supplies the pure run, `checkDecl_sound`
supplies the next model; the environment-free residue `ISOKF` and the
arena extension thread the persistent state across declarations.
-/

namespace Setlec

open EStore Expr

/-- A successful step validated its indices. -/
private theorem checkDeclSPStep_inRange {n0 : Nat} {fe : FEnv}
    {pd : DeclP} {s₀ : IState} {fe' : FEnv} {s' : IState}
    (h : checkDeclSPStep n0 fe pd s₀ = .ok (fe', s')) :
    pd.inRangeB n0 = true := by
  unfold checkDeclSPStep at h
  by_cases hin : pd.inRangeB n0 = true
  · exact hin
  · rw [if_neg hin] at h
    exact absurd h (fun h => nomatch h)

/-- One step of the parsed fold: a successful run from a residue state
is reproduced by the pure fueled checker on the denoted declaration,
and the residue and arena extension thread to the next step. -/
theorem checkDeclSPStep_run {env : Env} (henv : EnvWF env) {pd : DeclP}
    {d : Declaration} {n0 : Nat} {s₀ : IState} (hres : ISOKF s₀)
    (hden : denoteDeclP s₀.store pd = some d)
    {fe' : FEnv} {s' : IState}
    (h : checkDeclSPStep n0 (mkFEnv env) pd s₀ = .ok (fe', s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
    ∃ F, checkDecl (fueledOps F) env d = .ok fe'.env := by
  unfold checkDeclSPStep at h
  by_cases hin : pd.inRangeB n0 = true
  case neg =>
    rw [if_neg hin] at h
    exact absurd h (fun h => nomatch h)
  rw [if_pos hin] at h
  obtain ⟨u, s₁, hflush, h⟩ := bindI_ok h
  rw [flushS_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hisok : ISOK env s₀.flushed := flushS_isok hres
  have hden' : denoteDeclP s₀.flushed.store pd = some d := hden
  have main : (∀ block, pd ≠ .indDecl block) →
      ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
      ∃ F, checkDecl (fueledOps F) env d = .ok fe'.env := by
    intro hind
    obtain ⟨hs', hext, v, ⟨henvEq, hmk⟩, F, hF⟩ :=
      (checkDeclSP_sim henv hisok hres.wf.tier_off hden' hind) fe' s' h
    refine ⟨hs'.residue (tierOffE hext hres.wf.tier_off), hext, hmk,
      F, ?_⟩
    rw [← checkDecl_datF, henvEq]
    exact hF
  cases pd with
  | indDecl block =>
    obtain rfl : Declaration.indDecl block = d := by
      simpa [denoteDeclP] using hden'
    have hrun : (match directPartsF? (mkFEnv env) block with
        | some p => checkDirectStructS (mkFEnv env) p
        | none => checkIndDeclSF (mkFEnv env) block) s₀.flushed =
        .ok (fe', s') := h
    obtain ⟨hres', hext, hfe, F, hF⟩ :=
      checkIndOrDirectSF_run henv (hisok.residue hres.wf.tier_off) hrun
    exact ⟨hres', hext, hfe, F, hF⟩
  | defnDecl cv value hint => exact main (fun _ h => DeclP.noConfusion h)
  | thmDecl cv value => exact main (fun _ h => DeclP.noConfusion h)
  | opaqueDecl cv value => exact main (fun _ h => DeclP.noConfusion h)
  | axiomDecl cv => exact main (fun _ h => DeclP.noConfusion h)
  | basisDecl kind => exact main (fun _ h => DeclP.noConfusion h)

/-- The parsed-declaration fold preserves having a model. -/
private theorem foldSP {V : Type u} [SetTheory V] {st0 : EStore}
    (hwfst : st0.WF) :
    ∀ (pds : List DeclP) (fe : FEnv) {fe' : FEnv} {s₀ s' : IState},
      fe = mkFEnv fe.env →
      Nonempty (EnvModel V fe.env) →
      EtaFamiliesClosed fe.env →
      ISOKF s₀ → Ext st0 s₀.store →
      (pds.foldlM (checkDeclSPStep (st0.nodes.size + st0.nodes.size)) fe) s₀ =
        .ok (fe', s') →
      Nonempty (EnvModel V fe'.env)
  | [], fe, fe', s₀, s', _, hm, _, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact hm
  | pd :: pds, fe, fe', s₀, s', hfe, hm, hE1, hres, hext0, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨m⟩ := hm
    obtain ⟨d, hd0⟩ := denoteDeclP_total hwfst
      (checkDeclSPStep_inRange hstep)
    have hd : denoteDeclP s₀.store pd = some d :=
      denoteDeclP_mono hwfst hext0 hd0
    rw [hfe] at hstep
    obtain ⟨hres₁, hext₁, hfe₁, F, hF⟩ :=
      checkDeclSPStep_run m.wf hres hd hstep
    obtain ⟨hm1, hE1'⟩ := checkDecl_sound hF m hE1
    exact foldSP hwfst pds fe₁ hfe₁ hm1 hE1' hres₁
      (hext0.trans hext₁) h

/-- Soundness of the **parsed-index executable** checker: every
environment it accepts has a set-theoretic model. -/
theorem checkDeclsSP_sound (V : Type u) [SetTheory V]
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP st pds = .ok env') :
    Nonempty (EnvModel V env') := by
  unfold checkDeclsSP at h
  simp only [Bind.bind, Except.bind] at h
  have hwf : st.raw.WF := st.wf
  cases hf : (pds.foldlM (checkDeclSPStep (st.raw.nodes.size + st.raw.nodes.size))
      (mkFEnv Env.empty)).run' { store := st.raw } with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    simp only [StateT.run'] at hf
    cases hrun : (pds.foldlM (checkDeclSPStep (st.raw.nodes.size + st.raw.nodes.size))
        (mkFEnv Env.empty)) { store := st.raw } with
    | error e =>
      rw [hrun] at hf
      exact nomatch hf
    | ok pr =>
      obtain ⟨feO, sO⟩ := pr
      rw [hrun] at hf
      simp only [Functor.map, Except.map, Except.ok.injEq] at hf
      subst hf
      exact foldSP hwf pds (mkFEnv Env.empty) rfl
        ⟨EnvModel.empty V⟩ EtaFamiliesClosed.empty (ISOKF.fresh hwf)
        (Ext.refl _) hrun

/-- **No proof of `Empty` is ever accepted by the parsed-index
executable checker**: if it accepts, no constant in the resulting
environment has type `Empty`. -/
theorem no_proof_of_Empty_SP (V : Type u) [SetTheory V]
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP st pds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSP_sound V h
  exact no_constant_of_Empty m c hc hty

/-- The parsed-index executable never accepts an input stream
containing a `def` or `theorem` record whose stated (parsed) type
denotes `Empty` — the stream-level statement, with the parsed-index ↦
expression identification through the parse store's denotation. -/
theorem no_proof_of_Empty_input_SP (V : Type u) [SetTheory V]
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP st pds = .ok env')
    {cvp : ConstantValP} {value : EIdx}
    (hd : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
      DeclP.thmDecl cvp value ∈ pds)
    (hty : st.denote cvp.type = some (.const emptyName [])) : False := by
  -- expose the raw-store denotation (`WFStore.denote` is the abbrev)
  replace hty : st.raw.denote cvp.type = some (.const emptyName []) := hty
  unfold checkDeclsSP at h
  have hwf : st.raw.WF := st.wf
  simp only [Bind.bind, Except.bind, StateT.run'] at h
  cases hrun : (pds.foldlM (checkDeclSPStep (st.raw.nodes.size + st.raw.nodes.size))
      (mkFEnv Env.empty)) { store := st.raw } with
  | error e =>
    rw [hrun] at h
    exact nomatch h
  | ok pr =>
    clear h
    obtain ⟨feO, sO⟩ := pr
    suffices hgen : ∀ (pds : List DeclP) (fe : FEnv) {fe' : FEnv}
        {s₀ s' : IState},
        fe = mkFEnv fe.env →
        Nonempty (EnvModel V fe.env) →
        EtaFamiliesClosed fe.env →
        ISOKF s₀ → Ext st.raw s₀.store →
        (pds.foldlM (checkDeclSPStep (st.raw.nodes.size + st.raw.nodes.size)) fe) s₀ =
          .ok (fe', s') →
        ((∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds) → False by
      exact hgen pds (mkFEnv Env.empty) rfl ⟨EnvModel.empty V⟩
        EtaFamiliesClosed.empty (ISOKF.fresh hwf) (Ext.refl _) hrun hd
    clear hrun hd
    intro pds
    induction pds with
    | nil =>
      intro fe fe' s₀ s' _ _ _ _ _ _ hd
      rcases hd with ⟨_, hd⟩ | hd <;> cases hd
    | cons pd pds ih =>
      intro fe fe' s₀ s' hfe hm hE1 hres hext0 h hd
      rw [List.foldlM_cons] at h
      obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
      obtain ⟨m⟩ := hm
      obtain ⟨d, hd0⟩ := denoteDeclP_total hwf
        (checkDeclSPStep_inRange hstep)
      have hden : denoteDeclP s₀.store pd = some d :=
        denoteDeclP_mono hwf hext0 hd0
      rw [hfe] at hstep
      obtain ⟨hres₁, hext₁, hfe₁, F, hF⟩ :=
        checkDeclSPStep_run m.wf hres hden hstep
      by_cases hdis : (∃ hint, pd = DeclP.defnDecl cvp value hint) ∨
          pd = DeclP.thmDecl cvp value
      · -- this record is the culprit: its denotation is a spec
        -- declaration whose stated type is `Empty`
        have hdd : ∃ ve, (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve hint) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve := by
          rcases hdis with ⟨hint, rfl⟩ | rfl
          · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
              Option.map_eq_some_iff] at hd0
            obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
            rw [hty] at hty'
            cases hty'
            exact ⟨ve, .inl ⟨hint, rfl⟩⟩
          · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
              Option.map_eq_some_iff] at hd0
            obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
            rw [hty] at hty'
            cases hty'
            exact ⟨ve, .inr rfl⟩
        obtain ⟨ve, hdd⟩ := hdd
        have hfin : ((d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                (.regular 0) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve) ∨
            (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve hint)) →
            False := by
          intro hcase
          have hstores : ∃ type, annotateCore fe.env F 0
                (.const emptyName []) = .ok type ∧
              ∃ c, c ∈ fe₁.env.consts ∧ c.toConstantVal =
                ⟨cvp.name, cvp.levelParams, type⟩ := by
            rcases hcase with hdis' | ⟨hint, hdis'⟩
            · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis'
              exact ⟨type, hann, c, hc, hcv⟩
            · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF
                (Or.inl hdis')
              exact ⟨type, hann, c, hc, hcv⟩
          obtain ⟨type, hann, c, hc, hcv⟩ := hstores
          obtain rfl : Expr.const emptyName [] = type := by
            have h1 : annotateCore fe.env F 0 (.const emptyName []) =
                .ok type := hann
            cases F with
            | zero =>
              rw [annotateCore_zero] at h1
              simp [throw, throwThe, MonadExceptOf.throw] at h1
            | succ F' =>
              rw [annotateCore_succ] at h1
              simpa [annotateBody, pure, Except.pure] using h1
          obtain ⟨⟨m1⟩, -⟩ := checkDecl_sound hF m hE1
          exact no_constant_of_Empty m1 c hc (by rw [hcv])
        rcases hdd with ⟨hint, rfl⟩ | rfl
        · exact hfin (.inr ⟨hint, rfl⟩)
        · exact hfin (.inl (.inr rfl))
      · have hd' : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
            DeclP.thmDecl cvp value ∈ pds := by
          rcases hd with ⟨hint, hdm⟩ | hdm
          · rcases List.mem_cons.mp hdm with heq | hmem
            · exact absurd (.inl ⟨hint, heq.symm⟩) hdis
            · exact .inl ⟨hint, hmem⟩
          · rcases List.mem_cons.mp hdm with heq | hmem
            · exact absurd (.inr heq.symm) hdis
            · exact .inr hmem
        obtain ⟨hm1, hE1'⟩ := checkDecl_sound hF m hE1
        exact ih fe₁ hfe₁ hm1 hE1' hres₁
          (hext0.trans hext₁) h hd'

end Setlec
