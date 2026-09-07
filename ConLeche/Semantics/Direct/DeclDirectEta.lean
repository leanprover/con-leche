import ConLeche.Semantics.Direct.DeclDirect
import ConLeche.Semantics.IndBlockRun
import ConLeche.Semantics.DeclEta
import ConLeche.Verify.Extend.Inversions

import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Direct.DirectInv

/-!
# The direct-structure declaration keeps the η-families closed (task #175 wiring, W5)

The declaration fold's η half at the `.indDecl` dispatch: the modeled
arm is `declIndEtaClosedRun` (`IndBlockRun`), and the direct arm is
proved here from `DeclDirectRun`'s recorded runs — every store the
direct install performs is a **fresh cons** (`checkConstantVal`'s
duplicate guard for the three constants, `checkDirectProj`'s own
`isNone` guard for the entries), and the one former it stores carries
`directCaps`, whose `eta` slot is a literal `false`, so
`EtaFamiliesClosed.cons_nonind` applies at every step.

With this the two dispatch lemmas below make the fold's η half
**flag-agnostic**: `declStepPM` (`SetP/FoldP`) and `declEtaStep` read
the kernel's own `directParts?` dispatch and no longer consult
the former master switch (gone at W4c).
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  DirectParts fueledOps checkDirectInd checkDirectCtor checkConstantVal
  checkDirectProjTable projTableName directCaps EtaFamiliesClosed ProjEntry)

/-! ## The stage shapes, with their freshness guards -/

/-- A thrown step never succeeds. -/
theorem throw_ne_ok {α : Type} {e : ConLeche.CheckError} {a : α}
    (h : (throw e : ConLeche.CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The shape walk's closers, shared by the three stage inversions:
the surviving `pure` (after the join point's zeta step) hands the
result over; every other goal holds a `throw … = .ok _`. -/
local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact throw_ne_ok (by assumption))
        | (exfalso; exact throw_ne_ok (by simpa [bind, Except.bind] using ‹_›)))

/-- Stage 1 conses the annotated former (`checkConstantVal`'s
output).  Stated with the run existential — the shape walk's `split`
re-introduces the bound constant anonymously, so its guards
(`checkConstantVal_inv`) are read off the run afterwards. -/
theorem checkDirectInd_inv {μ : CheckMode} {F : Nat} {env envI : Env}
    {p : DirectParts} {cvTa : ConstantVal}
    (h : checkDirectInd (m := ConLeche.CheckM) (fueledOps μ F) env p
      = .ok (envI, cvTa)) :
    ∃ cv : ConstantVal,
      checkConstantVal (m := ConLeche.CheckM) (fueledOps μ F) env p.cvT = .ok cv ∧
      cvTa = cv ∧ envI = ⟨.indInfo cv (directCaps p) :: env.consts⟩ := by
  unfold checkDirectInd at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨_, by assumption, rfl, rfl⟩)
    | close_throw

/-- Stage 2 conses the annotated constructor. -/
theorem checkDirectCtor_inv {μ : CheckMode} {F : Nat} {env₀ env envC : Env}
    {p : DirectParts} {cvTa cvCa : ConstantVal} {sorts : List Level}
    (h : checkDirectCtor (m := ConLeche.CheckM) (fueledOps μ F) env₀ env p cvTa
      = .ok (envC, cvCa, sorts)) :
    ∃ cv : ConstantVal,
      checkConstantVal (m := ConLeche.CheckM) (fueledOps μ F) env p.cvC = .ok cv ∧
      cvCa = cv ∧ envC = ⟨.ctorInfo cv p.nP p.nF :: env.consts⟩ := by
  unfold checkDirectCtor at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       exact ⟨_, by assumption, rfl, rfl⟩)
    | close_throw

/-- Stage 3 admits the stream's recursor by the ordinary constant check
and conses the *generated* recursor at the stream's name and level
parameters (task #175 S2). -/
theorem checkDirectRec_inv {μ : CheckMode} {F : Nat} {env : Env}
    {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr}
    (h : checkDirectRec (m := ConLeche.CheckM) (fueledOps μ F) env p cvTa cvCa
      = .ok (cvRa, rhsA)) :
    ∃ cv : ConstantVal,
      checkConstantVal (m := ConLeche.CheckM) (fueledOps μ F) env p.cvR = .ok cv ∧
      cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams := by
  unfold checkDirectRec at h
  obtain ⟨cvRi, hcv, h⟩ := ConLeche.exceptBind_ok h
  repeat' first
    | (obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h)
    | split at h
    | (dsimp only at h)
  all_goals first
    | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨cvRi, hcv, rfl, rfl⟩)
    | close_throw

/-- The table stage's run: the tower table consed at a fresh table
name (task #175 S1). -/
theorem checkDirectProjTable_shape {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {cvCa : ConstantVal} {env env' : Env}
    (h : checkDirectProjTable (m := ConLeche.CheckM) T C lps nP nF
      resSort guards cvCa env = .ok env') :
    ∃ tbl : ConLeche.ProjTable, env.find? (projTableName T) = none ∧
      tbl.structName = T ∧ env' = ⟨.projInfo tbl :: env.consts⟩ := by
  obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := ConLeche.checkDirectProjTable_inv h
  exact ⟨_, hfresh, rfl, rfl⟩

/-! ## The η half of the direct arm -/

/-- The table stage keeps the η-families closed: a fresh cons of a
table. -/
theorem checkDirectProjTable_etaClosed {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {cvCa : ConstantVal} {env env₂ : Env}
    (h : checkDirectProjTable (m := ConLeche.CheckM) T C lps nP nF
      resSort guards cvCa env = .ok env₂)
    (hE : EtaFamiliesClosed env) : EtaFamiliesClosed env₂ := by
  obtain ⟨tbl, hfresh, hsn, rfl⟩ := checkDirectProjTable_shape h
  refine EtaFamiliesClosed.cons_nonind hE ?_ (fun _ _ heq => nomatch heq)
  show env.find? (projTableName tbl.structName) = none
  rw [hsn]; exact hfresh

/-- **The direct arm keeps the η-families closed.** -/
theorem declDirectRun_etaClosed {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectParts} (hE : EtaFamiliesClosed env)
    (h : DeclDirectRun μ F env p env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨cvTa, cvCa, cvRa, sorts, rhsA, envI, envC, hInd, hCtor, hRec,
    hfold⟩ := h
  obtain ⟨cvT', hcvT, -, hI⟩ := checkDirectInd_inv hInd
  obtain ⟨hfT, -, -, -, -, -, _, _, _, -, -, -, -, -, hTeq⟩ :=
    ConLeche.checkConstantVal_inv hcvT
  obtain ⟨cvC', hcvC, -, hC⟩ := checkDirectCtor_inv hCtor
  obtain ⟨hfC, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
    ConLeche.checkConstantVal_inv hcvC
  obtain ⟨cvRi, hCV, hnR, -⟩ := checkDirectRec_inv hRec
  obtain ⟨hfR, -, -, -, -, -, _, _, _, -, -, -, -, -, -⟩ :=
    ConLeche.checkConstantVal_inv hCV
  have hnT : cvT'.name = p.cvT.name := by rw [hTeq]
  have hnC : cvC'.name = p.cvC.name := by rw [hCeq]
  -- the former claims eta (`directCaps`, task #175 W4c), so the family
  -- is closed only once its constructor is consed: at `envC` the new
  -- former's constructor is the head, and every prefix family keeps
  -- its constructor through the two fresh conses
  have hE₂ : EtaFamiliesClosed envC := by
    rw [hC, hI]
    intro T'' cvT'' caps hf he hr
    rw [ConLeche.Env.find?_cons] at hf
    split at hf
    · exact nomatch (Option.some.inj hf)
    · rw [ConLeche.Env.find?_cons] at hf
      split at hf
      · obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
        refine ⟨cvC', ?_⟩
        show Env.find? ⟨.ctorInfo cvC' p.nP p.nF :: _⟩ p.cvC.name
          = some (.ctorInfo cvC' p.nP p.nF)
        rw [← hnC]
        exact ConLeche.Env.find?_cons_self _ _
      · obtain ⟨cvC, hfC'⟩ := hE T'' cvT'' caps hf he hr
        refine ⟨cvC, ?_⟩
        exact ConLeche.Env.find?_cons_of_fresh
          (show Env.find? ⟨.indInfo cvT' (directCaps p) :: env.consts⟩
              cvC'.name = none by rw [← hI, hnC]; exact hfC)
          (ConLeche.Env.find?_cons_of_fresh
            (show env.find? cvT'.name = none by rw [hnT]; exact hfT) hfC')
  refine checkDirectProjTable_etaClosed hfold ?_
  exact EtaFamiliesClosed.cons_nonind hE₂
    (show envC.find? cvRa.name = none by rw [hnR]; exact hfR)
    (fun _ _ heq => nomatch heq)

end ConLeche.Semantics
