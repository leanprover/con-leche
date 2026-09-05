import Setlec.SetBase.DeclDirect
import Setlec.SetBase.IndBlockRun
import Setlec.SetBase.DeclEta
import Setlec.Verify.Extend.Inversions
import Setlec.Verify.ProjPinInv

/-!
# The direct-structure declaration keeps the η-families closed (task #175 wiring, W5)

The declaration fold's η half at the `.indDecl` dispatch: the modeled
arm is `declIndEtaClosedRun` (`IndBlockRun`), and the direct arm is
proved here from `DeclDirectR`'s recorded runs — every store the
direct install performs is a **fresh cons** (`checkConstantVal`'s
duplicate guard for the three constants, `checkDirectProj`'s own
`isNone` guard for the entries), and the one former it stores carries
`directCaps`, whose `eta` slot is a literal `false`, so
`EtaFamiliesClosed.cons_nonind` applies at every step.

With this the two dispatch lemmas below make the fold's η half
**flag-agnostic**: `declStepPM` (`SetP/FoldP`) and `declEtaStep` read
the kernel's own `directParts?` dispatch and no longer consult
`directStructsEnabled` through `declIndRunDispatchR_eq_ind`.
-/

namespace Setlec.SetR

open Setlec (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  DirectParts fueledOps checkDirectInd checkDirectCtor checkConstantVal
  checkDirectProj projFnName directCaps EtaFamiliesClosed ProjEntry)

/-! ## The stage shapes, with their freshness guards -/

/-- A thrown step never succeeds. -/
theorem throw_ne_ok {α : Type} {e : Setlec.CheckError} {a : α}
    (h : (throw e : Setlec.CheckM α) = .ok a) : False := by
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
    (h : checkDirectInd (m := Setlec.CheckM) (fueledOps μ F) env p
      = .ok (envI, cvTa)) :
    ∃ cv : ConstantVal,
      checkConstantVal (m := Setlec.CheckM) (fueledOps μ F) env p.cvT = .ok cv ∧
      cvTa = cv ∧ envI = ⟨.indInfo cv (directCaps p) :: env.consts⟩ := by
  unfold checkDirectInd at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := Setlec.exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨_, by assumption, rfl, rfl⟩)
    | close_throw

/-- Stage 2 conses the annotated constructor. -/
theorem checkDirectCtor_inv {μ : CheckMode} {F : Nat} {env₀ env envC : Env}
    {p : DirectParts} {cvTa cvCa : ConstantVal}
    (h : checkDirectCtor (m := Setlec.CheckM) (fueledOps μ F) env₀ env p cvTa
      = .ok (envC, cvCa)) :
    ∃ cv : ConstantVal,
      checkConstantVal (m := Setlec.CheckM) (fueledOps μ F) env p.cvC = .ok cv ∧
      cvCa = cv ∧ envC = ⟨.ctorInfo cv p.nP p.nF :: env.consts⟩ := by
  unfold checkDirectCtor at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := Setlec.exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨_, by assumption, rfl, rfl⟩)
    | close_throw

/-- A projection slot's run: either no entry (the O4 else-branch) or a
tower entry consed at a fresh slot.  The freshness is the slot guard's
own surviving branch. -/
theorem checkDirectProj_inv {μ : CheckMode} {F : Nat} {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {cvTa cvCa : ConstantVal} {env env' : Env} {i : Nat}
    (h : checkDirectProj (m := Setlec.CheckM) (fueledOps μ F) T C lps nP nF
      resSort cvTa cvCa env i = .ok env') :
    env' = env ∨
      ∃ entry : ProjEntry, env.find? (projFnName T i) = none ∧
        entry.tower = true ∧ entry.native = true ∧
        entry.structName = T ∧ entry.idx = i ∧ entry.ctor = C ∧
        entry.numParams = nP ∧ entry.numFields = nF ∧
        entry.levelParams = lps ∧
        env' = ⟨.projInfo entry :: env.consts⟩ := by
  unfold checkDirectProj at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := Setlec.exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq] at h
       first
         | exact Or.inl h.symm
         | (refine Or.inr ⟨_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.symm⟩
            first
              | assumption
              | exact Option.isNone_iff_eq_none.mp (by assumption)))
    | close_throw

/-! ## The η half of the direct arm -/

/-- The projection-slot fold keeps the η-families closed: every step
is a fresh cons of a table entry, or nothing. -/
theorem directProjFoldR_etaClosed {μ : CheckMode} {F : Nat} {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {cvTa cvCa : ConstantVal} :
    ∀ (idxs : List Nat) {env env₂ : Env},
      DirectProjFoldR μ F T C lps nP nF resSort cvTa cvCa env idxs env₂ →
      EtaFamiliesClosed env → EtaFamiliesClosed env₂
  | [], _, _, h, hE => by rw [h]; exact hE
  | i :: rest, env, env₂, h, hE => by
    obtain ⟨env'', hstep, hrest⟩ := h
    refine directProjFoldR_etaClosed rest hrest ?_
    rcases checkDirectProj_inv hstep with rfl | ⟨entry, hfresh, -, -, hsn, hidx, -, -, -, -, rfl⟩
    · exact hE
    · refine EtaFamiliesClosed.cons_nonind hE ?_ (fun _ _ heq => nomatch heq)
      have hname : (ConstantInfo.projInfo entry).name = projFnName T i := by
        show projFnName entry.structName entry.idx = projFnName T i
        rw [hsn, hidx]
      rw [hname]; exact hfresh

/-- **The direct arm keeps the η-families closed.** -/
theorem declDirectR_etaClosed {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectParts} (hE : EtaFamiliesClosed env)
    (h : DeclDirectR μ F env p env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨cvTa, cvCa, cvRa, rhsA, envI, envC, hInd, hCtor, hCV, -, -, -,
    hfold⟩ := h
  obtain ⟨cvT', hcvT, -, hI⟩ := checkDirectInd_inv hInd
  obtain ⟨hfT, -, -, -, -, -, _, _, _, -, -, -, -, -, hTeq⟩ :=
    Setlec.checkConstantVal_inv hcvT
  obtain ⟨cvC', hcvC, -, hC⟩ := checkDirectCtor_inv hCtor
  obtain ⟨hfC, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
    Setlec.checkConstantVal_inv hcvC
  obtain ⟨hfR, -, -, -, -, -, _, _, _, -, -, -, -, -, hReq⟩ :=
    Setlec.checkConstantVal_inv hCV
  have hnT : cvT'.name = p.cvT.name := by rw [hTeq]
  have hnC : cvC'.name = p.cvC.name := by rw [hCeq]
  have hnR : cvRa.name = p.cvR.name := by rw [hReq]
  have hE₁ : EtaFamiliesClosed envI := by
    rw [hI]
    exact EtaFamiliesClosed.cons_nonind hE
      (show env.find? cvT'.name = none by rw [hnT]; exact hfT)
      (fun cv caps heq hcape => by
        obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
        simp [Setlec.directCaps] at hcape)
  have hE₂ : EtaFamiliesClosed envC := by
    rw [hC]
    exact EtaFamiliesClosed.cons_nonind hE₁
      (show envI.find? cvC'.name = none by rw [hnC]; exact hfC)
      (fun _ _ heq => nomatch heq)
  refine directProjFoldR_etaClosed _ hfold ?_
  exact EtaFamiliesClosed.cons_nonind hE₂
    (show envC.find? cvRa.name = none by rw [hnR]; exact hfR)
    (fun _ _ heq => nomatch heq)

/-! ## The dispatch, flag-agnostic -/

/-- The `.indDecl` run dispatch keeps the η-families closed, by the
kernel's own `directParts?` case split. -/
theorem declIndRunDispatchEtaClosed {μ : CheckMode} {F : Nat}
    {env envI : Env} {block : List ConstantInfo}
    (hE : EtaFamiliesClosed env)
    (h : DeclIndRunDispatchR μ F env block envI) : EtaFamiliesClosed envI := by
  unfold DeclIndRunDispatchR at h
  split at h
  · exact declDirectR_etaClosed hE h
  · exact declIndEtaClosedRun hE h

/-- The `.indDecl` dispatch (relation level), likewise. -/
theorem declIndDispatchEtaClosed {μ : CheckMode} {F : Nat}
    {env envI : Env} {cval : Setlec.TTVerify.TConstVal}
    {block : List ConstantInfo}
    (hE : EtaFamiliesClosed env)
    (h : DeclIndDispatchR μ F env cval block envI) : EtaFamiliesClosed envI := by
  unfold DeclIndDispatchR at h
  split at h
  · exact declDirectR_etaClosed hE h
  · exact declIndEtaClosed hE h

/-- **The declaration fold's η-closure half**, `DeclR` instance
(relocated from `DeclEta` at W5, where it read the flag through
`declIndDispatchR_eq_ind`; now the dispatch's own case split). -/
theorem declEtaStep {μ : CheckMode} {F : Nat}
    {cval : Setlec.TTVerify.TConstVal}
    {env : Env} {d : Setlec.Declaration} {env₂ : Env}
    (hE : EtaFamiliesClosed env)
    (h : DeclR μ F cval env d env₂) : EtaFamiliesClosed env₂ :=
  declEtaStepRun (fun hb => declIndDispatchEtaClosed hE hb) hE
    (DeclR.toRun h)

end Setlec.SetR
