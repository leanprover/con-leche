import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Direct.DirectWF
import ConLeche.Verify.Direct.DirectResid
import ConLeche.Verify.Direct.SumWF
import ConLeche.Verify.Direct.FixWF
import ConLeche.Verify.Cached.WalkersC

/-!
# Cached shared-state checker: the inductive block and the per-declaration bridge

Port of `ConLeche/Verify/BridgeSDecl.lean` for the cached tier.  The tail
of the per-declaration composition whose bulk is
`ConLeche/Verify/Cached/BridgeCS4.lean`: the inductive-block driver
(`checkIndDeclSF_run`), its dispatch (`checkIndOrDirectSF_run`), and the
per-declaration bridge (`checkDeclSharedF_bridge`).

As in the interned original the *direct simple-structure* run has no
bridge here: `directStructsEnabled = false` makes the arm that would
call it unreachable and `directParts?_none` collapses it at one `rw`.

Against `BridgeSDecl` the systematic deletions of the tier carry
through: no arena, hence no `Ext` conjunct anywhere and no
`tierOffE`/tier-flag side condition; `ISOKF` becomes `CSOKF`, whose
`residue` needs no flag witness; the fresh state is `CSOK.empty` rather
than `ISOK.fresh`.  Every pure comparand is byte-identical to the
interned original's.

One piece the interned tier keeps in a *shared* file has to be
replicated here: `checkDeclSF_nonind` (`ConLeche/Verify/CheckerF.lean`)
is stated for `CheckIM`, because the `throw`/`ite` peels it uses are
monad-specific (`rfl` at a concrete `StateT`).  Its `CheckCM` twin —
`checkDeclSFC_nonind`, with the `_push` lemmas it consumes — is proved
below; the pure comparand (`checkDecl` at `sharedOpsC`) is the same
program.  These are the only additions: everything else in the file is
the transposition.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

theorem throwC_bind_eq {α β : Type} (e : CheckError)
    (f : α → CheckCM β) : ((throw e : CheckCM α) >>= f) = throw e := rfl


open ConLeche

variable {mode : CheckMode}

/-! ## `CheckCM` peels (the `CheckIM` helpers of
`ConLeche/Verify/CheckerF.lean` at the cached monad) -/

theorem bindC_congr {α β : Type} {x : CheckCM α} {f g : α → CheckCM β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  rw [funext h]

theorem ite_bindC {α β : Type} (c : Prop) [Decidable c]
    (a b : CheckCM α) (f : α → CheckCM β) :
    ((if c then a else b) >>= f)
      = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem installBasisDeclF_pushC (env : Env) (ci : ConstantInfo) :
    (installBasisDeclF (mkFEnv env) ci : CheckCM FEnv)
      = installBasisDecl env ci >>= fun e => pure (mkFEnv e) := by
  unfold installBasisDeclF installBasisDecl
  simp only [mkFEnv_find?, push_mkFEnv, pure_bind, ite_bindC,
    throwC_bind_eq] <;> rfl

theorem installBasisFoldF_pushC :
    ∀ (l : List ConstantInfo) (env : Env),
      (l.foldlM installBasisDeclF (mkFEnv env) : CheckCM FEnv)
        = l.foldlM installBasisDecl env >>= fun e => pure (mkFEnv e)
  | [], env => by
    simp only [List.foldlM_nil, pure_bind]
  | ci :: l, env => by
    rw [List.foldlM_cons, List.foldlM_cons, installBasisDeclF_pushC,
      bind_assoc, bind_assoc]
    refine bindC_congr fun e => ?_
    rw [pure_bind, installBasisFoldF_pushC l e]

/-! ### The direct simple-structure path's extending stages (task #175
W4c: the cached run bridge restored) -/

/-- The former's telescope stage through the index (task #195): the
whnf loop reads the index's environment, the re-check is the indexed
`checkConstantValF`. -/
theorem checkDirectSumTeleF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) :
    checkDirectSumTeleF ops (mkFEnv env) cv n cvTa₀
      = checkDirectSumTele ops env cv n cvTa₀ := by
  unfold checkDirectSumTeleF checkDirectSumTele
  cases hst : cvTa₀.type.stripPis n with
  | none => simp only [checkConstantValF_eq, mkFEnv_env]
  | some q =>
    obtain ⟨bs, body⟩ := q
    cases body <;> simp only [checkConstantValF_eq, mkFEnv_env]

/-- The direct sum's type-former stage through the index (task #175
sum-types). -/
theorem checkDirectSumIndF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (p : DirectSumParts) (capsOf : DirectSumParts → IndCaps) :
    checkDirectSumIndF ops (mkFEnv env) p capsOf
      = checkDirectSumInd ops env p capsOf
          >>= fun q => pure (mkFEnv q.1, q.2) := by
  unfold checkDirectSumIndF checkDirectSumInd
  simp only [checkConstantValF_eq, checkDirectSumTeleF_pushC, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-- The projection table through the index (task #175 S1). -/
theorem checkDirectProjTableF_pushC (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal)
    (env : Env) :
    checkDirectProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa (mkFEnv env)
      = checkDirectProjTable (m := CheckCM) T C lps nP nF rs guards off cvCa env
          >>= fun e => pure (mkFEnv e) := by
  unfold checkDirectProjTableF checkDirectProjTable
  simp only [DirectWalkers.plain, constsResolveF_eq, mkFEnv_find?, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-! ## `checkIndDecl` and the final bridge -/

/-! ## The direct simple-structure install (task #82; the cached run
bridge restored at task #175 W4c, the direct install being the only
projection route) -/

/-- The projection-table stage of the cached driver, run-level (task
#175 S1): operation-free, the state is unchanged, the environment is
the pure stage's. -/
theorem checkDirectProjTableS_run {T C : Name} {lps : List Name} {nP nF : Nat}
    {rs : Level} {guards : List Level} {off : Nat} {cvCa : ConstantVal}
    (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkDirectProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa
      (mkFEnv env) s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkDirectProjTable T C lps nP nF rs guards off cvCa env : FueledM Env).val F
      = .ok fe'.env := by
  rw [checkDirectProjTableF_pushC] at h
  obtain ⟨e₁, s₁, hstep, h⟩ := bindC_ok h
  obtain ⟨hfe, rfl⟩ := pureC_ok h
  subst hfe
  -- the pure stage in the cached monad: state unchanged, the value the
  -- `CheckM` instantiation's
  have hrun : s₀ = s₁ ∧ checkDirectProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok e₁ := by
    unfold checkDirectProjTable at hstep ⊢
    cases hb : directProjBodies T nP nF cvCa.type with
    | none =>
      try rw [hb] at hstep
      exact absurd hstep throwC_bind_ok
    | some bodies =>
      try rw [hb] at hstep
      simp only [unwrapOr, pure_bind] at hstep ⊢
      split at hstep
      · next hg =>
        rw [if_pos hg]
        split at hstep
        · next hfam =>
          rw [if_pos hfam]
          split at hstep
          · next hn =>
            rw [if_pos hn]
            obtain ⟨hfe, rfl⟩ := pureC_ok hstep
            subst hfe
            exact ⟨rfl, rfl⟩
          · exact absurd hstep throwC_bind_ok
        · exact absurd hstep throwC_bind_ok
      · exact absurd hstep throwC_bind_ok
  obtain ⟨rfl, hpure⟩ := hrun
  refine ⟨hwf, rfl, direct_table_wf henv hpure, 0, ?_⟩
  rw [checkDirectProjTable_datF]
  exact hpure

/-- The projection-table stage of the fixpoint route at the cached
driver, run-level (task #210 Part A): at a structure-like block the
direct structure's table stage (`checkDirectProjTableS_run`), else the
environment unchanged. -/
theorem checkDirectFixTableS_run {p : DirectFixParts} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkDirectFixTableF (m := CheckCM) .plain p ctorsA sortss (mkFEnv env) s₀
      = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkDirectFixTable (m := FueledM) p ctorsA sortss env).val F = .ok fe'.env := by
  match ctorsA, sortss with
  | [cA], [sorts] =>
    simp only [checkDirectFixTableF] at h
    simp only [checkDirectFixTable]
    by_cases hi : (p.nIdx == 0) = true
    · rw [if_pos hi] at h
      rw [if_pos hi]
      exact checkDirectProjTableS_run env henv hwf h
    · rw [if_neg hi] at h
      rw [if_neg hi]
      obtain ⟨rfl, rfl⟩ := pureC_ok h
      exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [], _ =>
    simp only [checkDirectFixTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | _ :: _ :: _, _ =>
    simp only [checkDirectFixTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [_], [] =>
    simp only [checkDirectFixTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [_], _ :: _ :: _ =>
    simp only [checkDirectFixTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩

set_option maxHeartbeats 1600000 in
/-- The kinds' classification is operation-free: in the cached monad it
leaves the state alone and computes what the pure one does (task #210
Part D). -/
theorem classifyFixKindsC_ok {T : Name} {lps : List Name} {nP nIdx : Nat}
    {ctorsA : List (ConstantVal × Nat)} {s₀ s' : CState}
    {kinds : List (List RecFieldKind)}
    (h : classifyFixKinds (m := CheckCM) T lps nP nIdx ctorsA s₀ = .ok (kinds, s')) :
    s' = s₀ ∧ classifyFixKinds (m := CheckM) T lps nP nIdx ctorsA = .ok kinds := by
  unfold classifyFixKinds at h ⊢
  obtain ⟨ks, s₁, hu, h⟩ := bindC_ok h
  cases hk : ctorsA.mapM (recCtorKinds T lps nP nIdx) with
  | none => rw [hk] at hu; exact nomatch hu
  | some ks' =>
  rw [hk] at hu
  simp only [unwrapOr] at hu
  obtain ⟨rfl, rfl⟩ := pureC_ok hu
  simp only [unwrapOr, hk]
  try dsimp only at h
  split at h
  · exact absurd h throwC_bind_ok
  · try dsimp only at h
    split at h
    · exact absurd h throwC_bind_ok
    · obtain ⟨rfl, rfl⟩ := pureC_ok h
      simp only [*, bind, Except.bind, ↓reduceIte, pure, Except.pure]
      exact ⟨trivial, rfl⟩

/-- The direct recursive install at the cached driver is reproduced by
the pure fueled `checkDirectFix` (task #188). -/
theorem checkDirectFixS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p₀ : DirectFixParts} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkDirectFixS mode (mkFEnv env) p₀ s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDirectFix (fueledOps mode F) env p₀ = .ok feOut.env := by
  unfold checkDirectFixS at h
  rw [directWalkersC_eq_plain] at h
  -- the front guard
  by_cases hnd : (p₀.ctors.map (·.1.name)).Nodup
  case neg => rw [if_neg hnd] at h; exact absurd h throwC_bind_ok
  rw [if_pos hnd] at h
  -- THE PROVISIONAL PASS (task #210 Part D): a throwaway former, the
  -- constructors at it, the kinds
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  rw [checkDirectSumIndF_pushC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨qP, sP₁, hindP, h⟩ := bindC_ok h
  obtain ⟨hsP₁, qP', hPP, FP₁, hFP₁⟩ :=
    (checkDirectSumIndS_sim hμ henv (flushC_csok hwf)) qP sP₁ hindP
  obtain ⟨rfl, -⟩ := hPP
  obtain ⟨envP, cvTaP, p₁P⟩ := qP
  have hFP₁p : checkDirectSumInd (fueledOps mode FP₁) env p₀.toDirectSumParts
      (fun _ => {}) = .ok (envP, cvTaP, p₁P) := by
    rw [← checkDirectSumInd_datF]; exact hFP₁
  obtain ⟨henvP, hTfP⟩ := direct_sum_ind_wf henv hFP₁p
  try simp only at h
  obtain ⟨uP, sPB, hflP, h⟩ := bindC_ok h
  rw [flushC_run] at hflP
  injection hflP with hflP
  obtain rfl : sP₁.flushed = sPB := congrArg Prod.snd hflP
  rw [checkDirectSumCtorsF_eq] at h
  obtain ⟨qP₂, sP₂, hctP, h⟩ := bindC_ok h
  obtain ⟨hsP₂, qP₂', hPP₂, FP₂, hFP₂⟩ :=
    (checkDirectSumCtorsS_sim hμ henvP hTfP (flushC_csok hsP₁.residue)) qP₂ sP₂ hctP
  obtain rfl : qP₂ = qP₂' := hPP₂
  obtain ⟨ctorsP, sortssP⟩ := qP₂
  try simp only [bind_assoc, pure_bind] at h
  have hFP₂p : checkDirectSumCtors (fueledOps mode FP₂) envP envP (p₀.complete p₁P).cvT.name
      (p₀.complete p₁P).cvT.levelParams (p₀.complete p₁P).nP (p₀.complete p₁P).nIdx
      (p₀.complete p₁P).resSort (p₀.complete p₁P).isProp (p₀.complete p₁P).large cvTaP
      (p₀.complete p₁P).ctors = .ok (ctorsP, sortssP) := by
    rw [← checkDirectSumCtors_datF]; exact hFP₂
  try simp only at h
  obtain ⟨kinds, sK, hK, h⟩ := bindC_ok h
  obtain ⟨hsK, hKp⟩ := classifyFixKindsC_ok hK
  -- stage 1: the type former, at the kinds
  obtain ⟨u1, sA', hfl0', h⟩ := bindC_ok h
  rw [flushC_run] at hfl0'
  injection hfl0' with hfl0'
  obtain rfl : sK.flushed = sA' := congrArg Prod.snd hfl0'
  rw [checkDirectSumIndF_pushC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨q1, s₁, hind, h⟩ := bindC_ok h
  have hsK' : CSOKF sK := hsK ▸ hsP₂.residue
  obtain ⟨hs₁, q1', hP1, F₁, hF₁⟩ :=
    (checkDirectSumIndS_sim hμ henv (flushC_csok hsK')) q1 s₁ hind
  obtain ⟨rfl, -⟩ := hP1
  obtain ⟨env₁, cvTa, p₁⟩ := q1
  have hF₁p : checkDirectSumInd (fueledOps mode F₁) env p₀.toDirectSumParts
      (fun p₁ => directFixCaps ((p₀.complete p₁).withKinds kinds)) = .ok (env₁, cvTa, p₁) := by
    rw [← checkDirectSumInd_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_sum_ind_wf henv hF₁p
  -- the completed record, and the elimination guard on it
  try simp only at h
  generalize hp : (p₀.complete p₁).withKinds kinds = p at h
  by_cases hg : (p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length)) = true
  · rw [if_pos hg] at h; exact absurd h throwC_bind_ok
  rw [if_neg hg] at h
  -- the index binders' sorts, read
  obtain ⟨u1, sB, hfl1, h⟩ := bindC_ok h
  rw [flushC_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  cases htq : openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 with
  | none => rw [htq] at h; exact absurd h throwC_bind_ok
  | some tq =>
  rw [htq] at h
  simp only [unwrapOr, pure_bind] at h
  rw [checkDirectFieldSortsIF_eq] at h
  obtain ⟨isorts, sS, hsorts, h⟩ := bindC_ok h
  have hTw : Expr.WScoped 0 cvTa.type := Expr.WScoped.of_not_hasFvar hTf
  obtain ⟨htqW, -⟩ := openPisAtFvars_WScoped _ _ _ htq hTw
  have hidxT := openPisAtFvars_index _ _ _ htq
  have hxPos : ∀ (i : Nat) (x : Expr), (tq.1.drop p.nP)[i]? = some x →
      Expr.WScoped (p.nP + i) (Expr.fvarTypeD x) := by
    intro i x hx
    rw [List.getElem?_drop] at hx
    obtain ⟨ty, rfl⟩ := hidxT (p.nP + i) x hx
    have hw := htqW _ (List.mem_of_getElem? hx)
    simp only [Expr.WScoped, Nat.zero_add] at hw
    exact hw.2
  obtain ⟨hsS, isorts', hPs, F₀, hF₀⟩ :=
    (checkDirectFieldSortsIS_sim hμ henv₁ hxPos (flushC_csok hs₁.residue)) isorts sS hsorts
  obtain rfl : isorts = isorts' := hPs
  have hF₀p : checkDirectFieldSortsI (fueledOps mode F₀) env₁ true false p.resSort p.nP
      (tq.1.drop p.nP) [] p.nIdx = .ok isorts := by
    rw [← checkDirectFieldSortsI_datF]; exact hF₀
  -- stage 2: every constructor, at the former's environment, the
  -- resolution guard pointed at that same environment
  rw [checkDirectSumCtorsF_eq] at h
  obtain ⟨q2, s₂, hct, h⟩ := bindC_ok h
  obtain ⟨hs₂, q2', hP2, F₂, hF₂⟩ :=
    (checkDirectSumCtorsS_sim hμ henv₁ hTf hsS) q2 s₂ hct
  obtain rfl : q2 = q2' := hP2
  obtain ⟨ctorsA, sortss⟩ := q2
  have hF₂p : checkDirectSumCtors (fueledOps mode F₂) env₁ env₁ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors
      = .ok (ctorsA, sortss) := by
    rw [← checkDirectSumCtors_datF]; exact hF₂
  -- the field kinds, re-checked
  try simp only at h
  rw [directFixFieldsOkF_eq] at h
  by_cases hk : directFixFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true
  case neg => rw [if_neg hk] at h; exact absurd h throwC_bind_ok
  rw [if_pos hk] at h
  -- the stream's rules against the generated ones
  by_cases hr : directFixRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP
      p.ctors.length ctorsA p.kinds p.rhss = true
  case neg => rw [if_neg hr] at h; exact absurd h throwC_bind_ok
  rw [if_pos hr] at h
  -- the constructors' conses
  obtain ⟨hlen, -, hall⟩ := checkDirectSumCtors_inv hF₂p
  have henv₂ : EnvWF (consSumCtors p.nP ctorsA env₁) := by
    refine envWF_consSumCtors henv₁ ?_
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, sorts, -, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    exact direct_sum_ctor_typeWF hrun
  rw [consSumCtorsF_mkFEnv] at h
  -- stage 3: the recursor with the inductive hypotheses, generated
  -- and compared
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : s₂.flushed = sC := congrArg Prod.snd hfl2
  rw [checkDirectFixRecF_eq] at h
  obtain ⟨q3, s₃, hrc, h⟩ := bindC_ok h
  obtain ⟨hs₃, q3', hP3, F₃, hF₃⟩ :=
    (checkDirectFixRecS_sim hμ henv₂ (flushC_csok hs₂.residue)) q3 s₃ hrc
  obtain rfl : q3 = q3' := hP3
  obtain ⟨cvRa, rhss⟩ := q3
  have hF₃p : checkDirectFixRec (fueledOps mode F₃) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) := by
    rw [← checkDirectFixRec_datF]; exact hF₃
  have henv₃ := direct_fix_rec_wf henv₂ hF₃p
  -- the projection table at a structure-like block (task #210 Part A)
  rw [push_mkFEnv] at h
  obtain ⟨hwfO, hfeO, -, F₆, hF₆⟩ := checkDirectFixTableS_run _ henv₃ hs₃.residue h
  obtain ⟨G, hleP₁, hleP₂, hle₁, hle₀, hle₂, hle₃, hle₆⟩ :
      ∃ G, FP₁ ≤ G ∧ FP₂ ≤ G ∧ F₁ ≤ G ∧ F₀ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G ∧ F₆ ≤ G :=
    ⟨max FP₁ (max FP₂ (max F₁ (max F₀ (max F₂ (max F₃ F₆))))), by omega, by omega, by omega,
      by omega, by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have gP₁ : checkDirectSumInd (fueledOps mode G) env p₀.toDirectSumParts
      (fun _ => {}) = .ok (envP, cvTaP, p₁P) := by
    rw [← checkDirectSumInd_datF]; exact FueledM.up hleP₁ hFP₁
  have gP₂ : checkDirectSumCtors (fueledOps mode G) envP envP (p₀.complete p₁P).cvT.name
      (p₀.complete p₁P).cvT.levelParams (p₀.complete p₁P).nP (p₀.complete p₁P).nIdx
      (p₀.complete p₁P).resSort (p₀.complete p₁P).isProp (p₀.complete p₁P).large cvTaP
      (p₀.complete p₁P).ctors = .ok (ctorsP, sortssP) := by
    rw [← checkDirectSumCtors_datF]; exact FueledM.up hleP₂ hFP₂
  have g₁ : checkDirectSumInd (fueledOps mode G) env p₀.toDirectSumParts
      (fun p₁ => directFixCaps ((p₀.complete p₁).withKinds kinds)) = .ok (env₁, cvTa, p₁) := by
    rw [← checkDirectSumInd_datF]; exact FueledM.up hle₁ hF₁
  have g₀ : checkDirectFieldSortsI (fueledOps mode G) env₁ true false p.resSort p.nP
      (tq.1.drop p.nP) [] p.nIdx = .ok isorts := by
    rw [← checkDirectFieldSortsI_datF]; exact FueledM.up hle₀ hF₀
  have g₂ : checkDirectSumCtors (fueledOps mode G) env₁ env₁ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors
      = .ok (ctorsA, sortss) := by
    rw [← checkDirectSumCtors_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkDirectFixRec (fueledOps mode G) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) := by
    rw [← checkDirectFixRec_datF]; exact FueledM.up hle₃ hF₃
  have g₆ : checkDirectFixTable (m := CheckM) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (directSumRules p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ = .ok feOut.env := by
    rw [← checkDirectFixTable_datF]; exact FueledM.up hle₆ hF₆
  unfold checkDirectFix
  rw [if_pos hnd]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [gP₁]
  simp only [Except.bind]
  rw [gP₂]
  simp only [Except.bind]
  rw [hKp]
  simp only [Except.bind]
  rw [g₁]
  simp only [Except.bind]
  rw [hp, if_neg hg]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [htq]
  simp only [unwrapOr, pure, Except.pure, Except.bind]
  rw [g₀]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [if_pos hk, if_pos hr]
  rw [g₃]
  simp only [Except.bind]
  exact g₆

/-- The inductive block at the cached driver is reproduced by the
pure fueled `checkIndDecl`. -/
theorem checkIndDeclSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkIndDeclSF mode (mkFEnv env) block s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkIndDecl mode (fueledOps mode F) env block = .ok feOut.env := by
  unfold checkIndDeclSF at h
  have hbnAll : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have : ci.name ∈ block.map (·.name) :=
      List.mem_map_of_mem (List.mem_filter.mp hci).1
    simpa using this
  split at h
  case isFalse hsplit =>
    exact absurd h throwC_bind_ok
  case isTrue hsplit =>
  split at h
  case _ cvT c0 cvC nP nF heq1 heq2 =>
    obtain ⟨caps, s₁, hcaps, h⟩ := bindC_ok h
    obtain ⟨hcapsv, rfl⟩ := pureC_ok hcaps
    have hcapsv' : indBlockCaps mode env cvT cvC nP nF = caps := by
      rw [← indBlockCapsF_eq]; exact hcapsv
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindC_ok h
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run hμ _ env henv hwf hfold
    obtain ⟨fe₃, s₃, hrecs, h⟩ := bindC_ok h
    rw [hfe₂] at hrecs
    obtain ⟨hwf₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run hμ henv₂ hbnAll hwf₂ hrecs
    rw [hfe₃] at h
    simp only [mkFEnv_find?] at h
    rw [ctorResidualOkF_eq] at h
    by_cases hctorRes : ctorResidualOk mode fe₃.env cvT.name cvC.name
        cvT.levelParams nP nF caps.eta = true
    case neg =>
      rw [if_neg hctorRes] at h
      exact absurd h throwC_bind_ok
    rw [if_pos hctorRes] at h
    by_cases hguard : (List.range nF).all
        (fun j => (fe₃.env.find? (projFnName cvT.name j)).isNone) = true
    case neg =>
      rw [if_neg hguard] at h
      exact absurd h throwC_bind_ok
    rw [if_pos hguard] at h
    -- the projection phase: structure-like blocks only (task #175
    -- SigmaHom); off the shape the phase is the identity
    by_cases hsl : ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF
        = true
    case neg =>
      rw [if_neg hsl] at h
      obtain ⟨hfe₄, rfl⟩ := pureC_ok h
      subst hfe₄
      refine ⟨hwf₃, rfl, max F₁ F₂, ?_⟩
      have hF₁p := FueledM.up (Nat.le_max_left F₁ F₂) hF₁
      rw [foldlM_atF] at hF₁p
      simp only [checkIndMember_datF] at hF₁p
      have hF₂p := FueledM.up (Nat.le_max_right F₁ F₂) hF₂
      rw [checkIndRecs_datF] at hF₂p
      have hF₁p' : List.foldlM (checkIndMember (fueledOps mode (max F₁ F₂))
          (block.map (·.name)) caps) env _ = .ok fe₂.env := hF₁p
      simp only [checkIndDecl]
      split
      case isFalse hgs => exact absurd hsplit hgs
      case isTrue hgs =>
      split
      next cvT' c0' cvC' nP' nF' heq1' heq2' =>
        have h12 : ([(.indInfo cvT c0 : ConstantInfo)]) =
            [(.indInfo cvT' c0' : ConstantInfo)] :=
          heq1.symm.trans heq1'
        have h34 : ([(.ctorInfo cvC nP nF : ConstantInfo)]) =
            [(.ctorInfo cvC' nP' nF' : ConstantInfo)] :=
          heq2.symm.trans heq2'
        simp only [List.cons.injEq, and_true,
          ConstantInfo.indInfo.injEq, ConstantInfo.ctorInfo.injEq]
          at h12 h34
        obtain ⟨rfl, rfl⟩ := h12
        obtain ⟨rfl, rfl, rfl⟩ := h34
        simp only [Bind.bind, Except.bind, pure, Except.pure]
        rw [hcapsv']
        split
        next err herr => exact nomatch (hF₁p'.symm.trans herr)
        next v hok =>
        obtain rfl : fe₂.env = v := by
          have hv : (Except.ok fe₂.env : Except CheckError Env) = .ok v :=
            hF₁p'.symm.trans hok
          injection hv
        split
        next err herr => exact nomatch (hF₂p.symm.trans herr)
        next v hok =>
        obtain rfl : fe₃.env = v := by
          have hv : (Except.ok fe₃.env : Except CheckError Env) = .ok v :=
            hF₂p.symm.trans hok
          injection hv
        rw [if_pos hctorRes, if_pos hguard, if_neg hsl]
        rfl
      next x1 x2 hne' =>
        exact (hne' cvT c0 cvC nP nF heq1 heq2).elim
    rw [if_pos hsl] at h
    obtain ⟨hwf₄, hfe₄, henv₄, F₃, hF₃⟩ :=
      foldProjFnS_run hμ _ fe₃.env henv₃ hwf₃ h
    refine ⟨hwf₄, hfe₄, max F₁ (max F₂ F₃), ?_⟩
    have hF₁p := FueledM.up (Nat.le_max_left F₁ (max F₂ F₃)) hF₁
    rw [foldlM_atF] at hF₁p
    simp only [checkIndMember_datF] at hF₁p
    have hF₂p := FueledM.up (Nat.le_trans (Nat.le_max_left F₂ F₃)
      (Nat.le_max_right F₁ (max F₂ F₃))) hF₂
    rw [checkIndRecs_datF] at hF₂p
    have hF₃p := FueledM.up (Nat.le_trans (Nat.le_max_right F₂ F₃)
      (Nat.le_max_right F₁ (max F₂ F₃))) hF₃
    rw [foldlM_atF] at hF₃p
    simp only [installProjFnStep_datF] at hF₃p
    have hF₁p' : List.foldlM (checkIndMember
        (fueledOps mode (max F₁ (max F₂ F₃)))
        (block.map (·.name)) caps) env _ = .ok fe₂.env := hF₁p
    have hF₃p' : List.foldlM (installProjFnStep mode
        (fueledOps mode (max F₁ (max F₂ F₃)))
        cvT.name cvC.name cvT.levelParams nP nF) fe₃.env _ =
        .ok feOut.env := hF₃p
    simp only [checkIndDecl]
    split
    case isFalse hgs => exact absurd hsplit hgs
    case isTrue hgs =>
    split
    next cvT' c0' cvC' nP' nF' heq1' heq2' =>
      have h12 : ([(.indInfo cvT c0 : ConstantInfo)]) =
          [(.indInfo cvT' c0' : ConstantInfo)] :=
        heq1.symm.trans heq1'
      have h34 : ([(.ctorInfo cvC nP nF : ConstantInfo)]) =
          [(.ctorInfo cvC' nP' nF' : ConstantInfo)] :=
        heq2.symm.trans heq2'
      simp only [List.cons.injEq, and_true,
        ConstantInfo.indInfo.injEq, ConstantInfo.ctorInfo.injEq]
        at h12 h34
      obtain ⟨rfl, rfl⟩ := h12
      obtain ⟨rfl, rfl, rfl⟩ := h34
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [hcapsv']
      split
      next err herr => exact nomatch (hF₁p'.symm.trans herr)
      next v hok =>
      obtain rfl : fe₂.env = v := by
        have hv : (Except.ok fe₂.env : Except CheckError Env) = .ok v :=
          hF₁p'.symm.trans hok
        injection hv
      split
      next err herr => exact nomatch (hF₂p.symm.trans herr)
      next v hok =>
      obtain rfl : fe₃.env = v := by
        have hv : (Except.ok fe₃.env : Except CheckError Env) = .ok v :=
          hF₂p.symm.trans hok
        injection hv
      rw [if_pos hctorRes, if_pos hguard, if_pos hsl]
      exact hF₃p'
    next x1 x2 hne' =>
      exact (hne' cvT c0 cvC nP nF heq1 heq2).elim
  case _ =>
    rename_i x1 x2 hne
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindC_ok h
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run hμ _ env henv hwf hfold
    rw [hfe₂] at h
    obtain ⟨hwf₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run hμ henv₂ hbnAll hwf₂ h
    refine ⟨hwf₃, hfe₃, max F₁ F₂, ?_⟩
    have hF₁p := FueledM.up (Nat.le_max_left F₁ F₂) hF₁
    rw [foldlM_atF] at hF₁p
    simp only [checkIndMember_datF] at hF₁p
    have hF₂p := FueledM.up (Nat.le_max_right F₁ F₂) hF₂
    rw [checkIndRecs_datF] at hF₂p
    have hF₁p' : List.foldlM (checkIndMember (fueledOps mode (max F₁ F₂))
        (block.map (·.name)) {}) env _ = .ok fe₂.env := hF₁p
    simp only [checkIndDecl]
    split
    case isFalse hgs => exact absurd hsplit hgs
    case isTrue hgs =>
    split
    next cvT' c0' cvC' nP' nF' heq1' heq2' =>
      exact (hne cvT' c0' cvC' nP' nF' heq1' heq2').elim
    next y1 y2 hne' =>
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      split
      next err herr => exact nomatch (hF₁p'.symm.trans herr)
      next v hok =>
      obtain rfl : fe₂.env = v := by
        have hv : (Except.ok fe₂.env : Except CheckError Env) = .ok v :=
          hF₁p'.symm.trans hok
        injection hv
      exact hF₂p

/-- The inductive-block dispatch of the cached driver: a RECOGNISED
block goes to `checkDirectFixS`, everything else to `checkIndDeclSF`,
and either way the pure fueled `checkDecl` reproduces the run. -/
theorem checkIndOrDirectSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match directFixParts? block with
          | some p => checkDirectFixS mode (mkFEnv env) p
          | none => checkIndDeclSF mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) env (.indDecl block) =
      .ok feOut.env := by
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match directFixParts? block with
      | some p => checkDirectFix (fueledOps mode F) env p
      | none => checkIndDecl mode (fueledOps mode F) env block) = .ok feOut.env
  cases hfp : directFixParts? block with
  | some p =>
    rw [hfp] at h
    obtain ⟨hres, hfe, F, hF⟩ := checkDirectFixS_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩
  | none =>
    rw [hfp] at h
    obtain ⟨hres, hfe, F, hF⟩ := checkIndDeclSF_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩

end ConLeche.Cached
