module

public import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.FastOps
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Verify.Inductives.SumWF
import ConLeche.Verify.Inductives.FixWF
import ConLeche.Verify.Inductives.MutualWF
import ConLeche.Verify.Cached.WalkersC

public section

/-!
# Cached shared-state checker: the inductive block and the per-declaration bridge

Port of `ConLeche/Verify/BridgeSDecl.lean` for the cached tier.  The tail
of the per-declaration composition whose bulk is
`ConLeche/Verify/Cached/BridgeCS4.lean`: the inductive-block driver
(`checkIndDeclSF_run`), its dispatch (`checkModeledOrNativeSF_run`), and the
per-declaration bridge (`checkDeclSharedF_bridge`).

As in the interned original the *direct simple-structure* run has no
bridge here: `structsEnabled = false` makes the arm that would
call it unreachable and `structParts?_none` collapses it at one `rw`.

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
variable {pins : List NatOpPinSet}

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
theorem checkSumTeleF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) :
    checkSumTeleF ops (mkFEnv env) cv n cvTa₀
      = checkSumTele ops env cv n cvTa₀ := by
  unfold checkSumTeleF checkSumTele
  cases hst : cvTa₀.type.stripPis n with
  | none => simp only [checkConstantValF_eq, mkFEnv_env]
  | some q =>
    obtain ⟨bs, body⟩ := q
    cases body <;> simp only [checkConstantValF_eq, mkFEnv_env]

/-- The direct sum's type-former stage through the index (task #175
sum-types). -/
theorem checkSumIndF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (p : InductiveShape) (capsOf : InductiveShape → IndCaps) :
    checkSumIndF ops (mkFEnv env) p capsOf
      = checkSumInd ops env p capsOf
          >>= fun q => pure (mkFEnv q.1, q.2) := by
  unfold checkSumIndF checkSumInd
  simp only [checkConstantValF_eq, checkSumTeleF_pushC, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-- The projection table through the index (task #175 S1). -/
theorem checkStructProjTableF_pushC (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal)
    (env : Env) :
    checkStructProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa (mkFEnv env)
      = checkStructProjTable (m := CheckCM) T C lps nP nF rs guards off cvCa env
          >>= fun e => pure (mkFEnv e) := by
  unfold checkStructProjTableF checkStructProjTable
  simp only [StructWalkers.plain, constsResolveF_eq, mkFEnv_find?, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-! ## `checkModeled` and the final bridge -/

/-! ## The direct simple-structure install (task #82; the cached run
bridge restored at task #175 W4c, the direct install being the only
projection route) -/

/-- The projection-table stage of the cached driver, run-level (task
#175 S1): operation-free, the state is unchanged, the environment is
the pure stage's. -/
theorem checkStructProjTableS_run {T C : Name} {lps : List Name} {nP nF : Nat}
    {rs : Level} {guards : List Level} {off : Nat} {cvCa : ConstantVal}
    (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkStructProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa
      (mkFEnv env) s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkStructProjTable T C lps nP nF rs guards off cvCa env : FueledM Env).val F
      = .ok fe'.env := by
  rw [checkStructProjTableF_pushC] at h
  obtain ⟨e₁, s₁, hstep, h⟩ := bindC_ok h
  obtain ⟨hfe, rfl⟩ := pureC_ok h
  subst hfe
  -- the pure stage in the cached monad: state unchanged, the value the
  -- `CheckM` instantiation's
  have hrun : s₀ = s₁ ∧ checkStructProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok e₁ := by
    unfold checkStructProjTable at hstep ⊢
    cases hb : structProjBodies T nP nF cvCa.type with
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
  rw [checkStructProjTable_datF]
  exact hpure

/-- The projection-table stage of the fixpoint route at the cached
driver, run-level (task #210 Part A): at a structure-like block the
direct structure's table stage (`checkStructProjTableS_run`), else the
environment unchanged. -/
theorem checkNativeTableS_run {p : NativeParts} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkNativeTableF (m := CheckCM) .plain p ctorsA sortss (mkFEnv env) s₀
      = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkNativeTable (m := FueledM) p ctorsA sortss env).val F = .ok fe'.env := by
  match ctorsA, sortss with
  | [cA], [sorts] =>
    simp only [checkNativeTableF] at h
    simp only [checkNativeTable]
    by_cases hi : (p.nIdx == 0) = true
    · rw [if_pos hi] at h
      rw [if_pos hi]
      exact checkStructProjTableS_run env henv hwf h
    · rw [if_neg hi] at h
      rw [if_neg hi]
      obtain ⟨rfl, rfl⟩ := pureC_ok h
      exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [], _ =>
    simp only [checkNativeTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | _ :: _ :: _, _ =>
    simp only [checkNativeTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [_], [] =>
    simp only [checkNativeTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [_], _ :: _ :: _ =>
    simp only [checkNativeTableF] at h
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

/-- One pass at the cached driver (task #268) is reproduced by the
pure fueled `checkNativePass`: the former's environment is the index
over the pure one, the memo state is sound at it, and the
constructors' conses onto it are well-formed. -/
theorem checkNativePassS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p₀ : NativeParts} {isRec : Bool} {s₀ : CState} (hs : CSOK mode env s₀)
    {q : NativePass FEnv} {b : Bool} {s' : CState}
    (h : checkNativePassS mode (mkFEnv env) p₀ isRec s₀ = .ok ((q, b), s')) :
    ∃ env₁ : Env, q.env₁ = mkFEnv env₁ ∧ CSOK mode env₁ s' ∧ EnvWF env₁ ∧
      q.cvTa.type.hasFvar = false ∧ EnvWF (consSumCtors q.p.nP q.ctorsA env₁) ∧
      ∃ F, (checkNativePass (fueledOpsM mode) env p₀ isRec).val F
        = .ok (⟨env₁, q.cvTa, q.p, q.ctorsA, q.sortss⟩, b) := by
  unfold checkNativePassS at h
  -- the type former, at the record at the verdict
  rw [checkSumIndF_pushC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨q1, s₁, hind, h⟩ := bindC_ok h
  obtain ⟨hs₁, q1', hP1, F₁, hF₁⟩ := (checkSumIndS_sim hμ henv hs) q1 s₁ hind
  obtain ⟨rfl, -⟩ := hP1
  obtain ⟨env₁, cvTa, p₁⟩ := q1
  have hF₁p : checkSumInd (fueledOps mode F₁) env p₀.toInductiveShape
      (fun p₁ => nativeCapsAt p₁ isRec) = .ok (env₁, cvTa, p₁) := by
    rw [← checkSumInd_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_sum_ind_wf henv hF₁p (fun q => nativeCapsAt_arity q isRec)
  -- every constructor, at the former's environment, the resolution
  -- guard pointed at that same environment
  try simp only at h
  obtain ⟨uB, sB, hflB, h⟩ := bindC_ok h
  rw [flushC_run] at hflB
  injection hflB with hflB
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hflB
  rw [checkSumCtorsF_eq] at h
  obtain ⟨q2, s₂, hct, h⟩ := bindC_ok h
  obtain ⟨hs₂, q2', hP2, F₂, hF₂⟩ :=
    (checkSumCtorsS_sim hμ henv₁ hTf (flushC_csok hs₁.residue)) q2 s₂ hct
  obtain rfl : q2 = q2' := hP2
  obtain ⟨ctorsA, sortss⟩ := q2
  have hF₂p : checkSumCtors (fueledOps mode F₂) env₁ env₁ (p₀.complete p₁).cvT.name
      (p₀.complete p₁).cvT.levelParams (p₀.complete p₁).nP (p₀.complete p₁).nIdx
      (p₀.complete p₁).resSort (p₀.complete p₁).isProp (p₀.complete p₁).large cvTa
      (p₀.complete p₁).ctors = .ok (ctorsA, sortss) := by
    rw [← checkSumCtors_datF]; exact hF₂
  -- the kinds, classified on the stored constructors
  try simp only at h
  obtain ⟨kinds, sK, hK, h⟩ := bindC_ok h
  obtain ⟨hsK, hKp⟩ := classifyFixKindsC_ok hK
  obtain ⟨hq, rfl⟩ := pureC_ok h
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  subst hsK
  -- the constructors' conses
  have henv₂ : EnvWF (consSumCtors (p₀.complete p₁).nP ctorsA env₁) := by
    refine envWF_consSumCtors henv₁ ?_
    intro c hc
    obtain ⟨hlen, -, hall⟩ := checkSumCtors_inv hF₂p
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < (p₀.complete p₁).ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, sorts, -, hrun⟩ := hall j ((p₀.complete p₁).ctors[j]) c
      (List.getElem?_eq_getElem hj') hj
    exact direct_sum_ctor_typeWF hrun
  refine ⟨env₁, rfl, hs₂, henv₁, hTf, henv₂, max F₁ F₂, ?_⟩
  have g₁ : checkSumInd (fueledOps mode (max F₁ F₂)) env p₀.toInductiveShape
      (fun p₁ => nativeCapsAt p₁ isRec) = .ok (env₁, cvTa, p₁) := by
    rw [← checkSumInd_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
  have g₂ : checkSumCtors (fueledOps mode (max F₁ F₂)) env₁ env₁ (p₀.complete p₁).cvT.name
      (p₀.complete p₁).cvT.levelParams (p₀.complete p₁).nP (p₀.complete p₁).nIdx
      (p₀.complete p₁).resSort (p₀.complete p₁).isProp (p₀.complete p₁).large cvTa
      (p₀.complete p₁).ctors = .ok (ctorsA, sortss) := by
    rw [← checkSumCtors_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
  rw [checkNativePass_datF]
  unfold checkNativePass
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [hKp]

/-- The install after the pass at the cached driver is reproduced by
the pure fueled `checkNativeTail`. -/
theorem checkNativeTailS_run (hμ : mode.verifiedChecks = true) {env env₁ : Env}
    (henv₁ : EnvWF env₁) {cvTa : ConstantVal} {p : NativeParts}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hTf : cvTa.type.hasFvar = false) (henv₂ : EnvWF (consSumCtors p.nP ctorsA env₁))
    {s₀ : CState} (hs : CSOK mode env₁ s₀) {feOut : FEnv} {s' : CState}
    (h : checkNativeTailS mode (mkFEnv env) ⟨mkFEnv env₁, cvTa, p, ctorsA, sortss⟩ s₀
      = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (checkNativeTail (fueledOpsM mode) env ⟨env₁, cvTa, p, ctorsA, sortss⟩).val F
      = .ok feOut.env := by
  unfold checkNativeTailS at h
  rw [structWalkersC_eq_plain] at h
  try simp only at h
  -- the elimination guard on the completed record
  by_cases hg : (p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length)) = true
  · rw [if_pos hg] at h; exact absurd h throwC_bind_ok
  rw [if_neg hg] at h
  -- the index binders' sorts, read
  cases htq : openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 with
  | none => rw [htq] at h; exact absurd h throwC_bind_ok
  | some tq =>
  rw [htq] at h
  simp only [unwrapOr, pure_bind] at h
  rw [checkStructFieldSortsIF_eq] at h
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
    (checkStructFieldSortsIS_sim hμ henv₁ hxPos hs) isorts sS hsorts
  obtain rfl : isorts = isorts' := hPs
  -- the field kinds, re-checked
  try simp only at h
  rw [nativeFieldsOkF_eq] at h
  by_cases hk : nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true
  case neg => rw [if_neg hk] at h; exact absurd h throwC_bind_ok
  rw [if_pos hk] at h
  -- the stream's rules against the generated ones
  by_cases hr : nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP
      p.ctors.length ctorsA p.kinds p.rhss p.cvR.type = true
  case neg => rw [if_neg hr] at h; exact absurd h throwC_bind_ok
  rw [if_pos hr] at h
  rw [consSumCtorsF_mkFEnv] at h
  -- the recursor with the inductive hypotheses, generated and compared
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : sS.flushed = sC := congrArg Prod.snd hfl2
  rw [checkNativeRecF_eq] at h
  obtain ⟨q3, s₃, hrc, h⟩ := bindC_ok h
  obtain ⟨hs₃, q3', hP3, F₃, hF₃⟩ :=
    (checkNativeRecS_sim hμ henv₂ (flushC_csok hsS.residue)) q3 s₃ hrc
  obtain rfl : q3 = q3' := hP3
  obtain ⟨cvRa, rhss⟩ := q3
  have hF₃p : checkNativeRec (fueledOps mode F₃) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) := by
    rw [← checkNativeRec_datF]; exact hF₃
  have henv₃ := direct_fix_rec_wf henv₂ hF₃p
  -- the projection table at a structure-like block (task #210 Part A)
  rw [push_mkFEnv, show FEnv.find? (mkFEnv (consSumCtors p.nP ctorsA env₁))
    = (consSumCtors p.nP ctorsA env₁).find? from
    mkFEnv_find?_fun _] at h
  obtain ⟨hwfO, hfeO, -, F₆, hF₆⟩ := checkNativeTableS_run _ henv₃ hs₃.residue h
  obtain ⟨G, hle₀, hle₃, hle₆⟩ : ∃ G, F₀ ≤ G ∧ F₃ ≤ G ∧ F₆ ≤ G :=
    ⟨max F₀ (max F₃ F₆), by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₀ : checkStructFieldSortsI (fueledOps mode G) env₁ true false p.resSort p.nP
      (tq.1.drop p.nP) [] p.nIdx = .ok isorts := by
    rw [← checkStructFieldSortsI_datF]; exact FueledM.up hle₀ hF₀
  have g₃ : checkNativeRec (fueledOps mode G) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) := by
    rw [← checkNativeRec_datF]; exact FueledM.up hle₃ hF₃
  have g₆ : checkNativeTable (m := CheckM) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules (consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ = .ok feOut.env := by
    rw [← checkNativeTable_datF]; exact FueledM.up hle₆ hF₆
  rw [checkNativeTail_datF]
  unfold checkNativeTail
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg hg]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [htq]
  simp only [unwrapOr, pure, Except.pure, Except.bind]
  rw [g₀]
  simp only [Except.bind]
  rw [if_pos hk, if_pos hr]
  rw [g₃]
  simp only [Except.bind]
  exact g₆

/-- The direct recursive install at the cached driver is reproduced by
the pure fueled `checkNative` (task #188): the pass at the syntactic
reading, again at the classified verdict where it overshot (task
#268), and the install after the settled one. -/
theorem checkNativeS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p₀ : NativeParts} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkNativeS mode (mkFEnv env) p₀ s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkNative (fueledOps mode F) env p₀ = .ok feOut.env := by
  unfold checkNativeS at h
  -- the front guard
  by_cases hnd : (p₀.ctors.map (·.1.name)).Nodup
  case neg => rw [if_neg hnd] at h; exact absurd h throwC_bind_ok
  rw [if_pos hnd] at h
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  -- the pass at the syntactic reading
  obtain ⟨r, s₁, hP, h⟩ := bindC_ok h
  obtain ⟨⟨fe₁, cvTa, p, ctorsA, sortss⟩, settled⟩ := r
  obtain ⟨env₁, hq₁, hs₁, henv₁, hTf, henv₂, F₁, hF₁⟩ :=
    checkNativePassS_run hμ henv (flushC_csok hwf) hP
  simp only at hq₁ hs₁ henv₁ hTf henv₂ hF₁
  subst hq₁
  try simp only at h
  cases settled with
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hwfO, hfeO, F₂, hF₂⟩ := checkNativeTailS_run hμ henv₁ hTf henv₂ hs₁ h
    refine ⟨hwfO, hfeO, max F₁ F₂, ?_⟩
    have g₁ : checkNativePass (fueledOps mode (max F₁ F₂)) env p₀ (nativeRawRec p₀)
        = .ok (⟨env₁, cvTa, p, ctorsA, sortss⟩, true) := by
      rw [← checkNativePass_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
    have g₂ : checkNativeTail (fueledOps mode (max F₁ F₂)) env ⟨env₁, cvTa, p, ctorsA, sortss⟩
        = .ok feOut.env := by
      rw [← checkNativeTail_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
    unfold checkNative
    rw [if_pos hnd]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [g₁]
    simp only [Except.bind, ↓reduceIte]
    exact g₂
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- the pass again, at the classified verdict
  obtain ⟨u1, sB, hfl1, h⟩ := bindC_ok h
  rw [flushC_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  obtain ⟨r', s₂, hP', h⟩ := bindC_ok h
  obtain ⟨⟨fe₁', cvTa', p', ctorsA', sortss'⟩, settled'⟩ := r'
  obtain ⟨env₁', hq₁', hs₁', henv₁', hTf', henv₂', F₂, hF₂⟩ :=
    checkNativePassS_run hμ henv (flushC_csok hs₁.residue) hP'
  simp only at hq₁' hs₁' henv₁' hTf' henv₂' hF₂
  subst hq₁'
  try simp only at h
  cases settled' with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h throwC_bind_ok
  | true =>
  simp only [↓reduceIte] at h
  obtain ⟨hwfO, hfeO, F₃, hF₃⟩ := checkNativeTailS_run hμ henv₁' hTf' henv₂' hs₁' h
  obtain ⟨G, hle₁, hle₂, hle₃⟩ : ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G :=
    ⟨max F₁ (max F₂ F₃), by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₁ : checkNativePass (fueledOps mode G) env p₀ (nativeRawRec p₀)
      = .ok (⟨env₁, cvTa, p, ctorsA, sortss⟩, false) := by
    rw [← checkNativePass_datF]; exact FueledM.up hle₁ hF₁
  have g₂ : checkNativePass (fueledOps mode G) env p₀ (nativeIsRec p.kinds)
      = .ok (⟨env₁', cvTa', p', ctorsA', sortss'⟩, true) := by
    rw [← checkNativePass_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkNativeTail (fueledOps mode G) env ⟨env₁', cvTa', p', ctorsA', sortss'⟩
      = .ok feOut.env := by
    rw [← checkNativeTail_datF]; exact FueledM.up hle₃ hF₃
  unfold checkNative
  rw [if_pos hnd]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind, Bool.false_eq_true, ↓reduceIte]
  rw [g₂]
  simp only [Except.bind, ↓reduceIte]
  exact g₃

/-- The inductive block at the cached driver is reproduced by the
pure fueled `checkModeled`. -/
theorem checkIndDeclSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkIndDeclSF mode (mkFEnv env) block s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkModeled mode (fueledOps mode F) env block = .ok feOut.env := by
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
    -- the block's capability pins at its (single) inductive member:
    -- the member IS the former the record was computed for
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run hμ _ env henv hwf (by
        intro ci hci cv caps₀ hceq
        have hmemI : ci ∈ [ConstantInfo.indInfo cvT c0] := by
          rw [← heq1]
          exact List.mem_filter.mpr ⟨(List.mem_filter.mp hci).1, by subst hceq; rfl⟩
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj
          (hceq ▸ List.mem_singleton.mp hmemI)
        rw [← hcapsv']
        exact ConLeche.etaPins_of_indBlockCaps) hfold
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
      simp only [checkModeled]
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
    simp only [checkModeled]
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
      foldIndMemberS_run hμ _ env henv hwf
        (fun _ _ _ _ _ => ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide))⟩) hfold
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
    simp only [checkModeled]
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

/-! ## The mutual install (task #278)

The `FEnv`-to-`Env` mirrors of the member-aware stages (the
`ConLeche/Verify/CheckerF.lean` family at a mutual block), then the
run bridges: the formers' flushing fold, the cross-member checks, the
constructors, the recursors and the tables. -/

section MutualMirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem normCtorValMF_eq (ops : CheckerOps m) (env : Env) (memberNames : List Name)
    (nP nF : Nat) (cvC cvCa : ConstantVal) :
    normCtorValMF ops (mkFEnv env) memberNames nP nF cvC cvCa
      = normCtorValM ops env memberNames nP nF cvC cvCa := by
  simp only [normCtorValMF, normCtorValM, mkFEnv_env, checkConstantValF_eq]

theorem checkMutualCtorF_eq (ops : CheckerOps m) (env : Env) (memberNames : List Name)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    checkMutualCtorF ops .plain (mkFEnv env) memberNames T lps nP nIdx resSort isProp large
        cvC nF cvTa
      = checkMutualCtor ops env memberNames T lps nP nIdx resSort isProp large cvC nF cvTa := by
  simp only [checkMutualCtorF, checkMutualCtor, checkConstantValF_eq, normCtorValMF_eq,
    checkStructDomsAtFA_eq, checkStructDomsAtF_eq, openPisAtFvarsF_eq,
    checkStructFieldSortsIFA_eq, checkStructFieldSortsIF_eq, StructWalkers.plain,
    constsResolveF_eq]

theorem checkMutualCtorsF_eq (ops : CheckerOps m) (env : Env) (b : MutualBlock)
    (fms : List MutualFormerA) (isProp : Bool) :
    ∀ (cs : List MutualCtor),
      checkMutualCtorsF ops .plain (mkFEnv env) b fms isProp cs
        = checkMutualCtors ops env b fms isProp cs
  | [] => rfl
  | c :: cs => by
    simp only [checkMutualCtorsF, checkMutualCtors, checkMutualCtorF_eq,
      checkMutualCtorsF_eq ops env b fms isProp cs]

theorem checkMutualRecTyF_eq (ops : CheckerOps m) (env : Env) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4) (mIdx : Nat)
    (streamRec : Option ConstantVal) :
    checkMutualRecTyF ops .plain (mkFEnv env) b formers4 ctors4 mIdx streamRec
      = checkMutualRecTy ops env b formers4 ctors4 mIdx streamRec := by
  simp only [checkMutualRecTyF, checkMutualRecTy, mkFEnv_env, checkConstantValF_eq,
    StructWalkers.plain, constsResolveF_eq] <;> rfl

theorem checkMutualRecTysF_eq (ops : CheckerOps m) (env : Env) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
    (streamRecs : Option (List (ConstantVal × List RecRule))) :
    ∀ (k : Nat),
      checkMutualRecTysF ops .plain (mkFEnv env) b formers4 ctors4 streamRecs k
        = checkMutualRecTys ops env b formers4 ctors4 streamRecs k
  | 0 => rfl
  | k + 1 => by
    simp only [checkMutualRecTysF, checkMutualRecTys, checkMutualRecTyF_eq,
      checkMutualRecTysF_eq ops env b formers4 ctors4 streamRecs k]

theorem checkMutualMemberRulesF_eq (envR : Env) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4) (mIdx : Nat)
    (streamRec : Option (ConstantVal × List RecRule)) :
    checkMutualMemberRulesF (m := m) .plain (mkFEnv envR) b formers4 ctors4 mIdx streamRec
      = checkMutualMemberRules (m := m) envR b formers4 ctors4 mIdx streamRec := by
  simp only [checkMutualMemberRulesF, checkMutualMemberRules, StructWalkers.plain,
    constsResolveF_eq] <;> rfl

theorem checkMutualAllRulesF_eq (envR : Env) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
    (streamRecs : Option (List (ConstantVal × List RecRule))) :
    ∀ (k : Nat),
      checkMutualAllRulesF (m := m) .plain (mkFEnv envR) b formers4 ctors4 streamRecs k
        = checkMutualAllRules (m := m) envR b formers4 ctors4 streamRecs k
  | 0 => rfl
  | k + 1 => by
    simp only [checkMutualAllRulesF, checkMutualAllRules, checkMutualMemberRulesF_eq,
      checkMutualAllRulesF_eq envR b formers4 ctors4 streamRecs k]

end MutualMirrors

theorem consMutualFormersF_mkFEnv :
    ∀ (fms : List MutualFormerA) (env : Env),
      consMutualFormersF fms (mkFEnv env) = mkFEnv (consMutualFormers fms env)
  | [], _ => rfl
  | f :: fs, env => by
    simp only [consMutualFormersF, consMutualFormers, push_mkFEnv,
      consMutualFormersF_mkFEnv fs ⟨.indInfo f.cvTa {} :: env.consts⟩]

theorem consMutualCtorsF_mkFEnv (nP : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (env : Env),
      consMutualCtorsF nP cs (mkFEnv env) = mkFEnv (consMutualCtors nP cs env)
  | [], _ => rfl
  | c :: cs, env => by
    simp only [consMutualCtorsF, consMutualCtors, push_mkFEnv,
      consMutualCtorsF_mkFEnv nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩]

theorem provisionMutualRecsF_mkFEnv (b : MutualBlock) (fms : List MutualFormerA) :
    ∀ (l : List (ConstantVal × Nat)) (env : Env),
      provisionMutualRecsF b fms l (mkFEnv env) = mkFEnv (provisionMutualRecs b fms l env)
  | [], _ => rfl
  | (cvRa, mIdx) :: rest, env => by
    simp only [provisionMutualRecsF, provisionMutualRecs, push_mkFEnv,
      provisionMutualRecsF_mkFEnv b fms rest _]

theorem storeMutualRecsF_mkFEnv (env₂ : Env) (b : MutualBlock) (fms : List MutualFormerA)
    (rulesOf : List (List (MutualCtor × Expr))) :
    ∀ (l : List (ConstantVal × Nat)) (env : Env),
      storeMutualRecsF (mkFEnv env₂) b fms rulesOf l (mkFEnv env)
        = mkFEnv (storeMutualRecs env₂ b fms rulesOf l env)
  | [], _ => rfl
  | (cvRa, mIdx) :: rest, env => by
    simp only [storeMutualRecsF, storeMutualRecs, push_mkFEnv, mkFEnv_find?_fun,
      storeMutualRecsF_mkFEnv env₂ b fms rulesOf rest _]

theorem mutualOpenedOkF_eq (env₀ : Env) (members : List (Name × Nat × Nat))
    (lps : List Name) (nP : Nat) (cty : Expr) (nF : Nat) (ks : List (RecFieldKind × Nat)) :
    mutualOpenedOkF .plain (mkFEnv env₀) members lps nP cty nF ks
      = mutualOpenedOk env₀ members lps nP cty nF ks := by
  simp only [mutualOpenedOkF, mutualOpenedOk, StructWalkers.plain, constsResolveF_eq] <;> rfl

theorem mutualFieldsOkF_eq (env₀ : Env) (members : List (Name × Nat × Nat))
    (lps : List Name) (nP : Nat) (ctorsA : List (ConstantVal × Nat))
    (kinds : List (List (RecFieldKind × Nat))) :
    mutualFieldsOkF .plain (mkFEnv env₀) members lps nP ctorsA kinds
      = mutualFieldsOk env₀ members lps nP ctorsA kinds := by
  simp only [mutualFieldsOkF, mutualFieldsOk, mutualOpenedOkF_eq] <;> rfl

/-! ### The mutual install's run bridges -/

/-- The block's shape guard is operation-free: it leaves the state
alone, and the pure twin takes the same branch. -/
theorem mutualShapeOkC_bind {β : Type} {b : MutualBlock} {k : Unit → CheckCM β}
    {s₀ s' : CState} {v : β}
    (h : (mutualShapeOk (m := CheckCM) b >>= k) s₀ = .ok (v, s')) :
    mutualShapeOk (m := CheckM) b = .ok () ∧ k () s₀ = .ok (v, s') := by
  unfold mutualShapeOk at h ⊢
  simp only [] at h ⊢
  by_cases h1 : b.blockNames.Nodup
  case neg => rw [if_neg h1] at h; exact absurd h throwC_bind_ok
  by_cases h2 : ((b.formers.all fun f => f.1.levelParams == b.lps) &&
      b.ctors.all fun c => c.cv.levelParams == b.lps) = true
  case neg =>
    rw [if_pos h1, if_neg h2] at h
    exact absurd h throwC_bind_ok
  by_cases h3 : (b.ctors.all fun c => decide (c.member < b.k)) = true
  case neg =>
    rw [if_pos h1, if_pos h2, if_neg h3] at h
    exact absurd h throwC_bind_ok
  by_cases h4 : mutualCtorsGrouped b.ctors = true
  case neg =>
    rw [if_pos h1, if_pos h2, if_pos h3, if_neg h4] at h
    exact absurd h throwC_bind_ok
  rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4] at h
  rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4]
  simp only [pure_bind] at h
  exact ⟨rfl, h⟩

/-- The kinds' classification at a mutual block is operation-free. -/
theorem classifyMutualKindsC_ok {members : List (Name × Nat × Nat)} {lps : List Name}
    {nP : Nat} {ctorsA : List (ConstantVal × Nat)} {s₀ s' : CState}
    {kinds : List (List (RecFieldKind × Nat))}
    (h : classifyMutualKinds (m := CheckCM) members lps nP ctorsA s₀ = .ok (kinds, s')) :
    s' = s₀ ∧ classifyMutualKinds (m := CheckM) members lps nP ctorsA = .ok kinds := by
  unfold classifyMutualKinds at h ⊢
  obtain ⟨ks, s₁, hu, h⟩ := bindC_ok h
  cases hk : ctorsA.mapM (mutualCtorKinds members lps nP) with
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

/-- One member's projection table at the cached driver. -/
theorem mutualMemberTableS_run {b : MutualBlock} {f : MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {mIdx : Nat}
    (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : mutualMemberTableF (m := CheckCM) .plain b f ctorsA sortss mIdx (mkFEnv env) s₀
      = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    mutualMemberTable (m := CheckM) b f ctorsA sortss mIdx env = .ok fe'.env := by
  unfold mutualMemberTableF at h
  unfold mutualMemberTable
  cases hoc : b.ownCtors mIdx with
  | nil =>
    rw [hoc] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, rfl⟩
  | cons x xs =>
    cases xs with
    | cons y ys =>
      rw [hoc] at h
      obtain ⟨rfl, rfl⟩ := pureC_ok h
      exact ⟨hwf, rfl, henv, rfl⟩
    | nil =>
      obtain ⟨J, c⟩ := x
      rw [hoc] at h
      simp only [] at h ⊢
      by_cases hz : (f.nIdx == 0) = true
      · rw [if_pos hz] at h
        rw [if_pos hz]
        obtain ⟨hres, hfe, henv', F, hF⟩ := checkStructProjTableS_run env henv hwf h
        refine ⟨hres, hfe, henv', ?_⟩
        rw [← checkStructProjTable_datF (F := F)]
        exact hF
      · rw [if_neg hz] at h
        rw [if_neg hz]
        obtain ⟨rfl, rfl⟩ := pureC_ok h
        exact ⟨hwf, rfl, henv, rfl⟩

/-- The table stage over the members. -/
theorem mutualTablesS_run {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ (l : List (MutualFormerA × Nat)) (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState},
      EnvWF env → CSOKF s₀ →
      mutualTablesF (m := CheckCM) .plain b ctorsA sortss l (mkFEnv env) s₀ = .ok (fe', s') →
      CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    unfold mutualTablesF at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, rfl⟩
  | (f, mIdx) :: rest, env, s₀, fe', s', henv, hwf, h => by
    unfold mutualTablesF at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindC_ok h
    obtain ⟨hwf₁, hfe₁, henv₁, hp₁⟩ := mutualMemberTableS_run env henv hwf hstep
    rw [hfe₁] at h
    obtain ⟨hwf', hfe', henv', hp'⟩ := mutualTablesS_run rest fe₁.env henv₁ hwf₁ h
    refine ⟨hwf', hfe', henv', ?_⟩
    unfold mutualTables
    simp only [Bind.bind, Except.bind]
    rw [hp₁]
    exact hp'

/-- **The formers' checks at the cached driver**: every member's
former is checked at the SAME index — the block's starting one — so
one memo invariant carries the whole stage, and the pure comparand is
`mutualFormerChecks` at that one environment. -/
theorem mutualFormerChecksS_run (hμ : mode.verifiedChecks = true) {nP : Nat} :
    ∀ (l : List (ConstantVal × Nat)) (env : Env) {s₀ : CState}
      {fms : List MutualFormerA} {s' : CState},
      EnvWF env → CSOK mode env s₀ →
      mutualFormerChecksS mode (mkFEnv env) nP l s₀ = .ok (fms, s') →
      CSOK mode env s' ∧ (∀ f ∈ fms, f.cvTa.type.hasFvar = false) ∧
      ∃ F, mutualFormerChecks (fueledOps mode F) env nP l = .ok fms
  | [], env, s₀, fms, s', _, hs, h => by
    unfold mutualFormerChecksS at h
    obtain ⟨hr, rfl⟩ := pureC_ok h
    subst hr
    exact ⟨hs, (fun f hf => nomatch hf), 0, rfl⟩
  | (cv, nIdx) :: rest, env, s₀, fms, s', henv, hs, h => by
    unfold mutualFormerChecksS at h
    -- the constant check and official's telescope, both at `env`
    rw [checkConstantValF_eq] at h
    obtain ⟨cvTa₀, s₂, hcv, h⟩ := bindC_ok h
    obtain ⟨hs₂, cvTa₀', hP₀, F₁, hF₁⟩ := (checkConstantValS_sim hμ henv hs) cvTa₀ s₂ hcv
    obtain ⟨rfl, hw₀⟩ := hP₀
    rw [checkSumTeleF_pushC] at h
    obtain ⟨q, s₃, hte, h⟩ := bindC_ok h
    obtain ⟨hs₃, q', hPq, F₂, hF₂⟩ := (checkSumTeleS_sim hμ henv hs₂ hw₀) q s₃ hte
    obtain ⟨rfl, hwT⟩ := hPq
    obtain ⟨cvTa, sx⟩ := q
    simp only [] at h
    -- the pure guards
    cases hst : cvTa.type.stripPis (nP + nIdx) with
    | none =>
      rw [hst] at h
      simp only [unwrapOr] at h
      exact absurd h throwC_bind_ok
    | some tq =>
    rw [hst] at h
    simp only [unwrapOr, pure_bind] at h
    obtain ⟨tbs, tbody⟩ := tq
    by_cases hb : (tbody == Expr.sort sx) = true
    case neg =>
      rw [if_neg hb] at h
      exact absurd h throwC_bind_ok
    rw [if_pos hb] at h
    have hF₂p : checkSumTele (fueledOps mode (max F₁ F₂)) env cv (nP + nIdx) cvTa₀
        = .ok (cvTa, sx) := by
      rw [← checkSumTele_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
    have hF₁p : checkConstantVal (fueledOps mode (max F₁ F₂)) env cv = .ok cvTa₀ := by
      rw [← checkConstantVal_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
    obtain ⟨cv', hccv'⟩ : ∃ cv',
        checkConstantVal (fueledOps mode (max F₁ F₂)) env cv' = .ok cvTa := by
      rcases checkSumTele_shape hF₂p with ⟨rfl, -⟩ | ⟨ty, hccv⟩
      · exact ⟨cv, hF₁p⟩
      · exact ⟨{ cv with type := ty }, hccv⟩
    have hTf : cvTa.type.hasFvar = false := (checkConstantVal_typeWF hccv').1
    -- the rest of the stage, at the SAME environment
    obtain ⟨q2, s₄, hrec, h⟩ := bindC_ok h
    obtain ⟨hs₄, hall, F₃, hF₃⟩ := mutualFormerChecksS_run hμ rest env henv hs₃ hrec
    obtain ⟨hr, rfl⟩ := pureC_ok h
    subst hr
    obtain ⟨G, hle₁, hle₂, hle₃⟩ : ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G :=
      ⟨max F₁ (max F₂ F₃), by omega, by omega, by omega⟩
    refine ⟨hs₄, ?_, G, ?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hTf
      · exact hall f hf
    · have g₁ : checkConstantVal (fueledOps mode G) env cv = .ok cvTa₀ := by
        rw [← checkConstantVal_datF]; exact FueledM.up hle₁ hF₁
      have g₂ : checkSumTele (fueledOps mode G) env cv (nP + nIdx) cvTa₀ = .ok (cvTa, sx) := by
        rw [← checkSumTele_datF]; exact FueledM.up hle₂ hF₂
      have g₃ : mutualFormerChecks (fueledOps mode G) env nP rest = .ok q2 := by
        rw [← mutualFormerChecks_datF]
        exact FueledM.up hle₃ (by rw [mutualFormerChecks_datF]; exact hF₃)
      unfold mutualFormerChecks
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [g₁]
      simp only [Except.bind]
      rw [g₂]
      simp only [Except.bind, unwrapOr, hst, if_pos hb]
      rw [g₃]
      simp only [pure, Except.pure, Except.bind, if_pos hb]

/-- The formers' stage at the cached driver: ONE flush entering it,
the checks at that index, the conses after them. -/
theorem mutualFormersS_run (hμ : mode.verifiedChecks = true) {nP : Nat}
    (l : List (ConstantVal × Nat)) (env : Env) {s₀ : CState}
    {r : FEnv × List MutualFormerA} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : mutualFormersS mode nP l (mkFEnv env) s₀ = .ok (r, s')) :
    CSOKF s' ∧ r.1 = mkFEnv r.1.env ∧ EnvWF r.1.env ∧
    (∀ f ∈ r.2, f.cvTa.type.hasFvar = false) ∧
    ∃ F, mutualFormers (fueledOps mode F) nP l env = .ok (r.1.env, r.2) := by
  unfold mutualFormersS at h
  obtain ⟨u, s₁, hfl, h⟩ := bindC_ok h
  rw [flushC_run] at hfl
  injection hfl with hfl
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hfl
  obtain ⟨fms, s₂, hchk, h⟩ := bindC_ok h
  obtain ⟨hs₂, hTfs, F, hF⟩ := mutualFormerChecksS_run hμ l env henv (flushC_csok hwf) hchk
  obtain ⟨hr, rfl⟩ := pureC_ok h
  subst hr
  simp only []
  rw [consMutualFormersF_mkFEnv]
  refine ⟨hs₂.residue, rfl, ?_, hTfs, F, ?_⟩
  · exact envWF_consMutualFormers henv (mutualFormerChecks_typeWF hF)
  · unfold mutualFormers
    simp only [Bind.bind, Except.bind, pure, Except.pure, hF, mkFEnv_env]

/-- A `getD` is a member or the default. -/
private theorem getD_mem_or_default {α : Type} [Inhabited α] (l : List α) (i : Nat) :
    l.getD i default ∈ l ∨ l.getD i default = default := by
  rw [List.getD_eq_getElem?_getD]
  cases hm : l[i]? with
  | none => exact Or.inr rfl
  | some x => exact Or.inl (by simpa using List.mem_of_getElem? hm)

/-- **The mutual install at the cached driver is reproduced by the pure
fueled `checkMutualCore`** (task #278): the formers' flushing fold, the
cross-member checks at the formers' environment, the constructors
there too, the recursors at the constructors' environment and the
tables on top. -/
theorem checkMutualCoreS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {b : MutualBlock} {streamRecs : Option (List (ConstantVal × List RecRule))}
    {s₀ : CState} (hwf : CSOKF s₀) {feOut : FEnv} {s' : CState}
    (h : checkMutualCoreS mode (mkFEnv env) b streamRecs s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkMutualCore (fueledOps mode F) env b streamRecs = .ok feOut.env := by
  unfold checkMutualCoreS at h
  simp only [] at h
  rw [structWalkersC_eq_plain] at h
  -- 0. the block's shape
  obtain ⟨hshapeP, h⟩ := mutualShapeOkC_bind h
  -- 1. the formers, each at the index it is pushed onto
  obtain ⟨r1, s₁, hform, h⟩ := bindC_ok h
  obtain ⟨fe₁, fms⟩ := r1
  obtain ⟨hwf₁, hfe₁, henv₁, hTfs, F₁, hF₁⟩ :=
    mutualFormersS_run hμ b.formers env henv hwf hform
  simp only [] at hfe₁ henv₁ hTfs hF₁ h
  rw [hfe₁] at h
  -- the first member
  cases hf₀ : fms[0]? with
  | none =>
    rw [hf₀] at h
    simp only [unwrapOr] at h
    exact absurd h throwC_bind_ok
  | some f₀ =>
  rw [hf₀] at h
  simp only [unwrapOr, pure_bind] at h
  -- the flush entering the cross-member checks
  obtain ⟨u1, sB, hfl1, h⟩ := bindC_ok h
  rw [flushC_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  have hf₀mem : f₀ ∈ fms := List.mem_of_getElem? hf₀
  have hf₀f : f₀.cvTa.type.hasFvar = false := hTfs f₀ hf₀mem
  cases htq₀ : openPisAtFvars b.nP f₀.cvTa.type 0 with
  | none =>
    rw [htq₀] at h
    simp only [unwrapOr] at h
    exact absurd h throwC_bind_ok
  | some tq₀ =>
  rw [htq₀] at h
  simp only [unwrapOr, pure_bind] at h
  obtain ⟨htq₀W, -⟩ := openPisAtFvars_WScoped b.nP f₀.cvTa.type 0 htq₀
    (Expr.WScoped.of_not_hasFvar hf₀f)
  -- 2. the cross-member checks
  obtain ⟨u2, s₂, hcross, h⟩ := bindC_ok h
  obtain ⟨hs₂, u2', -, F₂, hF₂⟩ :=
    (mutualCrossChecksS_sim hμ henv₁
      (fun i x hx => by
        rw [List.getElem?_map] at hx
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨ty, rfl⟩ := openPisAtFvars_index b.nP f₀.cvTa.type 0 htq₀ i y hy
        have hw := htq₀W _ (List.mem_of_getElem? hy)
        simp only [Expr.WScoped] at hw
        rw [Nat.zero_add] at hw
        exact hw.2)
      (flushC_csok hwf₁)
      (fun f hf => Expr.WScoped.of_not_hasFvar (hTfs f hf))) u2 s₂ hcross
  -- the eliminator's level parameters
  by_cases hlg : (b.large == f₀.s.isNeverZero) = true
  case neg =>
    rw [if_neg hlg] at h
    exact absurd h throwC_bind_ok
  rw [if_pos hlg] at h
  -- 3. the constructors at the formers' environment
  rw [checkMutualCtorsF_eq] at h
  obtain ⟨r3, s₃, hctors, h⟩ := bindC_ok h
  obtain ⟨ctorsA, sortss⟩ := r3
  obtain ⟨hs₃, r3', hP3, F₃, hF₃⟩ :=
    (checkMutualCtorsS_sim hμ henv₁ (fms := fms)
      (fun m => by
        rcases getD_mem_or_default fms m with hm | hm
        · exact hTfs _ hm
        · rw [hm]; rfl) hs₂) (ctorsA, sortss) s₃ hctors
  obtain rfl : (ctorsA, sortss) = r3' := hP3
  have hF₃p : checkMutualCtors (fueledOps mode F₃) fe₁.env b fms
      (Level.isEquiv f₀.s .zero == some true) b.ctors = .ok (ctorsA, sortss) := by
    rw [← checkMutualCtors_datF]; exact hF₃
  -- the kinds, classified on the stored constructors
  simp only [] at h
  obtain ⟨kinds, s₄, hkinds, h⟩ := bindC_ok h
  obtain ⟨hs₄eq, hkindsP⟩ := classifyMutualKindsC_ok hkinds
  -- the kinds re-checked on the opened constructors
  rw [mutualFieldsOkF_eq] at h
  by_cases hfk : mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true
  case neg =>
    rw [if_neg hfk] at h
    exact absurd h throwC_bind_ok
  rw [if_pos hfk] at h
  -- 4. the recursors at the constructors' environment
  rw [consMutualCtorsF_mkFEnv] at h
  have henv₂ : EnvWF (consMutualCtors b.nP ctorsA fe₁.env) :=
    envWF_consMutualCtors henv₁ (checkMutualCtors_typeWF hF₃p)
  obtain ⟨u5, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : s₄.flushed = sC := congrArg Prod.snd hfl2
  rw [checkMutualRecTysF_eq] at h
  obtain ⟨cvRas, s₅, hrectys, h⟩ := bindC_ok h
  obtain ⟨hs₅, cvRas', hP5, F₅, hF₅⟩ :=
    (checkMutualRecTysS_sim hμ henv₂ (flushC_csok (hs₄eq ▸ hs₃.residue))) cvRas s₅ hrectys
  obtain rfl : cvRas = cvRas' := hP5
  have hF₅p : checkMutualRecTys (fueledOps mode F₅) (consMutualCtors b.nP ctorsA fe₁.env) b
      (mutualGenData b fms ctorsA kinds).1 (mutualGenData b fms ctorsA kinds).2 streamRecs b.k
      = .ok cvRas := by
    rw [← checkMutualRecTys_datF]; exact hF₅
  rw [provisionMutualRecsF_mkFEnv, checkMutualAllRulesF_eq] at h
  obtain ⟨rulesOf, s₆, hrules, h⟩ := bindC_ok h
  obtain ⟨hs₆, rulesOf', hP6, F₆, hF₆⟩ := (checkMutualAllRulesS_sim hs₅) rulesOf s₆ hrules
  obtain rfl : rulesOf = rulesOf' := hP6
  have hF₆p : checkMutualAllRules (m := CheckM)
      (provisionMutualRecs b fms cvRas.zipIdx (consMutualCtors b.nP ctorsA fe₁.env)) b
      (mutualGenData b fms ctorsA kinds).1 (mutualGenData b fms ctorsA kinds).2 streamRecs b.k
      = .ok rulesOf := by
    rw [← checkMutualAllRules_datF]; exact hF₆
  have henv₃ : EnvWF (storeMutualRecs (consMutualCtors b.nP ctorsA fe₁.env) b fms rulesOf
      cvRas.zipIdx (consMutualCtors b.nP ctorsA fe₁.env)) := mutual_recs_wf henv₂ hF₅p hF₆p
  -- 5. the projection tables
  rw [storeMutualRecsF_mkFEnv] at h
  obtain ⟨u7, sD, hfl3, h⟩ := bindC_ok h
  rw [flushC_run] at hfl3
  injection hfl3 with hfl3
  obtain rfl : s₆.flushed = sD := congrArg Prod.snd hfl3
  obtain ⟨hwfO, hfeO, -, hF₇⟩ := mutualTablesS_run fms.zipIdx _ henv₃ hs₆.residue.flushed h
  -- the pure run, at the joined fuel
  obtain ⟨G, hle₁, hle₂, hle₃, hle₅⟩ : ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G ∧ F₅ ≤ G :=
    ⟨max F₁ (max F₂ (max F₃ F₅)), by omega, by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₁ : mutualFormers (fueledOps mode G) b.nP b.formers env = .ok (fe₁.env, fms) := by
    rw [← mutualFormers_datF]
    exact FueledM.up hle₁ (by rw [mutualFormers_datF]; exact hF₁)
  have g₂ : mutualCrossChecks (fueledOps mode G) fe₁.env b.nP f₀
      (tq₀.1.map Expr.fvarTypeD) fms = .ok () := by
    rw [← mutualCrossChecks_datF]
    exact FueledM.up hle₂ hF₂
  have g₃ : checkMutualCtors (fueledOps mode G) fe₁.env b fms
      (Level.isEquiv f₀.s .zero == some true) b.ctors = .ok (ctorsA, sortss) := by
    rw [← checkMutualCtors_datF]; exact FueledM.up hle₃ hF₃
  have g₅ : checkMutualRecTys (fueledOps mode G) (consMutualCtors b.nP ctorsA fe₁.env) b
      (mutualGenData b fms ctorsA kinds).1 (mutualGenData b fms ctorsA kinds).2 streamRecs b.k
      = .ok cvRas := by
    rw [← checkMutualRecTys_datF]; exact FueledM.up hle₅ hF₅
  unfold checkMutualCore
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [hshapeP]
  simp only [Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind, pure, Except.pure, unwrapOr, hf₀, htq₀]
  rw [g₂]
  simp only [Except.bind, pure, Except.pure, if_pos hlg]
  rw [g₃]
  simp only [Except.bind, pure, Except.pure]
  rw [hkindsP]
  simp only [Except.bind, pure, Except.pure, if_pos hfk]
  rw [g₅]
  simp only [Except.bind, pure, Except.pure]
  rw [hF₆p]
  simp only [Except.bind, pure, Except.pure]
  exact hF₇

/-- **The recognised mutual block at the cached driver is reproduced by
the pure fueled `checkMutual`.** -/
theorem checkMutualS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p : MutualParts} {s₀ : CState} (hwf : CSOKF s₀) {feOut : FEnv} {s' : CState}
    (h : checkMutualS mode (mkFEnv env) p s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkMutual (fueledOps mode F) env p = .ok feOut.env := by
  unfold checkMutualS at h
  simp only [] at h
  by_cases hpin : p.recPinned = true
  case neg =>
    rw [if_neg hpin] at h
    exact absurd h throwC_bind_ok
  rw [if_pos hpin] at h
  obtain ⟨hres, hfe, F, hF⟩ := checkMutualCoreS_run hμ henv hwf h
  refine ⟨hres, hfe, F, ?_⟩
  unfold checkMutual
  simp only [Bind.bind, Except.bind, pure, Except.pure, if_pos hpin]
  exact hF

/-- The inductive-block dispatch of the cached driver: a RECOGNISED
fixpoint block goes to `checkNativeS`, a recognised MUTUAL block to
`checkMutualS` (task #278), everything else to `checkIndDeclSF`, and
either way the pure fueled `checkDecl` reproduces the run. -/
theorem checkModeledOrNativeSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {nP : Nat} (hpin : basisPinHit block = none)
    (hok : indParamsOk nP block = true)
    {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match nativeParts? nP block with
          | some p => checkNativeS mode (mkFEnv env) p
          | none =>
            match mutualParts? nP block with
            | some q => checkMutualS mode (mkFEnv env) q
            | none => checkIndDeclSF mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) pins env (.indDecl block nP) =
      .ok feOut.env := by
  -- the declared parameter count (task #228) is a pure guard shared by
  -- the two drivers: `hok` is the branch both take
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match basisPinHit block with
      | some kind => checkBasisDecl (m := CheckM) env kind
      | none =>
        if indParamsOk nP block = true then
          (match nativeParts? nP block with
            | some p => checkNative (fueledOps mode F) env p
            | none =>
              match mutualParts? nP block with
              | some q => checkMutual (fueledOps mode F) env q
              | none => checkModeled mode (fueledOps mode F) env block)
        else throw (CheckError.invalid "number of parameters mismatch")) = .ok feOut.env
  -- task #293: this block is not one of the five pinned ones (the
  -- recognition happened before the dispatch, on both sides)
  simp only [hpin, if_pos hok]
  cases hfp : nativeParts? nP block with
  | some p =>
    rw [hfp] at h
    obtain ⟨hres, hfe, F, hF⟩ := checkNativeS_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩
  | none =>
    rw [hfp] at h
    cases hmp : mutualParts? nP block with
    | some q =>
      rw [hmp] at h
      obtain ⟨hres, hfe, F, hF⟩ := checkMutualS_run hμ henv hwf h
      exact ⟨hres, hfe, F, hF⟩
    | none =>
      rw [hmp] at h
      obtain ⟨hres, hfe, F, hF⟩ := checkIndDeclSF_run hμ henv hwf h
      exact ⟨hres, hfe, F, hF⟩

end ConLeche.Cached
