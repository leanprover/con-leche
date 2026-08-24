import Setlec.Model.DirectExtend
import Setlec.Model.Extend.Proj

/-!
# The direct simple-structure install: environment assembly

`checkDirectStruct` (`Setlec/Kernel/Checker.lean`, task #82) installs a
recognised simple structure — the type former, the constructor, the
recursor with its single rule and the `nF` projection functions — from
the reference checks alone, and this module carries the corresponding
model extension, one constant at a time (`extend_basis_one`, then
`extend_rec_swap` for the rule-carrying members).

The values are the constructed ones of `Setlec/Model/DirectInstall.lean`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-! ### Inversions of the direct install stages -/

/-- Inversion for `checkDirectInd` (stage 1). -/
theorem checkDirectInd_inv {env : Env} {p : DirectParts} {F : Nat}
    {v : Env × ConstantVal}
    (h : checkDirectInd (fueledOps F) env p = .ok v) :
    ∃ cvTa bs, checkConstantVal (fueledOps F) env p.cvT = .ok cvTa ∧
      Expr.stripPis p.nP cvTa.type = some (bs, .sort p.resSort) ∧
      v = (⟨.indInfo cvTa (directCaps p) :: env.consts⟩, cvTa) := by
  rw [checkDirectInd] at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨cvTa, hcv, h⟩ := Except.bind_ok h
  refine ⟨cvTa, ?_⟩
  cases hst : Expr.stripPis p.nP cvTa.type with
  | none =>
    rw [hst] at h
    simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  | some q =>
    obtain ⟨tbs, tbody⟩ := q
    rw [hst] at h
    simp only [unwrapOr, pure, Except.pure, Except.bind] at h
    by_cases h1 : (tbody == Expr.sort p.resSort) = true
    · obtain rfl : tbody = Expr.sort p.resSort := eq_of_beq h1
      rw [if_pos h1] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨tbs, hcv, rfl, h.symm⟩
    · rw [if_neg h1] at h
      simp only [throw, throwThe, MonadExceptOf.throw] at h
      exact nomatch h

/-- The frame conditions of a constant type that `checkConstantVal` has
just accepted: closed, so the syntactic three are free, and the checker's
own annotation and inference runs supply the two semantic ones. -/
theorem FrameOk.ofCheckedType {env : Env} (m : EnvModel V env) {F : Nat}
    {φ : Name → Nat} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps F) env cv = .ok cv') :
    FrameOk V m.val env φ 0 (rho0 V) cv'.type := by
  obtain ⟨-, -, -, -, hlb, hfv, tyA, stype, u, hann, -, -, hst, -,
    hcvA⟩ := checkConstantVal_inv h
  have htypeA : cv'.type = tyA := by rw [hcvA]
  have htyf : tyA.hasFvar = false :=
    not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F _ hann (WScoped.of_not_hasFvar hfv)).fvarsBelow)
  have htyb : tyA.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F _ hann hlb
  have hAty : AnnotOk V m.val env φ 0 (rho0 V) tyA :=
    annotate_sound m _ hann (WScoped.of_not_hasFvar hfv) hlb
      (Expr.LeavesBounded.of_not_hasFvar hfv) (rho0 V)
      (FvarsOk.of_not_hasFvar hfv)
  obtain ⟨⟨v, tv, hvi, -, -⟩, -, -⟩ :=
    inferTypeCore_sound (φ := φ) m F hst (WScoped.of_not_hasFvar htyf) htyb
      (Expr.LeavesBounded.of_not_hasFvar htyf)
      (FvarsOk.of_not_hasFvar htyf) hAty
  rw [htypeA]
  exact ⟨WScoped.of_not_hasFvar htyf, htyb,
    Expr.LeavesBounded.of_not_hasFvar htyf, FvarsOk.of_not_hasFvar htyf,
    hAty, v, hvi⟩

/-! ### Uninstantiating a value-spine fit's levels

The capability laws quantify over a level substitution (`us` for the
constant's own parameters) and state the telescope fit over the
*substituted* type; the constructed values are indexed by the composed
assignment.  This moves the fit back to the raw telescope, exactly as
`TeleFitI.instLev_down` does for expression spines. -/

theorem TeleFit.instLev_down {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {ks : List Name} {lvs : List Level} (hcp : ConstValParams cval env) :
    ∀ {vs : List V} {d : Nat} {ρ : Nat → V} {e : Expr} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ (e.instantiateLevelParams ks lvs) vs d' ρ'
        rest →
      ∃ rest₂, TeleFit V cval env (Level.substFn φ ks lvs) d ρ e vs d' ρ'
        rest₂ := by
  intro vs
  induction vs with
  | nil =>
    intro d ρ e d' ρ' rest hfit
    generalize e.instantiateLevelParams ks lvs = E at hfit
    cases hfit
    exact ⟨e, TeleFit.nil⟩
  | cons x xs ih =>
    intro d ρ e d' ρ' rest hfit
    match e with
    | .forallE n ty body mb =>
      rw [Expr.instantiateLevelParams] at hfit
      cases hfit with
      | @cons _ _ _ _ _ _ _ _ _ _ _ A hity hx hsub =>
        rw [interp_instLevels hcp] at hity
        rw [← instantiateLevelParams_instantiate1] at hsub
        obtain ⟨rest₂, h₂⟩ := ih hsub
        exact ⟨rest₂, TeleFit.cons hity hx h₂⟩
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      rw [Expr.instantiateLevelParams] at hfit
      exact nomatch hfit

/-! ### Stage 1: the type former -/

/-- Extend a model by a direct simple structure's **type former**: an
opaque inductive-kind constant valued by the guarded dependent-pair
tower over the constructor's field telescope (`directTyVal`).

Its membership obligation is unconditional — that is what the guard in
`directTyBody` buys — so the only capability law with content is the
unit-like one, and only for a field-free structure, where the tower is
the singleton. -/
theorem extend_direct_ind {env : Env} (m : EnvModel V env) {p : DirectParts}
    {cvTa : ConstantVal} {F : Nat} {cty : Expr}
    {bs : List (Name × Expr × BinderMeta)}
    (hccv : checkConstantVal (fueledOps F) env p.cvT = .ok cvTa)
    (hstrip : Expr.stripPis p.nP cvTa.type = some (bs, .sort p.resSort))
    (hctyP : cty.allLevelParamsDefined cvTa.levelParams = true)
    -- from `directNoModel`, part of recognition: the block is the
    -- artifact-free route, so the type former has no companion and the
    -- artifact linkage is vacuous for it
    (_hnomodel : (env.find? (p.cvT.name.str "_model")).isNone = true) :
    ∃ m₁ : EnvModel V ⟨.indInfo cvTa (directCaps p) :: env.consts⟩,
      (∀ ψ, m₁.val cvTa.name ψ =
        directTyVal V m.val env cvTa.type cty p.nP p.nF p.resSort ψ) ∧
      (∀ n ψ, n ≠ cvTa.name → m₁.val n ψ = m.val n ψ) := by
  obtain ⟨hfind0, hnres0, hpshape0, hnd, hlb, hfv, tyA, stype, u,
    hann, hlp, hres, hst, hsort, hcvA⟩ := checkConstantVal_inv hccv
  have hnameA : cvTa.name = p.cvT.name := by rw [hcvA]
  have hlpsA : cvTa.levelParams = p.cvT.levelParams := by rw [hcvA]
  have htypeA : cvTa.type = tyA := by rw [hcvA]
  have hfind' : env.find? cvTa.name = none := by rw [hnameA]; exact hfind0
  have hnres : reservedBasisNames.contains cvTa.name = false := by
    rw [hnameA]; exact hnres0
  have hshapeA : cvTa.name.isProjFnShape = false := by
    rw [hnameA]; exact hpshape0
  have htyf : cvTa.type.hasFvar = false := by
    rw [htypeA]
    exact not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F _ hann (WScoped.of_not_hasFvar hfv)).fvarsBelow)
  have htyb : cvTa.type.looseBVarsBounded 0 = true := by
    rw [htypeA]; exact annotateCore_looseBVars F _ hann hlb
  have htlp : cvTa.type.allLevelParamsDefined cvTa.levelParams = true := by
    rw [htypeA, hlpsA]; exact hlp
  have htres : cvTa.type.constsResolve env = true := by rw [htypeA]; exact hres
  have hAty : ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) cvTa.type := by
    intro ψ
    rw [htypeA]
    exact annotate_sound m _ hann (WScoped.of_not_hasFvar hfv) hlb
      (Expr.LeavesBounded.of_not_hasFvar hfv) (rho0 V)
      (FvarsOk.of_not_hasFvar hfv)
  have htyfA : tyA.hasFvar = false := by rw [← htypeA]; exact htyf
  have hityI : ∀ ψ : Name → Nat, ∃ Tv,
      interpExpr V m.val env ψ 0 (rho0 V) cvTa.type = some Tv := by
    intro ψ
    have hAtyA : AnnotOk V m.val env ψ 0 (rho0 V) tyA := by
      rw [← htypeA]; exact hAty ψ
    obtain ⟨⟨v, tv, hvi, -, -⟩, -, -⟩ :=
      inferTypeCore_sound (φ := ψ) m F hst
        (WScoped.of_not_hasFvar htyfA)
        (by rw [← htypeA]; exact htyb)
        (Expr.LeavesBounded.of_not_hasFvar htyfA)
        (FvarsOk.of_not_hasFvar htyfA) hAtyA
    exact ⟨v, by rw [htypeA]; exact hvi⟩
  have hsP : p.resSort.allParamsDefined cvTa.levelParams = true := by
    have h := allLevelParamsDefined_stripPis_body p.nP hstrip htlp
    simpa [Expr.allLevelParamsDefined] using h
  have hnresI : reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa (directCaps p)).name = false := hnres
  have hwf : ConstWF ⟨.indInfo cvTa (directCaps p) :: env.consts⟩
      (.indInfo cvTa (directCaps p)) := by
    refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_, ?_⟩
    · intro cv2 v2 h2 heq; exact nomatch heq
    · intro cv2 mI' rP' rules heq; exact nomatch heq
    · intro cv2 v2 heq; exact nomatch heq
  refine extend_basis_one m (.indInfo cvTa (directCaps p))
    (fun ψ => directTyVal V m.val env cvTa.type cty p.nP p.nF p.resSort ψ)
    hfind' hwf htres (fun cv2 value2 h2 heq => nomatch heq) ?_ ?_ hAty
    (fun cv caps heq hn => absurd (hn ▸ hnresI) (by decide))
    (fun cv nP nF heq _ => nomatch heq)
    (fun cv caps heq hn => absurd (hn ▸ hnresI) (by decide))
    (fun hn => absurd (hn ▸ hnresI) (by decide))
    (fun _ hres2 => absurd (hres2 ▸ hnresI) (by simp))
    (fun cv mI rP rules heq => nomatch heq)
    (fun val' _ _ cvR mI rP rules heq => nomatch heq)
    (fun cvR mI rP rules heq => nomatch heq)
    (fun entry heq _ => nomatch heq)
    (hnotthm := fun cv2 value2 h => ConstantInfo.noConfusion h)
    (hcaps := fun val' _ _ => by
      refine ⟨?_, ?_⟩
      · intro T cvT capsT hfT hcape hresT hfam hpart
        exfalso
        rcases hpart with rfl | hC | ⟨j, hj, hP⟩
        · rw [Env.find?_cons, if_pos rfl] at hfT
          obtain heq2 := Option.some.inj hfT
          injection heq2 with h1 h2
          rw [← h2] at hcape
          simp [directCaps] at hcape
        · obtain ⟨-, ⟨cvC2, hfC⟩, -⟩ := hfam
          rw [hC, Env.find?_cons, if_pos rfl] at hfC
          exact nomatch (Option.some.inj hfC)
        · have hP' : projFnName T j = cvTa.name := hP
          rw [← hP'] at hshapeA
          simp [projFnName, Name.isProjFnShape] at hshapeA
      · intro cv caps heq hcapu _
        injection heq with h1 h2
        rw [← h2] at hcapu
        simp [directCaps] at hcapu)
  · -- `mem_type`
    intro ψ
    obtain ⟨Tv, hTv⟩ := hityI ψ
    exact ⟨Tv, hTv, directTyVal_mem hstrip hTv (hAty ψ)⟩
  · -- `val_params`
    intro ψ₁ ψ₂ hψ
    exact directTyVal_params m.val_params (ps := cvTa.levelParams) hψ
      htlp hctyP hsP

/-- Inversion for `checkDirectDomsAt`. -/
theorem checkDirectDomsAt_inv {env : Env} {F off : Nat}
    {fvs doms : List Expr} :
    ∀ (k : Nat),
      checkDirectDomsAt (fueledOps F) env off fvs doms k = .ok () →
      ∀ j, j < k → ∀ a b, fvs[j]? = some a → doms[j]? = some b →
        isDefEqCore env F (off + j) (Expr.fvarTypeD a) b = .ok true := by
  intro k
  induction k with
  | zero => intro _ j hj; exact absurd hj (by omega)
  | succ k ih =>
    intro h j hj a b ha hb
    rw [checkDirectDomsAt] at h
    simp only [fueledOps_isDefEq, Bind.bind, Except.bind, unwrapOr] at h
    cases hca : fvs[k]? with
    | none => rw [hca] at h; exact nomatch h
    | some a₀ =>
      rw [hca] at h
      simp only [pure, Except.pure] at h
      cases hcb : doms[k]? with
      | none => rw [hcb] at h; exact nomatch h
      | some b₀ =>
        rw [hcb] at h
        simp only [pure, Except.pure] at h
        cases hde : isDefEqCore env F (off + k) (Expr.fvarTypeD a₀) b₀ with
        | error _ => rw [hde] at h; exact nomatch h
        | ok v =>
          rw [hde] at h
          cases v with
          | false =>
            simp only [Bool.false_eq_true, if_false, throw, throwThe,
              MonadExceptOf.throw] at h
            exact nomatch h
          | true =>
            simp only [if_true] at h
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
            · exact ih h j hj' a b ha hb
            · obtain rfl : a₀ = a := Option.some.inj (hca.symm.trans ha)
              obtain rfl : b₀ = b := Option.some.inj (hcb.symm.trans hb)
              exact hde

/-- Inversion for `checkDirectCtor` (stage 2). -/
theorem checkDirectCtor_inv {env₀ env : Env} {p : DirectParts}
    {cvTa : ConstantVal} {F : Nat} {v : Env × ConstantVal}
    (h : checkDirectCtor (fueledOps F) env₀ env p cvTa = .ok v) :
    ∃ cvCa cbs fvsP crest tfvs trest xFvs,
      checkConstantVal (fueledOps F) env p.cvC = .ok cvCa ∧
      Expr.stripPis (p.nP + p.nF) cvCa.type =
        some (cbs, directFam p.cvT.name p.cvT.levelParams p.nP p.nF) ∧
      openPisAtFvars p.nP cvCa.type 0 = some (fvsP, crest) ∧
      openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest) ∧
      checkDirectDomsAt (fueledOps F) env 0 fvsP
        (tfvs.map Expr.fvarTypeD) p.nP = .ok () ∧
      openPisAtFvars p.nF crest p.nP = some (xFvs,
        Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
          fvsP) ∧
      (∀ x ∈ xFvs, (Expr.fvarTypeD x).constsResolve env₀ = true) ∧
      checkDirectFieldUniv (fueledOps F) env p.resSort p.nP xFvs p.nF
        = .ok () ∧
      v = (⟨.ctorInfo cvCa p.nP p.nF :: env.consts⟩, cvCa) := by
  rw [checkDirectCtor] at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨cvCa, hcv, h⟩ := Except.bind_ok h
  -- the annotated constructor telescope
  obtain ⟨q1, hq1⟩ : ∃ q, Expr.stripPis (p.nP + p.nF) cvCa.type = some q := by
    cases hh : Expr.stripPis (p.nP + p.nF) cvCa.type with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq1] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  by_cases hb : (q1.2 == directFam p.cvT.name p.cvT.levelParams p.nP p.nF)
      = true
  case neg =>
    rw [if_neg hb] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hb] at h
  have hq1b : Expr.stripPis (p.nP + p.nF) cvCa.type =
      some (q1.1, directFam p.cvT.name p.cvT.levelParams p.nP p.nF) := by
    rw [hq1]
    congr 1
    exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, eq_of_beq hb⟩ ▸ rfl
  -- the two openings
  obtain ⟨cq, hcq⟩ : ∃ q, openPisAtFvars p.nP cvCa.type 0 = some q := by
    cases hh : openPisAtFvars p.nP cvCa.type 0 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hcq] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨tq, htq⟩ : ∃ q, openPisAtFvars p.nP cvTa.type 0 = some q := by
    cases hh : openPisAtFvars p.nP cvTa.type 0 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [htq] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  -- the per-frame parameter-domain pins
  obtain ⟨u0, hpins, h⟩ := Except.bind_ok h
  obtain rfl : u0 = () := rfl
  -- the field telescope
  obtain ⟨xq, hxq⟩ : ∃ q, openPisAtFvars p.nF cq.2 p.nP = some q := by
    cases hh : openPisAtFvars p.nF cq.2 p.nP with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hxq] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  by_cases hr : (xq.2 == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1) = true
  case neg =>
    rw [if_neg hr] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hr] at h
  have hxqb : openPisAtFvars p.nF cq.2 p.nP = some (xq.1, Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1) := by
    rw [hxq]
    congr 1
    exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, eq_of_beq hr⟩ ▸ rfl
  by_cases hres : (xq.1.all fun x => (Expr.fvarTypeD x).constsResolve env₀)
      = true
  case neg =>
    rw [if_neg hres] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hres] at h
  obtain ⟨u1, hfu, h⟩ := Except.bind_ok h
  obtain rfl : u1 = () := rfl
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cvCa, q1.1, cq.1, cq.2, tq.1, tq.2, xq.1, hcv, hq1b, hcq, htq,
    hpins, hxqb, fun x hx => List.all_eq_true.mp hres x hx, hfu, h.symm⟩

/-- Inversion for `checkDirectRecTy` (stage 3): every intermediate the
model reads, with each pin at the frame it was checked at. -/
theorem checkDirectRecTy_inv {env : Env} {p : DirectParts}
    {cvTa cvCa cvRa : ConstantVal} {F : Nat} {v : Unit}
    (h : checkDirectRecTy (fueledOps F) env p cvTa cvCa cvRa = .ok v) :
    ∃ fvsP rest cdomsP crest mfv mbs mdom minfv xFvs cdomsF jbs,
      directShape p.cvT.name p.cvC.name p.cvT.levelParams p.elim p.nP p.nF
        cvTa.type cvCa.type cvRa.type = true ∧
      openPisAtFvars (p.nP + 2) cvRa.type 0 = some (fvsP, rest) ∧
      Expr.instPisAt (fvsP.take p.nP) cvCa.type = some (cdomsP, crest) ∧
      checkDirectDomsAt (fueledOps F) env 0 (fvsP.take p.nP) cdomsP p.nP
        = .ok () ∧
      fvsP[p.nP]? = some mfv ∧
      Expr.stripPis 1 (Expr.fvarTypeD mfv) =
        some (mbs, Expr.sort (.param p.elim)) ∧
      (mbs[0]?).map (·.2.1) = some mdom ∧
      isDefEqCore env F p.nP mdom
        (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
          (fvsP.take p.nP)) = .ok true ∧
      fvsP[p.nP + 1]? = some minfv ∧
      openPisAtFvars p.nF (Expr.fvarTypeD minfv) (p.nP + 2) = some (xFvs,
        Expr.app mfv (Expr.mkAppN
          (.const p.cvC.name (p.cvT.levelParams.map .param))
          (fvsP.take p.nP ++ xFvs))) ∧
      Expr.instPisAt xFvs crest = some (cdomsF,
        Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
          (fvsP.take p.nP)) ∧
      checkDirectDomsAt (fueledOps F) env (p.nP + 2) xFvs cdomsF p.nF
        = .ok () ∧
      Expr.stripPis 1 rest = some (jbs, Expr.app mfv (.bvar 0)) ∧
      ∃ jdom, (jbs[0]?).map (·.2.1) = some jdom ∧
        isDefEqCore env F (p.nP + 2) jdom
          (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
            (fvsP.take p.nP)) = .ok true := by
  rw [checkDirectRecTy] at h
  simp only [Bind.bind, Except.bind] at h
  by_cases hsh : directShape p.cvT.name p.cvC.name p.cvT.levelParams p.elim
      p.nP p.nF cvTa.type cvCa.type cvRa.type = true
  case neg =>
    rw [if_neg hsh] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hsh] at h
  obtain ⟨q1, hq1⟩ : ∃ q, openPisAtFvars (p.nP + 2) cvRa.type 0 = some q := by
    cases hh : openPisAtFvars (p.nP + 2) cvRa.type 0 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq1] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨q2, hq2⟩ : ∃ q, Expr.instPisAt (q1.1.take p.nP) cvCa.type
      = some q := by
    cases hh : Expr.instPisAt (q1.1.take p.nP) cvCa.type with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq2] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨u0, hpins1, h⟩ := Except.bind_ok h
  obtain rfl : u0 = () := rfl
  obtain ⟨mfv, hmfv⟩ : ∃ x, q1.1[p.nP]? = some x := by
    cases hh : q1.1[p.nP]? with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some x => exact ⟨x, rfl⟩
  rw [hmfv] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨q3, hq3⟩ : ∃ q, Expr.stripPis 1 (Expr.fvarTypeD mfv) = some q := by
    cases hh : Expr.stripPis 1 (Expr.fvarTypeD mfv) with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq3] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨mdom, hmdom⟩ : ∃ x, (q3.1[0]?).map (·.2.1) = some x := by
    cases hh : (q3.1[0]?).map (·.2.1) with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some x => exact ⟨x, rfl⟩
  rw [hmdom] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind, fueledOps_isDefEq] at h
  obtain ⟨b1, hb1, h⟩ := Except.bind_ok h
  cases b1 with
  | false =>
    simp only [Bool.false_eq_true, if_false, throw, throwThe,
      MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  | true =>
  simp only [if_true] at h
  by_cases hmb : (q3.2 == Expr.sort (.param p.elim)) = true
  case neg =>
    rw [if_neg hmb] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hmb] at h
  obtain ⟨minfv, hminfv⟩ : ∃ x, q1.1[p.nP + 1]? = some x := by
    cases hh : q1.1[p.nP + 1]? with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some x => exact ⟨x, rfl⟩
  rw [hminfv] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨q4, hq4⟩ : ∃ q, openPisAtFvars p.nF (Expr.fvarTypeD minfv)
      (p.nP + 2) = some q := by
    cases hh : openPisAtFvars p.nF (Expr.fvarTypeD minfv) (p.nP + 2) with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq4] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨q5, hq5⟩ : ∃ q, Expr.instPisAt q4.1 q2.2 = some q := by
    cases hh : Expr.instPisAt q4.1 q2.2 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq5] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨u1, hpins2, h⟩ := Except.bind_ok h
  obtain rfl : u1 = () := rfl
  by_cases hcr : (q5.2 == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param))
      (q1.1.take p.nP)) = true
  case neg =>
    rw [if_neg hcr] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hcr] at h
  by_cases hmc : (q4.2 == Expr.app mfv (Expr.mkAppN
      (.const p.cvC.name (p.cvT.levelParams.map .param))
      (q1.1.take p.nP ++ q4.1))) = true
  case neg =>
    rw [if_neg hmc] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hmc] at h
  obtain ⟨q6, hq6⟩ : ∃ q, Expr.stripPis 1 q1.2 = some q := by
    cases hh : Expr.stripPis 1 q1.2 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq6] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨jdom, hjdom⟩ : ∃ x, (q6.1[0]?).map (·.2.1) = some x := by
    cases hh : (q6.1[0]?).map (·.2.1) with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some x => exact ⟨x, rfl⟩
  rw [hjdom] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind, fueledOps_isDefEq] at h
  obtain ⟨b2, hb2, h⟩ := Except.bind_ok h
  cases b2 with
  | false =>
    simp only [Bool.false_eq_true, if_false, throw, throwThe,
      MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  | true =>
  simp only [if_true] at h
  by_cases hjb : (q6.2 == Expr.app mfv (.bvar 0)) = true
  case neg =>
    rw [if_neg hjb] at h
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  refine ⟨q1.1, q1.2, q2.1, q2.2, mfv, q3.1, mdom, minfv, q4.1, q5.1, q6.1,
    hsh, hq1, hq2, hpins1, hmfv, ?_, hmdom, hb1, hminfv, ?_, ?_, hpins2,
    ?_, jdom, hjdom, hb2⟩
  · rw [hq3]; congr 1; exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, eq_of_beq hmb⟩
  · rw [hq4]; congr 1; exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, eq_of_beq hmc⟩
  · rw [hq5]; congr 1; exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, eq_of_beq hcr⟩
  · rw [hq6]; congr 1; exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, eq_of_beq hjb⟩

/-! ### The constructor's semantic obligations -/

/-- The field telescope is small at every fitting parameter spine: the
fit lands exactly where the install's own opening does
(`TeleFit_open`), carries the frame conditions there
(`FrameOk.ofTeleFit`), and the checked per-field universe bound then
gives `FieldTele` (`FieldTele_of_walk`). -/
theorem directCtor_field {env : Env} (m : EnvModel V env) {F : Nat}
    {φ : Name → Nat} {p : DirectParts} {cty crest resid : Expr}
    {fvsP xFvs : List Expr}
    (hcq : openPisAtFvars p.nP cty 0 = some (fvsP, crest))
    (hxq : openPisAtFvars p.nF crest p.nP = some (xFvs, resid))
    (hfu : checkDirectFieldUniv (fueledOps F) env p.resSort p.nP xFvs p.nF
      = .ok ())
    (hfr0 : FrameOk V m.val env φ 0 (rho0 V) cty)
    {ps : List V} {d₁ : Nat} {ρ₁ : Nat → V} {mid : Expr}
    (hfit : TeleFit V m.val env φ 0 (rho0 V) cty ps d₁ ρ₁ mid)
    (hlen : ps.length = p.nP) :
    FieldTele V m.val env φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid := by
  obtain ⟨hd₁, fvs, hopen⟩ := TeleFit_open p.nP hfit hlen
  rw [Nat.zero_add] at hd₁
  subst hd₁
  obtain rfl : mid = crest := by
    rw [hcq] at hopen
    exact ((Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hopen).2).symm
  refine FieldTele_of_walk (F := F) m p.nF p.nP ρ₁ _ xFvs resid hxq
    (FrameOk.ofTeleFit hfit hfr0) ?_
  intro j hj
  exact checkDirectFieldUniv_inv p.nF hfu j hj

/-- **The residual identity.**  The constructor's opened residual is
the family at the opened parameters, and its interpretation *is* the
dependent-pair tower the constructor's value tuples into.

The parameter fit crosses to the type former's telescope through the
per-frame pins (`DomsInterpEq.of_pins`, `TeleFit.transfer`) — landing
at the very same frame and valuation — so the family's value folds at
exactly these parameters (`directTyVal_fold`), and the tower it folds
to is the one read off the constructor's own opening. -/
theorem directCtor_resid {env env₁ : Env} (m : EnvModel V env)
    (m₁ : EnvModel V env₁) {F : Nat} {φ : Name → Nat} {p : DirectParts}
    {cvTa cvCa : ConstantVal} {crest trest : Expr}
    {fvsP tfvs xFvs : List Expr} {tbs : List (Name × Expr × BinderMeta)}
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsP, crest))
    (htq : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    (hpins : checkDirectDomsAt (fueledOps F) env₁ 0 fvsP
      (tfvs.map Expr.fvarTypeD) p.nP = .ok ())
    (hxq : openPisAtFvars p.nF crest p.nP = some (xFvs,
      Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param)) fvsP))
    (hfrC : FrameOk V m₁.val env₁ φ 0 (rho0 V) cvCa.type)
    (hfrT : FrameOk V m₁.val env₁ φ 0 (rho0 V) cvTa.type)
    (hTfind : env₁.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTval : ∀ ψ : Name → Nat, m₁.val p.cvT.name ψ =
      directTyVal V m.val env cvTa.type cvCa.type p.nP p.nF p.resSort ψ)
    (hagree : InterpAgree V m.val env m₁.val env₁ φ)
    (htres : cvTa.type.constsResolve env = true)
    (hfres : ∀ x ∈ xFvs, (Expr.fvarTypeD x).constsResolve env = true)
    (hstripT : Expr.stripPis p.nP cvTa.type = some (tbs, .sort p.resSort))
    {ps fs : List V} {d₁ : Nat} {ρ₁ : Nat → V} {mid : Expr}
    {d' : Nat} {ρ' : Nat → V} {rest : Expr}
    (hfitP : TeleFit V m₁.val env₁ φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid)
    (hlenP : ps.length = p.nP)
    (hfitF : TeleFit V m₁.val env₁ φ d₁ ρ₁ mid fs d' ρ' rest)
    (hlenF : fs.length = p.nF)
    (hfieldAt : FieldTele V m₁.val env₁ φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid) :
    interpExpr V m₁.val env₁ φ d' ρ' rest =
      some (sigmaTowerV V m₁.val env₁ φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid) := by
  -- the two openings the fits land at
  obtain ⟨hd₁, fvs, hopen⟩ := TeleFit_open p.nP hfitP hlenP
  rw [Nat.zero_add] at hd₁
  subst hd₁
  obtain rfl : mid = crest := by
    rw [hcq] at hopen
    exact ((Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hopen).2).symm
  obtain ⟨hd', fvs', hopen'⟩ := TeleFit_open p.nF hfitF hlenF
  subst hd'
  obtain rfl : rest = Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) fvsP := by
    rw [hxq] at hopen'
    exact ((Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hopen').2).symm
  -- the opened parameter variables interpret to the fit's own values
  obtain ⟨hinstP, hlenFv, hshape⟩ := openPisAtFvars_spec p.nP 0 hcq
  have hspine : InterpSpine m₁.val env₁ φ (p.nP + p.nF) ρ' fvsP ps := by
    refine InterpSpine.of_pointwise (by rw [hlenFv, hlenP]) ?_
    intro k a v ha hv
    have hkp : k < ps.length := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hv
      exact hlt
    obtain ⟨nm, hnm⟩ := hshape k a ha
    have hrho : ρ' k = v := by
      rw [hfitF.rho_below k (by rw [← hlenP]; exact hkp)]
      have h0 := hfitP.slots k hkp
      rw [Nat.zero_add] at h0
      rw [h0, List.getD_eq_getElem?_getD, hv]
      rfl
    rw [hnm]
    simp only [interpExpr, Nat.zero_add]
    rw [hrho]
  -- the residual's interpretation is the family's value at those params
  have hconst : interpExpr V m₁.val env₁ φ (p.nP + p.nF) ρ'
      (.const p.cvT.name (p.cvT.levelParams.map .param)) =
      some (m₁.val p.cvT.name φ) := by
    rw [interp_const hTfind (by
      show (p.cvT.levelParams.map Level.param).length =
        cvTa.levelParams.length
      rw [hTlps, List.length_map])]
    have hsub : Level.substFn φ
        (ConstantInfo.indInfo cvTa (directCaps p)).toConstantVal.levelParams
        (p.cvT.levelParams.map Level.param) = φ := by
      show Level.substFn φ cvTa.levelParams
        (p.cvT.levelParams.map Level.param) = φ
      rw [hTlps]
      exact funext (fun q => Level.substFn_map_param)
    rw [hsub]
  rw [interp_mkAppN fvsP _ hconst hspine]
  -- the family's value folds at these very parameters
  refine congrArg some ?_
  rw [hTval φ,
    directTyVal_congr hagree htres (by rw [directCRest, hcq]; exact hxq)
      (fun x hx => hfres x hx)]
  have hcrestEq : directCRest cvCa.type p.nP = mid := by
    rw [directCRest, hcq]
  rw [← hcrestEq]
  refine directTyVal_fold hstripT hfrT.an ?_ hlenP
    (by rw [hcrestEq]; exact hfieldAt)
  obtain ⟨dT, ρT, restT, hfitT⟩ := TeleFit.transfer p.nP hfitP hlenP
    (DomsInterpEq.of_pins m₁ F p.nP 0 (rho0 V) cvCa.type cvTa.type
      fvsP tfvs _ trest hcq htq
      (fun j a b ha hb => by
        have hj : j < p.nP := by
          obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
          rw [hlenFv] at hlt
          exact hlt
        refine checkDirectDomsAt_inv p.nP hpins j hj a (Expr.fvarTypeD b)
          ha ?_
        rw [List.getElem?_map, hb]
        rfl)
      hfrC hfrT)
  obtain rfl : restT = Expr.sort p.resSort :=
    TeleFit_rest_sort p.nP hfitT hlenP hstripT
  obtain ⟨hdT, -, -⟩ := TeleFit_open p.nP hfitT hlenP
  rw [Nat.zero_add] at hdT
  subst hdT
  rw [TeleFit.rho_det hfitT hfitP] at hfitT
  exact hfitT

/-- **The constructor's value inhabits its type.**  `directCtorVal_mem`
at the two obligations above: the field telescope is small at every
fitting parameter spine, and the residual interprets to the tower the
constructor tuples into. -/
theorem directCtor_mem {env env₁ : Env} (m : EnvModel V env)
    (m₁ : EnvModel V env₁) {F : Nat} {φ : Name → Nat} {p : DirectParts}
    {cvTa cvCa : ConstantVal} {v : Env × ConstantVal}
    (hcc : checkDirectCtor (fueledOps F) env env₁ p cvTa = .ok v)
    (hfrT : FrameOk V m₁.val env₁ φ 0 (rho0 V) cvTa.type)
    (hnz : p.resSort.isNonZero = true)
    {tbs : List (Name × Expr × BinderMeta)}
    (hstripT : Expr.stripPis p.nP cvTa.type = some (tbs, .sort p.resSort))
    (hTfind : env₁.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTval : ∀ ψ : Name → Nat, m₁.val p.cvT.name ψ =
      directTyVal V m.val env cvTa.type cvCa.type p.nP p.nF p.resSort ψ)
    (hagree : InterpAgree V m.val env m₁.val env₁ φ)
    (htres : cvTa.type.constsResolve env = true)
    (hccC : checkConstantVal (fueledOps F) env₁ p.cvC = .ok cvCa) :
    ∃ Cv, interpClosed V m₁.val env₁ φ cvCa.type = some Cv ∧
      directCtorVal V m₁.val env₁ cvCa.type p.nP p.nF φ ∈ˢ Cv := by
  obtain ⟨cvCa', cbs, fvsP, crest, tfvs, trest, xFvs, hcv, hstripC, hcq, htq,
    hpins, hxq, hfres, hfu, -⟩ := checkDirectCtor_inv hcc
  have heqC : cvCa' = cvCa := by
    rw [hccC] at hcv
    exact (Except.ok.injEq _ _ ▸ hcv).symm
  rw [heqC] at hstripC hcq
  have hfrC : FrameOk V m₁.val env₁ φ 0 (rho0 V) cvCa.type :=
    FrameOk.ofCheckedType m₁ hccC
  obtain ⟨Cv, hCv⟩ := hfrC.it
  refine ⟨Cv, hCv, ?_⟩
  refine directCtorVal_mem (by rw [hstripC]; rfl) hCv hfrC.an
    (directCtorVal_body (Level.isNonZero_sound hnz φ) ?_ ?_)
  · intro ps d₁ ρ₁ mid hfit hlen
    exact directCtor_field m₁ hcq hxq hfu hfrC hfit hlen
  · intro ps fs d₁ ρ₁ mid d' ρ' rest hfitP hlenP hfitF hlenF
    exact directCtor_resid m m₁ hcq htq hpins hxq hfrC hfrT hTfind hTlps
      hTval hagree htres hfres hstripT hfitP hlenP hfitF hlenF
      (directCtor_field m₁ hcq hxq hfu hfrC hfitP hlenP)

/-- Extend a model by a direct simple structure's **constructor**: an
opaque constructor-kind constant valued by the iterated Kuratowski
tuple of its field values (`directCtorVal`).

Every capability clause is vacuous: the block's own former claims
neither `eta` nor `unitlike`, and the constructor cannot complete an
*earlier* family because a stored eta-capable former's constructor is
already stored (`EtaFamiliesClosed`) while this name is fresh. -/
theorem extend_direct_ctor {env env₁ : Env} (m : EnvModel V env)
    (m₁ : EnvModel V env₁) {p : DirectParts} {cvTa cvCa : ConstantVal}
    {F : Nat} {v : Env × ConstantVal}
    (hE1 : EtaFamiliesClosed env₁)
    (hcc : checkDirectCtor (fueledOps F) env env₁ p cvTa = .ok v)
    (hccC : checkConstantVal (fueledOps F) env₁ p.cvC = .ok cvCa)
    (hfrT : ∀ ψ : Name → Nat,
      FrameOk V m₁.val env₁ ψ 0 (rho0 V) cvTa.type)
    (hnz : p.resSort.isNonZero = true)
    {tbs : List (Name × Expr × BinderMeta)}
    (hstripT : Expr.stripPis p.nP cvTa.type = some (tbs, .sort p.resSort))
    (hTfind : env₁.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTval : ∀ ψ : Name → Nat, m₁.val p.cvT.name ψ =
      directTyVal V m.val env cvTa.type cvCa.type p.nP p.nF p.resSort ψ)
    (hagree : ∀ ψ : Name → Nat, InterpAgree V m.val env m₁.val env₁ ψ)
    (htres : cvTa.type.constsResolve env = true) :
    ∃ m₂ : EnvModel V ⟨.ctorInfo cvCa p.nP p.nF :: env₁.consts⟩,
      (∀ ψ, m₂.val cvCa.name ψ =
        directCtorVal V m₁.val env₁ cvCa.type p.nP p.nF ψ) ∧
      (∀ n ψ, n ≠ cvCa.name → m₂.val n ψ = m₁.val n ψ) := by
  obtain ⟨hfind0, hnres0, hpshape0, hnd, hlb, hfv, tyA, stype, u,
    hann, hlp, hres, hst, hsort, hcvA⟩ := checkConstantVal_inv hccC
  have hnameA : cvCa.name = p.cvC.name := by rw [hcvA]
  have hlpsA : cvCa.levelParams = p.cvC.levelParams := by rw [hcvA]
  have htypeA : cvCa.type = tyA := by rw [hcvA]
  have hfind' : env₁.find? cvCa.name = none := by rw [hnameA]; exact hfind0
  have hnres : reservedBasisNames.contains cvCa.name = false := by
    rw [hnameA]; exact hnres0
  have hshapeA : cvCa.name.isProjFnShape = false := by
    rw [hnameA]; exact hpshape0
  have htyf : cvCa.type.hasFvar = false := by
    rw [htypeA]
    exact not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F _ hann (WScoped.of_not_hasFvar hfv)).fvarsBelow)
  have htyb : cvCa.type.looseBVarsBounded 0 = true := by
    rw [htypeA]; exact annotateCore_looseBVars F _ hann hlb
  have htlp : cvCa.type.allLevelParamsDefined cvCa.levelParams = true := by
    rw [htypeA, hlpsA]; exact hlp
  have htresC : cvCa.type.constsResolve env₁ = true := by
    rw [htypeA]; exact hres
  have hAty : ∀ ψ : Name → Nat,
      AnnotOk V m₁.val env₁ ψ 0 (rho0 V) cvCa.type := by
    intro ψ
    rw [htypeA]
    exact annotate_sound m₁ _ hann (WScoped.of_not_hasFvar hfv) hlb
      (Expr.LeavesBounded.of_not_hasFvar hfv) (rho0 V)
      (FvarsOk.of_not_hasFvar hfv)
  have hnresC : reservedBasisNames.contains
      (ConstantInfo.ctorInfo cvCa p.nP p.nF).name = false := hnres
  have hwf : ConstWF ⟨.ctorInfo cvCa p.nP p.nF :: env₁.consts⟩
      (.ctorInfo cvCa p.nP p.nF) := by
    refine ⟨htyf, htlp, Expr.constsResolve_mono htresC, htyb, ?_, ?_, ?_⟩
    · intro cv2 v2 h2 heq; exact nomatch heq
    · intro cv2 mI' rP' rules heq; exact nomatch heq
    · intro cv2 v2 heq; exact nomatch heq
  refine extend_basis_one m₁ (.ctorInfo cvCa p.nP p.nF)
    (fun ψ => directCtorVal V m₁.val env₁ cvCa.type p.nP p.nF ψ)
    hfind' hwf htresC (fun cv2 value2 h2 heq => nomatch heq) ?_ ?_ hAty
    (fun cv caps heq _ => nomatch heq)
    (fun cv nP nF heq hn => absurd (hn ▸ hnresC) (by decide))
    (fun cv caps heq _ => nomatch heq)
    (fun hn => absurd (hn ▸ hnresC) (by decide))
    (fun _ hres2 => absurd (hres2 ▸ hnresC) (by simp))
    (fun cv mI rP rules heq => nomatch heq)
    (fun val' _ _ cvR mI rP rules heq => nomatch heq)
    (fun cvR mI rP rules heq => nomatch heq)
    (fun entry heq _ => nomatch heq)
    (hnotthm := fun cv2 value2 h => ConstantInfo.noConfusion h)
    (hcaps := fun val' _ _ => by
      refine ⟨?_, ?_⟩
      · intro T cvT capsT hfT hcape hresT hfam hpart
        exfalso
        rcases hpart with hT | hC | ⟨j, hj, hP⟩
        · rw [hT, Env.find?_cons, if_pos rfl] at hfT
          exact nomatch (Option.some.inj hfT)
        · -- an earlier eta-capable former's constructor is stored
          -- already, and this name is fresh
          rw [Env.find?_cons] at hfT
          split at hfT
          · exact nomatch (Option.some.inj hfT)
          · obtain ⟨cvC0, hfC0⟩ := hE1 T cvT capsT hfT hcape hresT
            rw [hC] at hfC0
            have hfC1 : env₁.find? cvCa.name =
                some (.ctorInfo cvC0 capsT.etaParams capsT.etaFields) := hfC0
            rw [hfind'] at hfC1
            exact nomatch hfC1
        · have hP' : projFnName T j = cvCa.name := hP
          rw [← hP'] at hshapeA
          simp [projFnName, Name.isProjFnShape] at hshapeA
      · intro cv caps heq hcapu _
        exact nomatch heq)
  · -- `mem_type`
    intro ψ
    exact directCtor_mem m m₁ hcc (hfrT ψ) hnz hstripT hTfind hTlps hTval
      (hagree ψ) htres hccC
  · -- `val_params`
    intro ψ₁ ψ₂ hψ
    exact directCtorVal_params m₁.val_params (ps := cvCa.levelParams) hψ htlp

/-! ### The recursor's semantic obligations -/

/-- Inversion of the recursor rule's stage (`checkDirectRule`): the
annotated right-hand side, its shape pin, and the **rule tower's own
frame** — the recursor telescope opened at `nP + 2`, the constructor's
field telescope opened on top of it at that very frame, and the
definitional pin of the stored λ-domains against the frame's
annotations. -/
theorem checkDirectRule_inv {env : Env} {p : DirectParts}
    {cvCa cvRa : ConstantVal} {F : Nat} {rhsA : Expr}
    (h : checkDirectRule (fueledOps F) env p cvCa cvRa = .ok rhsA) :
    ∃ rbs fvsP restR cdomsP crest xFvs crest2 ldoms lrest,
      p.rhs.hasFvar = false ∧ p.rhs.looseBVarsBounded 0 = true ∧
      annotateCore env F 0 p.rhs = .ok rhsA ∧
      rhsA.allLevelParamsDefined cvRa.levelParams = true ∧
      rhsA.constsResolve env = true ∧
      rhsA.looseBVarsBounded 0 = true ∧
      rhsA.hasFvar = false ∧
      rhsA.stripLams (p.nP + 2 + p.nF) = some (rbs, directRuleBody p.nF) ∧
      openPisAtFvars (p.nP + 2) cvRa.type 0 = some (fvsP, restR) ∧
      Expr.instPisAt (fvsP.take p.nP) cvCa.type = some (cdomsP, crest) ∧
      openPisAtFvars p.nF crest (p.nP + 2) = some (xFvs, crest2) ∧
      Expr.instLamsAt (fvsP ++ xFvs) rhsA = some (ldoms, lrest) ∧
      DefEqListOk F env (p.nP + 2 + p.nF)
        ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms ∧
      ∃ rhsTy, inferTypeCore env F 0 rhsA = .ok rhsTy := by
  simp only [checkDirectRule, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, fueledOps_ensureSort, fueledOps_whnf, Bind.bind,
    Except.bind] at h
  revert h
  by_cases hrawwf : (!p.rhs.hasFvar && p.rhs.looseBVarsBounded 0) = true
  case neg => intro h; rw [if_neg hrawwf] at h; exact nomatch h
  intro h
  rw [if_pos hrawwf] at h
  simp only [Bool.and_eq_true] at hrawwf
  obtain ⟨hrawf', hrawb⟩ := hrawwf
  have hrawf : p.rhs.hasFvar = false := by
    revert hrawf'
    cases p.rhs.hasFvar <;> simp
  try dsimp only at h
  cases hann : annotateCore env F 0 p.rhs with
  | error e => rw [hann] at h; exact nomatch h
  | ok rhsA' => ?_
  rw [hann] at h
  try dsimp only at h
  by_cases hrwf : (rhsA'.allLevelParamsDefined cvRa.levelParams &&
      rhsA'.constsResolve env && rhsA'.looseBVarsBounded 0 &&
      !rhsA'.hasFvar) = true
  case neg => rw [if_neg hrwf] at h; exact nomatch h
  rw [if_pos hrwf] at h
  simp only [Bool.and_eq_true] at hrwf
  obtain ⟨⟨⟨hrlp, hrres⟩, hrb⟩, hrf'⟩ := hrwf
  have hrf : rhsA'.hasFvar = false := by
    revert hrf'
    cases rhsA'.hasFvar <;> simp
  try dsimp only at h
  revert h
  match hstripR : rhsA'.stripLams (p.nP + 2 + p.nF) with
  | none => intro h; exact nomatch h
  | some (rbs, rbody) => ?_
  intro h
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  by_cases hrrb : (rbody == directRuleBody p.nF) = true
  case neg => rw [if_neg hrrb] at h; exact nomatch h
  rw [if_pos hrrb] at h
  obtain rfl := eq_of_beq hrrb
  try dsimp only at h
  revert h
  match hopR : openPisAtFvars (p.nP + 2) cvRa.type 0 with
  | none => intro h; exact nomatch h
  | some (fvsP, restR) => ?_
  intro h
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  match hinstC : Expr.instPisAt (fvsP.take p.nP) cvCa.type with
  | none => intro h; exact nomatch h
  | some (cdomsP, crest) => ?_
  intro h
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  match hopX : openPisAtFvars p.nF crest (p.nP + 2) with
  | none => intro h; exact nomatch h
  | some (xFvs, crest2) => ?_
  intro h
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  match hlinst : Expr.instLamsAt (fvsP ++ xFvs) rhsA' with
  | none => intro h; exact nomatch h
  | some (ldoms, lrest) => ?_
  intro h
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  revert h
  cases hde : checkDefEqList (fueledOps F) env (p.nP + 2 + p.nF)
      ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms with
  | error e => intro h; exact nomatch h
  | ok u1 => ?_
  intro h
  try dsimp only at h
  revert h
  cases hity : inferTypeCore env F 0 rhsA' with
  | error e => intro h; exact nomatch h
  | ok rhsTy => ?_
  intro h
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  exact ⟨rbs, fvsP, restR, cdomsP, crest, xFvs, crest2, ldoms, lrest,
    hrawf, hrawb, rfl, hrlp, hrres, hrb, hrf, hstripR, rfl, hinstC,
    hopX, hlinst, checkDefEqList_inv hde, rhsTy, hity⟩


omit [SetTheory V] in
/-- Inversion of a one-binder telescope strip. -/
theorem stripPis_one {e : Expr} {bs : List (Name × Expr × BinderMeta)}
    {body : Expr} (h : Expr.stripPis 1 e = some (bs, body)) :
    ∃ n d mb, e = .forallE n d body mb ∧ bs = [(n, d, mb)] := by
  match e with
  | .forallE n d b mb =>
    simp only [Expr.stripPis, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h
    exact ⟨n, d, mb, by rw [h.2], by rw [← h.1]⟩
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    exact nomatch h

/-- **The recursor's λ-tower body obligation.**

At every fitting spine `p⃗ M mi t` of the recursor's telescope the body
value — the minor premise applied to the major's projections — inhabits
the interpreted residual `M t`.  The three semantic inputs are supplied
by the block's earlier stages, transported to *this* install's
environment by the caller: the field telescope's universe bound
(`hfieldAt`), the type former's fold (`hTfold`) and the constructor's
fold (`hCfold`). -/
theorem directRec_body {env₂ : Env} (m₂ : EnvModel V env₂)
    {F : Nat} {φ : Name → Nat} {p : DirectParts}
    {cvTa cvCa cvRa : ConstantVal} {fvsC : List Expr} {crestC : Expr}
    {cbs : List (Name × Expr × BinderMeta)}
    (hrt : checkDirectRecTy (fueledOps F) env₂ p cvTa cvCa cvRa = .ok ())
    (hnz : p.resSort.isNonZero = true)
    (hfrRa : FrameOk V m₂.val env₂ φ 0 (rho0 V) cvRa.type)
    (hfrC : FrameOk V m₂.val env₂ φ 0 (rho0 V) cvCa.type)
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsC, crestC))
    (hstripC : Expr.stripPis (p.nP + p.nF) cvCa.type = some (cbs,
      directFam p.cvT.name p.cvT.levelParams p.nP p.nF))
    (hdomsCT : DomsInterpEq V m₂.val env₂ φ p.nP 0 (rho0 V)
      cvCa.type cvTa.type)
    (hfieldAt : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid →
      ps.length = p.nP →
      FieldTele V m₂.val env₂ φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid)
    (hTfold : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      SpineFold V (m₂.val p.cvT.name φ) ps =
        sigmaTowerV V m₂.val env₂ φ (p.resSort.eval φ) p.nF d₁ ρ₁ crestC)
    (hCfold : ∀ (vs : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvCa.type vs d₁ ρ₁ r →
      vs.length = p.nP + p.nF →
      SpineFold V (m₂.val p.cvC.name φ) vs = tupleV (vs.drop p.nP))
    (hTfind : env₂.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTname : cvTa.name = p.cvT.name)
    (hCfind : env₂.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hClps : cvCa.levelParams = p.cvT.levelParams) :
    TeleBody V m₂.val env₂ φ (p.nP + 3) 0 (rho0 V) cvRa.type
      (fun _ _ xs => SpineFold V (xs.getD (p.nP + 1) SetTheory.empty)
        ((List.range p.nF).map fun j =>
          projV j (xs.getD (p.nP + 2) SetTheory.empty))) := by
  obtain ⟨fvsP, restR, cdomsP, crest, mfv, mbs, mdom, minfv, xFvs, cdomsF,
    jbs, hsh, hopR, hinstC, hpinsP, hmfv, hmstrip, hmdom, hmpin, hminfv,
    hminop, hcinstF, hpinsF, hjstrip, jdom, hjdom, hjpin⟩ :=
    checkDirectRecTy_inv hrt
  obtain ⟨hinstRspec, hlenfvsP, hshapeP⟩ := openPisAtFvars_spec (p.nP + 2) 0 hopR
  obtain ⟨midP, hopP, hopMM⟩ := openPisAtFvars_add p.nP 2 0 hopR
  rw [Nat.zero_add] at hopMM
  -- the residual after the whole telescope: `motive t`
  obtain ⟨jn, jd, jm, hrestR, hjbs⟩ := stripPis_one hjstrip
  obtain rfl : jd = jdom := by
    rw [hjbs] at hjdom; simpa using hjdom
  -- the motive variable's index
  obtain ⟨nmM, hmfvEq⟩ := hshapeP p.nP mfv hmfv
  rw [Nat.zero_add] at hmfvEq
  intro xs d' ρ' rest hfit hlen
  -- split off the major premise
  have hxs : xs = xs.take (p.nP + 2) ++ xs.drop (p.nP + 2) :=
    (List.take_append_drop _ xs).symm
  rw [hxs] at hfit
  obtain ⟨dM, ρM, midM, hfitP2, hfitMaj⟩ := TeleFit_split hfit
  have hlen2 : (xs.take (p.nP + 2)).length = p.nP + 2 := by
    rw [List.length_take]; omega
  obtain ⟨hdM, fvs', hopen'⟩ := TeleFit_open (p.nP + 2) hfitP2 hlen2
  rw [Nat.zero_add] at hdM
  subst hdM
  obtain ⟨rfl, rfl⟩ : fvs' = fvsP ∧ midM = restR := by
    rw [hopR] at hopen'
    have h := Option.some.inj hopen'
    exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
  have hlend : (xs.drop (p.nP + 2)).length = 1 := by
    rw [List.length_drop]; omega
  obtain ⟨x, hxd⟩ : ∃ x, xs.drop (p.nP + 2) = [x] := by
    cases hL : xs.drop (p.nP + 2) with
    | nil => rw [hL] at hlend; exact nomatch hlend
    | cons a t =>
      cases t with
      | nil => exact ⟨a, rfl⟩
      | cons b t2 => rw [hL] at hlend; simp at hlend
  rw [hxd, hrestR] at hfitMaj
  cases hfitMaj with
  | @cons _ _ _ _ _ _ _ _ _ _ _ Amaj hjdI hxmem hnil =>
    cases hnil
    -- the parameter, motive and minor stages
    have hxs2 : xs.take (p.nP + 2) =
        (xs.take (p.nP + 2)).take p.nP ++ (xs.take (p.nP + 2)).drop p.nP :=
      (List.take_append_drop _ _).symm
    rw [hxs2] at hfitP2
    obtain ⟨dP, ρP, midP', hfitPs, hfitMM⟩ := TeleFit_split hfitP2
    have hlenPs : ((xs.take (p.nP + 2)).take p.nP).length = p.nP := by
      simp only [List.length_take]; omega
    obtain ⟨hdP, fvsA, hopA⟩ := TeleFit_open p.nP hfitPs hlenPs
    rw [Nat.zero_add] at hdP
    subst hdP
    obtain ⟨rfl, rfl⟩ : fvsA = List.take p.nP fvs' ∧ midP' = midP := by
      rw [hopP] at hopA
      have h := Option.some.inj hopA
      exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
    have hlenMM : ((xs.take (p.nP + 2)).drop p.nP).length = 2 := by
      simp only [List.length_drop, List.length_take]; omega
    obtain ⟨M0, mi0, hMM⟩ :
        ∃ a b, (xs.take (p.nP + 2)).drop p.nP = [a, b] := by
      cases hL : (xs.take (p.nP + 2)).drop p.nP with
      | nil => rw [hL] at hlenMM; exact nomatch hlenMM
      | cons a t =>
        cases t with
        | nil => rw [hL] at hlenMM; simp at hlenMM
        | cons b t2 =>
          cases t2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons c t3 => rw [hL] at hlenMM; simp at hlenMM
    rw [hMM] at hfitMM
    cases hfitMM with
    | @cons _ _ nm0 dom0 body0 m0 _ _ _ _ _ AM hdom0 hM0 hfitMM' =>
      generalize hgt1 : body0.instantiate1 (Expr.fvar p.nP nm0 dom0) = t1
        at hfitMM'
      cases hfitMM' with
      | @cons _ _ nm1 dom1 body1 m1 _ _ _ _ _ Amin hdom1 hmi0 hfitNil =>
        generalize hgt2 : body1.instantiate1 (Expr.fvar (p.nP + 1) nm1 dom1)
          = t2 at hfitNil
        cases hfitNil
        -- the minor premise's opening variable
        have hdropfvs : List.drop p.nP fvs' =
            [Expr.fvar p.nP nm0 dom0, Expr.fvar (p.nP + 1) nm1 dom1] := by
          have h1 : openPisAtFvars 2 (Expr.forallE nm0 dom0 body0 m0) p.nP =
              some ([Expr.fvar p.nP nm0 dom0, Expr.fvar (p.nP + 1) nm1 dom1],
                body1.instantiate1 (Expr.fvar (p.nP + 1) nm1 dom1)) := by
            simp only [openPisAtFvars, hgt1]
          rw [h1] at hopMM
          exact (congrArg Prod.fst (Option.some.inj hopMM)).symm
        have hminfvEq : minfv = Expr.fvar (p.nP + 1) nm1 dom1 := by
          rw [show fvs'[p.nP + 1]? = (List.drop p.nP fvs')[1]? from by
            simp [List.getElem?_drop], hdropfvs] at hminfv
          simpa using hminfv.symm
        -- the two values the body reads off the spine
        have hxsNP2 : xs.getD (p.nP + 2) SetTheory.empty = x := by
          rw [List.getD_eq_getElem?_getD,
            show xs[p.nP + 2]? = (List.drop (p.nP + 2) xs)[0]? from by
              simp [List.getElem?_drop], hxd]
          rfl
        have hxsNP1 : xs.getD (p.nP + 1) SetTheory.empty = mi0 := by
          rw [List.getD_eq_getElem?_getD,
            show xs[p.nP + 1]? =
              (List.drop p.nP (List.take (p.nP + 2) xs))[1]? from by
              simp [List.getElem?_drop, List.getElem?_take], hMM]
          rfl
        -- the parameter fit, transferred to the constructor and the former
        have hdomsRC : DomsAgree V m₂.val env₂ φ p.nP 0 (rho0 V) cvRa.type
            0 (rho0 V) cvCa.type :=
          DomsAgree.of_pins_inst m₂ F p.nP 0 (rho0 V) cvRa.type cvCa.type
            (List.take p.nP fvs') (Expr.forallE nm0 dom0 body0 m0)
            cdomsP crest hopP hinstC
            (fun j a b ha hb => by
              have hj : j < p.nP := by
                obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
                simp only [List.length_take, hlenfvsP] at hlt
                omega
              exact checkDirectDomsAt_inv p.nP hpinsP j hj a b ha hb)
            hfrRa hfrC
        obtain ⟨dC, ρC, restC0, hfitC0⟩ :=
          TeleFit.transfer p.nP hfitPs hlenPs hdomsRC
        obtain ⟨hdC, fvsC0, hopC0⟩ := TeleFit_open p.nP hfitC0 hlenPs
        rw [Nat.zero_add] at hdC
        subst hdC
        have hrestC : restC0 = crestC := by
          rw [hcq] at hopC0
          exact (congrArg Prod.snd (Option.some.inj hopC0)).symm
        have hρC : ρC = ρP := TeleFit.rho_det hfitC0 hfitPs
        rw [hrestC, hρC] at hfitC0
        have hfldC := hfieldAt _ p.nP ρP crestC hfitC0 hlenPs
        obtain ⟨dT, ρT, restT0, hfitT0⟩ :=
          TeleFit.transfer p.nP hfitC0 hlenPs hdomsCT
        obtain ⟨hdT, -, -⟩ := TeleFit_open p.nP hfitT0 hlenPs
        rw [Nat.zero_add] at hdT
        subst hdT
        have hρT : ρT = ρP := TeleFit.rho_det hfitT0 hfitPs
        rw [hρT] at hfitT0
        have hTf := hTfold _ p.nP ρP restT0 hfitT0 hlenPs
        -- the frame-relocation chain onto the minor premise's telescope
        have hCcl : cvCa.type.hasFvar = false :=
          not_hasFvar_of_fvarsBelow_zero hfrC.ws.fvarsBelow
        obtain ⟨hcqinst, hlenfvsC, hshapeC⟩ := openPisAtFvars_spec p.nP 0 hcq
        have hlenTake : (List.take p.nP fvs').length = p.nP := by
          simp only [List.length_take, hlenfvsP]; omega
        have hsp₁ : FvarSpine p.nP ρP fvsC
            (List.take p.nP (List.take (p.nP + 2) xs)) := by
          refine FvarSpine.of_pointwise (by rw [hlenfvsC, hlenPs]) ?_
          intro k a v ha hv
          obtain ⟨nm, hnm⟩ := hshapeC k a ha
          have hk : k < p.nP := by
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
            rw [hlenfvsC] at hlt; exact hlt
          refine ⟨0 + k, nm, Expr.fvarTypeD a, hnm, by omega, ?_⟩
          have h0 := hfitPs.slots k (by rw [hlenPs]; exact hk)
          rw [Nat.zero_add] at h0 ⊢
          rw [h0, List.getD_eq_getElem?_getD, hv]
          rfl
        have hsp₂ : FvarSpine (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) (List.take p.nP fvs')
            (List.take p.nP (List.take (p.nP + 2) xs)) := by
          refine FvarSpine.of_pointwise (by rw [hlenTake, hlenPs]) ?_
          intro k a v ha hv
          have hk : k < p.nP := by
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
            rw [hlenTake] at hlt; exact hlt
          have ha' : fvs'[k]? = some a := by
            rwa [List.getElem?_take_of_lt hk] at ha
          obtain ⟨nm, hnm⟩ := hshapeP k a ha'
          refine ⟨0 + k, nm, Expr.fvarTypeD a, hnm, by omega, ?_⟩
          have h0 := hfitPs.slots k (by rw [hlenPs]; exact hk)
          rw [Nat.zero_add] at h0 ⊢
          simp only [updV]
          rw [if_neg (by omega), if_neg (by omega), h0,
            List.getD_eq_getElem?_getD, hv]
          rfl
        have hstripC' : Expr.stripPis (fvsC.length + p.nF) cvCa.type =
            some (cbs, directFam p.cvT.name p.cvT.levelParams p.nP p.nF) := by
          rw [hlenfvsC]; exact hstripC
        have hagCC : DomsAgree V m₂.val env₂ φ p.nF p.nP ρP crestC
            (p.nP + 2) (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) crest :=
          DomsAgree.of_shift hCcl hfrC.bb p.nF hstripC' hcqinst hinstC hsp₁ hsp₂
        -- the minor premise's telescope, and the field domains' pins
        have hfrRes : FrameOk V m₂.val env₂ φ p.nP ρP
            (Expr.forallE nm0 dom0 body0 m0) := FrameOk.ofTeleFit hfitPs hfrRa
        have hfrT1 : FrameOk V m₂.val env₂ φ (p.nP + 1) (updV V ρP p.nP M0)
            (Expr.forallE nm1 dom1 body1 m1) := by
          rw [← hgt1]; exact hfrRes.body hdom0 hM0
        have hfrDom1 : FrameOk V m₂.val env₂ φ (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) dom1 :=
          FrameOk.weaken_top hfrT1.dom
        have hfrCrest : FrameOk V m₂.val env₂ φ (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) crest := by
          refine FrameOk.weaken_top (FrameOk.weaken_top ?_)
          refine FrameOk.ofInstWalk m₂ F (List.take p.nP fvs') hinstC
            (by rw [hlenTake]; exact hopP) hfitPs (by rw [hlenTake]; exact hlenPs)
            hfrRa hfrC ?_
          intro j a b ha hb
          have hj : j < p.nP := by
            obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
            rw [hlenTake] at hlt; exact hlt
          exact checkDirectDomsAt_inv p.nP hpinsP j hj a b ha hb
        have hminop' : openPisAtFvars p.nF dom1 (p.nP + 2) = some (xFvs,
            mfv.app ((Expr.const p.cvC.name
              (p.cvT.levelParams.map Level.param)).mkAppN
              (List.take p.nP fvs' ++ xFvs))) := by
          rw [hminfvEq] at hminop; exact hminop
        have hagMC : DomsAgree V m₂.val env₂ φ p.nF (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) dom1
            (p.nP + 2) (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) crest :=
          DomsAgree.of_pins_inst m₂ F p.nF (p.nP + 2) _ dom1 crest xFvs _
            cdomsF _ hminop' hcinstF
            (fun j a b ha hb => by
              have hj : j < p.nF := by
                obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
                rw [(openPisAtFvars_spec p.nF (p.nP + 2) hminop').2.1] at hlt
                exact hlt
              exact checkDirectDomsAt_inv p.nF hpinsF j hj a b ha hb)
            hfrDom1 hfrCrest
        have hAg : DomsAgree V m₂.val env₂ φ p.nF p.nP ρP crestC
            (p.nP + 2) (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) dom1 :=
          DomsAgree.trans p.nF hagCC (DomsAgree.symm p.nF hfrDom1 hagMC)
        have hfldMin := FieldTele_reframe p.nF hAg hfldC
        have htowEq := sigmaTowerV_reframe p.nF hAg hfldC
        -- the major premise inhabits the tower
        obtain ⟨Tv, hTvI, hTvmem⟩ := m₂.mem_type _ (find?_mem hTfind) φ
        have hTannot := (m₂.annot_ok _ (find?_mem hTfind) φ).1
        have hparFr : ∀ a ∈ List.take p.nP fvs',
            FrameOk V m₂.val env₂ φ (p.nP + 2)
              (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) a := by
          intro a ha
          exact FrameOk.weaken_top (FrameOk.weaken_top
            (FrameOk.openVars p.nP hopP hfitPs hlenPs hfrRa a ha))
        have hspine : InterpSpine m₂.val env₂ φ (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) (List.take p.nP fvs')
            (List.take p.nP (List.take (p.nP + 2) xs)) := by
          refine InterpSpine.of_pointwise (by rw [hlenTake, hlenPs]) ?_
          intro k a v ha hv
          obtain ⟨i, n, ty, rfl, hlt, hval⟩ := FvarSpine.pointwise hsp₂ k ha hv
          rw [interpExpr, hval]
        have hconstI : interpExpr V m₂.val env₂ φ (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0)
            (.const p.cvT.name (p.cvT.levelParams.map Level.param)) =
            some (m₂.val p.cvT.name φ) := by
          rw [interp_const hTfind (by
            show (p.cvT.levelParams.map Level.param).length =
              cvTa.levelParams.length
            rw [hTlps, List.length_map])]
          have hsub : Level.substFn φ
              (ConstantInfo.indInfo cvTa
                (directCaps p)).toConstantVal.levelParams
              (p.cvT.levelParams.map Level.param) = φ := by
            show Level.substFn φ cvTa.levelParams
              (p.cvT.levelParams.map Level.param) = φ
            rw [hTlps]
            exact funext (fun q => Level.substFn_map_param)
          rw [hsub]
        have hchain : ChainSlots V (m₂.val p.cvT.name φ)
            (List.take p.nP (List.take (p.nP + 2) xs)) := by
          rw [← hTname]
          exact TeleFit.chainSlots hfitT0 hTannot hTvI hTvmem
        obtain ⟨hfamA, hfamI⟩ :=
          annotOk_spine (List.take p.nP fvs')
            (.const p.cvT.name (p.cvT.levelParams.map Level.param))
            (by simp only [AnnotOk]) hconstI
            (fun a ha => (hparFr a ha).an) hspine hchain
        have hfrFam : FrameOk V m₂.val env₂ φ (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0)
            ((Expr.const p.cvT.name
              (p.cvT.levelParams.map Level.param)).mkAppN
              (List.take p.nP fvs')) := by
          refine ⟨Expr.WScoped.mkAppN (by simp only [Expr.WScoped])
              (fun a ha => (hparFr a ha).ws),
            looseBVarsBounded_mkAppN (by rfl) (fun a ha => (hparFr a ha).bb),
            ?_, ?_, hfamA, _, hfamI⟩
          · intro l hl
            rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
            · simp [Expr.fvarLeaves] at hl'
            · exact (hparFr y hy).lb l hly
          · intro l hl
            rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
            · simp [Expr.fvarLeaves] at hl'
            · exact (hparFr y hy).fv l hly
        have hfrmidM : FrameOk V m₂.val env₂ φ (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) midM :=
          FrameOk.ofTeleFit hfitP2 hfrRa
        have hfrjd : FrameOk V m₂.val env₂ φ (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) jd := by
          rw [hrestR] at hfrmidM; exact hfrmidM.dom
        have hAmaj : Amaj = SpineFold V (m₂.val p.cvT.name φ)
            (List.take p.nP (List.take (p.nP + 2) xs)) :=
          isDefEqCore_sound m₂ F hjpin hfrjd.ws hfrFam.ws hfrjd.bb hfrFam.bb
            hfrjd.lb hfrFam.lb hfrjd.fv hfrFam.fv hfrjd.an hfrFam.an hjdI hfamI
        have hxTow : x ∈ˢ sigmaTowerV V m₂.val env₂ φ (p.resSort.eval φ) p.nF
            (p.nP + 2) (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) dom1 := by
          rw [← htowEq, ← hTf, ← hAmaj]; exact hxmem
        -- the minor premise, applied to a fitting field spine
        have hdom1' : interpExpr V m₂.val env₂ φ (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) dom1 = some Amin := by
          rw [interp_weaken_top hfrT1.dom.ws]; exact hdom1
        have hAgSym : DomsAgree V m₂.val env₂ φ p.nF (p.nP + 2)
            (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) dom1 p.nP ρP crestC :=
          DomsAgree.symm p.nF (FrameOk.ofTeleFit hfitC0 hfrC) hAg
        obtain ⟨hxfvsInst, hlenxFvs, hshapexF⟩ :=
          openPisAtFvars_spec p.nF (p.nP + 2) hminop'
        have hmi : ∀ (fs : List V) (dF : Nat) (ρF : Nat → V) (rF : Expr),
            TeleFit V m₂.val env₂ φ (p.nP + 2)
              (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0) dom1 fs dF ρF rF →
            fs.length = p.nF →
            SpineFold V mi0 fs ∈ˢ SetTheory.app M0 (tupleV fs) := by
          intro fs dF ρF rF hfitMin hlenfs
          obtain ⟨hdF, fvsMin, hopMin⟩ := TeleFit_open p.nF hfitMin hlenfs
          subst hdF
          have hrFEq : rF =
              mfv.app ((Expr.const p.cvC.name
                (p.cvT.levelParams.map Level.param)).mkAppN
                (List.take p.nP fvs' ++ xFvs)) := by
            rw [hminop'] at hopMin
            exact (congrArg Prod.snd (Option.some.inj hopMin)).symm
          subst hrFEq
          obtain ⟨Q, hQ, hmemQ, -⟩ :=
            TeleFit.elim hfitMin hfrDom1.an hdom1' hmi0
          -- the residual's interpretation: the motive at the constructor spine
          have hmfvI : interpExpr V m₂.val env₂ φ (p.nP + 2 + p.nF) ρF mfv =
              some M0 := by
            rw [hmfvEq, interpExpr, hfitMin.rho_below p.nP (by omega)]
            simp [updV]
          have hconstCI : interpExpr V m₂.val env₂ φ (p.nP + 2 + p.nF) ρF
              (.const p.cvC.name (p.cvT.levelParams.map Level.param)) =
              some (m₂.val p.cvC.name φ) := by
            rw [interp_const hCfind (by
              show (p.cvT.levelParams.map Level.param).length =
                cvCa.levelParams.length
              rw [hClps, List.length_map])]
            have hsub : Level.substFn φ
                (ConstantInfo.ctorInfo cvCa p.nP p.nF).toConstantVal.levelParams
                (p.cvT.levelParams.map Level.param) = φ := by
              show Level.substFn φ cvCa.levelParams
                (p.cvT.levelParams.map Level.param) = φ
              rw [hClps]
              exact funext (fun q => Level.substFn_map_param)
            rw [hsub]
          have hspineP : InterpSpine m₂.val env₂ φ (p.nP + 2 + p.nF) ρF
              (List.take p.nP fvs')
              (List.take p.nP (List.take (p.nP + 2) xs)) := by
            refine InterpSpine.of_pointwise (by rw [hlenTake, hlenPs]) ?_
            intro k a v ha hv
            obtain ⟨i, n, ty, rfl, hlt, hval⟩ := FvarSpine.pointwise hsp₂ k ha hv
            rw [interpExpr, ← hval, hfitMin.rho_below i (by omega)]
          have hspineF : InterpSpine m₂.val env₂ φ (p.nP + 2 + p.nF) ρF
              xFvs fs := by
            refine InterpSpine.of_pointwise (by rw [hlenxFvs, hlenfs]) ?_
            intro k a v ha hv
            obtain ⟨nm, hnm⟩ := hshapexF k a ha
            have hkf : k < p.nF := by
              obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hv
              rw [hlenfs] at hlt; exact hlt
            rw [hnm, interpExpr,
              hfitMin.slots k (by rw [hlenfs]; exact hkf),
              List.getD_eq_getElem?_getD, hv]
            rfl
          have hspineC := InterpSpine.append hspineP hspineF
          have hcinterp := interp_mkAppN (List.take p.nP fvs' ++ xFvs)
            (.const p.cvC.name (p.cvT.levelParams.map Level.param))
            hconstCI hspineC
          -- the constructor's value folds to the tuple of the fields
          obtain ⟨dF2, ρF2, rF2, hfitF⟩ :=
            TeleFit.transfer p.nF hfitMin hlenfs hAgSym
          have hfitCfull := TeleFit_append hfitC0 hfitF
          have hfold := hCfold _ _ _ _ hfitCfull (by
            simp only [List.length_append, hlenPs, hlenfs])
          rw [List.drop_left' hlenPs] at hfold
          have hresI : interpExpr V m₂.val env₂ φ (p.nP + 2 + p.nF) ρF
              (mfv.app ((Expr.const p.cvC.name
                (p.cvT.levelParams.map Level.param)).mkAppN
                (List.take p.nP fvs' ++ xFvs))) =
              some (SetTheory.app M0 (tupleV fs)) := by
            rw [interpExpr, hmfvI, hcinterp, hfold]
          rw [hresI] at hQ
          obtain rfl := Option.some.inj hQ
          exact hmemQ
        -- the body value inhabits `motive t`
        refine ⟨SetTheory.app M0 x, ?_, ?_⟩
        · have hv1 : (updV V (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0)
              (p.nP + 2) x) p.nP = M0 := by simp [updV]
          have hv2 : (updV V (updV V (updV V ρP p.nP M0) (p.nP + 1) mi0)
              (p.nP + 2) x) (p.nP + 2) = x := by simp [updV]
          have h1 : (Expr.app mfv (Expr.bvar 0)).instantiate1
              (Expr.fvar (p.nP + 2) jn jd) =
              Expr.app mfv (Expr.fvar (p.nP + 2) jn jd) := by
            rw [hmfvEq]; rfl
          rw [h1, interpExpr, hmfvEq, interpExpr, interpExpr, hv1, hv2]
        · simp only [hxsNP1, hxsNP2]
          exact directRec_body_mem (M := fun y => SetTheory.app M0 y)
            (Level.isNonZero_sound hnz φ) hfldMin hxTow hmi

omit [SetTheory V] in
/-- The recursor's telescope length is part of the checked shape. -/
theorem directShape_stripPis {T C : Name} {lps : List Name} {elim : Name}
    {nP nF : Nat} {tty cty rty : Expr}
    (h : directShape T C lps elim nP nF tty cty rty = true) :
    (Expr.stripPis (nP + 3) rty).isSome = true := by
  unfold directShape at h
  split at h
  · simp_all
  · exact nomatch h

set_option maxHeartbeats 3200000 in
/-- **The direct recursor rule's `RecRulesOk` obligation**:
`rule_eq_of_bottom_ext` at the constructed values.  The bottom fact is
the composite of the recursor's own fold (`teleLamV_fold` over
`directRec_body`), the constructor's fold to the tuple
(`directCtorVal_fold`, through `hCfold`) and `directRec_iota`, which
reads the fields back off that tuple; the rule's right-hand side
instantiates to the minor premise applied to the very field variables,
so the two sides meet at `SpineFold mi f⃗`. -/
theorem directRec_rule_eq {env₂ : Env} (m₂ : EnvModel V env₂)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal}
    {fvsC : List Expr} {crestC : Expr}
    {cbs : List (Name × Expr × BinderMeta)} {rhsA : Expr}
    (hrt : checkDirectRecTy (fueledOps F) env₂ p cvTa cvCa cvRa = .ok ())
    (hru : checkDirectRule (fueledOps F) env₂ p cvCa cvRa = .ok rhsA)
    (hnz : p.resSort.isNonZero = true)
    (hfrRa : ∀ φ : Name → Nat, FrameOk V m₂.val env₂ φ 0 (rho0 V) cvRa.type)
    (hfrC : ∀ φ : Name → Nat, FrameOk V m₂.val env₂ φ 0 (rho0 V) cvCa.type)
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsC, crestC))
    (hstripC : Expr.stripPis (p.nP + p.nF) cvCa.type = some (cbs,
      directFam p.cvT.name p.cvT.levelParams p.nP p.nF))
    (hdomsCT : ∀ φ : Name → Nat, DomsInterpEq V m₂.val env₂ φ p.nP 0
      (rho0 V) cvCa.type cvTa.type)
    (hfieldAt : ∀ (φ : Name → Nat) (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V)
        (mid : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid →
      ps.length = p.nP →
      FieldTele V m₂.val env₂ φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid)
    (hTfold : ∀ (φ : Name → Nat) (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V)
        (r : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      SpineFold V (m₂.val p.cvT.name φ) ps =
        sigmaTowerV V m₂.val env₂ φ (p.resSort.eval φ) p.nF d₁ ρ₁ crestC)
    (hCfold : ∀ (φ : Name → Nat) (vs : List V) (d₁ : Nat) (ρ₁ : Nat → V)
        (r : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvCa.type vs d₁ ρ₁ r →
      vs.length = p.nP + p.nF →
      SpineFold V (m₂.val p.cvC.name φ) vs = tupleV (vs.drop p.nP))
    (hTfind : env₂.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTname : cvTa.name = p.cvT.name)
    (hCfind : env₂.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hClps : cvCa.levelParams = p.cvT.levelParams)
    (hRres : cvRa.type.constsResolve env₂ = true)
    (hCres : cvCa.type.constsResolve env₂ = true)
    -- the extension carrying the recursor
    {fire : RecRuleFire} (hfirep : fire = .plain)
    (hfresh : env₂.find? cvRa.name = none)
    {val' : ConstVal V}
    (hagree : ∀ n, (env₂.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = m₂.val n ψ)
    (hvalR : ∀ ψ : Name → Nat, val' cvRa.name ψ =
      directRecVal V m₂.val env₂ cvRa.type p.nP p.nF ψ) :
    ∃ fvms bL,
      ruleLhsParts cvRa.name cvRa (p.nP + 2)
          ⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩ cvCa = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = p.nP + 2 + p.nF ∧
      (closeLamsAt fvms bL).constsResolve
        (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
          [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩
          : Env) = true ∧
      ∀ ψ : Name → Nat,
        AnnotOk V val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
            [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env)
          ψ 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V val'
            (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
              [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env)
            ψ (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V val'
            (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
              [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env)
            ψ rhsA = some Rv := by
  obtain ⟨rbs, fvsP, restR, cdomsP, crest, xFvs, crest2, ldoms, lrest,
    hrawf, hrawb, hann, hrlp, hrres, hrb, hrf, hstripR, hopR, hinstC,
    hopX, hlinst, hdeLam, rhsTy, hity⟩ := checkDirectRule_inv hru
  obtain ⟨fvsP₂, rest₂, cdomsP₂, crest₂, mfv, mbs, mdom, minfv, xFvsM,
    cdomsF, jbs, hsh, hopR₂, hinstC₂, hpinsP, hmfv, hmstrip, hmdom, hmpin,
    hminfv, hminop, hcinstF, hpinsF, hjstrip, jdom, hjdom, hjpin⟩ :=
    checkDirectRecTy_inv hrt
  have hfvsPeq : fvsP₂ = fvsP := by
    rw [hopR] at hopR₂
    exact (congrArg Prod.fst (Option.some.inj hopR₂)).symm
  have hrest₂eq : rest₂ = restR := by
    rw [hopR] at hopR₂
    exact (congrArg Prod.snd (Option.some.inj hopR₂)).symm
  rw [hfvsPeq] at hinstC₂ hpinsP hmfv hmpin hminfv hminop hjpin
  rw [hrest₂eq] at hjstrip
  have hcrest₂eq : crest₂ = crest := by
    rw [hinstC] at hinstC₂
    exact (congrArg Prod.snd (Option.some.inj hinstC₂)).symm
  have hcdomsP₂eq : cdomsP₂ = cdomsP := by
    rw [hinstC] at hinstC₂
    exact (congrArg Prod.fst (Option.some.inj hinstC₂)).symm
  rw [hcrest₂eq] at hcinstF
  rw [hcdomsP₂eq] at hpinsP
  -- syntactic facts of the stored types
  have hRcl : cvRa.type.hasFvar = false :=
    not_hasFvar_of_fvarsBelow_zero (hfrRa (fun _ => 0)).ws.fvarsBelow
  have hCcl : cvCa.type.hasFvar = false :=
    not_hasFvar_of_fvarsBelow_zero (hfrC (fun _ => 0)).ws.fvarsBelow
  have hArhs : ∀ ψ : Name → Nat,
      AnnotOk V m₂.val env₂ ψ 0 (rho0 V) rhsA :=
    fun ψ => annotate_sound m₂ _ hann (Expr.WScoped.of_not_hasFvar hrawf)
      hrawb (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
      (FvarsOk.of_not_hasFvar hrawf)
  have hIrhs : ∀ ψ : Name → Nat, ∃ L,
      interpClosed V m₂.val env₂ ψ rhsA = some L := by
    intro ψ
    obtain ⟨⟨v, tv, hvi, -, -⟩, -, -⟩ :=
      inferTypeCore_sound (φ := ψ) m₂ F hity
        (Expr.WScoped.of_not_hasFvar hrf) hrb
        (Expr.LeavesBounded.of_not_hasFvar hrf)
        (FvarsOk.of_not_hasFvar hrf) (hArhs ψ)
    exact ⟨v, hvi⟩
  have hfP₁ : (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env).find?
      cvRa.name = some (.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩]) := by
    rw [Env.find?_cons, if_pos (show (ConstantInfo.recInfo cvRa
      (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩]).name = cvRa.name from rfl)]
  -- the parameter prefix of the recursor's opening
  obtain ⟨midP, hopP, hopMM⟩ := openPisAtFvars_add p.nP 2 0 hopR
  rw [Nat.zero_add] at hopMM
  obtain ⟨hopRinst, hlenfvsP, hshapeP⟩ :=
    openPisAtFvars_spec (p.nP + 2) 0 hopR
  obtain ⟨hopXinst, hlenxFvs, hshapeX⟩ :=
    openPisAtFvars_spec p.nF (p.nP + 2) hopX
  have hlenTake : (fvsP.take p.nP).length = p.nP := by
    rw [List.length_take, hlenfvsP]; omega
  have hspineLen : (fvsP ++ xFvs).length = p.nP + 2 + p.nF := by
    rw [List.length_append, hlenfvsP, hlenxFvs]
  refine rule_eq_of_bottom_ext m₂ F (c₀ := .recInfo cvRa (p.nP + 2)
      (p.nP + 2) [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩])
    hfresh hagree (by omega) hfP₁ hCfind hfirep rfl rfl hstripR hstripC
    rfl (by simp) hopR hinstC ?_ hopX hlinst hdeLam hRcl
    (hfrRa (fun _ => 0)).bb hCcl (hfrC (fun _ => 0)).bb hRres hCres hrres
    hrf hrb (fun ψ => (hfrRa ψ).an) (fun ψ => (hfrRa ψ).it) hArhs hIrhs ?_
  · -- the constructor residual's package, from the *per-frame* pins
    obtain ⟨hfvsPWf, -⟩ := openPisAtFvars_wf (p.nP + 2) 0 hopR
      (Expr.WScoped.of_not_hasFvar hRcl) (hfrRa (fun _ => 0)).bb
      (Expr.LeavesBounded.of_not_hasFvar hRcl)
    have hWcr : Expr.WScoped (p.nP + 2) crest :=
      (instPisAt_wscoped (D := p.nP + 2) (fvsP.take p.nP) hinstC
        (Expr.WScoped.of_not_hasFvar hCcl)
        (fun a ha => by
          have h := (hfvsPWf a (List.mem_of_mem_take ha)).1
          rwa [Nat.zero_add] at h)).2
    intro ψ xs hle hge hpref
    have hlenPs : (xs.take p.nP).length = p.nP := by
      rw [List.length_take]; omega
    have hrho0 : (fun l => (xs.take 0).getD l SetTheory.empty) = rho0 V := by
      funext l; rfl
    have hfitPs := TeleFit.of_framePref hpref p.nP 0 hopP
      (fun k hk => by
        rw [Nat.zero_add, List.getElem?_append_left (by omega)]
        exact (List.getElem?_take_of_lt hk).symm)
      (by omega)
    rw [hrho0, List.drop_zero, Nat.zero_add] at hfitPs
    have hfr := FrameOk.ofInstWalk m₂ F (fvsP.take p.nP) hinstC
      (by rw [hlenTake]; exact hopP) hfitPs (by rw [hlenTake]; exact hlenPs)
      (hfrRa ψ) (hfrC ψ)
      (fun j a b ha hb => by
        have hj : j < p.nP := by
          obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
          rw [hlenTake] at hlt; exact hlt
        exact checkDirectDomsAt_inv p.nP hpinsP j hj a b ha hb)
    have hup := FrameOk.getD_up (j := p.nP) (xs := xs)
      (D := p.nP + 2 + p.nF) (by omega) (by omega) hfr
    exact ⟨hWcr, hup.bb, hup.lb, hup.fv, hup.an, hup.it⟩
  -- ===== the bottom fact =====
  obtain ⟨jn, jd, jm, hrestR, hjbs⟩ := stripPis_one hjstrip
  obtain rfl : jd = jdom := by rw [hjbs] at hjdom; simpa using hjdom
  have hshapeA : ∀ (j : Nat) (a : Expr), (fvsP ++ xFvs)[j]? = some a →
      ∃ nm ty, a = Expr.fvar j nm ty := by
    intro j a hj
    rcases Nat.lt_or_ge j (p.nP + 2) with hjn | hjn
    · rw [List.getElem?_append_left (by omega)] at hj
      obtain ⟨nm, ha⟩ := hshapeP j a hj
      rw [Nat.zero_add] at ha
      exact ⟨nm, Expr.fvarTypeD a, ha⟩
    · rw [List.getElem?_append_right (by omega), hlenfvsP] at hj
      obtain ⟨nm, ha⟩ := hshapeX (j - (p.nP + 2)) a hj
      refine ⟨nm, Expr.fvarTypeD a, ?_⟩
      rw [show j = p.nP + 2 + (j - (p.nP + 2)) from by omega]
      exact ha
  intro ψ xs hxs hpref
  have hlenPs : (xs.take p.nP).length = p.nP := by
    rw [List.length_take]; omega
  have hlen2 : (xs.take (p.nP + 2)).length = p.nP + 2 := by
    rw [List.length_take]; omega
  have hfsLen : (xs.drop (p.nP + 2)).length = p.nF := by
    rw [List.length_drop]; omega
  have hrho0 : (fun l => (xs.take 0).getD l SetTheory.empty) = rho0 V := by
    funext l; rfl
  -- the three fits the frame invariant supplies
  have hfitP2 := TeleFit.of_framePref hpref (p.nP + 2) 0 hopR
    (fun k hk => by
      rw [Nat.zero_add]
      exact List.getElem?_append_left (by omega))
    (by omega)
  rw [hrho0, List.drop_zero, Nat.zero_add] at hfitP2
  have hfitPs := TeleFit.of_framePref hpref p.nP 0 hopP
    (fun k hk => by
      rw [Nat.zero_add, List.getElem?_append_left (by omega)]
      exact (List.getElem?_take_of_lt hk).symm)
    (by omega)
  rw [hrho0, List.drop_zero, Nat.zero_add] at hfitPs
  have hfitX := TeleFit.of_framePref hpref p.nF (p.nP + 2) hopX
    (fun k hk => by
      rw [List.getElem?_append_right (by omega), hlenfvsP,
        show p.nP + 2 + k - (p.nP + 2) = k from by omega])
    (by omega)
  rw [show (xs.drop (p.nP + 2)).take p.nF = xs.drop (p.nP + 2) from by
      rw [List.take_of_length_le (by omega)],
    show xs.take (p.nP + 2 + p.nF) = xs from
      List.take_of_length_le (by omega)] at hfitX
  -- the parameters cross to the constructor's and the former's telescopes
  have hdomsRC : DomsAgree V m₂.val env₂ ψ p.nP 0 (rho0 V) cvRa.type
      0 (rho0 V) cvCa.type :=
    DomsAgree.of_pins_inst m₂ F p.nP 0 (rho0 V) cvRa.type cvCa.type
      (fvsP.take p.nP) midP cdomsP crest hopP hinstC
      (fun j a b ha hb => by
        have hj : j < p.nP := by
          obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
          rw [hlenTake] at hlt; exact hlt
        exact checkDirectDomsAt_inv p.nP hpinsP j hj a b ha hb)
      (hfrRa ψ) (hfrC ψ)
  obtain ⟨dC, ρC, restC0, hfitC0⟩ := TeleFit.transfer p.nP hfitPs hlenPs hdomsRC
  obtain ⟨hdC, fvsC0, hopC0⟩ := TeleFit_open p.nP hfitC0 hlenPs
  rw [Nat.zero_add] at hdC
  subst hdC
  have hrestC : restC0 = crestC := by
    rw [hcq] at hopC0
    exact (congrArg Prod.snd (Option.some.inj hopC0)).symm
  have hρC : ρC = (fun l => (xs.take p.nP).getD l SetTheory.empty) :=
    TeleFit.rho_det hfitC0 hfitPs
  rw [hrestC, hρC] at hfitC0
  obtain ⟨dT, ρT0, restT0, hfitT0⟩ :=
    TeleFit.transfer p.nP hfitC0 hlenPs (hdomsCT ψ)
  obtain ⟨hdT, -, -⟩ := TeleFit_open p.nP hfitT0 hlenPs
  rw [Nat.zero_add] at hdT
  subst hdT
  have hρT : ρT0 = (fun l => (xs.take p.nP).getD l SetTheory.empty) :=
    TeleFit.rho_det hfitT0 hfitPs
  rw [hρT] at hfitT0
  have hfldC := hfieldAt ψ _ p.nP _ crestC hfitC0 hlenPs
  have hTf := hTfold ψ _ p.nP _ restT0 hfitT0 hlenPs
  -- the field fit relocates from the rule frame onto the constructor's own
  obtain ⟨hcqinst, hlenfvsC, hshapeC⟩ := openPisAtFvars_spec p.nP 0 hcq
  have hsp₁ : FvarSpine p.nP (fun l => (xs.take p.nP).getD l SetTheory.empty)
      fvsC (xs.take p.nP) := by
    refine FvarSpine.of_pointwise (by rw [hlenfvsC, hlenPs]) ?_
    intro k a v ha hv
    obtain ⟨nm, hnm⟩ := hshapeC k a ha
    have hk : k < p.nP := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
      rw [hlenfvsC] at hlt; exact hlt
    refine ⟨0 + k, nm, Expr.fvarTypeD a, hnm, by omega, ?_⟩
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hv]
    rfl
  have hsp₂ : FvarSpine (p.nP + 2)
      (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty)
      (fvsP.take p.nP) (xs.take p.nP) := by
    refine FvarSpine.of_pointwise (by rw [hlenTake, hlenPs]) ?_
    intro k a v ha hv
    have hk : k < p.nP := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
      rw [hlenTake] at hlt; exact hlt
    have ha' : fvsP[k]? = some a := by
      rwa [List.getElem?_take_of_lt hk] at ha
    obtain ⟨nm, hnm⟩ := hshapeP k a ha'
    refine ⟨0 + k, nm, Expr.fvarTypeD a, hnm, by omega, ?_⟩
    rw [Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (show k < p.nP + 2 from by omega)]
    rw [List.getElem?_take_of_lt hk] at hv
    rw [hv]
    rfl
  have hstripC' : Expr.stripPis (fvsC.length + p.nF) cvCa.type =
      some (cbs, directFam p.cvT.name p.cvT.levelParams p.nP p.nF) := by
    rw [hlenfvsC]; exact hstripC
  have hagCC : DomsAgree V m₂.val env₂ ψ p.nF p.nP
      (fun l => (xs.take p.nP).getD l SetTheory.empty) crestC
      (p.nP + 2) (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty)
      crest :=
    DomsAgree.of_shift hCcl (hfrC ψ).bb p.nF hstripC' hcqinst hinstC hsp₁ hsp₂
  have hAgSym : DomsAgree V m₂.val env₂ ψ p.nF (p.nP + 2)
      (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty) crest
      p.nP (fun l => (xs.take p.nP).getD l SetTheory.empty) crestC :=
    DomsAgree.symm p.nF (FrameOk.ofTeleFit hfitC0 (hfrC ψ)) hagCC
  obtain ⟨dF, ρF, restF, hfitXC⟩ := TeleFit.transfer p.nF hfitX hfsLen hAgSym
  have hfitCfull : TeleFit V m₂.val env₂ ψ 0 (rho0 V) cvCa.type
      (xs.take p.nP ++ xs.drop (p.nP + 2)) dF ρF restF :=
    TeleFit_append hfitC0 hfitXC
  have hCf := hCfold ψ _ _ _ _ hfitCfull (by
    simp only [List.length_append, hlenPs, hfsLen])
  rw [List.drop_left' hlenPs] at hCf
  -- the major premise's value inhabits the family
  have hxmem : tupleV (xs.drop (p.nP + 2)) ∈ˢ
      SpineFold V (m₂.val p.cvT.name ψ) (xs.take p.nP) := by
    rw [hTf]
    exact tupleV_mem (Level.isNonZero_sound hnz ψ) hfldC hfitXC hfsLen
  -- the major premise's domain is the family at the parameters
  have hfrRest : FrameOk V m₂.val env₂ ψ (p.nP + 2)
      (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty) restR :=
    FrameOk.ofTeleFit hfitP2 (hfrRa ψ)
  rw [hrestR] at hfrRest
  have hfrjd := hfrRest.dom
  obtain ⟨Amaj, hjdI⟩ := hfrjd.it
  have hparFr : ∀ a ∈ fvsP.take p.nP,
      FrameOk V m₂.val env₂ ψ (p.nP + 2)
        (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty) a :=
    fun a ha => FrameOk.openVars (p.nP + 2) hopR hfitP2 hlen2 (hfrRa ψ) a
      (List.mem_of_mem_take ha)
  have hspineT : InterpSpine m₂.val env₂ ψ (p.nP + 2)
      (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty)
      (fvsP.take p.nP) (xs.take p.nP) := by
    refine InterpSpine.of_pointwise (by rw [hlenTake, hlenPs]) ?_
    intro k a v ha hv
    obtain ⟨i, n, ty, rfl, hlt, hval⟩ := FvarSpine.pointwise hsp₂ k ha hv
    rw [interpExpr, hval]
  have hconstI : interpExpr V m₂.val env₂ ψ (p.nP + 2)
      (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty)
      (.const p.cvT.name (p.cvT.levelParams.map Level.param)) =
      some (m₂.val p.cvT.name ψ) := by
    rw [interp_const hTfind (by
      show (p.cvT.levelParams.map Level.param).length =
        cvTa.levelParams.length
      rw [hTlps, List.length_map])]
    have hsub : Level.substFn ψ
        (ConstantInfo.indInfo cvTa (directCaps p)).toConstantVal.levelParams
        (p.cvT.levelParams.map Level.param) = ψ := by
      show Level.substFn ψ cvTa.levelParams
        (p.cvT.levelParams.map Level.param) = ψ
      rw [hTlps]
      exact funext (fun q => Level.substFn_map_param)
    rw [hsub]
  obtain ⟨Tv, hTvI, hTvmem⟩ := m₂.mem_type _ (find?_mem hTfind) ψ
  have hTannot := (m₂.annot_ok _ (find?_mem hTfind) ψ).1
  have hchainT : ChainSlots V (m₂.val p.cvT.name ψ) (xs.take p.nP) := by
    rw [← hTname]
    exact TeleFit.chainSlots hfitT0 hTannot hTvI hTvmem
  obtain ⟨hfamA, hfamI⟩ := annotOk_spine (fvsP.take p.nP)
    (.const p.cvT.name (p.cvT.levelParams.map Level.param))
    (by simp only [AnnotOk]) hconstI (fun a ha => (hparFr a ha).an)
    hspineT hchainT
  have hfrFam : FrameOk V m₂.val env₂ ψ (p.nP + 2)
      (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty)
      ((Expr.const p.cvT.name (p.cvT.levelParams.map Level.param)).mkAppN
        (fvsP.take p.nP)) := by
    refine ⟨Expr.WScoped.mkAppN (by simp only [Expr.WScoped])
        (fun a ha => (hparFr a ha).ws),
      looseBVarsBounded_mkAppN (by rfl) (fun a ha => (hparFr a ha).bb),
      ?_, ?_, hfamA, _, hfamI⟩
    · intro l hl
      rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · simp [Expr.fvarLeaves] at hl'
      · exact (hparFr y hy).lb l hly
    · intro l hl
      rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · simp [Expr.fvarLeaves] at hl'
      · exact (hparFr y hy).fv l hly
  have hAmaj : Amaj = SpineFold V (m₂.val p.cvT.name ψ) (xs.take p.nP) :=
    isDefEqCore_sound m₂ F hjpin hfrjd.ws hfrFam.ws hfrjd.bb hfrFam.bb
      hfrjd.lb hfrFam.lb hfrjd.fv hfrFam.fv hfrjd.an hfrFam.an hjdI hfamI
  -- the full recursor spine and the recursor's own fold
  obtain ⟨dR, ρR, restRR, hfitMaj⟩ :
      ∃ d' ρ' r, TeleFit V m₂.val env₂ ψ (p.nP + 2)
        (fun l => (xs.take (p.nP + 2)).getD l SetTheory.empty) restR
        [tupleV (xs.drop (p.nP + 2))] d' ρ' r := by
    rw [hrestR]
    exact ⟨_, _, _,
      TeleFit.cons hjdI (by rw [hAmaj]; exact hxmem) TeleFit.nil⟩
  have hfitFull := TeleFit_append hfitP2 hfitMaj
  have hRfold := teleLamV_fold (directShape_stripPis hsh) hfitFull
    (by simp [hlen2]) (hfrRa ψ).an
    (directRec_body m₂ hrt hnz (hfrRa ψ) (hfrC ψ) hcq hstripC (hdomsCT ψ)
      (hfieldAt ψ) (hTfold ψ) (hCfold ψ) hTfind hTlps hTname hCfind hClps)
  have hgetD1 : (xs.take (p.nP + 2) ++
      [tupleV (xs.drop (p.nP + 2))]).getD (p.nP + 1) SetTheory.empty =
      xs.getD (p.nP + 1) SetTheory.empty := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt (show p.nP + 1 < p.nP + 2 from by omega),
      ← List.getD_eq_getElem?_getD]
  have hgetD2 : (xs.take (p.nP + 2) ++
      [tupleV (xs.drop (p.nP + 2))]).getD (p.nP + 2) SetTheory.empty =
      tupleV (xs.drop (p.nP + 2)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      hlen2]
    simp
  rw [hgetD1, hgetD2, directRec_iota hfsLen] at hRfold
  -- ===== the extended environment: lookups, spines, values =====
  have hCfind₁ : (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env).find?
      p.cvC.name = some (.ctorInfo cvCa p.nP p.nF) := by
    rw [Env.find?_cons_of_isSome (c := ConstantInfo.recInfo cvRa (p.nP + 2)
      (p.nP + 2) [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩])
      (show env₂.find? (ConstantInfo.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩]).name = none from hfresh)
      (by rw [hCfind]; rfl)]
    exact hCfind
  have hvalC : val' p.cvC.name ψ = m₂.val p.cvC.name ψ :=
    hagree _ (by rw [hCfind]; rfl) ψ
  have hRi : interpExpr V val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
      (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty)
      (.const cvRa.name (cvRa.levelParams.map Level.param)) =
      some (val' cvRa.name ψ) := by
    rw [interp_const hfP₁ (by simp [ConstantInfo.toConstantVal])]
    rw [show (ConstantInfo.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩]).toConstantVal.levelParams =
        cvRa.levelParams from rfl]
    rw [show Level.substFn ψ cvRa.levelParams
        (cvRa.levelParams.map Level.param) = ψ from
      funext fun q => Level.substFn_map_param]
  have hCi : interpExpr V val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
      (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty)
      (.const p.cvC.name (cvCa.levelParams.map Level.param)) =
      some (val' p.cvC.name ψ) := by
    rw [interp_const hCfind₁ (by simp [ConstantInfo.toConstantVal])]
    rw [show Level.substFn ψ
        (ConstantInfo.ctorInfo cvCa p.nP p.nF).toConstantVal.levelParams
        (cvCa.levelParams.map Level.param) = ψ from
      funext fun q => Level.substFn_map_param]
  have hspAll : InterpSpine val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
      (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty)
      (fvsP ++ xFvs) xs := by
    refine InterpSpine.of_pointwise (by rw [hspineLen, hxs]) ?_
    intro k a v ha hv
    obtain ⟨nm, ty, rfl⟩ := hshapeA k a ha
    simp only [interpExpr]
    rw [List.getD_eq_getElem?_getD, hv]
    rfl
  have hfvAnnot : ∀ x ∈ fvsP ++ xFvs,
      AnnotOk V val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
        (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty) x := by
    intro x hx
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    obtain ⟨nm, ty, rfl⟩ := hshapeA j x hj
    simp only [AnnotOk]
  have htakeSp : (fvsP ++ xFvs).take (p.nP + 2) = fvsP := by
    rw [List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  have hdropSp : (fvsP ++ xFvs).drop (p.nP + 2) = xFvs := by
    rw [List.drop_append_of_le_length (by omega),
      List.drop_of_length_le (by omega), List.nil_append]
  have hspR : InterpSpine val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
      (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty)
      fvsP (xs.take (p.nP + 2)) := by
    have h := InterpSpine.take (p.nP + 2) hspAll
    rwa [htakeSp] at h
  have hspX : InterpSpine val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
      (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty)
      xFvs (xs.drop (p.nP + 2)) := by
    have h := InterpSpine.drop (p.nP + 2) hspAll
    rwa [hdropSp] at h
  have hspC : InterpSpine val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
      (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty)
      (fvsP.take p.nP ++ xFvs) (xs.take p.nP ++ xs.drop (p.nP + 2)) := by
    refine InterpSpine.append ?_ hspX
    have h := InterpSpine.take p.nP hspR
    rwa [List.take_take, Nat.min_eq_left (by omega)] at h
  -- the constructor application folds to the tuple
  have hctorVal := interp_mkAppN (fvsP.take p.nP ++ xFvs)
    (.const p.cvC.name (cvCa.levelParams.map Level.param)) hCi hspC
  rw [hvalC, hCf] at hctorVal
  -- the whole canonical body
  have hbodyVal := interp_mkAppN
    (fvsP ++ [Expr.mkAppN (.const p.cvC.name
      (cvCa.levelParams.map Level.param)) (fvsP.take p.nP ++ xFvs)])
    (.const cvRa.name (cvRa.levelParams.map Level.param)) hRi
    (InterpSpine.append hspR
      (show InterpSpine val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
          [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
        (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty) [_]
        [tupleV (xs.drop (p.nP + 2))] from ⟨hctorVal, trivial⟩))
  have hRfold' : SpineFold V
      (directRecVal V m₂.val env₂ cvRa.type p.nP p.nF ψ)
      (xs.take (p.nP + 2) ++ [tupleV (xs.drop (p.nP + 2))]) =
      SpineFold V (xs.getD (p.nP + 1) SetTheory.empty)
        (xs.drop (p.nP + 2)) := hRfold
  rw [hvalR ψ, hRfold'] at hbodyVal
  -- ===== the rule tower's instantiated body =====
  have hbounded : ∀ a ∈ fvsP ++ xFvs, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hshapeA j a hj
    rfl
  have hRmid : lrest = Expr.instSeq (fvsP ++ xFvs) (p.nP + 2 + p.nF - 1)
      (directRuleBody p.nF) := by
    have h1 := (instLamsAt_stripLams (fvsP ++ xFvs) hlinst
      (by rw [hspineLen]; exact hstripR)).1
    rw [hspineLen] at h1
    exact h1
  have hminfvA : (fvsP ++ xFvs)[p.nP + 1]? = some minfv := by
    rw [List.getElem?_append_left (by omega)]
    exact hminfv
  obtain ⟨nmM, tyM, hminfvSh⟩ := hshapeA (p.nP + 1) minfv hminfvA
  have hheadSeq : Expr.instSeq (fvsP ++ xFvs) (p.nP + 2 + p.nF - 1)
      (.bvar p.nF) = minfv := by
    have h1 := Expr.instSeq_bvar (fvsP ++ xFvs) (p.nP + 2 + p.nF - 1) p.nF
      hbounded (by omega) (by rw [hspineLen]; omega)
    rw [show p.nP + 2 + p.nF - 1 - p.nF = p.nP + 1 from by omega,
      hminfvA] at h1
    exact (Option.some.inj h1).symm
  have hargsSeq : ((List.range p.nF).map fun j =>
      Expr.bvar (p.nF - 1 - j)).map
      (Expr.instSeq (fvsP ++ xFvs) (p.nP + 2 + p.nF - 1) ·) = xFvs := by
    refine List.ext_getElem? ?_
    intro j
    rcases Nat.lt_or_ge j p.nF with hj | hj
    · have h1 := Expr.instSeq_bvar (fvsP ++ xFvs) (p.nP + 2 + p.nF - 1)
        (p.nF - 1 - j) hbounded (by omega) (by rw [hspineLen]; omega)
      rw [show p.nP + 2 + p.nF - 1 - (p.nF - 1 - j) = p.nP + 2 + j from by
          omega,
        List.getElem?_append_right (by omega), hlenfvsP,
        show p.nP + 2 + j - (p.nP + 2) = j from by omega] at h1
      simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]
      exact h1.symm
    · have hb1 : j ≥ (((List.range p.nF).map fun k =>
          Expr.bvar (p.nF - 1 - k)).map
          (Expr.instSeq (fvsP ++ xFvs) (p.nP + 2 + p.nF - 1) ·)).length := by
        simp only [List.length_map, List.length_range]; omega
      rw [List.getElem?_eq_none hb1,
        List.getElem?_eq_none (by rw [hlenxFvs]; omega)]
  have heRi : interpExpr V val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
      (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty) lrest =
      some (SpineFold V (xs.getD (p.nP + 1) SetTheory.empty)
        (xs.drop (p.nP + 2))) := by
    rw [hRmid, directRuleBody, Expr.instSeq_mkAppN, hheadSeq, hargsSeq,
      hminfvSh]
    refine interp_mkAppN xFvs _ ?_ hspX
    simp only [interpExpr]
  -- ===== the body's annotations =====
  obtain ⟨Cv, hCvI, hCvmem⟩ := m₂.mem_type _ (find?_mem hCfind) ψ
  have hCannot := (m₂.annot_ok _ (find?_mem hCfind) ψ).1
  have hchainC : ChainSlots V (val' p.cvC.name ψ)
      (xs.take p.nP ++ xs.drop (p.nP + 2)) := by
    rw [hvalC, ← (show (ConstantInfo.ctorInfo cvCa p.nP p.nF).name =
      p.cvC.name from find?_name hCfind)]
    exact TeleFit.chainSlots hfitCfull hCannot hCvI hCvmem
  obtain ⟨Rv, hRvI⟩ := (hfrRa ψ).it
  have hRvmem := directRecVal_mem (directShape_stripPis hsh) hRvI
    (hfrRa ψ).an
    (directRec_body m₂ hrt hnz (hfrRa ψ) (hfrC ψ) hcq hstripC (hdomsCT ψ)
      (hfieldAt ψ) (hTfold ψ) (hCfold ψ) hTfind hTlps hTname hCfind hClps)
  have hchainR : ChainSlots V (val' cvRa.name ψ)
      (xs.take (p.nP + 2) ++ [tupleV (xs.drop (p.nP + 2))]) := by
    rw [hvalR ψ]
    exact TeleFit.chainSlots hfitFull (hfrRa ψ).an hRvI hRvmem
  obtain ⟨hActor, hictor⟩ := annotOk_spine (fvsP.take p.nP ++ xFvs)
    (.const p.cvC.name (cvCa.levelParams.map Level.param))
    (by simp only [AnnotOk]) hCi
    (fun x hx => by
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hfvAnnot x (List.mem_append_left _ (List.mem_of_mem_take hx'))
      · exact hfvAnnot x (List.mem_append_right _ hx'))
    hspC hchainC
  rw [hvalC, hCf] at hictor
  obtain ⟨hAbL, hibL⟩ := annotOk_spine
    (fvsP ++ [Expr.mkAppN (.const p.cvC.name
      (cvCa.levelParams.map Level.param)) (fvsP.take p.nP ++ xFvs)])
    (.const cvRa.name (cvRa.levelParams.map Level.param))
    (by simp only [AnnotOk]) hRi
    (by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hfvAnnot x (List.mem_append_left _ hx')
      · obtain rfl : x = Expr.mkAppN (.const p.cvC.name
            (cvCa.levelParams.map Level.param))
            (fvsP.take p.nP ++ xFvs) := by simpa using hx'
        exact hActor)
    (InterpSpine.append hspR
      (show InterpSpine val' (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
          [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: env₂.consts⟩ : Env) ψ
        (p.nP + 2 + p.nF) (fun l => xs.getD l SetTheory.empty) [_]
        [tupleV (xs.drop (p.nP + 2))] from ⟨hictor, trivial⟩))
    hchainR
  refine ⟨⟨SpineFold V (xs.getD (p.nP + 1) SetTheory.empty)
      (xs.drop (p.nP + 2)), hbodyVal, ?_⟩, hAbL⟩
  intro e hee
  rw [interp_erasedEq hee _ _, heRi]

/-! ### The projections' semantic obligations -/

/-- Inversion for `checkDirectProj` (stage 5, one field): the generated
type, its annotation and inference runs, and the stage's **two frame
pins** — the subject binder's domain against the family at the opened
parameters (frame `nP`), and the residual against the constructor's
`i`-th field domain instantiated at those parameters and at the earlier
projections (frame `nP + 1`). -/
theorem checkDirectProj_inv {env envOut : Env} {T C : Name} {lps : List Name}
    {nP nF i : Nat} {cvTa cvCa : ConstantVal} {F : Nat}
    (h : checkDirectProj (fueledOps F) T C lps nP nF cvTa cvCa env i
      = .ok envOut) :
    ∃ pty ptyA sty u fvsP prest sbs sbody sdom tFvs resid tfv cds fn fdom
      fbody fm rhsA,
      directProjTy T lps nP nF i cvTa.type cvCa.type = some pty ∧
      pty.hasFvar = false ∧ pty.looseBVarsBounded 0 = true ∧
      annotateCore env F 0 pty = .ok ptyA ∧
      ptyA.allLevelParamsDefined lps = true ∧
      ptyA.constsResolve env = true ∧
      ptyA.looseBVarsBounded 0 = true ∧
      ptyA.hasFvar = false ∧
      (ptyA.stripPis (nP + 1)).isSome = true ∧
      inferTypeCore env F 0 ptyA = .ok sty ∧
      ensureSortCore env F 0 sty = .ok u ∧
      env.find? (projFnName T i) = none ∧
      (∃ w : Unit, (checkProjShape ptyA cvCa.type nP nF : CheckM Unit)
        = .ok w) ∧
      openPisAtFvars nP ptyA 0 = some (fvsP, prest) ∧
      prest.stripPis 1 = some (sbs, sbody) ∧
      (sbs[0]?).map (·.2.1) = some sdom ∧
      isDefEqCore env F nP sdom
        (Expr.mkAppN (.const T (lps.map .param)) fvsP) = .ok true ∧
      openPisAtFvars 1 prest nP = some (tFvs, resid) ∧
      tFvs[0]? = some tfv ∧
      Expr.instPisAt (fvsP ++ (List.range i).map (fun j =>
          Expr.mkAppN (.const (projFnName T j) (lps.map .param))
            (fvsP ++ [tfv]))) cvCa.type
        = some (cds, .forallE fn fdom fbody fm) ∧
      isDefEqCore env F (nP + 1) resid fdom = .ok true ∧
      checkProjRule (fueledOps F) env ptyA cvCa lps nP nF i = .ok rhsA ∧
      envOut = ⟨.recInfo ⟨projFnName T i, lps, ptyA⟩ nP nP
        [⟨C, nF, nP,
          if Expr.recRulePlain ptyA nP nP nP then .plain else .inert, rhsA⟩]
        :: env.consts⟩ := by
  rw [checkDirectProj] at h
  simp only [fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, Bind.bind, Except.bind] at h
  -- the generated type
  obtain ⟨pty, hpty⟩ : ∃ q, directProjTy T lps nP nF i cvTa.type cvCa.type
      = some q := by
    cases hh : directProjTy T lps nP nF i cvTa.type cvCa.type with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hpty] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  by_cases hsc : (!pty.hasFvar && pty.looseBVarsBounded 0) = true
  case neg =>
    rw [if_neg hsc] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hsc] at h
  obtain ⟨hptyf, hptyb⟩ : pty.hasFvar = false ∧ pty.looseBVarsBounded 0 = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsc; exact hsc
  -- the annotation
  obtain ⟨ptyA, hann, h⟩ := Except.bind_ok h
  by_cases hwf : (ptyA.allLevelParamsDefined lps && ptyA.constsResolve env &&
      ptyA.looseBVarsBounded 0 && !ptyA.hasFvar) = true
  case neg =>
    rw [if_neg hwf] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hwf] at h
  obtain ⟨⟨⟨hlp, hres⟩, hbb⟩, hfv⟩ :
      ((ptyA.allLevelParamsDefined lps = true ∧ ptyA.constsResolve env = true) ∧
        ptyA.looseBVarsBounded 0 = true) ∧ ptyA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hwf; exact hwf
  by_cases hst : (ptyA.stripPis (nP + 1)).isSome = true
  case neg =>
    rw [if_neg hst] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hst] at h
  obtain ⟨sty, hsty, h⟩ := Except.bind_ok h
  obtain ⟨u, hu, h⟩ := Except.bind_ok h
  by_cases hnone : (env.find? (projFnName T i)).isNone = true
  case neg =>
    rw [if_neg hnone] at h
    simp only [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  rw [if_pos hnone] at h
  obtain ⟨w, hshape, h⟩ := Except.bind_ok h
  -- the parameter opening
  obtain ⟨q1, hq1⟩ : ∃ q, openPisAtFvars nP ptyA 0 = some q := by
    cases hh : openPisAtFvars nP ptyA 0 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq1] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨q2, hq2⟩ : ∃ q, q1.2.stripPis 1 = some q := by
    cases hh : q1.2.stripPis 1 with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq2] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨sdom, hsdom⟩ : ∃ x, (q2.1[0]?).map (·.2.1) = some x := by
    cases hh : (q2.1[0]?).map (·.2.1) with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some x => exact ⟨x, rfl⟩
  rw [hsdom] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨b1, hb1, h⟩ := Except.bind_ok h
  cases b1 with
  | false =>
    simp only [Bool.false_eq_true, if_false, throw, throwThe,
      MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  | true =>
  simp only [if_true] at h
  -- the subject opening
  obtain ⟨q3, hq3⟩ : ∃ q, openPisAtFvars 1 q1.2 nP = some q := by
    cases hh : openPisAtFvars 1 q1.2 nP with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq3] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨tfv, htfv⟩ : ∃ x, q3.1[0]? = some x := by
    cases hh : q3.1[0]? with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some x => exact ⟨x, rfl⟩
  rw [htfv] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  -- the constructor field telescope, walked at the earlier projections
  obtain ⟨q4, hq4⟩ : ∃ q, Expr.instPisAt (q1.1 ++ (List.range i).map
      (fun j => Expr.mkAppN (.const (projFnName T j) (lps.map .param))
        (q1.1 ++ [tfv]))) cvCa.type = some q := by
    cases hh : Expr.instPisAt (q1.1 ++ (List.range i).map
        (fun j => Expr.mkAppN (.const (projFnName T j) (lps.map .param))
          (q1.1 ++ [tfv]))) cvCa.type with
    | none =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
    | some q => exact ⟨q, rfl⟩
  rw [hq4] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨fn, fdom, fbody, fm, hcres⟩ :
      ∃ n d b m, q4.2 = Expr.forallE n d b m := by
    cases hh : q4.2 with
    | forallE n d b m => exact ⟨n, d, b, m, rfl⟩
    | bvar _ | fvar _ _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ _
    | letE _ _ _ _ | lit _ | proj _ _ _ =>
      rw [hh] at h
      simp only [unwrapOr, throw, throwThe, MonadExceptOf.throw,
        Except.bind] at h
      exact nomatch h
  rw [hcres] at h
  simp only [unwrapOr, pure, Except.pure, Except.bind] at h
  obtain ⟨b2, hb2, h⟩ := Except.bind_ok h
  cases b2 with
  | false =>
    simp only [Bool.false_eq_true, if_false, throw, throwThe,
      MonadExceptOf.throw, Except.bind] at h
    exact nomatch h
  | true =>
  simp only [if_true] at h
  obtain ⟨rhsA, hrule, h⟩ := Except.bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨pty, ptyA, sty, u, q1.1, q1.2, q2.1, q2.2, sdom, q3.1, q3.2, tfv,
    q4.1, fn, fdom, fbody, fm, rhsA, hpty, hptyf, hptyb, hann, hlp, hres,
    hbb, hfv, hst, hsty, hu, Option.isNone_iff_eq_none.mp hnone, ⟨w, hshape⟩,
    hq1, hq2, hsdom, hb1, hq3, htfv, by rw [hq4, ← hcres], hb2, hrule, h.symm⟩

/-- The projection phase's fold invariant — the direct analogue of
`ProjPhaseInv`.  Every already-installed projection function of the
block is stored at the block's own level parameters, its type is fit by
the canonical spine `p⃗ t`, and its value folds along that spine to
field `j` of the subject.  Field `i`'s generated type substitutes
exactly those applications for the earlier fields, so this is what
identifies the residual pin's right-hand side. -/
def DirectProjInv (V : Type u) [SetTheory V] (cval : ConstVal V) (env : Env)
    (φ : Name → Nat) (T : Name) (lps : List Name) (tyT : Expr)
    (nP i : Nat) : Prop :=
  ∀ j, j < i → ∃ cij : ConstantInfo,
    env.find? (projFnName T j) = some cij ∧
    cij.toConstantVal.levelParams = lps ∧
    ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V cval env φ 0 (rho0 V) tyT ps d₁ ρ₁ r → ps.length = nP →
      ∀ x : V, x ∈ˢ SpineFold V (cval T φ) ps →
        (∃ d' ρ' rest, TeleFit V cval env φ 0 (rho0 V)
          cij.toConstantVal.type (ps ++ [x]) d' ρ' rest) ∧
        SpineFold V (cval (projFnName T j) φ) (ps ++ [x]) = projV j x

/-- The projection stage's **parameter half**, at any fitting parameter
spine: the fit crosses to the constructor's and the type former's
telescopes at one frame (`TeleFit.transfer` over the stage's own
parameter-domain pins and the constructor stage's), the field telescope
is small there, the type former's value is the tower over it, and the
subject binder's domain — pinned against the family at the opened
parameters — interprets to exactly that value. -/
theorem directProj_param_stage {envP : Env} (mP : EnvModel V envP)
    {F : Nat} {φ : Name → Nat} {p : DirectParts}
    {cvTa cvCa : ConstantVal} {ptyA prest sdom sbody crestC : Expr}
    {n₀ : Name} {m₀ : BinderMeta} {fvsP fvsC : List Expr}
    (hfrPty : FrameOk V mP.val envP φ 0 (rho0 V) ptyA)
    (hopP : openPisAtFvars p.nP ptyA 0 = some (fvsP, prest))
    (hprest : prest = Expr.forallE n₀ sdom sbody m₀)
    (hpin1 : isDefEqCore envP F p.nP sdom
      (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param)) fvsP)
      = .ok true)
    (hAgPC : DomsAgree V mP.val envP φ p.nP 0 (rho0 V) ptyA 0 (rho0 V)
      cvCa.type)
    (hdomsCT : DomsInterpEq V mP.val envP φ p.nP 0 (rho0 V) cvCa.type
      cvTa.type)
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsC, crestC))
    (hfieldAt : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid →
      ps.length = p.nP →
      FieldTele V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid)
    (hTfold : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      SpineFold V (mP.val p.cvT.name φ) ps =
        sigmaTowerV V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ crestC)
    (hTfind : envP.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTname : cvTa.name = p.cvT.name) :
    ∀ (ps : List V) (ρ' : Nat → V),
      TeleFit V mP.val envP φ 0 (rho0 V) ptyA ps p.nP ρ' prest →
      ps.length = p.nP →
      (∃ restT, TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps p.nP ρ'
        restT) ∧
      TeleFit V mP.val envP φ 0 (rho0 V) cvCa.type ps p.nP ρ' crestC ∧
      interpExpr V mP.val envP φ p.nP ρ' sdom =
        some (SpineFold V (mP.val p.cvT.name φ) ps) ∧
      FieldTele V mP.val envP φ (p.resSort.eval φ) p.nF p.nP ρ' crestC ∧
      SpineFold V (mP.val p.cvT.name φ) ps =
        sigmaTowerV V mP.val envP φ (p.resSort.eval φ) p.nF p.nP ρ' crestC := by
  obtain ⟨hopPinst, hlenfvsP, hshapeP⟩ := openPisAtFvars_spec p.nP 0 hopP
  intro ps ρ' hfitPs hlenPs
  -- the fit, transferred to the constructor's and the former's telescopes
  obtain ⟨dC, ρC, restC0, hfitC0⟩ := TeleFit.transfer p.nP hfitPs hlenPs hAgPC
  obtain ⟨hdC, fvsC0, hopC0⟩ := TeleFit_open p.nP hfitC0 hlenPs
  rw [Nat.zero_add] at hdC
  subst hdC
  have hrestC : restC0 = crestC := by
    rw [hcq] at hopC0
    exact (congrArg Prod.snd (Option.some.inj hopC0)).symm
  have hρC : ρC = ρ' := TeleFit.rho_det hfitC0 hfitPs
  rw [hrestC, hρC] at hfitC0
  obtain ⟨dT, ρT0, restT0, hfitT0⟩ := TeleFit.transfer p.nP hfitC0 hlenPs hdomsCT
  obtain ⟨hdT, -, -⟩ := TeleFit_open p.nP hfitT0 hlenPs
  rw [Nat.zero_add] at hdT
  subst hdT
  have hρT : ρT0 = ρ' := TeleFit.rho_det hfitT0 hfitPs
  rw [hρT] at hfitT0
  refine ⟨⟨restT0, hfitT0⟩, hfitC0, ?_, hfieldAt _ p.nP ρ' crestC hfitC0 hlenPs,
    hTfold _ p.nP ρ' restT0 hfitT0 hlenPs⟩
  -- the subject binder's domain is the family at the parameters
  have hparFr : ∀ a ∈ fvsP, FrameOk V mP.val envP φ p.nP ρ' a :=
    fun a ha => FrameOk.openVars p.nP hopP hfitPs hlenPs hfrPty a ha
  have hspFv : FvarSpine p.nP ρ' fvsP ps := by
    refine FvarSpine.of_pointwise (by rw [hlenfvsP, hlenPs]) ?_
    intro k a v ha hv
    obtain ⟨nm, hnm⟩ := hshapeP k a ha
    have hk : k < p.nP := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
      rw [hlenfvsP] at hlt; exact hlt
    refine ⟨0 + k, nm, Expr.fvarTypeD a, hnm, by omega, ?_⟩
    have h0 := hfitPs.slots k (by rw [hlenPs]; exact hk)
    rw [Nat.zero_add] at h0 ⊢
    rw [h0, List.getD_eq_getElem?_getD, hv]
    rfl
  have hspine : InterpSpine mP.val envP φ p.nP ρ' fvsP ps := by
    refine InterpSpine.of_pointwise (by rw [hlenfvsP, hlenPs]) ?_
    intro k a v ha hv
    obtain ⟨j, n, ty, rfl, hlt, hval⟩ := FvarSpine.pointwise hspFv k ha hv
    rw [interpExpr, hval]
  have hconstI : interpExpr V mP.val envP φ p.nP ρ'
      (.const p.cvT.name (p.cvT.levelParams.map Level.param)) =
      some (mP.val p.cvT.name φ) := by
    rw [interp_const hTfind (by
      show (p.cvT.levelParams.map Level.param).length = cvTa.levelParams.length
      rw [hTlps, List.length_map])]
    have hsub : Level.substFn φ
        (ConstantInfo.indInfo cvTa (directCaps p)).toConstantVal.levelParams
        (p.cvT.levelParams.map Level.param) = φ := by
      show Level.substFn φ cvTa.levelParams
        (p.cvT.levelParams.map Level.param) = φ
      rw [hTlps]
      exact funext (fun q => Level.substFn_map_param)
    rw [hsub]
  obtain ⟨Tv, hTvI, hTvmem⟩ := mP.mem_type _ (find?_mem hTfind) φ
  have hTannot := (mP.annot_ok _ (find?_mem hTfind) φ).1
  have hchain : ChainSlots V (mP.val p.cvT.name φ) ps := by
    rw [← hTname]
    exact TeleFit.chainSlots hfitT0 hTannot hTvI hTvmem
  obtain ⟨hfamA, hfamI⟩ :=
    annotOk_spine fvsP (.const p.cvT.name (p.cvT.levelParams.map Level.param))
      (by simp only [AnnotOk]) hconstI (fun a ha => (hparFr a ha).an)
      hspine hchain
  have hfrFam : FrameOk V mP.val envP φ p.nP ρ'
      ((Expr.const p.cvT.name (p.cvT.levelParams.map Level.param)).mkAppN
        fvsP) := by
    refine ⟨Expr.WScoped.mkAppN (by simp only [Expr.WScoped])
        (fun a ha => (hparFr a ha).ws),
      looseBVarsBounded_mkAppN (by rfl) (fun a ha => (hparFr a ha).bb),
      ?_, ?_, hfamA, _, hfamI⟩
    · intro l hl
      rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · simp [Expr.fvarLeaves] at hl'
      · exact (hparFr y hy).lb l hly
    · intro l hl
      rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · simp [Expr.fvarLeaves] at hl'
      · exact (hparFr y hy).fv l hly
  have hfrPrest : FrameOk V mP.val envP φ p.nP ρ'
      (Expr.forallE n₀ sdom sbody m₀) := by
    have h := FrameOk.ofTeleFit hfitPs hfrPty
    rw [hprest] at h
    exact h
  obtain ⟨Asub, hsdomI⟩ := hfrPrest.dom.it
  have hAsub : Asub = SpineFold V (mP.val p.cvT.name φ) ps :=
    isDefEqCore_sound mP F hpin1 hfrPrest.dom.ws hfrFam.ws hfrPrest.dom.bb
      hfrFam.bb hfrPrest.dom.lb hfrFam.lb hfrPrest.dom.fv hfrFam.fv
      hfrPrest.dom.an hfrFam.an hsdomI hfamI
  rw [← hAsub]
  exact hsdomI

set_option maxHeartbeats 1000000 in
/-- **The projection stage's semantic kit.**

At a fitting spine `p⃗ t` the stored (annotated) projection type's
residual is pinned against the constructor's `i`-th field domain
instantiated at the parameters and at the earlier projections of `t`
(`checkDirectProj`'s second frame pin).  Those projections' values are
`projV j t` by the phase invariant, so the pin's right-hand side
interprets to exactly the `i`-th domain along the *canonical* field
spine of `t` — and structure eta (`directProj_body_mem`) puts
`projV i t` in it.  That is the λ-tower body obligation; the last
clause is its converse direction, the fit of the stored type at every
canonical spine, which is what the fold equation consumes. -/
theorem directProj_facts {envP : Env} (mP : EnvModel V envP)
    {F : Nat} {φ : Name → Nat} {p : DirectParts} {i : Nat}
    {cvTa cvCa : ConstantVal} {envOut : Env}
    {fvsC : List Expr} {crestC : Expr}
    {cbs : List (Name × Expr × BinderMeta)}
    (hpj : checkDirectProj (fueledOps F) p.cvT.name p.cvC.name
      p.cvT.levelParams p.nP p.nF cvTa cvCa envP i = .ok envOut)
    (hi : i < p.nF)
    (hnz : p.resSort.isNonZero = true)
    (hfrC : FrameOk V mP.val envP φ 0 (rho0 V) cvCa.type)
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsC, crestC))
    (hstripC : Expr.stripPis (p.nP + p.nF) cvCa.type = some (cbs,
      directFam p.cvT.name p.cvT.levelParams p.nP p.nF))
    (hdomsCT : DomsInterpEq V mP.val envP φ p.nP 0 (rho0 V)
      cvCa.type cvTa.type)
    (hfieldAt : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid →
      ps.length = p.nP →
      FieldTele V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid)
    (hTfold : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      SpineFold V (mP.val p.cvT.name φ) ps =
        sigmaTowerV V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ crestC)
    (hinv : DirectProjInv V mP.val envP φ p.cvT.name p.cvT.levelParams
      cvTa.type p.nP i)
    (hTfind : envP.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTname : cvTa.name = p.cvT.name) :
    ∃ ptyA rhsA,
      envOut = ⟨.recInfo ⟨projFnName p.cvT.name i, p.cvT.levelParams, ptyA⟩
        p.nP p.nP [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain ptyA p.nP p.nP p.nP then .plain else .inert,
          rhsA⟩] :: envP.consts⟩ ∧
      FrameOk V mP.val envP φ 0 (rho0 V) ptyA ∧
      (Expr.stripPis (p.nP + 1) ptyA).isSome = true ∧
      TeleBody V mP.val envP φ (p.nP + 1) 0 (rho0 V) ptyA
        (fun _ _ xs => projV i (xs.getD p.nP SetTheory.empty)) ∧
      ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
        TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
        ps.length = p.nP →
        ∀ x : V, x ∈ˢ SpineFold V (mP.val p.cvT.name φ) ps →
          ∃ d' ρ' rest, TeleFit V mP.val envP φ 0 (rho0 V) ptyA (ps ++ [x])
            d' ρ' rest := by
  obtain ⟨pty, ptyA, sty, u, fvsP, prest, sbs, sbody, sdom, tFvs, resid, tfv,
    cds, fn, fdom, fbody, fm, rhsA, hpty, hptyf, hptyb, hann, hlpA, hresA,
    hbbA, hfvA, hstA, hsty, hu, hnone, hshape, hopP, hsstrip, hsdom,
    hpin1, hopT, htfv, hcinst, hpin2, hrule, henv⟩ := checkDirectProj_inv hpj
  -- the annotated projection type's frame conditions
  have hAptyA : AnnotOk V mP.val envP φ 0 (rho0 V) ptyA :=
    annotate_sound mP _ hann (Expr.WScoped.of_not_hasFvar hptyf) hptyb
      (Expr.LeavesBounded.of_not_hasFvar hptyf) (rho0 V)
      (FvarsOk.of_not_hasFvar hptyf)
  have hfrPty : FrameOk V mP.val envP φ 0 (rho0 V) ptyA := by
    obtain ⟨⟨v, tv, hvi, -, -⟩, -, -⟩ :=
      inferTypeCore_sound (φ := φ) mP F hsty
        (Expr.WScoped.of_not_hasFvar hfvA) hbbA
        (Expr.LeavesBounded.of_not_hasFvar hfvA)
        (FvarsOk.of_not_hasFvar hfvA) hAptyA
    exact ⟨Expr.WScoped.of_not_hasFvar hfvA, hbbA,
      Expr.LeavesBounded.of_not_hasFvar hfvA, FvarsOk.of_not_hasFvar hfvA,
      hAptyA, v, hvi⟩
  -- the parameter-domain agreement, from `checkProjRule`'s fixed-frame pins
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fvsP', rest0, cdomsP,
    crestP, -, -, -, -, hopP', hcinstP, hdeParsP, -, -, -, -⟩ :=
    checkProjRule_inv hrule
  have hfvsPeq : fvsP' = fvsP := by
    rw [hopP] at hopP'
    exact (congrArg Prod.fst (Option.some.inj hopP')).symm
  rw [hfvsPeq] at hcinstP hdeParsP
  have hAgPC : DomsAgree V mP.val envP φ p.nP 0 (rho0 V) ptyA 0 (rho0 V)
      cvCa.type :=
    DomsAgree.of_pins_inst_at mP F p.nP 0 (p.nP + p.nF) (rho0 V) ptyA
      cvCa.type fvsP prest cdomsP crestP (by omega) hopP hcinstP
      (fun j a b ha hb => DefEqListOk.pointwise hdeParsP j
        (by rw [List.getElem?_map, ha]; rfl) hb)
      hfrPty hfrC
  -- syntactic data of the constructor telescope
  have hCcl : cvCa.type.hasFvar = false :=
    not_hasFvar_of_fvarsBelow_zero hfrC.ws.fvarsBelow
  obtain ⟨hcqinst, hlenfvsC, hshapeC⟩ := openPisAtFvars_spec p.nP 0 hcq
  obtain ⟨hopPinst, hlenfvsP, hshapeP⟩ := openPisAtFvars_spec p.nP 0 hopP
  -- the constructor's `i`-th field domain, closed and position-bounded
  obtain ⟨mid₀, hstripL, hstripR⟩ :=
    Expr.stripPis_add (p.nP + i) (p.nF - i)
      (show Expr.stripPis ((p.nP + i) + (p.nF - i)) cvCa.type = _ from by
        rw [show (p.nP + i) + (p.nF - i) = p.nP + p.nF from by omega]
        exact hstripC)
  obtain ⟨mid₁, hstrip1, -⟩ := Expr.stripPis_add 1 (p.nF - i - 1)
    (show Expr.stripPis (1 + (p.nF - i - 1)) mid₀ = _ from by
      rw [show 1 + (p.nF - i - 1) = p.nF - i from by omega]
      exact hstripR)
  obtain ⟨n₁, D₀, m₁, hmid₀, -⟩ := stripPis_one hstrip1
  have hmid₀cl : mid₀.hasFvar = false :=
    stripPis_body_hasFvar (p.nP + i) hstripL hCcl
  have hD₀cl : D₀.hasFvar = false := by
    rw [hmid₀] at hmid₀cl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hmid₀cl
    exact hmid₀cl.1
  have hD₀b : D₀.looseBVarsBounded (p.nP + i) = true := by
    have h := stripPis_body_bounded (p.nP + i) hstripL hfrC.bb
    rw [hmid₀, Nat.zero_add] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨n₀, sd₀, m₀, hprest0, hsbs⟩ := stripPis_one hsstrip
  have hsd : sd₀ = sdom := by rw [hsbs] at hsdom; simpa using hsdom
  rw [hsd] at hprest0
  have hprest : prest = Expr.forallE n₀ sdom sbody m₀ := hprest0
  have hopTeq : tFvs = [Expr.fvar p.nP n₀ sdom] ∧
      resid = sbody.instantiate1 (Expr.fvar p.nP n₀ sdom) := by
    rw [hprest] at hopT
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hopT
    exact ⟨hopT.1.symm, hopT.2.symm⟩
  obtain rfl : tfv = Expr.fvar p.nP n₀ sdom := by
    rw [hopTeq.1] at htfv; simpa using htfv.symm
  obtain ⟨pa, hpaDef⟩ : ∃ l : List Expr, l = (List.range i).map fun j =>
      Expr.mkAppN (.const (projFnName p.cvT.name j)
        (p.cvT.levelParams.map Level.param))
        (fvsP ++ [Expr.fvar p.nP n₀ sdom]) := ⟨_, rfl⟩
  rw [← hpaDef] at hcinst
  have hlenpa : pa.length = i := by rw [hpaDef]; simp
  have hpaget : ∀ k, k < i → pa[k]? = some (Expr.mkAppN
      (.const (projFnName p.cvT.name k) (p.cvT.levelParams.map Level.param))
      (fvsP ++ [Expr.fvar p.nP n₀ sdom])) := by
    intro k hk
    rw [hpaDef, List.getElem?_map, List.getElem?_range hk]
    rfl
  have hpamem : ∀ a ∈ pa, ∃ k, k < i ∧ a = Expr.mkAppN
      (.const (projFnName p.cvT.name k) (p.cvT.levelParams.map Level.param))
      (fvsP ++ [Expr.fvar p.nP n₀ sdom]) := by
    intro a ha
    rw [hpaDef] at ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    exact ⟨k, List.mem_range.mp hk, rfl⟩
  -- the parameter half, at any fitting parameter spine
  have hstage := directProj_param_stage mP hfrPty hopP hprest hpin1 hAgPC
    hdomsCT hcq hfieldAt hTfold hTfind hTlps hTname
  have hfitClause : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      ∀ x : V, x ∈ˢ SpineFold V (mP.val p.cvT.name φ) ps →
        ∃ d' ρ' rest, TeleFit V mP.val envP φ 0 (rho0 V) ptyA (ps ++ [x])
          d' ρ' rest := by
    intro ps d₁ ρ₁ r hfitT hlenPs x hx
    have hAgTP : DomsAgree V mP.val envP φ p.nP 0 (rho0 V) cvTa.type 0
        (rho0 V) ptyA :=
      DomsAgree.trans p.nP (DomsAgree.symm p.nP hfrC hdomsCT)
        (DomsAgree.symm p.nP hfrPty hAgPC)
    obtain ⟨dQ, ρQ, restQ, hfitQ⟩ := TeleFit.transfer p.nP hfitT hlenPs hAgTP
    obtain ⟨hdQ, fvsQ, hopQ⟩ := TeleFit_open p.nP hfitQ hlenPs
    rw [Nat.zero_add] at hdQ
    subst hdQ
    have hrestQ : restQ = prest := by
      rw [hopP] at hopQ
      exact (congrArg Prod.snd (Option.some.inj hopQ)).symm
    rw [hrestQ] at hfitQ
    obtain ⟨-, -, hsdomEq, -, -⟩ := hstage ps ρQ hfitQ hlenPs
    have htail : TeleFit V mP.val envP φ p.nP ρQ prest [x] (p.nP + 1)
        (updV V ρQ p.nP x) (sbody.instantiate1 (Expr.fvar p.nP n₀ sdom)) := by
      rw [hprest]
      exact TeleFit.cons hsdomEq hx TeleFit.nil
    exact ⟨_, _, _, TeleFit_append hfitQ htail⟩
  refine ⟨ptyA, rhsA, henv, hfrPty, hstA, ?_, hfitClause⟩
  -- the projection type's telescope, at a fitting spine
  intro xs d' ρ' rest hfit hlen
  have hxs : xs = xs.take p.nP ++ xs.drop p.nP :=
    (List.take_append_drop _ xs).symm
  rw [hxs] at hfit
  obtain ⟨dP, ρP, midP, hfitP, hfitX⟩ := TeleFit_split hfit
  have hlenP : (xs.take p.nP).length = p.nP := by rw [List.length_take]; omega
  obtain ⟨hdP, fvs', hopen'⟩ := TeleFit_open p.nP hfitP hlenP
  rw [Nat.zero_add] at hdP
  subst hdP
  have hmidP : midP = prest := by
    rw [hopP] at hopen'
    exact (congrArg Prod.snd (Option.some.inj hopen')).symm
  rw [hmidP] at hfitP hfitX
  have hlend : (xs.drop p.nP).length = 1 := by rw [List.length_drop]; omega
  obtain ⟨x, hxd⟩ : ∃ x, xs.drop p.nP = [x] := by
    cases hL : xs.drop p.nP with
    | nil => rw [hL] at hlend; exact nomatch hlend
    | cons a t =>
      cases t with
      | nil => exact ⟨a, rfl⟩
      | cons b t2 => rw [hL] at hlend; simp at hlend
  have hxsNP : xs.getD p.nP SetTheory.empty = x := by
    rw [List.getD_eq_getElem?_getD,
      show xs[p.nP]? = (List.drop p.nP xs)[0]? from by
        simp [List.getElem?_drop], hxd]
    rfl
  rw [hxd, hprest] at hfitX
  cases hfitX with
  | @cons _ _ _ _ _ _ _ _ _ _ _ Asub hsdomI hxmem hnil =>
    obtain ⟨rfl, rfl, rfl⟩ := TeleFit_nil_eq hnil
    -- the parameter fit on the constructor's and the former's telescopes
    obtain ⟨⟨restT0, hfitT0⟩, hfitC0, hsdomEq, hfldC, hTf⟩ :=
      hstage (xs.take p.nP) ρP hfitP hlenP
    have hparFr : ∀ a ∈ fvsP, FrameOk V mP.val envP φ p.nP ρP a :=
      fun a ha => FrameOk.openVars p.nP hopP hfitP hlenP hfrPty a ha
    have hspFv : FvarSpine p.nP ρP fvsP (xs.take p.nP) := by
      refine FvarSpine.of_pointwise (by rw [hlenfvsP, hlenP]) ?_
      intro k a v ha hv
      obtain ⟨nm, hnm⟩ := hshapeP k a ha
      have hk : k < p.nP := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
        rw [hlenfvsP] at hlt; exact hlt
      refine ⟨0 + k, nm, Expr.fvarTypeD a, hnm, by omega, ?_⟩
      have h0 := hfitP.slots k (by rw [hlenP]; exact hk)
      rw [Nat.zero_add] at h0 ⊢
      rw [h0, List.getD_eq_getElem?_getD, hv]
      rfl
    have hfrPrest : FrameOk V mP.val envP φ p.nP ρP
        (Expr.forallE n₀ sdom sbody m₀) := by
      have h := FrameOk.ofTeleFit hfitP hfrPty
      rw [hprest] at h
      exact h
    have hAsub : Asub = SpineFold V (mP.val p.cvT.name φ) (xs.take p.nP) :=
      Option.some.inj (hsdomI.symm.trans hsdomEq)
    have hxTow : x ∈ˢ sigmaTowerV V mP.val envP φ (p.resSort.eval φ) p.nF
        p.nP ρP crestC := by
      rw [← hTf, ← hAsub]; exact hxmem
    -- the goal's residual interprets
    obtain ⟨Q, hQ⟩ := (FrameOk.ofTeleFit hfit hfrPty).it
    refine ⟨Q, hQ, ?_⟩
    show projV i (xs.getD p.nP SetTheory.empty) ∈ˢ Q
    rw [hxsNP]
    refine directProj_body_mem (Level.isNonZero_sound hnz φ) hi hfldC hxTow ?_
    intro dF ρF rF hfitPjs
    obtain ⟨pjs, hpjsDef⟩ : ∃ l : List V,
        l = (List.range p.nF).map fun j => projV j x := ⟨_, rfl⟩
    rw [← hpjsDef] at hfitPjs ⊢
    have hlenpjs : pjs.length = p.nF := by rw [hpjsDef]; simp
    have hpjsget : ∀ j, j < p.nF → pjs[j]? = some (projV j x) := by
      intro j hj
      rw [hpjsDef, List.getElem?_map, List.getElem?_range hj]
      rfl
    rw [show pjs.getD i SetTheory.empty = projV i x from by
      rw [List.getD_eq_getElem?_getD, hpjsget i hi]; rfl]
    -- split the canonical field spine at `i`
    rw [show pjs = pjs.take i ++ pjs.drop i from
      (List.take_append_drop _ _).symm] at hfitPjs
    obtain ⟨dI, ρI, midI, hfitI, hfitRest⟩ := TeleFit_split hfitPjs
    have hlenI : (pjs.take i).length = i := by
      rw [List.length_take, hlenpjs]; omega
    obtain ⟨hdI, xFvsI, hopI⟩ := TeleFit_open i hfitI hlenI
    subst hdI
    have hdropi : pjs.drop i = projV i x :: pjs.drop (i + 1) := by
      have hlt : i < pjs.length := by rw [hlenpjs]; exact hi
      rw [List.drop_eq_getElem_cons hlt]
      congr 1
      have h := hpjsget i hi
      rw [List.getElem?_eq_getElem hlt] at h
      exact Option.some.inj h
    rw [hdropi] at hfitRest
    -- the `i`-th *opened* field domain, as an instantiation sequence
    obtain ⟨hxinst, hlenxFvsI, hshapexI⟩ := openPisAtFvars_spec i p.nP hopI
    have hlenR : (fvsC ++ xFvsI).length = p.nP + i := by
      rw [List.length_append, hlenfvsC, hlenxFvsI]
    obtain ⟨hmidIeq, -⟩ :=
      instPisAt_stripPis (fvsC ++ xFvsI)
        (instPisAt_append_of fvsC hcqinst hxinst) (by rw [hlenR]; exact hstripL)
    rw [hlenR, hmid₀,
      instSeq_forallE (fvsC ++ xFvsI) (p.nP + i - 1) n₁ D₀ mid₁ m₁
        (by rw [hlenR]; omega)] at hmidIeq
    rw [hmidIeq] at hfitRest
    -- the `i`-th *walked* field domain: the pin's right-hand side
    have hlenPA : (fvsP ++ pa).length = p.nP + i := by
      rw [List.length_append, hlenfvsP, hlenpa]
    obtain ⟨hfdomEq, -⟩ :=
      instPisAt_stripPis (fvsP ++ pa) hcinst (by rw [hlenPA]; exact hstripL)
    rw [hlenPA, hmid₀,
      instSeq_forallE (fvsP ++ pa) (p.nP + i - 1) n₁ D₀ mid₁ m₁
        (by rw [hlenPA]; omega)] at hfdomEq
    have hfdom : fdom = instSeq (fvsP ++ pa) (p.nP + i - 1) D₀ := by
      have h := hfdomEq
      simp only [Expr.forallE.injEq] at h
      exact h.2.1
    -- the subject variable and the earlier projections' applications
    have hfrPrestDom := hfrPrest.dom
    have hfrTfv : FrameOk V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
        (Expr.fvar p.nP n₀ sdom) := by
      refine ⟨?_, rfl, LeavesBounded.fvar hfrPrestDom.bb hfrPrestDom.lb, ?_,
        by simp only [AnnotOk], x, by rw [interpExpr]; simp [updV]⟩
      · simp only [Expr.WScoped]
        exact ⟨by omega, hfrPrestDom.ws⟩
      · intro l hl
        simp only [Expr.fvarLeaves, List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact ⟨by omega, AnnotOk.weaken_top hfrPrestDom.ws hfrPrestDom.an,
            Asub, by rw [interp_weaken_top hfrPrestDom.ws]; exact hsdomI,
            by simpa [updV] using hxmem⟩
        · exact (FrameOk.weaken_top hfrPrestDom).fv l hl
    have hparFr' : ∀ a ∈ fvsP, FrameOk V mP.val envP φ (p.nP + 1)
        (updV V ρP p.nP x) a := fun a ha => FrameOk.weaken_top (hparFr a ha)
    have hspine' : InterpSpine mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
        (fvsP ++ [Expr.fvar p.nP n₀ sdom]) (xs.take p.nP ++ [x]) := by
      refine InterpSpine.append ?_ ?_
      · refine InterpSpine.of_pointwise (by rw [hlenfvsP, hlenP]) ?_
        intro k a v ha hv
        obtain ⟨j, n, ty, rfl, hlt, hval⟩ := FvarSpine.pointwise hspFv k ha hv
        rw [interpExpr]
        simp only [updV]
        rw [if_neg (by omega), hval]
      · refine InterpSpine.of_pointwise rfl ?_
        intro k a v ha hv
        cases k with
        | zero =>
          obtain rfl := Option.some.inj ha
          obtain rfl := Option.some.inj hv
          rw [interpExpr]; simp [updV]
        | succ k => simp at ha
    have hprojFact : ∀ k, k < i →
        FrameOk V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
          (Expr.mkAppN (.const (projFnName p.cvT.name k)
            (p.cvT.levelParams.map Level.param))
            (fvsP ++ [Expr.fvar p.nP n₀ sdom])) ∧
        interpExpr V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
          (Expr.mkAppN (.const (projFnName p.cvT.name k)
            (p.cvT.levelParams.map Level.param))
            (fvsP ++ [Expr.fvar p.nP n₀ sdom])) = some (projV k x) := by
      intro k hk
      obtain ⟨cik, hfind, hlpsk, hfacts⟩ := hinv k hk
      obtain ⟨⟨dk, ρk, restk, hfitk⟩, hfoldk⟩ :=
        hfacts (xs.take p.nP) p.nP ρP restT0 hfitT0 hlenP x
          (by rw [← hAsub]; exact hxmem)
      obtain ⟨Pk, hPkI, hPkmem⟩ := mP.mem_type _ (find?_mem hfind) φ
      have hnamek : cik.name = projFnName p.cvT.name k := find?_name hfind
      have hAnnotk := (mP.annot_ok _ (find?_mem hfind) φ).1
      have hchaink : ChainSlots V (mP.val (projFnName p.cvT.name k) φ)
          (xs.take p.nP ++ [x]) := by
        refine TeleFit.chainSlots hfitk hAnnotk hPkI ?_
        rw [← hnamek]; exact hPkmem
      have hconstk : interpExpr V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
          (.const (projFnName p.cvT.name k)
            (p.cvT.levelParams.map Level.param)) =
          some (mP.val (projFnName p.cvT.name k) φ) := by
        rw [interp_const hfind (by rw [hlpsk, List.length_map])]
        rw [show Level.substFn φ cik.toConstantVal.levelParams
            (p.cvT.levelParams.map Level.param) = φ from by
          rw [hlpsk]; exact funext (fun q => Level.substFn_map_param)]
      have hargFr : ∀ a ∈ fvsP ++ [Expr.fvar p.nP n₀ sdom],
          FrameOk V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x) a := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hparFr' a ha
        · obtain rfl : a = Expr.fvar p.nP n₀ sdom := by simpa using ha
          exact hfrTfv
      obtain ⟨hAppA, hAppI⟩ :=
        annotOk_spine (fvsP ++ [Expr.fvar p.nP n₀ sdom])
          (.const (projFnName p.cvT.name k)
            (p.cvT.levelParams.map Level.param))
          (by simp only [AnnotOk]) hconstk
          (fun a ha => (hargFr a ha).an) hspine' hchaink
      rw [hfoldk] at hAppI
      refine ⟨⟨Expr.WScoped.mkAppN (by simp only [Expr.WScoped])
          (fun a ha => (hargFr a ha).ws),
        looseBVarsBounded_mkAppN (by rfl) (fun a ha => (hargFr a ha).bb),
        ?_, ?_, hAppA, _, hAppI⟩, hAppI⟩
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
        · simp [Expr.fvarLeaves] at hl'
        · exact (hargFr y hy).lb l hly
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
        · simp [Expr.fvarLeaves] at hl'
        · exact (hargFr y hy).fv l hly
    have hargFr₂ : ∀ a ∈ fvsP ++ pa,
        FrameOk V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x) a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hparFr' a ha
      · obtain ⟨k, hk, rfl⟩ := hpamem a ha
        exact (hprojFact k hk).1
    -- the two argument spines, carrying the same values
    have hfitCI := TeleFit_append hfitC0 hfitI
    have hia₁ : InstArgs mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
        (fvsP ++ pa) (xs.take p.nP ++ pjs.take i) := by
      refine InstArgs.append ?_ ?_
      · refine InstArgs.of_pointwise (by rw [hlenfvsP, hlenP]) ?_
        intro k a v ha hv
        refine ⟨(hparFr' a (List.mem_of_getElem? ha)).ws,
          (hparFr' a (List.mem_of_getElem? ha)).bb, ?_⟩
        obtain ⟨j, n, ty, rfl, hlt, hval⟩ := FvarSpine.pointwise hspFv k ha hv
        rw [interpExpr]
        simp only [updV]
        rw [if_neg (by omega), hval]
      · refine InstArgs.of_pointwise (by rw [hlenpa, hlenI]) ?_
        intro k a v ha hv
        have hk : k < i := by
          obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
          rw [hlenpa] at hlt; exact hlt
        obtain rfl : a = Expr.mkAppN (.const (projFnName p.cvT.name k)
            (p.cvT.levelParams.map Level.param))
            (fvsP ++ [Expr.fvar p.nP n₀ sdom]) := by
          rw [hpaget k hk] at ha
          exact (Option.some.inj ha).symm
        obtain rfl : v = projV k x := by
          rw [List.getElem?_take_of_lt hk, hpjsget k (by omega)] at hv
          exact (Option.some.inj hv).symm
        exact ⟨(hprojFact k hk).1.ws, (hprojFact k hk).1.bb, (hprojFact k hk).2⟩
    have hia₂ : InstArgs mP.val envP φ (p.nP + i) ρI (fvsC ++ xFvsI)
        (xs.take p.nP ++ pjs.take i) := by
      have hwsCrest : Expr.WScoped p.nP crestC :=
        (FrameOk.ofTeleFit hfitC0 hfrC).ws
      refine InstArgs.of_pointwise (by
        rw [hlenR, List.length_append, hlenP, hlenI]) ?_
      intro k a v ha hv
      have hk : k < p.nP + i := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
        rw [hlenR] at hlt; exact hlt
      have hslot := hfitCI.slots k (by
        rw [List.length_append, hlenP, hlenI]; exact hk)
      rw [Nat.zero_add] at hslot
      rcases Nat.lt_or_ge k p.nP with hlo | hhi
      · have ha' : fvsC[k]? = some a := by
          rwa [List.getElem?_append_left (by rw [hlenfvsC]; exact hlo)] at ha
        obtain ⟨nm, hnm⟩ := hshapeC k a ha'
        refine ⟨((openPisAtFvars_wscoped p.nP 0 hcq hfrC.ws).1 k a ha').mono
            (by omega), by rw [hnm]; rfl, ?_⟩
        rw [hnm, interpExpr, Nat.zero_add, hslot, List.getD_eq_getElem?_getD,
          hv]
        rfl
      · have ha' : xFvsI[k - p.nP]? = some a := by
          rwa [List.getElem?_append_right (by rw [hlenfvsC]; omega),
            hlenfvsC] at ha
        obtain ⟨nm, hnm⟩ := hshapexI (k - p.nP) a ha'
        refine ⟨((openPisAtFvars_wscoped i p.nP hopI hwsCrest).1 (k - p.nP) a
            ha').mono (by omega), by rw [hnm]; rfl, ?_⟩
        rw [hnm, interpExpr, show p.nP + (k - p.nP) = k from by omega, hslot,
          List.getD_eq_getElem?_getD, hv]
        rfl
    -- the pin's two sides interpret alike
    cases hfitRest with
    | @cons _ _ _ _ _ _ _ _ _ _ _ AI hdomII hximem _ =>
      have hframes := interp_instSeq_frames (V := V) (cval := mP.val)
        (env := envP) (φ := φ) hia₁ hia₂ hD₀cl (by rw [hlenPA]; exact hD₀b)
      rw [hlenPA, hlenR] at hframes
      have hfdomI : interpExpr V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
          fdom = some AI := by
        rw [hfdom, hframes]; exact hdomII
      obtain ⟨Pc, hPc⟩ := hfrC.it
      have hfrCat : FrameOk V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
          cvCa.type := by
        refine ⟨Expr.WScoped.of_not_hasFvar hCcl, hfrC.bb,
          Expr.LeavesBounded.of_not_hasFvar hCcl, FvarsOk.of_not_hasFvar hCcl,
          AnnotOk.closed_invariant hCcl _ _ hfrC.an, Pc, ?_⟩
        rw [interp_closed_invariant hCcl, ← interp_closed_invariant hCcl 0
          (rho0 V)]
        exact hPc
      obtain ⟨-, -, argsO, hteleO, -⟩ :=
        TeleFit.toTeleFitI hfitCI (Expr.WScoped.of_not_hasFvar hCcl)
      have hteleI := TeleFitI.ofInstWalk (fvsP ++ pa) hcinst hia₁
        (fun a ha => (hargFr₂ a ha).an) hfrCat.ws.fvarsBelow
        (fit_mem_frames hCcl hfrC.bb hstripL hcinst hlenPA hia₁ hteleO)
      obtain ⟨hRws, hRbb, hRan, hRleaves⟩ :=
        TeleFitI.rest_wf hteleI hfrCat.ws hfrC.bb hfrCat.an
      have hRleavesD : ∀ l ∈ fdom.fvarLeaves, ∃ a ∈ fvsP ++ pa,
          l ∈ a.fvarLeaves := by
        intro l hl
        rcases hRleaves l (by
          simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl)
          with hl' | h
        · rw [fvarLeaves_eq_nil_of_not_hasFvar hCcl] at hl'
          exact nomatch hl'
        · exact h
      have hfrFdom : FrameOk V mP.val envP φ (p.nP + 1) (updV V ρP p.nP x)
          fdom := by
        refine ⟨?_, ?_, ?_, ?_, ?_, AI, hfdomI⟩
        · simp only [Expr.WScoped] at hRws; exact hRws.1
        · simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hRbb
          exact hRbb.1
        · intro l hl
          obtain ⟨a, ha, hla⟩ := hRleavesD l hl
          exact (hargFr₂ a ha).lb l hla
        · intro l hl
          obtain ⟨a, ha, hla⟩ := hRleavesD l hl
          exact (hargFr₂ a ha).fv l hla
        · simp only [AnnotOk] at hRan; exact hRan.1
      have hfrResid := FrameOk.ofTeleFit hfit hfrPty
      rw [← hopTeq.2] at hfrResid hQ
      have hQAI : Q = AI :=
        isDefEqCore_sound mP F hpin2 hfrResid.ws hfrFdom.ws hfrResid.bb
          hfrFdom.bb hfrResid.lb hfrFdom.lb hfrResid.fv hfrFdom.fv
          hfrResid.an hfrFdom.an hQ hfdomI
      rw [hQAI]
      exact hximem

/-- **A projection function's `mem_type`**: `⟦T.proj.i⟧` inhabits the
interpretation of its stored (generated, annotated) type. -/
theorem directProj_mem {envP : Env} (mP : EnvModel V envP)
    {F : Nat} {φ : Name → Nat} {p : DirectParts} {i : Nat}
    {cvTa cvCa : ConstantVal} {envOut : Env}
    {fvsC : List Expr} {crestC : Expr}
    {cbs : List (Name × Expr × BinderMeta)}
    (hpj : checkDirectProj (fueledOps F) p.cvT.name p.cvC.name
      p.cvT.levelParams p.nP p.nF cvTa cvCa envP i = .ok envOut)
    (hi : i < p.nF)
    (hnz : p.resSort.isNonZero = true)
    (hfrC : FrameOk V mP.val envP φ 0 (rho0 V) cvCa.type)
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsC, crestC))
    (hstripC : Expr.stripPis (p.nP + p.nF) cvCa.type = some (cbs,
      directFam p.cvT.name p.cvT.levelParams p.nP p.nF))
    (hdomsCT : DomsInterpEq V mP.val envP φ p.nP 0 (rho0 V)
      cvCa.type cvTa.type)
    (hfieldAt : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid →
      ps.length = p.nP →
      FieldTele V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid)
    (hTfold : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      SpineFold V (mP.val p.cvT.name φ) ps =
        sigmaTowerV V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ crestC)
    (hinv : DirectProjInv V mP.val envP φ p.cvT.name p.cvT.levelParams
      cvTa.type p.nP i)
    (hTfind : envP.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTname : cvTa.name = p.cvT.name) :
    ∃ ptyA rhsA,
      envOut = ⟨.recInfo ⟨projFnName p.cvT.name i, p.cvT.levelParams, ptyA⟩
        p.nP p.nP [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain ptyA p.nP p.nP p.nP then .plain else .inert,
          rhsA⟩] :: envP.consts⟩ ∧
      ∃ Pv, interpClosed V mP.val envP φ ptyA = some Pv ∧
        directProjVal V mP.val envP ptyA p.nP i φ ∈ˢ Pv := by
  obtain ⟨ptyA, rhsA, henv, hfrPty, hstA, hbody, -⟩ :=
    directProj_facts mP hpj hi hnz hfrC hcq hstripC hdomsCT hfieldAt hTfold
      hinv hTfind hTlps hTname
  obtain ⟨Pv, hPv⟩ := hfrPty.it
  exact ⟨ptyA, rhsA, henv, Pv, hPv,
    directProjVal_mem hstA hPv hfrPty.an hbody⟩

/-- **A projection function's fold equation**: at a fitting parameter
spine and a member of the family, the constructed λ-tower folds to that
field of the subject.  This is what the *next* field's install consumes
(`DirectProjInv`) and what the stored rule's bottom fact needs. -/
theorem directProj_fold {envP : Env} (mP : EnvModel V envP)
    {F : Nat} {φ : Name → Nat} {p : DirectParts} {i : Nat}
    {cvTa cvCa : ConstantVal} {envOut : Env}
    {fvsC : List Expr} {crestC : Expr}
    {cbs : List (Name × Expr × BinderMeta)}
    (hpj : checkDirectProj (fueledOps F) p.cvT.name p.cvC.name
      p.cvT.levelParams p.nP p.nF cvTa cvCa envP i = .ok envOut)
    (hi : i < p.nF)
    (hnz : p.resSort.isNonZero = true)
    (hfrC : FrameOk V mP.val envP φ 0 (rho0 V) cvCa.type)
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsC, crestC))
    (hstripC : Expr.stripPis (p.nP + p.nF) cvCa.type = some (cbs,
      directFam p.cvT.name p.cvT.levelParams p.nP p.nF))
    (hdomsCT : DomsInterpEq V mP.val envP φ p.nP 0 (rho0 V)
      cvCa.type cvTa.type)
    (hfieldAt : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid →
      ps.length = p.nP →
      FieldTele V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid)
    (hTfold : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      SpineFold V (mP.val p.cvT.name φ) ps =
        sigmaTowerV V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ crestC)
    (hinv : DirectProjInv V mP.val envP φ p.cvT.name p.cvT.levelParams
      cvTa.type p.nP i)
    (hTfind : envP.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTname : cvTa.name = p.cvT.name) :
    ∃ ptyA rhsA,
      envOut = ⟨.recInfo ⟨projFnName p.cvT.name i, p.cvT.levelParams, ptyA⟩
        p.nP p.nP [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain ptyA p.nP p.nP p.nP then .plain else .inert,
          rhsA⟩] :: envP.consts⟩ ∧
      ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
        TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
        ps.length = p.nP →
        ∀ x : V, x ∈ˢ SpineFold V (mP.val p.cvT.name φ) ps →
          (∃ d' ρ' rest, TeleFit V mP.val envP φ 0 (rho0 V) ptyA (ps ++ [x])
            d' ρ' rest) ∧
          SpineFold V (directProjVal V mP.val envP ptyA p.nP i φ)
            (ps ++ [x]) = projV i x := by
  obtain ⟨ptyA, rhsA, henv, hfrPty, hstA, hbody, hfits⟩ :=
    directProj_facts mP hpj hi hnz hfrC hcq hstripC hdomsCT hfieldAt hTfold
      hinv hTfind hTlps hTname
  refine ⟨ptyA, rhsA, henv, ?_⟩
  intro ps d₁ ρ₁ r hfitT hlenPs x hx
  obtain ⟨d', ρ', rest, hf⟩ := hfits ps d₁ ρ₁ r hfitT hlenPs x hx
  refine ⟨⟨d', ρ', rest, hf⟩, ?_⟩
  have h := teleLamV_fold hstA hf
    (by rw [List.length_append, hlenPs]; rfl) hfrPty.an hbody
  rw [show (ps ++ [x]).getD p.nP SetTheory.empty = x from by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      hlenPs]
    simp] at h
  exact h

omit [SetTheory V] in
/-- The projection stage's stored constant determines its type and its
rule's right-hand side. -/
theorem directProj_store_inj {T C : Name} {lps : List Name} {nP nF : Nat}
    {ptyA₁ ptyA₂ rhsA₁ rhsA₂ : Expr} {f₁ f₂ : RecRuleFire}
    {cs : List ConstantInfo}
    (h : (⟨.recInfo ⟨T, lps, ptyA₁⟩ nP nP [⟨C, nF, nP, f₁, rhsA₁⟩] :: cs⟩
        : Env) =
      ⟨.recInfo ⟨T, lps, ptyA₂⟩ nP nP [⟨C, nF, nP, f₂, rhsA₂⟩] :: cs⟩) :
    ptyA₁ = ptyA₂ ∧ rhsA₁ = rhsA₂ := by
  simp only [Env.mk.injEq, List.cons.injEq, ConstantInfo.recInfo.injEq,
    ConstantVal.mk.injEq, RecRule.mk.injEq, and_true, true_and] at h
  exact ⟨h.1, h.2.2⟩

set_option maxHeartbeats 3200000 in
/-- **The direct projection rule's `RecRulesOk` obligation**:
`proj_rule_eq_of_bottom` at the constructed values.  Everything but the
bottom fact is provenance-free and shared with the modeled path; the
bottom is discharged here.

Over a full frame the canonical left-hand side `T.proj.i p⃗ (C p⃗ f⃗)`
interprets to the frame's `i`-th field value: `directCtorVal_fold`
folds the constructor's spine to `tupleV f⃗`, `directProj_fold` folds
the projection at `p⃗ (tupleV f⃗)` to `projV i (tupleV f⃗)`, and
`directProj_iota` reads that back off the tuple.

The two fits the folds consume come from the frame invariant
(`TeleFit.of_framePref`), the parameter half crossed onto the
constructor's and the type former's telescopes (`TeleFit.transfer` over
the stage's own pins) and the field half onto the constructor's *own*
opening — the two instantiations are index-matched, so
`instPisAt_erasedEq_spines` and `TeleFit.erasedEq` identify them. -/
theorem directProj_rule_eq {envP : Env} (mP : EnvModel V envP)
    {F : Nat} {p : DirectParts} {i : Nat}
    {cvTa cvCa : ConstantVal} {envOut : Env}
    {fvsC : List Expr} {crestC : Expr}
    {cbs : List (Name × Expr × BinderMeta)}
    (hpj : checkDirectProj (fueledOps F) p.cvT.name p.cvC.name
      p.cvT.levelParams p.nP p.nF cvTa cvCa envP i = .ok envOut)
    (hi : i < p.nF)
    (hnz : p.resSort.isNonZero = true)
    (hfrC : ∀ φ : Name → Nat, FrameOk V mP.val envP φ 0 (rho0 V) cvCa.type)
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsC, crestC))
    (hstripC : Expr.stripPis (p.nP + p.nF) cvCa.type = some (cbs,
      directFam p.cvT.name p.cvT.levelParams p.nP p.nF))
    (hdomsCT : ∀ φ : Name → Nat, DomsInterpEq V mP.val envP φ p.nP 0 (rho0 V)
      cvCa.type cvTa.type)
    (hfieldAt : ∀ (φ : Name → Nat) (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V)
        (mid : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid →
      ps.length = p.nP →
      FieldTele V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid)
    (hTfold : ∀ (φ : Name → Nat) (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V)
        (r : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      SpineFold V (mP.val p.cvT.name φ) ps =
        sigmaTowerV V mP.val envP φ (p.resSort.eval φ) p.nF d₁ ρ₁ crestC)
    (hCfold : ∀ (φ : Name → Nat) (vs : List V) (d₁ : Nat) (ρ₁ : Nat → V)
        (r : Expr),
      TeleFit V mP.val envP φ 0 (rho0 V) cvCa.type vs d₁ ρ₁ r →
      vs.length = p.nP + p.nF →
      SpineFold V (mP.val p.cvC.name φ) vs = tupleV (vs.drop p.nP))
    (hinv : ∀ φ : Name → Nat, DirectProjInv V mP.val envP φ p.cvT.name
      p.cvT.levelParams cvTa.type p.nP i)
    (hTfind : envP.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTname : cvTa.name = p.cvT.name)
    (hCfind : envP.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF)) :
    ∃ ptyA rhsA fire,
      envOut = ⟨.recInfo ⟨projFnName p.cvT.name i, p.cvT.levelParams, ptyA⟩
        p.nP p.nP [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: envP.consts⟩ ∧
      ∀ (c₀ : ConstantInfo) (val' : ConstVal V),
        c₀.name = projFnName p.cvT.name i →
        c₀.toConstantVal.levelParams = p.cvT.levelParams →
        (∀ n, (envP.find? n).isSome = true → ∀ ψ : Name → Nat,
          val' n ψ = mP.val n ψ) →
        (∀ ψ : Name → Nat, val' (projFnName p.cvT.name i) ψ =
          directProjVal V mP.val envP ptyA p.nP i ψ) →
        fire = .plain →
        ∃ fvms bL,
          ruleLhsParts (projFnName p.cvT.name i)
              ⟨projFnName p.cvT.name i, p.cvT.levelParams, ptyA⟩ p.nP
              ⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩ cvCa = some (fvms, bL) ∧
          FrameWf 0 fvms bL ∧
          fvms.length = p.nP + p.nF ∧
          (closeLamsAt fvms bL).constsResolve
            (⟨c₀ :: envP.consts⟩ : Env) = true ∧
          ∀ ψ : Name → Nat,
            AnnotOk V val' (⟨c₀ :: envP.consts⟩ : Env) ψ 0 (rho0 V)
              (closeLamsAt fvms bL) ∧
            ∃ Rv, interpClosed V val' (⟨c₀ :: envP.consts⟩ : Env) ψ
                (closeLamsAt fvms bL) = some Rv ∧
              interpClosed V val' (⟨c₀ :: envP.consts⟩ : Env) ψ rhsA =
                some Rv := by
  obtain ⟨pty, ptyA, sty, u, fvsP, prest, sbs, sbody, sdom, tFvs, resid, tfv,
    cds, fn, fdom, fbody, fm, rhsA, hpty, hptyf, hptyb, hann, hlpA, hresA,
    hbbA, hfvA, hstA, hsty, hu, hnone, hshape, hopP, hsstrip, hsdom,
    hpin1, hopT, htfv, hcinst, hpin2, hrule, henv⟩ := checkDirectProj_inv hpj
  obtain ⟨raw, rbinders, cbindersR, cbody0, hraw, hrawf, hrawb, hannR, hlpR,
    hresR, hbbR, hfvR, hstripR, hCstrip0, hdmatch, fvsP', rest0, cdomsP,
    crestP, xFvs, crest2X, ldoms, lrestL, hopP', hcinstP, hdeParsP, hopenX,
    hlinstP, hdeLamP, hrhsTy⟩ := checkProjRule_inv hrule
  have hfvsPeq : fvsP' = fvsP := by
    rw [hopP] at hopP'
    exact (congrArg Prod.fst (Option.some.inj hopP')).symm
  rw [hfvsPeq] at hcinstP hdeParsP hlinstP hdeLamP
  refine ⟨ptyA, rhsA, _, henv, ?_⟩
  intro c₀ val' hc₀name hlpsP hagree hvalP hfirep
  -- the stored data's syntactic and semantic well-formedness
  have hAty : ∀ ψ : Name → Nat, AnnotOk V mP.val envP ψ 0 (rho0 V) ptyA :=
    fun ψ => annotate_sound mP _ hann (Expr.WScoped.of_not_hasFvar hptyf)
      hptyb (Expr.LeavesBounded.of_not_hasFvar hptyf) (rho0 V)
      (FvarsOk.of_not_hasFvar hptyf)
  have hIty : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V mP.val envP ψ ptyA = some T := by
    intro ψ
    obtain ⟨⟨v, tv, hvi, -, -⟩, -, -⟩ :=
      inferTypeCore_sound (φ := ψ) mP F hsty
        (Expr.WScoped.of_not_hasFvar hfvA) hbbA
        (Expr.LeavesBounded.of_not_hasFvar hfvA)
        (FvarsOk.of_not_hasFvar hfvA) (hAty ψ)
    exact ⟨v, hvi⟩
  have hACty : ∀ ψ : Name → Nat,
      AnnotOk V mP.val envP ψ 0 (rho0 V) cvCa.type :=
    fun ψ => (mP.annot_ok _ (find?_mem hCfind) ψ).1
  have hICty : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V mP.val envP ψ cvCa.type = some T := by
    intro ψ
    obtain ⟨t, ht, -⟩ := mP.mem_type _ (find?_mem hCfind) ψ
    exact ⟨t, ht⟩
  have hArhs : ∀ ψ : Name → Nat, AnnotOk V mP.val envP ψ 0 (rho0 V) rhsA :=
    fun ψ => annotate_sound mP _ hannR (Expr.WScoped.of_not_hasFvar hrawf)
      hrawb (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
      (FvarsOk.of_not_hasFvar hrawf)
  have hIrhs : ∀ ψ : Name → Nat, ∃ L,
      interpClosed V mP.val envP ψ rhsA = some L := by
    intro ψ
    obtain ⟨rhsTy, hity⟩ := hrhsTy
    obtain ⟨⟨v, tv, hvi, -, -⟩, -, -⟩ :=
      inferTypeCore_sound (φ := ψ) mP F hity
        (Expr.WScoped.of_not_hasFvar hfvR) hbbR
        (Expr.LeavesBounded.of_not_hasFvar hfvR)
        (FvarsOk.of_not_hasFvar hfvR) (hArhs ψ)
    exact ⟨v, hvi⟩
  obtain ⟨hCcl, -, hCres, hCb, -⟩ := mP.wf _ (find?_mem hCfind)
  have hfresh : envP.find? c₀.name = none := by rw [hc₀name]; exact hnone
  have hfP₁ : (⟨c₀ :: envP.consts⟩ : Env).find? (projFnName p.cvT.name i) =
      some c₀ := by
    rw [Env.find?_cons, if_pos hc₀name]
  refine proj_rule_eq_of_bottom mP F hfresh hagree hfP₁ hCfind hfirep rfl rfl
    hstripR hstripC rfl (by simp) hopP hcinstP hdeParsP hopenX hlinstP
    hdeLamP hfvA hbbA hCcl hCb hresA hCres hresR hfvR hbbR hAty hIty
    hACty hICty hArhs hIrhs ?_
  intro φ xs hxs hpref
  have hfrC := hfrC φ
  have hdomsCT := hdomsCT φ
  have hfieldAt := hfieldAt φ
  have hTfold := hTfold φ
  have hCfold := hCfold φ
  have hinv := hinv φ
  have hvalP := hvalP φ
  -- the annotated projection type's frame conditions
  have hAptyA : AnnotOk V mP.val envP φ 0 (rho0 V) ptyA :=
    annotate_sound mP _ hann (Expr.WScoped.of_not_hasFvar hptyf) hptyb
      (Expr.LeavesBounded.of_not_hasFvar hptyf) (rho0 V)
      (FvarsOk.of_not_hasFvar hptyf)
  have hfrPty : FrameOk V mP.val envP φ 0 (rho0 V) ptyA := by
    obtain ⟨⟨v, tv, hvi, -, -⟩, -, -⟩ :=
      inferTypeCore_sound (φ := φ) mP F hsty
        (Expr.WScoped.of_not_hasFvar hfvA) hbbA
        (Expr.LeavesBounded.of_not_hasFvar hfvA)
        (FvarsOk.of_not_hasFvar hfvA) hAptyA
    exact ⟨Expr.WScoped.of_not_hasFvar hfvA, hbbA,
      Expr.LeavesBounded.of_not_hasFvar hfvA, FvarsOk.of_not_hasFvar hfvA,
      hAptyA, v, hvi⟩
  -- the stage's own parameter-domain agreement
  have hAgPC : DomsAgree V mP.val envP φ p.nP 0 (rho0 V) ptyA 0 (rho0 V)
      cvCa.type :=
    DomsAgree.of_pins_inst_at mP F p.nP 0 (p.nP + p.nF) (rho0 V) ptyA
      cvCa.type fvsP prest cdomsP crestP (by omega) hopP hcinstP
      (fun j a b ha hb => DefEqListOk.pointwise hdeParsP j
        (by rw [List.getElem?_map, ha]; rfl) hb)
      hfrPty hfrC
  -- spine shapes
  obtain ⟨hopPinst, hlenfvsP, hshapeP⟩ := openPisAtFvars_spec p.nP 0 hopP
  obtain ⟨hxInst, hlenxFvs, hshapeX⟩ :=
    openPisAtFvars_spec p.nF p.nP hopenX
  obtain ⟨hcqinst, hlenfvsC, hshapeC⟩ := openPisAtFvars_spec p.nP 0 hcq
  have hspineLen : (fvsP ++ xFvs).length = p.nP + p.nF := by
    rw [List.length_append, hlenfvsP, hlenxFvs]
  have hshapeA : ∀ (j : Nat) (a : Expr), (fvsP ++ xFvs)[j]? = some a →
      ∃ nm ty, a = Expr.fvar j nm ty := by
    intro j a hj
    rcases Nat.lt_or_ge j p.nP with hjn | hjn
    · rw [List.getElem?_append_left (by omega)] at hj
      obtain ⟨nm, ha⟩ := hshapeP j a hj
      rw [Nat.zero_add] at ha
      exact ⟨nm, Expr.fvarTypeD a, ha⟩
    · rw [List.getElem?_append_right (by omega), hlenfvsP] at hj
      obtain ⟨nm, ha⟩ := hshapeX (j - p.nP) a hj
      refine ⟨nm, Expr.fvarTypeD a, ?_⟩
      rw [show j = p.nP + (j - p.nP) from by omega]
      exact ha
  -- the two fits the frame invariant supplies
  have hrho0 : (fun l => (xs.take 0).getD l SetTheory.empty) = rho0 V := by
    funext l; rfl
  have hfitP0 := TeleFit.of_framePref hpref p.nP 0 hopP
    (fun k hk => by
      rw [Nat.zero_add]
      exact List.getElem?_append_left (by omega))
    (by omega)
  rw [hrho0, List.drop_zero, Nat.zero_add] at hfitP0
  have hlenps : (xs.take p.nP).length = p.nP := by
    rw [List.length_take]; omega
  have hfsLen : (xs.drop p.nP).length = p.nF := by
    rw [List.length_drop]; omega
  have hfitX := TeleFit.of_framePref hpref p.nF p.nP hopenX
    (fun k hk => by
      rw [List.getElem?_append_right (by omega), hlenfvsP,
        show p.nP + k - p.nP = k from by omega])
    (by omega)
  rw [show (xs.drop p.nP).take p.nF = xs.drop p.nP from by
      rw [List.take_of_length_le (by omega)],
    show xs.take (p.nP + p.nF) = xs from
      List.take_of_length_le (by omega)] at hfitX
  -- the parameters cross to the constructor's and the former's telescopes
  obtain ⟨dC, ρC, restC0, hfitC0⟩ := TeleFit.transfer p.nP hfitP0 hlenps hAgPC
  obtain ⟨hdC, fvsC0, hopC0⟩ := TeleFit_open p.nP hfitC0 hlenps
  rw [Nat.zero_add] at hdC
  subst hdC
  have hrestC : restC0 = crestC := by
    rw [hcq] at hopC0
    exact (congrArg Prod.snd (Option.some.inj hopC0)).symm
  have hρC : ρC = (fun l => (xs.take p.nP).getD l SetTheory.empty) :=
    TeleFit.rho_det hfitC0 hfitP0
  rw [hrestC, hρC] at hfitC0
  obtain ⟨dT, ρT0, restT0, hfitT0⟩ :=
    TeleFit.transfer p.nP hfitC0 hlenps hdomsCT
  obtain ⟨hdT, -, -⟩ := TeleFit_open p.nP hfitT0 hlenps
  rw [Nat.zero_add] at hdT
  subst hdT
  have hρT : ρT0 = (fun l => (xs.take p.nP).getD l SetTheory.empty) :=
    TeleFit.rho_det hfitT0 hfitP0
  rw [hρT] at hfitT0
  -- the field half moves onto the constructor's own opening
  have hEEcrest : Expr.ErasedEq crestP crestC :=
    (instPisAt_erasedEq_spines fvsP (Expr.ErasedEq.rfl cvCa.type)
      (by rw [hlenfvsP, hlenfvsC])
      (fun j a b ha hb => by
        obtain ⟨nma, hea⟩ := hshapeP j a ha
        obtain ⟨nmb, heb⟩ := hshapeC j b hb
        rw [hea, heb]
        exact rfl)
      hcinstP hcqinst).2
  obtain ⟨crestC2, hfitXC, -⟩ := hfitX.erasedEq hEEcrest
  have hfitCfull : TeleFit V mP.val envP φ 0 (rho0 V) cvCa.type xs
      (p.nP + p.nF) (fun l => xs.getD l SetTheory.empty) crestC2 := by
    have h := TeleFit_append hfitC0 hfitXC
    rwa [List.take_append_drop] at h
  -- the three fold facts
  have hCf : SpineFold V (mP.val p.cvC.name φ) xs = tupleV (xs.drop p.nP) :=
    hCfold xs _ _ _ hfitCfull hxs
  have hfld : FieldTele V mP.val envP φ (p.resSort.eval φ) p.nF p.nP
      (fun l => (xs.take p.nP).getD l SetTheory.empty) crestC :=
    hfieldAt _ _ _ _ hfitC0 hlenps
  have hxmem : tupleV (xs.drop p.nP) ∈ˢ
      SpineFold V (mP.val p.cvT.name φ) (xs.take p.nP) := by
    rw [hTfold _ _ _ _ hfitT0 hlenps]
    exact tupleV_mem (Level.isNonZero_sound hnz φ) hfld hfitXC hfsLen
  obtain ⟨ptyA₂, rhsA₂, henv₂, -, hstA', hbody, hfits⟩ :=
    directProj_facts mP hpj hi hnz hfrC hcq hstripC hdomsCT hfieldAt hTfold
      hinv hTfind hTlps hTname
  obtain ⟨hpeq, -⟩ : ptyA₂ = ptyA ∧ rhsA₂ = rhsA :=
    directProj_store_inj (henv₂.symm.trans henv)
  rw [hpeq] at hstA' hbody hfits
  obtain ⟨d', ρ', rest', hfitPX⟩ := hfits (xs.take p.nP) _ _ _ hfitT0 hlenps
    _ hxmem
  have hprojFold : SpineFold V (directProjVal V mP.val envP ptyA p.nP i φ)
      (xs.take p.nP ++ [tupleV (xs.drop p.nP)]) =
      projV i (tupleV (xs.drop p.nP)) := by
    have h := teleLamV_fold hstA' hfitPX
      (by rw [List.length_append, hlenps]; rfl) hfrPty.an hbody
    rw [show (xs.take p.nP ++ [tupleV (xs.drop p.nP)]).getD p.nP
        SetTheory.empty = tupleV (xs.drop p.nP) from by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        hlenps]
      simp] at h
    exact h
  -- the field value the whole left-hand side computes to
  have hfieldVal : projV i (tupleV (xs.drop p.nP)) =
      xs.getD (p.nP + i) SetTheory.empty := by
    rw [directProj_iota hfsLen hi, List.getD_eq_getElem?_getD,
      List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  -- the extended environment's lookups
  have hfresh : envP.find? c₀.name = none := by rw [hc₀name]; exact hnone
  have hfP₁ : (⟨c₀ :: envP.consts⟩ : Env).find? (projFnName p.cvT.name i) =
      some c₀ := by
    rw [Env.find?_cons, if_pos hc₀name]
  have hCfind₁ : (⟨c₀ :: envP.consts⟩ : Env).find? p.cvC.name =
      some (.ctorInfo cvCa p.nP p.nF) := by
    rw [Env.find?_cons_of_isSome hfresh (by rw [hCfind]; rfl)]
    exact hCfind
  have hvalC : val' p.cvC.name φ = mP.val p.cvC.name φ :=
    hagree _ (by rw [hCfind]; rfl) φ
  -- the constant heads' interpretations
  have hPi : interpExpr V val' (⟨c₀ :: envP.consts⟩ : Env) φ (p.nP + p.nF)
      (fun l => xs.getD l SetTheory.empty)
      (.const (projFnName p.cvT.name i) (p.cvT.levelParams.map .param)) =
      some (val' (projFnName p.cvT.name i) φ) := by
    rw [interp_const hfP₁ (by rw [hlpsP, List.length_map])]
    rw [show Level.substFn φ c₀.toConstantVal.levelParams
        (p.cvT.levelParams.map Level.param) = φ from by
      rw [hlpsP]
      exact funext fun q => Level.substFn_map_param]
  have hCi : interpExpr V val' (⟨c₀ :: envP.consts⟩ : Env) φ (p.nP + p.nF)
      (fun l => xs.getD l SetTheory.empty)
      (.const p.cvC.name (cvCa.levelParams.map .param)) =
      some (val' p.cvC.name φ) := by
    rw [interp_const hCfind₁ (by simp [ConstantInfo.toConstantVal])]
    rw [show Level.substFn φ
        (ConstantInfo.ctorInfo cvCa p.nP p.nF).toConstantVal.levelParams
        (cvCa.levelParams.map Level.param) = φ from
      funext fun q => Level.substFn_map_param]
  -- the frame spine interprets to the frame values
  have hspAll : InterpSpine val' (⟨c₀ :: envP.consts⟩ : Env) φ (p.nP + p.nF)
      (fun l => xs.getD l SetTheory.empty) (fvsP ++ xFvs) xs := by
    refine InterpSpine.of_pointwise (by rw [hspineLen, hxs]) ?_
    intro k a v ha hv
    obtain ⟨nm, ty, rfl⟩ := hshapeA k a ha
    simp only [interpExpr]
    rw [List.getD_eq_getElem?_getD, hv]
    rfl
  have hfvAnnot : ∀ x ∈ fvsP ++ xFvs,
      AnnotOk V val' (⟨c₀ :: envP.consts⟩ : Env) φ (p.nP + p.nF)
        (fun l => xs.getD l SetTheory.empty) x := by
    intro x hx
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    obtain ⟨nm, ty, rfl⟩ := hshapeA j x hj
    simp only [AnnotOk]
  -- chain slots for the two heads
  obtain ⟨Cv, hCvI, hCvmem⟩ := mP.mem_type _ (find?_mem hCfind) φ
  have hCannot := (mP.annot_ok _ (find?_mem hCfind) φ).1
  have hchainC : ChainSlots V (val' p.cvC.name φ) xs := by
    rw [hvalC, ← (show (ConstantInfo.ctorInfo cvCa p.nP p.nF).name =
      p.cvC.name from find?_name hCfind)]
    exact TeleFit.chainSlots hfitCfull hCannot hCvI hCvmem
  obtain ⟨Pv, hPvI⟩ := hfrPty.it
  have hchainP : ChainSlots V (val' (projFnName p.cvT.name i) φ)
      (xs.take p.nP ++ [tupleV (xs.drop p.nP)]) := by
    rw [hvalP]
    exact TeleFit.chainSlots hfitPX hfrPty.an hPvI
      (directProjVal_mem hstA' hPvI hfrPty.an hbody)
  -- the constructor application
  obtain ⟨hActor, hictor⟩ := annotOk_spine (fvsP ++ xFvs)
    (.const p.cvC.name (cvCa.levelParams.map Level.param))
    (by simp only [AnnotOk]) hCi hfvAnnot hspAll hchainC
  rw [hvalC, hCf] at hictor
  -- the whole left-hand side
  have htakeP : (fvsP ++ xFvs).take p.nP = fvsP := by
    rw [List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  obtain ⟨hAbL, hibL⟩ := annotOk_spine
    ((fvsP ++ xFvs).take p.nP ++
      [Expr.mkAppN (.const p.cvC.name (cvCa.levelParams.map Level.param))
        (fvsP ++ xFvs)])
    (.const (projFnName p.cvT.name i) (p.cvT.levelParams.map Level.param))
    (by simp only [AnnotOk]) hPi
    (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hfvAnnot x (List.mem_of_mem_take hx)
      · obtain rfl : x = Expr.mkAppN
            (.const p.cvC.name (cvCa.levelParams.map Level.param))
            (fvsP ++ xFvs) := by simpa using hx
        exact hActor)
    (InterpSpine.append (InterpSpine.take p.nP hspAll)
      (show InterpSpine val' (⟨c₀ :: envP.consts⟩ : Env) φ (p.nP + p.nF)
        (fun l => xs.getD l SetTheory.empty) [_]
        [tupleV (xs.drop p.nP)] from ⟨hictor, trivial⟩))
    hchainP
  -- the rule tower's instantiated body is the frame's `i`-th value
  have hbounded : ∀ a ∈ fvsP ++ xFvs, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hshapeA j a hj
    rfl
  have hRmid : lrestL =
      instSeq (fvsP ++ xFvs) (p.nP + p.nF - 1) (.bvar (p.nF - 1 - i)) := by
    have h1 := (instLamsAt_stripLams (fvsP ++ xFvs) hlinstP
      (by rw [hspineLen]; exact hstripR)).1
    rw [hspineLen] at h1
    exact h1
  have hbv := Expr.instSeq_bvar (fvsP ++ xFvs) (p.nP + p.nF - 1)
    (p.nF - 1 - i) hbounded (by omega) (by rw [hspineLen]; omega)
  rw [show p.nP + p.nF - 1 - (p.nF - 1 - i) = p.nP + i from by omega] at hbv
  obtain ⟨nmr, tyr, hfld₁⟩ := hshapeA (p.nP + i) _ hbv
  have heRi : interpExpr V val' (⟨c₀ :: envP.consts⟩ : Env) φ
      (p.nP + p.nF) (fun l => xs.getD l SetTheory.empty) lrestL =
      some (xs.getD (p.nP + i) SetTheory.empty) := by
    rw [hRmid, hfld₁]
    simp only [interpExpr]
  refine ⟨⟨xs.getD (p.nP + i) SetTheory.empty, ?_, ?_⟩, hAbL⟩
  · rw [hibL, htakeP] at *
    rw [hvalP, hprojFold, hfieldVal]
  · intro e hee
    rw [interp_erasedEq hee _ _, heRi]

/-- **The recursor's `mem_type`**: `⟦T.rec⟧` inhabits the
interpretation of its (annotated) type, from `directRec_body`. -/
theorem directRec_mem {env₂ : Env} (m₂ : EnvModel V env₂)
    {F : Nat} {φ : Name → Nat} {p : DirectParts}
    {cvTa cvCa cvRa : ConstantVal} {fvsC : List Expr} {crestC : Expr}
    {cbs : List (Name × Expr × BinderMeta)}
    (hrt : checkDirectRecTy (fueledOps F) env₂ p cvTa cvCa cvRa = .ok ())
    (hnz : p.resSort.isNonZero = true)
    (hfrRa : FrameOk V m₂.val env₂ φ 0 (rho0 V) cvRa.type)
    (hfrC : FrameOk V m₂.val env₂ φ 0 (rho0 V) cvCa.type)
    (hcq : openPisAtFvars p.nP cvCa.type 0 = some (fvsC, crestC))
    (hstripC : Expr.stripPis (p.nP + p.nF) cvCa.type = some (cbs,
      directFam p.cvT.name p.cvT.levelParams p.nP p.nF))
    (hdomsCT : DomsInterpEq V m₂.val env₂ φ p.nP 0 (rho0 V)
      cvCa.type cvTa.type)
    (hfieldAt : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (mid : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvCa.type ps d₁ ρ₁ mid →
      ps.length = p.nP →
      FieldTele V m₂.val env₂ φ (p.resSort.eval φ) p.nF d₁ ρ₁ mid)
    (hTfold : ∀ (ps : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvTa.type ps d₁ ρ₁ r →
      ps.length = p.nP →
      SpineFold V (m₂.val p.cvT.name φ) ps =
        sigmaTowerV V m₂.val env₂ φ (p.resSort.eval φ) p.nF d₁ ρ₁ crestC)
    (hCfold : ∀ (vs : List V) (d₁ : Nat) (ρ₁ : Nat → V) (r : Expr),
      TeleFit V m₂.val env₂ φ 0 (rho0 V) cvCa.type vs d₁ ρ₁ r →
      vs.length = p.nP + p.nF →
      SpineFold V (m₂.val p.cvC.name φ) vs = tupleV (vs.drop p.nP))
    (hTfind : env₂.find? p.cvT.name = some (.indInfo cvTa (directCaps p)))
    (hTlps : cvTa.levelParams = p.cvT.levelParams)
    (hTname : cvTa.name = p.cvT.name)
    (hCfind : env₂.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hClps : cvCa.levelParams = p.cvT.levelParams) :
    ∃ Rv, interpClosed V m₂.val env₂ φ cvRa.type = some Rv ∧
      directRecVal V m₂.val env₂ cvRa.type p.nP p.nF φ ∈ˢ Rv := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsh, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -⟩ := checkDirectRecTy_inv hrt
  obtain ⟨Rv, hRv⟩ := hfrRa.it
  exact ⟨Rv, hRv, directRecVal_mem (directShape_stripPis hsh) hRv hfrRa.an
    (directRec_body m₂ hrt hnz hfrRa hfrC hcq hstripC hdomsCT hfieldAt
      hTfold hCfold hTfind hTlps hTname hCfind hClps)⟩

end Setlec
