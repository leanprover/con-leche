module

public import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.SumInv
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.BridgeWfImp
public section

/-!
# The formers stage at EITHER front door (task #279 K.10, the model lane)

K.10 gave `mutualFormerChecks` a grade: at `auxRoute` a member whose name
carries the reserved `_nested` prefix — a copy the kernel minted itself —
goes through `checkConstantValPre`, which runs every check of
`checkConstantVal` on the given type WITHOUT the annotation walk and
returns its input.  The model tier read the formers stage through
`checkConstantVal … = .ok f.cvTa`, so the auxiliary install at the grade
had no model.  This module states what the model ACTUALLY consumes of a
former's check — `FormerFront`: the name facts, the type's syntactic
well-formedness and its inference at depth 0 — and reads it off the
stage at EITHER grade (`mutualFormerChecks_front`).  Nothing about the
annotation pass is in it: a former's reading comes from inference
(`acceptedReads_of`, `ClaimsAt.inferRow`), which is exactly what
validates a pre-annotated type's binder data (K.10).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem frontThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact frontThrow_ne_ok (by assumption))
        | (exfalso; exact frontThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-- **The pre-annotated front door, inverted in full**: every check of
`checkConstantVal` on the given type (and K.13's `.proj` slot check),
and the constant returned is the input.  (`NestedInv`'s
`checkConstantValPre_inv` is the two-conjunct read; this is the
`FormerFront` producer's.) -/
theorem checkConstantValPre_front {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    cv.type.allLevelParamsDefined cv.levelParams = true ∧
    cv.type.constsResolve env = true ∧
    cv.type.projTablesOk env = true ∧
    (∃ stype u, inferTypeCore mode env F 0 cv.type = .ok stype ∧
      ensureSortCore mode env F 0 stype = .ok u) ∧
    cvA = cv := by
  unfold checkConstantValPre at h
  by_cases h1 : (env.find? cv.name).isSome = true
  case pos => rw [if_pos h1] at h; close_throw
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  case pos => rw [if_pos h2] at h; close_throw
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  case pos => rw [if_pos h3] at h; close_throw
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; close_throw
  rw [if_pos h4] at h
  by_cases h5 : cv.type.looseBVarsBounded 0 = true
  case neg => rw [if_neg h5] at h; close_throw
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  case pos => rw [if_pos h6] at h; close_throw
  rw [if_neg h6] at h
  by_cases h7 : cv.type.allLevelParamsDefined cv.levelParams = true
  case neg => rw [if_neg h7] at h; close_throw
  rw [if_pos h7] at h
  by_cases h8 : cv.type.constsResolve env = true
  case neg => rw [if_neg h8] at h; close_throw
  rw [if_pos h8] at h
  by_cases h9 : cv.type.projTablesOk env = true
  case neg => rw [if_neg h9] at h; close_throw
  rw [if_pos h9] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨sty, hinf, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨u, hens, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  refine ⟨?_, ?_, ?_, h4, h5, ?_, h7, h8, h9, ⟨sty, u, hinf, hens⟩, h.symm⟩
  · cases hf : env.find? cv.name with
    | none => rfl
    | some c => exact absurd (by rw [hf]; rfl) h1
  · cases hr : reservedBasisNames.contains cv.name with
    | false => rfl
    | true => exact absurd hr h2
  · cases hp : cv.name.isProjFnShape with
    | false => rfl
    | true => exact absurd hp h3
  · cases hv : cv.type.hasFvar with
    | false => rfl
    | true => exact absurd hv h6

/-- **What the model reads of a former's check**, at either front door:
the DECLARED constant's name facts, the checked constant's name and
level parameters (the declared ones), its type's syntactic
well-formedness at the checking environment, and its inference there
at depth 0 (a sort). -/
structure FormerFront (mode : CheckMode) (F : Nat) (env : Env) (cv cvTa : ConstantVal) : Prop
    where
  fresh : env.find? cv.name = none
  nres : reservedBasisNames.contains cv.name = false
  pshape : cv.name.isProjFnShape = false
  lpsNodup : Name.nodup cv.levelParams = true
  name : cvTa.name = cv.name
  lps : cvTa.levelParams = cv.levelParams
  noFvar : cvTa.type.hasFvar = false
  bounded : cvTa.type.looseBVarsBounded 0 = true
  lpsOk : cvTa.type.allLevelParamsDefined cvTa.levelParams = true
  resolve : cvTa.type.constsResolve env = true
  infer : ∃ stype u, inferTypeCore mode env F 0 cvTa.type = .ok stype ∧
    ensureSortCore mode env F 0 stype = .ok u

namespace FormerFront

/-- The annotating front door. -/
theorem of_checkConstantVal {env : Env} {cv cvTa : ConstantVal} {F : Nat}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cvTa) :
    FormerFront mode F env cv cvTa := by
  obtain ⟨hfresh, hnres, hpshape, hnodup, -, -, type', stype, u, -, -, -, hinf, hens, hty⟩ :=
    checkConstantVal_inv h
  obtain ⟨hnf, hlps, hres, hb⟩ := checkConstantVal_typeWF h
  refine ⟨hfresh, hnres, hpshape, hnodup, by rw [hty], by rw [hty], hnf, hb, hlps, hres,
    stype, u, ?_, hens⟩
  rw [hty]; exact hinf

/-- The pre-annotated front door (K.10). -/
theorem of_pre {env : Env} {cv cvTa : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvTa) :
    FormerFront mode F env cv cvTa := by
  obtain ⟨hfresh, hnres, hpshape, hnodup, hb, hnf, hlps, hres, -, ⟨stype, u, hinf, hens⟩, rfl⟩ :=
    checkConstantValPre_front h
  exact ⟨hfresh, hnres, hpshape, hnodup, rfl, rfl, hnf, hb, hlps, hres, stype, u, hinf, hens⟩

/-- The record reads only the declared constant's name and level
parameters, so a retyped declared constant serves as well. -/
theorem retype {env : Env} {cv cvTa : ConstantVal} {ty : Expr} {F : Nat}
    (h : FormerFront mode F env { cv with type := ty } cvTa) : FormerFront mode F env cv cvTa :=
  ⟨h.fresh, h.nres, h.pshape, h.lpsNodup, h.name, h.lps, h.noFvar, h.bounded, h.lpsOk, h.resolve,
    h.infer⟩

end FormerFront

/-- **The formers' checks at EITHER grade, positionally**: one checked
former per declared one, each with `FormerFront` at the pre-block
environment (the front door is `checkConstantValPre` at `auxRoute` on a
`_nested`-named member and `checkConstantVal` otherwise; `checkSumTele`
either keeps the checked constant or re-checks its normalised type
through `checkConstantVal`), and the checked type is the telescope
ending in the result sort. -/
theorem mutualFormerChecks_front {nP F : Nat} {auxRoute : Bool} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP auxRoute l = .ok fms →
      fms.length = l.length ∧
      ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        ∃ (cv : ConstantVal) (bs : List (Expr × BinderMeta)),
          l[t]? = some (cv, f.nIdx) ∧
          FormerFront mode F env cv f.cvTa ∧
          f.cvTa.type.stripPis (nP + f.nIdx) = some (bs, .sort f.s)
  | [], _, _, h => by
    simp only [mutualFormerChecks, pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h.symm
    exact ⟨rfl, fun t f hf => nomatch hf⟩
  | (cv, nIdx) :: rest, env, fms, h => by
    -- the head: either front door, then the telescope stage
    have hhead : ∃ (cvTa₀ cvTa : ConstantVal) (s : Level) (bs : List (Expr × BinderMeta))
        (fs : List MutualFormerA),
        FormerFront mode F env cv cvTa₀ ∧
        checkSumTele (fueledOps mode F) env cv (nP + nIdx) cvTa₀ = .ok (cvTa, s) ∧
        cvTa.type.stripPis (nP + nIdx) = some (bs, Expr.sort s) ∧
        mutualFormerChecks (fueledOps mode F) env nP auxRoute rest = .ok fs ∧
        fms = ⟨cvTa, nIdx, s⟩ :: fs := by
      unfold mutualFormerChecks at h
      by_cases hg : auxRoute = true
      · rw [if_pos hg] at h
        obtain ⟨cvTa₀, hccv, h⟩ := exceptBind_ok h
        obtain ⟨q, htele, h⟩ := exceptBind_ok h
        obtain ⟨cvTa, s⟩ := q
        try simp only at h
        obtain ⟨q2, hq2, h⟩ := exceptBind_ok h
        obtain ⟨bs, tbody⟩ := q2
        have hq2' := unwrapOr_ok hq2
        try simp only at h
        by_cases hc : (tbody == Expr.sort s) = true
        case neg => rw [if_neg hc] at h; close_throw
        rw [if_pos hc] at h
        try simp only [bind, Except.bind] at h
        obtain ⟨fs, hrec, h⟩ := exceptBind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain rfl := h
        exact ⟨cvTa₀, cvTa, s, bs, fs, FormerFront.of_pre hccv, htele,
          by rw [hq2', beq_iff_eq.mp hc], hrec, rfl⟩
      · rw [if_neg hg] at h
        obtain ⟨cvTa₀, hccv, h⟩ := exceptBind_ok h
        obtain ⟨q, htele, h⟩ := exceptBind_ok h
        obtain ⟨cvTa, s⟩ := q
        try simp only at h
        obtain ⟨q2, hq2, h⟩ := exceptBind_ok h
        obtain ⟨bs, tbody⟩ := q2
        have hq2' := unwrapOr_ok hq2
        try simp only at h
        by_cases hc : (tbody == Expr.sort s) = true
        case neg => rw [if_neg hc] at h; close_throw
        rw [if_pos hc] at h
        try simp only [bind, Except.bind] at h
        obtain ⟨fs, hrec, h⟩ := exceptBind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain rfl := h
        exact ⟨cvTa₀, cvTa, s, bs, fs, FormerFront.of_checkConstantVal hccv, htele,
          by rw [hq2', beq_iff_eq.mp hc], hrec, rfl⟩
    obtain ⟨cvTa₀, cvTa, s, bs, fs, hfront, htele, hstrip, hrest, rfl⟩ := hhead
    obtain ⟨hlen, hall⟩ := mutualFormerChecks_front hrest
    refine ⟨by simp [hlen], ?_⟩
    intro t f hf
    cases t with
    | zero =>
      obtain rfl := Option.some.inj hf
      rcases checkSumTele_shape htele with ⟨rfl, -⟩ | ⟨ty, hccv⟩
      · exact ⟨cv, bs, rfl, hfront, hstrip⟩
      · exact ⟨cv, bs, rfl, (FormerFront.of_checkConstantVal hccv).retype, hstrip⟩
    | succ t =>
      simp only [List.getElem?_cons_succ] at hf ⊢
      exact hall t f hf

/-- Every checked former has `FormerFront` at SOME declared constant. -/
theorem mutualFormerChecks_front_mem {nP F : Nat} {auxRoute : Bool}
    {l : List (ConstantVal × Nat)} {env : Env} {fms : List MutualFormerA}
    (h : mutualFormerChecks (fueledOps mode F) env nP auxRoute l = .ok fms) :
    ∀ f ∈ fms, ∃ cv : ConstantVal, FormerFront mode F env cv f.cvTa := by
  intro f hf
  obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
  obtain ⟨cv, -, -, hfront, -⟩ := (mutualFormerChecks_front h).2 t f ht
  exact ⟨cv, hfront⟩


/-! ## The constructors' front door at either grade (K.12)

At `auxRoute` the constructor stage's front door is
`checkConstantValPre` and the positivity normalisation re-checks a
changed type through it too; off the grade both are `checkConstantVal`.
Either way the stored constructor carries the declared name, which the
front door found free. -/

/-- `normCtorValM` returns the checked constructor, or re-checks the
normalised type through a front door. -/
theorem normCtorValM_front {env : Env} {memberNames : List Name} {nP nF F : Nat}
    {cvC cvCa cvCa' : ConstantVal} {pre : Bool}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa pre
      = .ok cvCa') :
    cvCa' = cvCa ∨ ∃ ty', FormerFront mode F env { cvC with type := ty' } cvCa' := by
  unfold normCtorValM at h
  obtain ⟨_q, _h1, h⟩ := exceptBind_ok h
  obtain ⟨_cbs, _⟩ := _q
  try simp only at h
  obtain ⟨_r, _h2, h⟩ := exceptBind_ok h
  obtain ⟨_fvsP, _crest⟩ := _r
  try simp only at h
  obtain ⟨_u, _h3, h⟩ := exceptBind_ok h
  obtain ⟨_fbs, _resid⟩ := _u
  try simp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  · split at h
    · exact Or.inr ⟨_, FormerFront.of_pre h⟩
    · exact Or.inr ⟨_, FormerFront.of_checkConstantVal h⟩

/-- **One constructor at either grade**: the stored constructor carries
the declared name, and that name is free at the environment. -/
theorem checkMutualCtor_fresh {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx nF F : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {sorts : List Level} {pre : Bool}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa pre = .ok (cvCa, sorts)) :
    cvCa.name = cvC.name ∧ env.find? cvC.name = none := by
  unfold checkMutualCtor at h
  cases pre <;> simp only [if_true, Bool.false_eq_true, if_false] at h <;>
  obtain ⟨cvCa₀, hfront, h⟩ := exceptBind_ok h <;>
  obtain ⟨c, hnorm, h⟩ := exceptBind_ok h <;>
  have hff₀ : FormerFront mode F env cvC cvCa₀ := by
    first
    | exact FormerFront.of_pre hfront
    | exact FormerFront.of_checkConstantVal hfront
  all_goals
    have hcname : c.name = cvC.name := by
      rcases normCtorValM_front hnorm with rfl | ⟨ty', hff⟩
      · exact hff₀.name
      · exact hff.name
    obtain ⟨q, _hq, h⟩ := exceptBind_ok h
    obtain ⟨_cbs, cbody⟩ := q
    try simp only at h
    by_cases hc : structCtorResidOk T lps nP nF nIdx cbody = true
    case neg => rw [if_neg hc] at h; close_throw
    rw [if_pos hc] at h
    obtain ⟨cq, _hcq, h⟩ := exceptBind_ok h
    obtain ⟨fvsP, _crest⟩ := cq
    obtain ⟨tq, _htq, h⟩ := exceptBind_ok h
    obtain ⟨_tfvs, _trest⟩ := tq
    try simp only at h
    obtain ⟨u, _hdoms, h⟩ := exceptBind_ok h
    obtain ⟨xq, _hxq, h⟩ := exceptBind_ok h
    obtain ⟨xFvs, xrest⟩ := xq
    try simp only at h
    by_cases h2 : (xrest.getAppFn == Expr.const T (lps.map .param) &&
        xrest.getAppArgs.take nP == fvsP && xrest.getAppArgs.length == nP + nIdx) = true
    case neg => rw [if_neg h2] at h; close_throw
    rw [if_pos h2] at h
    by_cases h3 : (xFvs.all fun x => Expr.constsResolve env x.fvarTypeD) = true
    case neg => rw [if_neg h3] at h; close_throw
    rw [if_pos h3] at h
    by_cases h4 : ((xrest.getAppArgs.drop nP).all fun e => Expr.constsResolve env e) = true
    case neg => rw [if_neg h4] at h; close_throw
    rw [if_pos h4] at h
    obtain ⟨_sorts', _hsorts, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hcname, hff₀.fresh⟩


/-- **One constructor's stage at either grade**, inverted:
`checkMutualCtor_shape` with its front door read as `FormerFront` (the
annotating door off the grade, `checkConstantValPre` on it — and the
positivity normalisation's re-check likewise). -/
theorem checkMutualCtor_front {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {nF F : Nat} {sorts : List Level} {pre : Bool}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa pre = .ok (cvCa, sorts)) :
    (∃ ty', FormerFront mode F env { cvC with type := ty' } cvCa) ∧
    (∃ cbs es, cvCa.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (structPsAt nF nP ++ es)) ∧
      es.length = nIdx) ∧
    ∃ (fvsP : List Expr) (crest : Expr) (tfvs : List Expr) (trest : Expr)
      (xFvs idxArgs : List Expr),
      openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
      openPisAtFvars nP cvTa.type 0 = some (tfvs, trest) ∧
      checkStructDomsAt (fueledOps mode F) env 0 fvsP
        (tfvs.map Expr.fvarTypeD) nP = .ok () ∧
      openPisAtFvars nF crest nP
        = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) ∧
      idxArgs.length = nIdx ∧
      (∀ x ∈ xFvs, x.fvarTypeD.constsResolve env = true) ∧
      (∀ e ∈ idxArgs, e.constsResolve env = true) ∧
      checkStructFieldSortsI (fueledOps mode F) env isProp large resSort
        nP xFvs idxArgs nF = .ok sorts := by
  unfold checkMutualCtor at h
  cases pre <;> simp only [if_true, Bool.false_eq_true, if_false] at h <;>
  obtain ⟨cvCa₀, hccv₀, h⟩ := exceptBind_ok h <;>
  obtain ⟨cvCa', hnorm, h⟩ := exceptBind_ok h <;>
  have hff₀ : FormerFront mode F env cvC cvCa₀ := by
    first
    | exact FormerFront.of_pre hccv₀
    | exact FormerFront.of_checkConstantVal hccv₀
  all_goals
    have hccv : ∃ ty', FormerFront mode F env { cvC with type := ty' } cvCa' := by
      rcases normCtorValM_front hnorm with rfl | ⟨ty', hff⟩
      · exact ⟨cvC.type, hff₀⟩
      · exact ⟨ty', hff⟩
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    obtain ⟨cbs, cbody⟩ := q
    have hq' := unwrapOr_ok hq
    try simp only at h
    by_cases hc : structCtorResidOk T lps nP nF nIdx cbody = true
    case neg => rw [if_neg hc] at h; close_throw
    rw [if_pos hc] at h
    obtain ⟨cq, hcq, h⟩ := exceptBind_ok h
    have hcq' := unwrapOr_ok hcq
    obtain ⟨fvsP, crest⟩ := cq
    obtain ⟨tq, htq, h⟩ := exceptBind_ok h
    have htq' := unwrapOr_ok htq
    obtain ⟨tfvs, trest⟩ := tq
    try simp only at h
    obtain ⟨u, hdoms, h⟩ := exceptBind_ok h
    obtain ⟨xq, hxq, h⟩ := exceptBind_ok h
    have hxq' := unwrapOr_ok hxq
    obtain ⟨xFvs, xrest⟩ := xq
    try simp only at h
    by_cases h2 : (xrest.getAppFn == Expr.const T (lps.map .param) &&
        xrest.getAppArgs.take nP == fvsP && xrest.getAppArgs.length == nP + nIdx) = true
    case neg => rw [if_neg h2] at h; close_throw
    rw [if_pos h2] at h
    by_cases h3 : (xFvs.all fun x => Expr.constsResolve env x.fvarTypeD) = true
    case neg => rw [if_neg h3] at h; close_throw
    rw [if_pos h3] at h
    by_cases h4 : ((xrest.getAppArgs.drop nP).all fun e => Expr.constsResolve env e) = true
    case neg => rw [if_neg h4] at h; close_throw
    rw [if_pos h4] at h
    obtain ⟨sorts', hsorts, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [structCtorResidOk, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨es, hes, hesl⟩ := residual_shape hc.1.1 hc.2 hc.1.2
    refine ⟨hccv, ⟨cbs, es, by rw [hq', hes], hesl⟩,
      fvsP, crest, tfvs, trest, xFvs, xrest.getAppArgs.drop nP,
      hcq', htq', by cases u; exact hdoms, ?_, ?_, ?_, ?_, hsorts⟩
    · rw [hxq']
      congr 1
      rw [← h2.1.2, List.take_append_drop, ← h2.1.1, Expr.mkAppN_getApp]
    · rw [List.length_drop, h2.2]; omega
    · intro x hx
      exact List.all_eq_true.mp h3 x hx
    · intro e he
      exact List.all_eq_true.mp h4 e he

/-- The four type-slot facts of a checked constructor, at either grade. -/
theorem checkMutualCtor_typeWF {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {nF F : Nat} {sorts : List Level} {pre : Bool}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa pre = .ok (cvCa, sorts)) :
    cvCa.type.hasFvar = false ∧ cvCa.type.allLevelParamsDefined cvCa.levelParams = true ∧
    cvCa.type.constsResolve env = true ∧ cvCa.type.looseBVarsBounded 0 = true := by
  obtain ⟨⟨_, hff⟩, -, -⟩ := checkMutualCtor_front h
  exact ⟨hff.noFvar, hff.lpsOk, hff.resolve, hff.bounded⟩

end ConLeche
