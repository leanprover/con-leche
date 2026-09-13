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

/-- **The pre-annotated front door, inverted**: every check of
`checkConstantVal` on the given type, and the constant returned is the
input. -/
theorem checkConstantValPre_inv {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    cv.type.allLevelParamsDefined cv.levelParams = true ∧
    cv.type.constsResolve env = true ∧
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
  try simp only [bind, Except.bind] at h
  obtain ⟨sty, hinf, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨u, hens, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  refine ⟨?_, ?_, ?_, h4, h5, ?_, h7, h8, ⟨sty, u, hinf, hens⟩, h.symm⟩
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
  obtain ⟨hfresh, hnres, hpshape, hnodup, hb, hnf, hlps, hres, ⟨stype, u, hinf, hens⟩, rfl⟩ :=
    checkConstantValPre_inv h
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
      by_cases hg : (auxRoute && Name.hasPrefixOf nestedPrefixName cv.name) = true
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

end ConLeche
