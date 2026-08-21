import Setlec.Kernel.Checker
import Setlec.Model.Annotate
import Setlec.Model.BasisInstall
import Setlec.Model.IndInstall
import Setlec.Model.ProjInstall
import Setlec.Model.EtaInstall
import Setlec.Model.Extend.Ind
import Setlec.Model.Extend.ProjFn
import Setlec.Model.Extend.Modeled
import Setlec.Model.Extend.Iota
import Setlec.Model.Extend.BasisOne
import Setlec.Model.Extend.Model
import Setlec.Model.Extend.Sibs
import Setlec.Model.Extend.Inversions

/-!
# Model extension steps

One lemma per way the checker extends the environment: plain constants
(`extend_model`), pinned basis constants (`extend_basis_one`), opaque
modeled inductive-kind members (`extend_modeled_one`) and modeled
recursors with their checked iota rules (`extend_modeled_rec`,
consuming the `RuleChecked` bundles that `checkIotaRules_inv`
extracts).  `Setlec.Model.Consistency` assembles these into
`checkDecl_sound`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Invert stage 1 of `checkProjFn` (the stored-constant lookups). -/
theorem checkProjLookups_inv {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} {cvj mcv : ConstantVal}
    (h : (checkProjLookups env' T ctorName lps nP nF i : CheckM _) =
      .ok (cvj, mcv)) :
    ∃ mval,
      env'.find? ctorName = some (.ctorInfo cvj nP nF) ∧
      env'.find? (projModelName T i) = some (.defnInfo mcv mval) ∧
      mcv.levelParams = lps ∧
      env'.find? (projFnName T i) = none ∧
      (env'.find? T).isSome = true ∧
      env'.find? eqName = some eqA := by
  simp only [checkProjLookups, Bind.bind, Except.bind] at h
  revert h
  match hctor : env'.find? ctorName with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj' cnP cnF) => ?_
  intro h
  dsimp only at h
  by_cases hpp : cnP = nP ∧ cnF = nF
  case neg => rw [if_neg hpp] at h; exact nomatch h
  rw [if_pos hpp] at h
  obtain ⟨rfl, rfl⟩ := hpp
  try dsimp only at h
  revert h
  match hfm : env'.find? (projModelName T i) with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo mcv' mval) => ?_
  intro h
  dsimp only at h
  by_cases hmlps : mcv'.levelParams = lps
  case neg => rw [if_neg hmlps] at h; exact nomatch h
  rw [if_pos hmlps] at h
  try dsimp only at h
  by_cases hpn : (env'.find? (projFnName T i)).isNone = true
  case neg => rw [if_neg hpn] at h; exact nomatch h
  rw [if_pos hpn] at h
  have hpnone : env'.find? (projFnName T i) = none := by
    revert hpn
    cases env'.find? (projFnName T i) <;> simp
  try dsimp only at h
  by_cases hTf : (env'.find? T).isSome = true
  case neg => rw [if_neg hTf] at h; exact nomatch h
  rw [if_pos hTf] at h
  try dsimp only at h
  by_cases heqf : env'.find? eqName = some eqA
  case neg => rw [if_neg heqf] at h; exact nomatch h
  rw [if_pos heqf] at h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨mval, rfl, rfl, hmlps, hpnone, hTf, heqf⟩

/-- Invert stage 2 of `checkProjFn` (the public projection type). -/
theorem checkProjTy_inv {env' : Env} {T ctorName : Name} {lps : List Name}
    {mty pty : Expr} {nP nF : Nat}
    (h : (checkProjTy env' T ctorName lps mty nP nF : CheckM _) =
      .ok pty) :
    pty = mty.renameConsts (projBack T ctorName nF) ∧
    pty.renameConsts (projFwd T ctorName nF) = mty ∧
    pty.constsResolve env' = true ∧
    pty.looseBVarsBounded 0 = true ∧
    pty.hasFvar = false ∧
    pty.allLevelParamsDefined lps = true := by
  simp only [checkProjTy, Bind.bind, Except.bind] at h
  by_cases hround : ((mty.renameConsts (projBack T ctorName nF)).renameConsts
      (projFwd T ctorName nF) == mty) = true
  case neg => rw [if_neg hround] at h; exact nomatch h
  rw [if_pos hround] at h
  try dsimp only at h
  by_cases hres : (mty.renameConsts (projBack T ctorName nF)).constsResolve
      env' = true
  case neg => rw [if_neg hres] at h; exact nomatch h
  rw [if_pos hres] at h
  try dsimp only at h
  by_cases hwf3 : ((mty.renameConsts
        (projBack T ctorName nF)).looseBVarsBounded 0 &&
      !(mty.renameConsts (projBack T ctorName nF)).hasFvar &&
      (mty.renameConsts (projBack T ctorName nF)).allLevelParamsDefined
        lps) = true
  case neg => rw [if_neg hwf3] at h; exact nomatch h
  rw [if_pos hwf3] at h
  simp only [Bool.and_eq_true] at hwf3
  obtain ⟨⟨hptyb, hptyf'⟩, hptylp⟩ := hwf3
  have hptyf : (mty.renameConsts (projBack T ctorName nF)).hasFvar
      = false := by
    revert hptyf'
    cases (mty.renameConsts (projBack T ctorName nF)).hasFvar <;> simp
  try dsimp only at h
  by_cases hpis : ((mty.renameConsts
      (projBack T ctorName nF)).stripPis (nP + 1)).isSome = true
  case neg => rw [if_neg hpis] at h; exact nomatch h
  rw [if_pos hpis] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, eq_of_beq hround, hres, hptyb, hptyf, hptylp⟩

/-- Invert stage 3 of `checkProjFn` (the reduction rule). -/
theorem checkProjRule_inv {env' : Env} {cvj : ConstantVal} {lps : List Name}
    {nP nF i : Nat} {rhsA : Expr}
    (h : checkProjRule (fueledOps F) env' cvj lps nP nF i = .ok rhsA) :
    ∃ raw rbinders cbindersR cbody,
      Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) = some raw ∧
      raw.hasFvar = false ∧
      raw.looseBVarsBounded 0 = true ∧
      annotateCore env' F 0 raw = .ok rhsA ∧
      rhsA.allLevelParamsDefined lps = true ∧
      rhsA.constsResolve env' = true ∧
      rhsA.looseBVarsBounded 0 = true ∧
      rhsA.hasFvar = false ∧
      rhsA.stripLams (nP + nF) = some (rbinders, .bvar (nF - 1 - i)) ∧
      cvj.type.stripPis (nP + nF) = some (cbindersR, cbody) ∧
      domsMatchAux (fun _ e => e) rbinders cbindersR 0 0 (nP + nF)
        = true := by
  simp only [checkProjRule, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
  revert h
  match hraw : Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) with
  | none => intro h; exact nomatch h
  | some raw => ?_
  intro h
  dsimp only at h
  by_cases hrawwf : (!raw.hasFvar && raw.looseBVarsBounded 0) = true
  case neg => rw [if_neg hrawwf] at h; exact nomatch h
  rw [if_pos hrawwf] at h
  simp only [Bool.and_eq_true] at hrawwf
  obtain ⟨hrawf', hrawb⟩ := hrawwf
  have hrawf : raw.hasFvar = false := by
    revert hrawf'
    cases raw.hasFvar <;> simp
  try dsimp only at h
  cases hann : annotateCore env' F 0 raw with
  | error e => rw [hann] at h; exact nomatch h
  | ok rhsA' => ?_
  rw [hann] at h
  try dsimp only at h
  by_cases hrwf : (rhsA'.allLevelParamsDefined lps &&
      rhsA'.constsResolve env' && rhsA'.looseBVarsBounded 0 &&
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
  match hstripR : rhsA'.stripLams (nP + nF) with
  | none => intro h; exact nomatch h
  | some (rbinders, rrbody) => ?_
  intro h
  dsimp only at h
  by_cases hrrb : (rrbody == Expr.bvar (nF - 1 - i)) = true
  case neg => rw [if_neg hrrb] at h; exact nomatch h
  rw [if_pos hrrb] at h
  obtain rfl := eq_of_beq hrrb
  try dsimp only at h
  revert h
  match hC_strip : cvj.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (cbindersR, cbody) => ?_
  intro h
  dsimp only at h
  by_cases hdomsB : domsMatchAux (fun _ e => e) rbinders cbindersR 0 0
      (nP + nF) = true
  case neg => rw [if_neg hdomsB] at h; exact nomatch h
  rw [if_pos hdomsB] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨raw, rbinders, cbindersR, cbody, rfl, hrawf, hrawb, hann,
    hrlp, hrres, hrb, hrf, hstripR, rfl, hdomsB⟩

/-- Invert stage 4 of `checkProjFn` (the pinned iota statement). -/
theorem checkProjIota_inv {env' : Env} {T ctorName : Name}
    {lps : List Name} {cvj : ConstantVal} {nP nF i : Nat} {u : Unit}
    (h : (checkProjIota env' T ctorName lps cvj nP nF i : CheckM _) =
      .ok u) :
    ∃ tcv tval sbinders cbindersR cbody tySlot ℓA,
      env'.find? ((projModelName T i).str "iota") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      cvj.type.stripPis (nP + nF) = some (cbindersR, cbody) ∧
      domsMatchAux (fun _ e => e.renameConsts (projFwd T ctorName nF))
        sbinders cbindersR 0 0 (nP + nF) = true ∧
      tcv.type.stripPis (nP + nF) = some (sbinders,
        .app (.app (.app (.const eqName [ℓA]) tySlot)
          (Expr.mkAppN (.const (projModelName T i) (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
             [Expr.mkAppN
               (.const (ctorName.str "_model")
                 (cvj.levelParams.map .param))
               (((List.range nP).map fun k =>
                   Expr.bvar (nP + nF - 1 - k)) ++
                ((List.range nF).map fun k =>
                  Expr.bvar (nF - 1 - k)))])))
          (.bvar (nF - 1 - i))) := by
  simp only [checkProjIota, Bind.bind, Except.bind] at h
  revert h
  match hthm : env'.find? ((projModelName T i).str "iota") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo tcv tval) => ?_
  intro h
  dsimp only at h
  by_cases htlps : tcv.levelParams = lps
  case neg => rw [if_neg htlps] at h; exact nomatch h
  rw [if_pos htlps] at h
  try dsimp only at h
  revert h
  match hS_strip : tcv.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (sbinders, sbody) => ?_
  intro h
  dsimp only at h
  revert h
  match hC_strip : cvj.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (cbindersR, cbody) => ?_
  intro h
  dsimp only at h
  by_cases hsdomsB : domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) = true
  case neg => rw [if_neg hsdomsB] at h; exact nomatch h
  rw [if_pos hsdomsB] at h
  try dsimp only at h
  cases sbody
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sA rhsC
  cases sA
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sB lhsC
  cases sB
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sEq tySlot
  cases sEq
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case app => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i c ℓs
  cases ℓs
  case nil => exact nomatch h
  rename_i ℓA ℓtail
  cases ℓtail
  case cons => exact nomatch h
  try dsimp only at h
  by_cases hc : c = eqName
  case neg => rw [if_neg hc] at h; exact nomatch h
  rw [if_pos hc] at h
  subst hc
  try dsimp only at h
  by_cases hlhs : (lhsC == Expr.mkAppN
      (.const (projModelName T i) (lps.map .param))
      (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
       [Expr.mkAppN
         (.const (ctorName.str "_model") (cvj.levelParams.map .param))
         (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
          ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])) = true
  case neg => rw [if_neg hlhs] at h; exact nomatch h
  rw [if_pos hlhs] at h
  obtain rfl := eq_of_beq hlhs
  try dsimp only at h
  by_cases hrhsC : (rhsC == Expr.bvar (nF - 1 - i)) = true
  case neg => rw [if_neg hrhsC] at h; exact nomatch h
  rw [if_pos hrhsC] at h
  obtain rfl := eq_of_beq hrhsC
  exact ⟨tcv, tval, sbinders, cbindersR, cbody, tySlot, ℓA,
    rfl, htlps, rfl, hsdomsB, hS_strip⟩

/-- Invert a successful `checkProjFn` into its stages. -/
theorem checkProjFn_inv {env' env₁ : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat}
    (h : checkProjFn (fueledOps F) env' T ctorName lps nP nF i = .ok env₁) :
    ∃ cvj mcv,
      (checkProjLookups env' T ctorName lps nP nF i : CheckM _) =
        .ok (cvj, mcv) ∧
      ∃ pty, (checkProjTy env' T ctorName lps mcv.type nP nF : CheckM _) =
        .ok pty ∧
      i < nF ∧
      ∃ rhsA, checkProjRule (fueledOps F) env' cvj lps nP nF i = .ok rhsA ∧
      (∃ u : Unit, (checkProjIota env' T ctorName lps cvj nP nF i : CheckM _)
        = .ok u) ∧
      env₁ = ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
        [⟨ctorName, nF, rhsA⟩] :: env'.consts⟩ := by
  simp only [checkProjFn, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
  cases hlk : (checkProjLookups env' T ctorName lps nP nF i : CheckM _) with
  | error e => rw [hlk] at h; exact nomatch h
  | ok pr => ?_
  rw [hlk] at h
  obtain ⟨cvj, mcv⟩ := pr
  try dsimp only at h
  cases hty : (checkProjTy env' T ctorName lps mcv.type nP nF : CheckM _) with
  | error e => rw [hty] at h; exact nomatch h
  | ok pty => ?_
  rw [hty] at h
  try dsimp only at h
  by_cases hi : i < nF
  case neg => rw [if_neg hi] at h; exact nomatch h
  rw [if_pos hi] at h
  try dsimp only at h
  cases hrule : checkProjRule (fueledOps F) env' cvj lps nP nF i with
  | error e => rw [hrule] at h; exact nomatch h
  | ok rhsA => ?_
  rw [hrule] at h
  try dsimp only at h
  cases hio : (checkProjIota env' T ctorName lps cvj nP nF i : CheckM _) with
  | error e => rw [hio] at h; exact nomatch h
  | ok u => ?_
  rw [hio] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cvj, mcv, rfl, pty, hty, hi, rhsA, hrule, ⟨u, hio⟩, h.symm⟩

/-- The projection-phase fold invariant: the parent type and the
constructor still carry their model values, and every installed
projection function carries its `_model.proj_j`'s. -/
def ProjPhaseInv (T ctorName : Name) (nF : Nat) (env' : Env)
    (val : ConstVal V) : Prop :=
  (∀ ci, env'.find? T = some ci →
    ∃ cvm mval, env'.find? (T.str "_model") = some (.defnInfo cvm mval) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, val T ψ = val (T.str "_model") ψ) ∧
  (∀ ci, env'.find? ctorName = some ci →
    ∃ cvm mval,
      env'.find? (ctorName.str "_model") = some (.defnInfo cvm mval) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        val ctorName ψ = val (ctorName.str "_model") ψ) ∧
  (∀ j, j < nF → ∀ ci, env'.find? (projFnName T j) = some ci →
    ∃ cvm mval,
      env'.find? (projModelName T j) = some (.defnInfo cvm mval) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        val (projFnName T j) ψ = val (projModelName T j) ψ)

set_option maxHeartbeats 1600000 in
/-- One projection-function install preserves having a model together
with the phase invariant. -/
theorem checkProjFn_sound {env' env₁ : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat}
    (h : checkProjFn (fueledOps F) env' T ctorName lps nP nF i = .ok env₁)
    (m : EnvModel V env')
    (hinv : ProjPhaseInv T ctorName nF env' m.val) :
    ∃ m₁ : EnvModel V env₁, ProjPhaseInv T ctorName nF env₁ m₁.val := by
  obtain ⟨cvj, mcv, hlk, pty, hty, hi, rhsA, hrule, ⟨u, hio⟩, henv₁⟩ :=
    checkProjFn_inv h
  obtain ⟨mval, hctor, hfm, hmlps, hpnone, hTf, heqf⟩ :=
    checkProjLookups_inv hlk
  obtain ⟨hptyB, hround, hptyres, hptyb, hptyf, hptylp⟩ :=
    checkProjTy_inv hty
  obtain ⟨raw, rbinders, cbindersR, cbody, hraw, hrawf, hrawb, hann,
    hrlp, hrres, hrb, hrf, hstripR, hC_strip, hdomsB⟩ :=
    checkProjRule_inv hrule
  obtain ⟨tcv, tval, sbinders, cbindersR₂, cbody₂, tySlot, ℓA,
    hthm, htlps, hC_strip₂, hsdomsB, hS_strip⟩ := checkProjIota_inv hio
  obtain ⟨rfl, rfl⟩ : cbindersR = cbindersR₂ ∧ cbody = cbody₂ := by
    have hpair := Option.some.inj (hC_strip.symm.trans hC_strip₂)
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  subst henv₁
  -- basic disequalities from freshness
  have hTne : T ≠ projFnName T i := by
    intro he
    rw [he, hpnone] at hTf
    exact nomatch hTf
  have hCne : ctorName ≠ projFnName T i := by
    intro he
    rw [he, hpnone] at hctor
    exact nomatch hctor
  -- the semantically pruned renaming and the rule's full renaming
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Name → Name, f₀ = fun n =>
      if (env'.find? n).isSome then projFwd T ctorName nF n else n :=
    ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Name → Name, f = fun n =>
      if n = projFnName T i then projModelName T i else f₀ n := ⟨_, rfl⟩
  have hfound : ∀ n ci₂, env'.find? n = some ci₂ →
      (∃ ci', env'.find? (projFwd T ctorName nF n) = some ci' ∧
        ci'.toConstantVal.levelParams = ci₂.toConstantVal.levelParams) ∧
      (∀ ψ : Name → Nat,
        m.val (projFwd T ctorName nF n) ψ = m.val n ψ) := by
    intro n ci₂ hf₂
    unfold projFwd
    try dsimp only
    by_cases h1 : n = T
    · subst h1
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h1]
    by_cases h2 : n = ctorName
    · subst h2
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h2]
    cases hfind : (List.range nF).find? (fun j => n == projFnName T j) with
    | none => exact ⟨⟨ci₂, hf₂, rfl⟩, fun ψ => rfl⟩
    | some j =>
      have hjlt : j < nF :=
        List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      have hprop := List.find?_some hfind
      have hprop' : (n == projFnName T j) = true := by
        simpa using hprop
      have hn : n = projFnName T j := eq_of_beq hprop'
      subst hn
      obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.2 j hjlt ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
  have hro : RenameOk m.val env' f₀ := by
    refine ⟨?_, ?_, ?_⟩
    · intro n ci₂ hf₂
      rw [hf₀]
      dsimp only
      rw [if_pos (show (env'.find? n).isSome = true by rw [hf₂]; rfl)]
      exact (hfound n ci₂ hf₂).1
    · intro n hf₂
      rw [hf₀]
      dsimp only
      rw [if_neg (show ¬(env'.find? n).isSome = true by
        rw [hf₂]; exact fun hx => nomatch hx)]
      exact hf₂
    · intro n ψ
      rw [hf₀]
      dsimp only
      cases hf₂ : env'.find? n with
      | none =>
        rw [if_neg (show ¬(none : Option ConstantInfo).isSome = true
          from fun hx => nomatch hx)]
      | some ci₂ =>
        rw [if_pos (show (some ci₂ : Option ConstantInfo).isSome = true
          from rfl)]
        exact (hfound n ci₂ hf₂).2 ψ
  have hagree : ∀ n, (env'.find? n).isSome = true →
      f n = projFwd T ctorName nF n := by
    intro n hn
    have hne : n ≠ projFnName T i := by
      intro he
      rw [he, hpnone] at hn
      exact nomatch hn
    rw [hf]
    dsimp only
    rw [if_neg hne, hf₀]
    dsimp only
    rw [if_pos hn]
  have hff₀ : ∀ n, n ≠ projFnName T i → f n = f₀ n := by
    intro n hn
    rw [hf]
    dsimp only
    rw [if_neg hn]
  have hfself : f (projFnName T i) = projModelName T i := by
    rw [hf]
    dsimp only
    rw [if_pos rfl]
  have hfnot : ∀ n, f n ≠ projFnName T i := by
    intro n
    rw [hf]
    dsimp only
    by_cases hn : n = projFnName T i
    · rw [if_pos hn]
      exact fun hh => Name.num_ne_str _ _ _ _ hh.symm
    · rw [if_neg hn, hf₀]
      dsimp only
      cases hf₂ : env'.find? n with
      | none =>
        rw [if_neg (show ¬(none : Option ConstantInfo).isSome = true
          from fun hx => nomatch hx)]
        exact hn
      | some ci₂ =>
        rw [if_pos (show (some ci₂ : Option ConstantInfo).isSome = true
          from rfl)]
        unfold projFwd
        try dsimp only
        by_cases h1 : n = T
        · rw [if_pos h1]
          exact fun hh => Name.num_ne_str _ _ _ _ hh.symm
        rw [if_neg h1]
        by_cases h2 : n = ctorName
        · rw [if_pos h2]
          exact fun hh => Name.num_ne_str _ _ _ _ hh.symm
        rw [if_neg h2]
        cases (List.range nF).find? (fun j => n == projFnName T j) with
        | none => exact hn
        | some j => exact fun hh => Name.num_ne_str _ _ _ _ hh.symm
  have hren : pty.renameConsts f = mcv.type := by
    rw [Expr.renameConsts_congr_resolve hagree pty hptyres]
    exact hround
  have hcres : cvj.type.constsResolve env' = true := by
    obtain ⟨-, -, h3, -⟩ := m.wf _ (find?_mem hctor)
    exact h3
  have hdomres :=
    (Expr.constsResolve_stripPis (nP + nF) hC_strip hcres).1
  have hclen : cbindersR.length = nP + nF :=
    Expr.stripPis_length _ hC_strip
  have hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      rbinders[k]? = some b → cbindersR[k]? = some b' →
      b.2.1 = b'.2.1 := by
    intro k b b' hb hb'
    have hk : k < nP + nF := by
      rcases Nat.lt_or_ge k (nP + nF) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by omega)] at hb'
        exact nomatch hb'
    exact domsMatchAux_inv hdomsB hk
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
  have hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbindersR[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f := by
    intro k b b' hb hb'
    have hk : k < nP + nF := by
      rcases Nat.lt_or_ge k (nP + nF) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by omega)] at hb'
        exact nomatch hb'
    have hkfwd := domsMatchAux_inv hsdomsB hk
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
    rw [hkfwd]
    exact (Expr.renameConsts_congr_resolve hagree _
      (hdomres b' (List.mem_of_getElem? hb'))).symm
  have hfctor : f ctorName = ctorName.str "_model" := by
    rw [hagree ctorName (by rw [hctor]; rfl)]
    unfold projFwd
    try dsimp only
    by_cases hCT : ctorName = T
    · rw [if_pos hCT, hCT]
    · rw [if_neg hCT, if_pos rfl]
  have heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'' := by
    intro ψ''
    obtain ⟨-, hpv⟩ :=
      m.ind_ok.2.2.2.1 eqName eqA heqf (by rfl) (by decide)
    rw [hpv ψ'']
    simp [pinnedVal]
  have hwf : ConstWF
      ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
        [⟨ctorName, nF, rhsA⟩] :: env'.consts⟩
      (.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
        [⟨ctorName, nF, rhsA⟩]) := by
    refine ⟨hptyf, hptylp, Expr.constsResolve_mono hptyres, hptyb,
      ?_, ?_⟩
    · intro cv2 v2 heq
      exact nomatch heq
    · intro cv2 nP' nM' nm' ni' rules'' heq r hr
      injection heq with e1 e2 e3 e4 e5 e6
      subst e6
      rcases List.mem_cons.mp hr with rfl | hr
      · refine ⟨hrf, ?_, Expr.constsResolve_mono hrres, hrb⟩
        rw [← e1]
        exact hrlp
      · exact absurd hr List.not_mem_nil
  have hsbody' : (Expr.app (.app (.app (.const eqName [ℓA]) tySlot)
      (Expr.mkAppN (.const (projModelName T i) (lps.map .param))
        (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN
           (.const (ctorName.str "_model")
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k =>
              Expr.bvar (nF - 1 - k)))])))
      (.bvar (nF - 1 - i))) = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f (projFnName T i)) (lps.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f ctorName)
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)] := by
    rw [hfself, hfctor]
    rfl
  have hprojmArg : ∀ (T' : Name) (j : Nat),
      projFnName T i = projFnName T' j →
      (env'.find? (projModelName T' j)).isSome = true ∧
      ∀ ψ : Name → Nat,
        m.val (projModelName T i) ψ = m.val (projModelName T' j) ψ := by
    intro T' j hh
    have hh' : Name.num (T.str "proj") i = Name.num (T'.str "proj") j := hh
    injection hh' with hp hij
    injection hp with hT hs
    subst hij
    subst hT
    exact ⟨by rw [hfm]; rfl, fun ψ => rfl⟩
  obtain ⟨m₁, hval₁, hpres₁⟩ := extend_proj_fn m
    ⟨projFnName T i, lps, pty⟩ nP nF i ⟨ctorName, nF, rhsA⟩ f
    (projModelName T i) hpnone
    (reservedBasisNames_not_num _ _) hwf hptyres hfm hmlps hprojmArg hren
    f₀ hro hff₀ hfself hfnot heqf heqval hi hctor rfl
    hann hrawf hrawb hrf hrb hrres hstripR rfl hC_strip hS_strip
    hdoms hsdoms hsbody' hthm htlps
  have hval₁' : ∀ ψ : Name → Nat,
      m₁.val (projFnName T i) ψ = m.val (projModelName T i) ψ := hval₁
  have hpres₁' : ∀ (n : Name) (ψ : Name → Nat), n ≠ projFnName T i →
      m₁.val n ψ = m.val n ψ := hpres₁
  have hfindNe : ∀ n : Name, n ≠ projFnName T i →
      (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
        [⟨ctorName, nF, rhsA⟩] :: env'.consts⟩ : Env).find? n
        = env'.find? n := by
    intro n hn
    rw [Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩
        nP 0 0 0 [⟨ctorName, nF, rhsA⟩]).name = n from
        fun hh => hn hh.symm)]
  refine ⟨m₁, ?_, ?_, ?_⟩
  · -- the parent type's clause
    intro ci₂ hf₂
    rw [hfindNe T hTne] at hf₂
    obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
    refine ⟨cvm₂, mval₂, ?_, hlps₂, ?_⟩
    · rw [hfindNe (T.str "_model")
        (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁' _ ψ hTne,
        hpres₁' _ ψ (fun hh => Name.num_ne_str _ _ _ _ hh.symm),
        hv₂ ψ]
  · -- the constructor's clause
    intro ci₂ hf₂
    rw [hfindNe ctorName hCne] at hf₂
    obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
    refine ⟨cvm₂, mval₂, ?_, hlps₂, ?_⟩
    · rw [hfindNe (ctorName.str "_model")
        (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁' _ ψ hCne,
        hpres₁' _ ψ (fun hh => Name.num_ne_str _ _ _ _ hh.symm),
        hv₂ ψ]
  · -- the projection-family clause
    intro j hj ci₂ hf₂
    by_cases hji : projFnName T j = projFnName T i
    · -- the freshly installed projection
      have hn' : Name.num (T.str "proj") j =
          Name.num (T.str "proj") i := hji
      injection hn' with hp hij
      subst hij
      refine ⟨mcv, mval, ?_, ?_, ?_⟩
      · rw [hfindNe (projModelName T j)
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hfm
      · rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo ⟨projFnName T j, lps, pty⟩
            nP 0 0 0 [⟨ctorName, nF, rhsA⟩]).name = projFnName T j
            from rfl)] at hf₂
        obtain rfl := Option.some.inj hf₂
        exact hmlps
      · intro ψ
        rw [hval₁' ψ,
          hpres₁' (projModelName T j) ψ
            (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
    · -- an earlier install, preserved
      rw [hfindNe (projFnName T j) hji] at hf₂
      obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.2 j hj ci₂ hf₂
      refine ⟨cvm₂, mval₂, ?_, hlps₂, ?_⟩
      · rw [hfindNe (projModelName T j)
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hfm₂
      · intro ψ
        rw [hpres₁' _ ψ hji,
          hpres₁' (projModelName T j) ψ
            (fun hh => Name.num_ne_str _ _ _ _ hh.symm),
          hv₂ ψ]

/-- The projection-phase fold preserves having a model together with
the phase invariant. -/
theorem checkProjFold_sound {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM (fun e i =>
      if (e.find? (projModelName T i)).isSome then
        checkProjFn (fueledOps F) e T ctorName lps nP nF i
      else pure e) env' = .ok env₁ →
    ∀ m : EnvModel V env', ProjPhaseInv T ctorName nF env' m.val →
    ∃ m₁ : EnvModel V env₁, ProjPhaseInv T ctorName nF env₁ m₁.val
  | [], env', env₁, h, m, hinv => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m, hinv⟩
  | i₀ :: rest, env', env₁, h, m, hinv => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    by_cases hm : (env'.find? (projModelName T i₀)).isSome = true
    · rw [if_pos hm] at h
      cases hstep : checkProjFn (fueledOps F) env' T ctorName lps nP nF i₀ with
      | error e => rw [hstep] at h; exact nomatch h
      | ok env₂ => ?_
      rw [hstep] at h
      obtain ⟨m₂, hinv₂⟩ := checkProjFn_sound hstep m hinv
      exact checkProjFold_sound rest env₂ env₁ h m₂ hinv₂
    · rw [if_neg hm] at h
      simp only [pure, Except.pure, Except.bind] at h
      exact checkProjFold_sound rest env' env₁ h m hinv

/-- Checking a modeled inductive block preserves having a model. -/
theorem checkIndDecl_sound {env env₂ : Env} {block : List ConstantInfo}
    (h : checkIndDecl (fueledOps F) env block = .ok env₂) (m : EnvModel V env) :
    Nonempty (EnvModel V env₂) := by
  rw [checkIndDecl] at h
  have hbn : ∀ ci ∈ block, (block.map (·.name)).contains ci.name = true :=
    fun ci hci => by
      have : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
      simpa using this
  split at h
  · -- the single-constructor arm installs the projection family
    rename_i cvT capsT cvC nP nF heqI heqC
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₁, hfold, h⟩ := Except.bind_ok h
    have hI₀ : BlockInstalled (block.map (·.name)) env m.val := by
      intro n hn ci₂ hf₂
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [checkIndMember_fold_names block env env₁ hfold ci₀ hci₀] at hf₂
      exact nomatch hf₂
    have hpins0 : ∀ (cv : ConstantVal) (caps₂ : IndCaps),
        (ConstantInfo.indInfo cv caps₂) ∈ block →
        EtaPins env cv.name cv.levelParams
          (indBlockCaps env cvT cvC nP nF) := by
      intro cv caps₂ hmem
      have hmemf : (ConstantInfo.indInfo cv caps₂) ∈
          ([ConstantInfo.indInfo cvT capsT] : List ConstantInfo) := by
        rw [← heqI]
        exact List.mem_filter.mpr ⟨hmem, rfl⟩
      have hid := List.mem_singleton.mp hmemf
      injection hid with h1 h2
      rw [h1]
      refine ⟨?_, ?_⟩
      · intro hcape
        simp only [indBlockCaps, Bool.and_eq_true] at hcape
        exact checkEtaThm_inv hcape.2
      · intro hcapu
        simp only [indBlockCaps] at hcapu
        exact checkUnitThm_inv hcapu
    obtain ⟨m₁, hI₁⟩ := checkIndFold_sound block env env₁ hbn hpins0
      hfold m hI₀
    have hTin : (ConstantInfo.indInfo cvT capsT) ∈ block := by
      have h1 : ConstantInfo.indInfo cvT capsT ∈
          [ConstantInfo.indInfo cvT capsT] :=
        List.mem_singleton.mpr rfl
      rw [← heqI] at h1
      exact (List.mem_filter.mp h1).1
    have hCin : (ConstantInfo.ctorInfo cvC nP nF) ∈ block := by
      have h1 : ConstantInfo.ctorInfo cvC nP nF ∈
          [ConstantInfo.ctorInfo cvC nP nF] :=
        List.mem_singleton.mpr rfl
      rw [← heqC] at h1
      exact (List.mem_filter.mp h1).1
    have hbnT : (block.map (·.name)).contains cvT.name = true := by
      have hmm : cvT.name ∈ block.map (fun x => x.name) :=
        List.mem_map_of_mem (f := fun x => x.name) hTin
      simpa using hmm
    have hbnC : (block.map (·.name)).contains cvC.name = true := by
      have hmm : cvC.name ∈ block.map (fun x => x.name) :=
        List.mem_map_of_mem (f := fun x => x.name) hCin
      simpa using hmm
    try simp only [Bind.bind, Except.bind] at h
    by_cases hfresh : ((List.range nF).all
        (fun j => (env₁.find? (projFnName cvT.name j)).isNone)) = true
    case neg => rw [if_neg hfresh] at h; exact nomatch h
    rw [if_pos hfresh] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    have hinv₀ : ProjPhaseInv cvT.name cvC.name nF env₁ m₁.val := by
      refine ⟨?_, ?_, ?_⟩
      · intro ci hf
        exact hI₁ cvT.name hbnT ci hf
      · intro ci hf
        exact hI₁ cvC.name hbnC ci hf
      · intro j hj ci hf
        have hnone := List.all_eq_true.mp hfresh j (List.mem_range.mpr hj)
        rw [Option.isNone_iff_eq_none.mp hnone] at hf
        exact nomatch hf
    obtain ⟨mf, -⟩ :=
      checkProjFold_sound (List.range nF) env₁ env₂ h m₁ hinv₀
    exact ⟨mf⟩
  · -- no single-constructor structure: the plain member fold
    have hI₀ : BlockInstalled (block.map (·.name)) env m.val := by
      intro n hn ci₂ hf₂
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [checkIndMember_fold_names block env env₂ h ci₀ hci₀] at hf₂
      exact nomatch hf₂
    obtain ⟨m₂, -⟩ := checkIndFold_sound block env env₂ hbn
      (fun _ _ _ => ⟨fun hcape => absurd hcape (by decide),
        fun hcapu => absurd hcapu (by decide)⟩) h m hI₀
    exact ⟨m₂⟩

end Setlec
