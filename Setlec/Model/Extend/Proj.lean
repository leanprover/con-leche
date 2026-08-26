import Setlec.Verify.Extend.Proj
import Setlec.Model.Extend.ProjFn
import Setlec.Model.ModeledCaps

/-!
# Proj — split out of `Setlec.Model.Extend`

Soundness of the projection-family install phase: the `checkProjFn`
stage inversions, `ProjPhaseInv`, `checkProjFn_sound` and
`checkProjFold_sound`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by a Prop-fallback elimination-template entry: a
`native = false` projection-table constant with the closed junk type
`Prop` and a junk truth-value valuation.  Every semantic clause is
vacuous for template entries (the fallback's output is re-checked at
every use). -/
theorem extend_proj_template {env : Env} (m : EnvModel V env)
    (entry : ProjEntry)
    (hnat : entry.native = false)
    (hty : entry.ty = .sort .zero)
    (hfind' : env.find? (projFnName entry.structName entry.idx) = none) :
    ∃ m' : EnvModel V ⟨.projInfo entry :: env.consts⟩,
      (∀ ψ, m'.val (projFnName entry.structName entry.idx) ψ =
        eqv pt pt) ∧
      (∀ n ψ, n ≠ projFnName entry.structName entry.idx →
        m'.val n ψ = m.val n ψ) := by
  have hname : (ConstantInfo.projInfo entry).name =
      projFnName entry.structName entry.idx := rfl
  have hwf : ConstWF ⟨.projInfo entry :: env.consts⟩ (.projInfo entry) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show entry.ty.hasFvar = false
      rw [hty]; rfl
    · show entry.ty.allLevelParamsDefined _ = true
      rw [hty]; rfl
    · show entry.ty.constsResolve _ = true
      rw [hty]; rfl
    · show entry.ty.looseBVarsBounded 0 = true
      rw [hty]; rfl
    · intro cv2 v2 h2 heq
      exact nomatch heq
    · intro cv2 mI2 rP2 rules2 heq
      exact nomatch heq
    · intro cv2 v2 heq
      exact nomatch heq
  refine extend_fresh m (.projInfo entry) (fun _ => eqv pt pt)
    (hname ▸ hfind') hwf
    (by show entry.ty.constsResolve env = true
        rw [hty]; rfl)
    (fun cv2 v2 h2 heq => nomatch heq)
    (fun cv2 v2 heq => nomatch heq)
    (fun ψ => ?_)
    (fun _ _ _ => rfl)
    (fun ψ => by
      show AnnotOk V m.val env ψ 0 (rho0 V) entry.ty
      rw [hty]
      simp [AnnotOk])
    (fun cv caps heq _ => nomatch heq)
    (fun cv nP2 nF2 heq _ => nomatch heq)
    (fun cv caps heq _ => nomatch heq)
    (fun hn => by
      exfalso
      revert hn
      show ¬(ConstantInfo.projInfo entry).name = emptyName
      rw [hname]
      simp [projFnName, emptyName])
    (fun hb _ => nomatch hb)
    (fun _ _ _ _ hx => nomatch hx)
    (fun _ _ _ _ _ _ _ hx => nomatch hx)
    (fun _ _ _ _ hx => nomatch hx)
    (fun e2 heq hnat2 => by
      obtain rfl := ConstantInfo.projInfo.inj heq
      rw [hnat] at hnat2
      exact nomatch hnat2)
    (fun val' _ _ =>
      ⟨capsEtaHead_of_kinds
        (fun _ _ hx => nomatch hx)
        (fun _ _ _ hx => nomatch hx)
        (fun _ _ _ _ hx => nomatch hx),
      fun _ _ hx _ _ => nomatch hx⟩)
    (fun _ _ _ _ _ _ heq _ => nomatch heq)
    (fun _ _ _ _ _ _ heq _ => nomatch heq)
    (fun _ _ _ _ heq _ _ => nomatch heq)
  · -- the junk value inhabits `Prop`
    show ∃ T, interpClosed V m.val env ψ entry.ty = some T ∧
      eqv pt pt ∈ˢ T
    rw [hty]
    exact ⟨univ 0, by simp [interpClosed, interpExpr, Level.eval],
      eqv_mem_univ pt pt⟩

/-- The projection-phase fold invariant: the parent type and the
constructor still carry their model values, and every installed
projection function carries its `_model.proj_j`'s. -/
def ProjPhaseInv (T ctorName : Name) (nF : Nat) (env' : Env)
    (val : ConstVal V) : Prop :=
  (∀ ci, env'.find? T = some ci →
    ∃ cvm mval hmcvm, env'.find? (T.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, val T ψ = val (T.str "_model") ψ) ∧
  (∀ ci, env'.find? ctorName = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (ctorName.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        val ctorName ψ = val (ctorName.str "_model") ψ) ∧
  (∀ j, j < nF → ∀ ci, env'.find? (projFnName T j) = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (projModelName T j) = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        val (projFnName T j) ψ = val (projModelName T j) ψ)

set_option maxHeartbeats 1600000 in
/-- One projection-function install preserves having a model together
with the phase invariant. -/
theorem checkProjFn_sound {env' env₁ : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} {blockNames : List Name}
    (h : checkProjFn (fueledOps F) env' T ctorName lps nP nF i = .ok env₁)
    (m : EnvModel V env')
    (hinv : ProjPhaseInv T ctorName nF env' m.val)
    (hIB : BlockInstalled blockNames env' m.val)
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false)
    (hpinsT : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      EtaPins env' T cvT.levelParams capsT)
    (hCblock : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → blockNames.contains capsT.etaCtor = true)
    (hFields : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → capsT.etaFields = nF) :
    ∃ m₁ : EnvModel V env₁, ProjPhaseInv T ctorName nF env₁ m₁.val ∧
      BlockInstalled blockNames env₁ m₁.val ∧
      ∃ ciH : ConstantInfo, env₁ = ⟨ciH :: env'.consts⟩ ∧
        env'.find? ciH.name = none ∧ ciH.name = projFnName T i := by
  obtain ⟨cvj, mcv, hlk, pty, hty, ⟨u0, hshape⟩, hi, rhsA, hrule,
    ⟨u, hio⟩, henv₁⟩ := checkProjFn_inv h
  obtain ⟨mval, hmmcv, hctor, hfm, hmlps, hpnone, hTf, heqf⟩ :=
    checkProjLookups_inv hlk
  obtain ⟨hptyB, hround, hptyres, hptyb, hptyf, hptylp⟩ :=
    checkProjTy_inv hty
  obtain ⟨raw, rbinders, cbindersR, cbody, hraw, hrawf, hrawb, hann,
    hrlp, hrres, hrb, hrf, hstripR, hC_strip, hdomsB,
    fvsP0, rest00, cdomsP0, crestP0, xFvs0, crest2X0, ldoms0, lrestL0,
    hopenP0, hcinstP0, hdeParsP0, hopenX0, hlinstP0, hdeLamP0,
    rhsTy0, hity0⟩ := checkProjRule_inv hrule
  obtain ⟨tcv, tval, sbinders, cbindersR₂, cbody₂, tySlot, ℓA,
    hthm, htlps, hC_strip₂, hsdomsB, hS_strip,
    fvsO, sbodyO, hopenO, hlhsTyC, hrhsTyC⟩ :=
    checkProjIota_inv hio
  obtain ⟨rfl, rfl⟩ : cbindersR = cbindersR₂ ∧ cbody = cbody₂ := by
    have hpair := Option.some.inj (hC_strip.symm.trans hC_strip₂)
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  obtain ⟨abinders, arest, cbindersR₃, cbody₃, hA_strip, hC_strip₃,
    hcheadC, hclenP⟩ := checkProjShape_inv hshape
  obtain ⟨rfl, rfl⟩ : cbindersR = cbindersR₃ ∧ cbody = cbody₃ := by
    have hpair := Option.some.inj (hC_strip.symm.trans hC_strip₃)
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  obtain ⟨dN, dus, hchead⟩ := hcheadC
  have hcbody : cbody = Expr.mkAppN (.const dN dus) cbody.getAppArgs := by
    have h0 := Expr.mkAppN_getApp cbody
    rw [hchead] at h0
    exact h0.symm
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
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h1]
    by_cases h2 : n = ctorName
    · subst h2
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
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
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.2 j hjlt ci₂ hf₂
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
      ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩
      (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain else .inert), rhsA⟩]) := by
    refine ⟨hptyf, hptylp, Expr.constsResolve_mono hptyres, hptyb,
      ?_, ?_, ?_⟩
    · intro cv2 v2 h2 heq
      exact nomatch heq
    · intro cv2 mI' rP' rules'' heq r hr
      injection heq with e1 e2 e3 e4
      subst e4
      rcases List.mem_cons.mp hr with rfl | hr
      · refine ⟨hrf, ?_, Expr.constsResolve_mono hrres, hrb, ?_⟩
        · rw [← e1]
          exact hrlp
        · intro lvls pins h
          cases hcond : Expr.recRulePlain pty nP nP nP <;>
            simp [hcond] at h
      · exact absurd hr List.not_mem_nil
    · intro cv2 v2 heq
      exact nomatch heq
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
  have hnotb : blockNames.contains (projFnName T i) = false := by
    cases hc : blockNames.contains (projFnName T i) with
    | false => rfl
    | true =>
      have hsh := hbshape _ hc
      rw [show (projFnName T i).isProjFnShape = true from rfl] at hsh
      exact nomatch hsh
  have hheadEtaP : ∀ (T' : Name) (cvT : ConstantVal) (capsT : IndCaps),
      (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP [] ::
        env'.consts⟩ : Env).find? T' = some (.indInfo cvT capsT) →
      capsT.eta = true → reservedBasisNames.contains T' = false →
      EtaFamilyStored (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP [] ::
        env'.consts⟩ : Env) T' capsT →
      (∃ j, j < capsT.etaFields ∧ projFnName T' j = projFnName T i) →
      ∀ val₁ : ConstVal V,
        (∀ (n : Name) (ψ : Name → Nat), n ≠ projFnName T i →
          val₁ n ψ = m.val n ψ) →
        (∀ ψ : Name → Nat,
          val₁ (projFnName T i) ψ = m.val (projModelName T i) ψ) →
        EtaLaw V (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP [] ::
          env'.consts⟩ : Env) val₁ T' cvT capsT := by
    intro T' cvT capsT hfT' hcape hresT hfam hpart val₁ he₁ hv₁
    obtain ⟨j, hj, hP⟩ := hpart
    have hh' : Name.num (T'.str "proj") j =
        Name.num (T.str "proj") i := hP
    injection hh' with hp hij
    injection hp with hT hs
    have hieq : i = j := hij.symm
    subst hieq
    have hTeq : T = T' := hT.symm
    subst hTeq
    have hfT'' : env'.find? T = some (.indInfo cvT capsT) := by
      rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.recInfo
        ⟨projFnName T i, lps, pty⟩ nP nP []).name = T from
        fun hh => hTne hh.symm)] at hfT'
      exact hfT'
    have hpins₁ : EtaPins (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP []
        :: env'.consts⟩ : Env) T cvT.levelParams capsT :=
      EtaPins.step (hpinsT cvT capsT hfT'') hpnone
    have hI₁ : BlockInstalled blockNames
        (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP [] ::
          env'.consts⟩ : Env) val₁ :=
      BlockInstalled.fresh_cons hIB hnotb hpnone he₁
    have hcvp : ConstValParams val₁
        (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP [] ::
          env'.consts⟩ : Env) := by
      intro n ci₂ hf ψ₁ ψ₂ hψ
      by_cases hn : n = projFnName T i
      · subst hn
        rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo
            ⟨projFnName T i, lps, pty⟩ nP nP []).name =
            projFnName T i from rfl)] at hf
        obtain rfl := Option.some.inj hf
        rw [hv₁ ψ₁, hv₁ ψ₂]
        refine m.val_params _ _ hfm ψ₁ ψ₂ ?_
        intro p hp
        refine hψ p ?_
        rw [show (ConstantInfo.defnInfo mcv mval hmmcv).toConstantVal
          = mcv from rfl] at hp
        show p ∈ lps
        rw [← hmlps]
        exact hp
      · rw [Env.find?_cons, if_neg (fun hh => hn hh.symm)] at hf
        rw [he₁ n ψ₁ hn, he₁ n ψ₂ hn]
        exact m.val_params n ci₂ hf ψ₁ ψ₂ hψ
    obtain ⟨cvmT', mvalT', hmT', hfmT', hlpsT', hrenT', hvT'⟩ :=
      hIB T hTblock _ hfT''
    refine modeled_caps_eta
      (ci := .recInfo ⟨projFnName T i, lps, pty⟩ nP nP []) m hpnone
      he₁ hI₁ hcvp (reservedBasisNames_not_num _ _)
      (fun cv2 v2 hcon => nomatch hcon) hcape hpins₁ ?_ ?_ ?_ ?_ ?_ ?_
    · intro cvmT mvalT hm2 hfm₁
      rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.recInfo
        ⟨projFnName T i, lps, pty⟩ nP nP []).name = T.str "_model" from
        fun hh => Name.num_ne_str _ _ _ _ hh)] at hfm₁
      rw [hfmT'] at hfm₁
      obtain h1 := Option.some.inj hfm₁
      injection h1 with e1 e2 e3
      subst e1
      exact hrenT'
    · obtain ⟨h1, -⟩ := m.wf _ (find?_mem hfT'')
      exact h1
    · obtain ⟨-, -, h3, -⟩ := m.wf _ (find?_mem hfT'')
      exact Expr.constsResolve_mono h3
    · intro ψ
      rw [he₁ T ψ hTne,
        he₁ (T.str "_model") ψ
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hvT' ψ
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      have hCb : blockNames.contains capsT.etaCtor = true :=
        hCblock cvT capsT hfT'' hcape
      have hCshape := hbshape _ hCb
      have hCne : capsT.etaCtor ≠ projFnName T i := by
        intro hh
        rw [hh] at hCshape
        exact nomatch hCshape
      have hfC' : env'.find? capsT.etaCtor =
          some (.ctorInfo cvC capsT.etaParams capsT.etaFields) := by
        rw [Env.find?_cons, if_neg (fun hh => hCne hh.symm)] at hfC
        exact hfC
      obtain ⟨cvmC', mvalC', hmC', hfmC', -, -, hvC'⟩ :=
        hIB capsT.etaCtor hCb _ hfC'
      intro ψ
      rw [he₁ capsT.etaCtor ψ hCne,
        he₁ (capsT.etaCtor.str "_model") ψ
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hvC' ψ
    · intro j' hj' ψ
      by_cases hji : j' = i
      · subst hji
        rw [hv₁ ψ,
          he₁ (projModelName T j') ψ
            (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      · obtain ⟨-, -, hfP⟩ := hfam
        obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j' hj'
        have hne2 : projFnName T j' ≠ projFnName T i := by
          intro hh
          have hh2 : Name.num (T.str "proj") j' =
              Name.num (T.str "proj") i := hh
          injection hh2 with hp2 hij2
          exact hji hij2
        have hf2' : env'.find? (projFnName T j') =
            some (.recInfo cv2 mI2 rP2 rules2) := by
          rw [Env.find?_cons, if_neg (fun hh => hne2 hh.symm)] at hf2
          exact hf2
        have hjnF : j' < nF := by
          rw [← hFields cvT capsT hfT'' hcape]
          exact hj'
        obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ :=
          hinv.2.2 j' hjnF _ hf2'
        rw [he₁ _ ψ hne2,
          he₁ (projModelName T j') ψ
            (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hv₂ ψ
  obtain ⟨m₁, hval₁, hpres₁⟩ := extend_proj_fn m
    ⟨projFnName T i, lps, pty⟩ nP nF i
    ⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain else .inert), rhsA⟩ f
    (projModelName T i) hpnone
    (reservedBasisNames_not_num _ _) hwf hptyres hfm hmlps
    hren
    f₀ hro hff₀ hfself hfnot heqf heqval hi
    (fun lvls pins => by
      cases h : Expr.recRulePlain pty nP nP nP <;> simp [h])
    hctor rfl rfl
    hrres hstripR rfl hC_strip hS_strip
    hsdoms hcbody hclenP hsbody' hopenO hrhsTyC hthm htlps
    hopenP0 hcinstP0 hdeParsP0 hopenX0 hlinstP0 hdeLamP0 hrf hrb hity0
    hheadEtaP
  have hval₁' : ∀ ψ : Name → Nat,
      m₁.val (projFnName T i) ψ = m.val (projModelName T i) ψ := hval₁
  have hpres₁' : ∀ (n : Name) (ψ : Name → Nat), n ≠ projFnName T i →
      m₁.val n ψ = m.val n ψ := hpres₁
  have hfindNe : ∀ n : Name, n ≠ projFnName T i →
      (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain else .inert), rhsA⟩] :: env'.consts⟩ : Env).find? n
        = env'.find? n := by
    intro n hn
    rw [Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩
        nP nP [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain else .inert),
          rhsA⟩]).name = n from
        fun hh => hn hh.symm)]
  refine ⟨m₁, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- the parent type's clause
    intro ci₂ hf₂
    rw [hfindNe T hTne] at hf₂
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, ?_⟩
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
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, ?_⟩
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
      refine ⟨mcv, mval, hmmcv, ?_, ?_, ?_⟩
      · rw [hfindNe (projModelName T j)
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hfm
      · rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo ⟨projFnName T j, lps, pty⟩
            nP nP [⟨ctorName, nF, nP, (if Expr.recRulePlain pty nP nP nP then RecRuleFire.plain else .inert),
              rhsA⟩]).name = projFnName T j
            from rfl)] at hf₂
        obtain rfl := Option.some.inj hf₂
        exact hmlps
      · intro ψ
        rw [hval₁' ψ,
          hpres₁' (projModelName T j) ψ
            (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
    · -- an earlier install, preserved
      rw [hfindNe (projFnName T j) hji] at hf₂
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.2 j hj ci₂ hf₂
      refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, ?_⟩
      · rw [hfindNe (projModelName T j)
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hfm₂
      · intro ψ
        rw [hpres₁' _ ψ hji,
          hpres₁' (projModelName T j) ψ
            (fun hh => Name.num_ne_str _ _ _ _ hh.symm),
          hv₂ ψ]
  · -- the block invariant, preserved across the fresh non-member head
    exact BlockInstalled.fresh_cons hIB hnotb hpnone hpres₁'
  · -- the head's shape
    exact ⟨_, rfl, hpnone, rfl⟩


/-- The projection-phase fold preserves having a model together with
the phase invariant, the block invariant and the former's pins. -/
theorem checkProjFold_sound {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} {blockNames : List Name}
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false) :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM (installProjFnStep (fueledOps F) T ctorName lps nP nF)
      env' = .ok env₁ →
    ∀ m : EnvModel V env', ProjPhaseInv T ctorName nF env' m.val →
    BlockInstalled blockNames env' m.val →
    (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      EtaPins env' T cvT.levelParams capsT) →
    (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → blockNames.contains capsT.etaCtor = true) →
    (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → capsT.etaFields = nF) →
    ∃ m₁ : EnvModel V env₁, ProjPhaseInv T ctorName nF env₁ m₁.val
  | [], env', env₁, h, m, hinv, _, _, _, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m, hinv⟩
  | i₀ :: rest, env', env₁, h, m, hinv, hIB, hpinsT, hCblock, hFields => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    unfold installProjFnStep at h
    by_cases hm : (env'.find? (projModelName T i₀)).isSome = true
    · rw [if_pos hm] at h
      cases hstep : checkProjFn (fueledOps F) env' T ctorName lps nP nF i₀ with
      | error e => rw [hstep] at h; exact nomatch h
      | ok env₂ => ?_
      rw [hstep] at h
      obtain ⟨m₂, hinv₂, hIB₂, ciH, rfl, hfreshH, hnameH⟩ :=
        checkProjFn_sound hstep m hinv hIB hTblock hbshape hpinsT
          hCblock hFields
      have hTneH : T ≠ ciH.name := by
        intro he
        have hsh := hbshape T hTblock
        rw [he, hnameH] at hsh
        rw [show (projFnName T i₀).isProjFnShape = true from rfl] at hsh
        exact nomatch hsh
      have hTdown : ∀ cvT capsT,
          (⟨ciH :: env'.consts⟩ : Env).find? T =
            some (.indInfo cvT capsT) →
          env'.find? T = some (.indInfo cvT capsT) := by
        intro cvT capsT hf
        rw [Env.find?_cons, if_neg (fun hh => hTneH hh.symm)] at hf
        exact hf
      refine checkProjFold_sound hTblock hbshape rest _ env₁ h m₂ hinv₂
        hIB₂ ?_ ?_ ?_
      · intro cvT capsT hf
        exact EtaPins.step (hpinsT cvT capsT (hTdown cvT capsT hf))
          hfreshH
      · intro cvT capsT hf
        exact hCblock cvT capsT (hTdown cvT capsT hf)
      · intro cvT capsT hf
        exact hFields cvT capsT (hTdown cvT capsT hf)
    · rw [if_neg hm] at h
      simp only [pure, Except.pure, Except.bind] at h
      exact checkProjFold_sound hTblock hbshape rest env' env₁ h m hinv
        hIB hpinsT hCblock hFields

/-- The elimination-template fold preserves having a model: each
installed entry is fresh (runtime-checked) and semantically inert. -/
theorem installProjTemplates_sound {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM
      (installProjTemplateStep (m := CheckM) T ctorName lps nP nF)
      env' = .ok env₁ →
    ∀ _ : EnvModel V env', Nonempty (EnvModel V env₁)
  | [], env', env₁, h, m => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m⟩
  | i₀ :: rest, env', env₁, h, m => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : installProjTemplateStep (m := CheckM) T ctorName lps
        nP nF env' i₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₂ =>
      rw [hstep] at h
      have hnext : Nonempty (EnvModel V env₂) := by
        revert hstep
        unfold installProjTemplateStep installProjTemplate
        split
        case isFalse =>
          intro hstep
          simp only [pure, Except.pure, Except.ok.injEq] at hstep
          exact ⟨hstep ▸ m⟩
        case isTrue hfree =>
          split
          case h_2 =>
            intro hstep
            simp only [pure, Except.pure, Except.ok.injEq] at hstep
            exact ⟨hstep ▸ m⟩
          case h_1 cvR mI2 rP2 rule heqR =>
            split
            case isFalse =>
              intro hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              exact ⟨hstep ▸ m⟩
            case isTrue hcond =>
              intro hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              obtain ⟨m₂, -, -⟩ := extend_proj_template m
                ⟨T, i₀, lps, nP, ctorName, nF, .sort .zero, .zero,
                  .zero, false,
                  decide (cvR.levelParams.length = lps.length + 1)⟩
                rfl rfl (Option.isNone_iff_eq_none.mp hcond.1)
              exact ⟨hstep ▸ m₂⟩
      obtain ⟨m₂⟩ := hnext
      exact installProjTemplates_sound rest env₂ env₁ h m₂

end Setlec
