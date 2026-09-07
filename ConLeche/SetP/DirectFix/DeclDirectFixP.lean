import ConLeche.SetP.DirectFix.FixAssemblyKitP
import ConLeche.SetP.DirectFix.FixStageTableP
import ConLeche.SetP.DirectFix.FixZeroFieldP
import ConLeche.Semantics.Direct.DeclDirectFix
import ConLeche.Verify.Direct.FixParts

/-!
# The direct recursive install, assembled (task #188)

`declDirectFixP`: the P carrier survives the direct recursive
install's run (`DeclDirectFixRun`).  The stages: the former twice —
first the sum route's stage with the empty chain list, a carrier at
which the constructors' recursive data (`fixCtorFuns_of`) and the
former's index telescope (`idxOk_of`, `idxValid_of`) are read; then
the fixed-point stage (`stageFixFormer`) over the X-chains of that
data (`xChainsOk_of`), the leaf's fields `Fss₀` — the constructors
in order (`ctorsLoopGen`, the fibre fold from the fixed-point leaf
through `fixLeafApp` and `fixFamI_app_eq_sum`, the invariant carrying
every constructor's recursive data across the conses), and the
recursor (`stageFixRec`).  The data at the real former is identified
with the data at the dummy former except at the recursive fields
(`fixCtorDataI_ident`), whose real readings are the family at the
index tuple (`chainRealI_of`): the real chains `ChainsRealI` against
the leaf's.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AVExpr)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps DirectSumParts
  DirectFixParts BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Kit -/

/-- A fitting spine's prefix fits the fields' prefix. -/
theorem spineFit_take {Fs : List AVExpr} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i ≤ Fs.length) :
    SpineFit ρ (Fs.take i) (as.take i) := by
  have h' : SpineFit ρ (Fs.take i ++ Fs.drop i) as := by rw [List.take_append_drop]; exact h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_inv h'
  have hl : as₁.length = i := by
    rw [h1.length_eq, List.length_take]; exact Nat.min_eq_left hi
  have : as.take i = as₁ := by
    rw [heq, List.take_append, List.take_of_length_le (Nat.le_of_eq hl), hl, Nat.sub_self,
      List.take_zero, List.append_nil]
  rw [this]
  exact h1

/-! ## The assembly -/

set_option maxHeartbeats 25600000 in
/-- **The P carrier survives a direct recursive install.** -/
theorem declDirectFixP (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : DirectFixParts} (mp : EnvS2PM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.directFixParts? block = some p₀)
    (h : ConLeche.Semantics.DeclDirectFixRun μ F env p₀ env₂) : Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨hneg, hnd₀, cvTa, env₁, p₁, p, ctorsA, sortss, cvRa, rhss, tfvs, trest, isorts, hInd, rfl,
    hwl, hopT2, hsorts, hCtors, hFOk, hRec, hTbl⟩ := h
  obtain ⟨hshape, -, hlenK₀⟩ := ConLeche.directFixParts?_inv hdp
  obtain ⟨-, hRname₀, hClps₀, hresT₀, hresR₀, helimR₀, hRlps₀, -, -⟩ :=
    ConLeche.directFixShape?_inv hshape
  -- the former: its run completed the record with the sort it read
  -- (task #195; task #210 Part B: on this route too) — every later
  -- stage runs on the completed record `p`, and the recogniser's
  -- invariants transport to it by the completion's projections
  obtain ⟨cvT, s, hTname₀₀, hTlps₀₀, hccvT, rfl, rfl, bsT, hstripT₀⟩ :=
    ConLeche.checkDirectSumInd_shape hInd
  try dsimp only at hCtors hRec hTbl hFOk hsorts hopT2 hwl
  have hpT : (p₀.complete (p₀.toDirectSumParts.withSort s)).cvT = p₀.cvT := by simp
  have hpC : (p₀.complete (p₀.toDirectSumParts.withSort s)).ctors = p₀.ctors := by simp
  have hpK : (p₀.complete (p₀.toDirectSumParts.withSort s)).kinds = p₀.kinds := by simp
  have hpP : (p₀.complete (p₀.toDirectSumParts.withSort s)).nP = p₀.nP := by simp
  have hpI : (p₀.complete (p₀.toDirectSumParts.withSort s)).nIdx = p₀.nIdx := by simp
  have hpR : (p₀.complete (p₀.toDirectSumParts.withSort s)).cvR = p₀.cvR := by simp
  have hpE : (p₀.complete (p₀.toDirectSumParts.withSort s)).elim = p₀.elim := by simp
  have hpL : (p₀.complete (p₀.toDirectSumParts.withSort s)).large = p₀.large := by simp
  have hpS : (p₀.complete (p₀.toDirectSumParts.withSort s)).resSort = s := by simp
  have hpProp : (p₀.complete (p₀.toDirectSumParts.withSort s)).isProp
      = (Level.isEquiv (p₀.complete (p₀.toDirectSumParts.withSort s)).resSort .zero
          == some true) := by simp
  generalize hp : p₀.complete (p₀.toDirectSumParts.withSort s) = p at hCtors hRec hTbl hFOk hsorts hopT2 hwl hpT hpC hpK hpP hpI hpR hpE hpL hpS hpProp
  have hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true) := hpProp
  have hnd : (p.ctors.map (·.1.name)).Nodup := by rw [hpC]; exact hnd₀
  have hlenK : p.kinds.length = p.ctors.length := by rw [hpK, hpC]; exact hlenK₀
  have hClps : ∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      ConLeche.reservedBasisNames.contains c.1.name = false := by rw [hpC, hpT]; exact hClps₀
  have helimR : p.large = true → p.elim ∈ p.cvR.levelParams := by
    rw [hpL, hpE, hpR]; exact helimR₀
  have hRlps : ∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams := by rw [hpT, hpR]; exact hRlps₀
  have hRname : p.cvR.name = p.cvT.name.str "rec" := by rw [hpR, hpT]; exact hRname₀
  have hresT : ConLeche.reservedBasisNames.contains p.cvT.name = false := by
    rw [hpT]; exact hresT₀
  have hresR : ConLeche.reservedBasisNames.contains p.cvR.name = false := by
    rw [hpR]; exact hresR₀
  have hTname₀ : cvT.name = p.cvT.name := by rw [hpT]; exact hTname₀₀
  have hTlps₀ : cvT.levelParams = p.cvT.levelParams := by rw [hpT]; exact hTlps₀₀
  have hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort) := by
    rw [hpP, hpI, hpS]; exact hstripT₀
  obtain ⟨hfindT, -, hpshapeT, -, -, -, typeT, -, -, -, -, htrT, -, -, htyT⟩ :=
    ConLeche.checkConstantVal_inv hccvT
  have hTname : cvTa.name = p.cvT.name := by rw [htyT]; exact hTname₀
  have hlpsT : cvTa.levelParams = p.cvT.levelParams := by rw [htyT]; exact hTlps₀
  have hTtype : cvTa.type = typeT := by rw [htyT]
  obtain ⟨ppsAll, hFD⟩ := formerData_of hμ mp hccvT hstripT
  have hTfresh : env.find? cvTa.name = none := by rw [hTname, ← hTname₀]; exact hfindT
  have hTfresh' : env.find? p.cvT.name = none := by rw [← hTname₀]; exact hfindT
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (by rw [hTtype]; exact htrT)
  have hfT_I : (⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩ : Env).find?
      p.cvT.name = some (.indInfo cvTa (ConLeche.directFixCaps p)) := by
    rw [← hTname]; exact ConLeche.Env.find?_cons_self _ _
  have hProp' : p.isProp = true → (Level.isEquiv p.resSort .zero == some true) = true :=
    fun h => by rw [← hProp]; exact h
  obtain ⟨tfvsP, trestP, hopT⟩ := openPisAtFvars_of_stripPis_isSome p.nP 0
    (ConLeche.stripPis_isSome_of_le (Nat.le_add_right _ _) (by rw [hstripT]; rfl))
  have hE_I : ConLeche.EtaFamiliesClosedExcept
      ⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩ p.cvT.name :=
    (hE.except _).cons hTfresh (fun cv caps heq _ => Or.inr (by
      obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj heq
      exact hTname))
  -- the constructors' runs
  obtain ⟨hlenA, hlenS, hall⟩ := ConLeche.checkDirectSumCtors_inv hCtors
  have hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ c : ConstantVal × Nat, p.ctors[j]? = some c ∧
      cA.1.name = c.1.name ∧ cA.1.levelParams = p.cvT.levelParams ∧
      (⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩ : Env).find?
        cA.1.name = none ∧
      cA.1.type.constsResolve
        ⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩ = true ∧
      cA.1.name.isProjFnShape = false ∧
      ∃ sorts : List Level, sortss[j]? = some sorts ∧
      ConLeche.checkDirectSumCtor (ConLeche.fueledOps μ F)
        ⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩
        ⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩
        p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large c.1 cA.2 cvTa
        = .ok (cA.1, sorts) := by
    intro j cA hj
    have hjl : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; omega
    obtain ⟨hnF, sorts, hsj, hCtor⟩ := hall j (p.ctors[j]) cA (List.getElem?_eq_getElem hjl) hj
    rw [← hnF] at hCtor
    obtain ⟨hccvC, -, -⟩ := ConLeche.checkDirectSumCtor_shape hCtor
    obtain ⟨hfindC, -, hpshapeC, -, -, -, typeC, -, -, -, -, htrC, -, -, htyC⟩ :=
      ConLeche.checkConstantVal_inv hccvC
    refine ⟨p.ctors[j], List.getElem?_eq_getElem hjl, by rw [htyC], ?_, ?_, ?_,
      by rw [htyC]; exact hpshapeC, sorts, hsj, hCtor⟩
    · rw [htyC]
      exact (hClps _ (List.getElem_mem hjl)).1
    · show Env.find? _ cA.1.name = none
      rw [htyC]; exact hfindC
    · show Expr.constsResolve _ cA.1.type = true
      rw [htyC]; exact htrC
  have hrunOf' : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ (c : ConstantVal × Nat) (sorts : List Level),
        ConLeche.checkDirectSumCtor (ConLeche.fueledOps μ F)
          ⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩
          ⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩
          p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large c.1 cA.2 cvTa
          = .ok (cA.1, sorts) := by
    intro j cA hj
    obtain ⟨c, -, -, -, -, -, -, sorts, -, hCtor⟩ := hrunOf j cA hj
    exact ⟨c, sorts, hCtor⟩
  have hndA : (ctorsA.map (·.1.name)).Nodup := by
    have heq : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_map, List.getElem?_map]
      cases hi : ctorsA[i]? with
      | none =>
        have : p.ctors[i]? = none := by
          rw [List.getElem?_eq_none_iff] at hi ⊢; omega
        rw [this]
      | some cA =>
        obtain ⟨c, hc, hname, -⟩ := hrunOf i cA hi
        rw [hc]
        simp [hname]
    rw [heq]; exact hnd
  have hlenK' : p.kinds.length = ctorsA.length := by rw [hlenK, hlenA]
  -- names
  let ksF : Nat → List RecFieldKind := fun j => p.kinds.getD j []
  have hks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i) := by
    intro i hi
    show p.kinds[i]? = some (p.kinds.getD i [])
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  let rss : List (List Bool) := rssOfK ksF ctorsA.length
  have hrss : ∀ j, j < ctorsA.length → rss.getD j [] = rsOf (ksF j) := fun j hj => rssOfK_getD hj
  let Ids : (Name → Nat) → List AVExpr := fun ψ => ((ppsAll ψ).drop p.nP).map (·.2.2)
  have hlenIds : ∀ ψ, (Ids ψ).length = p.nIdx := by
    intro ψ; simp [Ids, hFD.len ψ]
  have hlenPps : ∀ ψ, (ppsAll ψ).length = p.nP + (Ids ψ).length := by
    intro ψ; rw [hlenIds, hFD.len ψ]
  have hIdsBelow : ∀ ψ, FieldsBelow p.nP (Ids ψ) := by
    intro ψ
    have := (DomsBelow.drop p.nP (hFD.below ψ)).fields
    rwa [Nat.zero_add] at this
  let uAV : (Name → Nat) → Nat := fun ψ => idxUniv (restrictΨ p.cvT.levelParams ψ) isorts
  have hUparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
      uAV ψ₁ = uAV ψ₂ := by
    intro ψ₁ ψ₂ hφ
    show idxUniv (restrictΨ p.cvT.levelParams ψ₁) isorts = idxUniv (restrictΨ p.cvT.levelParams ψ₂) isorts
    rw [restrictΨ_congr hφ]
  have hppsR : ∀ ψ, ppsAll (restrictΨ p.cvT.levelParams ψ) = ppsAll ψ := by
    intro ψ
    exact (hFD.params _ _ fun q hq => restrictΨ_agree _ _ q (by rw [← hlpsT]; exact hq)).1
  -- THE BLOCK'S CAPABILITY LAWS (task #210 Parts A and B): η is
  -- claimed only at a constructor with a field, and its premise — the
  -- projection-function family stored — fails below and at the table's
  -- environment (the table keeps the family free); unit-likeness is
  -- claimed at one fieldless index-free constructor, where the family
  -- at its parameters is the one tagged empty tuple (`FixZeroFieldP`)
  have hnFc : ∀ (j : Nat) (cA c : ConstantVal × Nat), ctorsA[j]? = some cA →
      p.ctors[j]? = some c → cA.2 = c.2 :=
    fun j cA c hj hc => (hall j c cA hc hj).1
  have hfreshFam : (ConLeche.directFixCaps p).eta = true →
      (⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (ConLeche.directSumRules p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (ConLeche.consSumCtors p.nP ctorsA
          ⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩).consts⟩ : Env).find?
        (projFnName p.cvT.name 0) = none :=
    fixTableFamFree hTbl hlenA hlenS
      (fun cA c hA hc => hnFc 0 cA c (by rw [hA]; rfl) (by rw [hc]; rfl))
  have hfreshFam₁ : (ConLeche.directFixCaps p).eta = true →
      (⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩ : Env).find?
        (projFnName p.cvT.name 0) = none :=
    fun he => ConLeche.consSumCtors_find?_none (find?_none_of_cons (hfreshFam he))
  have hunitOf : (ConLeche.directFixCaps p).unitlike = true →
      ∃ c, p.ctors = [c] ∧ p.nIdx = 0 ∧ c.2 = 0 := by
    intro hu
    unfold ConLeche.directFixCaps at hu
    split at hu
    · next c hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hu
      exact ⟨c, hc, hu.1, hu.2⟩
    · exact nomatch hu
  have hunitParams : ∀ ψ, (ConLeche.directFixCaps p).unitlike = true →
      (ConLeche.directFixCaps p).unitParams = (ppsAll ψ).length := by
    intro ψ hu
    obtain ⟨c, hc, hI, -⟩ := hunitOf hu
    rw [ConLeche.directFixCaps_single hc]
    show p.nP = (ppsAll ψ).length
    rw [hFD.len ψ, hI, Nat.add_zero]
  have hetaUnit : (ConLeche.directFixCaps p).unitlike = true →
      (ConLeche.directFixCaps p).eta = true → False := by
    intro hu he
    obtain ⟨c, hc, -, hz⟩ := hunitOf hu
    rw [ConLeche.directFixCaps_single hc] at he
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at he
    exact he.1.2 hz
  -- the laws at the dummy former's leaf (the family is empty)
  have hcapsLaws₀ : ∀ {env' : Env} (m' : EnvS2Core V env'),
      ((ConLeche.directFixCaps p).eta = true →
        env'.find? (projFnName p.cvT.name 0) = none) →
      FormerData m' cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, m'.acval p.cvT.name ψ = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ) []) →
      CapsLawsAt m' p.cvT.name cvTa (ConLeche.directFixCaps p) := by
    intro env' m' hfr hFD' hleaf
    by_cases hu : (ConLeche.directFixCaps p).unitlike = true
    · refine ⟨fun he _ => absurd he (hetaUnit hu), fun _ φ' => ?_⟩
      exact fixEmptyUnitLaw hleaf hFD'.read hFD'.okTy (fun ψ => hunitParams ψ hu)
    · exact fixCapsLawsAt_vacuous m' (by simpa using hu) hfr
  -- the dummy former: the constructors' readings and the index
  -- telescope need a carrier storing the former
  obtain ⟨mpI₀, hacI₀⟩ := stageSumFormer mp hE hccvT hTname₀ hFD (fun _ => []) (fun _ _ _ => rfl)
    (fun _ _ h => nomatch h) (fun _ _ _ => ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩)
    (ConLeche.directFixCaps p)
    (fun m₂ hac => by
      rw [hTname]
      exact hcapsLaws₀ m₂ hfreshFam₁
        (hFD.cross (c₀ := .indInfo cvTa (ConLeche.directFixCaps p)) hTfresh
          (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT m₂ hac)
        (fun ψ => by rw [hac, ← hTname]; exact congrFun acvalWith_self ψ))
  have hFD_I₀ : FormerData mpI₀.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll :=
    hFD.cross (c₀ := .indInfo cvTa (ConLeche.directFixCaps p)) hTfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT mpI₀.base2 hacI₀
  have hleafT₀ : ∀ ψ, ∃ B, mpI₀.base2.acval p.cvT.name ψ
      = mkLamsC (p.resSort.eval ψ + 1) (ppsAll ψ) B := by
    intro ψ
    rw [hacI₀, ← hTname, acvalWith_self]
    exact ⟨_, rfl⟩
  -- the index telescope
  have hIdx : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      IdxOk (uAV ψ) ρp (Ids ψ) ∧ FieldsValid ρp (Ids ψ) := by
    intro ψ ρp hρp
    refine ⟨?_, idxValid_of mpI₀ hfT_I hopT2 hFD_I₀ ψ ρp hρp⟩
    have := idxOk_of hμ mpI₀ hfT_I hopT2 hsorts hFD_I₀ (restrictΨ p.cvT.levelParams ψ) ρp
      (by rw [hppsR]; exact hρp)
    rw [hppsR] at this
    exact this
  -- the constructors' data at the dummy former
  obtain ⟨idxF₀, dsF₀, esF₀, srcsF₀, fvsPF₀, xFvsF₀, xrestF₀, eissF₀, tssF₀, hcf₀⟩ :=
    fixCtorFuns_of hμ mpI₀ hfT_I hlpsT hstripT hFOk hrunOf'
  let Fss₀ : (Name → Nat) → List (List AVExpr) :=
    fun ψ => fssOfR p.nP (fixCtorDataList dsF₀ esF₀ ksF eissF₀ tssF₀ ψ ctorsA 0)
  let Ess₀ : (Name → Nat) → List (List AVExpr) :=
    fun ψ => essOfR (fixCtorDataList dsF₀ esF₀ ksF eissF₀ tssF₀ ψ ctorsA 0)
  let Eiss₀ : (Name → Nat) → List (List (List AVExpr)) :=
    fun ψ => eissOfR (fixCtorDataList dsF₀ esF₀ ksF eissF₀ tssF₀ ψ ctorsA 0)
  let Tlss₀ : (Name → Nat) → List (List (List (Nat × Nat × AVExpr))) :=
    fun ψ => tlssOfR (fixCtorDataList dsF₀ esF₀ ksF eissF₀ tssF₀ ψ ctorsA 0)
  have hFss₀D : ∀ ψ j cA, ctorsA[j]? = some cA →
      (Fss₀ ψ).getD j [] = ((dsF₀ j ψ).drop p.nP).map (·.2.2) :=
    fun ψ j cA hj => fssOfR_fixCtorDataList_getD hj
  have hEss₀D : ∀ ψ j cA, ctorsA[j]? = some cA → (Ess₀ ψ).getD j [] = esF₀ j ψ :=
    fun ψ j cA hj => essOfR_fixCtorDataList_getD hj
  have hEiss₀D : ∀ ψ j cA, ctorsA[j]? = some cA → (Eiss₀ ψ).getD j [] = eissF₀ j ψ :=
    fun ψ j cA hj => eissOfR_fixCtorDataList_getD hj
  have hlenFss₀ : ∀ ψ, (Fss₀ ψ).length = ctorsA.length := by
    intro ψ; show (fssOfR _ _).length = _; rw [fssOfR_length, fixCtorDataList_length]
  have hlenEss₀ : ∀ ψ, (Ess₀ ψ).length = ctorsA.length := by
    intro ψ; show (essOfR _).length = _; rw [essOfR_length, fixCtorDataList_length]
  have hlenEiss₀ : ∀ ψ, (Eiss₀ ψ).length = ctorsA.length := by
    intro ψ; show (eissOfR _).length = _; rw [eissOfR_length, fixCtorDataList_length]
  have hlenFs₀ : ∀ ψ j cA, ctorsA[j]? = some cA → ((Fss₀ ψ).getD j []).length = cA.2 := by
    intro ψ j cA hj
    rw [hFss₀D ψ j cA hj]
    simp [(hcf₀ j cA hj).len ψ]
  have hksLen : ∀ j cA, ctorsA[j]? = some cA → (ksF j).length = cA.2 :=
    fun j cA hj => (hcf₀ j cA hj).ksLen
  -- the chain facts at the dummy former
  have hC₀ : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      ChainFacts (uAV ψ) (p.resSort.eval ψ) p.nP cA.2 ρp (Ids ψ) (ksF j) (tssF₀ j ψ)
        (((dsF₀ j ψ).drop p.nP).map (·.2.2)) (eissF₀ j ψ) (esF₀ j ψ) ∧
      ChainValidFacts p.nP cA.2 ρp (ksF j) (tssF₀ j ψ) (((dsF₀ j ψ).drop p.nP).map (·.2.2))
        (eissF₀ j ψ) (esF₀ j ψ) := by
    intro j cA hj ψ ρp hρp
    obtain ⟨c, -, -, -, -, -, -, _, -, hCtor⟩ := hrunOf j cA hj
    exact ⟨fixChainFacts_of hμ mpI₀ hCtor hfT_I hProp' hFD_I₀ hleafT₀ (hcf₀ j cA hj) (uAV ψ) ψ ρp hρp,
      fixChainValidFacts_of hμ mpI₀ hCtor hfT_I hProp' hFD_I₀ hleafT₀ (hcf₀ j cA hj) ψ ρp hρp⟩
  have hTlss₀D : ∀ ψ j cA, ctorsA[j]? = some cA → (Tlss₀ ψ).getD j [] = tssF₀ j ψ :=
    fun ψ j cA hj => tlssOfR_fixCtorDataList_getD hj
  have hTlss₀None : ∀ ψ j, ¬ j < ctorsA.length → (Tlss₀ ψ).getD j [] = [] := by
    intro ψ j hj
    show (tlssOfR _).getD j [] = []
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [tlssOfR_length, fixCtorDataList_length]; omega)]
    rfl
  have hX₀ : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ) ∧
      ∀ X, X ∈ˢ lfpFamSpace V (p.resSort.eval ψ) (idxSet (uAV ψ) ρp (Ids ψ)) →
        ∀ t, t ∈ˢ idxSet (uAV ψ) ρp (Ids ψ) →
        SumFieldsValid (cons t (cons X ρp))
          (chainsXI (uAV ψ) (Ids ψ) (Ids ψ).length rss (Tlss₀ ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ)) := by
    intro ψ ρp hρp
    refine xChainsOk_of (nP := p.nP) (hIdx ψ ρp hρp).1 (hIdx ψ ρp hρp).2 (hlenFss₀ ψ) hrss
      ?_ ?_
    · intro j hj
      obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hlenFs₀ ψ j cA hjA, hFss₀D ψ j cA hjA, hEss₀D ψ j cA hjA, hEiss₀D ψ j cA hjA,
        hTlss₀D ψ j cA hjA]
      exact (hC₀ j cA hjA ψ ρp hρp).1
    · intro j hj
      obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hlenFs₀ ψ j cA hjA, hFss₀D ψ j cA hjA, hEss₀D ψ j cA hjA, hEiss₀D ψ j cA hjA,
        hTlss₀D ψ j cA hjA]
      exact (hC₀ j cA hjA ψ ρp hρp).2
  let leafT : (Name → Nat) → AVExpr := fun ψ =>
    directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ)
  -- the laws at the fixpoint leaf: unit-likeness (one fieldless
  -- index-free constructor) folds the leaf to the one tagged empty
  -- tuple (`FixZeroFieldP`); η stays vacuous by the family's freshness
  have hcapsLaws : ∀ {env' : Env} (m' : EnvS2Core V env'),
      ((ConLeche.directFixCaps p).eta = true →
        env'.find? (projFnName p.cvT.name 0) = none) →
      FormerData m' cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, m'.acval p.cvT.name ψ = leafT ψ) →
      CapsLawsAt m' p.cvT.name cvTa (ConLeche.directFixCaps p) := by
    intro env' m' hfr hFD' hleaf
    by_cases hu : (ConLeche.directFixCaps p).unitlike = true
    · refine ⟨fun he _ => absurd he (hetaUnit hu), fun _ φ' => ?_⟩
      obtain ⟨c, hc, hI, hz⟩ := hunitOf hu
      obtain ⟨cA, hA⟩ := List.length_eq_one_iff.mp (by rw [hlenA, hc]; rfl : ctorsA.length = 1)
      have h0 : ctorsA[0]? = some cA := by rw [hA]; rfl
      have hzA : cA.2 = 0 := by
        rw [hnFc 0 cA c h0 (by rw [hc]; rfl)]; exact hz
      have hIds0 : ∀ ψ, Ids ψ = [] := fun ψ =>
        List.length_eq_zero_iff.mp (by rw [hlenIds, hI])
      have hFss0 : ∀ ψ, Fss₀ ψ = [[]] := by
        intro ψ
        obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp (by rw [hlenFss₀, hA]; rfl : (Fss₀ ψ).length = 1)
        have := hlenFs₀ ψ 0 cA h0
        rw [hFs, hzA] at this
        simp only [List.getD_cons_zero] at this
        rw [hFs, List.length_eq_zero_iff.mp this]
      have hEss0 : ∀ ψ, Ess₀ ψ = [[]] := by
        intro ψ
        obtain ⟨Es, hEs⟩ := List.length_eq_one_iff.mp (by rw [hlenEss₀, hA]; rfl : (Ess₀ ψ).length = 1)
        have hE0 : Es = esF₀ 0 ψ := by
          have := hEss₀D ψ 0 cA h0
          rwa [hEs] at this
        have hlen : (esF₀ 0 ψ).length = 0 := by
          have := (hcf₀ 0 cA h0).lenE ψ
          rwa [hI] at this
        rw [hEs, hE0, List.length_eq_zero_iff.mp hlen]
      have hleaf' : ∀ ψ, m'.acval p.cvT.name ψ
          = directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) [] rss (Tlss₀ ψ) (Eiss₀ ψ)
              (Fss₀ ψ) (Ess₀ ψ) := by
        intro ψ; rw [hleaf ψ]; show directFixTyAVI _ _ _ (Ids ψ) _ _ _ _ _ = _; rw [hIds0]
      refine fixFibreUnitLaw (u := uAV) (w := fun ψ => p.resSort.eval ψ) (rss := rss)
        (tlss := Tlss₀) (eiss := Eiss₀) (Fss₀ := Fss₀) (Ess := Ess₀) hleaf' ?_ hFD'.read hFD'.okTy
        (fun ψ => hunitParams ψ hu)
      intro ψ ρ ts hsp
      have hlenP : (ppsAll ψ).length = p.nP := by rw [hFD.len ψ, hI, Nat.add_zero]
      have hρp : Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse (consList ts ρ) := by
        rw [List.take_of_length_le (Nat.le_of_eq hlenP)]
        simpa using sat2_of_spineFit (Sat2_nil V ρ) hsp
      have hX := (hX₀ ψ (consList ts ρ) hρp).1
      rw [hIds0] at hX
      refine fixFoldSingle (Fs := []) hlenP (hEss0 ψ) hsp hX ?_
      rw [hFss0, hEss0]
      exact chainsRealI_zero
    · exact fixCapsLawsAt_vacuous m' (by simpa using hu) hfr
  -- the real former
  have hlpsA : ∀ cA ∈ ctorsA, cA.1.levelParams = p.cvT.levelParams := by
    intro cA hcA
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨-, -, -, hlps, -, -, -, -, -, -⟩ := hrunOf j cA hj
    exact hlps
  have hcds₀Params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) →
      fixCtorDataList dsF₀ esF₀ ksF eissF₀ tssF₀ ψ₁ ctorsA 0
        = fixCtorDataList dsF₀ esF₀ ksF eissF₀ tssF₀ ψ₂ ctorsA 0 := by
    intro ψ₁ ψ₂ hφ
    refine fixCtorDataList_congr ctorsA 0 fun i hi => ?_
    rw [Nat.zero_add]
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    have hlpsi := hlpsA cAi (List.mem_of_getElem? hi')
    have hφ' : ∀ q ∈ cAi.1.levelParams, ψ₁ q = ψ₂ q := fun q hq =>
      hφ q (by rw [hlpsT, ← hlpsi]; exact hq)
    obtain ⟨h1, h2⟩ := (hcf₀ i cAi hi').params ψ₁ ψ₂ hφ'
    exact ⟨h1, h2, (hcf₀ i cAi hi').eissParams ψ₁ ψ₂ hφ', (hcf₀ i cAi hi').tssParams ψ₁ ψ₂ hφ'⟩
  obtain ⟨mpI, hacI⟩ := stageFixFormer mp hE hccvT hTname₀ hFD uAV rss Tlss₀ Eiss₀ Fss₀ Ess₀
    (fun ψ₁ ψ₂ hφ => by
      refine ⟨hUparams ψ₁ ψ₂ (fun q hq => hφ q (by rw [hlpsT]; exact hq)), ?_, ?_, ?_, ?_⟩
      · show tlssOfR _ = tlssOfR _; rw [hcds₀Params ψ₁ ψ₂ hφ]
      · show eissOfR _ = eissOfR _; rw [hcds₀Params ψ₁ ψ₂ hφ]
      · show fssOfR _ _ = fssOfR _ _; rw [hcds₀Params ψ₁ ψ₂ hφ]
      · show essOfR _ = essOfR _; rw [hcds₀Params ψ₁ ψ₂ hφ])
    (fun ψ => by
      refine chainsXI_below_of (n := ctorsA.length) (hIdsBelow ψ) (hlenFss₀ ψ) ?_ ?_ ?_ ?_ ?_
      · intro j hj i
        obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hTlss₀D ψ j cA hjA]
        exact (hcf₀ j cA hjA).tssBelow ψ i
      · intro j hj i E hE
        obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hEiss₀D ψ j cA hjA] at hE
        rw [hTlss₀D ψ j cA hjA]
        exact (hcf₀ j cA hjA).eissBelow ψ i E hE
      · intro j hj
        obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hFss₀D ψ j cA hjA]
        have := (DomsBelow.drop p.nP ((hcf₀ j cA hjA).below ψ)).fields
        rwa [Nat.zero_add] at this
      · intro j hj
        obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hEss₀D ψ j cA hjA]
        exact (hcf₀ j cA hjA).lenE ψ
      · intro j hj E hE
        obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hEss₀D ψ j cA hjA] at hE
        rw [hlenFs₀ ψ j cA hjA]
        exact (hcf₀ j cA hjA).belowE ψ E hE)
    hIdx (fun ψ ρp hρp => (hX₀ ψ ρp hρp).1) (fun ψ ρp hρp => (hX₀ ψ ρp hρp).2)
    (ConLeche.directFixCaps p)
    (fun m₂ hac => by
      rw [hTname]
      exact hcapsLaws m₂ hfreshFam₁
        (hFD.cross (c₀ := .indInfo cvTa (ConLeche.directFixCaps p)) hTfresh
          (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT m₂ hac)
        (fun ψ => by rw [hac, ← hTname]; exact congrFun acvalWith_self ψ))
  have hacI' : mpI.base2.acval = acvalWith mp.base2.acval p.cvT.name
      (fun ψ => directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ) (Fss₀ ψ)
        (Ess₀ ψ)) := by
    rw [hacI, hTname]
  have hacI₀' : mpI₀.base2.acval = acvalWith mp.base2.acval p.cvT.name
      (fun ψ => directSumTyAV (p.resSort.eval ψ) (ppsAll ψ) []) := by
    rw [hacI₀, hTname]
  have hleafT_I : ∀ ψ, mpI.base2.acval p.cvT.name ψ
      = directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ) (Fss₀ ψ)
          (Ess₀ ψ) := by
    intro ψ
    rw [hacI', acvalWith_self]
  have hleafT_I' : ∀ ψ, ∃ B, mpI.base2.acval p.cvT.name ψ
      = mkLamsC (p.resSort.eval ψ + 1) (ppsAll ψ) B := by
    intro ψ
    rw [hleafT_I ψ]
    exact ⟨_, rfl⟩
  have hleafClosed : ∀ ψ, VExpr.bvarsBelow 0 (directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ)
      (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ)).erase := by
    intro ψ
    have := mpI.base2.cval_closedL p.cvT.name ψ
    rwa [hleafT_I ψ] at this
  have hFD_I : FormerData mpI.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll :=
    hFD.cross (c₀ := .indInfo cvTa (ConLeche.directFixCaps p)) hTfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT mpI.base2 hacI
  -- the constructors' data at the real former, identified with the
  -- dummy former's except at the recursive fields
  obtain ⟨idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, hcf⟩ :=
    fixCtorFuns_of hμ mpI hfT_I hlpsT hstripT hFOk hrunOf'
  have hident : ∀ j cA, ctorsA[j]? = some cA →
      idxF j = idxF₀ j ∧ (∀ ψ, esF j ψ = esF₀ j ψ) ∧ (∀ ψ, eissF j ψ = eissF₀ j ψ) ∧
      (∀ ψ, tssF j ψ = tssF₀ j ψ) ∧
      ∀ ψ i, i < cA.2 → (ksF j).getD i .ordinary ≠ .recursive →
        (ksF j).getD i .ordinary ≠ .reflexive →
        ((dsF j ψ).getD (p.nP + i) default).2.2 = ((dsF₀ j ψ).getD (p.nP + i) default).2.2 := by
    intro j cA hj
    obtain ⟨h1, -, -, -, h5, h6, h7, h8⟩ := fixCtorDataI_ident hacI' hacI₀' hTfresh' (hcf j cA hj)
      (hcf₀ j cA hj)
    exact ⟨h1, h5, h6, h7, h8⟩
  have hEss : ∀ ψ, essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) = Ess₀ ψ := by
    intro ψ
    refine essOfR_fixCtorDataList_congr ctorsA 0 fun i hi => ?_
    rw [Nat.zero_add]
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    exact (hident i cAi hi').2.1 ψ
  have hTlss : ∀ ψ, tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) = Tlss₀ ψ := by
    intro ψ
    refine tlssOfR_fixCtorDataList_congr ctorsA 0 fun i hi => ?_
    rw [Nat.zero_add]
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    exact (hident i cAi hi').2.2.2.1 ψ
  have hEiss : ∀ ψ, eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) = Eiss₀ ψ := by
    intro ψ
    refine eissOfR_fixCtorDataList_congr ctorsA 0 fun i hi => ?_
    rw [Nat.zero_add]
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    exact (hident i cAi hi').2.2.1 ψ
  let Fss : (Name → Nat) → List (List AVExpr) :=
    fun ψ => fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)
  have hFssD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (Fss ψ).getD j [] = ((dsF j ψ).drop p.nP).map (·.2.2) :=
    fun ψ j cA hj => fssOfR_fixCtorDataList_getD hj
  have hlenFss : ∀ ψ, (Fss ψ).length = ctorsA.length := by
    intro ψ; show (fssOfR _ _).length = _; rw [fssOfR_length, fixCtorDataList_length]
  have hlenFs : ∀ ψ j cA, ctorsA[j]? = some cA → ((Fss ψ).getD j []).length = cA.2 := by
    intro ψ j cA hj
    rw [hFssD ψ j cA hj]
    simp [(hcf j cA hj).len ψ]
  -- the frames of the real data
  have hframes : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
          Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
          (∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
            (∀ E ∈ esF j ψ, AnnotOkP V (consList bs ρ) E) ∧
            SpineFit ρ (Ids ψ) (idxValsAt ρ (esF j ψ) bs))) := by
    intro j cA hj
    obtain ⟨c, -, -, -, -, -, -, _, -, hCtor⟩ := hrunOf j cA hj
    obtain ⟨hiff, hfields, -⟩ := ctorFramesGen hμ mpI hCtor hfT_I hProp' hFD_I
      (hcf j cA hj).toCtorDataI hleafT_I'
    exact ⟨hiff, fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1, (hfields ψ ρ h).2.2.2⟩⟩
  -- the fields' bounds and sorts at a non-`Prop` family (task #210 Part
  -- A: the projection table's guards at a structure-like block)
  have hsortsOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ sorts : List Level, sortss[j]? = some sorts ∧ sorts.length = cA.2 ∧
      (∀ k, k < cA.2 → p.isProp = false → Level.leq (sorts.getD k .zero) p.resSort = some true) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        (p.isProp = false →
          FieldsBound (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2))) ∧
        ∀ k, k < cA.2 → ∀ as : List V,
          SpineFit ρ ((((dsF j ψ).drop p.nP).map (·.2.2)).take k) as →
          interp2 V (consList as ρ) ((((dsF j ψ).drop p.nP).map (·.2.2)).getD k default)
            ∈ˢ (univ ((sorts.getD k .zero).eval ψ) : V)) := by
    intro j cA hj
    obtain ⟨c, -, -, -, -, -, -, sorts, hsj, hCtor⟩ := hrunOf j cA hj
    obtain ⟨-, hfields, hlenS', hleq, hmem⟩ := ctorFramesGen hμ mpI hCtor hfT_I hProp' hFD_I
      (hcf j cA hj).toCtorDataI hleafT_I'
    exact ⟨sorts, hsj, hlenS', hleq, fun ψ ρ h => ⟨(hfields ψ ρ h).2.2.1, hmem ψ ρ h⟩⟩
  have hC : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      ChainFacts (uAV ψ) (p.resSort.eval ψ) p.nP cA.2 ρp (Ids ψ) (ksF j) (tssF j ψ)
        (((dsF j ψ).drop p.nP).map (·.2.2)) (eissF j ψ) (esF j ψ) := by
    intro j cA hj ψ ρp hρp
    obtain ⟨c, -, -, -, -, -, -, _, -, hCtor⟩ := hrunOf j cA hj
    exact fixChainFacts_of hμ mpI hCtor hfT_I hProp' hFD_I hleafT_I' (hcf j cA hj) (uAV ψ) ψ ρp hρp
  -- the real chains against the leaf's
  have hreal : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (Ids ψ) (Ids ψ).length rss (Tlss₀ ψ) (Eiss₀ ψ)
          (Fss₀ ψ) (Ess₀ ψ)) (uAV ψ) (p.resSort.eval ψ) ρp (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ) (Fss₀ ψ)
        (Fss ψ) (Ess₀ ψ) := by
    intro ψ ρp hρp
    refine ⟨by rw [hlenFss₀, hlenFss], by rw [hlenEss₀, hlenFss], fun j hj => ?_, fun j hj => ?_,
      fun j hj => ?_⟩
    · rw [hlenFss] at hj
      obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hEss₀D ψ j cA hjA, hlenIds]
      exact (hcf₀ j cA hjA).lenE ψ
    · rw [hlenFss] at hj
      obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hlenFs₀ ψ j cA hjA, hlenFs ψ j cA hjA]
    · rw [hlenFss] at hj
      obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hrss j hj, hEiss₀D ψ j cA hjA, hTlss₀D ψ j cA hjA, hFss₀D ψ j cA hjA, hFssD ψ j cA hjA]
      have hC₀j := (hC₀ j cA hjA ψ ρp hρp).1
      have hCj := hC j cA hjA ψ ρp hρp
      have hlenD := (hcf j cA hjA).len ψ
      have hlenD₀ := (hcf₀ j cA hjA).len ψ
      refine chainRealI_of (hIdx ψ ρp hρp).1 hC₀j (by simp [hlenD]) (fun i hi => hCj.nb i hi)
        (fun i hi hnr => ?_) (fun i hi hr as as' hlenA hrel hsp' => ?_)
      · rw [drop_map_getD hlenD hi, drop_map_getD hlenD₀ hi]
        exact (hident j cA hjA).2.2.2.2 ψ i hi
          (fun hk => hnr ⟨Nat.le_add_right _ _, Or.inl (by rwa [Nat.add_sub_cancel_left])⟩)
          (fun hk => hnr ⟨Nat.le_add_right _ _, Or.inr (by rwa [Nat.add_sub_cancel_left])⟩)
      · -- the slot's fit at the real spine (task #202)
        have hnbT : ∀ k d, ((tssF₀ j ψ).getD i [])[k]? = some d →
            NoBVar (exclP (fun q => recAt p.nP (ksF j) q ∧ q < p.nP + as.length)
              (p.nP + as.length + k)) d.2.2 := by
          rw [hlenA]; exact hC₀j.nbT i hi hr
        have hnbE : ∀ E ∈ (eissF₀ j ψ).getD i [],
            NoBVar (exclP (fun q => recAt p.nP (ksF j) q ∧ q < p.nP + as.length)
              (p.nP + as.length + ((tssF₀ j ψ).getD i []).length)) E := by
          rw [hlenA]; exact hC₀j.nbE i hi hr
        have hfitS : SlotFit (uAV ψ) (p.resSort.eval ψ) ρp (Ids ψ) ((tssF₀ j ψ).getD i [])
            ((eissF₀ j ψ).getD i []) as :=
          slotFit_congr_shadow hrel hnbT hnbE ((hC₀j.gr i hi as' hsp').2.2 hr)
        have hk := hr.2
        rw [Nat.add_sub_cancel_left] at hk
        rcases hk with hk | hk
        · -- a finitary field: the family at the readings' values
          have hnone := (hcf₀ j cA hjA).tssNone ψ i (by rw [hk]; intro h; cases h)
          rw [drop_map_getD hlenD hi, (hcf j cA hjA).recEntry ψ i hk hi, hleafT_I ψ,
            (hident j cA hjA).2.2.1 ψ, hnone, slotSet_nil]
          rw [hnone] at hfitS
          obtain ⟨-, hspE⟩ := SlotFit.fin hfitS
          have := fixLeafApp (nP := p.nP) (hlenPps ψ) (hX₀ ψ ρp hρp).1 hρp
            (A := directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ)
              (Fss₀ ψ) (Ess₀ ψ))
            (fun σ => interp2_closed V (hleafClosed ψ) σ _) (as := as)
            (Eis := (eissF₀ j ψ).getD i []) hspE
          rw [hlenA] at this
          exact this
        · -- a reflexive field: the nested product of the family over the telescope
          rw [drop_map_getD hlenD hi, (hcf j cA hjA).reflEntry ψ i hk hi, hleafT_I ψ,
            (hident j cA hjA).2.2.1 ψ, (hident j cA hjA).2.2.2.1 ψ]
          unfold slotSet
          refine ConLeche.Semantics.interp_mkPisAV_piTele (v := p.resSort.eval ψ) (acc := [])
            (fun d hd => (hcf₀ j cA hjA).tssBits ψ i d hd) ?_
          intro bs hsp
          rw [List.nil_append, ← consList_append]
          obtain ⟨-, hspE⟩ := hfitS.2.2 bs hsp
          have hlenAB : (as ++ bs).length = i + ((tssF₀ j ψ).getD i []).length := by
            rw [List.length_append, hlenA, hsp.length_eq, List.length_map]
          have := fixLeafApp (nP := p.nP) (hlenPps ψ) (hX₀ ψ ρp hρp).1 hρp
            (A := directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ)
              (Fss₀ ψ) (Ess₀ ψ))
            (fun σ => interp2_closed V (hleafClosed ψ) σ _) (as := as ++ bs)
            (Eis := (eissF₀ j ψ).getD i []) hspE
          rw [hlenAB, ← Nat.add_assoc] at this
          exact this
  -- the constructors' conses
  have hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
      fssOf p.nP (ctorDataList dsF esF ψ₁ ctorsA 0) = fssOf p.nP (ctorDataList dsF esF ψ₂ ctorsA 0) := by
    intro ψ₁ ψ₂ hφ
    have hcds : ctorDataList dsF esF ψ₁ ctorsA 0 = ctorDataList dsF esF ψ₂ ctorsA 0 := by
      refine ctorDataList_params fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
      have hlpsi := hlpsA cAi (List.mem_of_getElem? hi')
      exact (hcf i cAi hi').params ψ₁ ψ₂ (fun q hq => hφ q (by rw [← hlpsi]; exact hq))
    rw [hcds]
  have hcdMem : ∀ ψ i cd, (ctorDataList dsF esF ψ ctorsA 0)[i]? = some cd →
      ∃ cA, ctorsA[i]? = some cA ∧ cd = (cA.1.name, cA.2, dsF i ψ, esF i ψ) := by
    intro ψ i cd hi
    rw [ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : ctorsA[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cA => rw [h] at hi; exact ⟨cA, rfl, (Option.some.inj hi).symm⟩
  have hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0),
      FieldsBelow p.nP Fs := by
    intro ψ Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
    have := (DomsBelow.drop p.nP ((hcf i cA hiA).below ψ)).fields
    rwa [Nat.zero_add] at this
  have hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) ∧
      SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) := by
    intro ψ ρ hρ
    constructor
    · intro Fs hFs
      obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
      exact ((hframes i cA hiA).2 ψ ρ (((hframes i cA hiA).1 ψ ρ).mp hρ)).1
    · intro Fs hFs
      obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
      exact ((hframes i cA hiA).2 ψ ρ (((hframes i cA hiA).1 ψ ρ).mp hρ)).2.1
  have hfold : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
        interp2 V (consList bs ρ)
            (AVExpr.mkAppN (leafT ψ) (paramBvars p.nP cA.2 ++ esF j ψ))
          = sumSet (p.resSort.eval ψ) (sumFibre (p.resSort.eval ψ)
              (consList (idxValsAt ρ (esF j ψ) bs) ρ)
              (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
                (essOf (ctorDataList dsF esF ψ ctorsA 0)))) := by
    intro j cA hj ψ ρ hρ bs hsp
    have hlenB : bs.length = cA.2 := by
      rw [hsp.length_eq]; simp [(hcf j cA hj).len ψ]
    have hspE : SpineFit ρ (Ids ψ) ((esF j ψ).map (interp2 V (consList bs ρ))) :=
      (((hframes j cA hj).2 ψ ρ (((hframes j cA hj).1 ψ ρ).mp hρ)).2.2 bs hsp).2
    have hleaf := fixLeafApp (nP := p.nP) (hlenPps ψ) (hX₀ ψ ρ hρ).1 hρ
      (A := leafT ψ) (fun σ => interp2_closed V (hleafClosed ψ) σ _) (as := bs) (Eis := esF j ψ) hspE
    rw [hlenB] at hleaf
    rw [paramBvars_eq_paramBvarsAt, hleaf,
      fixFamI_app_eq_sum (hX₀ ψ ρ hρ).1 (hreal ψ ρ hρ) hspE]
    show sumSet _ (sumFibre _ _ (rChains (Ids ψ).length (Ids ψ).length (Fss ψ) (Ess₀ ψ))) = _
    rw [hlenIds, ← hEss ψ]
    show sumSet _ (sumFibre _ _ (rChains _ _ (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))) = _
    rw [fssOfR_fixCtorDataList, essOfR_fixCtorDataList]
    rfl
  -- the invariant across the conses: every constructor's recursive
  -- data, its type and index arguments bounded, the former found
  let Inv : ∀ {env' : Env}, EnvS2Core V env' → Prop := fun {env'} m' =>
    env'.find? p.cvT.name = some (.indInfo cvTa (ConLeche.directFixCaps p)) ∧
    ((ConLeche.directFixCaps p).eta = true →
      env'.find? (projFnName p.cvT.name 0) = none) ∧
    ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ConstsBound env' cA.1.type ∧ (∀ e ∈ idxF j, ConstsBound env' e) ∧
      FixCtorDataI m' env p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort p.isProp
        p.large (idxF j) (dsF j) (esF j) (srcsF j) (ksF j) (fvsPF j) (xFvsF j) (xrestF j) (eissF j)
        (tssF j)
  have hInv : ∀ {env' : Env} (m' : EnvS2Core V env') (cA : ConstantVal × Nat)
      (A : (Name → Nat) → AVExpr)
      (mC : EnvS2Core V ⟨.ctorInfo cA.1 p.nP cA.2 :: env'.consts⟩),
      cA ∈ ctorsA → env'.find? cA.1.name = none →
      mC.acval = acvalWith m'.acval cA.1.name A → Inv m' → Inv mC := by
    intro env' m' cA A mC hcA hfresh hac hinv
    have hTC : p.cvT.name ≠ cA.1.name := by
      intro h
      have h1 := hinv.1
      rw [h, hfresh] at h1
      exact nomatch h1
    have hcross : ∀ e : Expr, ConsCrossAt (.ctorInfo cA.1 p.nP cA.2) e :=
      fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hinv.1, fun he => ?_, fun j cAj hj => ?_⟩
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
      obtain ⟨-, -, -, -, -, -, hpshape, -⟩ := hrunOf j cA hj
      rw [ConLeche.Env.find?_cons, if_neg (fun h => by
        have h' : cA.1.name = projFnName p.cvT.name 0 := h
        have := projFnName_isProjFnShape p.cvT.name 0
        rw [← h', hpshape] at this
        exact nomatch this)]
      exact hinv.2.1 he
    obtain ⟨hcb, hcbI, hD⟩ := hinv.2.2 j cAj hj
    exact ⟨ConstsBound.cons _ hcb, fun e he => ConstsBound.cons _ (hcbI e he),
      hD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcross hcb hcbI mC hac⟩
  have hidxRes₀ : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true := by
    intro j cA hj e he
    have := (hcf j cA hj).opened.residRes
    rw [← (hcf j cA hj).idxEq] at this
    exact this e he
  have hinv₀ : Inv mpI.base2 := by
    refine ⟨hfT_I, hfreshFam₁, fun j cA hj => ?_⟩
    obtain ⟨-, -, -, -, -, htr, -, -, -, -⟩ := hrunOf j cA hj
    exact ⟨constsBound_of_constsResolve _ htr,
      fun e he => constsBound_of_constsResolve _ (Expr.constsResolve_mono (hidxRes₀ j cA hj e he)),
      hcf j cA hj⟩
  obtain ⟨mpC, hE_C, hfT_C, hFD_C, hleafT_C, hconsAll, hinvC⟩ := ctorsLoopGen hμ hCtors hndA hlpsT
    hlpsA hFssParams hFssBelow (fun j cA hj => (hframes j cA hj).1) hFssOkP
    (fun j cA hj ψ ρ hρ bs hsp => ((hframes j cA hj).2 ψ ρ hρ).2.2 bs hsp |>.2)
    Inv hInv (ConLeche.directFixCaps p) leafT
    (fun m' hinv hFD' hleaf' => hcapsLaws m' hinv.2.1 hFD' hleaf') hfold
    ctorsA 0 _ mpI (fun i => by rw [Nat.zero_add]) (Nat.zero_add _) hE_I hfT_I hFD_I hleafT_I
    (fun i cA hi _ => absurd hi (Nat.not_lt_zero _))
    (fun i cA _ hi => by
      obtain ⟨-, -, -, -, hfresh, htr, -, -, -, -⟩ := hrunOf i cA hi
      exact ⟨hfresh, htr, fun e he => Expr.constsResolve_mono (hidxRes₀ i cA hi e he),
        (hcf i cA hi).toCtorDataI⟩)
    hinv₀
  -- the recursor
  have hcf_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      FixCtorFactsAt mpC.base2 env p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF j cA := by
    intro j cA hj
    obtain ⟨⟨hfind, hlps, -⟩, -, -⟩ := hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj
    exact ⟨hfind, hlps, (hinvC.2.2 j cA hj).2.2⟩
  have hidxRes_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∀ e ∈ idxF j, e.constsResolve (ConLeche.consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (ConLeche.directFixCaps p) :: env.consts⟩) = true :=
    fun j cA hj => (hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj).2.1
  have hleafC_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA → ∀ ψ,
      mpC.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))) := by
    intro j cA hj ψ
    rw [fssOfR_fixCtorDataList]
    exact (hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj).2.2 ψ
  have hleafT_C' : ∀ ψ, mpC.base2.acval p.cvT.name ψ
      = directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (Ids ψ) rss
          (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (Fss₀ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) := by
    intro ψ
    rw [hEiss ψ, hEss ψ, hTlss ψ]
    exact hleafT_C ψ
  have hmI : p.majorIdx = p.nP + 1 + ctorsA.length + p.nIdx := by
    simp only [DirectSumParts.majorIdx, DirectSumParts.rulePrefix, hlenA]
  have hrP : p.rulePrefix = p.nP + 1 + ctorsA.length := by
    simp only [DirectSumParts.rulePrefix, hlenA]
  have hframesR : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (Ids ψ) rss
        (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (Fss₀ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (Ids ψ) p.nIdx rss
          (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (Fss₀ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
        (uAV ψ) (p.resSort.eval ψ) ρp (Ids ψ) rss
        (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (Fss₀ ψ)
        (Fss ψ) (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        FieldsOkB (p.resSort.eval ψ) ρp ((Fss ψ).getD j []) ∧
        ∀ bs : List V, SpineFit ρp ((Fss ψ).getD j []) bs →
          (∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
            AnnotOk2 V (consList bs ρp) E) ∧
          SpineFit ρp (Ids ψ)
            (idxValsAt ρp ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs)) ∧
      SumFieldsValid ρp (Fss ψ) ∧
      (∀ j, j < ctorsA.length →
        ∀ i ∈ recIdx (rss.getD j []) ((Fss ψ).getD j []).length,
        ∀ fs : List V, SpineFit ρp ((Fss ψ).getD j []) fs →
        FieldsValid (consList (fs.take i) ρp)
          ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map
            (·.2.2)) ∧
        ∀ bs : List V, SpineFit (consList (fs.take i) ρp)
          ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map
            (·.2.2)) bs →
        ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i [],
          AnnotValidV V (consList bs (consList (fs.take i) ρp)) E) ∧
      (∀ j, j < ctorsA.length →
        ∀ bs : List V, SpineFit ρp ((Fss ψ).getD j []) bs →
        ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
          AnnotValidV V (consList bs ρp) E) := by
    intro ψ ρp hρp
    rw [hEiss ψ, hEss ψ, hTlss ψ]
    refine ⟨(hX₀ ψ ρp hρp).1, by rw [← hlenIds ψ]; exact hreal ψ ρp hρp, fun j hj => ?_,
      fun Fs hFs => ?_, fun j hj i hi fs hsp => ?_, fun j hj bs hsp E hE => ?_⟩
    · obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hFssD ψ j cA hjA, hEss₀D ψ j cA hjA, ← (hident j cA hjA).2.1 ψ]
      have hf := (hframes j cA hjA).2 ψ ρp (((hframes j cA hjA).1 ψ ρp).mp hρp)
      exact ⟨hf.1, fun bs hsp => ⟨fun E hE => ((hf.2.2 bs hsp).1 E hE).1, (hf.2.2 bs hsp).2⟩⟩
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs
      rw [fssOfR_getElem?, fixCtorDataList_getElem?] at hj
      cases hjA : ctorsA[j]? with
      | none => rw [hjA] at hj; exact nomatch hj
      | some cA =>
        rw [hjA] at hj
        obtain rfl := Option.some.inj hj
        rw [Nat.zero_add]
        exact ((hframes j cA hjA).2 ψ ρp (((hframes j cA hjA).1 ψ ρp).mp hρp)).2.1
    · obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hTlss₀D ψ j cA hjA, hEiss₀D ψ j cA hjA, ← (hident j cA hjA).2.2.1 ψ,
        ← (hident j cA hjA).2.2.2.1 ψ]
      rw [hrss j hj, hlenFs ψ j cA hjA, ← hksLen j cA hjA, recIdx_rsOf, mem_recIdxOf] at hi
      obtain ⟨hilt, hk⟩ := hi
      rw [hFssD ψ j cA hjA] at hsp
      have hf := (hframes j cA hjA).2 ψ ρp (((hframes j cA hjA).1 ψ ρp).mp hρp)
      have hlenD := (hcf j cA hjA).len ψ
      have hi' : i < cA.2 := by rw [← hksLen j cA hjA]; exact hilt
      have hv := fieldsValid_getD hf.2.1 (j := i) (by simp [hlenD]; exact hi')
        (spineFit_take hsp (by simp [hlenD]; omega))
      rw [drop_map_getD hlenD hi'] at hv
      rcases hk with hk | hk
      · rw [(hcf j cA hjA).recEntry ψ i hk hi'] at hv
        rw [(hcf j cA hjA).tssNone ψ i (by rw [hk]; intro h; cases h)]
        obtain ⟨-, hargs⟩ := AnnotValidV.mkAppN_inv hv
        refine ⟨trivial, fun bs hbs E hE => ?_⟩
        cases bs with
        | nil => simpa using hargs E (List.mem_append_right _ hE)
        | cons b bs => exact hbs.elim
      · rw [(hcf j cA hjA).reflEntry ψ i hk hi'] at hv
        obtain ⟨hTV, hB⟩ := AnnotValidV_mkPisAV_inv hv
        refine ⟨hTV, fun bs hbs E hE => ?_⟩
        obtain ⟨-, hargs⟩ := AnnotValidV.mkAppN_inv (hB bs hbs)
        exact hargs E (List.mem_append_right _ hE)
    · obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hEss₀D ψ j cA hjA, ← (hident j cA hjA).2.1 ψ] at hE
      rw [hFssD ψ j cA hjA] at hsp
      have hf := (hframes j cA hjA).2 ψ ρp (((hframes j cA hjA).1 ψ ρp).mp hρp)
      exact ((hf.2.2 bs hsp).1 E hE).2
  obtain ⟨sAV, mp₃, hac₃⟩ := stageFixRec (fssZ := Fss₀) hE_C hμ mpC hmI hrP rfl rfl hRec hstripT hfT_C
    (fun m₂ _ hFD' hleaf' => hcapsLaws m₂ hfreshFam hFD'
      (fun ψ => by rw [hleaf' ψ]; exact hleafT_C ψ))
    hlpsT hopT helimR hRlps hFD_C hlenK' hks hcf_C hidxRes_C hUparams hleafT_C' hleafC_C
    (fun j cA hj => (hframes j cA hj).1) hframesR
    (fun hl => (hwl hl).imp_right fun h => by rw [hlenA]; exact h)
  -- the projection table at a structure-like block (task #210 Parts A, B)
  exact declDirectFixTable rfl rfl hTbl mpC mp₃ hac₃ hProp hRname hClps hresT hresR
    (by rw [← hTname₀]; exact hpshapeT)
    mp.base2.wf hlenA hnFc hrunOf hfT_C hlpsT hTfresh'
    (by rw [hTtype]; exact htrT) hFD_C hcf_C hleafT_C' hleafC_C hframes hsortsOf
    (fun ψ ρp h => ⟨(hframesR ψ ρp h).1, (hframesR ψ ρp h).2.1⟩) hRec

end ConLeche.SetP
