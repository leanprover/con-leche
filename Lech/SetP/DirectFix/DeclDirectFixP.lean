import Lech.SetP.DirectFix.FixAssemblyKitP
import Lech.Semantics.Direct.DeclDirectFix
import Lech.Verify.Direct.FixParts

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

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps DirectSumParts
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
    {block : List ConstantInfo} {p : DirectFixParts} (mp : EnvS2PM V μ env)
    (hE : Lech.EtaFamiliesClosed env) (hdp : Lech.directFixParts? block = some p)
    (h : Lech.Semantics.DeclDirectFixRun μ F env p env₂) : Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨-, hwl, hnd, cvTa, env₁, p₁, ctorsA, cvRa, rhss, tfvs, trest, isorts, hInd, hsort,
    hopT2, hsorts, hCtors, hFOk, hRec, rfl⟩ := h
  obtain ⟨hshape, -, hlenK, hpos⟩ := Lech.directFixParts?_inv hdp
  obtain ⟨hProp, -, hClps, -, -, helimR, hRlps, -, -⟩ := Lech.directFixShape?_inv hshape
  -- the former: its run completed the record with the sort it read
  -- (task #195), pinned equal to the syntactic one — so the record is
  -- the recogniser's
  obtain ⟨cvT, s, hTname₀, hTlps₀, hccvT, hps, rfl, bsT, hstripT⟩ :=
    Lech.checkDirectSumInd_shape hInd
  have hs : s = p.resSort := by subst hps; exact hsort
  subst hs
  have hp₁ : p₁ = p.toDirectSumParts := by
    rw [hps]; exact Lech.DirectSumParts.withSort_self _ hProp
  subst hp₁
  obtain ⟨hfindT, -, -, -, -, -, typeT, -, -, -, -, htrT, -, -, htyT⟩ :=
    Lech.checkConstantVal_inv hccvT
  have hTname : cvTa.name = p.cvT.name := by rw [htyT]; exact hTname₀
  have hlpsT : cvTa.levelParams = p.cvT.levelParams := by rw [htyT]; exact hTlps₀
  have hTtype : cvTa.type = typeT := by rw [htyT]
  obtain ⟨ppsAll, hFD⟩ := formerData_of hμ mp hccvT hstripT
  have hTfresh : env.find? cvTa.name = none := by rw [hTname, ← hTname₀]; exact hfindT
  have hTfresh' : env.find? p.cvT.name = none := by rw [← hTname₀]; exact hfindT
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (by rw [hTtype]; exact htrT)
  have hfT_I : (⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩ : Env).find?
      p.cvT.name = some (.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts)) := by
    rw [← hTname]; exact Lech.Env.find?_cons_self _ _
  have hProp' : p.isProp = true → (Level.isEquiv p.resSort .zero == some true) = true :=
    fun h => by rw [← hProp]; exact h
  obtain ⟨tfvsP, trestP, hopT⟩ := openPisAtFvars_of_stripPis_isSome p.nP 0
    (Lech.stripPis_isSome_of_le (Nat.le_add_right _ _) (by rw [hstripT]; rfl))
  have hE_I : Lech.EtaFamiliesClosed
      ⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩ := by
    intro T'' cvT'' caps hf he hr
    rw [Lech.Env.find?_cons] at hf
    split at hf
    · obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
      exact absurd he Bool.false_ne_true
    · obtain ⟨cvC', hfC'⟩ := hE T'' cvT'' caps hf he hr
      exact ⟨cvC', Lech.Env.find?_cons_of_fresh hTfresh hfC'⟩
  -- the constructors' runs
  obtain ⟨hlenA, hall⟩ := Lech.checkDirectSumCtors_inv hCtors
  have hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ c : ConstantVal × Nat, p.ctors[j]? = some c ∧
      cA.1.name = c.1.name ∧ cA.1.levelParams = p.cvT.levelParams ∧
      (⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩ : Env).find?
        cA.1.name = none ∧
      cA.1.type.constsResolve
        ⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩ = true ∧
      Lech.checkDirectSumCtor (Lech.fueledOps μ F)
        ⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩
        ⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩
        p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large c.1 cA.2 cvTa
        = .ok cA.1 := by
    intro j cA hj
    have hjl : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; omega
    obtain ⟨hnF, hCtor⟩ := hall j (p.ctors[j]) cA (List.getElem?_eq_getElem hjl) hj
    rw [← hnF] at hCtor
    obtain ⟨hccvC, -, -⟩ := Lech.checkDirectSumCtor_shape hCtor
    obtain ⟨hfindC, -, -, -, -, -, typeC, -, -, -, -, htrC, -, -, htyC⟩ :=
      Lech.checkConstantVal_inv hccvC
    refine ⟨p.ctors[j], List.getElem?_eq_getElem hjl, by rw [htyC], ?_, ?_, ?_, hCtor⟩
    · rw [htyC]
      exact (hClps _ (List.getElem_mem hjl)).1
    · show Env.find? _ cA.1.name = none
      rw [htyC]; exact hfindC
    · show Expr.constsResolve _ cA.1.type = true
      rw [htyC]; exact htrC
  have hrunOf' : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ c : ConstantVal × Nat, Lech.checkDirectSumCtor (Lech.fueledOps μ F)
        ⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩
        ⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩
        p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large c.1 cA.2 cvTa
        = .ok cA.1 := by
    intro j cA hj
    obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
    exact ⟨c, hCtor⟩
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
  -- the dummy former: the constructors' readings and the index
  -- telescope need a carrier storing the former
  obtain ⟨mpI₀, hacI₀⟩ := stageSumFormer mp hE hccvT hTname₀ hFD (fun _ => []) (fun _ _ _ => rfl)
    (fun _ _ h => nomatch h) (fun _ _ _ => ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩)
  have hFD_I₀ : FormerData mpI₀.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll :=
    hFD.cross (c₀ := .indInfo cvTa (Lech.directSumCaps p.toDirectSumParts)) hTfresh
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
    obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
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
  -- the real former
  have hlpsA : ∀ cA ∈ ctorsA, cA.1.levelParams = p.cvT.levelParams := by
    intro cA hcA
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨-, -, -, hlps, -⟩ := hrunOf j cA hj
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
    hFD.cross (c₀ := .indInfo cvTa (Lech.directSumCaps p.toDirectSumParts)) hTfresh
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
    obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
    obtain ⟨hiff, hfields⟩ := ctorFramesGen hμ mpI hCtor hfT_I hProp' hFD_I (hcf j cA hj).toCtorDataI
      hleafT_I'
    exact ⟨hiff, fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1, (hfields ψ ρ h).2.2.2⟩⟩
  have hC : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      ChainFacts (uAV ψ) (p.resSort.eval ψ) p.nP cA.2 ρp (Ids ψ) (ksF j) (tssF j ψ)
        (((dsF j ψ).drop p.nP).map (·.2.2)) (eissF j ψ) (esF j ψ) := by
    intro j cA hj ψ ρp hρp
    obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
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
          refine Lech.Semantics.interp_mkPisAV_piTele (v := p.resSort.eval ψ) (acc := [])
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
  let leafT : (Name → Nat) → AVExpr := fun ψ =>
    directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (Ids ψ) rss (Tlss₀ ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ)
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
    env'.find? p.cvT.name = some (.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts)) ∧
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
    refine ⟨Lech.Env.find?_cons_of_fresh hfresh hinv.1, fun j cAj hj => ?_⟩
    obtain ⟨hcb, hcbI, hD⟩ := hinv.2 j cAj hj
    exact ⟨ConstsBound.cons _ hcb, fun e he => ConstsBound.cons _ (hcbI e he),
      hD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcross hcb hcbI mC hac⟩
  have hidxRes₀ : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true := by
    intro j cA hj e he
    have := (hcf j cA hj).opened.residRes
    rw [← (hcf j cA hj).idxEq] at this
    exact this e he
  have hinv₀ : Inv mpI.base2 := by
    refine ⟨hfT_I, fun j cA hj => ?_⟩
    obtain ⟨-, -, -, -, -, htr, -⟩ := hrunOf j cA hj
    exact ⟨constsBound_of_constsResolve _ htr,
      fun e he => constsBound_of_constsResolve _ (Expr.constsResolve_mono (hidxRes₀ j cA hj e he)),
      hcf j cA hj⟩
  obtain ⟨mpC, hE_C, hfT_C, hFD_C, hleafT_C, hconsAll, hinvC⟩ := ctorsLoopGen hμ hCtors hndA hlpsT
    hlpsA hFssParams hFssBelow (fun j cA hj => (hframes j cA hj).1) hFssOkP
    (fun j cA hj ψ ρ hρ bs hsp => ((hframes j cA hj).2 ψ ρ hρ).2.2 bs hsp |>.2)
    Inv hInv leafT hfold
    ctorsA 0 _ mpI (fun i => by rw [Nat.zero_add]) (Nat.zero_add _) hE_I hfT_I hFD_I hleafT_I
    (fun i cA hi _ => absurd hi (Nat.not_lt_zero _))
    (fun i cA _ hi => by
      obtain ⟨-, -, -, -, hfresh, htr, -⟩ := hrunOf i cA hi
      exact ⟨hfresh, htr, fun e he => Expr.constsResolve_mono (hidxRes₀ i cA hi e he),
        (hcf i cA hi).toCtorDataI⟩)
    hinv₀
  -- the recursor
  have hcf_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      FixCtorFactsAt mpC.base2 env p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF j cA := by
    intro j cA hj
    obtain ⟨⟨hfind, hlps, -⟩, -, -⟩ := hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj
    exact ⟨hfind, hlps, (hinvC.2 j cA hj).2.2⟩
  have hidxRes_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∀ e ∈ idxF j, e.constsResolve (Lech.consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (Lech.directSumCaps p.toDirectSumParts) :: env.consts⟩) = true :=
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
  obtain ⟨sAV, mp₃, -⟩ := stageFixRec (fssZ := Fss₀) hE_C hμ mpC hmI hrP rfl rfl hRec hstripT hfT_C
    rfl rfl hlpsT hopT helimR hRlps hFD_C hlenK' hks hcf_C hidxRes_C hUparams hleafT_C' hleafC_C
    (fun j cA hj => (hframes j cA hj).1) hframesR
    (fun hl => (hwl hl).imp_right fun h => by rw [hlenA]; exact h) (by rw [hlenA]; exact hpos)
  exact ⟨mp₃⟩

end Lech.SetP
