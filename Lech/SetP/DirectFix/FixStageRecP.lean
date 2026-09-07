import Lech.SetP.DirectFix.FixRuleDataP
import Lech.SetP.DirectFix.FixRuleOkP
import Lech.SetP.DirectFix.FixRecLeafP
import Lech.Semantics.Tower.FixWire

/-!
# The recursive recursor's stage, part 1: the rule law (task #188)

The semantic data of a recursive block at an assignment (`fssOfR`,
`essOfR`, `eissOfR`, `rssOfK`), the recursor leaf (`fixLeafAV`), the
rule's binder data as domains (`fixRuleDataAV_map_dom`), and **the
rule law** at the recursor's cons (`fixRecRuleLaw`): the sum route's
`sumRecRuleLaw` with the rule read at the cons (`fixRuleData_of`),
its gradedness from the model (`fixRuleOkP`, supplied), and the
recursor's iota (`fixRecLawCore`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  DirectFixParts RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The semantic data of a block -/

/-- The constructors' field lists. -/
def fssOfR (nP : Nat) (cds : List CtorDatumR) : List (List AVExpr) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The constructors' index readings. -/
def essOfR (cds : List CtorDatumR) : List (List AVExpr) := cds.map fun cd => cd.2.2.2.1

/-- The constructors' per-field index expressions. -/
def eissOfR (cds : List CtorDatumR) : List (List (List AVExpr)) := cds.map fun cd => cd.2.2.2.2.2

/-- The recursive flags of the first `n` constructors. -/
def rssOfK (ksF : Nat → List RecFieldKind) (n : Nat) : List (List Bool) :=
  (List.range n).map fun j => rsOf (ksF j)

omit [SetTheory V] in
theorem fssOfR_getElem? (nP : Nat) (cds : List CtorDatumR) (j : Nat) :
    (fssOfR nP cds)[j]? = (cds[j]?).map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_getElem? (cds : List CtorDatumR) (j : Nat) :
    (essOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.1 := by simp [essOfR]

omit [SetTheory V] in
theorem eissOfR_getElem? (cds : List CtorDatumR) (j : Nat) :
    (eissOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.2.2 := by simp [eissOfR]

omit [SetTheory V] in
theorem fssOfR_length (nP : Nat) (cds : List CtorDatumR) : (fssOfR nP cds).length = cds.length := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_length (cds : List CtorDatumR) : (essOfR cds).length = cds.length := by simp [essOfR]

omit [SetTheory V] in
theorem eissOfR_length (cds : List CtorDatumR) : (eissOfR cds).length = cds.length := by
  simp [eissOfR]

omit [SetTheory V] in
theorem rssOfK_getD {ksF : Nat → List RecFieldKind} {n j : Nat} (hj : j < n) :
    (rssOfK ksF n).getD j [] = rsOf (ksF j) := by
  simp [rssOfK, List.getD_eq_getElem?_getD, List.getElem?_range hj]

/-! ## The rule's binder data as domains -/

theorem fixRuleDataAV_map_dom {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AVExpr)} {cds : List CtorDatumR}
    {ds : List (Nat × Nat × AVExpr)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx) :
    (fixRuleDataAV m T ψ nP nIdx ℓ pps ips cds ds).map (·.2)
      = ((fixRecDataAV m T ψ nP nIdx ℓ pps ips cds).take (nP + 1 + cds.length)).map (·.2.2) ++
        (liftDoms (cds.length + 1) 0 (ds.drop nP)).map (·.2.2) := by
  have hlenX : (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
      [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
      fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1).length = nP + 1 + cds.length := by
    simp only [List.length_append, rebit_length, hlenP, List.length_singleton, fixMinorsData_length]
  generalize hX : rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
      [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
      fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 = X at hlenX
  have hlenXD : (X ++ rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips)).length
      = nP + 1 + cds.length + nIdx := by
    rw [List.length_append, hlenX, rebit_length, liftDoms_length, hlenI]
  unfold fixRuleDataAV fixRecDataAV
  rw [hX, List.take_append_of_le_length (by omega :
      nP + 1 + cds.length ≤ (X ++ rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips)).length),
    List.take_append_of_le_length (by omega : nP + 1 + cds.length ≤ X.length),
    List.take_of_length_le (by omega : X.length ≤ nP + 1 + cds.length)]
  simp only [List.map_append, List.map_map, rebit]
  rfl

/-! ## The recursor leaf -/

/-- The restriction of an assignment to a level-parameter list. -/
def restrictΨ (lps : List Name) (ψ : Name → Nat) : Name → Nat :=
  fun q => if q ∈ lps then ψ q else 0

omit [SetTheory V] in
theorem restrictΨ_agree (lps : List Name) (ψ : Name → Nat) :
    ∀ q ∈ lps, restrictΨ lps ψ q = ψ q := by
  intro q hq
  simp [restrictΨ, hq]

omit [SetTheory V] in
theorem restrictΨ_congr {lps : List Name} {ψ₁ ψ₂ : Name → Nat}
    (h : ∀ q ∈ lps, ψ₁ q = ψ₂ q) : restrictΨ lps ψ₁ = restrictΨ lps ψ₂ := by
  funext q
  unfold restrictΨ
  split
  · next hq => exact h q hq
  · rfl

/-- The recursor leaf's sort: the kernel's inferred sort at the
restricted assignment, floored at one at a nonzero elimination level,
zero at a zero one. -/
def fixSortAV (elimL : Level) (u : Level) (lps : List Name) (ψ : Name → Nat) : Nat :=
  if elimL.eval ψ = 0 then 0 else max 1 (u.eval (restrictΨ lps ψ))

omit [SetTheory V] in
theorem fixSortAV_zero_iff (elimL u : Level) (lps : List Name) (ψ : Name → Nat) :
    fixSortAV elimL u lps ψ = 0 ↔ elimL.eval ψ = 0 := by
  unfold fixSortAV
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h =>
    exact ⟨fun h' => absurd h' (by have := Nat.le_max_left 1 (u.eval (restrictΨ lps ψ)); omega),
      fun h' => absurd h' h⟩


/-! ## The data at the parameters -/

theorem fixRecDataAV_take_nP {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AVExpr)} {cds : List CtorDatumR}
    (hlenP : pps.length = nP) :
    ((fixRecDataAV m T ψ nP nIdx ℓ pps ips cds).take nP).map (·.2.2) = pps.map (·.2.2) := by
  unfold fixRecDataAV
  rw [List.take_append_of_le_length (by simp [hlenP]),
    List.take_append_of_le_length (by simp [hlenP]),
    List.take_append_of_le_length (by simp [hlenP]),
    List.take_append_of_le_length (by simp [hlenP]),
    List.take_of_length_le (by simp [hlenP]), rebit_map_dom]

omit [SetTheory V] in
/-- The constructor data at two assignments agreeing on the data. -/
theorem fixCtorDataList_congr {dsF₁ dsF₂ : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF₁ esF₂ : Nat → (Name → Nat) → List AVExpr} {ksF : Nat → List RecFieldKind}
    {eissF₁ eissF₂ : Nat → (Name → Nat) → List (List AVExpr)} {ψ₁ ψ₂ : Name → Nat} :
    ∀ (cs : List (ConstantVal × Nat)) (j : Nat),
      (∀ i, i < cs.length → dsF₁ (j + i) ψ₁ = dsF₂ (j + i) ψ₂ ∧ esF₁ (j + i) ψ₁ = esF₂ (j + i) ψ₂ ∧
        eissF₁ (j + i) ψ₁ = eissF₂ (j + i) ψ₂) →
      fixCtorDataList dsF₁ esF₁ ksF eissF₁ ψ₁ cs j = fixCtorDataList dsF₂ esF₂ ksF eissF₂ ψ₂ cs j
  | [], _, _ => rfl
  | c :: cs, j, h => by
    simp only [fixCtorDataList]
    obtain ⟨h1, h2, h3⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h1 h2 h3
    rw [h1, h2, h3, fixCtorDataList_congr cs (j + 1) fun i hi => by
      have := h (i + 1) (by simpa using hi)
      rwa [show j + (i + 1) = j + 1 + i from by omega] at this]

/-! ## The rule law -/

set_option maxHeartbeats 6400000 in
/-- **The recursive recursor rule's law** at the recursor's cons. -/
theorem fixRecRuleLaw (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectFixParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {mI rP : Nat}
    (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    (hRec : Lech.checkDirectFixRec (Lech.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    {caps : IndCaps}
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {bsT : List (Name × Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    {ppsAll : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    {env₀ : Env} {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AVExpr)}
    (hlenK : p.kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt mp.base2 env₀ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF i cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    (hRD : SumRecData mp.base2 cvRa p.nP ctorsA.length p.nIdx (Lech.directElimLevel p.elim p.large)
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA))
    -- the leaf and its facts
    {A : (Name → Nat) → AVExpr} {sAV : (Name → Nat) → Nat} {uAV : (Name → Nat) → Nat}
    {fssZ : (Name → Nat) → List (List AVExpr)}
    (hA : ∀ ψ, A ψ = directFixRecAVI ((Lech.directElimLevel p.elim p.large).eval ψ) (p.resSort.eval ψ)
      p.nP (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) (((ppsAll ψ).drop p.nP).map (·.2.2))
      (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ) (sAV ψ))
    (hpre : ∀ ψ, FixPre V ((Lech.directElimLevel p.elim p.large).eval ψ) (p.resSort.eval ψ) (uAV ψ)
      p.nP (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (fssZ ψ)
      (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
      (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ) (sAV ψ))
    (hAcl : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase)
    (hokFssH : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      SumFieldsOkB (p.resSort.eval ψ) ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))))
    -- the rule
    {j : Nat} {cA : ConstantVal × Nat} (hj : ctorsA[j]? = some cA) {rhs : Expr}
    (hrhs : rhss[j]? = some rhs)
    (hRuleOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkLamsAV (fixRuleDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx
          (Lech.directElimLevel p.elim p.large) ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP)
          (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0) (dsF j ψ))
        (fixRuleCoreAV (A ψ) p.nP cA.2 ctorsA.length j (Lech.recIdxOf (ksF j)) (eissF j ψ))))
    (hfresh : env.find? cvRa.name = none)
    {rule : RecRule} (hrule : rule = ⟨cA.1.name, cA.2, p.nP, .plain, rhs⟩)
    {rules : List RecRule}
    (m₂ : EnvS2Core V ⟨.recInfo cvRa mI rP rules :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cvRa.name A)
    (φ : Name → Nat) :
    RecRuleLawP m₂ φ cvRa.name cvRa mI rP rule := by
  subst hrule
  obtain ⟨hfC, hlpsC, hD⟩ := hcf j cA hj
  have hCD := hD.toCtorDataI
  have hjn : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  -- the constructor's stored type
  obtain ⟨-, -, hCres, -, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCres
  have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ hCres
  have hRC : cA.1.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfC; exact nomatch hfC
  have hRT : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  have hcbT : ConstsBound env cvRa.type := by
    obtain ⟨cvRi, recTy, sty, u, -, -, -, htrR, -, -, -, -, -, -, hcvRa⟩ :=
      Lech.checkDirectFixRec_shape hRec
    have : cvRa.type = recTy := by rw [hcvRa]
    rw [this]
    exact constsBound_of_constsResolve _ htrR
  -- the cons crossing
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo cvRa mI rP rules) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hfindC : (⟨.recInfo cvRa mI rP rules :: env.consts⟩ : Env).find? cA.1.name
      = some (.ctorInfo cA.1 p.nP cA.2) := by
    rw [Lech.Env.find?_cons, if_neg (fun h => hRC h.symm)]
    exact hfC
  -- the readings at `m₂` are the readings at `mp`
  have hTac : ∀ ψ, m₂.acval p.cvT.name ψ = mp.base2.acval p.cvT.name ψ := by
    intro ψ; rw [hac, acvalWith_ne hRT]
  have hCac : ∀ ψ, ∀ cd ∈ fixCtorDataList dsF esF ksF eissF ψ ctorsA 0,
      m₂.acval cd.1 ψ = mp.base2.acval cd.1 ψ := by
    intro ψ cd hcd
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcd
    rw [fixCtorDataList_getElem?, Nat.zero_add] at hi
    cases hA' : ctorsA[i]? with
    | none => rw [hA'] at hi; exact nomatch hi
    | some cAi =>
      rw [hA'] at hi
      obtain rfl := Option.some.inj hi
      obtain ⟨hfi, -, -⟩ := hcf i cAi hA'
      have hne : cAi.1.name ≠ cvRa.name := by
        intro h; rw [h, hfresh] at hfi; exact nomatch hfi
      show m₂.acval cAi.1.name ψ = _
      rw [hac, acvalWith_ne hne]
  -- the law
  refine ⟨by omega, fun us hus => ?_⟩
  dsimp only
  have hinstR : ∀ (d : Nat) (e : Expr),
      denoteP m₂.acval _ φ d (e.instantiateLevelParams cvRa.levelParams us)
        = denoteP m₂.acval _ (Level.substFn φ cvRa.levelParams us) d e :=
    fun d e => denoteP_instLevels (acvalParamsAt_of_core m₂) φ d e
  generalize hψR : Level.substFn φ cvRa.levelParams us = ψR at hinstR ⊢
  -- the right-hand side's reading, at the extension
  obtain ⟨rhs', hrhs', -, -, -, hread⟩ := fixRuleData_of mp hRec hfT hlpsT hstripT hopT hFD hlenK hks
    hcf (mI := mI) (rP := rP) (rules := rules) hfresh hRT m₂ hac hj
  obtain rfl := Option.some.inj (hrhs.symm.trans hrhs')
  have hRa₂ : denoteP m₂.acval ⟨.recInfo cvRa mI rP rules :: env.consts⟩ φ 0
      (rhs.instantiateLevelParams cvRa.levelParams us)
      = some (mkLamsAV (fixRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx
          (Lech.directElimLevel p.elim p.large) ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP)
          (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0) (dsF j ψR))
        (fixRuleCoreAV (A ψR) p.nP cA.2 ctorsA.length j (Lech.recIdxOf (ksF j)) (eissF j ψR))) := by
    rw [hinstR, hread ψR, fixRuleDataAV_congr (hTac ψR) (hCac ψR)]
  refine ⟨_, hRa₂, hRuleOk ψR, fun _ _ h => absurd h (by simp), ?_⟩
  intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ hplain _ hidx hTVa
    hTVja hfitR hfitC
  -- the constructor found is the block's
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfindC.symm.trans hfcj))
  -- the level assignments
  have hagree : ∀ q ∈ p.cvT.levelParams,
      Level.substFn φ cA.1.levelParams usj q = ψR q := by
    have h := hψ
    simp only [Lech.recFireComparands] at h
    rw [hlpsC] at h
    rw [hlpsC, ← hψR]
    exact substFn_agree_of_comparand h
  generalize hψC : Level.substFn φ cA.1.levelParams usj = ψC at hagree hTVja hfitR hfitC ⊢
  have hdsEq : ∀ i, i < ctorsA.length →
      dsF i ψC = dsF i ψR ∧ esF i ψC = esF i ψR ∧ eissF i ψC = eissF i ψR := by
    intro i hi
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨-, hlpsi, hDi⟩ := hcf i cAi hi'
    exact ⟨(hDi.params ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq))).1,
      (hDi.params ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq))).2,
      hDi.eissParams ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq))⟩
  have hcdsEq : fixCtorDataList dsF esF ksF eissF ψC ctorsA 0
      = fixCtorDataList dsF esF ksF eissF ψR ctorsA 0 :=
    fixCtorDataList_congr ctorsA 0 fun i hi => by rw [Nat.zero_add]; exact hdsEq i hi
  have hdsjEq : dsF j ψC = dsF j ψR := (hdsEq j hjn).1
  have hesjEq : esF j ψC = esF j ψR := (hdsEq j hjn).2.1
  have hwEq : p.resSort.eval ψC = p.resSort.eval ψR :=
    (hFD.params ψC ψR (fun q hq => hagree q (by rw [← hlpsT]; exact hq))).2
  -- the recursor and constructor types' readings, at the extension
  have hRD₂ := hRD.cross (c₀ := .recInfo cvRa mI rP rules) hfresh (hcross _) hcbT m₂ hac
  have hCD₂ := hCD.cross (c₀ := .recInfo cvRa mI rP rules) hfresh hRT hcross hcbC
    (fun e he => constsBound_of_constsResolve _ (hidxRes j cA hj e he)) m₂ hac
  have hTVa' : TVa = mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψR)
      (recConcAV ctorsA.length p.nIdx) := by
    have h := hTVa
    rw [hinstR] at h
    exact Option.some.inj (h.symm.trans (hRD₂.read ψR))
  have hTVja' : TVja = mkPisAV (dsF j ψR) (ctorBodyAVI m₂ p.cvT.name p.nP cA.2 ψC (esF j ψR)) := by
    have h := hTVja
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ 0 cA.1.type, hψC] at h
    have := Option.some.inj (h.symm.trans (hCD₂.read ψC))
    rw [this, hdsjEq, hesjEq]
  -- the constructor's leaf at the extension
  have hleafC₂ : m₂.acval cA.1.name ψC
      = directSumMkAV (p.resSort.eval ψR) j (dsF j ψR) (((dsF j ψR).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0))) := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cA.1.name ψC = _
    rw [acvalWith_ne hRC, hleafC j cA hj ψC, hdsjEq, hwEq, hcdsEq]
  have hleafR₂ : m₂.acval cvRa.name ψR = A ψR := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cvRa.name ψR = _
    rw [acvalWith_self]
  -- the fits, as spines
  have hspR : SpineFit ρ ((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψR).map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directSumMkAV (p.resSort.eval ψR) j (dsF j ψR)
        (((dsF j ψR).drop p.nP).map (·.2.2))
        (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0)))) ys]).map
        (interp2 V ρ)) := by
    have hst := stripPisAV_mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψR)
      (recConcAV ctorsA.length p.nIdx)
    rw [hRD.len ψR] at hst
    have htele := piTeleP_of_stripPisAV hst
    have hfit := hfitR
    rw [hTVa'] at hfit
    try simp only [RecRule.ctor] at hfit
    rw [hleafC₂] at hfit
    have hchain := teleFitPA_to_chain (p.nP + ctorsA.length + p.nIdx + 2) htele
      (by simp [hxl, hmI]; omega) hfit
    refine spineFit_of_chain (by simp [hxl, hRD.len ψR, hmI]; omega) ?_
    intro n hn
    have := hchain n (by simpa [hRD.len ψR] using hn)
    simpa [hRD.len ψR] using this
  have hstC := stripPisAV_mkPisAV (dsF j ψR) (ctorBodyAVI m₂ p.cvT.name p.nP cA.2 ψC (esF j ψR))
  rw [hCD.len ψR] at hstC
  have hteleC := piTeleP_of_stripPisAV hstC
  have hspC : SpineFit ρ ((dsF j ψR).map (·.2.2)) (ys.map (interp2 V ρ)) := by
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain (p.nP + cA.2) hteleC (by simpa using hyl) hfit
    refine spineFit_of_chain (by simp [hyl, hCD.len ψR]) ?_
    intro n hn
    have := hchain n (by simpa [hCD.len ψR] using hn)
    simpa [hCD.len ψR] using this
  have hplain' : ∀ i, i < p.nP →
      interp2 V ρ (ys.getD i default) = interp2 V ρ (xs.getD i default) :=
    fun i hi => hplain rfl i hi (by omega)
  -- the index pin: the constructor's index values at the fields are the
  -- application's index arguments
  have hpin : ∀ i, i < p.nIdx →
      interp2 V (consList (ys.map (interp2 V ρ)) ρ) ((esF j ψR).getD i default)
        = interp2 V ρ (xs.getD (p.nP + 1 + ctorsA.length + i) default) := by
    intro i hi
    obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcarInterp⟩ := hidx
    rcases hcarLen with hcase | hcarLen
    · omega
    have hrest : restC = Lech.SetP.AVExpr.instSeq ys (p.nP + cA.2 - 1)
        (ctorBodyAVI m₂ p.cvT.name p.nP cA.2 ψC (esF j ψR)) := by
      have hfit := hfitC
      rw [hTVja'] at hfit
      exact teleFitPA_rest_eq (p.nP + cA.2) hteleC (by simpa using hyl) hfit
    have hrest2 : AVExpr.mkAppN Ha cargsa
        = AVExpr.mkAppN (Lech.SetP.AVExpr.instSeq ys (p.nP + cA.2 - 1) (m₂.acval p.cvT.name ψC))
            ((paramBvars p.nP cA.2 ++ esF j ψR).map (Lech.SetP.AVExpr.instSeq ys (p.nP + cA.2 - 1))) := by
      rw [← hrestEq, hrest]
      unfold ctorBodyAVI
      rw [instSeqP_mkAppN]
    have hlenE := hCD.lenE ψR
    obtain ⟨-, hcargs⟩ := AVExpr.mkAppN_inj hrest2
      (by simp [hcarLen, paramBvars, hlenE]; omega)
    have hcel : cargsa.getD (p.nP + i) default
        = Lech.SetP.AVExpr.instSeq ys (p.nP + cA.2 - 1) ((esF j ψR).getD i default) := by
      have h1 := congrArg (fun l => l[p.nP + i]?) hcargs
      simp only [List.getElem?_map, List.getElem?_append_right (show (paramBvars p.nP cA.2).length ≤ p.nP + i
        by simp [paramBvars]), show (paramBvars p.nP cA.2).length = p.nP by simp [paramBvars],
        Nat.add_sub_cancel_left] at h1
      rw [List.getD_eq_getElem?_getD, h1, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some, Option.getD_some]
    have hcar := hcarInterp i (by omega)
    rw [hcel, show p.nP + cA.2 - 1 = ys.length - 1 from by rw [hyl], interp2_instSeq, hrP] at hcar
    rw [← hcar]
    unfold chainP
    rw [consN_eq_consList]
  -- the law's two halves
  have hlenCds : (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0).length = ctorsA.length :=
    fixCtorDataList_length _ _ _ _ _ _ _
  have hjd : (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0)[j]?
      = some (cA.1.name, cA.2, dsF j ψR, esF j ψR, Lech.recIdxOf (ksF j), eissF j ψR) := by
    rw [fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl
  have hFsj : (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0))[j]?
      = some (((dsF j ψR).drop p.nP).map (·.2.2)) := by
    rw [fssOfR_getElem?, hjd]; rfl
  have hEsj : (essOfR (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0))[j]? = some (esF j ψR) := by
    rw [essOfR_getElem?, hjd]; rfl
  have hEisj : (eissOfR (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0)).getD j [] = eissF j ψR := by
    rw [List.getD_eq_getElem?_getD, eissOfR_getElem?, hjd]; rfl
  have hrssj : (rssOfK ksF ctorsA.length).getD j [] = rsOf (ksF j) := rssOfK_getD hjn
  have hlenPps : ((ppsAll ψR).take p.nP).length = p.nP := by
    rw [List.length_take, hFD.len ψR]; omega
  have hlenIps : ((ppsAll ψR).drop p.nP).length = p.nIdx := by
    rw [List.length_drop, hFD.len ψR]; omega
  have hokFss : ∀ ρp : Nat → V,
      Sat2 V ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψR).take p.nP).map (·.2.2)).reverse) ρp →
      SumFieldsOkB (p.resSort.eval ψR) ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0)) := by
    intro ρp hρ
    unfold fixRdsAV at hρ
    rw [fixRecDataAV_take_nP hlenPps] at hρ
    exact hokFssH ψR ρp hρ
  have hcore := fixRecLawCore (hpre ψR) (n := ctorsA.length) (nF := cA.2) (nIdx := p.nIdx) (j := j)
    (by rw [fssOfR_length, hlenCds]) (by rw [List.length_map, hlenIps]) (hCD.len ψR) hjn hFsj hEsj
    (hCD.lenE ψR) (R := A ψR) (by rw [hA ψR]) (hAcl ψR) hokFss
    (lds := fixRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx (Lech.directElimLevel p.elim p.large)
      ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP) (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0)
      (dsF j ψR))
    (by rw [fixRuleDataAV_map_dom hlenPps hlenIps, hlenCds]; rfl)
    (Ra := mkLamsAV (fixRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx
        (Lech.directElimLevel p.elim p.large) ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP)
        (fixCtorDataList dsF esF ksF eissF ψR ctorsA 0) (dsF j ψR))
      (fixRuleCoreAV (A ψR) p.nP cA.2 ctorsA.length j (Lech.recIdxOf (ksF j)) (eissF j ψR)))
    (by rw [hEisj, hrssj, ← recIdx_rsOf, hD.ksLen]) (hRuleOk ψR) (by rw [hxl, hmI])
    (by simpa using hyl) hspR hspC hplain' hpin
  try simp only [RecRule.ctor, RecRule.ctorParams] at hcore ⊢
  rw [hleafR₂, hleafC₂, hrP]
  exact hcore


/-! ## The stage -/

/-- The recursor leaf of a recursive block at an assignment. -/
def fixLeafAV {env : Env} (m : EnvS2Core V env) (p : DirectFixParts)
    (ppsAll : (Name → Nat) → List (Nat × Nat × AVExpr))
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (esF : Nat → (Name → Nat) → List AVExpr) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AVExpr)) (ctorsA : List (ConstantVal × Nat))
    (sAV : (Name → Nat) → Nat) (ψ : Name → Nat) : AVExpr :=
  directFixRecAVI ((Lech.directElimLevel p.elim p.large).eval ψ) (p.resSort.eval ψ) p.nP
    (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
    (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) (((ppsAll ψ).drop p.nP).map (·.2.2))
    (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
    (fixRdsAV m p ppsAll dsF esF ksF eissF ctorsA ψ) (sAV ψ)

set_option maxHeartbeats 12800000 in
/-- **The P step at the recursive recursor's cons.** -/
theorem stageFixRec (hE : Lech.EtaFamiliesClosed env)
    (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectFixParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {mI rP : Nat}
    (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    (hmIp : p.majorIdx = mI) (hrPp : p.rulePrefix = rP)
    (hRec : Lech.checkDirectFixRec (Lech.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    {bsT : List (Name × Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    {caps : IndCaps}
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hcapsE : caps.eta = false) (hcapsU : caps.unitlike = false)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    (helim : p.large = true → p.elim ∈ p.cvR.levelParams)
    (hRlps' : ∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    {env₀ : Env} {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AVExpr)}
    (hlenK : p.kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt mp.base2 env₀ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF i cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    {uAV : (Name → Nat) → Nat} {fssZ : (Name → Nat) → List (List AVExpr)}
    (_hUparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) → uAV ψ₁ = uAV ψ₂)
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directFixTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (((ppsAll ψ).drop p.nP).map (·.2.2))
          (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
          (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hframes : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
        (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) ∧
      ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) p.nIdx
          (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
          (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)))
        (uAV ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
        (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
        (fssZ ψ)
        (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
        (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        FieldsOkB (p.resSort.eval ψ) ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) ∧
        ∀ bs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) bs →
          (∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j [],
            AnnotOk2 V (consList bs ρp) E) ∧
          SpineFit ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
            (idxValsAt ρp ((essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) bs)) ∧
      SumFieldsValid ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        ∀ i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j [])
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).length,
        ∀ fs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) fs →
        ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).getD i [],
          AnnotValidV V (consList (fs.take i) ρp) E) ∧
      (∀ j, j < ctorsA.length →
        ∀ bs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) bs →
        ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j [],
          AnnotValidV V (consList bs ρp) E))
    (hwl : p.large = true → p.resSort.isNeverZero = true) :
    ∃ (sAV : (Name → Nat) → Nat)
      (mp' : EnvS2PM V μ ⟨.recInfo cvRa mI rP (Lech.directSumRules p.nP mI rP cvRa.type ctorsA rhss)
        :: env.consts⟩),
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name
        (fixLeafAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA sAV) := by
  -- the data, the openings
  obtain ⟨hRD, u, hsort⟩ := fixRecData_of hμ mp hRec hfT hlpsT hstripT hopT hFD hlenK hks hcf
  obtain ⟨fvsR, oR, hR⟩ := fixRecOpenedAll mp hRec hstripT hlenK hRD
  -- the constant's facts
  obtain ⟨cvRi, recTy, sty, u', hccv, -, htp, htrR, -, -, -, -, -, -, hcvRa⟩ :=
    Lech.checkDirectFixRec_shape hRec
  obtain ⟨hfind, hnres, hpshape, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    Lech.checkConstantVal_inv hccv
  have hRname : cvRa.name = p.cvR.name := by rw [hcvRa]
  have hRlps : cvRa.levelParams = p.cvR.levelParams := by rw [hcvRa]
  have hRtype : cvRa.type = recTy := by rw [hcvRa]
  have hfresh : env.find? cvRa.name = none := by rw [hRname]; exact hfind
  have htrR' : cvRa.type.constsResolve env = true := by rw [hRtype]; exact htrR
  have hcbR : ConstsBound env cvRa.type := constsBound_of_constsResolve _ htrR'
  have hwf := Lech.direct_fix_rec_wf (mode := μ) mp.base2.wf hRec
  rw [hmIp, hrPp] at hwf
  have hTR : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  -- names
  generalize hElimL : Lech.directElimLevel p.elim p.large = elimL at hRD hR hleafC ⊢
  let sAV : (Name → Nat) → Nat := fixSortAV elimL u cvRa.levelParams
  let A : (Name → Nat) → AVExpr := fixLeafAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA sAV
  have hrdsE : ∀ ψ, fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ
      = fixRecDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ((ppsAll ψ).take p.nP)
          ((ppsAll ψ).drop p.nP) (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0) := by
    intro ψ; unfold fixRdsAV; rw [hElimL]
  have hA : ∀ ψ, A ψ = directFixRecAVI (elimL.eval ψ) (p.resSort.eval ψ) p.nP
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) (((ppsAll ψ).drop p.nP).map (·.2.2))
      (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ) (sAV ψ) := by
    intro ψ
    show fixLeafAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA sAV ψ = _
    unfold fixLeafAV
    rw [hElimL]
  -- the block's lengths and the per-constructor pins
  have hn : ∀ ψ, (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0).length = ctorsA.length :=
    fun ψ => fixCtorDataList_length _ _ _ _ _ _ _
  have hlenPps : ∀ ψ, ((ppsAll ψ).take p.nP).length = p.nP := fun ψ => by
    rw [List.length_take, hFD.len ψ]; omega
  have hlenIps : ∀ ψ, ((ppsAll ψ).drop p.nP).length = p.nIdx := fun ψ => by
    rw [List.length_drop, hFD.len ψ]; omega
  have hlenIds : ∀ ψ, ((((ppsAll ψ).drop p.nP).map (·.2.2))).length = p.nIdx := fun ψ => by
    rw [List.length_map, hlenIps]
  have hlenFs : ∀ ψ, (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).length = ctorsA.length :=
    fun ψ => by rw [fssOfR_length, hn]
  have hlenEs : ∀ ψ, (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).length = ctorsA.length :=
    fun ψ => by rw [essOfR_length, hn]
  have hjd : ∀ ψ j cA, ctorsA[j]? = some cA →
      (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)[j]?
        = some (cA.1.name, cA.2, dsF j ψ, esF j ψ, Lech.recIdxOf (ksF j), eissF j ψ) := by
    intro ψ j cA hj
    rw [fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl
  have hFsjD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []
        = ((dsF j ψ).drop p.nP).map (·.2.2) := by
    intro ψ j cA hj
    rw [List.getD_eq_getElem?_getD, fssOfR_getElem?, hjd ψ j cA hj]; rfl
  have hEsjD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j [] = esF j ψ := by
    intro ψ j cA hj
    rw [List.getD_eq_getElem?_getD, essOfR_getElem?, hjd ψ j cA hj]; rfl
  have hEisjD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j [] = eissF j ψ := by
    intro ψ j cA hj
    rw [List.getD_eq_getElem?_getD, eissOfR_getElem?, hjd ψ j cA hj]; rfl
  have hcAof : ∀ j, j < ctorsA.length → ∃ cA, ctorsA[j]? = some cA :=
    fun j hj => ⟨_, List.getElem?_eq_getElem hj⟩
  -- the elimination level's bit and zeroness
  have hbz : ∀ ψ, elimL.eval ψ = 0 ↔ pwBit ψ (Level.zeronessOf elimL) = 0 := by
    intro ψ
    rw [pwBit_eq_zero_iff, Lech.PropWhen.zeronessOf_sound, beq_iff_eq]
  have hwℓ : ∀ ψ, p.resSort.eval ψ = 0 → elimL.eval ψ = 0 := by
    intro ψ hw0
    rw [← hElimL]
    cases hpl : p.large
    · simp [Lech.directElimLevel, Level.eval]
    · exact absurd hw0 (Lech.Level.isNeverZero_sound ψ _ (hwl hpl))
  have hs0 : ∀ ψ, sAV ψ = 0 ↔ elimL.eval ψ = 0 := fun ψ => fixSortAV_zero_iff elimL u _ ψ
  -- the recursor type's universe
  have hunivTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp2 V ρ (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ)
        (recConcAV ctorsA.length p.nIdx)) ∈ˢ (univ (sAV ψ) : V) := by
    intro ψ ρ
    show _ ∈ˢ (univ (fixSortAV elimL u cvRa.levelParams ψ) : V)
    unfold fixSortAV
    split
    · next h0 =>
      rw [univ_zero]
      have hlen := hRD.len ψ
      cases hrds : fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ with
      | nil => rw [hrds] at hlen; simp at hlen
      | cons d rest =>
        show piR d.2.1 _ _ ∈ˢ _
        have hd0 : d.2.1 = 0 := (hRD.bits ψ d (by rw [hrds]; exact List.mem_cons_self)).mp h0
        rw [hd0]
        exact piR_zero_mem_univZero
    · next h0 =>
      have hagree := restrictΨ_agree cvRa.levelParams ψ
      have hrdsEq := hRD.params (restrictΨ cvRa.levelParams ψ) ψ hagree
      have := hsort (restrictΨ cvRa.levelParams ψ) ρ
      rw [hrdsEq] at this
      exact univ_mono (Nat.le_max_right 1 _) _ this
  -- the frames at a parameter valuation, in `fixPre_of`'s shape
  have hframes' : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V ((((ppsAll ψ).take p.nP).map (·.2.2)).reverse) ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
        (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) ∧
      ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) p.nIdx
          (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
          (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)))
        (uAV ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
        (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
        (fssZ ψ)
        (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
        (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        FieldsOkB (p.resSort.eval ψ) ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) ∧
        ∀ bs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) bs →
          (∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j [],
            AnnotOk2 V (consList bs ρp) E) ∧
          SpineFit ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
            (idxValsAt ρp ((essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) bs)) ∧
      (∀ σ : Nat → V, interp2 V σ (mp.base2.acval p.cvT.name ψ)
        = interp2 V (fun k => ρp (k + p.nP))
            (directFixTyAVI (uAV ψ) (p.resSort.eval ψ) ((ppsAll ψ).take p.nP ++ (ppsAll ψ).drop p.nP)
              (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
              (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
              (fssZ ψ)
              (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)))) ∧
      (∀ j cd, (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)[j]? = some cd →
        ∀ (M : V) (ms : List V), ms.length = j →
        interp2 V (consList ms (cons M ρp))
            (minorAVAtR mp.base2 cd.1 ψ p.nP cd.2.1 (pwBit ψ (Level.zeronessOf elimL)) (1 + j)
              cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1 cd.2.2.2.2.2)
          = minorSpI (elimL.eval ψ) (fun fs => ihSpL (elimL.eval ψ)
              (concI (p.resSort.eval ψ) ρp M ((essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) j fs)
              (ihDomsI ρp M (rssOfK ksF ctorsA.length) (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
                (fun j' => ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j' []).length) j fs))
            ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) ρp []) := by
    intro ψ ρp hρp
    obtain ⟨hX, hreal, hfields, hv, hEisV, hEsV⟩ := hframes ψ ρp hρp
    have hokB : SumFieldsOkB (p.resSort.eval ψ) ρp
        (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) := by
      intro Fs hFs
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs
      have hjn : j < ctorsA.length := by
        rw [← hlenFs ψ]; exact (List.getElem?_eq_some_iff.mp hj).1
      have := (hfields j hjn).1
      rwa [List.getD_eq_getElem?_getD, hj] at this
    refine ⟨hX, hreal, hfields, ?_, ?_⟩
    · intro σ
      rw [List.take_append_drop, interp2_closed (V := V) (mp.base2.cval_closedL p.cvT.name ψ) σ
        (fun k => ρp (k + p.nP)), hleafT ψ]
    · intro j cd hcd M ms hlenM
      have hjn : j < ctorsA.length := by
        rw [← hn ψ]; exact (List.getElem?_eq_some_iff.mp hcd).1
      obtain ⟨cA, hj⟩ := hcAof j hjn
      obtain rfl := Option.some.inj ((hjd ψ j cA hj).symm.trans hcd)
      obtain ⟨-, -, hD⟩ := hcf j cA hj
      have hrss : Lech.recIdxOf (ksF j) = recIdx ((rssOfK ksF ctorsA.length).getD j []) cA.2 := by
        rw [rssOfK_getD hjn, ← hD.ksLen, recIdx_rsOf]
      show interp2 V (consList ms (cons M ρp))
        (minorAVAtR mp.base2 cA.1.name ψ p.nP cA.2 _ (1 + j) (dsF j ψ) (esF j ψ)
          (Lech.recIdxOf (ksF j)) (eissF j ψ)) = _
      rw [hrss, ← hEisjD ψ j cA hj, hEsjD ψ j cA hj, hFsjD ψ j cA hj]
      exact interp_minorAVAtR (hbz ψ) hlenM (hD.len ψ) (hleafC j cA hj ψ)
        (mp.base2.cval_closedL cA.1.name ψ) (by rw [fssOfR_getElem?, hjd ψ j cA hj]; rfl) hokB
        ((hiff j cA hj ψ ρp).mp hρp)
  -- the per-field data's pins
  have hEs : ∀ ψ j, j < ctorsA.length →
      ((essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).length = p.nIdx := by
    intro ψ j hj
    obtain ⟨cA, hjA⟩ := hcAof j hj
    rw [hEsjD ψ j cA hjA]
    exact (hcf j cA hjA).2.2.lenE ψ
  have hEisLen : ∀ ψ j i, i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j [])
      ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).length →
      (((eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).getD i []).length = p.nIdx := by
    intro ψ j i hi
    by_cases hj : j < ctorsA.length
    · obtain ⟨cA, hjA⟩ := hcAof j hj
      obtain ⟨-, -, hD⟩ := hcf j cA hjA
      rw [rssOfK_getD hj, hFsjD ψ j cA hjA, List.length_map, List.length_drop, hD.len ψ,
        Nat.add_sub_cancel_left, ← hD.ksLen, recIdx_rsOf, mem_recIdxOf] at hi
      rw [hEisjD ψ j cA hjA]
      exact hD.eisLen ψ i hi.2 (by rw [← hD.ksLen]; exact hi.1)
    · exfalso
      have h0 : (rssOfK ksF ctorsA.length).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [rssOfK]; omega)]; rfl
      rw [h0] at hi
      obtain ⟨-, hr⟩ := mem_recIdx.mp hi
      simp at hr
  have hEbelow : ∀ ψ j i, ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).getD i [],
      VExpr.bvarsBelow (p.nP + i) E.erase := by
    intro ψ j i E hE
    by_cases hj : j < ctorsA.length
    · obtain ⟨cA, hjA⟩ := hcAof j hj
      rw [hEisjD ψ j cA hjA] at hE
      exact (hcf j cA hjA).2.2.eissBelow ψ i E hE
    · exfalso
      have h0 : (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [eissOfR_length, hn]; omega)]; rfl
      rw [h0] at hE
      simp at hE
  -- the premise, the leaf's facts, the leaf's closedness
  have hpre : ∀ ψ, FixPre V (elimL.eval ψ) (p.resSort.eval ψ) (uAV ψ) p.nP
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (fssZ ψ)
      (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
      (eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0))
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ) (sAV ψ) := by
    intro ψ
    rw [hrdsE ψ]
    refine fixPre_of rfl rfl (hbz ψ) (hwℓ ψ) (hs0 ψ) (hlenPps ψ) (hlenIps ψ) (hn ψ) (hlenFs ψ)
      (hlenEs ψ) (hEs ψ) (hEisLen ψ) (hEbelow ψ) ?_ ?_ ?_ ?_ (hframes' ψ)
    · have := hRD.below ψ; rw [hrdsE ψ] at this; exact this
    · have := (hR ψ).okΓ; rw [hrdsE ψ] at this; exact this
    · intro ρ; have := (hRD.okTy ψ ρ).1; rw [hrdsE ψ] at this; exact this
    · intro ρ; have := hunivTy ψ ρ; rw [hrdsE ψ] at this; exact this
  have hokΓ : ∀ ψ, ∀ i, i < p.nP + ctorsA.length + p.nIdx + 2 → ∀ ρ : Nat → V,
      Sat2 V ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ).map (·.2.2)).reverse).drop
        (p.nP + ctorsA.length + p.nIdx + 2 - i)) ρ →
      AnnotOkP V ρ ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ).map (·.2.2)).reverse).getD
        (p.nP + ctorsA.length + p.nIdx + 2 - 1 - i) default) := fun ψ => (hR ψ).okΓ
  have hvFss : ∀ ψ ρp, Sat2 V ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ).take p.nP).map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length → ∀ bs : List V,
        SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) bs →
        ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j [],
          AnnotValidV V (consList bs ρp) E) ∧
      (∀ j, j < ctorsA.length → ∀ i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j [])
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).length,
        ∀ fs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []) fs →
        ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).getD i [],
          AnnotValidV V (consList (fs.take i) ρp) E) := by
    intro ψ ρp hρ
    rw [hrdsE ψ, fixRecDataAV_take_nP (hlenPps ψ)] at hρ
    obtain ⟨-, -, -, hv, hEisV, hEsV⟩ := hframes ψ ρp hρ
    exact ⟨hv, hEsV, hEisV⟩
  have hleafF : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkP V ρ (A ψ) ∧
      interp2 V ρ (A ψ) ∈ˢ interp2 V ρ (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ)
        (recConcAV ctorsA.length p.nIdx)) := by
    intro ψ ρ
    rw [hA ψ]
    exact fixRecLeafFacts (hpre ψ) (hlenFs ψ) (hlenIds ψ) (hokΓ ψ) (fun ρ' => (hRD.okTy ψ ρ').2)
      (hvFss ψ) ρ
  have hAcl : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase := by
    intro ψ
    rw [hA ψ]
    refine directFixRecAVI_below 0 (hRD.below ψ) (by rw [hRD.len ψ, hlenFs ψ, hlenIds ψ]; omega) rfl ?_
      (hEbelow ψ)
    -- the restricted chains are bounded
    have hFssB : ∀ Fs ∈ fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0), FieldsBelow (0 + p.nP) Fs := by
      intro Fs hFs
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs
      have hjn : j < ctorsA.length := by rw [← hlenFs ψ]; exact (List.getElem?_eq_some_iff.mp hj).1
      obtain ⟨cA, hjA⟩ := hcAof j hjn
      have hFj := hFsjD ψ j cA hjA
      rw [List.getD_eq_getElem?_getD, hj, Option.getD_some] at hFj
      rw [hFj]
      exact (DomsBelow.drop p.nP ((hcf j cA hjA).2.2.below ψ)).fields
    have hEssB : ∀ j, j < (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).length →
        ((essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).length = p.nIdx ∧
        ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j [],
          VExpr.bvarsBelow (0 + p.nP + ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)).getD j []).length)
            E.erase := by
      intro j hj
      rw [hlenFs ψ] at hj
      obtain ⟨cA, hjA⟩ := hcAof j hj
      obtain ⟨-, -, hD⟩ := hcf j cA hjA
      rw [hEsjD ψ j cA hjA, hFsjD ψ j cA hjA]
      refine ⟨hD.lenE ψ, fun E hE => ?_⟩
      have := hD.belowE ψ E hE
      rwa [show 0 + p.nP + (((dsF j ψ).drop p.nP).map (·.2.2)).length = p.nP + cA.2 from by
        simp [hD.len ψ]]
    intro Fs' hFs'
    rw [hlenIds ψ, hlenFs ψ] at hFs'
    have := rChains_below (d := p.nIdx + ctorsA.length + 1) (by omega) hFssB
      (fun j hj => hEssB j hj) Fs' hFs'
    refine fieldsBelow_mono (by rw [hlenIds ψ, hlenFs ψ]; omega) this
  -- the rule right-hand sides' gradedness
  have hRuleOk : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkLamsAV (fixRuleDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx elimL
          ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP)
          (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0) (dsF j ψ))
        (fixRuleCoreAV (A ψ) p.nP cA.2 ctorsA.length j (Lech.recIdxOf (ksF j)) (eissF j ψ))) := by
    intro j cA hj ψ ρ
    obtain ⟨-, -, hD⟩ := hcf j cA hj
    have hjn : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
    have hrss : Lech.recIdxOf (ksF j) = recIdx ((rssOfK ksF ctorsA.length).getD j []) cA.2 := by
      rw [rssOfK_getD hjn, ← hD.ksLen, recIdx_rsOf]
    have hpre' := hpre ψ
    rw [hrdsE ψ] at hpre'
    refine fixRuleOkP rfl rfl (hbz ψ) (hlenPps ψ) (hlenIps ψ) (hn ψ) (hlenFs ψ) (hlenEs ψ) (hEs ψ)
      (hEisLen ψ) hpre' ?_ (by rw [hA ψ, hrdsE ψ]) (hAcl ψ) (fun ρ' => (hleafF ψ ρ').1) (hframes' ψ)
      (fun ρp hρp => ⟨(hframes ψ ρp hρp).2.2.2.1, (hframes ψ ρp hρp).2.2.2.2.1⟩)
      (hjd ψ j cA hj) (hD.len ψ) (by rw [fssOfR_getElem?, hjd ψ j cA hj]; rfl)
      (by rw [essOfR_getElem?, hjd ψ j cA hj]; rfl) hrss (hEisjD ψ j cA hj) (hleafC j cA hj ψ)
      (mp.base2.cval_closedL cA.1.name ψ) (hiff j cA hj ψ) ρ
    have := hokΓ ψ; rw [hrdsE ψ] at this; exact this
  -- the leaf's level dependence
  have hAparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvRa.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂ := by
    intro ψ₁ ψ₂ hφ
    have hlpsAll : ∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q :=
      fun q hq => hφ q (by rw [hRlps]; exact hRlps' q hq)
    have hcds : fixCtorDataList dsF esF ksF eissF ψ₁ ctorsA 0
        = fixCtorDataList dsF esF ksF eissF ψ₂ ctorsA 0 := by
      refine fixCtorDataList_congr ctorsA 0 fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ := hcAof i hi
      obtain ⟨-, hlpsi, hDi⟩ := hcf i cAi hi'
      have hag : ∀ q ∈ cAi.1.levelParams, ψ₁ q = ψ₂ q := fun q hq => hlpsAll q (by rw [← hlpsi]; exact hq)
      exact ⟨(hDi.params ψ₁ ψ₂ hag).1, (hDi.params ψ₁ ψ₂ hag).2, hDi.eissParams ψ₁ ψ₂ hag⟩
    have hpps : ppsAll ψ₁ = ppsAll ψ₂ :=
      (hFD.params ψ₁ ψ₂ (fun q hq => hlpsAll q (by rw [← hlpsT]; exact hq))).1
    have hw : p.resSort.eval ψ₁ = p.resSort.eval ψ₂ :=
      (hFD.params ψ₁ ψ₂ (fun q hq => hlpsAll q (by rw [← hlpsT]; exact hq))).2
    have hℓ : elimL.eval ψ₁ = elimL.eval ψ₂ := by
      rw [← hElimL]
      cases hpl : p.large
      · simp [Lech.directElimLevel, Level.eval]
      · simp only [Lech.directElimLevel, if_true, Level.eval]
        exact hφ p.elim (by rw [hRlps]; exact helim hpl)
    have hs : sAV ψ₁ = sAV ψ₂ := by
      show fixSortAV elimL u cvRa.levelParams ψ₁ = fixSortAV elimL u cvRa.levelParams ψ₂
      unfold fixSortAV
      rw [hℓ, restrictΨ_congr hφ]
    rw [hA ψ₁, hA ψ₂, hℓ, hw, hcds, hpps, hRD.params ψ₁ ψ₂ hφ, hs]
  -- the cons head
  let c₀ : ConstantInfo := .recInfo cvRa mI rP (Lech.directSumRules p.nP mI rP cvRa.type ctorsA rhss)
  have hcross : ∀ e : Expr, ConsCrossAt c₀ e := fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hreadR : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval cvRa.name A) ⟨c₀ :: env.consts⟩ ψ 0 cvRa.type
        = some (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF ctorsA ψ)
            (recConcAV ctorsA.length p.nIdx)) := fun ψ =>
    denoteP_cons_mono (c₀ := c₀) hfresh (hcross _) ψ 0 hcbR (hRD.read ψ)
  have hnresC : Lech.reservedBasisNames.contains c₀.name = false := by
    show Lech.reservedBasisNames.contains cvRa.name = false
    rw [hRname]; exact hnres
  have hpshapeC : c₀.name.isProjFnShape = false := by
    show cvRa.name.isProjFnShape = false
    rw [hRname]; exact hpshape
  refine ⟨sAV, ?_⟩
  refine declStepPM_of_ind_rec_cons mp (c₀ := c₀) (A := A) hfresh hnresC ⟨_, _, _, _, rfl⟩
    (ConsHeadP.ofFresh hwf (fun ψ => hAcl ψ) hnresC
      (fun _ h => nomatch h)
      (fun cvR' mI' rP' rules heq r hr => by
        injection heq with _ _ _ hrules
        subst hrules
        obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Lech.directSumRules_getElem? hr
        obtain ⟨hf, -, -⟩ := hcf j cA hj
        exact ⟨cA.1, p.nP, cA.2, hf⟩))
    (fun ψ k => AVExpr.liftN_eq_self _ (VExpr.bvarsBelow.mono (Nat.zero_le k) (hAcl ψ)) 1)
    hAparams (fun ψ ρ => (hleafF ψ ρ).1.1) (fun ψ ρ => (hleafF ψ ρ).1.2) (fun ψ => ⟨_, hreadR ψ⟩)
    ?_ ?_ ?_ ?_
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadR ψ).symm.trans hta)
    exact hRD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadR ψ).symm.trans hta)
    exact (hleafF ψ ρ).2
  · -- `caps_ok`: the block claims no eta or unit law
    intro m₂ hac
    refine capsOkP_cons_direct mp (c₀ := c₀) (A := A) (T := p.cvT.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h) ?_ m₂ hac ?_
    · intro T' cvT' caps' hf hne hres hcape
      exact hE T' cvT' caps' hf hcape hres
    · intro cvT caps' hf _
      have hfT' : (⟨c₀ :: env.consts⟩ : Env).find? p.cvT.name = some (.indInfo cvTa caps) := by
        rw [Lech.Env.find?_cons, if_neg (fun h => hTR h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      exact ⟨fun he => absurd (hcapsE.symm.trans he) Bool.false_ne_true,
        fun hu => absurd (hcapsU.symm.trans hu) Bool.false_ne_true⟩
  · -- `rec_rules`
    intro m₂ hac φ'
    refine recRulesP_cons_rec mp (c₀ := c₀) (A := A) hfresh rfl m₂ hac φ' ?_
    intro rl hrl hfire
    obtain ⟨j, cA, rhs, hj, hrhs, rfl⟩ := Lech.directSumRules_getElem? hrl
    by_cases hplain : Expr.recRulePlain cvRa.type mI rP p.nP = true
    · have hrule : (⟨cA.1.name, cA.2, p.nP,
          if Expr.recRulePlain cvRa.type mI rP p.nP then .plain else .inert, rhs⟩ : RecRule)
          = ⟨cA.1.name, cA.2, p.nP, .plain, rhs⟩ := by
        simp [hplain]
      subst hElimL
      exact fixRecRuleLaw mp hmI hrP hRec hfT hlpsT hstripT hopT hFD hlenK hks hcf hidxRes hRD
        hA hpre hAcl (fun ψ ρp hρp => by
          intro Fs hFs
          obtain ⟨j', hj'⟩ := List.getElem?_of_mem hFs
          have hjn' : j' < ctorsA.length := by
            rw [← hlenFs ψ]; exact (List.getElem?_eq_some_iff.mp hj').1
          have := ((hframes ψ ρp hρp).2.2.1 j' hjn').1
          rwa [List.getD_eq_getElem?_getD, hj'] at this)
        hleafC hj hrhs (hRuleOk j cA hj) hfresh hrule m₂ hac φ'
    · exfalso
      apply hfire
      simp [hplain]

end Lech.SetP
