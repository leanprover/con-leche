import Setlec.SetP.DirectSum.SumRecLawP
import Setlec.SetP.DirectSum.SumStageCtorP

/-!
# The sum recursor's cons (task #175 sum-types)

`stageSumRec`: the P step at the sum recursor's cons.  The stored
recursor is the generated one: its data is read off syntactically
(`sumRecData_of`), its leaf is `directSumRecAV` over that data and
the field chains, the frames' walks (`sumRecLeafFacts` over
`sumRecFrames`) give the leaf's grading and membership, the
capability laws are vacuous (the former is stored with the empty
record), and every stored rule's law is `sumRecRuleLaw` over the
generated rule at its constructor's position (an inert rule owes
nothing).
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The rule data's shape -/

/-- The rule's λ-domains are the recursor's parameter, motive and
minor domains followed by the constructor's field domains lifted
`n + 1` under. -/
theorem sumRuleDataAV_map_dom {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat}
    {nP : Nat} {ℓ : Level} {pps ds : List (Nat × Nat × AVExpr)}
    {cds : List (Name × Nat × List (Nat × Nat × AVExpr))} :
    (sumRuleDataAV m T ψ nP ℓ pps cds ds).map (·.2)
      = ((rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
          [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAV m T ψ nP ℓ)] ++
          sumMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1).map
            (fun d : Nat × Nat × AVExpr => d.2.2)) ++
        (liftDoms (cds.length + 1) 0 (ds.drop nP)).map (fun d : Nat × Nat × AVExpr => d.2.2) := by
  unfold sumRuleDataAV
  rw [List.map_map, List.map_append]
  have h : ((fun x : Nat × AVExpr => x.2) ∘ fun d : Nat × Nat × AVExpr => (d.2.1, d.2.2))
      = fun d : Nat × Nat × AVExpr => d.2.2 := rfl
  rw [h, rebit_map_dom]

theorem mem_sumRuleDataAV_bit {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat}
    {nP : Nat} {ℓ : Level} {pps ds : List (Nat × Nat × AVExpr)}
    {cds : List (Name × Nat × List (Nat × Nat × AVExpr))} {d : Nat × AVExpr}
    (hd : d ∈ sumRuleDataAV m T ψ nP ℓ pps cds ds) : d.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  unfold sumRuleDataAV at hd
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
  simp only [List.mem_append, List.mem_singleton] at hd'
  rcases hd' with ((h | rfl) | h) | h
  · exact mem_rebit h
  · rfl
  · exact mem_sumMinorsData h
  · exact mem_rebit h

/-- The recursor data's length. -/
theorem sumRdsAV_length {m : EnvS2Core V env} {p : DirectSumParts}
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)} {ctorsA : List (ConstantVal × Nat)}
    {cvTa : ConstantVal} (hFD : FormerData m cvTa p.nP p.resSort pps) (ψ : Name → Nat) :
    (sumRdsAV m p pps dsF ctorsA ψ).length = p.nP + ctorsA.length + 2 := by
  simp only [sumRdsAV, sumRecDataAV, List.length_append, rebit_length, hFD.len ψ,
    List.length_singleton, sumMinorsData_length, ctorDataList_length]
  omega

/-! ## The per-constructor facts across a cons -/

/-- The constructors' facts cross a cons whose head is fresh and is
not the block's former nor a constructor. -/
theorem ctorFactsAt_cross {m : EnvS2Core V env} {T : Name} {lps : List Name} {nP : Nat}
    {resSort : Level} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {ctorsA : List (ConstantVal × Nat)}
    (hcf : ∀ j cA, ctorsA[j]? = some cA → CtorFactsAt m T lps nP resSort dsF j cA)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    ∀ j cA, ctorsA[j]? = some cA → CtorFactsAt m₂ T lps nP resSort dsF j cA := by
  intro j cA hj
  obtain ⟨hf, hlps, hstrip, hCD⟩ := hcf j cA hj
  have hcb : ConstsBound env cA.1.type :=
    constsBound_of_constsResolve _ (m.wf _ (Setlec.Semantics.Env.find?_mem hf)).2.2.1
  exact ⟨Setlec.Env.find?_cons_of_fresh hfresh hf, hlps, hstrip,
    hCD.cross hfresh hT (ConsCrossAt.ofNtc hntc) hcb m₂ hac⟩

/-! ## The rule law -/

set_option maxHeartbeats 6400000 in
/-- **The direct sum block's rule `j` fires at the readings.** -/
theorem sumRecRuleLaw (mp : EnvS2PM V μ env)
    {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {mI : Nat} (hmI : mI = p.nP + 1 + ctorsA.length)
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa {}))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.resSort dsF j cA)
    (hRD : SumRecData mp.base2 cvRa p.nP ctorsA.length (sumElimLevel p)
      (sumRdsAV mp.base2 p pps dsF ctorsA))
    {fvsR : List Expr} {oR : Expr}
    (hR : ∀ ψ : Name → Nat,
      OpenedP mp.base2 ψ (p.nP + ctorsA.length + 2) cvRa.type fvsR oR
        (((sumRdsAV mp.base2 p pps dsF ctorsA ψ).map (·.2.2)).reverse)
        (.app (.bvar (ctorsA.length + 1)) (.bvar 0)))
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (pps ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)))
    (hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2)
    (hn1 : ctorsA.length ≠ 1)
    {j : Nat} {cA : ConstantVal × Nat} (hj : ctorsA[j]? = some cA) {rhs : Expr}
    (hRuleRead : ∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 rhs
      = some (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψ p.nP (sumElimLevel p) (pps ψ)
          (ctorDataList dsF ψ ctorsA 0) (dsF j ψ)) (sumRuleCoreAV cA.2 ctorsA.length j)))
    (hRuleOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψ p.nP (sumElimLevel p) (pps ψ)
          (ctorDataList dsF ψ ctorsA 0) (dsF j ψ)) (sumRuleCoreAV cA.2 ctorsA.length j)))
    (hrhsRes : rhs.constsResolve env = true)
    (hRres : cvRa.type.constsResolve env = true)
    (hfresh : env.find? cvRa.name = none)
    {rule : RecRule} (hrule : rule = ⟨cA.1.name, cA.2, p.nP, .plain, rhs⟩)
    {rules : List RecRule}
    (m₂ : EnvS2Core V ⟨.recInfo cvRa mI mI rules :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cvRa.name
      (fun ψ => directSumRecAV ((sumElimLevel p).eval ψ) (p.resSort.eval ψ)
        (sumRdsAV mp.base2 p pps dsF ctorsA ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))))
    (hAokP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (directSumRecAV ((sumElimLevel p).eval ψ) (p.resSort.eval ψ)
        (sumRdsAV mp.base2 p pps dsF ctorsA ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))))
    (φ : Name → Nat) :
    RecRuleLawP m₂ φ cvRa.name cvRa mI mI rule := by
  subst hrule
  obtain ⟨hfC, hlpsC, hstripC, hCD⟩ := hcf j cA hj
  have hjn : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  -- the constructor's stored type
  obtain ⟨-, -, hCres, -, -⟩ := mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCres
  have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ hCres
  have hcbT : ConstsBound env cvRa.type := constsBound_of_constsResolve _ hRres
  have hcbR : ConstsBound env rhs := constsBound_of_constsResolve _ hrhsRes
  have hRC : cA.1.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfC; exact nomatch hfC
  have hRT : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  -- the cons crossing
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo cvRa mI mI rules) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hfindC : (⟨.recInfo cvRa mI mI rules :: env.consts⟩ : Env).find? cA.1.name
      = some (.ctorInfo cA.1 p.nP cA.2) := by
    rw [Setlec.Env.find?_cons, if_neg (fun h => hRC h.symm)]
    exact hfC
  -- the law
  refine ⟨Nat.le_refl _, fun us hus => ?_⟩
  dsimp only
  have hinstR : ∀ (d : Nat) (e : Expr),
      denoteP m₂.acval _ φ d (e.instantiateLevelParams cvRa.levelParams us)
        = denoteP m₂.acval _ (Level.substFn φ cvRa.levelParams us) d e :=
    fun d e => denoteP_instLevels (acvalParamsAt_of_core m₂) φ d e
  generalize hψR : Level.substFn φ cvRa.levelParams us = ψR at hinstR ⊢
  -- the right-hand side's reading, at the extension
  have hRa₂ : denoteP m₂.acval ⟨.recInfo cvRa mI mI rules :: env.consts⟩ φ 0
      (rhs.instantiateLevelParams cvRa.levelParams us)
      = some (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψR p.nP (sumElimLevel p) (pps ψR)
          (ctorDataList dsF ψR ctorsA 0) (dsF j ψR)) (sumRuleCoreAV cA.2 ctorsA.length j)) := by
    rw [hinstR, hac]
    exact denoteP_cons_mono hfresh (hcross _) ψR 0 hcbR (hRuleRead ψR)
  refine ⟨_, hRa₂, hRuleOk ψR, fun _ _ h => absurd h (by simp), ?_⟩
  intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ hplain _ _ hTVa
    hTVja hfitR hfitC
  -- the constructor found is the block's
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfindC.symm.trans hfcj))
  -- the level assignments
  have hagree : ∀ q ∈ p.cvT.levelParams,
      Level.substFn φ cA.1.levelParams usj q = ψR q := by
    have h := hψ
    simp only [Setlec.recFireComparands] at h
    rw [hlpsC] at h
    rw [hlpsC, ← hψR]
    exact substFn_agree_of_comparand h
  generalize hψC : Level.substFn φ cA.1.levelParams usj = ψC at hagree hTVja hfitR hfitC ⊢
  have hdsEq : ∀ i, i < ctorsA.length → dsF i ψC = dsF i ψR := by
    intro i hi
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨-, hlpsi, -, hCDi⟩ := hcf i cAi hi'
    exact hCDi.params ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq))
  have hcdsEq : ctorDataList dsF ψC ctorsA 0 = ctorDataList dsF ψR ctorsA 0 :=
    ctorDataList_params fun i hi => by rw [Nat.zero_add]; exact hdsEq i hi
  have hdsjEq : dsF j ψC = dsF j ψR := hdsEq j hjn
  have hwEq : p.resSort.eval ψC = p.resSort.eval ψR :=
    (hFD.params ψC ψR (fun q hq => hagree q (by rw [← hlpsT]; exact hq))).2
  -- the recursor and constructor types' readings, at the extension
  have hRD₂ := hRD.cross (c₀ := .recInfo cvRa mI mI rules) hfresh (hcross _) hcbT m₂ hac
  have hCD₂ := hCD.cross (c₀ := .recInfo cvRa mI mI rules) hfresh hRT (hcross _) hcbC m₂ hac
  have hTVa' : TVa = mkPisAV (sumRdsAV mp.base2 p pps dsF ctorsA ψR)
      (.app (.bvar (ctorsA.length + 1)) (.bvar 0)) := by
    have h := hTVa
    rw [hinstR] at h
    exact Option.some.inj (h.symm.trans (hRD₂.read ψR))
  have hTVja' : TVja = mkPisAV (dsF j ψR) (ctorBodyAV m₂ p.cvT.name p.nP cA.2 ψC) := by
    have h := hTVja
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ 0 cA.1.type, hψC] at h
    have := Option.some.inj (h.symm.trans (hCD₂.read ψC))
    rw [this, hdsjEq]
  -- the constructor's leaf at the extension
  have hleafC₂ : m₂.acval cA.1.name ψC
      = directSumMkAV (p.resSort.eval ψR) j (dsF j ψR) (((dsF j ψR).drop p.nP).map (·.2.2))
          (fssOf p.nP (ctorDataList dsF ψR ctorsA 0)) := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cA.1.name ψC = _
    rw [acvalWith_ne hRC, hleafC j cA hj ψC, hdsjEq, hwEq, hcdsEq]
  have hleafR₂ : m₂.acval cvRa.name ψR
      = directSumRecAV ((sumElimLevel p).eval ψR) (p.resSort.eval ψR)
          (sumRdsAV mp.base2 p pps dsF ctorsA ψR) (fssOf p.nP (ctorDataList dsF ψR ctorsA 0)) := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cvRa.name ψR = _
    rw [acvalWith_self]
  -- the fits, as spines
  have hspR : SpineFit ρ ((sumRdsAV mp.base2 p pps dsF ctorsA ψR).map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directSumMkAV (p.resSort.eval ψR) j (dsF j ψR)
        (((dsF j ψR).drop p.nP).map (·.2.2)) (fssOf p.nP (ctorDataList dsF ψR ctorsA 0))) ys]).map
        (interp2 V ρ)) := by
    have hst := stripPisAV_mkPisAV (sumRdsAV mp.base2 p pps dsF ctorsA ψR)
      (AVExpr.app (.bvar (ctorsA.length + 1)) (.bvar 0))
    rw [hRD.len ψR] at hst
    have htele := piTeleP_of_stripPisAV hst
    have hfit := hfitR
    rw [hTVa'] at hfit
    try simp only [RecRule.ctor] at hfit
    rw [hleafC₂] at hfit
    have hchain := teleFitPA_to_chain (p.nP + ctorsA.length + 2) htele
      (by simp [hxl, hmI]; omega) hfit
    refine spineFit_of_chain (by simp [hxl, hRD.len ψR, hmI]; omega) ?_
    intro n hn
    have := hchain n (by simpa [hRD.len ψR] using hn)
    simpa [hRD.len ψR] using this
  have hspC : SpineFit ρ ((dsF j ψR).map (·.2.2)) (ys.map (interp2 V ρ)) := by
    have hst := stripPisAV_mkPisAV (dsF j ψR) (ctorBodyAV m₂ p.cvT.name p.nP cA.2 ψC)
    rw [hCD.len ψR] at hst
    have htele := piTeleP_of_stripPisAV hst
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain (p.nP + cA.2) htele (by simpa using hyl) hfit
    refine spineFit_of_chain (by simp [hyl, hCD.len ψR]) ?_
    intro n hn
    have := hchain n (by simpa [hCD.len ψR] using hn)
    simpa [hCD.len ψR] using this
  have hplain' : ∀ i, i < p.nP →
      interp2 V ρ (ys.getD i default) = interp2 V ρ (xs.getD i default) :=
    fun i hi => hplain rfl i hi (by omega)
  -- the frames at ψR
  have hbase := sumRecFrames (m := mp.base2) hFD hcf hleafT hleafC hiff hfields hwl hn1 ψR (hR ψR)
  -- the law's two halves
  have hFsj : (fssOf p.nP (ctorDataList dsF ψR ctorsA 0))[j]?
      = some (((dsF j ψR).drop p.nP).map (·.2.2)) := by
    rw [fssOf_getElem?, ctorDataList_getElem?, hj, Nat.zero_add]
    rfl
  have hcore := sumRecLawCore (ℓ := (sumElimLevel p).eval ψR) (w := p.resSort.eval ψR)
    (nP := p.nP) (nF := cA.2) (n := ctorsA.length) (j := j)
    (pds := rebit (pwBit ψR (Level.zeronessOf (sumElimLevel p))) (pps ψR))
    (dms := sumMinorsData mp.base2 ψR p.nP (pwBit ψR (Level.zeronessOf (sumElimLevel p)))
      (ctorDataList dsF ψR ctorsA 0) 1)
    (ds := dsF j ψR)
    (dM := (0, pwBit ψR (Level.zeronessOf (sumElimLevel p)),
      motiveAV mp.base2 p.cvT.name ψR p.nP (sumElimLevel p)))
    (dt := (0, pwBit ψR (Level.zeronessOf (sumElimLevel p)),
      majorAVAt mp.base2 p.cvT.name ψR p.nP (ctorDataList dsF ψR ctorsA 0).length))
    (Fss := fssOf p.nP (ctorDataList dsF ψR ctorsA 0))
    (by rw [rebit_length, hFD.len ψR]) (by rw [sumMinorsData_length, ctorDataList_length])
    (by rw [fssOf_length, ctorDataList_length]) (hCD.len ψR) hjn hFsj
    (fun ρ' => (hAokP ψR ρ').1) (fun ρp h => hbase ρp (by rwa [rebit_map_dom] at h))
    (lds := sumRuleDataAV mp.base2 p.cvT.name ψR p.nP (sumElimLevel p) (pps ψR)
      (ctorDataList dsF ψR ctorsA 0) (dsF j ψR))
    (by rw [sumRuleDataAV_map_dom, ctorDataList_length])
    (fun d hd => by
      rw [mem_sumRuleDataAV_bit hd, pwBit_eq_zero_iff, Setlec.PropWhen.zeronessOf_sound,
        beq_iff_eq])
    rfl (hRuleOk ψR) (by rw [hxl, hmI]) (by simpa using hyl) hspR hspC hplain'
  try simp only [RecRule.ctor, RecRule.ctorParams] at hcore ⊢
  rw [hleafR₂, hleafC₂, hmI]
  exact hcore

/-! ## The stage -/

/-- The generated sum recursor type's opening, at every assignment. -/
theorem sumRecOpenedAll (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr}
    (hRec : Setlec.checkDirectSumRec (Setlec.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    {bsT : List (Name × Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis p.nP = some (bsT, .sort p.resSort))
    {rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hRD : SumRecData mp.base2 cvRa p.nP ctorsA.length (sumElimLevel p) rds) :
    ∃ (fvsR : List Expr) (oR : Expr), ∀ ψ : Name → Nat,
      OpenedP mp.base2 ψ (p.nP + ctorsA.length + 2) cvRa.type fvsR oR
        (((rds ψ).map (·.2.2)).reverse) (.app (.bvar (ctorsA.length + 1)) (.bvar 0)) := by
  obtain ⟨cvRi, recTy, sty, u, -, hgen, -, -, hbt, hRf, -, -, -, -, rfl⟩ :=
    Setlec.checkDirectSumRec_shape hRec
  obtain ⟨minors, hmin, hrec⟩ := Setlec.directRecTy_unfold hgen
  have hs1 := Setlec.replacePisPw_stripPis p.nP hrec hstripT
  -- the minors' telescope strips its `n` binders, then the major's
  have hsmin : ∀ (ctors : List (Name × Nat × Expr)) (o : Nat) (body mins : Expr),
      Setlec.directMinorsPis p.cvT.levelParams p.nP
        (Level.zeronessOf (Setlec.directElimLevel p.elim p.large)) ctors o body = some mins →
      ∃ bs, mins.stripPis ctors.length = some (bs, body) := by
    intro ctors
    induction ctors with
    | nil => intro o body mins h; rw [Setlec.directMinorsPis_nil h]; exact ⟨[], rfl⟩
    | cons c cs ih =>
      intro o body mins h
      obtain ⟨C, nF, cty⟩ := c
      obtain ⟨mty, rest, -, hrest, rfl⟩ := Setlec.directMinorsPis_cons h
      obtain ⟨bs, hbs⟩ := ih (o + 1) body rest hrest
      exact ⟨(Setlec.Name.lastStr C, mty,
        ⟨.default, Level.zeronessOf (Setlec.directElimLevel p.elim p.large)⟩) :: bs,
        by simp [Expr.stripPis, hbs]⟩
  obtain ⟨bsm, hbsm⟩ := hsmin _ _ _ _ hmin
  have h3 : ∃ bs, (Expr.forallE (.str .anonymous "t")
      (Setlec.directFam p.cvT.name p.cvT.levelParams p.nP
        ((ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length + 1))
      (.app (.bvar ((ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length + 1)) (.bvar 0))
      ⟨.default, Level.zeronessOf (Setlec.directElimLevel p.elim p.large)⟩).stripPis 1
      = some (bs, .app (.bvar ((ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length + 1)) (.bvar 0)) :=
    ⟨_, rfl⟩
  obtain ⟨bs3, h3⟩ := h3
  have h23 := Setlec.stripPis_append _ hbsm h3
  have hs2 := Setlec.stripPis_append 1 (e := Expr.forallE (.str .anonymous "motive")
    (Setlec.directMotiveTy p.cvT.name p.cvT.levelParams p.nP (Setlec.directElimLevel p.elim p.large))
    minors ⟨.default, Level.zeronessOf (Setlec.directElimLevel p.elim p.large)⟩)
    (bs := [(.str .anonymous "motive",
      Setlec.directMotiveTy p.cvT.name p.cvT.levelParams p.nP (Setlec.directElimLevel p.elim p.large),
      ⟨.default, Level.zeronessOf (Setlec.directElimLevel p.elim p.large)⟩)])
    (by simp [Expr.stripPis]) h23
  have hs := Setlec.stripPis_append p.nP hs1 hs2
  simp only [List.length_map] at hs
  rw [show p.nP + (1 + (ctorsA.length + 1)) = p.nP + ctorsA.length + 2 from by omega] at hs
  obtain ⟨fvsR, oR, hop⟩ := openPisAtFvars_of_stripPis_isSome (p.nP + ctorsA.length + 2) 0
    (by rw [hs]; rfl)
  exact ⟨fvsR, oR, fun ψ =>
    openedP_of_peel hop hRf hbt (hRD.read ψ) (hRD.len ψ) (hRD.okTy ψ)⟩

set_option maxHeartbeats 6400000 in
/-- **The P step at the sum recursor's cons.** -/
theorem stageSumRec (hE : Setlec.EtaFamiliesClosed env)
    (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {mI : Nat} (hmI : mI = p.nP + 1 + ctorsA.length)
    (hRec : Setlec.checkDirectSumRec (Setlec.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    {bsT : List (Name × Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis p.nP = some (bsT, .sort p.resSort))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa {}))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    (helim : p.large = true → p.elim ∈ p.cvR.levelParams)
    (hRlps' : ∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams)
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.resSort dsF j cA)
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (pps ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)))
    (hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2)
    (hn1 : ctorsA.length ≠ 1) :
    ∃ mp' : EnvS2PM V μ ⟨.recInfo cvRa mI mI (Setlec.directSumRules p.nP mI cvRa.type ctorsA rhss)
        :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name
        (fun ψ => directSumRecAV ((sumElimLevel p).eval ψ) (p.resSort.eval ψ)
          (sumRdsAV mp.base2 p pps dsF ctorsA ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))) := by
  -- the data, the openings, the frames
  have hRD := sumRecData_of hμ mp hRec hfT hlpsT hopT hFD hcf
  obtain ⟨fvsR, oR, hR⟩ := sumRecOpenedAll mp hRec hstripT hRD
  have hbase := fun ψ => sumRecFrames (m := mp.base2) hFD hcf hleafT hleafC hiff hfields hwl hn1 ψ (hR ψ)
  -- the constant's facts
  obtain ⟨cvRi, recTy, sty, u, hccv, -, htp, htrR, -, -, -, -, -, -, hcvRa⟩ :=
    Setlec.checkDirectSumRec_shape hRec
  obtain ⟨hfind, hnres, hpshape, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    Setlec.checkConstantVal_inv hccv
  have hRname : cvRa.name = p.cvR.name := by rw [hcvRa]
  have hRlps : cvRa.levelParams = p.cvR.levelParams := by rw [hcvRa]
  have hRtype : cvRa.type = recTy := by rw [hcvRa]
  have hfresh : env.find? cvRa.name = none := by rw [hRname]; exact hfind
  have htrR' : cvRa.type.constsResolve env = true := by rw [hRtype]; exact htrR
  have hcbR : ConstsBound env cvRa.type := constsBound_of_constsResolve _ htrR'
  have hwf := Setlec.direct_sum_rec_wf (mI := mI) mp.base2.wf hRec
  have hTR : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  -- the field chains' bounds and validity at the parameter frame
  have hFssBelow : ∀ ψ, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF ψ ctorsA 0), FieldsBelow (0 + p.nP) Fs := by
    intro ψ Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    rw [ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : ctorsA[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cA =>
      rw [h] at hi
      obtain rfl := Option.some.inj hi
      obtain ⟨-, -, -, hCD⟩ := hcf i cA h
      exact (DomsBelow.drop p.nP (hCD.below ψ)).fields
  have hvFss : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat2 V (((pps ψ).map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)) := by
    intro ψ ρp hρ Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    rw [ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : ctorsA[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cA =>
      rw [h] at hi
      obtain rfl := Option.some.inj hi
      exact (hfields i cA h ψ ρp ((hiff i cA h ψ ρp).mp hρ)).2
  -- the leaf
  let A : (Name → Nat) → AVExpr :=
    fun ψ => directSumRecAV ((sumElimLevel p).eval ψ) (p.resSort.eval ψ)
      (sumRdsAV mp.base2 p pps dsF ctorsA ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))
  have hAbelow : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase := fun ψ =>
    directSumRecAV_below (hRD.below ψ) (hFssBelow ψ)
      (by rw [sumRdsAV_length hFD, fssOf_length, ctorDataList_length])
  have hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (A ψ) ∧
      interp2 V ρ (A ψ) ∈ˢ interp2 V ρ (mkPisAV (sumRdsAV mp.base2 p pps dsF ctorsA ψ)
        (.app (.bvar (ctorsA.length + 1)) (.bvar 0))) := fun ψ ρ => by
    have h := sumRecLeafFacts (ℓ := (sumElimLevel p).eval ψ) (w := p.resSort.eval ψ)
      (nP := p.nP) (n := ctorsA.length)
      (pds := rebit (pwBit ψ (Level.zeronessOf (sumElimLevel p))) (pps ψ))
      (dms := sumMinorsData mp.base2 ψ p.nP (pwBit ψ (Level.zeronessOf (sumElimLevel p)))
        (ctorDataList dsF ψ ctorsA 0) 1)
      (dM := (0, pwBit ψ (Level.zeronessOf (sumElimLevel p)),
        motiveAV mp.base2 p.cvT.name ψ p.nP (sumElimLevel p)))
      (dt := (0, pwBit ψ (Level.zeronessOf (sumElimLevel p)),
        majorAVAt mp.base2 p.cvT.name ψ p.nP (ctorDataList dsF ψ ctorsA 0).length))
      (Fss := fssOf p.nP (ctorDataList dsF ψ ctorsA 0))
      (by rw [rebit_length, hFD.len ψ]) (by rw [sumMinorsData_length, ctorDataList_length])
      (by rw [fssOf_length, ctorDataList_length]) (hRD.bits ψ) (hR ψ).okΓ
      (fun ρp h => hbase ψ ρp (by rwa [rebit_map_dom] at h))
      (fun ρp h => hvFss ψ ρp (by rwa [rebit_map_dom] at h)) ρ
    exact h
  -- the cons head
  let c₀ : ConstantInfo := .recInfo cvRa mI mI (Setlec.directSumRules p.nP mI cvRa.type ctorsA rhss)
  have hcross : ∀ e : Expr, ConsCrossAt c₀ e := fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hreadR : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval cvRa.name A) ⟨c₀ :: env.consts⟩ ψ 0 cvRa.type
        = some (mkPisAV (sumRdsAV mp.base2 p pps dsF ctorsA ψ)
            (.app (.bvar (ctorsA.length + 1)) (.bvar 0))) := fun ψ =>
    denoteP_cons_mono (c₀ := c₀) hfresh (hcross _) ψ 0 hcbR (hRD.read ψ)
  have hnresC : Setlec.reservedBasisNames.contains c₀.name = false := by
    show Setlec.reservedBasisNames.contains cvRa.name = false
    rw [hRname]; exact hnres
  have hpshapeC : c₀.name.isProjFnShape = false := by
    show cvRa.name.isProjFnShape = false
    rw [hRname]; exact hpshape
  refine declStepPM_of_ind_rec_cons mp (c₀ := c₀) (A := A) hfresh hnresC ⟨_, _, _, _, rfl⟩
    (ConsHeadP.ofFresh hwf (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h)
      (fun cvR' mI' rP rules heq r hr => by
        injection heq with _ _ _ hrules
        subst hrules
        obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Setlec.directSumRules_getElem? hr
        obtain ⟨hf, -, -, -⟩ := hcf j cA hj
        exact ⟨cA.1, p.nP, cA.2, hf⟩))
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have hφR : ∀ q ∈ cvRa.levelParams, ψ₁ q = ψ₂ q := hφ
    have hlpsAll : ∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q :=
      fun q hq => hφR q (by rw [hRlps]; exact hRlps' q hq)
    have hcds : ctorDataList dsF ψ₁ ctorsA 0 = ctorDataList dsF ψ₂ ctorsA 0 := by
      refine ctorDataList_params fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨-, hlpsi, -, hCDi⟩ := hcf i cAi hi'
      exact hCDi.params ψ₁ ψ₂ (fun q hq => hlpsAll q (by rw [← hlpsi]; exact hq))
    have hw : p.resSort.eval ψ₁ = p.resSort.eval ψ₂ :=
      (hFD.params ψ₁ ψ₂ (fun q hq => hlpsAll q (by rw [← hlpsT]; exact hq))).2
    have hℓ : (sumElimLevel p).eval ψ₁ = (sumElimLevel p).eval ψ₂ := by
      cases hpl : p.large
      · simp [sumElimLevel, Setlec.directElimLevel, hpl, Level.eval]
      · simp only [sumElimLevel, Setlec.directElimLevel, hpl, if_true, Level.eval]
        exact hφR p.elim (by rw [hRlps]; exact helim hpl)
    show directSumRecAV _ _ (sumRdsAV mp.base2 p pps dsF ctorsA ψ₁) _
      = directSumRecAV _ _ (sumRdsAV mp.base2 p pps dsF ctorsA ψ₂) _
    rw [hRD.params ψ₁ ψ₂ hφR, hcds, hw, hℓ]
  · exact fun ψ ρ => (hleaf ψ ρ).1.1
  · exact fun ψ ρ => (hleaf ψ ρ).1.2
  · exact fun ψ => ⟨_, hreadR ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadR ψ).symm.trans hta)
    exact hRD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadR ψ).symm.trans hta)
    exact (hleaf ψ ρ).2
  · -- `caps_ok`: the former is stored with the empty record
    intro m₂ hac
    refine capsOkP_cons_direct mp (c₀ := c₀) (A := A) (T := p.cvT.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h) ?_ m₂ hac ?_
    · intro T' cvT' caps' hf hne hres hcape
      exact hE T' cvT' caps' hf hcape hres
    · intro cvT caps hf _
      have hfT' : (⟨c₀ :: env.consts⟩ : Env).find? p.cvT.name = some (.indInfo cvTa {}) := by
        rw [Setlec.Env.find?_cons, if_neg (fun h => hTR h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      exact ⟨fun he => absurd he Bool.false_ne_true, fun hu => absurd hu Bool.false_ne_true⟩
  · -- `rec_rules`
    intro m₂ hac φ'
    refine recRulesP_cons_rec mp (c₀ := c₀) (A := A) hfresh rfl m₂ hac φ' ?_
    intro rl hrl hfire
    obtain ⟨j, cA, rhs, hj, hrhs, rfl⟩ := Setlec.directSumRules_getElem? hrl
    by_cases hplain : Expr.recRulePlain cvRa.type mI mI p.nP = true
    · have hrule : (⟨cA.1.name, cA.2, p.nP,
          if Expr.recRulePlain cvRa.type mI mI p.nP then .plain else .inert, rhs⟩ : RecRule)
          = ⟨cA.1.name, cA.2, p.nP, .plain, rhs⟩ := by
        simp [hplain]
      obtain ⟨rhs', hrhs', hres, -, hRuleRead, hRuleOk⟩ :=
        sumRuleData_of hμ mp hRec hfT hlpsT hopT hFD hcf hj
      obtain rfl := Option.some.inj (hrhs.symm.trans hrhs')
      exact sumRecRuleLaw mp hmI hfT hlpsT hFD hcf hRD hR hleafT hleafC hiff hfields hwl hn1 hj
        hRuleRead hRuleOk hres htrR' hfresh hrule m₂ hac (fun ψ ρ => (hleaf ψ ρ).1) φ'
    · exfalso
      apply hfire
      simp [hplain]

end Setlec.SetP
