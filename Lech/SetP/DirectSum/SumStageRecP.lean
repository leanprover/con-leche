import Lech.SetP.DirectSum.SumRecLawP
import Lech.SetP.DirectSum.SumStageCtorP
import Lech.SetP.IndPointKitP

/-!
# The sum recursor's cons (task #175 sum-types, indexed)

`stageSumRec`: the P step at the sum recursor's cons.  The stored
recursor is the generated one: its data is read off syntactically
(`sumRecData_of`), its leaf is `directSumRecAV` over that data, the
field chains, the index readings and the sources, the frames' walks
(`sumRecLeafFacts` over `sumRecFrames`) give the leaf's grading and
membership, the capability laws are vacuous (the block claims no eta
or unit law; rule K needs no law — the kernel's K rescue is certified
by proof irrelevance at the fire), and every stored rule's law is
`sumRecRuleLaw` over the generated rule at its constructor's position
(an inert rule owes nothing).  The rule law consumes the kernel's
index pin (`IotaIndexPinP`, from `iotaIndexOk`): the constructor's
index values at the fields are the recursor application's index
arguments.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- A lifted telescope strips as the telescope does, the body lifted
above the stripped binders. -/
theorem stripPis_liftLooseBVars :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr} (n c : Nat),
      e.stripPis k = some (bs, body) →
      ∃ bs', (e.liftLooseBVars n c).stripPis k = some (bs', body.liftLooseBVars n (c + k))
  | 0, e, bs, body, n, c, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis]⟩
  | k + 1, e, bs, body, n, c, h => by
    match e, h with
    | .forallE ty b mb, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hs, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨bs'', hs''⟩ := stripPis_liftLooseBVars k n (c + 1) hs
      refine ⟨(nm, ty.liftLooseBVars n c, mb) :: bs'', ?_⟩
      show (Expr.forallE (Expr.liftLooseBVars n c ty) (Expr.liftLooseBVars n (c + 1) b) mb).stripPis
        (k + 1) = _
      simp only [Expr.stripPis, hs'', Option.map_some]
      rw [show c + 1 + k = c + (k + 1) from by omega]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-! ## The rule data's shape -/

/-- The rule's λ-domains are the recursor's parameter, motive and
minor domains followed by the constructor's field domains lifted
`n + 1` under. -/
theorem sumRuleDataAV_map_dom {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat}
    {nP nIdx : Nat} {ℓ : Level} {pps ips ds : List (Nat × Nat × AVExpr)} {cds : List CtorDatum} :
    (sumRuleDataAV m T ψ nP nIdx ℓ pps ips cds ds).map (·.2)
      = ((rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
          [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
          sumMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1).map
            (fun d : Nat × Nat × AVExpr => d.2.2)) ++
        (liftDoms (cds.length + 1) 0 (ds.drop nP)).map (fun d : Nat × Nat × AVExpr => d.2.2) := by
  unfold sumRuleDataAV
  rw [List.map_map, List.map_append]
  have h : ((fun x : Nat × AVExpr => x.2) ∘ fun d : Nat × Nat × AVExpr => (d.2.1, d.2.2))
      = fun d : Nat × Nat × AVExpr => d.2.2 := rfl
  rw [h, rebit_map_dom]

theorem mem_sumRuleDataAV_bit {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat}
    {nP nIdx : Nat} {ℓ : Level} {pps ips ds : List (Nat × Nat × AVExpr)} {cds : List CtorDatum}
    {d : Nat × AVExpr}
    (hd : d ∈ sumRuleDataAV m T ψ nP nIdx ℓ pps ips cds ds) : d.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  unfold sumRuleDataAV at hd
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
  simp only [List.mem_append, List.mem_singleton] at hd'
  rcases hd' with ((h | rfl) | h) | h
  · exact mem_rebit h
  · rfl
  · exact mem_sumMinorsData h
  · exact mem_rebit h

/-! ## The per-constructor facts across a cons -/

/-- The constructors' facts cross a cons whose head is fresh and is
not the block's former nor a constructor. -/
theorem ctorFactsAt_cross {m : EnvS2Core V env} {T : Name} {lps : List Name} {nP nIdx : Nat}
    {resSort : Level} {isProp large : Bool} {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    {ctorsA : List (ConstantVal × Nat)}
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt m T lps nP nIdx resSort isProp large idxF dsF esF srcsF j cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    (∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt m₂ T lps nP nIdx resSort isProp large idxF dsF esF srcsF j cA) ∧
    (∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j,
      e.constsResolve ⟨c₀ :: env.consts⟩ = true) := by
  refine ⟨fun j cA hj => ?_, fun j cA hj e he => Expr.constsResolve_mono (hidxRes j cA hj e he)⟩
  obtain ⟨hf, hlps, hCD⟩ := hcf j cA hj
  have hcb : ConstsBound env cA.1.type :=
    constsBound_of_constsResolve _ (m.wf _ (Lech.Semantics.Env.find?_mem hf)).2.2.1
  exact ⟨Lech.Env.find?_cons_of_fresh hfresh hf, hlps,
    hCD.cross hfresh hT (fun _ => ConsCrossAt.ofNtc hntc) hcb
      (fun e he => constsBound_of_constsResolve _ (hidxRes j cA hj e he)) m₂ hac⟩

/-! ## The rule law -/

set_option maxHeartbeats 12800000 in
/-- **The direct sum block's rule `j` fires at the readings.** -/
theorem sumRecRuleLaw (mp : EnvS2PM V μ env)
    {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {mI rP : Nat} (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    {caps : IndCaps}
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF j cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    (hRD : SumRecData mp.base2 cvRa p.nP ctorsA.length p.nIdx (sumElimLevel p)
      (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA))
    {fvsR : List Expr} {oR : Expr}
    (hR : ∀ ψ : Name → Nat,
      OpenedP mp.base2 ψ (p.nP + ctorsA.length + p.nIdx + 2) cvRa.type fvsR oR
        (((sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ).map (·.2.2)).reverse)
        (recConcAV ctorsA.length p.nIdx))
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ)
          (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
            (essOf (ctorDataList dsF esF ψ ctorsA 0))))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        (∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
          (∀ E ∈ esF j ψ, AnnotOkP V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs)))
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((ppsAll ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ
        (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0))) ∧
      SumFieldsValid ρ
        (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0))))
    (hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2)
    {j : Nat} {cA : ConstantVal × Nat} (hj : ctorsA[j]? = some cA) {rhs : Expr}
    (hRuleRead : ∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 rhs
      = some (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx (sumElimLevel p)
          ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP) (ctorDataList dsF esF ψ ctorsA 0) (dsF j ψ))
          (sumRuleCoreAV cA.2 ctorsA.length j)))
    (hRuleOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx (sumElimLevel p)
          ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP) (ctorDataList dsF esF ψ ctorsA 0) (dsF j ψ))
          (sumRuleCoreAV cA.2 ctorsA.length j)))
    (hrhsRes : rhs.constsResolve env = true)
    (hRres : cvRa.type.constsResolve env = true)
    (hfresh : env.find? cvRa.name = none)
    {rule : RecRule} (hrule : rule = ⟨cA.1.name, cA.2, p.nP, .plain, rhs⟩)
    {rules : List RecRule}
    (m₂ : EnvS2Core V ⟨.recInfo cvRa mI rP rules :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cvRa.name
      (fun ψ => directSumRecAV ((sumElimLevel p).eval ψ) (p.resSort.eval ψ)
        (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ) (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
        (essOf (ctorDataList dsF esF ψ ctorsA 0)) (srcssOf srcsF ctorsA.length) p.nIdx))
    (hAokP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (directSumRecAV ((sumElimLevel p).eval ψ) (p.resSort.eval ψ)
        (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ) (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
        (essOf (ctorDataList dsF esF ψ ctorsA 0)) (srcssOf srcsF ctorsA.length) p.nIdx))
    (φ : Name → Nat) :
    RecRuleLawP m₂ φ cvRa.name cvRa mI rP rule := by
  subst hrule
  obtain ⟨hfC, hlpsC, hCD⟩ := hcf j cA hj
  have hjn : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  -- the constructor's stored type
  obtain ⟨-, -, hCres, -, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCres
  have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ hCres
  have hcbT : ConstsBound env cvRa.type := constsBound_of_constsResolve _ hRres
  have hcbR : ConstsBound env rhs := constsBound_of_constsResolve _ hrhsRes
  have hRC : cA.1.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfC; exact nomatch hfC
  have hRT : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  -- the cons crossing
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo cvRa mI rP rules) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hfindC : (⟨.recInfo cvRa mI rP rules :: env.consts⟩ : Env).find? cA.1.name
      = some (.ctorInfo cA.1 p.nP cA.2) := by
    rw [Lech.Env.find?_cons, if_neg (fun h => hRC h.symm)]
    exact hfC
  -- the law
  refine ⟨by omega, fun us hus => ?_⟩
  dsimp only
  have hinstR : ∀ (d : Nat) (e : Expr),
      denoteP m₂.acval _ φ d (e.instantiateLevelParams cvRa.levelParams us)
        = denoteP m₂.acval _ (Level.substFn φ cvRa.levelParams us) d e :=
    fun d e => denoteP_instLevels (acvalParamsAt_of_core m₂) φ d e
  generalize hψR : Level.substFn φ cvRa.levelParams us = ψR at hinstR ⊢
  -- the right-hand side's reading, at the extension
  have hRa₂ : denoteP m₂.acval ⟨.recInfo cvRa mI rP rules :: env.consts⟩ φ 0
      (rhs.instantiateLevelParams cvRa.levelParams us)
      = some (mkLamsAV (sumRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx (sumElimLevel p)
          ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP) (ctorDataList dsF esF ψR ctorsA 0)
          (dsF j ψR)) (sumRuleCoreAV cA.2 ctorsA.length j)) := by
    rw [hinstR, hac]
    exact denoteP_cons_mono hfresh (hcross _) ψR 0 hcbR (hRuleRead ψR)
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
  have hdsEq : ∀ i, i < ctorsA.length → dsF i ψC = dsF i ψR ∧ esF i ψC = esF i ψR := by
    intro i hi
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨-, hlpsi, hCDi⟩ := hcf i cAi hi'
    exact hCDi.params ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq))
  have hcdsEq : ctorDataList dsF esF ψC ctorsA 0 = ctorDataList dsF esF ψR ctorsA 0 :=
    ctorDataList_params fun i hi => by rw [Nat.zero_add]; exact hdsEq i hi
  have hdsjEq : dsF j ψC = dsF j ψR := (hdsEq j hjn).1
  have hesjEq : esF j ψC = esF j ψR := (hdsEq j hjn).2
  have hwEq : p.resSort.eval ψC = p.resSort.eval ψR :=
    (hFD.params ψC ψR (fun q hq => hagree q (by rw [← hlpsT]; exact hq))).2
  -- the recursor and constructor types' readings, at the extension
  have hRD₂ := hRD.cross (c₀ := .recInfo cvRa mI rP rules) hfresh (hcross _) hcbT m₂ hac
  have hCD₂ := hCD.cross (c₀ := .recInfo cvRa mI rP rules) hfresh hRT hcross hcbC
    (fun e he => constsBound_of_constsResolve _ (hidxRes j cA hj e he)) m₂ hac
  have hTVa' : TVa = mkPisAV (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψR)
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
          (uChains (fssOf p.nP (ctorDataList dsF esF ψR ctorsA 0))) := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cA.1.name ψC = _
    rw [acvalWith_ne hRC, hleafC j cA hj ψC, hdsjEq, hwEq, hcdsEq]
  have hleafR₂ : m₂.acval cvRa.name ψR
      = directSumRecAV ((sumElimLevel p).eval ψR) (p.resSort.eval ψR)
          (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψR) (fssOf p.nP (ctorDataList dsF esF ψR ctorsA 0))
          (essOf (ctorDataList dsF esF ψR ctorsA 0)) (srcssOf srcsF ctorsA.length) p.nIdx := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cvRa.name ψR = _
    rw [acvalWith_self]
  -- the fits, as spines
  have hspR : SpineFit ρ ((sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψR).map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directSumMkAV (p.resSort.eval ψR) j (dsF j ψR)
        (((dsF j ψR).drop p.nP).map (·.2.2)) (uChains (fssOf p.nP (ctorDataList dsF esF ψR ctorsA 0)))) ys]).map
        (interp2 V ρ)) := by
    have hst := stripPisAV_mkPisAV (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψR)
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
  -- the frames at ψR
  have hbase := sumRecFrames (m := mp.base2) hFD hcf hleafT hleafC hiff hfields hFssOk hwl ψR (hR ψR)
  -- the law's two halves
  have hFsj : (fssOf p.nP (ctorDataList dsF esF ψR ctorsA 0))[j]?
      = some (((dsF j ψR).drop p.nP).map (·.2.2)) := by
    rw [fssOf_getElem?, ctorDataList_getElem?, hj, Nat.zero_add]
    rfl
  have hEsj : (essOf (ctorDataList dsF esF ψR ctorsA 0))[j]? = some (esF j ψR) := by
    rw [essOf_getElem?, ctorDataList_getElem?, hj, Nat.zero_add]
    rfl
  have hokFss : ∀ ρp : Nat → V, Sat2 V (((rebit (pwBit ψR (Level.zeronessOf (sumElimLevel p)))
      ((ppsAll ψR).take p.nP)).map (·.2.2)).reverse) ρp →
      SumFieldsOkB (p.resSort.eval ψR) ρp (fssOf p.nP (ctorDataList dsF esF ψR ctorsA 0)) := by
    intro ρp hρ
    rw [rebit_map_dom] at hρ
    intro Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    rw [ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : ctorsA[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cAi =>
      rw [h] at hi
      obtain rfl := Option.some.inj hi
      exact (hfields i cAi h ψR ρp ((hiff i cAi h ψR ρp).mp hρ)).1
  have hlenPps : ((ppsAll ψR).take p.nP).length = p.nP := by
    rw [List.length_take, hFD.len ψR]; omega
  have hlenIps : ((ppsAll ψR).drop p.nP).length = p.nIdx := by
    rw [List.length_drop, hFD.len ψR]; omega
  have hcore := sumRecLawCore (ℓ := (sumElimLevel p).eval ψR) (w := p.resSort.eval ψR)
    (nP := p.nP) (nF := cA.2) (nIdx := p.nIdx) (n := ctorsA.length) (j := j)
    (pds := rebit (pwBit ψR (Level.zeronessOf (sumElimLevel p))) ((ppsAll ψR).take p.nP))
    (dms := sumMinorsData mp.base2 ψR p.nP (pwBit ψR (Level.zeronessOf (sumElimLevel p)))
      (ctorDataList dsF esF ψR ctorsA 0) 1)
    (dis := rebit (pwBit ψR (Level.zeronessOf (sumElimLevel p)))
      (liftDoms ((ctorDataList dsF esF ψR ctorsA 0).length + 1) 0 ((ppsAll ψR).drop p.nP)))
    (ds := dsF j ψR)
    (dM := (0, pwBit ψR (Level.zeronessOf (sumElimLevel p)),
      motiveAVI mp.base2 p.cvT.name ψR p.nP p.nIdx (sumElimLevel p) ((ppsAll ψR).drop p.nP)))
    (dt := (0, pwBit ψR (Level.zeronessOf (sumElimLevel p)),
      majorAVAt mp.base2 p.cvT.name ψR p.nP p.nIdx (ctorDataList dsF esF ψR ctorsA 0).length))
    (Fss := fssOf p.nP (ctorDataList dsF esF ψR ctorsA 0))
    (Ess := essOf (ctorDataList dsF esF ψR ctorsA 0))
    (Ids := ((ppsAll ψR).drop p.nP).map (·.2.2))
    (famAt := fun ρp => sumFamAt (p.resSort.eval ψR) p.nIdx ρp
      (fssOf p.nP (ctorDataList dsF esF ψR ctorsA 0)) (essOf (ctorDataList dsF esF ψR ctorsA 0)))
    (srcs := srcssOf srcsF ctorsA.length) (Es := esF j ψR)
    (by rw [rebit_length, hlenPps]) (by rw [sumMinorsData_length, ctorDataList_length])
    (by rw [rebit_length, liftDoms_length, hlenIps]) (by rw [fssOf_length, ctorDataList_length])
    (by rw [List.length_map, hlenIps]) (hCD.len ψR) hjn hFsj hEsj (hCD.lenE ψR)
    (fun ρ' => (hAokP ψR ρ').1) (fun ρp h => hbase ρp (by rwa [rebit_map_dom] at h)) hokFss
    (lds := sumRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx (sumElimLevel p)
      ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP) (ctorDataList dsF esF ψR ctorsA 0) (dsF j ψR))
    (by rw [sumRuleDataAV_map_dom, ctorDataList_length])
    (fun d hd => by
      rw [mem_sumRuleDataAV_bit hd, pwBit_eq_zero_iff, Lech.PropWhen.zeronessOf_sound,
        beq_iff_eq])
    rfl (hRuleOk ψR) (by rw [hxl, hmI]) (by simpa using hyl) hspR hspC hplain' hpin
  try simp only [RecRule.ctor, RecRule.ctorParams] at hcore ⊢
  rw [hleafR₂, hleafC₂, hrP]
  exact hcore

/-! ## The stage -/

/-- The generated sum recursor type's opening, at every assignment. -/
theorem sumRecOpenedAll (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr}
    (hRec : Lech.checkDirectSumRec (Lech.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    {bsT : List (Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    {rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hRD : SumRecData mp.base2 cvRa p.nP ctorsA.length p.nIdx (sumElimLevel p) rds) :
    ∃ (fvsR : List Expr) (oR : Expr), ∀ ψ : Name → Nat,
      OpenedP mp.base2 ψ (p.nP + ctorsA.length + p.nIdx + 2) cvRa.type fvsR oR
        (((rds ψ).map (·.2.2)).reverse) (recConcAV ctorsA.length p.nIdx) := by
  obtain ⟨cvRi, recTy, sty, u, -, hgen, -, -, hbt, hRf, -, -, -, -, rfl⟩ :=
    Lech.checkDirectSumRec_shape hRec
  obtain ⟨tbs, itele, motiveTy, major, minors, hsT, -, hmaj, hmin, hrec⟩ :=
    Lech.directRecTyI_unfold hgen
  -- the former's index telescope strips
  have hstripI : (itele.stripPis p.nIdx).isSome = true :=
    stripPis_isSome_drop p.nP (by rw [hstripT]; rfl) hsT
  obtain ⟨⟨ibs, ibody⟩, hsI⟩ := Option.isSome_iff_exists.mp hstripI
  obtain ⟨ibs', hsI'⟩ := stripPis_liftLooseBVars p.nIdx (ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length.succ 0 hsI
  -- the major's telescope: the index binders then the major binder
  have hs3 := Lech.replacePisPw_stripPis p.nIdx hmaj hsI'
  have hs4 : ∃ bs, (Expr.forallE
      (Lech.directFamI p.cvT.name p.cvT.levelParams p.nP p.nIdx
        ((ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length + 1) 0)
      (Expr.mkAppN (.bvar (p.nIdx + (ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length + 1))
        (Lech.directPsAt 1 p.nIdx ++ [.bvar 0]))
      ⟨Level.zeronessOf (Lech.directElimLevel p.elim p.large)⟩).stripPis 1
      = some (bs, Expr.mkAppN (.bvar (p.nIdx + (ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length + 1))
        (Lech.directPsAt 1 p.nIdx ++ [.bvar 0])) :=
    ⟨_, rfl⟩
  obtain ⟨bs4, hs4⟩ := hs4
  have hs34 := Lech.stripPis_append p.nIdx hs3 hs4
  -- the minors' telescope strips its `n` binders
  have hsmin : ∀ (ctors : List (Name × Nat × Expr)) (o : Nat) (body mins : Expr),
      Lech.directMinorsPisI p.cvT.levelParams p.nP
        (Level.zeronessOf (Lech.directElimLevel p.elim p.large)) ctors o body = some mins →
      ∃ bs, mins.stripPis ctors.length = some (bs, body) := by
    intro ctors
    induction ctors with
    | nil => intro o body mins h; rw [Lech.directMinorsPisI_nil h]; exact ⟨[], rfl⟩
    | cons c cs ih =>
      intro o body mins h
      obtain ⟨C, nF, cty⟩ := c
      obtain ⟨mty, rest, -, hrest, rfl⟩ := Lech.directMinorsPisI_cons h
      obtain ⟨bs, hbs⟩ := ih (o + 1) body rest hrest
      exact ⟨(Lech.Name.lastStr C, mty,
        ⟨Level.zeronessOf (Lech.directElimLevel p.elim p.large)⟩) :: bs,
        by simp [Expr.stripPis, hbs]⟩
  obtain ⟨bsm, hbsm⟩ := hsmin _ _ _ _ hmin
  have h23 := Lech.stripPis_append _ hbsm hs34
  have hs2 := Lech.stripPis_append 1 (e := Expr.forallE motiveTy minors
      ⟨Level.zeronessOf (Lech.directElimLevel p.elim p.large)⟩)
    (bs := [(.str .anonymous "motive", motiveTy,
      ⟨Level.zeronessOf (Lech.directElimLevel p.elim p.large)⟩)])
    (by simp [Expr.stripPis]) h23
  have hs1 := Lech.replacePisPw_stripPis p.nP hrec hsT
  have hs := Lech.stripPis_append p.nP hs1 hs2
  simp only [List.length_map] at hs
  rw [show p.nP + (1 + (ctorsA.length + (p.nIdx + 1))) = p.nP + ctorsA.length + p.nIdx + 2 from by
    omega] at hs
  obtain ⟨fvsR, oR, hop⟩ := openPisAtFvars_of_stripPis_isSome (p.nP + ctorsA.length + p.nIdx + 2) 0
    (by rw [hs]; rfl)
  exact ⟨fvsR, oR, fun ψ =>
    openedP_of_peel hop hRf hbt (hRD.read ψ) (hRD.len ψ) (hRD.okTy ψ)⟩

set_option maxHeartbeats 6400000 in
/-- **The P step at the sum recursor's cons.** -/
theorem stageSumRec (hE : Lech.EtaFamiliesClosed env)
    (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectSumParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {mI rP : Nat}
    (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    (hRec : Lech.checkDirectSumRec (Lech.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    {bsT : List (Expr × BinderMeta)}
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
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF j cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ)
          (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
            (essOf (ctorDataList dsF esF ψ ctorsA 0))))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        (∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
          (∀ E ∈ esF j ψ, AnnotOkP V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs)))
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((ppsAll ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ
        (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0))) ∧
      SumFieldsValid ρ
        (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0))))
    (hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2) :
    ∃ mp' : EnvS2PM V μ ⟨.recInfo cvRa mI rP (Lech.directSumRules p.nP mI rP cvRa.type ctorsA rhss)
        :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name
        (fun ψ => directSumRecAV ((sumElimLevel p).eval ψ) (p.resSort.eval ψ)
          (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ) (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0)) (srcssOf srcsF ctorsA.length) p.nIdx) := by
  -- the data, the openings, the frames
  have hRD := sumRecData_of hμ mp hRec hfT hlpsT hstripT hopT hFD hcf
  obtain ⟨fvsR, oR, hR⟩ := sumRecOpenedAll mp hRec hstripT hRD
  have hbase := fun ψ => sumRecFrames (m := mp.base2) hFD hcf hleafT hleafC hiff hfields hFssOk hwl ψ (hR ψ)
  -- the constant's facts
  obtain ⟨cvRi, recTy, sty, u, hccv, -, htp, htrR, -, -, -, -, -, -, hcvRa⟩ :=
    Lech.checkDirectSumRec_shape hRec
  obtain ⟨hfind, hnres, hpshape, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    Lech.checkConstantVal_inv hccv
  have hRname : cvRa.name = p.cvR.name := by rw [hcvRa]
  have hRlps : cvRa.levelParams = p.cvR.levelParams := by rw [hcvRa]
  have hRtype : cvRa.type = recTy := by rw [hcvRa]
  have hfresh : env.find? cvRa.name = none := by rw [hRname]; exact hfind
  have htrR' : cvRa.type.constsResolve env = true := by rw [hRtype]; exact htrR
  have hcbR : ConstsBound env cvRa.type := constsBound_of_constsResolve _ htrR'
  have hwf := Lech.direct_sum_rec_wf (mI := mI) (rP := rP) mp.base2.wf hRec
  have hTR : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  -- the field chains' bounds and validity at the parameter frame
  have hcd : ∀ ψ i cd, (ctorDataList dsF esF ψ ctorsA 0)[i]? = some cd → ∃ cA, ctorsA[i]? = some cA ∧
      cd = (cA.1.name, cA.2, dsF i ψ, esF i ψ) := by
    intro ψ i cd hi
    rw [ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : ctorsA[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cA => rw [h] at hi; exact ⟨cA, rfl, (Option.some.inj hi).symm⟩
  have hFssBelow : ∀ ψ, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0), FieldsBelow (0 + p.nP) Fs := by
    intro ψ Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨cA, hiA, rfl⟩ := hcd ψ i cd hi
    obtain ⟨-, -, hCD⟩ := hcf i cA hiA
    exact (DomsBelow.drop p.nP (hCD.below ψ)).fields
  have hEssBelow : ∀ ψ j, j < (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)).length →
      ((essOf (ctorDataList dsF esF ψ ctorsA 0)).getD j []).length = p.nIdx ∧
      ∀ E ∈ (essOf (ctorDataList dsF esF ψ ctorsA 0)).getD j [],
        VExpr.bvarsBelow (0 + p.nP + ((fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)).getD j []).length)
          E.erase := by
    intro ψ j hj
    rw [fssOf_length, ctorDataList_length] at hj
    obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨-, -, hCD⟩ := hcf j cA hjA
    have hE : (essOf (ctorDataList dsF esF ψ ctorsA 0)).getD j [] = esF j ψ := by
      rw [List.getD_eq_getElem?_getD, essOf_getElem?, ctorDataList_getElem?, hjA, Nat.zero_add]; rfl
    have hF : (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)).getD j [] = ((dsF j ψ).drop p.nP).map (·.2.2) := by
      rw [List.getD_eq_getElem?_getD, fssOf_getElem?, ctorDataList_getElem?, hjA, Nat.zero_add]; rfl
    rw [hE, hF]
    refine ⟨hCD.lenE ψ, fun E hE' => ?_⟩
    have := hCD.belowE ψ E hE'
    rwa [show 0 + p.nP + (((dsF j ψ).drop p.nP).map (·.2.2)).length = p.nP + cA.2 from by
      simp [hCD.len ψ]]
  have hvFss : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat2 V ((((ppsAll ψ).take p.nP).map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) ∧
      ∀ j, j < ctorsA.length →
        ∀ bs : List V, SpineFit ρp ((fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)).getD j []) bs →
        ∀ E ∈ (essOf (ctorDataList dsF esF ψ ctorsA 0)).getD j [],
          AnnotValidV V (consList bs ρp) E := by
    intro ψ ρp hρ
    refine ⟨fun Fs hFs => ?_, fun j hj bs hsp E hE => ?_⟩
    · obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      obtain ⟨cA, hiA, rfl⟩ := hcd ψ i cd hi
      exact (hfields i cA hiA ψ ρp ((hiff i cA hiA ψ ρp).mp hρ)).2.1
    · obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
      have hE' : (essOf (ctorDataList dsF esF ψ ctorsA 0)).getD j [] = esF j ψ := by
        rw [List.getD_eq_getElem?_getD, essOf_getElem?, ctorDataList_getElem?, hjA, Nat.zero_add]; rfl
      have hF : (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)).getD j [] = ((dsF j ψ).drop p.nP).map (·.2.2) := by
        rw [List.getD_eq_getElem?_getD, fssOf_getElem?, ctorDataList_getElem?, hjA, Nat.zero_add]; rfl
      rw [hE'] at hE
      rw [hF] at hsp
      exact (((hfields j cA hjA ψ ρp ((hiff j cA hjA ψ ρp).mp hρ)).2.2 bs hsp).1 E hE).2
  have hsrcBnd : ∀ s ∈ (srcssOf srcsF ctorsA.length).getD 0 [], ∀ l, s = some l → l < p.nIdx := by
    intro s hs l hsl
    rcases Nat.eq_zero_or_pos ctorsA.length with h0 | hpos
    · simp [srcssOf, h0] at hs
    · obtain ⟨cA, hA⟩ : ∃ cA, ctorsA[0]? = some cA := ⟨_, List.getElem?_eq_getElem hpos⟩
      rw [srcssOf_getD srcsF hpos] at hs
      exact (hcf 0 cA hA).2.2.srcBnd s hs l hsl
  -- the leaf
  let A : (Name → Nat) → AVExpr :=
    fun ψ => directSumRecAV ((sumElimLevel p).eval ψ) (p.resSort.eval ψ)
      (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ) (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
      (essOf (ctorDataList dsF esF ψ ctorsA 0)) (srcssOf srcsF ctorsA.length) p.nIdx
  have hAbelow : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase := fun ψ =>
    directSumRecAV_below (hRD.below ψ) hsrcBnd
      (rChains_below (by omega) (hFssBelow ψ) (hEssBelow ψ))
      (by rw [sumRdsAV_length hFD, fssOf_length, ctorDataList_length])
  have hlenPps : ∀ ψ, ((ppsAll ψ).take p.nP).length = p.nP := fun ψ => by
    rw [List.length_take, hFD.len ψ]; omega
  have hlenIps : ∀ ψ, ((ppsAll ψ).drop p.nP).length = p.nIdx := fun ψ => by
    rw [List.length_drop, hFD.len ψ]; omega
  have hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (A ψ) ∧
      interp2 V ρ (A ψ) ∈ˢ interp2 V ρ (mkPisAV (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ)
        (recConcAV ctorsA.length p.nIdx)) := fun ψ ρ => by
    have h := sumRecLeafFacts (ℓ := (sumElimLevel p).eval ψ) (w := p.resSort.eval ψ)
      (nP := p.nP) (n := ctorsA.length) (nIdx := p.nIdx)
      (pds := rebit (pwBit ψ (Level.zeronessOf (sumElimLevel p))) ((ppsAll ψ).take p.nP))
      (dms := sumMinorsData mp.base2 ψ p.nP (pwBit ψ (Level.zeronessOf (sumElimLevel p)))
        (ctorDataList dsF esF ψ ctorsA 0) 1)
      (dis := rebit (pwBit ψ (Level.zeronessOf (sumElimLevel p)))
        (liftDoms ((ctorDataList dsF esF ψ ctorsA 0).length + 1) 0 ((ppsAll ψ).drop p.nP)))
      (dM := (0, pwBit ψ (Level.zeronessOf (sumElimLevel p)),
        motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ((ppsAll ψ).drop p.nP)))
      (dt := (0, pwBit ψ (Level.zeronessOf (sumElimLevel p)),
        majorAVAt mp.base2 p.cvT.name ψ p.nP p.nIdx (ctorDataList dsF esF ψ ctorsA 0).length))
      (Fss := fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
      (Ess := essOf (ctorDataList dsF esF ψ ctorsA 0))
      (Ids := ((ppsAll ψ).drop p.nP).map (·.2.2))
      (famAt := fun ρp => sumFamAt (p.resSort.eval ψ) p.nIdx ρp
        (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) (essOf (ctorDataList dsF esF ψ ctorsA 0)))
      (srcs := srcssOf srcsF ctorsA.length)
      (by rw [rebit_length, hlenPps]) (by rw [sumMinorsData_length, ctorDataList_length])
      (by rw [rebit_length, liftDoms_length, hlenIps]) (by rw [fssOf_length, ctorDataList_length])
      (by rw [List.length_map, hlenIps]) (hRD.bits ψ) (hR ψ).okΓ
      (fun ρp h => hbase ψ ρp (by rwa [rebit_map_dom] at h))
      (fun ρp h => hvFss ψ ρp (by rwa [rebit_map_dom] at h)) ρ
    exact h
  -- the cons head
  let c₀ : ConstantInfo := .recInfo cvRa mI rP (Lech.directSumRules p.nP mI rP cvRa.type ctorsA rhss)
  have hcross : ∀ e : Expr, ConsCrossAt c₀ e := fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hreadR : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval cvRa.name A) ⟨c₀ :: env.consts⟩ ψ 0 cvRa.type
        = some (mkPisAV (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ)
            (recConcAV ctorsA.length p.nIdx)) := fun ψ =>
    denoteP_cons_mono (c₀ := c₀) hfresh (hcross _) ψ 0 hcbR (hRD.read ψ)
  have hnresC : Lech.reservedBasisNames.contains c₀.name = false := by
    show Lech.reservedBasisNames.contains cvRa.name = false
    rw [hRname]; exact hnres
  have hpshapeC : c₀.name.isProjFnShape = false := by
    show cvRa.name.isProjFnShape = false
    rw [hRname]; exact hpshape
  refine declStepPM_of_ind_rec_cons mp (c₀ := c₀) (A := A) hfresh hnresC ⟨_, _, _, _, rfl⟩
    (ConsHeadP.ofFresh hwf (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h)
      (fun cvR' mI' rP' rules heq r hr => by
        injection heq with _ _ _ hrules
        subst hrules
        obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Lech.directSumRules_getElem? hr
        obtain ⟨hf, -, -⟩ := hcf j cA hj
        exact ⟨cA.1, p.nP, cA.2, hf⟩))
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have hφR : ∀ q ∈ cvRa.levelParams, ψ₁ q = ψ₂ q := hφ
    have hlpsAll : ∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q :=
      fun q hq => hφR q (by rw [hRlps]; exact hRlps' q hq)
    have hcds : ctorDataList dsF esF ψ₁ ctorsA 0 = ctorDataList dsF esF ψ₂ ctorsA 0 := by
      refine ctorDataList_params fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨-, hlpsi, hCDi⟩ := hcf i cAi hi'
      exact hCDi.params ψ₁ ψ₂ (fun q hq => hlpsAll q (by rw [← hlpsi]; exact hq))
    have hw : p.resSort.eval ψ₁ = p.resSort.eval ψ₂ :=
      (hFD.params ψ₁ ψ₂ (fun q hq => hlpsAll q (by rw [← hlpsT]; exact hq))).2
    have hℓ : (sumElimLevel p).eval ψ₁ = (sumElimLevel p).eval ψ₂ := by
      cases hpl : p.large
      · simp [sumElimLevel, Lech.directElimLevel, hpl, Level.eval]
      · simp only [sumElimLevel, Lech.directElimLevel, hpl, if_true, Level.eval]
        exact hφR p.elim (by rw [hRlps]; exact helim hpl)
    show directSumRecAV _ _ (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ₁) _ _ _ _
      = directSumRecAV _ _ (sumRdsAV mp.base2 p ppsAll dsF esF ctorsA ψ₂) _ _ _ _
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
      obtain ⟨rhs', hrhs', hres, -, hRuleRead, hRuleOk⟩ :=
        sumRuleData_of hμ mp hRec hfT hlpsT hstripT hopT hFD hcf hj
      obtain rfl := Option.some.inj (hrhs.symm.trans hrhs')
      exact sumRecRuleLaw mp hmI hrP hfT hlpsT hFD hcf hidxRes hRD hR hleafT hleafC hiff hfields
        hFssOk hwl hj hRuleRead hRuleOk hres htrR' hfresh hrule m₂ hac (fun ψ ρ => (hleaf ψ ρ).1) φ'
    · exfalso
      apply hfire
      simp [hplain]

end Lech.SetP
