module

public import ConLeche.Model.IndRep
import ConLeche.Model.Inductives.FixRuleData
import ConLeche.Model.Inductives.StructStageCtor
import ConLeche.Verify.Inductives.FixWF
public section

/-!
# The representation of a natively installed block (task #280)

`indRep_of_stage`: the facts the recursor stage of the fixpoint route
holds about a block (`stageFixRec`'s block-fact hypotheses, at the
carrier storing the former and the constructors) make the block's
representation `IndRep` (`ConLeche/Model/IndRep.lean`), with the
functor `fixFunVI` and the tagged-tower injections.  Two kits on the
way: the X-chains ignore the entries at recursive positions (the slot
is spelled instead), so every chain notion is congruent along an
agreement off those positions (`chainsXI_congr`, `XChainsOk.congr`) —
which identifies the functor spelled from the DUMMY former's readings
(the leaf's, `fssZ`) with the one spelled from the real readings (the
datum's `Fss`); and the fibre's membership is exactly the fitting of a
field spine (`fixStepI_iff`, both regimes).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps NativeParts
  RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Congruence of the chains off the recursive positions -/

section Congr

variable {u : Nat} {Ids : List AnnotTerm} {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Eis : List (List AnnotTerm)}

/-- Two chains agreeing off the recursive positions from `i` on. -/
@[expose] def AgreeOffRec (rs : List Bool) (i : Nat) (Fs Fs' : List AnnotTerm) : Prop :=
  Fs.length = Fs'.length ∧
  ∀ l, l < Fs.length → rs.getD (i + l) false = false → Fs.getD l default = Fs'.getD l default

omit [SetTheory V] in
theorem AgreeOffRec.tail {i : Nat} {F F' : AnnotTerm} {Fs Fs' : List AnnotTerm}
    (h : AgreeOffRec rs i (F :: Fs) (F' :: Fs')) : AgreeOffRec rs (i + 1) Fs Fs' := by
  refine ⟨by simpa using h.1, fun l hl hr => ?_⟩
  have := h.2 (l + 1) (by simp; omega) (by rw [show i + (l + 1) = i + 1 + l from by omega]; exact hr)
  simpa using this

omit [SetTheory V] in
theorem AgreeOffRec.head {i : Nat} {F F' : AnnotTerm} {Fs Fs' : List AnnotTerm}
    (h : AgreeOffRec rs i (F :: Fs) (F' :: Fs')) (hr : rs.getD i false = false) : F = F' := by
  have := h.2 0 (by simp) (by simpa using hr)
  simpa using this

omit [SetTheory V] in
theorem xEntry_congr {i : Nat} {F F' : AnnotTerm} {Fs Fs' : List AnnotTerm}
    (h : AgreeOffRec rs i (F :: Fs) (F' :: Fs')) :
    xEntry u Ids rs tls Eis F i = xEntry u Ids rs tls Eis F' i := by
  unfold xEntry
  by_cases hr : rs.getD i false = true
  · rw [if_pos hr, if_pos hr]
  · have hr' : rs.getD i false = false := by simpa using hr
    rw [if_neg hr, if_neg hr, h.head hr']

omit [SetTheory V] in
theorem chainXIGo_congr :
    ∀ (Fs Fs' : List AnnotTerm) (i : Nat), AgreeOffRec rs i Fs Fs' →
      chainXIGo u Ids rs tls Eis Fs i = chainXIGo u Ids rs tls Eis Fs' i
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h.1
  | _ :: _, [], _, h => nomatch h.1
  | F :: Fs, F' :: Fs', i, h => by
    rw [chainXIGo_cons, chainXIGo_cons, xEntry_congr h, chainXIGo_congr Fs Fs' (i + 1) h.tail]

omit [SetTheory V] in
theorem chainXI_congr {nIdx : Nat} {Es : List AnnotTerm} {Fs Fs' : List AnnotTerm}
    (h : AgreeOffRec rs 0 Fs Fs') :
    chainXI u Ids nIdx rs tls Eis Fs Es = chainXI u Ids nIdx rs tls Eis Fs' Es := by
  unfold chainXI
  rw [chainXIGo_congr Fs Fs' 0 h, h.1]

/-- Two chain lists agreeing off the recursive positions. -/
@[expose] def AgreeOffRecs (rss : List (List Bool)) (Fss Fss' : List (List AnnotTerm)) : Prop :=
  Fss.length = Fss'.length ∧
  ∀ j, j < Fss.length → AgreeOffRec (rss.getD j []) 0 (Fss.getD j []) (Fss'.getD j [])

omit [SetTheory V] in
theorem chainsXI_congr {nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : AgreeOffRecs rss Fss Fss') :
    chainsXI u Ids nIdx rss tlss Eiss Fss Ess = chainsXI u Ids nIdx rss tlss Eiss Fss' Ess := by
  unfold chainsXI
  rw [← h.1]
  apply List.map_congr_left
  intro j hj
  exact chainXI_congr (h.2 j (List.mem_range.mp hj))

theorem fixStepI_congr {w : Nat} {ρp : Nat → V} {nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : AgreeOffRecs rss Fss Fss') (X t : V) :
    fixStepI u w ρp Ids nIdx rss tlss Eiss Fss Ess X t
      = fixStepI u w ρp Ids nIdx rss tlss Eiss Fss' Ess X t := by
  unfold fixStepI; rw [chainsXI_congr h]

theorem fixFunVI_congr {w : Nat} {ρp : Nat → V} {nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : AgreeOffRecs rss Fss Fss') :
    fixFunVI u w ρp Ids nIdx rss tlss Eiss Fss Ess = fixFunVI u w ρp Ids nIdx rss tlss Eiss Fss' Ess := by
  unfold fixFunVI famFI
  simp only [fixStepI_congr h]

theorem fixFamI_congr {w : Nat} {ρp : Nat → V} {nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : AgreeOffRecs rss Fss Fss') :
    fixFamI u w ρp Ids nIdx rss tlss Eiss Fss Ess = fixFamI u w ρp Ids nIdx rss tlss Eiss Fss' Ess := by
  unfold fixFamI; rw [fixFunVI_congr h]

theorem slotsFitX_congr {w : Nat} {ρp : Nat → V} {X t : V} :
    ∀ (Fs Fs' : List AnnotTerm) (i : Nat) (as : List V), AgreeOffRec rs i Fs Fs' →
      (SlotsFitX u w ρp Ids rs tls Eis X t i as Fs ↔ SlotsFitX u w ρp Ids rs tls Eis X t i as Fs')
  | [], [], _, _, _ => Iff.rfl
  | [], _ :: _, _, _, h => nomatch h.1
  | _ :: _, [], _, _, h => nomatch h.1
  | F :: Fs, F' :: Fs', i, as, h => by
    simp only [SlotsFitX]
    rw [xEntry_congr h]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun a ha => (slotsFitX_congr Fs Fs' (i + 1) (as ++ [a]) h.tail).mp (h2 a ha)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun a ha => (slotsFitX_congr Fs Fs' (i + 1) (as ++ [a]) h.tail).mpr (h2 a ha)⟩

/-- The functor's premise is congruent off the recursive positions. -/
theorem xChainsOk_congr {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : XChainsOk u w ρp Ids rss tlss Eiss Fss Ess)
    (hag : AgreeOffRecs rss Fss Fss') :
    XChainsOk u w ρp Ids rss tlss Eiss Fss' Ess where
  hI := h.hI
  hok := by
    intro X hX t ht
    rw [← chainsXI_congr hag]
    exact h.hok X hX t ht
  hfit := by
    intro X hX t ht j hj
    rw [← hag.1] at hj
    exact (slotsFitX_congr _ _ 0 [] (hag.2 j hj)).mp (h.hfit X hX t ht j hj)
  hclosed := by
    rw [← fixFunVI_congr hag]
    exact h.hclosed

end Congr

/-! ## The fibre's membership, both regimes -/

/-- **The functor's fibre**: a member is the injection of a field spine
fitting some constructor's X-chain at `(X, t)`, and conversely. -/
theorem fixStepI_iff {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Ess : List (List AnnotTerm)} {X t x : V} :
    x ∈ˢ fixStepI u w ρp Ids Ids.length rss tlss Eiss Fss Ess X t ↔
      ∃ j fs, j < Fss.length ∧ fs.length = (Fss.getD j []).length ∧
        SpineFit (cons t (cons X ρp))
          (chainXIGo u Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) 0) fs ∧
        EqAll (consList fs (cons t (cons X ρp)))
          (eqsXI Ids.length (Fss.getD j []).length (Ess.getD j [])) ∧
        x = injW w j (mkTower (fs ++ [pt])) := by
  by_cases hw : w = 0
  · subst hw
    constructor
    · intro hx
      obtain ⟨rfl, j, fs, hj, hlen, hsp, hall⟩ := fixStepI_zero_elim hx
      exact ⟨j, fs, hj, hlen, hsp, hall, (injW_zero _ _).symm⟩
    · rintro ⟨j, fs, hj, hlen, hsp, hall, rfl⟩
      rw [injW_zero]
      unfold fixStepI
      refine pt_mem_sumSet_zero (i := j) (a := pt) ?_
      rw [sumFibre_of_getElem? (by rw [chainsXI_getElem?, if_pos hj])]
      unfold chainXI
      exact pt_mem_tower_teleOfFields (spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, hall⟩)
  · constructor
    · intro hx
      obtain ⟨j, fs, rfl, hj, hlen, hsp, hall⟩ := fixStepI_elim hw hx
      exact ⟨j, fs, hj, hlen, hsp, hall, (injW_pos hw _ _).symm⟩
    · rintro ⟨j, fs, hj, hlen, hsp, hall, rfl⟩
      rw [injW_pos hw]
      unfold fixStepI
      refine inj_mem hw ?_
      rw [sumFibre_of_getElem? (by rw [chainsXI_getElem?, if_pos hj])]
      unfold chainXI
      exact mkTower_mem_teleOfFields hw (spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, hall⟩)

/-! ## The rules' constructors -/

omit [SetTheory V] in
/-- The stored rules name the constructors in order. -/
theorem sumRules_map_ctor {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr}, rhss.length = ctorsA.length →
      (ConLeche.sumRules find? recName nP mI rP recTy ctorsA rhss).map (·.ctor)
        = ctorsA.map (·.1.name)
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | c :: cs, rhs :: rhss, h => by
    simp only [ConLeche.sumRules, List.map_cons, ConLeche.recRuleBits_ctor]
    rw [sumRules_map_ctor (by simpa using h)]

/-! ## The datum and the representation -/

/-- **The datum of a natively installed block**: the fixpoint route's
data, the functor `fixFunVI` and the tagged-tower injections. -/
@[expose] noncomputable def fixRepData (p : NativeParts) (env₀ : Env)
    (ctorsA : List (ConstantVal × Nat)) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List RecFieldKind) (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (uAV : (Name → Nat) → Nat) :
    IndRepData V where
  nP := p.nP
  nIdx := p.nIdx
  resSort := p.resSort
  isProp := p.isProp
  large := p.large
  env₀ := env₀
  ctorsA := ctorsA
  idxF := idxF
  dsF := dsF
  esF := esF
  srcsF := srcsF
  ksF := ksF
  fvsPF := fvsPF
  xFvsF := xFvsF
  xrestF := xrestF
  eissF := eissF
  tssF := tssF
  pps := ppsAll
  u := uAV
  Φ := fun ψ ρp =>
    fixFunVI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
      (((ppsAll ψ).drop p.nP).map (·.2.2)).length (rssOfK ksF ctorsA.length)
      (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
  inj := fun ψ j fs => injW (p.resSort.eval ψ) j (mkTower (fs ++ [pt]))

set_option maxHeartbeats 3200000 in
/-- **A natively installed block is represented**, from the recursor
stage's block facts (`stageFixRec`'s hypotheses at the carrier storing
the former and the constructors). -/
theorem indRep_of_stage {p : NativeParts} (m : EnvModel V env)
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {mI rP : Nat}
    (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    (hlenR : rhss.length = ctorsA.length)
    {bsT : List (Expr × ConLeche.BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    {env₀ : Env} {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt m env₀ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF i cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    {uAV : (Name → Nat) → Nat}
    (hUparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) → uAV ψ₁ = uAV ψ₂)
    {fssZ : (Name → Nat) → List (List AnnotTerm)}
    (hleafT : ∀ ψ, m.acval p.cvT.name ψ
      = nativeTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (((ppsAll ψ).drop p.nP).map (·.2.2))
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hagree : ∀ ψ, AgreeOffRecs (rssOfK ksF ctorsA.length) (fssZ ψ)
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, m.acval cA.1.name ψ
      = sumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hframes : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      ∀ j, j < ctorsA.length →
        FieldsOkB (p.resSort.eval ψ) ρp
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [])) :
    IndRep m p.cvT.name cvTa cvRa mI rP
      (ConLeche.sumRules env.find? cvRa.name p.nP mI rP cvRa.type ctorsA rhss)
      (fixRepData p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll uAV) := by
  -- the pieces, named
  let d : IndRepData V :=
    fixRepData p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll uAV
  show IndRep m p.cvT.name cvTa cvRa mI rP _ d
  have hIds : ∀ ψ, d.Ids ψ = ((ppsAll ψ).drop p.nP).map (·.2.2) := fun _ => rfl
  have hparams : ∀ ψ, d.params ψ = ((ppsAll ψ).take p.nP).map (·.2.2) := fun _ => rfl
  have hFss : ∀ ψ, d.Fss ψ = fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) :=
    fun _ => rfl
  have hw : ∀ ψ, d.w ψ = p.resSort.eval ψ := fun _ => rfl
  have hlenFss : ∀ ψ,
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).length = ctorsA.length := by
    intro ψ
    rw [fssOfR, List.length_map, fixCtorDataList_length]
  have hFssD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (d.Fss ψ).getD j [] = ((dsF j ψ).drop p.nP).map (·.2.2) := by
    intro ψ j cA hj
    show (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [] = _
    rw [List.getD_eq_getElem?_getD, fssOfR, List.getElem?_map, fixCtorDataList_getElem?, Nat.zero_add,
      hj]
    rfl
  have hFssE : ∀ ψ j cA, ctorsA[j]? = some cA →
      (d.Fss ψ)[j]? = some (((dsF j ψ).drop p.nP).map (·.2.2)) := by
    intro ψ j cA hj
    show (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))[j]? = _
    rw [fssOfR, List.getElem?_map, fixCtorDataList_getElem?, Nat.zero_add, hj]
    rfl
  -- the chains at the datum's readings
  have hX : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      XChainsOk (d.u ψ) (d.w ψ) ρp (d.Ids ψ) d.rss (d.tlss ψ) (d.Eiss ψ) (d.Fss ψ) (d.Ess ψ) :=
    fun ψ ρp hρ => xChainsOk_congr (hframes ψ ρp hρ).1 (hagree ψ)
  have hlenP : ∀ ψ, (d.params ψ).length = p.nP := by
    intro ψ
    rw [hparams, List.length_map, List.length_take, hFD.len ψ]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  refine {
    strip := ⟨bsT, hstripT⟩
    isProp := hProp
    mI := hmI
    rP := hrP
    rules := sumRules_map_ctor hlenR
    former := hFD
    ctors := fun j cA hj => by rw [hlpsT]; exact hcf j cA hj
    idxRes := hidxRes
    uParams := fun ψ₁ ψ₂ hq => hUparams ψ₁ ψ₂ (fun q hq' => hq q (by rw [hlpsT]; exact hq'))
    paramsIff := hiff
    chains := fun ψ ρp hρ => xChainsOk_toChainsOk (hX ψ ρp hρ)
    functor := fun ψ ρp hρ => ⟨fixFunVI_mem (hX ψ ρp hρ).hok, fixFunVI_mono (hX ψ ρp hρ),
      fixFunVI_maps (hX ψ ρp hρ), fixFunVI_closed_exists (hX ψ ρp hρ)⟩
    fibre := ?_
    leaf := ?_
    ctor := ?_
    mkZero := fun ψ hz j fs => by
      show injW (p.resSort.eval ψ) j _ = pt
      rw [show p.resSort.eval ψ = 0 from hz, injW_zero]
    mkInj := ?_ }
  · -- the fibre
    intro ψ ρp hρ X hX t ht x
    have hXs : X ∈ˢ lfpFamSpace V (p.resSort.eval ψ)
        (idxSet (uAV ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))) := by
      rw [lfpFamSpace_eq]; exact hX
    have ht' : t ∈ˢ idxSet (uAV ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) := ht
    show x ∈ˢ app (app (fixFunVI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
      (((ppsAll ψ).drop p.nP).map (·.2.2)).length (rssOfK ksF ctorsA.length)
      (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))) X) t ↔ _
    rw [fixFunVI_app hXs, famFI_app ht', fixStepI_iff]
    constructor
    · rintro ⟨j, fs, hj, hlen, hsp, hall, rfl⟩
      exact ⟨j, fs, by show j < ctorsA.length; rw [← hlenFss ψ]; exact hj, ⟨hlen, hsp, hall⟩, rfl⟩
    · rintro ⟨j, fs, hj, ⟨hlen, hsp, hall⟩, rfl⟩
      refine ⟨j, fs, ?_, hlen, hsp, hall, rfl⟩
      show j < (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).length
      rw [hlenFss ψ]; exact hj
  · -- the leaf
    intro ψ ρ as is hsp₁ hsp₂
    have hislen : is.length = (d.Ids ψ).length := hsp₂.length_eq
    have hsat : Sat V (d.params ψ).reverse (consList as ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
      simpa using this
    have hspAll : SpineFit ρ ((ppsAll ψ).map (·.2.2)) (as ++ is) := by
      have : (ppsAll ψ).map (·.2.2) = d.params ψ ++ d.Ids ψ := by
        rw [hparams, hIds, ← List.map_append, List.take_append_drop]
      rw [this]
      exact hsp₁.append hsp₂
    have hframe : consList (as ++ is) ρ = consList is (consList as ρ) := consList_append _ _ _
    have hshift : shiftE (d.Ids ψ).length 0 (consList (as ++ is) ρ) = consList as ρ := by
      rw [hframe, ← hislen]; exact shiftE_consList _ _
    have hfr : ConLeche.Semantics.frameIdx (d.Ids ψ).length (consList (as ++ is) ρ) = is := by
      rw [hframe, ← hislen]; exact frameIdx_consList' _ _
    have hXZ := (hframes ψ (consList as ρ) hsat).1
    have hbase : FixBaseI (uAV ψ) (p.resSort.eval ψ) (consList (as ++ is) ρ) (d.Ids ψ) d.rss
        (d.tlss ψ) (d.Eiss ψ) (fssZ ψ) (d.Ess ψ) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hshift]; exact hXZ.hI
      · rw [hshift]; exact hXZ.hok
      · rw [hshift, hfr]; exact hsp₂
    rw [hleafT ψ]
    have hfold := nativeTyAVI_fold hspAll hbase
    rw [hshift, hfr] at hfold
    refine hfold.trans ?_
    have hag' : AgreeOffRecs d.rss (fssZ ψ) (d.Fss ψ) := hagree ψ
    rw [fixFamI_congr hag']
    rfl
  · -- the constructors
    intro j cA hj ψ ρ as fs hsp₁ hsp₂
    have hlenD : (dsF j ψ).length = p.nP + cA.2 := (hcf j cA hj).2.2.len ψ
    have hsat : Sat V (d.params ψ).reverse (consList as ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
      simpa using this
    have hsp₁' : SpineFit ρ ((((dsF j ψ).take p.nP)).map (·.2.2)) as := by
      refine (spineFit_iff_of_sat_iff (Ds₁ := d.params ψ) ?_ (fun ρ' => hiff j cA hj ψ ρ') ρ as
        (by rw [hsp₁.length_eq])).mp hsp₁
      rw [hlenP, List.length_map, List.length_take, hlenD]
      exact (Nat.min_eq_left (Nat.le_add_right _ _)).symm
    rw [hleafC j cA hj ψ]
    have hsplit : dsF j ψ = (dsF j ψ).take p.nP ++ (dsF j ψ).drop p.nP :=
      (List.take_append_drop _ _).symm
    by_cases hz : p.resSort.eval ψ = 0
    · rw [hz, sumMkAV_zero, foldl_app_pt']
      show pt = injW (p.resSort.eval ψ) j _
      rw [hz, injW_zero]
    · show _ = injW (p.resSort.eval ψ) j (mkTower (fs ++ [pt]))
      rw [injW_pos hz]
      have hok : SumFieldsOkB (p.resSort.eval ψ) (consList as ρ) (uChains (d.Fss ψ)) := by
        refine SumFieldsOkB_uChains fun Fs hFs => ?_
        obtain ⟨j', hj'⟩ := List.getElem?_of_mem hFs
        have hj'lt : j' < ctorsA.length := by
          rw [← hlenFss ψ]; exact (List.getElem?_eq_some_iff.mp hj').1
        have := (hframes ψ (consList as ρ) hsat).2 j' hj'lt
        rw [← hFss, List.getD_eq_getElem?_getD, hj'] at this
        exact this
      have hjU : (uChains (d.Fss ψ))[j]? = some ((((dsF j ψ).drop p.nP).map (·.2.2)) ++ [idxEqAV []]) := by
        rw [uChains_getElem?, hFssE ψ j cA hj]; rfl
      rw [hFssD ψ j cA hj] at hsp₂
      have := sumMkAV_fold (V := V) hz (pds := (dsF j ψ).take p.nP) (fds := (dsF j ψ).drop p.nP)
        (Fss := uChains (d.Fss ψ)) (ρ := ρ) hsp₁' hsp₂ hok hjU
      rw [← hsplit] at this
      exact this
  · -- injectivity
    intro ψ hz j fs j' fs' hj hj' hlen hlen' heq
    have heq' : injW (p.resSort.eval ψ) j (mkTower (fs ++ [pt]))
        = injW (p.resSort.eval ψ) j' (mkTower (fs' ++ [pt])) := heq
    rw [injW_pos (w := p.resSort.eval ψ) hz, injW_pos (w := p.resSort.eval ψ) hz] at heq'
    obtain ⟨rfl, htow⟩ := inj_inj heq'
    refine ⟨rfl, ?_⟩
    have := mkTower_inj (by rw [List.length_append, List.length_append, hlen, hlen']) htow
    exact List.append_cancel_right this

end ConLeche.Model
