module

public import ConLeche.Model.Inductives.NestedRecFrames2
import ConLeche.Model.Inductives.BlockRecWD
import ConLeche.Model.Inductives.BlockRecEq
public import ConLeche.Model.Inductives.MutualRecsStage
public section

/-!
# The rules' equations at the restored readings (task #315, M7-2)

PLAN-M7 §2–3 (DESIGN §U.25 (e) 3–4): `NestedRecEqs` at the nested
block — the equations `eqs` of the recursors' stage are the SCRATCH
(auxiliary) block's own (`BlockModel.recEqs` at `DA`), and they are

* GRADED at every tuple typed at the RESTORED readings (`heq`) — by
  the mutual `IsBlockModels.blockEq_wd` at `DA`, whose hypothesis
  wants the tuple typed at the SCRATCH readings: the two Π-towers
  are ONE SET at every frame (`NestedTailIn.towerAgree`, the whole-tower
  corollary of the walk's reading law — the transfer's position-by-position
  agreement `domAgree_transfer` pushed through `piR_congr` down the
  tower, the bits being the same `pwBit` on both sides and the
  conclusions one `mutualConcAV`);
* satisfied at the CANDIDATE tuple (`hceq`) — PLAN-M7 §2.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## Kit: two Π-towers that agree position by position are one set -/

/-- **The whole-tower congruence**: two Π-towers of one length over
one conclusion, whose binder bits are equal and whose domains
interpret alike at every spine fitting the FIRST tower's prefix there,
interpret alike. -/
theorem interp_mkPisAV_congr {conc : AnnotTerm} :
    ∀ {rds rds' : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}, rds.length = rds'.length →
      (∀ (l : Nat), l < rds.length → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ ((rds.map (·.2.2)).take l) fs₁ →
        (rds.getD l default).2.1 = (rds'.getD l default).2.1 ∧
          interp V (consList fs₁ ρ) ((rds.map (·.2.2)).getD l default)
            = interp V (consList fs₁ ρ) ((rds'.map (·.2.2)).getD l default)) →
      interp V ρ (mkPisAV rds conc) = interp V ρ (mkPisAV rds' conc)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | d :: ds, d' :: ds', ρ, hlen, hag => by
    obtain ⟨hbit0, hdom0⟩ := hag 0 (by simp) [] rfl (by rw [List.take_zero]; trivial)
    simp only [List.getD_cons_zero, List.map_cons, consList_nil] at hbit0 hdom0
    show piR d.2.1 (interp V ρ d.2.2) (fun x => interp V (cons x ρ) (mkPisAV ds conc))
      = piR d'.2.1 (interp V ρ d'.2.2) (fun x => interp V (cons x ρ) (mkPisAV ds' conc))
    rw [hbit0, ← hdom0]
    refine piR_congr fun x hx => ?_
    refine interp_mkPisAV_congr (by simpa using hlen) fun l hl fs₁ hlf hf => ?_
    have h := hag (l + 1) (by simp only [List.length_cons]; omega) (x :: fs₁)
      (by simp only [List.length_cons, hlf]) ?_
    · simpa only [List.getD_cons_succ, List.map_cons, consList_cons] using h
    · simp only [List.map_cons, List.take_succ_cons]
      exact ⟨hx, hf⟩

/-! ## The run's section -/

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

local notation "ENV2" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

/-- the COMPOSED nested block's block model -/
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

/-- the SCRATCH (auxiliary) block's block model — the MUTUAL one -/
local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

/-- the pins' constructors at the nested block model -/
local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

/-- the pin groups at the restored environment's model -/
local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I

/-! ### The conclusion and the tower -/

/-- The SCRATCH recursor type's conclusion at class `c` is the
restored one's: the classes, the minors and the class's index count
are the auxiliary block's. -/
theorem NestedTailIn.blockConcA_eq {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    {c : Nat} (hc : c < b.k) :
    (DA).blockConc c = mutualConcAV b.k b.ctors.length (fms.getD c default).nIdx c := by
  obtain ⟨f, hf⟩ : ∃ f, fms[c]? = some f :=
    ⟨_, List.getElem?_eq_getElem (by rw [I.out.facts.lenFms]; exact hc)⟩
  have hfD : (fms.getD c default).nIdx = f.nIdx := by rw [List.getD_eq_getElem?_getD, hf]; rfl
  show mutualConcAV (DA).k (DA).nCtors ((DA).nIdxAt c) c = _
  rw [I.nCtorsA_eq S, mutualBlockModel_nIdxAt hf, hfD]
  rfl

/-- **THE TOWER AGREEMENT** (PLAN-M7 §3): class `c`'s RESTORED
recursor type's reading and the SCRATCH one's are ONE SET at every
frame — the transfer's position-by-position agreement
(`domAgree_transfer`) pushed through the whole tower
(`interp_mkPisAV_congr`), the bits being `pwBit ψ (zeronessOf
elimLevel)` on both sides (`classRecTy`, `mem_mutualRecDataAV`) and
the conclusions one (`blockConcA_eq`). -/
theorem NestedTailIn.towerAgree {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored pinsS)
    {c : Nat} (hc : c < b.k) (ψ : Name → Nat) (ρ : Nat → V)
    {rdsR : List (Nat × Nat × AnnotTerm)} {conc : AnnotTerm}
    (hread : denoteMeta mp₂.base2.acval (ENV2) ψ 0 (nestedRecCvAt p.k cvRms cvRns c).type
      = some (mkPisAV rdsR conc))
    (hlenR : rdsR.length = b.nP + (b.k + b.ctors.length + ((fms.getD c default).nIdx + 1))) :
    interp V ρ (mkPisAV rdsR conc)
      = interp V ρ (mkPisAV ((DA).blockRds mpA.base2 b.elimLevel c ψ) ((DA).blockConc c)) := by
  obtain ⟨-, u, rds, -, hspec⟩ := I.classRecTy hc
  obtain ⟨hr, hl, hbits, -, -⟩ := hspec ψ
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (by rw [hlenR, hl]) (Option.some.inj (hread.symm.trans hr))
  rw [I.blockConcA_eq S hc]
  refine interp_mkPisAV_congr (by rw [hlenR, I.auxRdsLen S hc ψ]) fun l hl' fs₁ hlf hf => ?_
  refine ⟨?_, I.domAgree_transfer S hnames hctorsJ hK35 hc ψ ρ hread hlenR l
    (by rw [List.length_map]; exact hl') fs₁ hlf hf⟩
  have hmemR : (rds ψ).getD l default ∈ rds ψ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']
    exact List.getElem_mem hl'
  have hmemA : ((DA).blockRds mpA.base2 b.elimLevel c ψ).getD l default
      ∈ (DA).blockRds mpA.base2 b.elimLevel c ψ := by
    have hl'' : l < ((DA).blockRds mpA.base2 b.elimLevel c ψ).length := by
      rw [I.auxRdsLen S hc ψ, ← hlenR]; exact hl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl'']
    exact List.getElem_mem hl''
  rw [(hbits _ hmemR).2, mem_mutualRecDataAV hmemA]

/-! ### The readings, class by class -/

omit I in
/-- Class `c`'s restored recursor type reads to the record's Π-tower —
the record's `readM` below `k`, its `readN` above. -/
theorem NestedTailIn.readAtOf {s : (Name → Nat) → Nat}
    {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {concM : Nat → AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    {c : Nat} (hc : c < (D).kT) (ψ : Name → Nat) :
    denoteMeta mp₂.base2.acval (ENV2) ψ 0 (nestedRecCvAt p.k cvRms cvRns c).type
      = some (mkPisAV (rdsM c ψ) (concM c)) := by
  have hkD : (D).k = p.k := rfl
  have hkT : (D).kT = (D).k + (D).nPins := rfl
  by_cases hck : c < p.k
  · have hcv : nestedRecCvAt p.k cvRms cvRns c = cvRms.getD c default := by
      unfold nestedRecCvAt; rw [if_pos hck]
    rw [hcv]
    exact R.readM c (by rw [hkD]; exact hck) ψ
  · have hq : c - p.k < (D).nPins := by rw [hkT, hkD] at hc; omega
    have hcv : nestedRecCvAt p.k cvRms cvRns c = cvRns.getD (c - p.k) default := by
      unfold nestedRecCvAt; rw [if_neg hck]
    rw [hcv]
    have h := R.readN (c - p.k) hq ψ
    rw [show (D).k + (c - p.k) = c from by rw [hkD]; omega] at h
    exact h

/-- The record's tower at class `c` has the auxiliary telescope's
length (the stage's bookkeeping rewritten to the auxiliary block's). -/
theorem NestedTailIn.lenAtOf {s : (Name → Nat) → Nat}
    {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {concM : Nat → AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    {c : Nat} (hc : c < b.k) (ψ : Name → Nat) :
    (rdsM c ψ).length = b.nP + (b.k + b.ctors.length + ((fms.getD c default).nIdx + 1)) := by
  have hlc := R.len c ψ (by rw [I.kT]; exact hc)
  rw [nestedBlockModel_nP, I.kT, I.nCtorsT, I.nIdxT hc] at hlc
  omega

/-! ### `heq` — the equations are graded at the restored readings -/

/-- **THE EQUATIONS ARE TRUTH VALUES AND GRADED** (PLAN-M7 §3,
`NestedRecEqs.heq`): at every tuple typed at the RESTORED readings,
every SCRATCH equation is `univZero`-valued (`specEqAV_univZero`) and
`WellDenoted` — the mutual `IsBlockModels.blockEq_wd` at the auxiliary
block, whose tuple hypothesis is the restored one carried across the
TOWER AGREEMENT. -/
theorem NestedTailIn.eqsWD {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
    (S : NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
      xrestF eissF tssF stored mpA cvRas)
    (hnames : NestedCtorPinNames env p st)
    (hctorsJ : ∀ (q₀ kJ i : Nat) (dJ : BlockModel V), PG mp₂.base2 q₀ kJ dJ → i < kJ →
      ∀ (ci : ContainerInfo) (J : ContainerMember),
        ConLeche.containerInfo? env ((D).pinAt (q₀ + i)).J = some ci → J ∈ ci.members →
        J.name = ((D).pinAt (q₀ + i)).J → (dJ.ctorsM i).map (·.1.name) = J.ctors.map (·.name))
    (hK35 : NestedRecTysAuxOk p st b stored pinsS)
    {s : (Name → Nat) → Nat} {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {concM : Nat → AnnotTerm}
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM)
    (ψ : Name → Nat) (ρ : Nat → V) {rs : List V} (hlen : rs.length = (D).kT)
    (hrs : ∀ c, c < (D).kT →
      rs.getD c pt ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c)))
    {e : AnnotTerm} (he : e ∈ (DA).recEqs mpA.base2 b.elimLevel ψ) :
    interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e := by
  -- the tuple, at the SCRATCH readings
  have hkA : (DA).k = b.k := S.record.k
  have hlenA : rs.length = (DA).k := by rw [hkA, ← I.kT]; exact hlen
  have hrsA : ∀ mm, mm < (DA).k → rs.getD mm pt ∈ˢ interp V ρ
      (mkPisAV ((DA).blockRds mpA.base2 b.elimLevel mm ψ) ((DA).blockConc mm)) := by
    intro mm hmm
    rw [hkA] at hmm
    have hmmT : mm < (D).kT := by rw [I.kT]; exact hmm
    rw [← I.towerAgree S hnames hctorsJ hK35 hmm ψ ρ (NestedTailIn.readAtOf R hmmT ψ) (I.lenAtOf R hmm ψ)]
    exact hrs mm hmmT
  -- the scratch towers are graded
  have hokT : ∀ mm, mm < (DA).k → ∀ ρ' : Nat → V,
      WellDenoted V ρ' (mkPisAV ((DA).blockRds mpA.base2 b.elimLevel mm ψ) ((DA).blockConc mm)) :=
    fun mm hmm ρ' => ((S.recData mm (by rw [← hkA]; exact hmm)).1.okTy ψ ρ').1
  obtain ⟨c, j, cA, hc, hj, rfl⟩ := (DA).mem_specEqs he
  exact ⟨specEqAV_univZero _ _ _ _,
    S.reps.blockEq_wd rfl (S.typed ψ).1 (S.typed ψ).2 (S.readings ψ) hokT ρ hlenA hrsA hc hj⟩

end Run

end ConLeche.Model
