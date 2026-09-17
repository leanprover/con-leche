module

public import ConLeche.Model.Inductives.NestedRecFrames2
import ConLeche.Model.Inductives.BlockRecWD
import ConLeche.Model.Inductives.BlockRecValid
import ConLeche.Model.Inductives.BlockRecLeaf
import ConLeche.Model.Inductives.BlockRecEq
import ConLeche.Model.Inductives.BlockRecFrames
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
    interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e ∧
      AnnotValid V (consList rs ρ) e := by
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
    S.reps.blockEq_wd rfl (S.typed ψ).1 (S.typed ψ).2 (S.readings ψ) hokT ρ hlenA hrsA hc hj,
    S.reps.blockEq_valid rfl (S.typed ψ).1 (S.typed ψ).2 (fun n ρ' => mpA.acval_validV n _ ρ')
      (S.readings ψ) (fun mm hmm ρ' => (S.recData mm (by rw [← hkA]; exact hmm)).1.okTy ψ ρ')
      ρ hlenA hrsA hc hj⟩

/-! ### `hceq` — the equations at the candidate -/

/-- **THE RULES' EQUATIONS HOLD AT THE CANDIDATE** (PLAN-M7 §2,
`NestedRecEqs.hceq`): at the tuple of the `k + nPins` CLASS candidates
(`blockCandT` over the RESTORED readings) every SCRATCH equation
holds.

The rule's spine fits the SCRATCH rule data (the equation's own), so
its prefix decomposes into the auxiliary block's frame
(`spineFit_prefix_inv`) and the whole spine fits the scratch recursor
type's reading (`spineFit_recData_of`) — and therefore, BY THE
TRANSFER, the RESTORED one's, which is what the candidate's λ-tower
consumes (`lamTower_fold`).  Its leaf is the class recursor at the
frame (`blockLeafVT_at`), whose ι rule at the constructor's value is
the frame's minor folded along the fields and the inductive hypotheses
(`blockRecAtT_iota`, lane L-D) — the frame's two typings being the
scratch frame's carried over by `motivesAt`/`minorsAt`, its field
chain the scratch one's (`fitsFrom_iff`, the index equations read off
the tuple) and its injection the copy's (`nestedInjT_eq`).  The
right-hand side's ih applications read to λ-towers over the fields'
telescopes (`interp_ihAppAVK_at`) whose leaves are the TARGET class's
candidate at the same transfer, i.e. the graph's value at the
predecessor (`kitPredT_mem`, `app_graph`).  At `ℓ = 0` both sides are
the point. -/
theorem NestedTailIn.eqsCand {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
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
    (ψ : Name → Nat) (ρ : Nat → V) {e : AnnotTerm}
    (he : e ∈ (DA).recEqs mpA.base2 b.elimLevel ψ) :
    (pt : V) ∈ˢ interp V
      (consList ((List.range (D).kT).map fun t =>
        (D).blockCandT PC ψ (b.elimLevel.eval ψ) (rdsM t ψ) t ρ) ρ) e := by
  obtain ⟨c, j, cA, hc, hj, rfl⟩ := (DA).mem_specEqs he
  have hreps := S.reps
  have hfT := (S.typed ψ).1
  have hR := S.readings ψ
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  obtain ⟨cvT0, cvR0, mI0, rP0, rules0, hD0⟩ := I.out.reps 0 I.kpos
  have hcd := h.ctorData hj
  have hj' : j < ((DA).ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
  have hpl := hreps.params_length (by omega) ψ
  have hb : pwBit ψ (Level.zeronessOf b.elimLevel) = 0 ↔ b.elimLevel.eval ψ = 0 :=
    pwBit_zeronessOf ψ b.elimLevel
  have hJ := (DA).minorIdx_lt hc hj'
  have hkA : (DA).k = b.k := S.record.k
  have hkTA : (D).kT = (DA).k := by rw [I.kT, hkA]
  have hcb : c < b.k := by rw [← hkA]; exact hc
  have hcT : c < (D).kT := by rw [hkTA]; exact hc
  have hjT : j < ((D).ctorsT PC c).length := by rw [I.ctorsT_length c]; exact hj'
  -- the tuple frame
  generalize hcands : ((List.range (D).kT).map fun t =>
    (D).blockCandT PC ψ (b.elimLevel.eval ψ) (rdsM t ψ) t ρ) = cands
  have hcandsLen : cands.length = (DA).k := by
    rw [← hcands, List.length_map, List.length_range, hkTA]
  have hcandsD : ∀ t, t < (DA).k → cands.getD t pt
      = (D).blockCandT PC ψ (b.elimLevel.eval ψ) (rdsM t ψ) t ρ := by
    intro t ht
    rw [← hcands, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by rw [hkTA]; exact ht)]
    rfl
  have hρcD : ∀ t, t < (DA).k → consList cands ρ ((DA).k - 1 - t) = cands.getD t pt := by
    intro t ht
    rw [consList_apply_lt' _ _ (by omega), hcandsLen,
      show (DA).k - 1 - ((DA).k - 1 - t) = t from by omega]
  rw [pt_mem_specEqAV_iff]
  intro xs hxs
  rw [mutualRuleDataAV_eq_prefix, List.map_append] at hxs
  obtain ⟨xs₁, fs, rfl, hpre, hfsL⟩ := spineFit_append_inv hxs
  -- the prefix, at the base frame
  have hbelowPre : DomsBelow 0 (recPrefixAV mpA.base2 ψ ((DA).recLs mpA.base2 ψ) (DA).nP
      (DA).recNIdxs b.elimLevel ((DA).recPps ψ) ((DA).recIpss ψ) ((DA).recCds ψ) (DA).recMots
      (DA).recTgts) := by
    have := hR.below c hc
    rw [mutualRecDataAV_eq_prefix] at this
    exact DomsBelow.append_left this
  have hpreρ := spineFit_transport₀ hbelowPre (ρ₂ := ρ) hpre
  obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hpreρ
  have hlenps : ps.length = (DA).nP := by rw [hF.params.length_eq, hpl]
  have hρp : Sat V ((DA).params ψ).reverse (consList ps ρ) := (DA).satOfSpine hF.params
  have hρpD : Sat V ((D).params ψ).reverse (consList ps ρ) := hρp
  have hspD : SpineFit ρ ((D).params ψ) ps := hF.params
  have hlenfs : fs.length = cA.2 := by
    rw [hfsL.length_eq, List.length_map, rebit_length, liftDoms_length, List.length_drop, hcd.len]
    omega
  have hlenMm : ((DA).recLs mpA.base2 ψ).length + ((DA).recCds ψ).length = (Msl ++ msl).length := by
    rw [List.length_append, hR.lsLen, hR.cdsLen, hF.mslLen, hF.minsLen]
  -- the fields, at both parameter frames
  have hfs' : SpineFit (consList ps (consList cands ρ)) (((DA).Fss c ψ).getD j []) fs := by
    rw [rebit_map_dom, spineFit_liftDoms, consList_append, consList_append,
      ← consList_append Msl msl, hlenMm, shiftE_consList] at hfsL
    rw [IsBlockModel.Fss_getD hj]; exact hfsL
  have hfs : SpineFit (consList ps ρ) (((DA).Fss c ψ).getD j []) fs := by
    rw [IsBlockModel.Fss_getD hj] at hfs' ⊢
    exact spineFit_transport (DomsBelow.drop (DA).nP (hcd.below ψ))
      (by rw [hlenps, Nat.zero_add]) hfs'
  have hEsρ : ((DA).esF c j ψ).map (interp V (consList fs (consList ps (consList cands ρ))))
      = ((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ))) := by
    apply List.map_congr_left
    intro E hE
    rw [← consList_append ps fs (consList cands ρ), ← consList_append ps fs ρ]
    exact interp_closed_bottom (hcd.belowE ψ E hE) (by rw [List.length_append, hlenps, hlenfs]) _ _
  have hfr : consList (ps ++ Msl ++ msl ++ fs) (consList cands ρ)
      = consList fs (consList msl (consList Msl (consList ps (consList cands ρ)))) := by
    simp only [consList_append]
  rw [hfr]
  -- the frame's data functions, at the composed classes
  have hMs : (D).MotivesTypedT ψ (consList ps ρ) (b.elimLevel.eval ψ)
      (fun c' => if c' < (D).kT then Msl.getD c' pt else pt) :=
    I.motivesAt S ψ ρ hF.params hF.motives
  have hms : (D).MinorsTypedT PC ψ (consList ps ρ) (b.elimLevel.eval ψ)
      (fun c' => if c' < (D).kT then Msl.getD c' pt else pt)
      (fun J => if J < (D).nCtorsT PC then msl.getD J pt else pt) :=
    I.minorsAt S ψ ρ hF.params hF.mslLen hF.minsLen hF.motives hF.minors
  -- the left-hand side
  rw [interp_specLhsAV_at hlenps hF.mslLen hF.minsLen hlenfs, hρcD c hc, hcandsD c hc, hEsρ]
  have hC : interp V (consList fs (consList msl (consList Msl (consList ps (consList cands ρ)))))
      (AnnotTerm.mkAppN (mpA.base2.acval cA.1.name ψ)
        (paramBvarsAt (DA).nP ((DA).nP + (DA).k + (DA).nCtors + cA.2) ++ fieldBvars cA.2))
      = (DA).inj ψ c j fs := by
    rw [show consList fs (consList msl (consList Msl (consList ps (consList cands ρ))))
        = consList fs (consList (Msl ++ msl) (consList ps (consList cands ρ))) from by
          rw [consList_append],
      show (DA).nP + (DA).k + (DA).nCtors + cA.2 = (DA).nP + ((Msl ++ msl).length + cA.2) from by
        rw [List.length_append, hF.mslLen, hF.minsLen]; omega,
      interp_formerApp hlenfs _ (mpA.base2.cval_closedL _ ψ), ← hlenps,
      range_reverse_map_consList ps]
    have hρ₀ : (fun i => consList ps (consList cands ρ) (i + ps.length)) = consList cands ρ := by
      funext i; rw [consList_apply_add]
    rw [hρ₀]
    have hbP : DomsBelow 0 (rebit (pwBit ψ (Level.zeronessOf b.elimLevel)) ((DA).recPps ψ)) :=
      DomsBelow.append_left (DomsBelow.append_left hbelowPre)
    have hpsC : SpineFit (consList cands ρ) ((DA).params ψ) ps := by
      have := spineFit_transport₀ hbP (ρ₁ := ρ) (ρ₂ := consList cands ρ)
        (by rw [rebit_map_dom, hR.ppsDom]; exact hF.params)
      rw [rebit_map_dom, hR.ppsDom] at this
      exact this
    exact h.ctor c j cA hc hj ψ _ ps fs hpsC hfs'
  rw [hC]
  -- the right-hand side
  unfold specRuleCoreAV
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList fs (consList msl (consList Msl
    (consList ps (consList cands ρ)))))) (g := SetTheory.app), List.map_append, interp_bvar,
    show cA.2 + (DA).nCtors - 1 - (DA).minorIdx c j
        = ((DA).nCtors - 1 - (DA).minorIdx c j) + fs.length from by rw [hlenfs]; omega,
    consList_apply_add, consList_apply_lt' _ _ (by rw [hF.minsLen]; omega), hF.minsLen,
    show (DA).nCtors - 1 - ((DA).nCtors - 1 - (DA).minorIdx c j) = (DA).minorIdx c j from by omega,
    show fieldBvars cA.2 = (List.range cA.2).map (fun k => AnnotTerm.bvar (cA.2 - 1 - k)) from rfl,
    map_fieldBvars_interp hlenfs, List.map_map]
  rcases Classical.em (b.elimLevel.eval ψ = 0) with hℓ0 | hℓ
  · -- the `Prop` regime: both sides are the point
    have hne : rdsM c ψ ≠ [] := by
      intro hnil
      have hlc := I.lenAtOf R hcb ψ
      rw [hnil] at hlc
      simp at hlc
    have hpt : (D).blockCandT PC ψ (b.elimLevel.eval ψ) (rdsM c ψ) c ρ = pt := by
      unfold BlockModel.blockCandT
      cases hd : rdsM c ψ with
      | nil => exact absurd hd hne
      | cons d' ds' =>
        show lamR (b.elimLevel.eval ψ) _ _ = pt
        rw [hℓ0]; exact lamR_zero
    have hmpt : msl.getD ((DA).minorIdx c j) pt = pt := by
      have hmin := hF.minors c j cA hc hj
      rw [hb.mpr hℓ0] at hmin
      exact hreps.minor_eq_pt rfl hfT hc hj hρp (Msl := Msl)
        (msl' := msl.take ((DA).minorIdx c j)) (o := (DA).k + (DA).minorIdx c j)
        (by rw [hF.mslLen, List.length_take, hF.minsLen]; congr 1
            exact Nat.min_eq_left (Nat.le_of_lt hJ))
        hF.mslLen hℓ0 hF.motives hmin
    rw [hpt, hmpt, foldl_app_pt, foldl_app_pt]
  · have hwA : (DA).w ψ ≠ 0 := by
      intro hw0
      exact hℓ (ConLeche.Model.elimLevel_zero_of_w_zero I.large ψ hw0)
    have hwD : (D).w ψ ≠ 0 := by
      intro hw0
      exact hℓ (ConLeche.Model.elimLevel_zero_of_w_zero I.large ψ hw0)
    have hk : 0 < (DA).k := by omega
    -- the left-hand side is the class recursor at the frame
    have hEs : SpineFit (consList ps ρ) ((DA).IdsM c ψ)
        (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ)))) :=
      hreps.res_es_fit hfT hc hj hρp hfs
    have hinj := hreps.inj_mem hfT (PinsTyped.of_noPins rfl ψ) hc hj hρp hfs
    have hsp₁ := hreps.spineFit_recData_of hR hc hpreρ hF hEs hinj
    have hlenEs : (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ)))).length
        = (DA).nIdxAt c := by rw [List.length_map, hcd.lenE]
    have hsp₁R : SpineFit ρ ((rdsM c ψ).map (·.2.2))
        (ps ++ Msl ++ msl ++ ((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ)))
          ++ [(DA).inj ψ c j fs]) :=
      (I.spineFit_transfer S hnames hctorsJ hK35 hcb ψ ρ
        (NestedTailIn.readAtOf R hcT ψ) (I.lenAtOf R hcb ψ) _).mpr hsp₁
    -- the lengths at the composed classes
    have hMslT : Msl.length = (D).kT := by rw [hkTA]; exact hF.mslLen
    have hmslT : msl.length = (D).nCtorsT PC := by rw [I.nCtorsT_eq S]; exact hF.minsLen
    have hnIdxT : (D).nIdxT c = (DA).nIdxAt c := by
      obtain ⟨f, hf⟩ : ∃ f, fms[c]? = some f :=
        ⟨_, List.getElem?_eq_getElem (by rw [I.out.facts.lenFms]; exact hcb)⟩
      have hfD : (fms.getD c default).nIdx = f.nIdx := by
        rw [List.getD_eq_getElem?_getD, hf]; rfl
      rw [I.nIdxT hcb, hfD, mutualBlockModel_nIdxAt hf]
    have hisT : (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ)))).length
        = (D).nIdxT c := by rw [hnIdxT]; exact hlenEs
    unfold BlockModel.blockCandT
    rw [lamTower_fold hℓ hsp₁R,
      (D).blockLeafVT_at PC ψ (b.elimLevel.eval ψ) c ρ _ hMslT hmslT hisT]
    -- the ι rule at the candidate
    have hEsT : SpineFit ((D).frameT c ψ (consList ps ρ)) ((D).IdsT c ψ)
        (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ)))) :=
      (I.idsT_iff ψ ρ ps hcb _).mpr hEs
    have htmaj : (D).injT PC ψ c j fs ∈ˢ SetTheory.app ((D).famAt ψ (consList ps ρ)
        (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList ps ρ)) ((D).Φ ψ (consList ps ρ))) c)
        ((D).tupT ψ c (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ))))) := by
      rw [nestedInjT_eq]
      exact (I.majorAt ψ ρ ps hspD hcb hEs _).mp hinj
    have hidxT : (D).tupT ψ c (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ))))
        ∈ˢ (D).idxT ψ (consList ps ρ) c :=
      mem_idx_of_app_famSpace (hD0.famAt_mem hρpD (lfpTuple_mem _ _ _ _) hcT) htmaj
    have hfitL := hreps.fitsFrom_of_spineFit_go hfT (PinsTyped.of_noPins rfl ψ) hc hj hρp _ 0 []
      fs rfl trivial (by rw [consList_nil]; exact hfs)
    rw [consList_nil] at hfitL
    have hfitT : (D).ChainFitT PC ψ (consList ps ρ)
        ((D).famAt ψ (consList ps ρ)
          (lfpTuple ((D).w ψ) (D).k ((D).idx ψ (consList ps ρ)) ((D).Φ ψ (consList ps ρ))))
        ((D).tupT ψ c (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ))))) c j fs := by
      refine ⟨(I.fitsFrom_iff S ψ ρ ps hspD hcb hj fs).mp hfitL, fun l hl => ?_⟩
      have hl' : l < (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ)))).length := by
        rw [hEsT.length_eq]; exact hl
      unfold BlockModel.tupT
      rw [I.EssT_eq ψ hj, IsBlockModel.Ess_getD hj ψ,
        ← getD_eq_projS_tupW (I.idxOkT ψ (consList ps ρ) hρpD hcT) hEsT hl',
        List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by rw [List.length_map] at hl'; exact hl'), Option.map_some,
        Option.getD_some, Option.getD_some]
    rw [← nestedInjT_eq ψ c j fs,
      hD0.blockRecAtT_iota I.out.reps I.pinLaws hρpD hwD hMs hms hcT hidxT hjT hfitT]
    -- the minor and the inductive hypotheses
    have hrecIdx : recIdx (((D).rssT PC c).getD j []) ((((D).FssT PC ψ c).getD j []).length)
        = ConLeche.recIdxOf ((DA).ksF c j) := by
      rw [I.rssT_eq hj, I.FssT_len_eq S ψ hcb hj, ← h.Fss_length hj ψ]
      exact h.recIdx_eq hj ψ
    show (fs ++ (D).kitIhsT PC ψ (consList ps ρ) (b.elimLevel.eval ψ) c j fs _).foldl SetTheory.app
      (if (D).minorIdxT PC c j < (D).nCtorsT PC then msl.getD ((D).minorIdxT PC c j) pt else pt)
        = _
    rw [I.minorIdxT_eq c j, if_pos (by rw [I.nCtorsT_eq S]; exact hJ), List.foldl_append,
      List.foldl_append]
    congr 1
    unfold BlockModel.kitIhsT
    rw [hrecIdx]
    apply List.map_congr_left
    intro i hiI
    have hiK : i < ((DA).ksF c j).length := (mem_recIdxOf.mp hiI).1
    have hiA : i < cA.2 := by rw [← hcd.ksLen]; exact hiK
    have hr : (rsOf ((DA).ksF c j)).getD i false = true := by
      rw [rsOf_getD hiK, decide_eq_true_iff]; exact (mem_recIdxOf.mp hiI).2
    have hiR : i ∈ recIdx (((DA).rss c).getD j []) ((((DA).Fss c ψ).getD j []).length) := by
      rw [h.recIdx_eq hj]; exact hiI
    have hiRT : i ∈ recIdx (((D).rssT PC c).getD j []) ((((D).FssT PC ψ c).getD j []).length) := by
      rw [hrecIdx]; exact hiI
    have htgt : (DA).tgts c j i < (DA).k := h.tgt_lt hj' hiK rfl
    have htgtb : (DA).tgts c j i < b.k := by rw [← hkA]; exact htgt
    have htgtT : (DA).tgts c j i < (D).kT := by rw [hkTA]; exact htgt
    obtain ⟨cvT', cvR', mI', rP', rules', ht⟩ := hreps _ htgt
    have hfsI := spineFit_take' hfs (i := i) (by rw [h.Fss_length hj]; exact Nat.le_of_lt hiA)
    have hlenI : (fs.take i).length = i := by
      rw [List.length_take, hlenfs]; exact Nat.min_eq_left (Nat.le_of_lt hiA)
    simp only [Function.comp]
    rw [interp_ihAppAVK_at hlenps hF.mslLen hF.minsLen hlenfs hk hiA, hρcD _ htgt, hcandsD _ htgt,
      lamTower_bit_agree hb, I.teleAtT_eq ψ hj i, I.eisAtT_eq ψ hj i, I.tgtsT_eq hj hiA]
    symm
    rw [show consList (fs.take i) (consList ps (consList cands ρ))
        = consList (ps ++ fs.take i) (consList cands ρ) from by rw [consList_append],
      show consList (fs.take i) (consList ps ρ) = consList (ps ++ fs.take i) ρ from by
        rw [consList_append]]
    refine lamTower_congr_bottom (fun k' d' hd' => ?_) fun bs hbs => ?_
    · rw [List.length_append, hlenps, hlenI]
      exact domsBelow_getElem? (hcd.tssBelow ψ i) hd'
    -- the leaves: the target class's candidate, the graph's value at the predecessor
    have hlenbs : bs.length = (((DA).tssF c j ψ).getD i []).length := by
      rw [hbs.length_eq, List.length_map]
    have hbsρ : SpineFit (consList (fs.take i) (consList ps ρ))
        ((((DA).tssF c j ψ).getD i []).map (·.2.2)) bs := by
      have := spineFit_transport (hcd.tssBelow ψ i) (as := ps ++ fs.take i)
        (by rw [List.length_append, hlenps, hlenI]) (ρ₁ := consList cands ρ) (ρ₂ := ρ) hbs
      rwa [consList_append] at this
    have hEisρ : (((DA).eissF c j ψ).getD i []).map
        (interp V (consList (ps ++ fs.take i ++ bs) (consList cands ρ)))
        = (((DA).eissF c j ψ).getD i []).map (interp V (consList (ps ++ fs.take i ++ bs) ρ)) := by
      apply List.map_congr_left
      intro E hE
      exact interp_closed_bottom (hcd.eissBelow ψ i E hE)
        (by rw [List.length_append, List.length_append, hlenps, hlenI, hlenbs]) _ _
    rw [hEisρ, consList_append (ps ++ fs.take i) bs (consList cands ρ),
      consList_append (ps ++ fs.take i) bs ρ, ← hlenbs, frameIdx_consList', frameIdx_consList',
      consList_append ps (fs.take i) ρ]
    have hEis : SpineFit (consList ps ρ) ((DA).IdsM ((DA).tgts c j i) ψ)
        ((((DA).eissF c j ψ).getD i []).map
          (interp V (consList bs (consList (fs.take i) (consList ps ρ))))) :=
      hreps.eis_fit hfT hc hj hρp hiA htgt hr hfsI hbsρ
    have hlenEis : ((((DA).eissF c j ψ).getD i []).map
        (interp V (consList bs (consList (fs.take i) (consList ps ρ))))).length
          = (DA).nIdxAt ((DA).tgts c j i) := by
      rw [hEis.length_eq, ht.IdsM_length]
    -- the predecessor, at the auxiliary block and at the composed classes
    have hv := hreps.kitPred_mem rfl hc hj' hfitL hiR
      (bs := bs) (by rw [BlockModel.teleAt, IsBlockModel.tlss_getD hj]; exact hbsρ)
      ((DA).tup ψ c (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ)))))
    rw [BlockModel.eisAt, IsBlockModel.Eiss_getD hj] at hv
    have hvU := relPred_subset _ _ _ _ hv
    have hfold : bs.foldl SetTheory.app (fs.getD i pt)
        ∈ˢ SetTheory.app (lfpTuple ((DA).w ψ) (DA).k ((DA).idx ψ (consList ps ρ))
              ((DA).Φ ψ (consList ps ρ)) ((DA).tgts c j i))
          ((DA).tup ψ ((DA).tgts c j i)
            ((((DA).eissF c j ψ).getD i []).map
              (interp V (consList bs (consList (fs.take i) (consList ps ρ)))))) :=
      (tagged_mem_unionSet_iff.mp hvU).2.2
    have hvT := hD0.kitPredT_mem I.pinLaws hρpD hcT hjT hfitT.1 hiRT
      (bs := bs) (by rw [I.teleAtT_eq ψ hj i]; exact hbsρ)
      ((D).tupT ψ c (((DA).esF c j ψ).map (interp V (consList fs (consList ps ρ)))))
    rw [I.eisAtT_eq ψ hj i, I.tgtsT_eq hj hiA] at hvT
    -- the target's candidate at the transferred fit
    have hsp₂ := hreps.spineFit_recData_of hR htgt hpreρ hF hEis hfold
    have hsp₂R : SpineFit ρ ((rdsM ((DA).tgts c j i) ψ).map (·.2.2))
        (ps ++ Msl ++ msl ++ (((DA).eissF c j ψ).getD i []).map
          (interp V (consList bs (consList (fs.take i) (consList ps ρ))))
          ++ [bs.foldl SetTheory.app (fs.getD i pt)]) :=
      (I.spineFit_transfer S hnames hctorsJ hK35 htgtb ψ ρ
        (NestedTailIn.readAtOf R htgtT ψ) (I.lenAtOf R htgtb ψ) _).mpr hsp₂
    have hnIdxTt : (D).nIdxT ((DA).tgts c j i) = (DA).nIdxAt ((DA).tgts c j i) := by
      obtain ⟨f', hf'⟩ : ∃ f', fms[(DA).tgts c j i]? = some f' :=
        ⟨_, List.getElem?_eq_getElem (by rw [I.out.facts.lenFms]; exact htgtb)⟩
      have hfD' : (fms.getD ((DA).tgts c j i) default).nIdx = f'.nIdx := by
        rw [List.getD_eq_getElem?_getD, hf']; rfl
      rw [I.nIdxT htgtb, hfD', mutualBlockModel_nIdxAt hf']
    unfold BlockModel.blockCandT
    rw [lamTower_fold hℓ hsp₂R,
      (D).blockLeafVT_at PC ψ (b.elimLevel.eval ψ) ((DA).tgts c j i) ρ _ hMslT hmslT
        (by rw [hnIdxTt]; exact hlenEis),
      app_graph hvT]
    rfl

/-! ### The record -/

/-- **THE EQUATIONS AT THE TAIL** (PLAN-M7 §2–3): `NestedRecEqs` at
the SCRATCH block's own rule equations — graded at every tuple typed
at the restored readings (`eqsWD`) and satisfied at the candidate
tuple (`eqsCand`). -/
theorem NestedTailIn.recEqsOf {mpA : EnvModelM V μ ENVA} {cvRas : List ConstantVal}
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
    (R : NestedRecReadings mp₂.base2 (D) PC cvRms cvRns b.rlps b.elimLevel s rdsM concM) :
    ∃ eqs : (Name → Nat) → List AnnotTerm,
      NestedRecEqs (D) PC (fun ψ => b.elimLevel.eval ψ) rdsM concM eqs :=
  ⟨fun ψ => (DA).recEqs mpA.base2 b.elimLevel ψ,
    { heq := fun ψ ρ _rs hlen hrs _e he =>
        ⟨(I.eqsWD S hnames hctorsJ hK35 R ψ ρ hlen hrs he).1,
          (I.eqsWD S hnames hctorsJ hK35 R ψ ρ hlen hrs he).2.1⟩
      hceq := fun ψ ρ _e he => I.eqsCand S hnames hctorsJ hK35 R ψ ρ he
      valid := fun ψ ρ _rs hlen hrs _e he =>
        (I.eqsWD S hnames hctorsJ hK35 R ψ ρ hlen hrs he).2.2
      below := fun ψ _e he => by
        have h := S.reps.specEqs_below (S.readings ψ) _ he
        rw [S.record.k, ← I.kT] at h
        exact h }⟩

end Run

/-! ## The named fact and its consumer -/

/-- **THE EQUATIONS AT THE RUN** — `NestedRecEqsOf`, the second of
`nestedTailModeled_of`'s three named facts, at every tail input and
every readings record, modulo the same three model faces the readings
take: K.35 (`NestedRecTysAuxOf`), K.36 (`NestedCtorPinNamesOf`) and
the groups' constructor names (`NestedGroupCtorNamesOf`). -/
theorem nestedRecEqsOf_of_faces {F : Nat} (hK35 : NestedRecTysAuxOf μ F)
    (hK36 : NestedCtorPinNamesOf μ F) (hctorsJ : NestedGroupCtorNamesOf V μ F) :
    NestedRecEqsOf V μ F := by
  intro env mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀ fms f₀
    ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR
    pinsS mp₂ I s rdsM concM R
  obtain ⟨mpA, cvRas, S⟩ := I.scratch
  exact I.recEqsOf S (hK36 env p st fmsA ctorsA₀ I.hfA I.hcA I.helim I.hcont)
    (fun q₀ kJ i dJ G hi ci J h1 h2 h3 =>
      hctorsJ mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA₀ fms f₀
        ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR
        pinsS mp₂ I q₀ kJ i dJ G hi ci J h1 h2 h3)
    (hK35 env p st b envAux stored pinsS I.hb I.haux I.hstored I.out.stage.pinsLen) R

/-- **THE CONSUMER** (consumer-first): with the readings and the
equations both discharged from the three model faces, the recursors'
stage of a nested block needs only the stage proper
(`NestedRecsStored`, item 5). -/
theorem nestedTailModeled_of_stage {F : Nat} (hK35 : NestedRecTysAuxOf μ F)
    (hK36 : NestedCtorPinNamesOf μ F) (hctorsJ : NestedGroupCtorNamesOf V μ F)
    (hst : NestedRecsStored V μ F) : NestedTailModeled V μ F :=
  nestedTailModeled_of_faces hK35 hK36 hctorsJ (nestedRecEqsOf_of_faces hK35 hK36 hctorsJ) hst

end ConLeche.Model
