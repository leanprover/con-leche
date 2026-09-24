module

public import ConLeche.Model.Inductives.BlockModel
public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.BlockHoleFold
import ConLeche.Model.Inductives.FixAssemblyKit
public import ConLeche.Model.Annot.BlockLfpTup
public section

/-!
# `BlockModelAt` from the stages' three records (task #315 M3; moved by lane ENVLFP)

`blockModelAt_of_records`: the block's representation, built from the
three records the uniform install's constructors' stage produces
(`BlockNamesOk`, `BlockCtorsStage`, `BlockCtorsCore`).  It lived in
`BlockRecPreRun.lean` (§7–§8) while only the recursor regimes consumed
it; the environment invariant's lfp clause is now recorded by the
install itself (`declBlock`, `EnvModelM.addLfp`), upstream of the
recursor stage, so the construction moved here, below `DeclBlock`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 8. `BlockModelAt` from the stages' three records

`declBlock` hands the recursor stage the block data `dR` with the three
records `blockModelAt_of_stages` consumes (`BlockNamesOk`,
`BlockCtorsStage`, `BlockCtorsCore`) rather than the representation
itself.  The members' leaves are the block operator at the HOLE chains
(`BlockCtorsStage.leaf`, lane HOLE2 stage B), whose operator IS the
datum's; the slot operator's premise bundle is still stated at the DUMMY
former's field readings `fssZ`, bridged to the real ones by
`blockChainsOk_congr_ord`, for the fibre and the slots' index fit.

`blockModelAt_of_stages`'s per-component clauses (`hlenPps`, `hparams`,
`hparamsC`) are bounded by `d.N` — at `c ≥ d.N` they are not facts
about the block — so the records suffice and only the operator's and
the injections' identification stay premises (both `rfl` at
`blockDataOf`), beside `d.nInst = 0` and `0 < d.k`. -/

/-- **The members' index telescopes are graded** at every parameter
frame, from the constructors' stage. -/
theorem BlockCtorsStage.idxOkAt {envI : Env} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {ctorsOf : Name → List Name}
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A envI ctorsOf) (hk0 : 0 < d.k) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ) := by
  intro ψ ρp hs c hc
  have hNk : d.N = d.k := by rw [BlockData.N, hS.inst]; rfl
  exact hS.idxOk 0 hk0 ψ ρp hs c (by rw [← hNk]; exact hc)

/-- **The operator's fibre is the hole fit**, from the stages' records:
the datum's operator is the hole operator (`hPhi`), whose fibre is the
hole fit (`LfpDatum.holeOp_fibre`). -/
theorem blockHoleFib_of_records {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hk0 : 0 < d.k)
    (hPhi : ∀ (ψ : Name → Nat) (ρp : Nat → V), d.Φ ψ ρp = d.toLfp.holeOp ψ ρp)
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → ∀ c, c < d.N →
      ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
        x ∈ˢ app (d.Φ ψ ρp X c) t ↔ ∃ j fs, d.toLfp.HFits ψ ρp X t c j fs ∧ x = d.inj ψ c j fs := by
  intro ψ ρp hs X _ c hc t ht x
  have hH : BlockHoleFacts mo d lps := blockHoleFacts_of_stage hN hS hcore hk0
  have hidxOk := hS.idxOkAt hk0
  have hok : d.toLfp.HoleTmOk ψ ρp := fun m hm =>
    ⟨⟨(hH.parsLen ψ m hm).trans (hH.lenP ψ).symm, hH.parsSat ψ m hm ρp hs⟩,
      fun _ => (hidxOk ψ ρp hs m (Nat.lt_of_lt_of_le hm (Nat.le_add_right _ _))).2⟩
  have happ : ∀ j, j < d.toLfp.nctors c → d.toLfp.HolesApplied ψ c j :=
    fun j hj => blockHolesApplied hH ψ hc hj
  have hres : ∀ j, j < d.toLfp.nctors c →
      (d.toLfp.resIdx ψ c j).length = (d.toLfp.ids c ψ).length := by
    intro j hj
    show (d.absE ψ c j).length = (d.IdsM c ψ).length
    simp only [BlockData.absE, List.length_map]
    exact hH.lenE ψ c hc j hj
  rw [hPhi, LfpDatum.holeOp_fibre hok (Nat.le_add_right _ _) X happ hres ht x]
  refine exists_congr fun j => exists_congr fun fs => and_congr_right fun _ => ?_
  rw [hinj]
  rfl

/-- **The block's representation, from the stages' three records.** -/
theorem blockModelAt_of_records {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hinst : d.nInst = 0) (hk0 : 0 < d.k)
    (hPhi : ∀ (ψ : Name → Nat) (ρp : Nat → V), d.Φ ψ ρp = d.toLfp.holeOp ψ ρp)
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    (hmono : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (d.params ψ).reverse ρp → MonoTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp))
    (hfitsMono : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X Y, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) Y →
      TupleLe d.N (d.idx ψ ρp) X Y → ∀ c, c < d.N → ∀ (t : V) (j : Nat) (fs : List V),
        d.toLfp.HFits ψ ρp X t c j fs → d.toLfp.HFits ψ ρp Y t c j fs) :
    BlockModelAt mo d.memberNames d := by
  have hNk : d.N = d.k := by rw [BlockData.N, hinst]; rfl

  have hcAof : ∀ (c j : Nat) (hj : j < (d.ctorsM c).length),
      (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := fun _ _ hj => List.getElem?_eq_getElem hj
  -- the field chains' shape, off the data
  have hlenC : ∀ (ψ : Name → Nat) (c : Nat), (d.Fss c ψ).length = (d.ctorsM c).length := by
    intro ψ c
    show (fssOfR _ _).length = _
    rw [fssOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hFssD : ∀ (ψ : Name → Nat) (c j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cA →
      (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fun _ _ _ _ hj => fssOfR_fixCtorDataList_getD hj
  have hdsLenA : ∀ (ψ : Name → Nat) (c j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cA → (d.dsF c j ψ).length = d.nP + cA.2 :=
    fun ψ c j cA hj => (hcore.2.2.1 c j cA hj).2.2.len ψ
  have hnF : ∀ (ψ : Name → Nat) (c j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cA → ((d.Fss c ψ).getD j []).length = cA.2 := by
    intro ψ c j cA hj
    rw [hFssD ψ c j cA hj, List.length_map, List.length_drop, hdsLenA ψ c j cA hj]
    omega
  -- the parameter frame, at every component and every constructor
  have hlenPps : ∀ (ψ : Name → Nat) (c : Nat), c < d.N →
      (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length :=
    fun ψ c hc => hS.lenPps c ψ (by rw [← hNk]; exact hc)
  have hparams : ∀ (ψ : Name → Nat) (c : Nat), c < d.N → ∀ ρ : Nat → V,
      Sat V (d.params ψ).reverse ρ ↔
        Sat V (((d.ppsM c ψ).take d.nP).map (·.2.2)).reverse ρ := by
    intro ψ c hc ρ
    have hck : c < d.k := by rw [← hNk]; exact hc
    exact ⟨fun h => hS.paramsOf 0 hk0 ψ ρ h c hck, fun h => hS.paramsOf c hck ψ ρ h 0 hk0⟩
  have hparamsC : ∀ (ψ : Name → Nat) (c j : Nat), c < d.N → j < (d.ctorsM c).length →
      ∀ ρ : Nat → V,
      Sat V (d.params ψ).reverse ρ ↔
        Sat V (((d.dsF c j ψ).take d.nP).map (·.2.2)).reverse ρ := by
    intro ψ c j hc hj ρ
    exact (hparams ψ c hc ρ).trans
      ((hS.frames c (by rw [← hNk]; exact hc) j _ (hcAof c j hj)).1 ψ ρ)
  have hH : BlockHoleFacts mo d lps := blockHoleFacts_of_stage hN hS hcore hk0
  have hidxOk := hS.idxOkAt hk0
  have hfib := blockHoleFib_of_records hN hS hcore hk0 hPhi hinj
  -- the formers' leaves: closed, and the members' values at the carrier
  have hcvOf : ∀ c, c < d.k → ∃ cvTb, cvTas[c]? = some cvTb :=
    fun c hc => ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2.2]; exact hc)⟩
  have hcl : ∀ c, c < d.k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A c ψ).erase := by
    intro c hc ψ
    obtain ⟨cvTb, hcvTb⟩ := hcvOf c hc
    have := mo.cval_closedL cvTb.name ψ
    rwa [(hcore.1 c cvTb hcvTb).2.2.1 ψ] at this
  have hacv : ∀ c, c < d.k → ∀ ψ : Name → Nat, mo.acval (d.memberName c) ψ = A c ψ := by
    intro c hc ψ
    obtain ⟨cvTb, hcvTb⟩ := hcvOf c hc
    rw [hN.1 c cvTb hcvTb]
    exact (hcore.1 c cvTb hcvTb).2.2.1 ψ
  -- at the least tuple the hole fit is the stored fit (the override law)
  have hcarrier : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.N → ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ (j : Nat) (fs : List V),
        d.toLfp.HFits ψ ρp (lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp)) t c j fs ↔
          d.StoredFit ψ ρp t c j fs := by
    intro ψ ρp hs c hc t _ j fs
    have hck : c < d.k := by rw [← hNk]; exact hc
    have hover : ∀ j', j' < (d.ctorsM c).length → ∀ i, i < ((d.Fss c ψ).getD j' []).length →
        ∀ as : List V, as.length = i →
        interp V (consList as (consList ((List.range d.k).map fun c =>
            interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp)) (d.absField ψ c j' i)
          = interp V (consList as ρp) (((d.Fss c ψ).getD j' []).getD i default) := by
      intro j' hj' i hi as has
      have hj'A : (d.ctorsM c)[j']? = some (d.ctorsM c)[j'] := List.getElem?_eq_getElem hj'
      have hD' : BlockCtorRead mo d lps c j' (d.ctorsM c)[j'] := hH.facts c hc j' _ hj'A
      have hi' : i < ((d.ctorsM c)[j']).2 := by rw [← hD'.nF hj'A ψ]; exact hi
      have htgt : d.tgts c j' i < d.k := by rw [← hN.2.2.2]; exact hN.2.1 c j' i
      refine interp_absField_override hj'A hD' hi' htgt (by simp) ρp (fun σ => ?_) has
      rw [hacv _ htgt ψ, interp_closed V (hcl _ htgt ψ) σ (shiftE d.nP 0 ρp),
        List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range htgt]
      rfl
    have hfam : lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp)
        = blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
            (d.toLfp.holeChains ψ) := by
      rw [hPhi]
      show lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (blockPhiG d.N (d.w ψ) ρp (fun c => d.uM c ψ)
          (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ))
        = lfpTuple (d.w ψ) d.k (blockIdx (fun c => d.uM c ψ) ρp fun c => d.IdsM c ψ)
          (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
            (d.toLfp.holeChains ψ))
      rw [hNk]
      rfl
    rw [hfam]
    exact blockHFits_lfp_iff hH hinst (fun c _ => hS.leaf c ψ) hs (fun c hc => hS.lenPps c ψ hc)
      (fun c hc => hidxOk ψ ρp hs c (by rw [hNk]; exact hc)) (hS.holeOk ψ ρp hs) hck hover t j fs
  -- the closed tuple: the constructors' stage's, of the hole operator (stage D)
  have hclosed : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∃ L, IsClosedTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) L := by
    intro ψ ρp hs
    rw [hPhi]
    show ∃ L, IsClosedTuple (d.w ψ) d.N (blockIdx (fun c => d.uM c ψ) ρp fun c => d.IdsM c ψ)
      (blockPhiG d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)) L
    rw [hNk]
    exact (hS.holeFun ψ ρp hs).2
  have hmaps : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      MapsTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) := by
    intro ψ ρp hs
    rw [hPhi]
    show MapsTuple (d.w ψ) d.N (blockIdx (fun c => d.uM c ψ) ρp fun c => d.IdsM c ψ)
      (blockPhiG d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ))
    rw [hNk]
    exact blockPhi_maps_of (hS.holeOk ψ ρp hs)
  refine blockModelAt_of_stages mo rfl hinj hlenC (by rw [hNk]; exact hk0) hlenPps
    hidxOk hfib hmaps hmono hfitsMono hclosed hcarrier (fun ψ => d.toLfp.holeChains ψ) ?_ ?_
    hparams ?_
    (fun ψ c j hj => hFssD ψ c j _ (hcAof c j hj)) ?_ hparamsC ?_ ?_
  -- the members' leaves: the block operator at the HOLE chains
  · intro mm hmm ψ
    obtain ⟨hnameOf, -, -, hlenCv⟩ := hN
    have hmmlt : mm < cvTas.length := by rw [hlenCv]; exact hmm
    have hcv : cvTas[mm]? = some cvTas[mm] := List.getElem?_eq_getElem hmmlt
    rw [hnameOf mm _ hcv, (hcore.1 mm _ hcv).2.2.1 ψ, hS.leaf mm ψ, hNk]
  -- the hole chains are graded, and their operator IS the datum's
  · intro ψ ρp hs
    refine ⟨by rw [hNk]; exact hS.holeOk ψ ρp hs, fun X _ c _ => ?_⟩
    rw [hPhi]
    rfl
  -- the constructors' leaves
  · intro c hc j cA hj ψ
    exact (hcore.2.2.2 c (by rw [← hNk]; exact hc) j cA hj).2.2 ψ
  -- the field lists' lengths against the constructors' binder data
  · intro ψ c j hj
    rw [hdsLenA ψ c j _ (hcAof c j hj), hnF ψ c j _ (hcAof c j hj)]
  -- the field chains are graded at every parameter frame
  · intro ψ ρ hsat c hc
    refine SumFieldsOkB_uChains fun Fs hFs => ?_
    obtain ⟨j, hjget⟩ := List.getElem?_of_mem hFs
    have hjlt : j < (d.Fss c ψ).length := (List.getElem?_eq_some_iff.mp hjget).1
    have hjc : j < (d.ctorsM c).length := by rw [← hlenC ψ c]; exact hjlt
    have hFsEq : Fs = ((d.dsF c j ψ).drop d.nP).map (·.2.2) := by
      rw [← hFssD ψ c j _ (hcAof c j hjc), List.getD_eq_getElem?_getD, hjget]
      rfl
    rw [hFsEq]
    have hfr := hS.frames c (by rw [← hNk]; exact hc) j _ (hcAof c j hjc)
    exact (hfr.2 ψ ρ ((hfr.1 ψ ρ).mp ((hparams ψ c hc ρ).mp hsat))).1
  -- the constructors' RESULT index readings fit the component's telescope
  · intro ψ ρ hsat c hc j hj fs hfs
    have hjc := hcAof c j hj
    have hfr := hS.frames c (by rw [← hNk]; exact hc) j _ hjc
    have hFs : SpineFit ρ (((d.dsF c j ψ).drop d.nP).map (·.2.2)) fs := by
      rw [← hFssD ψ c j _ hjc]; exact hfs
    have hq := (hfr.2 ψ ρ ((hfr.1 ψ ρ).mp ((hparams ψ c hc ρ).mp hsat))).2.2 fs hFs
    rw [show (d.Ess c ψ).getD j [] = d.esF c j ψ from essOfR_fixCtorDataList_getD hjc]
    exact hq


/-- **The operator is monotone, from positivity** (lane HOLE2, charter
item 2: "monotonicity is DERIVED from positivity"): its fibre is the
hole fit (`blockHoleFib_of_records`), and every constructor positive
along the tuple order at the hole frame makes it monotone
(`monoTuple_of_tupRel`). -/
theorem blockMono_of_pos {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hk0 : 0 < d.k)
    (hPhi : ∀ (ψ : Name → Nat) (ρp : Nat → V), d.Φ ψ ρp = d.toLfp.holeOp ψ ρp)
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    (hpos : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (d.params ψ).reverse ρp → MonoTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) :=
  fun ψ ρp hs => monoTuple_of_tupRel (D := d.toLfp)
    (blockHoleFib_of_records hN hS hcore hk0 hPhi hinj ψ ρp hs) (hpos ψ ρp hs)

/-- **The hole fit grows with the tuple, from positivity**: every
constructor positive along the tuple order at the hole frame
(`LfpDatum.hfits_mono`). -/
theorem blockFitsMono_of_pos {d : BlockData V}
    (hpos : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X Y, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) Y →
      TupleLe d.N (d.idx ψ ρp) X Y → ∀ c, c < d.N → ∀ (t : V) (j : Nat) (fs : List V),
        d.toLfp.HFits ψ ρp X t c j fs → d.toLfp.HFits ψ ρp Y t c j fs :=
  fun ψ ρp hs X Y hX hY hXY c hc _ j _ hf =>
    LfpDatum.hfits_mono (hpos ψ ρp hs c hc j hf.1) ⟨X, Y, hX, hY, hXY, rfl, rfl⟩ hf

/-! ## 9. The block's LFP CLAUSE from the stages' records (lanes ENVLFP, HOLE2)

The clause the install records (`EnvModelM.addLfp`) is the
representation's (`BlockModelAt.toLfp`, `BlockLfpHoles.lean`), whose
hole form reads the constructors' facts the records carry
(`BlockHoleFacts`). -/

/-- **The block's lfp clause, in hole form, from the stages' records.** -/
theorem blockLfpClause_of_records {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hinst : d.nInst = 0) (hk0 : 0 < d.k)
    (hPhi : ∀ (ψ : Name → Nat) (ρp : Nat → V), d.Φ ψ ρp = d.toLfp.holeOp ψ ρp)
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    (hpos : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j) :
    LfpClause mo.acval d.toLfp :=
  (blockModelAt_of_records hN hS hcore hinst hk0 hPhi hinj
    (blockMono_of_pos hN hS hcore hk0 hPhi hinj hpos) (blockFitsMono_of_pos hpos)).toLfp
    (lps := lps)
    (blockHoleFacts_of_stage hN hS hcore hk0)

end ConLeche.Model
