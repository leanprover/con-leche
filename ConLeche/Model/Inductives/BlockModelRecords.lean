module

import ConLeche.Model.Inductives.BlockModel
public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.BlockAssemblyKit
import ConLeche.Model.Inductives.FixAssemblyKit
public import ConLeche.Model.Inductives.BlockLfpHoles
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

/-! ## 7. The LEAF's bridge from the dummy chains to the real ones

`blockModelAt_of_stages` asks for the members' leaves at the REAL
field readings `d.Fss`, while every stage supplies them at the dummy
former's `fssZ` (`BlockCtorsStage.leaf`): the constructors are checked
against a former whose recursive fields are not yet the member's own.
The operator's half of that bridge is `blockChainsOk_congr_ord`
(`BlockAssemblyKit.lean`); the LEAF's half is here, and it is a pure
CONGRUENCE — `blockTyAV` reads the field lists only through
`chainsXBI`, and `chainsXBI_congr_ord` already says those are the same
list when the two readings agree at the ordinary positions. -/

/-- The tuple-maker is congruent in its component function over the
range it reads. -/
theorem ndMkTowerAV_congr_lt {r : Nat} {Gty G G' : Nat → AnnotTerm} :
    ∀ (n s : Nat), (∀ i, i < n → G (s + i) = G' (s + i)) →
      ndMkTowerAV r Gty G s n = ndMkTowerAV r Gty G' s n
  | 0, _, _ => rfl
  | n + 1, s, h => by
    have h0 : G s = G' s := by simpa using h 0 (Nat.succ_pos n)
    have hrest : ∀ i, i < n → G (s + 1 + i) = G' (s + 1 + i) := by
      intro i hi
      have := h (i + 1) (by omega)
      rwa [show s + (i + 1) = s + 1 + i from by omega] at this
    show AnnotTerm.mkAppN _ [_, _, G s, ndMkTowerAV r Gty G (s + 1) n] = _
    rw [h0, ndMkTowerAV_congr_lt n (s + 1) hrest]
    rfl

/-- **The block's operator term is congruent** in the field readings,
at equal chains. -/
theorem blockFunAV_congr_chains {k w : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
    {Chs Chs' : Nat → List (List AnnotTerm)} (hchains : ∀ m, m < k → Chs m = Chs' m) :
    blockFunG k w uf Idss Chs = blockFunG k w uf Idss Chs' := by
  unfold blockFunG
  refine congrArg _ (ndMkTowerAV_congr_lt k 0 fun i hi => ?_)
  rw [Nat.zero_add]
  unfold blockArmG
  rw [hchains i hi]

/-- **The LEAF's bridge**: a member's former leaf is the same term at
the dummy former's field readings and at the members' real ones, when
the two agree at the ORDINARY positions — the `blockTyAV` twin of
`blockChainsOk_congr_ord`. -/
theorem blockTyAV_congr_ord {k w : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
    {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Fsss' Esss : Nat → List (List AnnotTerm)}
    (hlen : ∀ m, m < k → (Fsss m).length = (Fsss' m).length)
    (hlenj : ∀ m, m < k → ∀ j, j < (Fsss m).length →
      ((Fsss m).getD j []).length = ((Fsss' m).getD j []).length)
    (hord : ∀ m, m < k → ∀ j, j < (Fsss m).length → ∀ l, l < ((Fsss m).getD j []).length →
      ((rsss m).getD j []).getD l false = false →
      ((Fsss m).getD j []).getD l default = ((Fsss' m).getD j []).getD l default)
    (pps : List (Nat × Nat × AnnotTerm)) (m : Nat) :
    blockTyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss pps m
      = blockTyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss' Esss pps m := by
  have hchains : ∀ m', m' < k →
      chainsXBI uf Idss (Idss m').length (rsss m') (tgtsss m') (tlsss m') (Eisss m') (Fsss m')
          (Esss m')
        = chainsXBI uf Idss (Idss m').length (rsss m') (tgtsss m') (tlsss m') (Eisss m')
            (Fsss' m') (Esss m') :=
    fun m' hm' => chainsXBI_congr_ord (hlen m' hm') (hlenj m' hm') (hord m' hm')
  unfold blockTyAV blockTyG blockBodyG
  rw [blockFunAV_congr_chains (w := w) (Chs := slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    (Chs' := slotChs uf Idss rsss tgtsss tlsss Eisss Fsss' Esss) hchains]

/-! ## 8. `BlockModelAt` from the stages' three records

`declBlock` hands the recursor stage the block data `dR` with the three
records `blockModelAt_of_stages` consumes (`BlockNamesOk`,
`BlockCtorsStage`, `BlockCtorsCore`) rather than the representation
itself, because the records state the operator's premise bundle and
the members' leaves at the DUMMY former's field readings `fssZ` while
the record wants them at the members' real ones.  Both bridges are
congruences at the chains — `blockChainsOk_congr_ord` for the operator
and §7's `blockTyAV_congr_ord` for the leaf — and this is the call.

`blockModelAt_of_stages`'s per-component clauses (`hlenPps`, `hparams`,
`hparamsC`) are bounded by `d.N` — at `c ≥ d.N` they are not facts
about the block — so the records suffice and only the operator's and
the injections' identification stay premises (both `rfl` at
`blockDataOf`), beside `d.nInst = 0` and `0 < d.k`. -/

/-- **The constructors' hole facts, from the stages' records.** -/
theorem blockHoleFacts_of_records {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A fssZ envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hinst : d.nInst = 0) (hk0 : 0 < d.k) :
    BlockHoleFacts mo d lps := by
  have hNk : d.N = d.k := by rw [BlockData.N, hinst]; rfl
  refine ⟨fun c hc j cA hj => ?_, fun c hc j cA hj l _ => ?_, fun ψ => ?_, fun ψ mm hmm => ?_,
      fun ψ mm hmm ρ h => hS.paramsOf 0 hk0 ψ ρ h mm hmm, fun ψ c hc j hj => ?_⟩
  · have hck : c < d.k := by rw [← hNk]; exact hc
    obtain ⟨h1, h2, -⟩ := hcore.2.2.2 c hck j cA hj
    exact ⟨h1, h2, (hcore.2.2.1 c j cA hj).2.2⟩
  · rw [← hN.2.2.2]; exact hN.2.1 c j l
  · show (((d.ppsM 0 ψ).take d.nP).map (·.2.2)).length = d.nP
    rw [List.length_map, List.length_take, hS.lenPps 0 ψ hk0]
    omega
  · show (((d.ppsM mm ψ).take d.nP).map (·.2.2)).length = d.nP
    rw [List.length_map, List.length_take, hS.lenPps mm ψ hmm]
    omega
  · have hck : c < d.k := by rw [← hNk]; exact hc
    have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
    rw [show (d.Ess c ψ).getD j [] = d.esF c j ψ from essOfR_fixCtorDataList_getD hcj,
      ((hcore.2.2.1 c j _ hcj).2.2).lenE ψ, hS.lenIds c hck ψ]

/-- **The block's representation, from the stages' three records.** -/
theorem blockModelAt_of_records {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A fssZ envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hinst : d.nInst = 0) (hk0 : 0 < d.k)
    (hPhi : ∀ (ψ : Name → Nat) (ρp : Nat → V), d.Φ ψ ρp
      = blockPhi d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
          (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fun c => d.Fss c ψ) (fun c => d.Ess c ψ))
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    (hmono : d.IdxFit → d.Fibre → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (d.params ψ).reverse ρp → MonoTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp)) :
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
  -- the per-field targets, off the data and the names
  have hks : ∀ (ψ : Name → Nat) (c j : Nat), j < (d.ctorsM c).length →
      (d.ksF c j).length = ((d.Fss c ψ).getD j []).length := by
    intro ψ c j hj
    rw [hnF ψ c j _ (hcAof c j hj)]
    exact (hcore.2.2.1 c j _ (hcAof c j hj)).2.2.ksLen
  have htgts : ∀ (ψ : Name → Nat) (c j l : Nat), j < (d.ctorsM c).length →
      l < ((d.Fss c ψ).getD j []).length →
      ((d.tgtss c).getD j []).getD l 0 = d.tgts c j l ∧ d.tgts c j l < d.N := by
    intro ψ c j l hj hl
    have hlk : l < (d.ksF c j).length := by rw [hks ψ c j hj]; exact hl
    refine ⟨?_, ?_⟩
    · have hinner : (d.tgtss c).getD j [] = (List.range (d.ksF c j).length).map (d.tgts c j) := by
        show (((List.range (d.ctorsM c).length).map fun j' =>
          (List.range (d.ksF c j').length).map (d.tgts c j')).getD j []) = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
        rfl
      rw [hinner, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlk]
      rfl
    · rw [hNk, ← hN.2.2.2]
      exact hN.2.1 c j l
  -- the two chain lists agree: lengths, and the ordinary positions
  have hlenZF : ∀ (ψ : Name → Nat) (m : Nat), m < d.k → (fssZ ψ m).length = (d.Fss m ψ).length :=
    fun ψ m hm => by rw [hS.lenZ m hm ψ, hlenC ψ m]
  have hlenjZF : ∀ (ψ : Name → Nat) (m : Nat), m < d.k → ∀ j, j < (fssZ ψ m).length →
      ((fssZ ψ m).getD j []).length = ((d.Fss m ψ).getD j []).length := by
    intro ψ m hm j hj
    have hjc : j < (d.ctorsM m).length := by rw [← hS.lenZ m hm ψ]; exact hj
    rw [hS.lenZj m hm ψ j _ (hcAof m j hjc), hnF ψ m j _ (hcAof m j hjc)]
  have hordF : ∀ (ψ : Name → Nat) (m : Nat), m < d.k → ∀ j, j < (fssZ ψ m).length →
      ∀ l, l < ((fssZ ψ m).getD j []).length →
      ((d.rss m).getD j []).getD l false = false →
      ((fssZ ψ m).getD j []).getD l default = ((d.Fss m ψ).getD j []).getD l default := by
    intro ψ m hm j hj l hl hr
    have hjc : j < (d.ctorsM m).length := by rw [← hS.lenZ m hm ψ]; exact hj
    have hlj : ((fssZ ψ m).getD j []).length = ((d.ctorsM m)[j]).2 :=
      hS.lenZj m hm ψ j _ (hcAof m j hjc)
    have hks : (d.ksF m j).length = ((d.ctorsM m)[j]).2 :=
      (hcore.2.2.1 m j _ (hcAof m j hjc)).2.2.ksLen
    have hlk : l < (d.ksF m j).length := by rw [hks, ← hlj]; exact hl
    have hrs : (d.rss m).getD j [] = rsOf (d.ksF m j) := rssOfK_getD hjc
    have hnrec : ¬ recAt d.nP (d.ksF m j) (d.nP + l) := by
      rw [recAt_iff_rsOf hlk, ← hrs, hr]
      exact Bool.false_ne_true
    exact (hS.ord m hm j _ (hcAof m j hjc) ψ l (by rw [← hlj]; exact hl) hnrec).symm
  refine blockModelAt_of_stages mo rfl hPhi hinj ?_ hlenC (by rw [hNk]; exact hk0) hlenPps
    htgts ?_ hparams ?_ (fun ψ c j hj => hFssD ψ c j _ (hcAof c j hj)) ?_ hparamsC ?_ ?_ ?_
  -- the operator's premise bundle, at the REAL chains
  · intro ψ ρp hsat
    rw [hNk]
    exact blockChainsOk_congr_ord (hlenZF ψ) (hlenjZF ψ) (hordF ψ)
      (hS.chainsOk 0 hk0 ψ ρp ((hparams ψ 0 (by rw [hNk]; exact hk0) ρp).mp hsat))
  -- the members' leaves, at the REAL chains
  · intro mm hmm ψ
    obtain ⟨hnameOf, -, -, hlenCv⟩ := hN
    have hmmlt : mm < cvTas.length := by rw [hlenCv]; exact hmm
    have hcv : cvTas[mm]? = some cvTas[mm] := List.getElem?_eq_getElem hmmlt
    rw [hnameOf mm _ hcv, (hcore.1 mm _ hcv).2.2.1 ψ, hS.leaf mm ψ, hNk]
    exact blockTyAV_congr_ord (hlenZF ψ) (hlenjZF ψ) (hordF ψ) _ _
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

  -- the operator's monotonicity (lane HOLE2: positivity's)
  · exact hmono

/-- **The operator is monotone, from positivity** (lane HOLE2, charter
item 2: "monotonicity is DERIVED from positivity"): given the fibre law
and the slots' index fit — which make the block's fit relation the hole
fit (`blockReadsHoles`) — every constructor positive along the tuple
order at the hole frame makes the operator monotone
(`monoTuple_of_tupRel`). -/
theorem blockMono_of_pos {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A fssZ envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hinst : d.nInst = 0) (hk0 : 0 < d.k)
    (hpos : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j) :
    d.IdxFit → d.Fibre → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (d.params ψ).reverse ρp → MonoTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) := by
  intro hidx hfib ψ ρp hs
  refine monoTuple_of_tupRel (D := d.toLfp)
    (blockReadsHoles hidx (blockHoleFacts_of_records hN hS hcore hinst hk0)) hs
    (fun X hX c hc t ht x => ?_) (hpos ψ ρp hs)
  show x ∈ˢ app (d.Φ ψ ρp X c) t ↔
    ∃ j fs, (j < (d.ctorsM c).length ∧ d.ChainFit ψ ρp X t c j fs) ∧ x = d.inj ψ c j fs
  rw [hfib ψ ρp hs X hX c hc t ht x]
  constructor
  · rintro ⟨j, fs, hj, hfit, rfl⟩; exact ⟨j, fs, ⟨hj, hfit⟩, rfl⟩
  · rintro ⟨j, fs, ⟨hj, hfit⟩, rfl⟩; exact ⟨j, fs, hj, hfit, rfl⟩

/-! ## 9. The block's LFP CLAUSE from the stages' records (lanes ENVLFP, HOLE2)

The clause the install records (`EnvModelM.addLfp`) is the
representation's (`BlockModelAt.toLfp`, `BlockLfpHoles.lean`), whose
hole form reads the constructors' facts the records carry
(`BlockHoleFacts`). -/

/-- **The block's lfp clause, in hole form, from the stages' records.** -/
theorem blockLfpClause_of_records {envC envI : Env} {mo : EnvModel V envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {F : Nat} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {ctorsOf : Name → List Name}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A fssZ envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A d.k)
    (hinst : d.nInst = 0) (hk0 : 0 < d.k)
    (hPhi : ∀ (ψ : Name → Nat) (ρp : Nat → V), d.Φ ψ ρp
      = blockPhi d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
          (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fun c => d.Fss c ψ) (fun c => d.Ess c ψ))
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    (hpos : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j) :
    LfpClause mo.acval d.toLfp :=
  (blockModelAt_of_records hN hS hcore hinst hk0 hPhi hinj
    (blockMono_of_pos hN hS hcore hinst hk0 hpos)).toLfp (lps := lps)
    (blockHoleFacts_of_records hN hS hcore hinst hk0)

end ConLeche.Model
