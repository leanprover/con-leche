module

import ConLeche.Model.IndRep
import ConLeche.Model.Inductives.FixRuleData
import ConLeche.Model.Inductives.StructStageCtor
import ConLeche.Verify.Inductives.FixWF
public import ConLeche.Model.Inductives.FixRecData
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

theorem fixStepI_congr {tbl : List (List Nat)} {w : Nat} {ρp : Nat → V} {nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : AgreeOffRecs rss Fss Fss') (X t : V) :
    fixStepI tbl u w ρp Ids nIdx rss tlss Eiss Fss Ess X t
      = fixStepI tbl u w ρp Ids nIdx rss tlss Eiss Fss' Ess X t := by
  unfold fixStepI sumFibreT; rw [chainsXI_congr h, chainsXI_length]

theorem fixFunVI_congr {tbl : List (List Nat)} {w : Nat} {ρp : Nat → V} {nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : AgreeOffRecs rss Fss Fss') :
    fixFunVI tbl u w ρp Ids nIdx rss tlss Eiss Fss Ess = fixFunVI tbl u w ρp Ids nIdx rss tlss Eiss Fss' Ess := by
  unfold fixFunVI famFI
  simp only [fixStepI_congr h]

theorem fixFamI_congr {tbl : List (List Nat)} {w : Nat} {ρp : Nat → V} {nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : AgreeOffRecs rss Fss Fss') :
    fixFamI tbl u w ρp Ids nIdx rss tlss Eiss Fss Ess = fixFamI tbl u w ρp Ids nIdx rss tlss Eiss Fss' Ess := by
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
theorem xChainsOk_congr {tbl : List (List Nat)} {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : XChainsOk tbl u w ρp Ids rss tlss Eiss Fss Ess)
    (hag : AgreeOffRecs rss Fss Fss') :
    XChainsOk tbl u w ρp Ids rss tlss Eiss Fss' Ess where
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
  hoff := h.hoff

end Congr

/-! ## The fibre's membership, both regimes -/

/-- **The functor's fibre at a tag table**: a member is the injection,
at a LOCAL tag `jc`, of a field spine fitting the flat constructor
`tagOf tbl Fss.length t jc`'s X-chain at `(X, t)`, and conversely. -/
theorem fixStepI_iffT {tbl : List (List Nat)} {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)} {X t x : V} :
    x ∈ˢ fixStepI tbl u w ρp Ids Ids.length rss tlss Eiss Fss Ess X t ↔
      ∃ jc j fs, j = tagOf tbl Fss.length t jc ∧ j < Fss.length ∧ fs.length = (Fss.getD j []).length ∧
        SpineFit (cons t (cons X ρp))
          (chainXIGo u Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) 0) fs ∧
        EqAll (consList fs (cons t (cons X ρp)))
          (eqsXI Ids.length (Fss.getD j []).length (Ess.getD j [])) ∧
        x = injW w jc (mkTower (fs ++ [pt])) := by
  by_cases hw : w = 0
  · subst hw
    constructor
    · intro hx
      obtain ⟨rfl, jc, j, fs, hJ, hj, hlen, hsp, hall⟩ := fixStepI_zero_elim hx
      exact ⟨jc, j, fs, hJ, hj, hlen, hsp, hall, (injW_zero _ _).symm⟩
    · rintro ⟨jc, j, fs, hJ, hj, hlen, hsp, hall, rfl⟩
      rw [injW_zero, fixStepI_eq]
      refine pt_mem_sumSet_zero (i := jc) (a := pt) ?_
      rw [← hJ, sumFibre_of_getElem? (by rw [chainsXI_getElem?, if_pos hj])]
      unfold chainXI
      exact pt_mem_tower_teleOfFields (spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, hall⟩)
  · constructor
    · intro hx
      obtain ⟨jc, j, fs, hJ, rfl, hj, hlen, hsp, hall⟩ := fixStepI_elim hw hx
      exact ⟨jc, j, fs, hJ, hj, hlen, hsp, hall, (injW_pos hw _ _).symm⟩
    · rintro ⟨jc, j, fs, hJ, hj, hlen, hsp, hall, rfl⟩
      rw [injW_pos hw, fixStepI_eq]
      refine inj_mem hw (f := fun jc => sumFibre w (cons t (cons X ρp)) _ (tagOf tbl Fss.length t jc)) ?_
      show mkTower (fs ++ [pt]) ∈ˢ sumFibre w (cons t (cons X ρp)) _ (tagOf tbl Fss.length t jc)
      rw [← hJ, sumFibre_of_getElem? (by rw [chainsXI_getElem?, if_pos hj])]
      unfold chainXI
      exact mkTower_mem_teleOfFields hw (spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, hall⟩)

/-- **The functor's fibre** (the flat instance): a member is the injection
of a field spine fitting some constructor's X-chain at `(X, t)`, and
conversely. -/
theorem fixStepI_iff {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Ess : List (List AnnotTerm)} {X t x : V} :
    x ∈ˢ fixStepI [] u w ρp Ids Ids.length rss tlss Eiss Fss Ess X t ↔
      ∃ j fs, j < Fss.length ∧ fs.length = (Fss.getD j []).length ∧
        SpineFit (cons t (cons X ρp))
          (chainXIGo u Ids (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) (Fss.getD j []) 0) fs ∧
        EqAll (consList fs (cons t (cons X ρp)))
          (eqsXI Ids.length (Fss.getD j []).length (Ess.getD j [])) ∧
        x = injW w j (mkTower (fs ++ [pt])) := by
  rw [fixStepI_iffT]
  constructor
  · rintro ⟨jc, j, fs, hJ, hj, hlen, hsp, hall, rfl⟩
    rw [tagOf_nil] at hJ
    subst hJ
    exact ⟨j, fs, hj, hlen, hsp, hall, rfl⟩
  · rintro ⟨j, fs, hj, hlen, hsp, hall, rfl⟩
    exact ⟨j, j, fs, rfl, hj, hlen, hsp, hall, rfl⟩

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
    (ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (lvlsAll : (Name → Nat) → List Nat)
    (uAV : (Name → Nat) → Nat) :
    IndRepData V where
  nP := p.nP
  nIdx := p.nIdx
  resSort := p.resSort
  isProp := p.isProp
  large := p.large
  elim := p.elim
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
  essC := esF
  eissC := eissF
  tssF := tssF
  k := 1
  nIdxs := [p.nIdx]
  memberNames := [p.cvT.name]
  mems := fun _ => 0
  tgts := fun _ _ => 0
  ppsM := fun _ => ppsAll
  lvlsM := fun _ => lvlsAll
  IdsC := fun ψ => ((ppsAll ψ).drop p.nP).map (·.2.2)
  u := uAV
  tup := fun ψ _ is => tupW (uAV ψ) is
  Φ := fun ψ ρp =>
    fixFunVI [] (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
      (((ppsAll ψ).drop p.nP).map (·.2.2)).length (rssOfK ksF ctorsA.length)
      (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
  inj := fun ψ j fs => injW (p.resSort.eval ψ) j (mkTower (fs ++ [pt]))

section FixRepDataReduced

variable {p : NativeParts} {env₀ : Env} {ctorsA : List (ConstantVal × Nat)} {idxF : Nat → List Expr}
  {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {esF : Nat → (Name → Nat) → List AnnotTerm}
  {srcsF : Nat → List (Option Nat)} {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr}
  {xrestF : Nat → Expr} {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvlsAll : (Name → Nat) → List Nat}
  {uAV : (Name → Nat) → Nat}

/-! The fixpoint datum's recursor-view pieces, reduced (each by `rfl`:
the datum has one member, no copies, and the defaults). -/

theorem fixRepData_Ls (m : EnvModel V env) (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).Ls m ψ = [m.acval p.cvT.name ψ] := rfl

theorem fixRepData_pinsOf (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).pinsOf ψ = fun _ => paramBvarsAt p.nP p.nP := rfl

theorem fixRepData_ipss (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).ipss ψ = [(ppsAll ψ).drop p.nP] := rfl

theorem fixRepData_cdsR (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).cdsR ψ = fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0 := by
  unfold IndRepData.cdsR IndRepData.ctorsAll
  simp only [fixRepData, List.append_nil]

theorem fixRepData_nP :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).nP = p.nP := rfl

theorem fixRepData_k :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).k = 1 := rfl

theorem fixRepData_nIdxs :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).nIdxs = [p.nIdx] := rfl

theorem fixRepData_mems :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).mems = fun _ => 0 := rfl

theorem fixRepData_tgtsR :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).tgtsR = fun _ _ => 0 := rfl

theorem fixRepData_ppsM (t : Nat) (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).ppsM t ψ = ppsAll ψ := rfl

theorem fixRepData_dsF (j : Nat) (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).dsF j ψ = dsF j ψ := rfl

theorem fixRepData_ksR (j : Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).ksR j = ksF j := rfl

theorem fixRepData_tssR (j : Nat) (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).tssR j ψ = tssF j ψ := rfl

theorem fixRepData_eissR (j : Nat) (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).eissR j ψ = eissF j ψ := rfl

theorem fixRepData_recNames (t : Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).recNames t = ([p.cvT.name].getD t .anonymous).str "rec" := rfl

theorem fixRepData_nAll :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).nAll = ctorsA.length := rfl

theorem fixRepData_elimL :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).elimL = ConLeche.structElimLevel p.elim p.large := rfl

theorem fixRepData_bb (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
      lvlsAll uAV).bb ψ = pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) := rfl

end FixRepDataReduced

/-- **The fixpoint datum's recursor tower is the generated reading** —
the `k = 1` instance of the pinned spelling at the parameter variables
(`recDataAVP_params`, `mutualRecDataAV_one`). -/
theorem fixRepData_recDataAV {p : NativeParts} (m : EnvModel V env) {env₀ : Env}
    {ctorsA : List (ConstantVal × Nat)} {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvlsAll : (Name → Nat) → List Nat}
    {uAV : (Name → Nat) → Nat} (ψ : Name → Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
        lvlsAll uAV).recDataAV m ψ 0
      = fixRdsAV m p ppsAll dsF esF ksF eissF tssF ctorsA ψ := by
  unfold IndRepData.recDataAV fixRdsAV fixRecDataAV
  rw [fixRepData_Ls, fixRepData_pinsOf, fixRepData_ipss, fixRepData_cdsR, fixRepData_elimL,
    fixRepData_nP, fixRepData_nIdxs, fixRepData_mems, fixRepData_tgtsR, fixRepData_ppsM,
    recDataAVP_params]
  exact mutualRecDataAV_one _ _ _ _ _ _ _

/-- **The fixpoint datum's rule spelling is the generated rule
reading** — the `k = 1` instance at the parameter variables, the one
recursor leaf `T.rec`'s. -/
theorem fixRepData_ruleAV {p : NativeParts} (m : EnvModel V env) {env₀ : Env}
    {ctorsA : List (ConstantVal × Nat)} {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvlsAll : (Name → Nat) → List Nat}
    {uAV : (Name → Nat) → Nat} (ψ : Name → Nat) (j nF : Nat) :
    (fixRepData (V := V) p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll
        lvlsAll uAV).ruleAV m ψ j nF
      = mkLamsAV (fixRuleDataAV m p.cvT.name ψ p.nP p.nIdx (ConLeche.structElimLevel p.elim p.large)
          ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP)
          (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) (dsF j ψ))
        (fixRuleCoreAV (pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)))
          (m.acval (p.cvT.name.str "rec") ψ) p.nP nF ctorsA.length j
          (ConLeche.recIdxOf (ksF j)) (tssF j ψ) (eissF j ψ)) := by
  unfold IndRepData.ruleAV
  rw [fixRepData_Ls, fixRepData_pinsOf, fixRepData_ipss, fixRepData_cdsR, fixRepData_elimL,
    fixRepData_bb, fixRepData_nAll, fixRepData_nP, fixRepData_k, fixRepData_nIdxs, fixRepData_mems,
    fixRepData_tgtsR, fixRepData_ppsM, fixRepData_dsF, fixRepData_ksR, fixRepData_tssR,
    fixRepData_eissR, ruleDataAVP_params, mutualRuleDataAV_one,
    mutualRuleCoreAV_congr_Rof (Rof' := fun _ => m.acval (p.cvT.name.str "rec") ψ)
      (fun _ _ => rfl), mutualRuleCoreAV_one]

set_option maxHeartbeats 3200000 in
/-- **A natively installed block is represented**, from the recursor
stage's block facts (`stageFixRec`'s hypotheses at the carrier storing
the former and the constructors). -/
theorem indRep_of_stage {p : NativeParts} (m : EnvModel V env)
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {mI rP : Nat}
    (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    (hlenR : rhss.length = ctorsA.length)
    (hRname : cvRa.name = p.cvT.name.str "rec") (hnotR : env.find? cvRa.name = none)
    {bsT : List (Expr × ConLeche.BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfT : ∃ caps : IndCaps, env.find? p.cvT.name = some (.indInfo cvTa caps))
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvlsAll : (Name → Nat) → List Nat}
    (hFD : FormerData m cvTa (p.nP + p.nIdx) p.resSort ppsAll lvlsAll)
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
      = nativeTyAVI [] (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (((ppsAll ψ).drop p.nP).map (·.2.2))
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hagree : ∀ ψ, AgreeOffRecs (rssOfK ksF ctorsA.length) (fssZ ψ)
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, m.acval cA.1.name ψ
      = sumMkAV [] 0 (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hframes : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk [] (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      ∀ j, j < ctorsA.length →
        FieldsOkB (p.resSort.eval ψ) ρp
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []))
    -- the recursor's type reading (task #279 M-A′)
    (hRread : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvRa.type
      = some (mkPisAV (fixRdsAV m p ppsAll dsF esF ksF eissF tssF ctorsA ψ)
          (recConcAV ctorsA.length p.nIdx))) :
    IndRep m p.cvT.name cvTa cvRa mI rP
      (ConLeche.sumRules env.find? cvRa.name p.nP mI rP cvRa.type ctorsA rhss)
      (fixRepData p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll lvlsAll
        uAV) 0 := by
  -- the pieces, named
  let d : IndRepData V :=
    fixRepData p env₀ ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF ppsAll lvlsAll uAV
  show IndRep m p.cvT.name cvTa cvRa mI rP _ d 0
  have hIds : ∀ ψ, d.IdsC ψ = ((ppsAll ψ).drop p.nP).map (·.2.2) := fun _ => rfl
  have hIdsM : ∀ ψ, d.IdsM 0 ψ = d.IdsC ψ := fun _ => rfl
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
      XChainsOk [] (d.u ψ) (d.w ψ) ρp (d.IdsC ψ) d.rss (d.tlss ψ) (d.Eiss ψ) (d.Fss ψ) (d.Ess ψ) :=
    fun ψ ρp hρ => xChainsOk_congr (hframes ψ ρp hρ).1 (hagree ψ)
  have hlenP : ∀ ψ, (d.params ψ).length = p.nP := by
    intro ψ
    rw [hparams, List.length_map, List.length_take, hFD.len ψ]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  refine {
    member := rfl
    strip := ⟨bsT, hstripT⟩
    isProp := hProp
    rulesRead := fun _ h => by rw [hnotR] at h; exact nomatch h
    mI := hmI
    rP := hrP
    rules := fun _ => by
      rw [IndRepData.memberCtors_of_all (d := d) (mm := 0) (fun _ => rfl)]
      exact sumRules_map_ctor hlenR
    kRealLe := Nat.le_refl _
    memReal := Nat.zero_lt_one
    recName := hRname.symm
    recNamesReal := fun _ _ => rfl
    tgtsRLt := fun _ _ => Nat.zero_lt_one
    membersFound := fun t ht => by
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      exact ⟨_, _, hfT.choose_spec⟩
    membersLps := membersLps_one rfl hfT.choose_spec
    memberNodup := memberNodup_one rfl
    memsReal := fun j hj => ⟨fun _ => hj, fun _ => Nat.zero_lt_one⟩
    ctorsCFound := fun _ h => nomatch h
    pinsReal := fun _ _ => ⟨fun _ => rfl, rfl⟩
    recRead := fun ψ => by
      rw [hRread ψ, fixRepData_recDataAV, show d.k = 1 from rfl, show d.nAll = ctorsA.length from rfl,
        show d.nIdxAt 0 = p.nIdx from rfl, mutualConcAV_one]
    former := hFD
    formersRead := fun t ht cv caps hf => by
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      rw [show d.memberName 0 = p.cvT.name from rfl, hfT.choose_spec] at hf
      obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
      exact hFD
    leafShape := fun t ht ψ => by
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      exact ⟨_, hleafT ψ⟩
    ctors := fun j cA hj => by rw [hlpsT]; exact hcf j cA hj
    memsFound := fun j hj => ⟨⟨_, _, hfT.choose_spec⟩, fun _ => ⟨_, _, hfT.choose_spec⟩⟩
    idxRes := hidxRes
    uParams := fun ψ₁ ψ₂ hq => hUparams ψ₁ ψ₂ (fun q hq' => hq q (by rw [hlpsT]; exact hq'))
    paramsIff := hiff
    paramsIffM := fun t ht ψ ρ => by
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      exact Iff.rfl
    chains := fun ψ ρp hρ => xChainsOk_toChainsOk (hX ψ ρp hρ)
    functor := fun ψ ρp hρ => ⟨fixFunVI_mem (hX ψ ρp hρ).hok, fixFunVI_mono (hX ψ ρp hρ),
      fixFunVI_maps (hX ψ ρp hρ), fixFunVI_closed_exists (hX ψ ρp hρ)⟩
    fibre := ?_
    leaf := ?_
    tupMem := fun ψ ρp _ is hi => by
      show tupW (uAV ψ) is ∈ˢ idxSet (uAV ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
      exact tupW_mem hi
    ctor := ?_
    mkZero := fun ψ hz j fs => by
      show injW (p.resSort.eval ψ) j _ = pt
      rw [show p.resSort.eval ψ = 0 from hz, injW_zero]
    mkInj := ?_
    idxRecover := ?_
    slotRecover := ?_ }
  · -- the fibre
    intro ψ ρp hρ X hX t ht x
    have hXs : X ∈ˢ lfpFamSpace V (p.resSort.eval ψ)
        (idxSet (uAV ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))) := by
      rw [lfpFamSpace_eq]; exact hX
    have ht' : t ∈ˢ idxSet (uAV ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) := ht
    show x ∈ˢ app (app (fixFunVI [] (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
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
    have hislen : is.length = (d.IdsC ψ).length := hsp₂.length_eq
    have hsat : Sat V (d.params ψ).reverse (consList as ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
      simpa using this
    have hspAll : SpineFit ρ ((ppsAll ψ).map (·.2.2)) (as ++ is) := by
      have : (ppsAll ψ).map (·.2.2) = d.params ψ ++ d.IdsC ψ := by
        rw [hparams, hIds, ← List.map_append, List.take_append_drop]
      rw [this]
      exact hsp₁.append hsp₂
    have hframe : consList (as ++ is) ρ = consList is (consList as ρ) := consList_append _ _ _
    have hshift : shiftE (d.IdsC ψ).length 0 (consList (as ++ is) ρ) = consList as ρ := by
      rw [hframe, ← hislen]; exact shiftE_consList _ _
    have hfr : ConLeche.Semantics.frameIdx (d.IdsC ψ).length (consList (as ++ is) ρ) = is := by
      rw [hframe, ← hislen]; exact frameIdx_consList' _ _
    have hXZ := (hframes ψ (consList as ρ) hsat).1
    have hbase : FixBaseI [] (uAV ψ) (p.resSort.eval ψ) (consList (as ++ is) ρ) (d.IdsC ψ) d.rss
        (d.tlss ψ) (d.Eiss ψ) (fssZ ψ) (d.Ess ψ) := by
      refine ⟨?_, ?_, ?_, offOk_nil _ _ _⟩
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
      have := sumMkAV_fold (V := V) (tbl := []) (m := 0) (jc := j) hz (pds := (dsF j ψ).take p.nP)
        (fds := (dsF j ψ).drop p.nP) (Fss := uChains (d.Fss ψ)) (ρ := ρ) hsp₁' hsp₂ hok hjU
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
  · -- the tuple recovers the member and the readings (task #279 M-C′):
    -- the terminator's reading against the tuple's projections
    intro ψ ρp hρ is hsp X j fs hj hlen _ _ hall
    obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
    have hI : IdxOk (d.u ψ) ρp (d.IdsC ψ) := (hX ψ ρp hρ).hI
    have hEs : (d.Ess ψ).getD j [] = esF j ψ := by
      show (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [] = _
      rw [List.getD_eq_getElem?_getD, essOfR, List.getElem?_map, fixCtorDataList_getElem?,
        Nat.zero_add, hjA]
      rfl
    have hEsLen : (esF j ψ).length = (d.IdsC ψ).length := by
      rw [(hcf j cA hjA).2.2.lenE ψ, hIds, List.length_map, List.length_drop, hFD.len ψ]
      omega
    have htup : d.tup ψ 0 is = tupW (d.u ψ) is := rfl
    rw [hEs, ← hlen, htup] at hall
    have h := idxValsAt_of_eqsXI (u := d.u ψ) hI hsp hEsLen hall
    exact ⟨rfl, h⟩
  · -- a slot's tuple is the target's tuple (task #279 M-C′): the
    -- container view IS the family view at a single family
    intro ψ ρp _ j i hj _ τ _ _ _
    obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
    have hE : (d.Eiss ψ).getD j [] = eissF j ψ := by
      show (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [] = _
      rw [List.getD_eq_getElem?_getD, eissOfR, List.getElem?_map, fixCtorDataList_getElem?,
        Nat.zero_add, hjA]
      rfl
    rw [hE]
    rfl

end ConLeche.Model
