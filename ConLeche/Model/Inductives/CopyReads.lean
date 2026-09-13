module

public import ConLeche.Model.Inductives.CopyPins
public import ConLeche.Model.Inductives.DeclNested
import ConLeche.Verify.Inductives.NestedLedger
public section

/-!
# The copies' records, READ off the run (task #279 M-B′ step 3g / §M.24)

`CopyPins.lean` states the three records the copies owe (`PinRead`,
`CopyIdxRead`, `CopyCtorRead`) and discharges `InvSetup`'s copy-side
hypotheses from them; `pinRead_of` reads the first off the pin check,
and `copyIdxRead_of_align` reads the second off the ALIGNMENT of the
copy's stored former with the container's at the annotated pin.

Since K.9 (`nestedRemint`) every copy's type is MINTED as the
container's stored annotated former at the ANNOTATED pin components,
closed over the block's first former's annotated binders — so the
alignment is BY CONSTRUCTION, up to the fact K.10 records in the run
(the auxiliary install stores the minted type as it is: the pass
keeps every written datum of a fully annotated term) and the
agreement of the two annotation runs of a pin (the re-mint's at the
pre-block environment plus the formers, the pin check's at the
scratch environment — the reader branch is environment-monotone,
K.5).  This module therefore takes that alignment as ONE named
hypothesis, `CopyTypesAsMinted`, stated in the form the read consumes
(the stored former opened at the pin check's openers IS the
container's at the pin check's annotated components), and reads
`PinRead` and `CopyIdxRead` for every copy of the scratch block from
`DeclNestedRun` under it and the containers' representation at the
scratch environment (`ContainersAt`).  The earlier route through the
annotator (session 11's `CopyStable.lean` — `copyFormer_aligned` under
the premises `AuxFormersAnnot`/`AuxOpensAt`/`PinCompsAgree`) was
superseded for the formers by K.9/K.10 and DELETED in session 13
(DESIGN §M.25); nothing of it is consumed.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember AuxType BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-- The sort transfer of `CopyIdxRead` across the block's re-sorting. -/
theorem CopyIdxRead.congr_sort {d : IndRepData V} {s s' : Level}
    (hs : ∀ φ : Name → Nat, s.eval φ = s'.eval φ)
    {ψ : Name → Nat} {t : Nat} {dJ : IndRepData V} {ψ' : Name → Nat} {mmJ : Nat}
    {DsA : List AnnotTerm}
    (h : ({d with resSort := s} : IndRepData V).CopyIdxRead ψ t dJ ψ' mmJ DsA) :
    ({d with resSort := s'} : IndRepData V).CopyIdxRead ψ t dJ ψ' mmJ DsA :=
  ⟨by
    have h1 : dJ.w ψ' = s.eval ψ := h.sort
    show dJ.w ψ' = s'.eval ψ
    rw [← hs ψ]; exact h1, h.idxIff⟩

/-- **`PinRead` and `CopyIdxRead` for a copy member, from the run's
facts**: the copy's representation in the scratch block, the block's
opened parameter context, the container's member at the scratch
environment, the pin's scope and check, and the ALIGNMENT (the stored
former opened at the check's openers is the container's at the check's
annotated components — K.9's construction, K.10's equation). -/
theorem copyIdxRead_of_copy {μ : CheckMode} (hμ : μ.verifiedChecks = true) {envAux : Env}
    {mpAux : EnvModelM V μ envAux} {b : MutualBlock} {d : IndRepData V}
    (hreps : MutualBlockReps mpAux.base2 b d) {ψ : Name → Nat}
    -- the copy: member `t` of the scratch block, at the pin `J.{lvls} Ds`
    {t : Nat} (ht : t < b.k) {Jn : Name} {lvls : List Level} {Ds : List Expr}
    {cvT : ConstantVal} {capsT : IndCaps}
    (hfT : envAux.find? (d.memberName t) = some (.indInfo cvT capsT))
    -- the block's parameter context: the first member's former opened at the openers
    {fvsA : List Expr} {cvT₀ : ConstantVal} {oA : Expr} {R : AnnotTerm}
    (hopened : Opened mpAux.base2 ψ d.nP cvT₀.type fvsA oA (d.params ψ).reverse R)
    (hlenF : fvsA.length = d.nP)
    -- the container's member at the scratch environment
    {cvTJ : ConstantVal} {capsJ : IndCaps} (hfJ : envAux.find? Jn = some (.indInfo cvTJ capsJ))
    (hlvls : lvls.length = cvTJ.levelParams.length)
    {dJ : IndRepData V} {mmJ : Nat}
    (hFDJ : FormerData mpAux.base2 cvTJ (dJ.nP + dJ.nIdxAt mmJ) dJ.resSort (dJ.ppsM mmJ) (dJ.lvlsM mmJ))
    (hDsLen : Ds.length = dJ.nP)
    -- the pin's scope and its check at the scratch environment
    (hclosed : (Expr.abstractRange (Expr.mkAppN (.const Jn lvls) Ds) 0 d.nP 0).hasFvar = false ∧
      (Expr.abstractRange (Expr.mkAppN (.const Jn lvls) Ds) 0 d.nP 0).looseBVarsBounded d.nP
        = true)
    {e ty : Expr} {F₁ : Nat}
    (hpinAnn : ConLeche.annotateCore μ envAux F₁ d.nP (Expr.instantiateList
      (Expr.abstractRange (Expr.mkAppN (.const Jn lvls) Ds) 0 d.nP 0) fvsA.reverse) = .ok e)
    (hpinInf : ConLeche.inferTypeCore μ envAux F₁ d.nP e = .ok ty)
    -- THE ALIGNMENT, at the components the check computes
    (halign : ∀ argsA : List Expr,
      ConLeche.annotateCore μ envAux F₁ d.nP (Expr.instantiateList
        (Expr.abstractRange (Expr.mkAppN (.const Jn lvls) Ds) 0 d.nP 0) fvsA.reverse)
        = .ok (Expr.mkAppN (.const Jn lvls) argsA) →
      ∃ rest, ConLeche.openPisAtFvars d.nP cvT.type 0 = some (fvsA, rest) ∧
        Expr.instPis (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) argsA = some rest) :
    ∃ (s : Level) (DsA : List AnnotTerm), (∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ') ∧
      ({d with resSort := s} : IndRepData V).PinRead ψ
        (mpAux.base2.acval Jn (Level.substFn ψ cvTJ.levelParams lvls)) DsA Ds.length ∧
      ({d with resSort := s} : IndRepData V).CopyIdxRead ψ t dJ
        (Level.substFn ψ cvTJ.levelParams lvls) mmJ DsA := by
  -- the copy's own representation and former
  obtain ⟨-, hkb, hkRb, -, -, -, -, hall⟩ := hreps
  obtain ⟨s, cvT', cvR, caps', mI, rP, rules, hfT', -, -, hsv, hrep⟩ := hall t ht
  obtain ⟨h1, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hfT))
  have h2 := h1.symm
  subst h2
  have hFD : FormerData mpAux.base2 cvT
      (({d with resSort := s} : IndRepData V).nP + ({d with resSort := s} : IndRepData V).nIdxAt t)
      ({d with resSort := s} : IndRepData V).resSort
      (({d with resSort := s} : IndRepData V).ppsM t) (({d with resSort := s} : IndRepData V).lvlsM t) :=
    hrep.formersRead t (by show t < d.kReal; rw [hkRb]; exact ht) cvT capsT hfT
  -- the pin, read
  obtain ⟨argsA, DsA, hannA, hlenA, hargs, hsp, hlenD, hpin⟩ :=
    IndRepData.pinRead_of ({d with resSort := s} : IndRepData V) hμ hopened hfJ hlvls rfl hpinAnn
      hpinInf hclosed hlenF
  -- the former, aligned
  obtain ⟨rest, hopen, hrest⟩ := halign argsA hannA
  refine ⟨s, DsA, hsv, hpin, ?_⟩
  exact IndRepData.copyIdxRead_of_align ({d with resSort := s} : IndRepData V) mpAux hFD hfJ hFDJ
    rfl (by rw [hlenA, hDsLen]) hargs hsp hopen hrest

/-! ## The premises, as the run's consumer states them

Two facts the copies' reads take of the run and its environment; each
is stated once here so that `copyIdxRead_of_run` reads every copy of
the scratch block from `DeclNestedRun` under exactly these. -/

/-- **The containers at the scratch environment**: every container
member the elimination recovers is stored there with the data the read
consumes (its former's data at its own datum).  This is the container's
representation at the scratch environment, which comes through the
modelled route's `ModeledLeaf` disjunct until that route is deleted
(DESIGN §M.19). -/
def ContainersAt (env envAux : Env) (m : EnvModel V envAux) : Prop :=
  ∀ (I : Name) (ci : ConLeche.ContainerInfo), ConLeche.containerInfo? env I = some ci →
    ∀ (i : Nat) (J : ContainerMember), ci.members[i]? = some J →
      ∃ (cvTJ : ConstantVal) (capsJ : IndCaps) (dJ : IndRepData V) (mmJ : Nat),
        envAux.find? J.name = some (.indInfo cvTJ capsJ) ∧ J.type = cvTJ.type ∧
        J.lps = cvTJ.levelParams ∧ ci.nP = dJ.nP ∧
        FormerData m cvTJ (dJ.nP + dJ.nIdxAt mmJ) dJ.resSort (dJ.ppsM mmJ) (dJ.lvlsM mmJ)

/-- **The copies' stored types are the minted ones** (K.9's
construction, K.10's recorded equation), read at the pin check: copy
`k + j`'s stored former, opened at the block's openers (the stored first
member's, the ones the pin check annotates at), is the container's
stored former at the level instantiation, instantiated at the pin's
components AS THE CHECK ANNOTATES THEM.  What stands behind it: the
re-mint builds the copy's type as `closeTelescope pbsA 0 (instPis
(JtyA[lvls]) argsA)` from the annotated first former's binders and the
annotated components; the auxiliary install stores it unchanged (the
pass keeps every datum of a fully annotated term — the flag K.10 adds
makes that a recorded identity); `openPisAtFvars_closeTelescope` opens
it at those binders; and the check's annotation of a component at the
scratch environment agrees with the re-mint's at the pre-block
environment plus the formers (the reader branch is environment-monotone,
K.5).  None of it is a measured premise. -/
def CopyTypesAsMinted (μ : CheckMode) (F : Nat) (envAux : Env) (b : MutualBlock) (k nP : Nat)
    (fvsA : List Expr) (pins : List ConLeche.NestedPin) : Prop :=
  ∀ (j : Nat) (q : ConLeche.NestedPin), pins[j]? = some q →
    ∀ (Jn : Name) (lvls : List Level) (Ds : List Expr), q.pin = Expr.mkAppN (.const Jn lvls) Ds →
    ∀ (cv : ConstantVal) (nIdx : Nat), b.formers[k + j]? = some (cv, nIdx) →
    ∀ (cvT : ConstantVal) (caps : IndCaps), envAux.find? cv.name = some (.indInfo cvT caps) →
    ∀ (cvTJ : ConstantVal) (capsJ : IndCaps), envAux.find? Jn = some (.indInfo cvTJ capsJ) →
    ∀ argsA : List Expr,
      ConLeche.annotateCore μ envAux F nP
        (Expr.instantiateList (Expr.abstractRange q.pin 0 nP 0) fvsA.reverse)
        = .ok (Expr.mkAppN (.const Jn lvls) argsA) →
      ∃ rest, ConLeche.openPisAtFvars nP cvT.type 0 = some (fvsA, rest) ∧
        Expr.instPis (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) argsA = some rest

/-! ## Every copy of the scratch block, read off the run -/

/-- A member's name in the auxiliary block is its former's. -/
theorem memberNames_getD {b : MutualBlock} {t : Nat} {cv : ConstantVal} {nIdx : Nat}
    (h : b.formers[t]? = some (cv, nIdx)) : b.memberNames.getD t .anonymous = cv.name := by
  unfold MutualBlock.memberNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

/-- **`PinRead` and `CopyIdxRead` for EVERY copy of the scratch block,
from the run**, under the two premises above: for pin `j` the copy
member `p.k + j` has its pin `J.{lvls} Ds` read at the block's parameter
frame and its index telescope the container's at the pin's readings. -/
theorem copyIdxRead_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ConLeche.ElimState) (b : MutualBlock) (envAux : Env) (fvsA : List Expr),
      ConLeche.auxBlock p st = some b ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
      (ContainersAt env envAux mpAux.base2 →
        CopyTypesAsMinted μ F envAux b p.k p.nP fvsA st.pins →
        ∀ (j : Nat), j < st.pins.length → ∀ (ψ : Name → Nat),
          ∃ (q : ConLeche.NestedPin) (Jn : Name) (lvls : List Level) (Ds : List Expr)
            (cvTJ : ConstantVal) (dJ : IndRepData V) (mmJ : Nat) (s : Level) (DsA : List AnnotTerm),
            st.pins[j]? = some q ∧ q.pin = Expr.mkAppN (.const Jn lvls) Ds ∧
            (∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ') ∧
            ({d with resSort := s} : IndRepData V).PinRead ψ
              (mpAux.base2.acval Jn (Level.substFn ψ cvTJ.levelParams lvls)) DsA Ds.length ∧
            ({d with resSort := s} : IndRepData V).CopyIdxRead ψ (p.k + j) dJ
              (Level.substFn ψ cvTJ.levelParams lvls) mmJ DsA) := by
  obtain ⟨-, -, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, st₀, a₀, fvsA, order,
    helim, hremint, -, hfresh, -, hb, hcore, hstored, ha₀, hfv, hpc, hpinsAux, -, hrm, -⟩ := h
  obtain ⟨mpAux, d, hreps⟩ := nestedAuxModel hμ mp hE helim hremint hfresh hb hcore hstored hrm
  refine ⟨st, b, envAux, fvsA.1, hb, mpAux, d, hreps, ?_⟩
  intro hcont hminted j hj ψ
  -- the re-mint: pins, names and lengths are the elimination's
  obtain ⟨hpins, -, hlenT, -⟩ := ConLeche.nestedRemint_inv hremint
  -- the block's shape
  obtain ⟨hbnP, -, -, -, hblen, hbformers, -⟩ := ConLeche.auxBlock_inv hb
  have hk : b.k = st.types.length := ConLeche.auxBlock_k hb
  have hlenSt : st.types.length = p.k + st.pins.length := by
    have := ConLeche.elimNested_length helim
    rw [nestedTypes0_length] at this
    rw [hlenT, hpins]; exact this
  have hreps₀ := hreps
  obtain ⟨hctorsC, hkb, hkRb, hnP, -, -, hnames, hall⟩ := hreps
  -- the copy's origin (at the elimination's state)
  have hj₀ : j < st₀.pins.length := by rw [← hpins]; exact hj
  obtain ⟨t₀, params, body, pbs, body₀, ht₀, hop, hstrip, I, ci, i, j₀, J, lvls, Ds, q, copy,
    st₁, st₂, cs', hci, hJ, hjE, hgrp, hq, hqc, hqp, hmk, hDs, hpbs, hDsLen, hty, hrun, h₁, h₂⟩ :=
    ConLeche.elimNested_copy helim hj₀
  rw [nestedTypes0_length] at hty
  rw [← hpins] at hq
  have ht : p.k + j < b.k := by rw [hk, hlenSt]; omega
  -- the copy's entry in the re-minted state: same name
  obtain ⟨tS, htyS⟩ : ∃ tS, st.types[p.k + j]? = some tS :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenSt]; omega)⟩
  have hnameS : tS.name = copy.name := by
    have := ConLeche.nestedRemint_name hremint (p.k + j)
    rw [htyS, hty] at this
    exact Option.some.inj this
  -- the copy's former in the auxiliary block
  obtain ⟨nIdx, -, hform⟩ := hbformers (p.k + j) _ htyS
  have hname : d.memberName (p.k + j) = tS.name := by
    rw [hnames _ ht, memberNames_getD hform]
  obtain ⟨s, cvT, cvR, capsT, mI, rP, rules, hfT, -, -, hsv, hrep⟩ := hall (p.k + j) ht
  have hfTc : envAux.find? tS.name = some (.indInfo cvT capsT) := by rw [← hname]; exact hfT
  -- the first member's opened parameter context
  have hk0 : 0 < b.k := Nat.lt_of_le_of_lt (Nat.zero_le _) ht
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, hfT₀, -, -, -, hrep₀⟩ := hall 0 hk0
  obtain ⟨hstoredLen, hstoredAt⟩ := ConLeche.auxStoredAll_inv hstored
  have hkp : p.k ≤ b.k := by rw [hk, hlenSt]; omega
  have hkpos : 0 < p.k := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, List.take_zero] at ha₀
    exact nomatch ha₀
  have ha₀' : stored[0]? = some a₀ := by
    rw [List.head?_eq_getElem?, List.getElem?_take_of_lt hkpos] at ha₀
    exact ha₀
  rw [hstoredAt 0 (by omega)] at ha₀'
  obtain ⟨cv₀, nIdx₀, capsA₀, hform₀, hfA₀⟩ := ConLeche.auxStored?_inv ha₀'
  have hname₀ : d.memberName 0 = cv₀.name := by rw [hnames 0 hk0, memberNames_getD hform₀]
  rw [hname₀] at hfT₀
  obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT₀.symm.trans hfA₀))
  have hFD₀ : FormerData mpAux.base2 a₀.cvTa
      (({d with resSort := s₀} : IndRepData V).nP + ({d with resSort := s₀} : IndRepData V).nIdxAt 0)
      ({d with resSort := s₀} : IndRepData V).resSort
      (({d with resSort := s₀} : IndRepData V).ppsM 0) (({d with resSort := s₀} : IndRepData V).lvlsM 0) :=
    hrep₀.formersRead 0 (by show 0 < d.kReal; rw [hkRb]; exact hk0) a₀.cvTa caps₀
      (by rw [← hname₀] at hfT₀; exact hfT₀)
  have hdnP : d.nP = p.nP := by rw [hnP, hbnP]
  have hfv' : ConLeche.openPisAtFvars ({d with resSort := s₀} : IndRepData V).nP a₀.cvTa.type 0
      = some (fvsA.1, fvsA.2) := by
    show ConLeche.openPisAtFvars d.nP a₀.cvTa.type 0 = some (fvsA.1, fvsA.2)
    rw [hdnP]; exact hfv
  obtain ⟨R, hopened⟩ := IndRepData.opened_params ({d with resSort := s₀} : IndRepData V) ψ
    (by rw [← hname₀] at hfT₀; exact hfT₀) hFD₀ hfv'
  -- the pin's check and scope
  have hqmem : q ∈ st.pins := List.mem_of_getElem? hq
  obtain ⟨e, ty, hpinAnn, hpinInf⟩ := ConLeche.nestedPinsOk_inv hpinsAux q hqmem
  have hclosed := ConLeche.pinsClosed_inv hpc q hqmem
  -- the container's member at the scratch environment
  obtain ⟨cvTJ, capsJ, dJ, mmJ, hfJ, hJtype, hJlps, hciNP, hFDJ⟩ := hcont I ci hci i J hJ
  have hlvls : lvls.length = cvTJ.levelParams.length := by
    rw [← hJlps]; exact (ConLeche.mkCopy_inv hmk).1
  -- the alignment, at this copy
  have halign := hminted j q hq J.name lvls Ds hqp _ _ hform cvT capsT hfTc cvTJ capsJ hfJ
  rw [hqp] at hpinAnn hclosed halign
  -- the read
  have hopened' : Opened mpAux.base2 ψ d.nP a₀.cvTa.type fvsA.1 fvsA.2 (d.params ψ).reverse R :=
    hopened
  have hlenF : fvsA.1.length = d.nP := by
    rw [hdnP]; exact ConLeche.Verify.openPisAtFvars_length _ hfv
  obtain ⟨s', DsA, hsv', hpin, hidx⟩ := copyIdxRead_of_copy hμ hreps₀ (ψ := ψ) ht hfT
    hopened' hlenF hfJ hlvls hFDJ (by rw [hDsLen, hciNP])
    (by rw [hdnP]; exact hclosed) (by rw [hdnP]; exact hpinAnn) (by rw [hdnP]; exact hpinInf)
    (fun argsA hA => by
      obtain ⟨rest, hopen, hrest⟩ := halign argsA (by rw [← hdnP]; exact hA)
      exact ⟨rest, by rw [hdnP]; exact hopen, hrest⟩)
  exact ⟨q, J.name, lvls, Ds, cvTJ, dJ, mmJ, s', DsA, hq, hqp, hsv', hpin, hidx⟩

end ConLeche.Model
