module

public import ConLeche.Model.Inductives.CopyPins
public import ConLeche.Model.Inductives.DeclNested
public import ConLeche.Verify.Inductives.CopyStable
import ConLeche.Verify.Inductives.NestedLedger
public section

/-!
# The copies' records, READ off the run (task #279 M-B′ step 3g)

`CopyPins.lean` states the three records the copies owe (`PinRead`,
`CopyIdxRead`, `CopyCtorRead`) and discharges `InvSetup`'s copy-side
hypotheses from them; `pinRead_of` reads the first off the pin check,
and `copyIdxRead_of_align` reads the second off the ALIGNMENT of the
copy's stored former with the container's at the annotated pin.  This
module closes the alignment: `copyIdxRead_of_copy` reads `PinRead` and
`CopyIdxRead` for a copy member of the scratch block from the mint
(`mkCopy`), the install's annotation of the minted former, the pin
check, the container's representation at the scratch environment, and
the two syntactic premises the annotation theorem K.4 needs
(`ConLeche/Verify/Inductives/CopyStable.lean`, `copyFormer_aligned`):

* **the container's stability** (`ReaderStable`): the head reader
  answers every binder's datum of the container's stored former — the
  property the kernel lane measured over every container of the
  Mathlib cone and init-full (corpus-vacuous; DESIGN `#### K.4`, the
  kernel lane's DOCKET §M1);
* **the per-component agreement** (`SortAgreeW`/`ProofAgreeW`): where
  the container's parameter domain reads as a sort, the annotated
  component's head reads the same — the one place K.4's frontier
  (a redex-headed component) shows;

and one ALIGNMENT premise of the elimination's own making: the copy's
stored former opens at the block's openers (the parameter telescopes of
the scratch block's members agree syntactically; the mutual install
compares them only definitionally, and an elaborated stream has them
identical); and one fact about the install: the copy's stored former is
the annotation, at the scratch environment, of its minted type (the
install annotates it at the pre-block environment and keeps it when its
telescope ends in a sort — the two lemmas that turn the run's facts into
this one are the docket's).
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
facts** (the statement's hypotheses are named in the module docstring). -/
theorem copyIdxRead_of_copy {μ : CheckMode} (hμ : μ.verifiedChecks = true) {envAux : Env}
    {mpAux : EnvModelM V μ envAux} {b : MutualBlock} {d : IndRepData V}
    (hreps : MutualBlockReps mpAux.base2 b d) {ψ : Name → Nat}
    -- the copy: member `t` of the scratch block, minted from `J` at `Ds`
    {t : Nat} (ht : t < b.k) {J : ContainerMember} {lvls : List Level} {Ds : List Expr}
    {pbs : List (Expr × BinderMeta)} {aux : Name} {copy : AuxType}
    (hmk : ConLeche.mkCopy pbs lvls Ds aux J = .ok copy)
    (hDs : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true) (hpbs : pbs.length = d.nP)
    -- the copy's stored former is the annotation of its minted type at the scratch env
    {cvT : ConstantVal} {capsT : IndCaps}
    (hfT : envAux.find? (d.memberName t) = some (.indInfo cvT capsT))
    {F : Nat} (hann : ConLeche.annotateCore μ envAux F 0 copy.type = .ok cvT.type)
    (hcl : copy.type.looseBVarsBounded 0 = true) (hnf : copy.type.hasFvar = false)
    -- the alignment premise: the stored former opens at the block's openers
    {fvsA : List Expr} {restC : Expr}
    (hopen : ConLeche.openPisAtFvars d.nP cvT.type 0 = some (fvsA, restC))
    -- the block's parameter context: the first member's former opened at those openers
    {cvT₀ : ConstantVal} {oA : Expr} {R : AnnotTerm}
    (hopened : Opened mpAux.base2 ψ d.nP cvT₀.type fvsA oA (d.params ψ).reverse R)
    -- the container's member at the scratch environment
    {cvTJ : ConstantVal} {capsJ : IndCaps} (hfJ : envAux.find? J.name = some (.indInfo cvTJ capsJ))
    (hJtype : J.type = cvTJ.type) (hJlps : J.lps = cvTJ.levelParams)
    {dJ : IndRepData V} {mmJ : Nat}
    (hFDJ : FormerData mpAux.base2 cvTJ (dJ.nP + dJ.nIdxAt mmJ) dJ.resSort (dJ.ppsM mmJ) (dJ.lvlsM mmJ))
    (hDsLen : Ds.length = dJ.nP)
    (hstab : ConLeche.ReaderStable envAux.find? 0 cvTJ.type)
    {bsJ : List (Expr × BinderMeta)} {uJ : Level}
    (hJtele : cvTJ.type.stripPis (dJ.nP + dJ.nIdxAt mmJ) = some (bsJ, .sort uJ))
    -- the pin's scope and its check at the scratch environment
    (hclosed : (Expr.abstractRange (Expr.mkAppN (.const J.name lvls) Ds) 0 d.nP 0).hasFvar = false ∧
      (Expr.abstractRange (Expr.mkAppN (.const J.name lvls) Ds) 0 d.nP 0).looseBVarsBounded d.nP
        = true)
    {e ty : Expr} {F₁ : Nat}
    (hpinAnn : ConLeche.annotateCore μ envAux F₁ d.nP (Expr.instantiateList
      (Expr.abstractRange (Expr.mkAppN (.const J.name lvls) Ds) 0 d.nP 0) fvsA.reverse) = .ok e)
    (hpinInf : ConLeche.inferTypeCore μ envAux F₁ d.nP e = .ok ty)
    -- the per-component premise, of the annotation the check computes
    (hcomp : ∀ (argsA dsA : List Expr) (restA : Expr),
      ConLeche.annotateCore μ envAux F₁ d.nP (Expr.instantiateList
        (Expr.abstractRange (Expr.mkAppN (.const J.name lvls) Ds) 0 d.nP 0) fvsA.reverse)
        = .ok (Expr.mkAppN (.const J.name lvls) argsA) →
      Expr.instPisAt argsA (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls)
        = some (dsA, restA) →
      ∀ (i : Nat) (A a : Expr), dsA[i]? = some A → argsA[i]? = some a →
        ConLeche.SortAgreeW envAux.find? A a ∧ ConLeche.ProofAgreeW envAux.find? A a) :
    ∃ (s : Level) (DsA : List AnnotTerm), (∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ') ∧
      ({d with resSort := s} : IndRepData V).PinRead ψ
        (mpAux.base2.acval J.name (Level.substFn ψ cvTJ.levelParams lvls)) DsA Ds.length ∧
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
  -- the mint
  obtain ⟨hlvls, ⟨tyI, htyI, hcopyTy⟩, -, -⟩ := ConLeche.mkCopy_inv hmk
  rw [hJtype, hJlps] at htyI
  rw [hJlps] at hlvls
  have hlenF : fvsA.length = d.nP := ConLeche.Verify.openPisAtFvars_length d.nP hopen
  -- the pin, read
  obtain ⟨argsA, DsA, hannA, hlenA, hargs, hsp, hlenD, hpin⟩ :=
    IndRepData.pinRead_of ({d with resSort := s} : IndRepData V) hμ hopened hfJ hlvls rfl hpinAnn
      hpinInf hclosed hlenF
  -- the container's telescope has room for the components
  obtain ⟨bsJ', rJ', hJtele'⟩ :=
    ConLeche.stripPis_instantiateLevelParams_some cvTJ.levelParams lvls _ hJtele
  obtain ⟨dsA, restA, hAt⟩ := ConLeche.instPisAt_of_stripPis' argsA hJtele'
    (by rw [hlenA, hDsLen]; exact Nat.le_add_right _ _)
  -- the former, aligned
  have hpinSpine : Expr.instantiateList
      (Expr.abstractRange (Expr.mkAppN (.const J.name lvls) Ds) 0 d.nP 0) fvsA.reverse
      = Expr.mkAppN (.const J.name lvls)
        (Ds.map fun D => Expr.instantiateList (D.abstractRange 0 d.nP 0) fvsA.reverse) := by
    rw [ConLeche.abstractRange_mkAppN, ConLeche.instantiateList_mkAppN, List.map_map]
    rw [show (Expr.const J.name lvls).abstractRange 0 d.nP 0 = .const J.name lvls from rfl,
      Expr.instantiateList]
    rfl
  have hcompA := hcomp argsA dsA restA hannA hAt
  rw [hpinSpine] at hannA
  have hfvsA : ∀ (i : Nat) (x : Expr), fvsA[i]? = some x →
      ∃ ty, x = .fvar i ty ∧ Expr.WScoped i ty ∧ ty.looseBVarsBounded 0 = true := by
    intro i x hx
    obtain ⟨⟨ty, rfl⟩, hw, hb, -, -⟩ := hopened.var i x hx
    exact ⟨ty, rfl, hw, hb⟩
  rw [hcopyTy] at hann hcl hnf
  have halign : restC = restA :=
    ConLeche.copyFormer_aligned mpAux.base2.wf hfJ hstab hJtele hDs
      (by rw [hDsLen]; exact Nat.le_add_right _ _) htyI hpbs hann hcl hnf hopen hfvsA hclosed.1
      hannA (by rw [hlenA]) hAt hcompA
  -- the record
  refine ⟨s, DsA, hsv, hpin, ?_⟩
  refine IndRepData.copyIdxRead_of_align ({d with resSort := s} : IndRepData V) mpAux hFD hfJ hFDJ
    rfl (by rw [hlenA, hDsLen]) hargs hsp hopen ?_
  rw [halign]
  exact ConLeche.instPis_of_instPisAt argsA hAt

/-! ## The premises, as the run's consumer states them

Four facts the copies' reads take of the run and its environment; each
is stated once here so that `copyIdxRead_of_run` reads every copy of
the scratch block from `DeclNestedRun` under exactly these. -/

/-- **The containers at the scratch environment**: every container
member the elimination recovers is stored there with the data the read
consumes (its former's data at its own datum), is STABLE under the head
reader (the property the kernel lane measured, corpus-vacuous) and is a
syntactic telescope ending in a sort (every stored former is, by
`checkSumTele`; not an environment invariant).  This is the container's
representation at the scratch environment, which comes through the
modelled route's `ModeledLeaf` disjunct until that route is deleted
(DESIGN §M.19). -/
def ContainersAt (env envAux : Env) (m : EnvModel V envAux) : Prop :=
  ∀ (I : Name) (ci : ConLeche.ContainerInfo), ConLeche.containerInfo? env I = some ci →
    ∀ (i : Nat) (J : ContainerMember), ci.members[i]? = some J →
      ∃ (cvTJ : ConstantVal) (capsJ : IndCaps) (dJ : IndRepData V) (mmJ : Nat)
        (bsJ : List (Expr × BinderMeta)) (uJ : Level),
        envAux.find? J.name = some (.indInfo cvTJ capsJ) ∧ J.type = cvTJ.type ∧
        J.lps = cvTJ.levelParams ∧ ci.nP = dJ.nP ∧
        FormerData m cvTJ (dJ.nP + dJ.nIdxAt mmJ) dJ.resSort (dJ.ppsM mmJ) (dJ.lvlsM mmJ) ∧
        ConLeche.ReaderStable envAux.find? 0 cvTJ.type ∧
        cvTJ.type.stripPis (dJ.nP + dJ.nIdxAt mmJ) = some (bsJ, .sort uJ)

/-- **The copies' stored formers are the annotations of their minted
types at the scratch environment.**  The install annotates a former at
the PRE-block environment (`mutualFormerChecks`) and keeps it when its
telescope ends in a sort (`checkSumTele`'s first branch); the copy's
minted former mentions no block member, so the two annotations agree,
and its telescope does end in a sort (the container's does).  The two
lemmas that turn the run into this statement — the annotator's
stability under a conservative environment extension on a resolving
term, and the minted former's telescope shape — are docketed. -/
def AuxFormersAnnot (μ : CheckMode) (F : Nat) (envAux : Env) (b : MutualBlock) (k : Nat) : Prop :=
  ∀ t, k ≤ t → t < b.k → ∀ (cv : ConstantVal) (nIdx : Nat), b.formers[t]? = some (cv, nIdx) →
    ∀ (cvT : ConstantVal) (caps : IndCaps), envAux.find? cv.name = some (.indInfo cvT caps) →
      ConLeche.annotateCore μ envAux F 0 cv.type = .ok cvT.type ∧
      cv.type.looseBVarsBounded 0 = true ∧ cv.type.hasFvar = false

/-- **The alignment premise**: every copy's stored former opens at the
block's openers — the ones the pin check annotates at (the stored first
member's).  The parameter telescopes of the scratch block's members
agree syntactically on an elaborated stream (the constructors' binders
are the type's); the mutual install compares them only definitionally. -/
def AuxOpensAt (envAux : Env) (b : MutualBlock) (k : Nat) (nP : Nat) (fvsA : List Expr) : Prop :=
  ∀ t, k ≤ t → t < b.k → ∀ (cv : ConstantVal) (nIdx : Nat), b.formers[t]? = some (cv, nIdx) →
    ∀ (cvT : ConstantVal) (caps : IndCaps), envAux.find? cv.name = some (.indInfo cvT caps) →
      ∃ restC, ConLeche.openPisAtFvars nP cvT.type 0 = some (fvsA, restC)

/-- **The components read like the parameters they replace**, per pin,
of the annotation the pin check computes at the openers: wherever the
container's parameter domain (with the earlier components substituted)
reads as a sort, the component reads the same, for both readers.
K.4's frontier is exactly where this fails (a redex-headed component). -/
def PinCompsAgree (μ : CheckMode) (F : Nat) (envAux : Env) (nP : Nat) (fvsA : List Expr)
    (pins : List ConLeche.NestedPin) : Prop :=
  ∀ q ∈ pins, ∀ (Jn : Name) (lvls : List Level) (Ds : List Expr),
    q.pin = Expr.mkAppN (.const Jn lvls) Ds →
    ∀ (cvTJ : ConstantVal) (capsJ : IndCaps), envAux.find? Jn = some (.indInfo cvTJ capsJ) →
    ∀ (argsA dsA : List Expr) (restA : Expr),
      ConLeche.annotateCore μ envAux F nP
        (Expr.instantiateList (Expr.abstractRange q.pin 0 nP 0) fvsA.reverse)
        = .ok (Expr.mkAppN (.const Jn lvls) argsA) →
      Expr.instPisAt argsA (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls)
        = some (dsA, restA) →
      ∀ (i : Nat) (A a : Expr), dsA[i]? = some A → argsA[i]? = some a →
        ConLeche.SortAgreeW envAux.find? A a ∧ ConLeche.ProofAgreeW envAux.find? A a

/-! ## Every copy of the scratch block, read off the run -/

/-- A member's name in the auxiliary block is its former's. -/
theorem memberNames_getD {b : MutualBlock} {t : Nat} {cv : ConstantVal} {nIdx : Nat}
    (h : b.formers[t]? = some (cv, nIdx)) : b.memberNames.getD t .anonymous = cv.name := by
  unfold MutualBlock.memberNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

/-- **`PinRead` and `CopyIdxRead` for EVERY copy of the scratch block,
from the run**, under the four premises above: for pin `j` the copy
member `p.k + j` has its pin `J.{lvls} Ds` read at the block's parameter
frame and its index telescope the container's at the pin's readings. -/
theorem copyIdxRead_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ConLeche.ElimState) (b : MutualBlock) (envAux : Env) (fvsA : List Expr),
      ConLeche.auxBlock p st = some b ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
      (ContainersAt env envAux mpAux.base2 → AuxFormersAnnot μ F envAux b p.k →
        AuxOpensAt envAux b p.k p.nP fvsA → PinCompsAgree μ F envAux p.nP fvsA st.pins →
        ∀ (j : Nat), j < st.pins.length → ∀ (ψ : Name → Nat),
          ∃ (q : ConLeche.NestedPin) (Jn : Name) (lvls : List Level) (Ds : List Expr)
            (cvTJ : ConstantVal) (dJ : IndRepData V) (mmJ : Nat) (s : Level) (DsA : List AnnotTerm),
            st.pins[j]? = some q ∧ q.pin = Expr.mkAppN (.const Jn lvls) Ds ∧
            (∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ') ∧
            ({d with resSort := s} : IndRepData V).PinRead ψ
              (mpAux.base2.acval Jn (Level.substFn ψ cvTJ.levelParams lvls)) DsA Ds.length ∧
            ({d with resSort := s} : IndRepData V).CopyIdxRead ψ (p.k + j) dJ
              (Level.substFn ψ cvTJ.levelParams lvls) mmJ DsA) := by
  obtain ⟨-, -, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, a₀, fvsA,
    helim, -, hfresh, hb, hcore, hstored, ha₀, hfv, hpc, hpinsAux, -, hrm, -⟩ := h
  obtain ⟨mpAux, d, hreps⟩ := nestedAuxModel hμ mp hE helim hfresh hb hcore hstored hrm
  refine ⟨st, b, envAux, fvsA.1, hb, mpAux, d, hreps, ?_⟩
  intro hcont hannAll hopens hcomps j hj ψ
  -- the block's shape
  obtain ⟨hbnP, -, -, -, hblen, hbformers, -⟩ := ConLeche.auxBlock_inv hb
  have hk : b.k = st.types.length := ConLeche.auxBlock_k hb
  have hlenSt : st.types.length = p.k + st.pins.length := by
    have := ConLeche.elimNested_length helim
    rwa [nestedTypes0_length] at this
  have hreps₀ := hreps
  obtain ⟨hctorsC, hkb, hkRb, hnP, -, -, hnames, hall⟩ := hreps
  -- the copy's origin
  obtain ⟨t₀, params, body, ht₀, hop, I, ci, i, j₀, J, lvls, Ds, pbs, q, copy, st₁, st₂, cs',
    hci, hJ, hjE, hgrp, hq, hqc, hqp, hmk, hDs, hpbs, hDsLen, hty, hrun, h₁, h₂⟩ :=
    ConLeche.elimNested_copy helim hj
  rw [nestedTypes0_length] at hty
  have ht : p.k + j < b.k := by rw [hk, hlenSt]; omega
  -- the copy's former in the auxiliary block, and its stored form
  obtain ⟨nIdx, -, hform⟩ := hbformers (p.k + j) _ hty
  have hname : d.memberName (p.k + j) = copy.name := by
    rw [hnames _ ht, memberNames_getD hform]
  obtain ⟨s, cvT, cvR, capsT, mI, rP, rules, hfT, -, -, hsv, hrep⟩ := hall (p.k + j) ht
  have hfTc : envAux.find? copy.name = some (.indInfo cvT capsT) := by rw [← hname]; exact hfT
  obtain ⟨hann, hcl, hnf⟩ := hannAll (p.k + j) (Nat.le_add_right _ _) ht _ _ hform cvT capsT hfTc
  obtain ⟨restC, hopen⟩ := hopens (p.k + j) (Nat.le_add_right _ _) ht _ _ hform cvT capsT hfTc
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
  rw [hqp] at hpinAnn hclosed
  -- the container's member at the scratch environment
  obtain ⟨cvTJ, capsJ, dJ, mmJ, bsJ, uJ, hfJ, hJtype, hJlps, hciNP, hFDJ, hstab, hJtele⟩ :=
    hcont I ci hci i J hJ
  have hcomp := hcomps q hqmem J.name lvls Ds hqp cvTJ capsJ hfJ
  rw [hqp] at hcomp
  -- the read
  have hdnP' : d.nP = p.nP := hdnP
  have hopened' : Opened mpAux.base2 ψ d.nP a₀.cvTa.type fvsA.1 fvsA.2 (d.params ψ).reverse R :=
    hopened
  obtain ⟨s', DsA, hsv', hpin, hidx⟩ := copyIdxRead_of_copy hμ hreps₀ (ψ := ψ) ht hmk hDs
    (by rw [hpbs, hdnP]) hfT hann hcl hnf (by rw [hdnP]; exact hopen)
    hopened' hfJ hJtype hJlps hFDJ (by rw [hDsLen, hciNP]) hstab hJtele
    (by rw [hdnP]; exact hclosed) (by rw [hdnP]; exact hpinAnn) (by rw [hdnP]; exact hpinInf)
    (fun argsA dsA restA hA hB => hcomp argsA dsA restA (by rw [← hdnP]; exact hA) hB)
  exact ⟨q, J.name, lvls, Ds, cvTJ, dJ, mmJ, s', DsA, hq, hqp, hsv', hpin, hidx⟩

end ConLeche.Model
