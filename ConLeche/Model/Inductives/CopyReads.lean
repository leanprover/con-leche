module

public import ConLeche.Model.Inductives.CopyPins
public import ConLeche.Model.Inductives.DeclNested
import ConLeche.Verify.Inductives.NestedLedger
import ConLeche.Verify.Inductives.AuxFormers
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Leaves
import ConLeche.Verify.InstLevels
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
    rw [← hs ψ]; exact h1, h.nIdx, h.idxIff⟩

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
    {e ty : Expr} {F₁ : Nat} {envA : Env} {Fa : Nat}
    -- the pin's annotation (K.10: the re-mint's, at the pre-block environment
    -- plus the formers) and its inference at the scratch environment
    (hpinAnn : ConLeche.annotateCore μ envA Fa d.nP (Expr.instantiateList
      (Expr.abstractRange (Expr.mkAppN (.const Jn lvls) Ds) 0 d.nP 0) fvsA.reverse) = .ok e)
    (hpinInf : ConLeche.inferTypeCore μ envAux F₁ d.nP e = .ok ty)
    -- THE ALIGNMENT, at the annotated components
    (halign : ∀ argsA : List Expr,
      ConLeche.annotateCore μ envA Fa d.nP (Expr.instantiateList
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

/-- **The copies' stored types are the minted ones** (K.9's construction,
K.10's identity), stated over the ONE list of annotated pins the run
records (`pinsA`, returned by `nestedRemint` and typed by both pin
checks): pin `j`'s annotated form is the annotation, at the pre-block
environment plus the block's formers, of the pin abstracted over the
block's parameters and opened at the STORED first former's openers; and
copy `k + j`'s stored former, opened at those openers, is the container's
stored former at the level instantiation, instantiated at the annotated
components.  DERIVED from the run by `copyTypesAsMinted_of_facts`
below (the re-mint's type ledger, the auxiliary install storing the
minted type, the bvar-form round trip) under two syntactic premises
(`ContainersStored`, `FirstFormerStoredAsAnnotated`); it stays a named
record because it is the exact shape `copyIdxRead_of_copy` consumes. -/
def CopyTypesAsMinted (μ : CheckMode) (F : Nat) (env envAux : Env) (p : ConLeche.NestedParts)
    (b : MutualBlock) (fvsA : List Expr) (pinsA : List (ConLeche.NestedPin × Expr)) : Prop :=
  ∀ (j : Nat) (q : ConLeche.NestedPin) (pinA : Expr), pinsA[j]? = some (q, pinA) →
    ConLeche.annotateCore μ
      ⟨(p.formers.map fun f => ConstantInfo.indInfo f.1 {}).reverse ++ env.consts⟩ F p.nP
      (Expr.instantiateList (Expr.abstractRange q.pin 0 p.nP 0) fvsA.reverse) = .ok pinA ∧
    ∀ (Jn : Name) (lvls : List Level) (argsA : List Expr),
      pinA = Expr.mkAppN (.const Jn lvls) argsA →
    ∀ (cv : ConstantVal) (nIdx : Nat), b.formers[p.k + j]? = some (cv, nIdx) →
    ∀ (cvT : ConstantVal) (caps : IndCaps), envAux.find? cv.name = some (.indInfo cvT caps) →
    ∀ (cvTJ : ConstantVal) (capsJ : IndCaps), envAux.find? Jn = some (.indInfo cvTJ capsJ) →
      ∃ rest, ConLeche.openPisAtFvars p.nP cvT.type 0 = some (fvsA, rest) ∧
        Expr.instPis (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) argsA = some rest

/-! ## The identity, DERIVED from the run (K.10, DESIGN §M.25)

`CopyTypesAsMinted` is no hypothesis on a real run: it follows from the
run's own conjuncts and two syntactic premises about the STORED
records the run does not itself record. -/

/-- **The containers' stored records** (a syntactic premise, universal
for inductives this checker stored; the run does not record it): every
member `J` of a recovered group is named, is recovered again by ITS OWN
`containerInfo?` lookup with the same type and level parameters (the
group is read off each member's recursor, and the run records only the
occurrence head's lookup), is stored at the scratch environment with
its recovered type and level parameters, and is a closed syntactic
telescope ending in a sort over the group's parameters and its own
indices. -/
def ContainersStored (env envAux : Env) : Prop :=
  ∀ (I : Name) (ci : ConLeche.ContainerInfo), ConLeche.containerInfo? env I = some ci →
    ∀ (i : Nat) (J : ContainerMember), ci.members[i]? = some J →
      J.name ≠ .anonymous ∧
      (∃ (ciJ : ConLeche.ContainerInfo) (J' : ContainerMember),
        ConLeche.containerInfo? env J.name = some ciJ ∧
        ciJ.members.find? (fun J'' => J''.name == J.name) = some J' ∧
        J'.type = J.type ∧ J'.lps = J.lps) ∧
      (∃ (cvTJ : ConstantVal) (capsJ : IndCaps),
        envAux.find? J.name = some (.indInfo cvTJ capsJ) ∧ J.type = cvTJ.type ∧
        J.lps = cvTJ.levelParams) ∧
      J.type.hasFvar = false ∧ J.type.looseBVarsBounded 0 = true ∧
      ∃ (nIdx : Nat) (bs : List (Expr × BinderMeta)) (u : Level),
        J.type.stripPis (ci.nP + nIdx) = some (bs, .sort u)

/-- **The stored first former is its annotation**: `checkSumTele` took
its identity branch on member 0 — true whenever the block's first
former's annotated type is a syntactic telescope ending in a sort
(every elaborated stream; a crafted `T : id Type` takes the other
branch, and the re-mint's openers then differ from the stored former's
in their annotations — K.11 (b)). -/
def FirstFormerStoredAsAnnotated (μ : CheckMode) (F : Nat) (env : Env) (p : ConLeche.NestedParts)
    (a₀ : AuxStored) : Prop :=
  ∃ cv₀ : ConstantVal, p.formers.head?.map (·.1) = some cv₀ ∧
    ConLeche.annotateCore μ env F 0 cv₀.type = .ok a₀.cvTa.type

/-- A leaf of the head is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN_head : ∀ (args : List Expr) (f : Expr) (l : Nat × Expr),
    l ∈ f.fvarLeaves → l ∈ (Expr.mkAppN f args).fvarLeaves
  | [], _, _, hl => hl
  | a :: args, f, l, hl => by
    show l ∈ (Expr.mkAppN (.app f a) args).fvarLeaves
    refine mem_fvarLeaves_mkAppN_head args (.app f a) l ?_
    simp only [Expr.fvarLeaves, List.mem_append]
    exact Or.inl hl

/-- A leaf of a spine argument is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN_arg :
    ∀ (args : List Expr) (f : Expr) {a : Expr}, a ∈ args → ∀ l ∈ a.fvarLeaves,
      l ∈ (Expr.mkAppN f args).fvarLeaves
  | [], _, _, ha, _, _ => nomatch ha
  | a₀ :: args, f, a, ha, l, hl => by
    show l ∈ (Expr.mkAppN (.app f a₀) args).fvarLeaves
    rcases List.mem_cons.mp ha with rfl | ha
    · refine mem_fvarLeaves_mkAppN_head args (.app f a) l ?_
      simp only [Expr.fvarLeaves, List.mem_append]
      exact Or.inr hl
    · exact mem_fvarLeaves_mkAppN_arg args (.app f a₀) ha l hl

/-- Two positions of a nodup list holding the same element coincide. -/
theorem nodup_getElem?_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {x : α}
    (hi : l[i]? = some x) (hj : l[j]? = some x) : i = j := by
  obtain ⟨hil, hix⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hjx⟩ := List.getElem?_eq_some_iff.mp hj
  have hpw := List.pairwise_iff_getElem.mp h
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd (hix.trans hjx.symm) (hpw i j hil hjl hlt)
  · exact heq
  · exact absurd (hjx.trans hix.symm) (hpw j i hjl hil hgt)

set_option maxHeartbeats 1600000 in
/-- **`CopyTypesAsMinted`, derived from the run**: for every returned
pair, the annotation equation is the re-mint's at the stored first
former's openers (`FirstFormerStoredAsAnnotated` identifies them with
the re-mint's), and the copy's stored former opened there is the
container's at the annotated components — through the re-mint's type
ledger (`remintCopyTypes_type`, the fold collapsing to the one naming
pin by the block's name discipline), the arm firing
(`remintOne_fires`, its four conditions from the ledger and
`ContainersStored`), the auxiliary install storing the minted type
(`nestedCopyFormerType_eq`, the minted name's reserved prefix), the
stored former being the checked one (`auxFormers_stored`), and the
bvar-form round trip (`openPisAtFvars_closeTelescope_strip`). -/
theorem copyTypesAsMinted_of_facts {F : Nat} {env envAux : Env}
    {p : NestedParts} {st₀ st : ElimState} {b : MutualBlock} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms : List ConstantVal}
    {pinsA : List (ConLeche.NestedPin × Expr)} {a₀ : AuxStored} {fvsA : List Expr × Expr}
    (helim : ConLeche.elimNested env p.nP p.lps
      (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
        (⟨cv.name, cv.type,
          (p.ctors.filter (fun (c : MutualCtor) => c.member == mIdx)).map
            fun (c : MutualCtor) => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType)) = .ok st₀)
    (hremint : ConLeche.nestedRemint (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p st₀
      = .ok (st, pinsA))
    (hfresh : ConLeche.copiesFresh env p.k st = true)
    (hb : ConLeche.auxBlock p st = some b)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (ha₀ : (stored.take p.k).head? = some a₀)
    (hfv : ConLeche.openPisAtFvars p.nP a₀.cvTa.type 0 = some fvsA)
    (hpc : ConLeche.pinsClosed p.nP st.pins = true)
    (hrm : ConLeche.restoreRecTys (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms)
    (hcs : ContainersStored env envAux) (hT₀ : FirstFormerStoredAsAnnotated μ F env p a₀) :
    CopyTypesAsMinted μ F env envAux p b fvsA.1 pinsA := by
  -- the re-mint's chain, and the stored first former as its annotation
  obtain ⟨hpins, -, hlenT, -, cv₀, t₀A, fvsA₀, r₁, pbsA, r₂, hcv₀, ht₀A, hop₀, hstrip₀,
    hremintC⟩ := ConLeche.nestedRemint_inv hremint
  obtain ⟨-, -, hlenPA, hpinsA⟩ := ConLeche.remintCopyTypes_inv hremintC
  obtain ⟨cv₀', hcv₀', hann₀⟩ := hT₀
  rw [hcv₀] at hcv₀'
  obtain rfl := Option.some.inj hcv₀'
  have ht₀eq : a₀.cvTa.type = t₀A := Except.ok.inj (hann₀.symm.trans ht₀A)
  have hfvsA : fvsA = (fvsA₀, r₁) := by
    rw [ht₀eq, hop₀] at hfv
    exact (Option.some.inj hfv).symm
  -- the stored formers are the checked ones
  have hrun : DeclMutualCoreRun μ F env b none true envAux := declMutualCoreRun_of hcore
  have hfacts := nestedRecNameFacts helim hremint hfresh hb hcore hstored hrm
  obtain ⟨fms, hformers, hkF, hposF, hstoredF⟩ :=
    auxFormers_stored hrun (fun t ht => (hfacts t ht).1)
  obtain ⟨hNodup, -, -, -, -⟩ := ConLeche.checkMutualCore_inv hcore
  -- the block's shape
  have hk : b.k = st.types.length := ConLeche.auxBlock_k hb
  have hlenSt : st.types.length = p.k + st.pins.length := by
    have := ConLeche.elimNested_length helim
    rw [nestedTypes0_length] at this
    rw [hlenT, hpins]; exact this
  obtain ⟨-, -, -, -, -, hbformers, -⟩ := ConLeche.auxBlock_inv hb
  -- the names of the elimination's entries are the block's member names, nodup
  have hmemNames : ∀ (i : Nat) (t : AuxType), st₀.types[i]? = some t →
      b.memberNames[i]? = some t.name := by
    intro i t ht
    have h1 := ConLeche.nestedRemint_name hremint i
    rw [ht] at h1
    obtain ⟨tS, htS, hnS⟩ : ∃ tS, st.types[i]? = some tS ∧ tS.name = t.name := by
      cases htS : st.types[i]? with
      | none => rw [htS] at h1; exact nomatch h1
      | some tS => rw [htS] at h1; exact ⟨tS, rfl, Option.some.inj h1⟩
    obtain ⟨nIdx, -, hf⟩ := hbformers i tS htS
    unfold MutualBlock.memberNames
    rw [List.getElem?_map, hf, hnS]
    rfl
  have hndM : b.memberNames.Nodup := by
    have h0 := hNodup
    unfold ConLeche.MutualBlock.blockNames at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  -- the stored first former is the checked one, closed
  have hkpos : 0 < p.k := by
    cases hh : p.formers with
    | nil => rw [hh] at hcv₀; exact nomatch hcv₀
    | cons _ _ => show 0 < p.formers.length; rw [hh]; simp
  have hk0 : 0 < b.k := by rw [hk, hlenSt]; omega
  obtain ⟨hstoredLen, hstoredAt⟩ := ConLeche.auxStoredAll_inv hstored
  have ha₀' : stored[0]? = some a₀ := by
    rw [List.head?_eq_getElem?, List.getElem?_take_of_lt hkpos] at ha₀
    exact ha₀
  rw [hstoredAt 0 hk0] at ha₀'
  obtain ⟨cv₀₂, nIdx₀, capsA₀, hform₀, hfA₀⟩ := ConLeche.auxStored?_inv ha₀'
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, fms[0]? = some f₀ :=
    ⟨_, List.getElem?_eq_getElem (by rw [hkF]; exact hk0)⟩
  obtain ⟨cv₀₃, bs₀, hl₀, hff₀, -⟩ := hposF 0 f₀ hf₀
  rw [hform₀] at hl₀
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl₀)
  have hfind₀ := hstoredF f₀ (List.mem_of_getElem? hf₀)
  rw [hff₀.name, hfA₀] at hfind₀
  obtain ⟨ha₀eq, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfind₀)
  have hnf₀ : t₀A.hasFvar = false := by rw [← ht₀eq, ha₀eq]; exact hff₀.noFvar
  have hb₀ : t₀A.looseBVarsBounded 0 = true := by rw [← ht₀eq, ha₀eq]; exact hff₀.bounded
  -- the openers' facts
  have hlenF₀ : fvsA₀.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hop₀
  obtain ⟨bs₀S, body₀S, -, -, hshape₀, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis p.nP hop₀
  have hvar₀ : ∀ (i : Nat) (x : Expr), fvsA₀[i]? = some x → ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    have hi : i < p.nP := by rw [← hlenF₀]; exact (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨ty, hty⟩ := hshape₀ i hi
    rw [hx] at hty
    exact ⟨ty, by rw [Nat.zero_add] at hty; exact Option.some.inj hty⟩
  obtain ⟨hwsF₀, -⟩ := ConLeche.openPisAtFvars_WScoped p.nP t₀A 0 hop₀
    (Expr.WScoped.of_not_hasFvar hnf₀)
  obtain ⟨-, hbF₀⟩ := ConLeche.Verify.openPisAtFvars_bounded p.nP hop₀ hb₀
  have hleavesF₀ := ConLeche.Verify.openPisAtFvars_leaves p.nP hop₀
  have hvarFull : ∀ (i : Nat) (x : Expr), fvsA₀[i]? = some x →
      (∃ ty, x = Expr.fvar i ty) ∧ Expr.WScoped i (Expr.fvarTypeD x) ∧
      (Expr.fvarTypeD x).looseBVarsBounded 0 = true ∧
      ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsA₀ := by
    intro i x hx
    obtain ⟨ty, rfl⟩ := hvar₀ i x hx
    have hmem : Expr.fvar i ty ∈ fvsA₀ := List.mem_of_getElem? hx
    have hw := hwsF₀ _ hmem
    simp only [Expr.WScoped] at hw
    refine ⟨⟨ty, rfl⟩, hw.2, hbF₀ _ hmem, fun l hl => ?_⟩
    have hl₂ : l ∈ (Expr.fvar i ty).fvarLeaves := by
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
    rcases hleavesF₀ l (Or.inr ⟨_, hmem, hl₂⟩) with hl' | hl'
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf₀] at hl'; exact nomatch hl'
    · exact hl'
  -- the per-pin claim
  intro j q pinA hqA
  obtain ⟨hq₀, hannP⟩ := hpinsA j q pinA hqA
  refine ⟨by rw [hfvsA]; exact hannP, ?_⟩
  intro Jn lvls argsA hpinAeq cv nIdx hform cvT caps hfT cvTJ capsJ hfJ
  -- the ledger at `j`
  have hj₀ : j < st₀.pins.length := (List.getElem?_eq_some_iff.mp hq₀).1
  obtain ⟨t₀, params, body, pbs, body₀, -, -, -, I, ci, i, j₀, J, lvls', Ds, q', copy,
    st₁, st₂, cs', hci, hJ, hjE, hgrp, hq', hqc, hqp, hmk, hDs, hpbs, hDsLen, hty₀, -, -, -,
    hpre⟩ := ConLeche.elimNested_copy helim hj₀
  rw [hq₀] at hq'
  obtain rfl := Option.some.inj hq'
  rw [nestedTypes0_length] at hty₀
  -- the annotated pin is a spine at the container's head
  have hclosed := ConLeche.pinsClosed_inv hpc q (by rw [hpins]; exact List.mem_of_getElem? hq₀)
  rw [hqp] at hclosed hannP
  have hconst : Expr.instantiateList ((Expr.const J.name lvls').abstractRange 0 p.nP 0)
      fvsA₀.reverse = .const J.name lvls' := by
    rw [show (Expr.const J.name lvls').abstractRange 0 p.nP 0 = .const J.name lvls' from rfl,
      Expr.instantiateList]
  have hspine : Expr.instantiateList
      (Expr.abstractRange (Expr.mkAppN (.const J.name lvls') Ds) 0 p.nP 0) fvsA₀.reverse
      = Expr.mkAppN (.const J.name lvls')
        (Ds.map fun D => Expr.instantiateList (D.abstractRange 0 p.nP 0) fvsA₀.reverse) := by
    rw [ConLeche.abstractRange_mkAppN, ConLeche.instantiateList_mkAppN, List.map_map, hconst]
    rfl
  obtain ⟨hws, hbP, hleaf⟩ := ConLeche.instantiateList_openers_scoped hlenF₀ hclosed.1 hclosed.2
    hvarFull
  rw [hspine] at hannP hws hbP hleaf
  obtain ⟨f', args', hlenA, hpinA', F', hf'⟩ := ConLeche.annotateCore_mkAppN_inv hannP
  obtain rfl := ConLeche.annotateCore_const_inv hf'
  -- identify the given decomposition with the annotated spine
  have hfn : pinA.getAppFn = .const Jn lvls := by rw [hpinAeq, Expr.getAppFn_mkAppN]; rfl
  have hfn' : pinA.getAppFn = .const J.name lvls' := by rw [hpinA', Expr.getAppFn_mkAppN]; rfl
  obtain ⟨rfl, rfl⟩ := Expr.const.inj (hfn.symm.trans hfn')
  have hargs : pinA.getAppArgs = argsA := by
    rw [hpinAeq, Expr.getAppArgs_mkAppN]; rfl
  have hargs' : argsA = args' := by
    have := hargs
    rw [hpinA', Expr.getAppArgs_mkAppN] at this
    exact this.symm
  subst hargs'
  subst hpinA'
  have hlenArgs : argsA.length = ci.nP := by rw [hlenA, List.length_map, hDsLen]
  -- the annotated pin's guards
  have hwsE : Expr.WScoped p.nP (Expr.mkAppN (.const J.name lvls) argsA) :=
    ConLeche.annotateCore_WScoped F _ hannP hws
  have hbE : (Expr.mkAppN (.const J.name lvls) argsA).looseBVarsBounded 0 = true :=
    ConLeche.annotateCore_looseBVars F _ hannP hbP
  have hleafE : ∀ l ∈ (Expr.mkAppN (.const J.name lvls) argsA).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsA₀ := by
    intro l hl
    exact hleaf l (ConLeche.annotateCore_leaves_sub F _ hannP hws hbP l hl)
  have hargsB : ∀ a ∈ argsA, a.looseBVarsBounded 0 = true := by
    intro a ha
    exact (ConLeche.looseBVarsBounded_mkAppN_args hbE).2 a ha
  -- the container's stored records
  obtain ⟨hJne, ⟨ciJ, J', hciJ, hfind, hJ'ty, hJ'lps⟩, ⟨cvTJ', capsJ', hfJ', hJty, hJlps⟩, hJnf,
    hJb, nIdxJ, bsJ, uJ, hstripJ⟩ := hcs I ci hci i J hJ
  rw [hfJ'] at hfJ
  obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfJ)
  -- the instantiation at the annotated components succeeds
  obtain ⟨bsL, hbsL⟩ := ConLeche.stripPis_sort_instantiateLevelParams J.lps lvls (ci.nP + nIdxJ)
    hstripJ
  rw [← hlenArgs] at hbsL
  obtain ⟨tyI, bsI, htyI, -⟩ := ConLeche.stripPis_sort_instPis argsA hbsL
  -- the arm fires at this pin, and at no other pin on this entry
  have hnameC : copy.name = q.aux := ConLeche.mkCopy_name hmk
  have hlvls : lvls.length = J.lps.length := (ConLeche.mkCopy_inv hmk).1
  have hfires : ConLeche.remintOne env pbsA q (Expr.mkAppN (.const J.name lvls) argsA)
      { copy with ctors := cs' }
      = { { copy with ctors := cs' } with type := closeTelescope pbsA 0 tyI } :=
    ConLeche.remintOne_fires hfn (by rw [hqc]; exact hciJ) (by rw [hqc]; exact hfind)
      (by rw [hJ'lps]; exact hlvls) (by rw [hargs, hJ'ty, hJ'lps]; exact htyI) hnameC
  have hothers : ∀ (j' : Nat) (qp' : ConLeche.NestedPin × Expr), pinsA[j']? = some qp' →
      j' ≠ j → qp'.1.aux ≠ ({ copy with ctors := cs' } : AuxType).name := by
    intro j' qp' hj' hne
    obtain ⟨hq₀', -⟩ := hpinsA j' qp'.1 qp'.2 hj'
    have hj₀' : j' < st₀.pins.length := (List.getElem?_eq_some_iff.mp hq₀').1
    obtain ⟨t₀₂, params₂, body₂, pbs₂, body₀₂, -, -, -, I₂, ci₂, i₂, j₀₂, J₂, lvls₂, Ds₂, q₂,
      copy₂, st₁₂, st₂₂, cs₂, -, -, -, -, hq₂, -, -, hmk₂, -, -, -, hty₂, -, -, -, -⟩ :=
      ConLeche.elimNested_copy helim hj₀'
    rw [hq₀'] at hq₂
    obtain rfl := Option.some.inj hq₂
    rw [nestedTypes0_length] at hty₂
    have hn₂ := hmemNames _ _ hty₂
    have hn₁ := hmemNames _ _ hty₀
    show qp'.1.aux ≠ copy.name
    rw [← ConLeche.mkCopy_name hmk₂]
    intro heq
    have hne' : p.k + j' ≠ p.k + j := fun hh => hne (Nat.add_left_cancel hh)
    rw [heq] at hn₂
    exact hne' (nodup_getElem?_inj hndM hn₂ hn₁)
  have hfold := ConLeche.remintCopyTypes_type hremintC (p.k + j) _ hty₀
  rw [ConLeche.foldl_remintOne_single env pbsA pinsA j (q, Expr.mkAppN (.const J.name lvls) argsA)
    _ hqA hothers, hfires] at hfold
  -- the auxiliary install stores it: the copy's stored former IS this type
  have hprefix : Name.hasPrefixOf ConLeche.nestedPrefixName
      ({ { copy with ctors := cs' } with type := closeTelescope pbsA 0 tyI } : AuxType).name
        = true := by
    show Name.hasPrefixOf ConLeche.nestedPrefixName copy.name = true
    rw [hnameC]; exact hpre hJne
  obtain ⟨env₁, fms', f, hformers', -, hf, hfty⟩ :=
    ConLeche.nestedCopyFormerType_eq hb hcore (p.k + j) _ hfold hprefix
  rw [hformers] at hformers'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hformers')
  obtain ⟨cv', bs, hl, hff, -⟩ := hposF (p.k + j) f hf
  rw [hform] at hl
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl)
  have hfindT := hstoredF f (List.mem_of_getElem? hf)
  rw [hff.name, hfT] at hfindT
  obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfindT)
  have hcvT : f.cvTa.type = closeTelescope pbsA 0 tyI := hfty
  -- the round trip: the closed type re-opens to the openers and `tyI`
  obtain ⟨hbsNF, -⟩ := ConLeche.stripPis_not_hasFvar p.nP hstrip₀ hnf₀
  obtain ⟨ds, hAt⟩ := instPisAt_of_instPis argsA htyI
  have hJbL : (J.type.instantiateLevelParams J.lps lvls).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hJb
  have hJnfL : (J.type.instantiateLevelParams J.lps lvls).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hJnf
  obtain ⟨-, htyIb⟩ := ConLeche.Verify.instPisAt_bounded argsA hAt hJbL hargsB
  have hcons : ∀ x ∈ fvsA₀, ∀ (idx : Nat) (ty : Expr), x = .fvar idx ty →
      Expr.fvarConsistent idx ty tyI := by
    intro x hx idx ty hxe
    subst hxe
    refine ConLeche.fvarConsistent_of_leaves tyI fun l hl hidx => ?_
    rcases ConLeche.Verify.instPisAt_leaves argsA hAt l (Or.inr hl) with hl' | ⟨a, ha, hl'⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hJnfL] at hl'; exact nomatch hl'
    · have hmem : Expr.fvar l.1 l.2 ∈ fvsA₀ :=
        hleafE l (mem_fvarLeaves_mkAppN_arg argsA _ ha l hl')
      rw [hidx] at hmem
      have h1 := ConLeche.openers_mem_eq hvar₀ hmem
      have h2 := ConLeche.openers_mem_eq hvar₀ hx
      rw [h1] at h2
      exact (Expr.fvar.inj (Option.some.inj h2)).2
  have hround := ConLeche.openPisAtFvars_closeTelescope_strip p.nP hstrip₀ hop₀
    (fun b' hb' => Expr.WScoped.of_not_hasFvar (hbsNF b' hb')) htyIb hcons
  refine ⟨tyI, ?_, ?_⟩
  · rw [hcvT, hfvsA]; exact hround
  · rw [← hJty, ← hJlps]; exact htyI

/-! ## Every copy of the scratch block, read off the run -/

/-- A member's name in the auxiliary block is its former's. -/
theorem memberNames_getD {b : MutualBlock} {t : Nat} {cv : ConstantVal} {nIdx : Nat}
    (h : b.formers[t]? = some (cv, nIdx)) : b.memberNames.getD t .anonymous = cv.name := by
  unfold MutualBlock.memberNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

/-- **`PinRead` and `CopyIdxRead` for EVERY copy of the scratch block,
from the run**, under the containers' representation at the scratch
environment and the two SYNTACTIC premises (`ContainersStored`,
`FirstFormerStoredAsAnnotated`) — `CopyTypesAsMinted` is DERIVED
(`copyTypesAsMinted_of_facts`): for pin `j` the copy member `p.k + j`
has its pin `J.{lvls} Ds` read at the block's parameter frame and its
index telescope the container's at the pin's readings. -/
theorem copyIdxRead_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ConLeche.ElimState) (b : MutualBlock) (envAux : Env) (a₀ : AuxStored),
      ConLeche.auxBlock p st = some b ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
      (ContainersAt env envAux mpAux.base2 →
        ContainersStored env envAux → FirstFormerStoredAsAnnotated μ F env p a₀ →
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
    pinsA, helim, hremint, -, hfresh, -, hb, hcore, hstored, ha₀, hfv, hpc, hpinsAux, -, hrm, -⟩ :=
    h
  obtain ⟨mpAux, d, hreps⟩ := nestedAuxModel hμ mp hE helim hremint hfresh hb hcore hstored hrm
  refine ⟨st, b, envAux, a₀, hb, mpAux, d, hreps, ?_⟩
  intro hcont hcs hT₀ j hj ψ
  have hminted : CopyTypesAsMinted μ F env envAux p b fvsA.1 pinsA :=
    copyTypesAsMinted_of_facts helim hremint hfresh hb hcore hstored ha₀ hfv hpc hrm hcs hT₀
  -- the re-mint: pins, names and lengths are the elimination's
  obtain ⟨hpins, -, hlenT, -, cv₀, t₀A, fvsA₀, r₁, pbsA, r₂, -, -, -, -, hremintC⟩ :=
    ConLeche.nestedRemint_inv hremint
  obtain ⟨-, -, hlenPA, hpinsA⟩ := ConLeche.remintCopyTypes_inv hremintC
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
    st₁, st₂, cs', hci, hJ, hjE, hgrp, hq, hqc, hqp, hmk, hDs, hpbs, hDsLen, hty, hrun, h₁, h₂, -⟩ :=
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
  -- the pin's annotated form (the re-mint's), its check and its scope
  have hqmem : q ∈ st.pins := List.mem_of_getElem? hq
  obtain ⟨⟨q', pinA⟩, hqA⟩ : ∃ qp, pinsA[j]? = some qp :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenPA, ← hpins]; exact hj)⟩
  obtain ⟨hq', -⟩ := hpinsA j q' pinA hqA
  rw [← hpins, hq] at hq'
  obtain rfl := Option.some.inj hq'
  obtain ⟨hpinAnn, halignA⟩ := hminted j q pinA hqA
  obtain ⟨ty, hpinInf⟩ := ConLeche.nestedPinsOk_inv hpinsAux (q, pinA) (List.mem_of_getElem? hqA)
  have hclosed := ConLeche.pinsClosed_inv hpc q hqmem
  -- the container's member at the scratch environment
  obtain ⟨cvTJ, capsJ, dJ, mmJ, hfJ, hJtype, hJlps, hciNP, hFDJ⟩ := hcont I ci hci i J hJ
  have hlvls : lvls.length = cvTJ.levelParams.length := by
    rw [← hJlps]; exact (ConLeche.mkCopy_inv hmk).1
  -- the alignment, at this copy
  have halign : ∀ argsA : List Expr,
      ConLeche.annotateCore μ
        ⟨(p.formers.map fun f => ConstantInfo.indInfo f.1 {}).reverse ++ env.consts⟩ F p.nP
        (Expr.instantiateList (Expr.abstractRange q.pin 0 p.nP 0) fvsA.1.reverse)
        = .ok (Expr.mkAppN (.const J.name lvls) argsA) →
      ∃ rest, ConLeche.openPisAtFvars p.nP cvT.type 0 = some (fvsA.1, rest) ∧
        Expr.instPis (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) argsA = some rest := by
    intro argsA hA
    rw [hpinAnn] at hA
    exact halignA J.name lvls argsA (Except.ok.inj hA) _ _ hform cvT capsT hfTc cvTJ capsJ hfJ
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
