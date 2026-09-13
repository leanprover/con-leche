module

public import ConLeche.Model.Inductives.CopyPins
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

end ConLeche.Model
