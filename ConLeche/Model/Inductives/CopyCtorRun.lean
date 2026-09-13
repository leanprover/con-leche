module

public import ConLeche.Model.Inductives.PsiRun

public section

/-!
# The constructor side of ψ, from the run (task #279 M-B′ step 3l, DESIGN §M.29)

`PsiRun.lean` closes ψ at the run level under three named premises,
one of them `CopyCtorsOfRun`: at every pin, `CopyCtorFacts` for the
container's constructors — the record `CopyCtorAsRead` (the copy's
constructor read through the container's, field by field) together
with the copy's own constructor facts in the auxiliary datum.  This
module derives everything in `CopyCtorFacts` EXCEPT the record from
the run, so that the premise narrows to the record alone
(`CopyCtorsRead`):

* **`auxOfsOf`** — the auxiliary datum's index of the copy of a
  container constructor: the copy of member `dJ.mems Jc`'s
  constructors starts at `ctorBase st (k₀ + base + dJ.mems Jc)`
  (`NestedCtors.lean`), and the constructor is the `posIn dJ Jc`-th of
  its member;
* **`copyCtorsOfRun_of_read`** — from the run's pin facts
  (`PinRunFacts`: the pin's group, the group-mates' pins with their
  group data, `ContainerCtorsAt`, `CopyCtorsStored`), the block's
  representations and `CtorsChecked`: the copy's constructor at that
  index IS the auxiliary datum's (`CtorsChecked` names the stage's
  list, `CopyCtorsStored` the entry), its field count the container
  constructor's, its `FixCtorFactsAt` the member's representation's
  (moved to the block's sort), its stored type closed (the front
  door), the parameter equivalence, the view identities, the targets
  and the member within the block;
* **`psiFold_typed_of_read`** — `psiFold_typed_of_run` restated with
  `CopyCtorsRead` in place of `CopyCtorsOfRun`.

The record itself — the identity arm of `nestedCopyCtorType_eq` read
field by field through the walk — is the next step; the
group-mate's identification goes through the ledger's group clause
(the group's pins carry the group's base, so the group-mate's `CopyData`
is at the same base) and `containerInfo?_member_eq` (a member is
determined by its name).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The sort transfer of a constructor's facts -/

/-- `FixCtorFactsAt` across two spellings of the sort: only the `Prop`
tests (`bits`, `srcProp`, `tssBits`) mention it, by value. -/
theorem FixCtorFactsAt.congr_sort {m : EnvModel V env} {env₀ : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {s s' : Level} (hs : ∀ φ : Name → Nat, s.eval φ = s'.eval φ)
    {isProp large : Bool} {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List ConLeche.RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {j : Nat} {cA : ConstantVal × Nat} {tgtOf : Nat → Name} {nIdxOf : Nat → Nat}
    (h : FixCtorFactsAt m env₀ T lps nP nIdx s isProp large idxF dsF esF srcsF ksF fvsPF xFvsF
      xrestF eissF tssF j cA tgtOf nIdxOf) :
    FixCtorFactsAt m env₀ T lps nP nIdx s' isProp large idxF dsF esF srcsF ksF fvsPF xFvsF
      xrestF eissF tssF j cA tgtOf nIdxOf := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  exact { h3 with
    toCtorDataI := { h3.toCtorDataI with
      bits := fun ψ dd hd => by rw [← hs ψ]; exact h3.bits ψ dd hd
      srcProp := fun hl ψ hz => by rw [← hs ψ] at hz; exact h3.srcProp hl ψ hz }
    tssBits := fun ψ i dd hd => by rw [← hs ψ]; exact h3.tssBits ψ i dd hd }

/-! ## The copies' constructor indices -/

/-- The auxiliary datum's index of the copy of container constructor
`Jc` at pin `j'`: the group-mate's copy (member `k₀ + base + dJ.mems
Jc` of the block) starts at `ctorBase`, and the constructor is the
`posIn`-th of its member. -/
@[expose] def auxOfsOf (st : ElimState) (k₀ : Nat) (cd : Nat → CopyData V) (j' Jc : Nat) : Nat :=
  ConLeche.ctorBase st (k₀ + ((cd j').base + (cd j').dJ.mems Jc)) + posIn (cd j').dJ Jc

/-- **The record premise**: at every pin, every container constructor's
copy reads through it (`CopyCtorAsRead`) at the index `auxOfsOf`. -/
@[expose] def CopyCtorsRead {μ : CheckMode} (mp : EnvModelM V μ env) (d : IndRepData V) (ψ : Name → Nat)
    (st : ElimState) (k₀ n : Nat) (cd : Nat → CopyData V) : Prop :=
  ∀ j', j' < n → ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ →
    d.CopyCtorAsRead mp.base2 (cd j').dJ ψ (cd j').ψ' (cd j').DsA k₀ (cd j').base
      (fun j'' => (cd j'').dJ.memberName (cd j'').mm) (fun j'' => (cd j'').ψ')
      (fun j'' => (cd j'').DsA) Jc (auxOfsOf st k₀ cd j' Jc) cAJ.2

omit [SetTheory V] in
/-- The group base and member of a group-mate's `CopyData`, off the
ledger's group clause: the group-mate's pin carries the group's base,
and `ElimState.grp` reads it back. -/
theorem groupMate_base {st : ElimState} {j₂ base t : Nat} {q₂ : NestedPin} {c₂ : CopyData V}
    (hq₂ : st.pins[j₂]? = some q₂) (hq₂b : q₂.grpBase = base) (hj₂ : j₂ = base + t)
    (hg : ElimState.grp st j₂ = (c₂.base, c₂.dJ.k)) (hbm : c₂.base + c₂.mm = j₂) :
    c₂.base = base ∧ c₂.mm = t := by
  unfold ElimState.grp at hg
  rw [hq₂] at hg
  have h1 : (q₂.grpBase, q₂.grpSize) = (c₂.base, c₂.dJ.k) := hg
  obtain ⟨h2, -⟩ := Prod.mk.inj h1
  refine ⟨by rw [← h2, hq₂b], ?_⟩
  rw [← h2, hq₂b] at hbm
  omega

set_option maxHeartbeats 800000 in
/-- **One container constructor's copy, from the run, given the record**:
with the block's representations (member `0`'s `IndRep` at its own
sort), the stage's constructor list as the datum's (`CtorsChecked`) and
every pin's run facts, the record at container constructor `Jc` of pin
`j'` gives `CopyCtorFacts` at the index `auxOfsOf`, at member `0`'s
level parameters — and the auxiliary datum's constructor there is the
group-mate copy's PROCESSED constructor by name. -/
theorem copyCtorFacts_of_read {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hpins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    {s₀ : Level} {cvT₀ cvR₀ : ConstantVal} {mI₀ rP₀ : Nat} {rules₀ : List RecRule}
    (hsv₀ : ∀ φ : Name → Nat, s₀.eval φ = d.resSort.eval φ)
    (hrep₀ : IndRep mpAux.base2 (d.memberName 0) cvT₀ cvR₀ mI₀ rP₀ rules₀
      { d with resSort := s₀ } 0)
    {j' : Nat} (hj' : j' < st.pins.length) {Jc : Nat} {cAJ : ConstantVal × Nat}
    (hJc : (cd j').dJ.ctorsA[Jc]? = some cAJ)
    (hrd : d.CopyCtorAsRead mpAux.base2 (cd j').dJ ψ (cd j').ψ' (cd j').DsA p.k (cd j').base
      (fun j'' => (cd j'').dJ.memberName (cd j'').mm) (fun j'' => (cd j'').ψ')
      (fun j'' => (cd j'').DsA) Jc (auxOfsOf st p.k cd j' Jc) cAJ.2) :
    ∃ cA, d.ctorsA[auxOfsOf st p.k cd j' Jc]? = some cA ∧
      CopyCtorFacts mpAux.base2 d (cd j').dJ ψ (cd j').ψ' (cd j').DsA p.k (cd j').base cd
        cvT₀.levelParams Jc (auxOfsOf st p.k cd j' Jc) cAJ cA ∧
      (cd j').dJ.mems Jc < (cd j').dJ.k ∧
      ∃ (tyA : AuxType) (c : Name × Expr × Nat),
        st.types[p.k + ((cd j').base + (cd j').dJ.mems Jc)]? = some tyA ∧ c ∈ tyA.ctors ∧
        cA.1.name = c.1 := by
  obtain ⟨-, -, -, -, -, hview, -, -⟩ := hreps
  obtain ⟨env₁', fms', f₀', ctorsA', sortss', hformers', hf0', hctors', hdA, -, hmems⟩ := hchk
  obtain ⟨pf, hbm, q, I, ci, J, lvls, Ds, cvTJ, capsJ, hq, hci, hJ, hJn, hmn, hlenM, hgrp, hqp, hg,
    hfJ, hψ', hsp, hcat, hcst⟩ := hpins j' hj'
  -- the constructor's member and its container member
  obtain ⟨Jm, c, hJm, hcl, hname, htype, hnF⟩ := hcat Jc cAJ hJc
  have ht : (cd j').dJ.mems Jc < (cd j').dJ.k := by
    rw [← hlenM]; exact (List.getElem?_eq_some_iff.mp hJm).1
  -- the group-mate's pin, and its own run facts
  obtain ⟨q₂, hq₂, hq₂c, hq₂p, hq₂b, hq₂s⟩ := hgrp _ Jm hJm
  have hj₂ : (cd j').base + (cd j').dJ.mems Jc < st.pins.length :=
    (List.getElem?_eq_some_iff.mp hq₂).1
  obtain ⟨pf₂, hbm₂, q₂', I₂, ci₂, J₂, lvls₂, Ds₂, cvTJ₂, capsJ₂, hq₂', hci₂, hJ₂, hJ₂n, -, -, -, -,
    hg₂, -, -, -, -, hcst₂⟩ := hpins _ hj₂
  obtain rfl : q₂' = q₂ := Option.some.inj (hq₂'.symm.trans hq₂)
  obtain ⟨hbase₂, hmm₂⟩ := groupMate_base hq₂ hq₂b rfl hg₂ hbm₂
  rw [hmm₂] at hJ₂
  -- the group-mate's member is `Jm`: one name, one member
  have hJ₂m : J₂ = Jm :=
    ConLeche.containerInfo?_member_eq hci₂ hci (List.mem_of_getElem? hJ₂) (List.mem_of_getElem? hJm)
      (by rw [hJ₂n, hq₂c])
  subst hJ₂m
  -- the copy's constructor, from the mint to the store
  obtain ⟨tyA, htyA, htyAn, hlenA, env₁, fms, f₀, ctorsA, sortss, hformers, henv₁, hf0, hctors,
    hlenCA, hallC⟩ := hcst₂
  obtain ⟨cI, cbody, body', pbs', rest, sta, stb, cA, hcI, hstrip', hinst, hwalk, hsta, hstb, -, htyl,
    hbl, hcA, hnorm, hstores, hproj⟩ := hallC (posIn (cd j').dJ Jc) c hcl
  -- the stage's list is the datum's
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hformers'.symm.trans hformers))
  obtain rfl := Option.some.inj (hf0'.symm.trans hf0)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hctors'.symm.trans hctors))
  have hget : d.ctorsA[auxOfsOf st p.k cd j' Jc]? = some cA := by
    show d.ctorsA[ConLeche.ctorBase st (p.k + ((cd j').base + (cd j').dJ.mems Jc)) + posIn (cd j').dJ Jc]?
      = some cA
    rw [hdA]; exact hcA
  have hmemJa : d.mems (auxOfsOf st p.k cd j' Jc) = p.k + ((cd j').base + (cd j').dJ.mems Jc) := by
    show d.mems (ConLeche.ctorBase st (p.k + ((cd j').base + (cd j').dJ.mems Jc)) + posIn (cd j').dJ Jc)
      = _
    rw [hmems, List.getD_eq_getElem?_getD, hbl]
    rfl
  have hmemLt : p.k + ((cd j').base + (cd j').dJ.mems Jc) < d.k := by
    have := pf.kA _ ht; omega
  -- the front door: the stored type is closed
  obtain ⟨-, -, hallCtors⟩ := ConLeche.checkMutualCtors_inv hctors
  obtain ⟨hnF', sorts, -, hrun⟩ := hallCtors _ _ cA hbl hcA
  obtain ⟨⟨ty', hff⟩, -, -⟩ := ConLeche.checkMutualCtor_front hrun
  simp only at hnF'
  -- the stored constructor is the processed one by name
  have hnameC : cA.1.name = Name.replacePrefix J₂.name q₂'.aux c.name := by
    rcases hstores with h | ⟨ty', h⟩ <;> (rw [h]; try rfl)
  refine ⟨cA, hget, ⟨by rw [hnF', hnF], hrd, ?_, hff.noFvar, hff.bounded,
    fun ρ' => hrep₀.paramsIff _ cA hget ψ ρ', hview _, fun i => hrep₀.tgtsRLt _ i,
    by rw [hmemJa]; exact hmemLt⟩, ht, tyA, _, htyA, List.mem_of_getElem? htyl, hnameC⟩
  exact FixCtorFactsAt.congr_sort hsv₀ (hrep₀.ctors _ cA hget)

/-- **The constructor side from the run, given the record**: at every
pin, at member `0`'s level parameters. -/
theorem copyCtorsOfRun_of_read {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hpins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hread : CopyCtorsRead mpAux d ψ st p.k st.pins.length cd) :
    ∃ lpsT : List Name, CopyCtorsOfRun mpAux d ψ p.k st.pins.length lpsT cd (auxOfsOf st p.k cd) := by
  have hreps' := hreps
  obtain ⟨-, hkb, -, -, -, -, -, hall⟩ := hreps
  by_cases hn : st.pins.length = 0
  · exact ⟨[], fun j' hj' => by omega⟩
  -- member 0's representation carries the block's facts
  have hk0 : 0 < d.k := by
    obtain ⟨pf, -⟩ := hpins 0 (by omega)
    have := pf.kA 0 (Nat.lt_of_lt_of_le (Nat.zero_lt_of_ne_zero (by
      intro h0; have := pf.mm; omega)) (Nat.le_refl _))
    omega
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, hsv₀, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  refine ⟨cvT₀.levelParams, fun j' hj' Jc cAJ hJc => ?_⟩
  obtain ⟨cA, hget, hf, -⟩ :=
    copyCtorFacts_of_read hreps' hchk hpins hsv₀ hrep₀ hj' hJc (hread j' hj' Jc cAJ hJc)
  exact ⟨cA, hget, hf⟩

/-! ## The bridge's mention clause, over the group -/

/-- **The copies' constructors are stored UNNORMALISED**: every stored
constructor of a copy has the PROCESSED constructor's type — the
identity arm of `nestedCopyCtorType_eq` at every copy.  A syntactic,
corpus-measurable premise (false at a λ-pin, where the positivity
normalisation `whnf`s a field; DESIGN §M.29). -/
@[expose] def CopiesUnnormalised (envAux : Env) (p : ConLeche.NestedParts) (st : ElimState) : Prop :=
  ∀ t ∈ st.types.drop p.k, ∀ c ∈ t.ctors, ∀ (cv : ConstantVal) (nP nF : Nat),
    envAux.find? c.1 = some (.ctorInfo cv nP nF) → cv.type = c.2.1

/-- **The bridge's mention clause, over the GROUP**: at every transport
(a field the copy's constructor sees as recursive into the target and
the container's as ordinary) SOME copy of the source's mint group has a
processed constructor mentioning the target copy's name — the copy of
the member whose constructor carries the transport.  (`CopyRef`'s
mention clause asks this of pin `j'`'s own copy; ψ at pin `j'` folds
through the whole group's constructors, so the relation the order must
respect is this group-wide one — DESIGN §M.29.) -/
@[expose] def BridgeMention (d : IndRepData V) (st : ElimState) (k₀ n : Nat) (cd : Nat → CopyData V)
    (auxOfs : Nat → Nat → Nat) : Prop :=
  ∀ j', j' < n → ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
    i ∈ ConLeche.recIdxOf (d.ksR (auxOfs j' Jc)) → i ∉ ConLeche.recIdxOf ((cd j').dJ.ksF Jc) →
    k₀ ≤ d.tgtsR (auxOfs j' Jc) i →
    ∀ t' : AuxType, st.types[d.tgtsR (auxOfs j' Jc) i]? = some t' →
      ∃ g, g < (cd j').dJ.k ∧ ∃ t : AuxType, st.types[k₀ + ((cd j').base + g)]? = some t ∧
        ∃ c ∈ t.ctors, (c.2.1).mentionsConst t'.name = true

omit [SetTheory V] in
/-- A member's name in the auxiliary block is its type's. -/
theorem memberName_eq_type {b : MutualBlock} {d : IndRepData V} {p : ConLeche.NestedParts}
    {st : ElimState} (hb : ConLeche.auxBlock p st = some b)
    (hnames : ∀ t, t < b.k → d.memberName t = b.memberNames.getD t .anonymous)
    {t : Nat} {ty : AuxType} (hty : st.types[t]? = some ty) (ht : t < b.k) :
    d.memberName t = ty.name := by
  obtain ⟨nIdx, hform, -⟩ := (ConLeche.auxBlock_former hb).2 t ty hty
  rw [hnames t ht, memberNames_getD hform]

set_option maxHeartbeats 800000 in
/-- **The mention clause, from the read**: the transport's constructor is
the group-mate copy's processed constructor (unnormalised), whose
opened field `i` has the target member's name at its head
(`FixOpened.recF`/`reflF`), and a mention in an opened telescope is a
mention in the closed constructor type. -/
theorem bridgeMention_of_read {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hb : ConLeche.auxBlock p st = some b)
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hpins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hread : CopyCtorsRead mpAux d ψ st p.k st.pins.length cd)
    (hunn : CopiesUnnormalised envAux p st) :
    BridgeMention d st p.k st.pins.length cd (auxOfsOf st p.k cd) := by
  have hreps' := hreps
  obtain ⟨-, hkb, -, -, -, -, hnames, hall⟩ := hreps
  intro j' hj' Jc cAJ hJc i hi hA hT _ t' ht'
  have hk0 : 0 < d.k := by
    obtain ⟨pf, -⟩ := hpins j' hj'
    have := pf.kA 0 (Nat.lt_of_lt_of_le (Nat.zero_lt_of_ne_zero (by
      intro h0; have := pf.mm; omega)) (Nat.le_refl _))
    omega
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, hsv₀, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  obtain ⟨cA, hget, hf, hg, tyA, c, htyA, hc, hnameC⟩ :=
    copyCtorFacts_of_read hreps' hchk hpins hsv₀ hrep₀ hj' hJc (hread j' hj' Jc cAJ hJc)
  refine ⟨(cd j').dJ.mems Jc, hg, tyA, htyA, c, hc, ?_⟩
  -- the stored constructor's type is the processed one
  obtain ⟨hfind, -, hdat⟩ := hf.ctor
  have htyEq : cA.1.type = c.2.1 :=
    hunn tyA (List.mem_of_getElem? (by rw [List.getElem?_drop]; exact htyA)) c hc cA.1 _ _
      (by rw [← hnameC]; exact hfind)
  rw [← htyEq]
  -- the target's name is the member's
  have hview := hf.view
  have htgtLt : d.tgtsR (auxOfsOf st p.k cd j' Jc) i < d.k := hf.tgts i
  have hmemT : d.memberName (d.tgts (auxOfsOf st p.k cd j' Jc) i) = t'.name := by
    rw [← hview.2.1]
    exact memberName_eq_type hb hnames ht' (by rw [← hkb]; exact htgtLt)
  -- the opened field's head is the target
  obtain ⟨crest, hop1, hop2⟩ := hdat.opens
  have hiF : i < cA.2 := by rw [hf.nF]; exact hi
  obtain ⟨x, hx⟩ : ∃ x, (d.xFvsF (auxOfsOf st p.k cd j' Jc))[i]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hdat.xLen]; exact hiF)⟩
  rw [hview.1] at hA
  obtain ⟨-, hk⟩ := mem_recIdxOf.mp hA
  have hxm : x.fvarTypeD.mentionsConst t'.name = true := by
    rcases hk with hk | hk
    · obtain ⟨hhead, -⟩ := hdat.opened.recF i x hx hk
      rw [← hmemT]
      exact ConLeche.Expr.mentionsConst_of_getAppFn _ _ hhead
    · obtain ⟨afvs, body, hopen, -, -, hhead, -⟩ := hdat.opened.reflF i x hx hk
      rw [← hmemT]
      exact ConLeche.openPisAtFvars_mentionsConst _ _ _ hopen
        (Or.inl (ConLeche.Expr.mentionsConst_of_getAppFn _ _ hhead))
  exact ConLeche.openPisAtFvars_mentionsConst _ _ _ hop1
    (Or.inl (ConLeche.openPisAtFvars_mentionsConst _ _ _ hop2
      (Or.inr ⟨x, List.mem_of_getElem? hx, hxm⟩)))

/-- **ψ at every pin, from the run, given the record** —
`psiFold_typed_of_run` with `CopyCtorsOfRun` replaced by the record
premise `CopyCtorsRead` (the rest of the constructor side is read),
at the indices `auxOfsOf`. -/
theorem psiFold_typed_of_read {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (order : List Nat),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
      st.types.length = p.k + st.pins.length ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧
        ∃ (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta)),
        (ContainersRep env envAux mpAux.base2 → ∀ ψ : Name → Nat,
          ∃ cd : Nat → CopyData V,
            (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) ∧
            (CopyCtorsRead mpAux d ψ st p.k st.pins.length cd →
              BridgeSyntax d st p.k st.pins.length cd (auxOfsOf st p.k cd) →
              ∀ (ρ₀ : Nat → V) (psA : List AnnotTerm), psA.length = d.nP →
                SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)) →
                ∀ (tbl₀ : Nat → AnnotTerm) (j' : Nat), j' < st.pins.length →
                  d.PsiP mpAux.base2 ψ p.k (consList (psA.map (interp V ρ₀)) ρ₀) cd j'
                    (ConLeche.orderFold (d.psiStep mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd)) order
                      tbl₀ j'))) := by
  obtain ⟨st, b, envAux, order, hb, hord, hlenSt, mpAux, d, hreps, hchk, params, pbs, hrest⟩ :=
    psiFold_typed_of_run hμ mp hE h
  refine ⟨st, b, envAux, order, hb, hord, hlenSt, mpAux, d, hreps, hchk, params, pbs, ?_⟩
  intro hcr ψ
  obtain ⟨cd, hpins, hfold⟩ := hrest hcr ψ
  refine ⟨cd, hpins, fun hread hsyn => ?_⟩
  obtain ⟨lpsT, hctors⟩ := copyCtorsOfRun_of_read hreps hchk hpins hread
  exact hfold lpsT _ hctors hsyn

end ConLeche.Model
