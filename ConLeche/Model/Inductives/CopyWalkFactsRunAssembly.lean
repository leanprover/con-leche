module

public import ConLeche.Model.Inductives.CopyWalkFactsAssembly
public import ConLeche.Model.Inductives.CopyCtorWalkRun
import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedRestoreWalk
import ConLeche.Verify.Inductives.NestedLeaves
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedFields

public section

/-!
# The walk's facts AT THE RUN (task #279 M-D′ step (1), DESIGN §M.46)

`CopyWalkFactsRun.lean` derives `CopyCtorWalkFacts` — the syntactic
half of the constructor record — from the STORED data of one copy
constructor, under some thirty-five syntactic hypotheses;
`CopyWalkFactsAssembly.lean` discharges four of them (the container's
recursive fields' shape, the fields through K.17, the residual, the
group exclusion).  This module assembles the two at the RUN: at
`env₁ = consNestedFormers (stored.take p.k) env` and
`R = restoreTbl p st` every input is a fact the run already carries —
the pin's constructor walked and stored (`CopyCtorsStored`), K.17's
pair (`nestedCtorPairs_mem`), the table's well-formedness
(`restoreTbl_wf` off K.3's `pinsClosed`), the copies' freshness and the
block's name discipline — so `CopyWalkFacts` is a READ off the run and
`copyCtorsRead_of_run` loses its first premise.

Three facts stay NAMED (DESIGN §M.46), each stated once here:

* `NestedGroupExclusionOk env envAux p st` and `IndRepData.OrdNotRec`
  (K.23, the kernel lane's record and the container datum's side);
* the containers' level parameters are distinct (K.21);
* `PinsMentionMember` — the pins' components mention a block member
  (the ledger's conjunct: a pin exists because `replaceIfNested` found
  a member mention);
* `ResidContent` — the residual's W2 clause, which `copyResid_of_stored`
  proves from the walk's states and whose two inputs the run does not
  expose (DESIGN §M.46's finding).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState ContainerCtor AuxStored)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The named facts of this step -/

/-- **The pins' components mention a block member** (DESIGN §M.46, the
ledger's conjunct): a pin exists because `replaceIfNested` fired, and
it fires only where a container's PARAMETER argument mentions a type of
the growing list.  Not recorded: `MintStep`/`PinOriginAt` keep the
mint's data, not the occurrence check that caused it. -/
@[expose] def PinsMentionMember (d : IndRepData V) (st : ElimState) (k₀ : Nat) : Prop :=
  ∀ q ∈ st.pins, ∃ D ∈ q.pin.getAppArgs, ∃ t, t < k₀ ∧ D.mentionsConstE (d.memberName t) = true

/-- **The residual of a copy's constructor, against the container's at
the pin** (DESIGN §M.46): W2 — the walk fired at the top of the
constructor's body, so the stored residual is the copy at its own
parameter openers and the container's index arguments up to erasure.
`copyResid_of_stored` proves it of the walk's states; the run does not
relate those states' TYPE lists to the final one (only their pin
lists), so the clause is named here. -/
@[expose] def ResidContent (p : ConLeche.NestedParts) (st : ElimState) (d : IndRepData V)
    (cd : Nat → CopyData V) : Prop :=
  ∀ (j' : Nat), j' < st.pins.length → ∀ (q : NestedPin) (lvls : List Level) (Ds : List Expr),
    st.pins[j']? = some q → q.pin = Expr.mkAppN (.const q.container lvls) Ds →
    ∀ (Jc : Nat) (cAJ : ConstantVal × Nat), (cd j').dJ.ctorsA[Jc]? = some cAJ →
    ∀ cI : Expr,
      Expr.instPis (cAJ.1.type.instantiateLevelParams cAJ.1.levelParams lvls) Ds = some cI →
    ∀ (xFvsC : List Expr) (xrestC : Expr),
      ConLeche.openPisAtFvars cAJ.2 cI d.nP = some (xFvsC, xrestC) →
      ∃ (aux : Name) (idx idxC : List Expr),
        d.xrestF (auxOfsOf st p.k cd j' Jc)
          = Expr.mkAppN (.const aux (p.lps.map Level.param))
              (d.fvsPF (auxOfsOf st p.k cd j' Jc) ++ idx) ∧
        xrestC = Expr.mkAppN (.const ((cd j').dJ.memberName ((cd j').dJ.mems Jc)) lvls)
            (Ds ++ idxC) ∧
        idx.length = idxC.length ∧
        ∀ (k : Nat) (e eC : Expr), idx[k]? = some e → idxC[k]? = some eC → Expr.ErasedEq e eC

/-- **The containers' level parameters are distinct** (K.21): what a
container's own install checked (`FormerFront.lpsNodup`) and the
model's `IndRep` does not record. -/
@[expose] def ContainerLpsNodup (env : Env) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (caps : IndCaps), env.find? n = some (.indInfo cv caps) →
    cv.levelParams.Nodup


/-- **The container's instantiated constructor mentions no table name**
(DESIGN §M.46, item (ii)): the pin's constructor, instantiated at the
pin's components, mentions none of the restore table's names — the
copies, their constructors and their recursors.  The elimination's
mention invariant (`elimNested_mentionInv` at `ok n := (env.find? n).isSome
∨ n ∈ the block's own members`) is what proves it; it is not threaded
through the run. -/
@[expose] def ContainerCtorsNoAux (p : ConLeche.NestedParts) (st : ElimState)
    (cd : Nat → CopyData V) : Prop :=
  ∀ (j' : Nat), j' < st.pins.length → ∀ (q : NestedPin) (lvls : List Level) (Ds : List Expr),
    st.pins[j']? = some q → q.pin = Expr.mkAppN (.const q.container lvls) Ds →
    ∀ (Jc : Nat) (cAJ : ConstantVal × Nat), (cd j').dJ.ctorsA[Jc]? = some cAJ →
    ∀ cI : Expr,
      Expr.instPis (cAJ.1.type.instantiateLevelParams cAJ.1.levelParams lvls) Ds = some cI →
      ∀ n ∈ (ConLeche.restoreTbl p st).auxNames, cI.mentionsConstE n = false


/-! ## A recovered group holds its own name -/

omit [SetTheory V] in
/-- **`containerInfo?` recovers a group holding the name it was looked
up at** (the `names.contains I` guard, through the members' `mapM`). -/
theorem containerInfo?_self_mem {env : Env} {I : Name} {ci : ContainerInfo}
    (h : ConLeche.containerInfo? env I = some ci) :
    ∃ (i : Nat) (J : ContainerMember), ci.members[i]? = some J ∧ J.name = I := by
  unfold ConLeche.containerInfo? at h
  split at h
  · exact nomatch h
  simp only [ConLeche.bindOption_eq_some_iff] at h
  obtain ⟨cT, hfT, h⟩ := h
  split at h
  · next cvT caps =>
    simp only [ConLeche.bindOption_eq_some_iff] at h
    obtain ⟨cR, hfR, h⟩ := h
    split at h
    · next cvR mI rP rules =>
      split at h
      · next hle =>
        simp only [ConLeche.bindOption_eq_some_iff] at h
        obtain ⟨nP, hnP, h⟩ := h
        obtain ⟨pp, hstrip, h⟩ := h
        obtain ⟨bsR, recBody⟩ := pp
        simp only at h
        split at h
        · next hnames =>
          simp only [ConLeche.bindOption_eq_some_iff] at h
          obtain ⟨members, hmapM, h⟩ := h
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hnames
          have hIn : I ∈ ConLeche.containerMembersGo env nP (rP + 1) 0 recBody := by
            have := hnames.1
            simpa using this
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hIn
          obtain ⟨hlen, hall⟩ := optionMapM_getElem? hmapM
          obtain ⟨J, hJ, hf⟩ := hall i I hi
          refine ⟨i, J, hJ, ?_⟩
          simp only [ConLeche.bindOption_eq_some_iff] at hf
          obtain ⟨cC, hfC, hf⟩ := hf
          split at hf
          · next cvC capsC =>
            simp only [ConLeche.bindOption_eq_some_iff] at hf
            obtain ⟨cRc, hfRc, hf⟩ := hf
            split at hf
            · next cvRc mIc rPc rulesC =>
              split at hf
              · simp only [ConLeche.bindOption_eq_some_iff] at hf
                obtain ⟨ctors, hctors, hf⟩ := hf
                simp only [Option.some.injEq] at hf
                rw [← hf]
              · exact nomatch hf
            · exact nomatch hf
          · exact nomatch hf
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

omit [SetTheory V] in
/-- **A group the pins cover recovers itself at every member** (K.15's
`containerGroupOk`, at the run): the group's own name is a member
(`containerInfo?_self_mem`), the pins carry every member's group, and
`nestedContainersOk` checked the facts at every pin's container. -/
theorem containerGroupOk_of_pins {env : Env} {st : ElimState} {ci : ContainerInfo} {I : Name}
    {base : Nat} (hcont : ConLeche.nestedContainersOk env st.pins = true)
    (hci : ConLeche.containerInfo? env I = some ci)
    (hgrp : ∀ (i' : Nat) (J' : ContainerMember), ci.members[i']? = some J' →
      ∃ q', st.pins[base + i']? = some q' ∧ q'.container = J'.name) :
    ConLeche.containerGroupOk env ci = true := by
  obtain ⟨i, J, hJ, hn⟩ := containerInfo?_self_mem hci
  obtain ⟨q', hq', hq'c⟩ := hgrp i J hJ
  obtain ⟨-, hall⟩ := ConLeche.nestedContainersOk_inv' hcont
  obtain ⟨ci₀, hci₀, hok⟩ := hall q' (List.mem_of_getElem? hq')
  rw [hq'c, hn, hci] at hci₀
  obtain rfl := Option.some.inj hci₀
  exact hok

/-! ## The walk's facts, at the run -/

set_option maxHeartbeats 1600000 in
/-- **`CopyWalkFacts` is a READ off the run** (DESIGN §M.46): at
`env₁ = consNestedFormers (stored.take p.k) env` and
`R = restoreTbl p st`, every input of `copyCtorWalkFacts_of_stored` and
of the four pieces (`containerRecField_shape`, `copyFields_of_whnfOk`,
`copyResid_of_stored`, `groupExclusion_of_K23`) is a fact the run
carries — modulo the named ones this module states. -/
theorem copyWalkFacts_of_run {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {stored : List AuxStored}
    {fmsA ctorsA : List ConstantVal}
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hb : ConLeche.auxBlock p st = some b)
    (hlenSt : st.types.length = p.k + st.pins.length)
    (hcopies : ConLeche.copiesFresh env p.k st = true)
    (hcont : ConLeche.nestedContainersOk env st.pins = true)
    (hwf : EnvWF env)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstoredAll : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hpc : ConLeche.pinsClosed p.nP st.pins = true)
    (hK20 : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hK17 : ConLeche.nestedCtorsWhnfOk (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.nP
      (ConLeche.nestedCtorPairs b stored) = .ok ())
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (hparamsLen : params.length = p.nP)
    (hpo : PinsAtOpeners st params)
    (hhead : ∃ (t₀ : AuxType) (body body₀ : Expr), st.types[0]? = some t₀ ∧
      ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body) ∧
      t₀.type.stripPis p.nP = some (pbs, body₀) ∧ pbs.length = p.nP ∧ t₀.type.hasFvar = false)
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hpins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hK23 : NestedGroupExclusionOk env envAux p st)
    (hONR : ∀ j', j' < st.pins.length → IndRepData.OrdNotRec (cd j').dJ)
    (hlpsNodup : ContainerLpsNodup env)
    (hmention : PinsMentionMember d st p.k)
    (hnoAux : ContainerCtorsNoAux p st cd)
    (hresidC : ResidContent p st d cd) :
    CopyWalkFacts μ F (ConLeche.consNestedFormers (stored.take p.k) env) p st
      (ConLeche.restoreTbl p st) d cd := by
  intro j' hj' q lvls Ds hq hqp Jc cAJ hJc cI hcI
  -- the block's shape
  have hreps' := hreps
  obtain ⟨-, hkb, hkRb, hnPb, -, hviewAll, hnames, hall⟩ := hreps
  obtain ⟨t₀, bodyT, body₀, ht₀, hop₀, hst₀, hpbsLen, hnf₀⟩ := hhead
  have hdk : d.k = p.k + st.pins.length := by rw [hkb, ConLeche.auxBlock_k hb, hlenSt]
  have hnP : d.nP = p.nP := by rw [hnPb, (ConLeche.auxBlock_inv hb).1]
  -- the pin's run facts, at the levels and components the walk names
  obtain ⟨⟨pf, hbm, q₀, I, ci, J, lvls₀, Ds₀, cvTJ, capsJ, hq₀, hci, hJ, hJn, hmn, hlenM, hgrp,
      hqp₀, hgq, hfJ, hψ', hDsW, hsp, hcat, hcst, hlpsAll, hlvlsLen, hagLvl, hmemNames⟩, hgrpCd⟩ :=
    hpins j' hj'
  obtain rfl : q = q₀ := Option.some.inj (hq.symm.trans hq₀)
  obtain ⟨rfl, rfl⟩ : lvls = lvls₀ ∧ Ds = Ds₀ := by
    rw [hqp₀] at hqp
    have h1 := congrArg Expr.getAppFn hqp
    have h2 := congrArg Expr.getAppArgs hqp
    rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at h1
    rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at h2
    simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append, Expr.const.injEq] at h1 h2
    exact ⟨h1.2.symm, h2.symm⟩
  -- the container constructor's member, and the group-mate's pin
  obtain ⟨Jm, c, hJm, hcl, hnameC, htypeC, hnFC⟩ := hcat.fwd Jc cAJ hJc
  have hmemsJ : (cd j').dJ.mems Jc < (cd j').dJ.k := by
    rw [← hlenM]; exact (List.getElem?_eq_some_iff.mp hJm).1
  have hk0 : 0 < d.k := by have := pf.kA _ hmemsJ; omega
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, hsv₀, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  -- the group-mate's pin, and its own run facts
  obtain ⟨q₂, hq₂, hq₂c, hq₂p, hq₂b, hq₂s⟩ := hgrp _ Jm hJm
  have hj₂ : (cd j').base + (cd j').dJ.mems Jc < st.pins.length :=
    (List.getElem?_eq_some_iff.mp hq₂).1
  obtain ⟨⟨pf₂, hbm₂, q₂', I₂, ci₂, J₂, lvls₂, Ds₂, cvTJ₂, capsJ₂, hq₂', hci₂, hJ₂, hJ₂n, -, -, -,
    hqp₂, hg₂, -, -, -, -, -, hcst₂, -, -, -, -⟩, -⟩ := hpins _ hj₂
  obtain rfl : q₂ = q₂' := Option.some.inj (hq₂.symm.trans hq₂')
  obtain ⟨hbase₂, hmm₂⟩ := groupMate_base hq₂ hq₂b rfl hg₂ hbm₂
  rw [hmm₂] at hJ₂
  have hJ₂m : J₂ = Jm :=
    ConLeche.containerInfo?_member_eq hci₂ hci (List.mem_of_getElem? hJ₂) (List.mem_of_getElem? hJm)
      (by rw [hJ₂n, hq₂c])
  subst hJ₂m
  obtain ⟨-, hlv, hDsE⟩ := group_pin_eq hq₂ hq₂ hq₂p hqp₂
  rw [← hlv, ← hDsE] at hcst₂
  -- the copy's constructor, from the mint to the store
  obtain ⟨tyA, htyA, htyAn, hlenA, env₁', fms, f₀, ctorsA, sortss, hformers, henv₁, hf0, hctors,
    hlenCA, hallC⟩ := hcst₂
  obtain ⟨cI₀, cbody, body', pbs', rest, sta, stb, cA, hcI₀, hstrip', hinst, hwalkC, hsta, hstb,
    hpi, htyl, hbl, hcA, hnorm, hstores, hproj⟩ := hallC (posIn (cd j').dJ Jc) c hcl
  -- the stage's list is the datum's
  obtain ⟨env₁'', fms', f₀', ctorsA', sortss', hformers', hf0', hctors', hdA, hkinds, hmems⟩ := hchk
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hformers'.symm.trans hformers))
  obtain rfl := Option.some.inj (hf0'.symm.trans hf0)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hctors'.symm.trans hctors))
  have hget : d.ctorsA[auxOfsOf st p.k cd j' Jc]? = some cA := by
    show d.ctorsA[ConLeche.ctorBase st (p.k + ((cd j').base + (cd j').dJ.mems Jc))
      + posIn (cd j').dJ Jc]? = some cA
    rw [hdA]; exact hcA
  have hmemJa : d.mems (auxOfsOf st p.k cd j' Jc)
      = p.k + ((cd j').base + (cd j').dJ.mems Jc) := by
    show d.mems (ConLeche.ctorBase st (p.k + ((cd j').base + (cd j').dJ.mems Jc))
      + posIn (cd j').dJ Jc) = _
    rw [hmems, List.getD_eq_getElem?_getD, hbl]
    rfl
  -- the field count
  obtain ⟨-, -, hallCtors⟩ := ConLeche.checkMutualCtors_inv hctors
  obtain ⟨hnF', sorts, -, hrun⟩ := hallCtors _ _ cA hbl hcA
  simp only at hnF'
  have hnF : cA.2 = cAJ.2 := by rw [hnF', hnFC]
  -- the copy's constructor at the auxiliary datum
  have hDfacts := FixCtorFactsAt.congr_sort hsv₀ (hrep₀.ctors _ cA hget)
  have hD := hDfacts.2.2
  have hview := hviewAll (auxOfsOf st p.k cd j' Jc)
  have htgtLt : ∀ i, d.tgts (auxOfsOf st p.k cd j' Jc) i < d.k := by
    intro i
    have := hrep₀.tgtsRLt (auxOfsOf st p.k cd j' Jc) i
    rw [hview.2.1] at this
    exact this
  have hxLen : (d.xFvsF (auxOfsOf st p.k cd j' Jc)).length = cA.2 := hD.xLen
  -- the copy's ORDINARY fields resolve before the block (`mutualFieldsOk`)
  obtain ⟨kinds, -, hfo, hksF⟩ := hkinds
  obtain ⟨-, hfoJ⟩ := mutualFieldsOk_inv hfo
  obtain ⟨ks, hksGet, hksLen, hopened⟩ := hfoJ _ cA (by rw [← hdA]; exact hget)
  obtain ⟨fvsP', crest', xFvs', xrest', hop1', hop2', hMO⟩ := mutualOpened_of hopened
  obtain ⟨crest, hop1, hop2⟩ := hD.opens
  rw [← hnPb] at hop1' hop2'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj (hop1'.symm.trans hop1))
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop2'.symm.trans hop2))
  have hksEq : kinds.getD (auxOfsOf st p.k cd j' Jc) [] = ks := by
    rw [List.getD_eq_getElem?_getD, hksGet]; rfl
  have hks : ∀ i, i < cA.2 → (d.ksF (auxOfsOf st p.k cd j' Jc)).getD i .ordinary = kindAt ks i := by
    intro i hi
    have hiks : i < ks.length := by rw [hksLen]; exact hi
    rw [hksF _, hksEq, kindsOf_getD hiks]
  -- the block's members are the state's types, by name
  have hmemberTy : ∀ (t : Nat) (ty : AuxType), st.types[t]? = some ty → t < d.k →
      d.memberName t = ty.name :=
    fun t ty hty ht => memberName_eq_type hb hnames hty (by rw [← hkb]; exact ht)
  have hfreshCopies := ConLeche.copiesFresh_inv hcopies
  have hdropMem : ∀ t, p.k ≤ t → t < d.k → ∃ ty, st.types[t]? = some ty ∧
      ty ∈ st.types.drop p.k := by
    intro t hkt ht
    obtain ⟨ty, hty⟩ : ∃ ty, st.types[t]? = some ty :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨ty, hty, List.mem_of_getElem? (i := t - p.k) ?_⟩
    rw [List.getElem?_drop, show p.k + (t - p.k) = t by omega]
    exact hty
  have hcopyNames : ∀ t, p.k ≤ t → t < d.k →
      d.memberName t ∈ (st.types.map (·.name)).drop p.k := by
    intro t hkt ht
    obtain ⟨ty, hty, hmem⟩ := hdropMem t hkt ht
    rw [hmemberTy t ty hty ht, ← List.map_drop]
    exact List.mem_map_of_mem hmem
  have hnodupM : ((List.range d.k).map d.memberName).Nodup := by
    have h0 := hrep₀.memberNodup
    have hkE : d.kReal = d.k := by rw [hkRb, hkb]
    rw [← hkE]
    exact h0
  -- the pins are structurally distinct (K.15)
  have hnodupP : (st.pins.map (·.pin)).Nodup := (ConLeche.nestedContainersOk_inv' hcont).1
  -- every pin's copy is the block member above it
  have hpinName : ∀ (jq : Nat) (qq : NestedPin), st.pins[jq]? = some qq →
      d.memberName (p.k + jq) = qq.aux := by
    intro jq qq hqq
    have hjq : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
    obtain ⟨⟨-, -, qq', I', ci', J', lvls', Ds', cvT', caps', hqq', -, -, -, -, -, -, -, -, -, -,
      -, -, -, hcstq, -⟩, -⟩ := hpins jq hjq
    obtain rfl : qq' = qq := Option.some.inj (hqq'.symm.trans hqq)
    obtain ⟨tyq, htyq, htyqn, -⟩ := hcstq
    rw [hmemberTy _ tyq htyq (by omega), htyqn]
  -- the container's constructor at its own datum
  obtain ⟨cvTm, cvRm, mIm, rPm, rulesm, hrepm⟩ := pf.repAll _ hmemsJ
  have hDJfacts := hrepm.ctors Jc cAJ hJc
  have hDJ := hDJfacts.2.2
  have htgtJLt : ∀ i, (cd j').dJ.tgts Jc i < (cd j').dJ.k := by
    intro i
    have h1 := hrepm.tgtsRLt Jc i
    rw [(pf.view Jc).2.1] at h1
    exact h1
  have hgroup : ∀ g, g < (cd j').dJ.k → ∃ qq, st.pins[(cd j').base + g]? = some qq ∧
      qq.pin = Expr.mkAppN (.const ((cd j').dJ.memberName g) lvls) Ds := by
    intro g hg
    obtain ⟨J', hJ'⟩ : ∃ J', ci.members[g]? = some J' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact hg)⟩
    obtain ⟨qq, hqq, -, hqqp, -, -⟩ := hgrp g J' hJ'
    exact ⟨qq, hqq, by rw [hqqp, (hmemNames g J' hJ').1]⟩
  -- the container member's level parameters
  have hfindM : envAux.find? ((cd j').dJ.memberName (cd j').mm) = some (.indInfo cvTJ capsJ) := by
    rw [hmn]; exact hfJ
  have hlpsJ : cvTJ.levelParams = cvTm.levelParams := hrepm.membersLps _ pf.mm cvTJ capsJ hfindM
  have hlpsC : cAJ.1.levelParams = cvTm.levelParams := hDJfacts.2.1
  have hJmLps : J₂.lps = cvTm.levelParams := by rw [hlpsAll _ J₂ hJm, hlpsJ]
  -- the walk, at the instantiation the mint performed
  have hcI' : Expr.instPis (cAJ.1.type.instantiateLevelParams cvTm.levelParams lvls) Ds
      = some cI := by rw [← hlpsC]; exact hcI
  obtain rfl : cI₀ = cI := by
    rw [htypeC, hlpsC, ← hJmLps] at hcI
    exact Option.some.inj (hcI₀.symm.trans hcI)
  have hDsLenE : Ds.length = (cd j').dJ.nP := by rw [DenoteMetaSpine.length hsp, pf.len]
  have hDsC : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true := fun a ha => (hDsW a ha).2
  -- K.21 at this container, and the container's stored constructor closed
  obtain ⟨⟨cvC, capsC, hfC, htyC, hlpsCC⟩, hctorsC⟩ :=
    ConLeche.containerInfo?_stored hci J₂ (List.mem_of_getElem? hJm)
  have hlpsJnodup : cvTm.levelParams.Nodup := by
    rw [← hJmLps, hlpsCC]; exact hlpsNodup _ cvC capsC hfC
  have hJnf : cAJ.1.type.hasFvar = false := by
    rw [htypeC]
    exact (ConLeche.containersClosed_of_wf hwf _ ci hci J₂
      (List.mem_of_getElem? hJm)).2 c (List.mem_of_getElem? hcl)
  have hlvlsLen' : lvls.length = cvTm.levelParams.length := by rw [hlvlsLen, hlpsJ]
  -- the container's constructor at the pin, stripped at the fields
  obtain ⟨fs, idx₀, hstripC⟩ := containerResid_at_pin mpAux hDJ hlpsJnodup hlvlsLen' hDsLenE hDsC
    hcI'
  obtain ⟨xFvsC, xrestC, hopen⟩ :=
    ConLeche.openPisAtFvars_of_stripPis' cAJ.2 d.nP hstripC
  refine ⟨xFvsC, xrestC, hopen, ?_⟩
  -- ## the formers' front door: every block name is fresh before the block
  obtain ⟨hchecksF, -⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨hlenFms, hposF⟩ := ConLeche.mutualFormerChecks_front hchecksF
  have hmemNameB : ∀ t, t < d.k → d.memberName t ∈ b.memberNames ∧ env.find? (d.memberName t) = none := by
    intro t ht
    obtain ⟨f, hft⟩ : ∃ f, fms'[t]? = some f :=
      ⟨_, List.getElem?_eq_getElem (show t < fms'.length by rw [hlenFms]; show t < b.k; exact hkb ▸ ht)⟩
    obtain ⟨cv, bs, hl, hff, -⟩ := hposF t f hft
    rw [hnames t (by rw [← hkb]; exact ht), memberNames_getD hl]
    exact ⟨List.mem_map_of_mem (List.mem_of_getElem? hl), hff.fresh⟩
  have hrealFresh : ∀ t, t < d.k → env.find? (d.memberName t) = none :=
    fun t ht => (hmemNameB t ht).2
  -- ## the block's names are distinct
  have hnodupB : b.blockNames.Nodup := ConLeche.nestedBlockNames_nodup hcore
  have hdisjMC : ∀ a ∈ b.memberNames, ∀ a' ∈ b.ctors.map (·.cv.name), a ≠ a' :=
    (List.nodup_append.mp (List.nodup_append.mp hnodupB).1).2.2
  have hdisjMR : ∀ a ∈ b.memberNames ++ b.ctors.map (·.cv.name),
      ∀ a' ∈ (List.range b.k).map b.recName, a ≠ a' := (List.nodup_append.mp hnodupB).2.2
  have hrecNameB : ∀ t, t < d.k →
      (d.memberName t).str "rec" ∈ (List.range b.k).map b.recName := by
    intro t ht
    obtain ⟨f, hft⟩ : ∃ f, fms'[t]? = some f :=
      ⟨_, List.getElem?_eq_getElem (show t < fms'.length by rw [hlenFms]; show t < b.k; exact hkb ▸ ht)⟩
    obtain ⟨cv, bs, hl, hff, -⟩ := hposF t f hft
    refine List.mem_map.mpr ⟨t, List.mem_range.mpr (by rw [← hkb]; exact ht), ?_⟩
    show (b.formers.getD t default).1.name.str "rec" = _
    rw [hnames t (by rw [← hkb]; exact ht), memberNames_getD hl, List.getD_eq_getElem?_getD, hl]
    rfl
  -- ## every copy's constructor is a constructor of the block
  have hcopyCtorB : ∀ (t : Nat) (ty : AuxType), st.types[t]? = some ty → ∀ c' ∈ ty.ctors,
      c'.1 ∈ b.ctors.map (·.cv.name) := by
    intro t ty hty c' hc'
    obtain ⟨l, hl⟩ := List.getElem?_of_mem hc'
    exact List.mem_map_of_mem (List.mem_of_getElem? (ConLeche.auxBlock_ctor_getElem? hb hty hl))
  -- ## the restore table's names: fresh, and none a real member's
  have hauxFresh : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
      env.find? n = none ∧ ∀ t, t < p.k → d.memberName t ≠ n := by
    intro n hn
    simp only [ConLeche.restoreTbl] at hn
    have hpinAux : ∀ qq ∈ st.pins, ∃ jq, jq < st.pins.length ∧ st.pins[jq]? = some qq ∧
        d.memberName (p.k + jq) = qq.aux := by
      intro qq hqq
      obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hqq
      exact ⟨jq, (List.getElem?_eq_some_iff.mp hjq).1, hjq, hpinName jq qq hjq⟩
    rcases List.mem_append.mp hn with hn | hn
    · rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨qq, hqq, rfl⟩ := List.mem_map.mp hn
        obtain ⟨jq, hjqlt, hjq, hnm⟩ := hpinAux qq hqq
        refine ⟨by rw [← hnm]; exact hrealFresh _ (by omega), fun t ht hEq => ?_⟩
        have := memberName_inj hnodupM (by omega : t < d.k) (by omega : p.k + jq < d.k)
          (by rw [hEq, hnm])
        omega
      · obtain ⟨ty, hty, hc'⟩ := List.mem_flatMap.mp hn
        obtain ⟨c', hc'mem, rfl⟩ := List.mem_map.mp hc'
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hty
        rw [List.getElem?_drop] at hi
        refine ⟨(hfreshCopies ty (List.mem_of_getElem? (by
          rw [List.getElem?_drop]; exact hi))).2.2 c' hc'mem, fun t ht hEq => ?_⟩
        refine hdisjMC _ (hmemNameB t (by omega)).1 _ ?_ hEq
        exact hcopyCtorB _ ty hi c' hc'mem
    · obtain ⟨qq, hqq, rfl⟩ := List.mem_map.mp hn
      obtain ⟨jq, hjqlt, hjq, hnm⟩ := hpinAux qq hqq
      obtain ⟨ty, hty, hmem⟩ := hdropMem (p.k + jq) (by omega) (by omega)
      have htyn : ty.name = qq.aux := by rw [← hmemberTy _ ty hty (by omega), hnm]
      refine ⟨by rw [← htyn]; exact (hfreshCopies ty hmem).2.1, fun t ht hEq => ?_⟩
      refine hdisjMR _ (List.mem_append_left _ (hmemNameB t (by omega)).1) _ ?_ hEq
      rw [← hnm]
      exact hrecNameB _ (by omega)
  -- ## every pin's group recovers itself, and its components count
  have hpinArity : ∀ (jq : Nat) (qq : NestedPin), st.pins[jq]? = some qq →
      ∃ ciq : ContainerInfo, ConLeche.containerInfo? env qq.container = some ciq ∧
        qq.pin.getAppArgs.length = ciq.nP := by
    intro jq qq hqq
    have hjq : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
    obtain ⟨t₀e, paramse, bodye, pbse, body₀e, ht₀e, hope, hstripe, Ie, cie, ie, j₀e, Je, lvlse,
      Dse, qe, copye, st₁e, st₂e, cs'e, hcie, hJe, hjEe, hgrpe, hqe, hqce, hqpe, hqbe, hqse, hmke,
      hDse, hpbse, hDsLene, htye, helimCe, -, hst₂e, hpie, -⟩ := ConLeche.elimNested_copy helim hjq
    obtain rfl : qe = qq := Option.some.inj (hqe.symm.trans hqq)
    have hgrpOke : ConLeche.containerGroupOk env cie = true :=
      containerGroupOk_of_pins hcont hcie (fun i' J' hJ' => by
        obtain ⟨q', hq', hq'c, -, -, -⟩ := hgrpe i' J' hJ'
        exact ⟨q', hq', hq'c⟩)
    obtain ⟨ciq, hciq, hnPq, -⟩ :=
      ConLeche.containerGroupOk_inv hgrpOke Je (List.mem_of_getElem? hJe)
    refine ⟨ciq, by rw [hqce]; exact hciq, ?_⟩
    rw [hqpe, Expr.getAppArgs_mkAppN]
    simp only [Expr.getAppArgs, List.nil_append]
    rw [hnPq]
    exact hDsLene
  -- ## this pin's group recovers itself (K.15)
  have hgrpOkCi : ConLeche.containerGroupOk env ci = true :=
    containerGroupOk_of_pins hcont hci (fun i' J' hJ' => by
      obtain ⟨q', hq', hq'c, -, -, -⟩ := hgrp i' J' hJ'
      exact ⟨q', hq', hq'c⟩)
  have hciNP : ci.nP = (cd j').dJ.nP := by
    obtain ⟨ciq, hciq, hlenq⟩ := hpinArity j' q hq
    obtain ⟨ci₁, hci₁, hnP₁, -⟩ :=
      ConLeche.containerGroupOk_inv hgrpOkCi J (List.mem_of_getElem? hJ)
    rw [hJn] at hci₁
    have hcieq : ci₁ = ciq := Option.some.inj (hci₁.symm.trans hciq)
    rw [← hnP₁, hcieq, ← hlenq, hqp₀, Expr.getAppArgs_mkAppN]
    simp only [Expr.getAppArgs, List.nil_append]
    exact hDsLenE
  -- ## a pin on this group's member carries the group's components
  have hpinLen : ∀ qq ∈ st.pins, ∀ g, g < (cd j').dJ.k →
      qq.container = (cd j').dJ.memberName g → qq.pin.getAppArgs.length = (cd j').dJ.nP := by
    intro qq hqq g hg hcname
    obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hqq
    obtain ⟨ciq, hciq, hlenq⟩ := hpinArity jq qq hjq
    obtain ⟨J', hJ'⟩ : ∃ J', ci.members[g]? = some J' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact hg)⟩
    obtain ⟨ci₁, hci₁, hnP₁, -⟩ :=
      ConLeche.containerGroupOk_inv hgrpOkCi J' (List.mem_of_getElem? hJ')
    rw [← (hmemNames g J' hJ').1, ← hcname] at hci₁
    have hcieq : ci₁ = ciq := Option.some.inj (hci₁.symm.trans hciq)
    rw [hlenq, ← hcieq, hnP₁, hciNP]
  -- ## K.23's group data at the group-mate's pin
  obtain ⟨ci'', hci''₀, hnP'', hnames''⟩ :=
    ConLeche.containerGroupOk_inv hgrpOkCi J₂ (List.mem_of_getElem? hJm)
  have hci'' : ConLeche.containerInfo? env q₂.container = some ci'' := by
    rw [hq₂c]; exact hci''₀
  have hJ₂'' : J₂ ∈ ci''.members := by
    have hmn₂ : J₂.name ∈ ci''.members.map (·.name) := by
      rw [hnames'']; exact List.mem_map_of_mem (List.mem_of_getElem? hJm)
    obtain ⟨J₃, hJ₃, hJ₃n⟩ := List.mem_map.mp hmn₂
    obtain rfl : J₃ = J₂ :=
      ConLeche.containerInfo?_member_eq hci''₀ hci hJ₃ (List.mem_of_getElem? hJm) hJ₃n
    exact hJ₃
  have hmemNames'' : ∀ C, C ∈ ci''.members.map (·.name) →
      ∃ t, t < (cd j').dJ.k ∧ (cd j').dJ.memberName t = C := by
    intro C hC
    rw [hnames''] at hC
    obtain ⟨J₃, hJ₃, rfl⟩ := List.mem_map.mp hC
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hJ₃
    exact ⟨t, by rw [← hlenM]; exact (List.getElem?_eq_some_iff.mp ht).1, (hmemNames t J₃ ht).1⟩
  sorry

end ConLeche.Model
