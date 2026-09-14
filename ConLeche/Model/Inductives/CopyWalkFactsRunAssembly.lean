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
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop1'.symm.trans hop1))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop2'.symm.trans hop2))
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
  obtain rfl : cI = cI₀ := by
    rw [htypeC, hlpsC, ← hJmLps] at hcI
    exact (Option.some.inj (hcI₀.symm.trans hcI)).symm
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
  -- ## the copies' names, and the table at the openers
  have hauxEq : st.pins.map (·.aux) = ((List.range d.k).map d.memberName).drop p.k := by
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_map, List.getElem?_drop, List.getElem?_map]
    by_cases hi : i < st.pins.length
    · obtain ⟨qq, hqq⟩ : ∃ qq, st.pins[i]? = some qq := ⟨_, List.getElem?_eq_getElem hi⟩
      rw [hqq, List.getElem?_range (by omega)]
      simp only [Option.map_some]
      rw [hpinName i qq hqq]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
      rfl
  have hauxNodup : (st.pins.map (·.aux)).Nodup := by
    rw [hauxEq]; exact hnodupM.sublist (List.drop_sublist _ _)
  have hcopyAux : ∀ T ∈ (st.types.map (·.name)).drop p.k,
      T ∈ (ConLeche.restoreTbl p st).auxNames := by
    intro T hT
    rw [← List.map_drop] at hT
    obtain ⟨ty, hty, rfl⟩ := List.mem_map.mp hT
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hty
    rw [List.getElem?_drop] at hi
    have hlt : i < st.pins.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega
    obtain ⟨qq, hqq⟩ : ∃ qq, st.pins[i]? = some qq := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hnq : ty.name = qq.aux := by
      rw [← hmemberTy (p.k + i) ty hi (by omega), hpinName i qq hqq]
    rw [hnq]
    show qq.aux ∈ st.pins.map (fun x => x.aux) ++ _ ++ _
    exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_map_of_mem (List.mem_of_getElem? hqq)))
  -- ## the group's members are stored, before the block and at `env₁`
  have hfreshExt : ConLeche.Semantics.FreshEtaExt env
      (ConLeche.consNestedFormers (stored.take p.k) env) :=
    ConLeche.Semantics.consNestedFormers_freshExt hK20
  have hstoredJ : ∀ g, g < (cd j').dJ.k →
      (∃ (cv : ConstantVal) (caps : IndCaps),
        (ConLeche.consNestedFormers (stored.take p.k) env).find? ((cd j').dJ.memberName g)
          = some (.indInfo cv caps)) ∧
      (env.find? ((cd j').dJ.memberName g)).isSome = true := by
    intro g hg
    obtain ⟨J', hJ'⟩ : ∃ J', ci.members[g]? = some J' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact hg)⟩
    obtain ⟨⟨cvC', capsC', hfC', -, -⟩, -⟩ :=
      ConLeche.containerInfo?_stored hci J' (List.mem_of_getElem? hJ')
    rw [(hmemNames g J' hJ').1]
    exact ⟨⟨cvC', capsC', hfreshExt.find?_some hfC'⟩, by rw [hfC']; rfl⟩
  -- ## the openers' shape, the leaves and the closedness of the pin's constructor
  obtain ⟨bs₀S, body₀S, -, -, hshape₀, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis p.nP hop₀
  have hshape : ∀ (i : Nat) (x : Expr), params[i]? = some x → ∃ ty, x = .fvar i ty := by
    intro i x hx
    have hi : i < p.nP := by rw [← hparamsLen]; exact (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨ty, hty⟩ := hshape₀ i hi
    rw [hx] at hty
    exact ⟨ty, by rw [Nat.zero_add] at hty; exact Option.some.inj hty⟩
  have hqL : Expr.LeavesIn params q.pin := hpo q (List.mem_of_getElem? hq)
  have hDsL : ∀ D ∈ Ds, Expr.LeavesIn params D := by
    intro D hD
    exact leavesIn_component (J := q.container) (lvls := lvls) (by rw [← hqp₀]; exact hqL) hD
  obtain ⟨cvc, nPc, nFc', hfc, hctyEq⟩ := hctorsC c (List.mem_of_getElem? hcl)
  have hcWF := hwf _ (List.mem_of_find?_eq_some hfc)
  have hcTyB : c.type.looseBVarsBounded 0 = true := by rw [hctyEq]; exact hcWF.2.2.2.1
  have hcIL : Expr.LeavesIn params cI :=
    Expr.LeavesIn.instPis hcI' (Expr.LeavesIn.instantiateLevelParams hJnf _ _) hDsL
  have hcIB : cI.looseBVarsBounded 0 = true := by
    refine ConLeche.instPis_looseBVarsBounded Ds hcI' ?_ hDsC
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams, htypeC]
    exact hcTyB
  have hDsMention : ∃ D ∈ Ds, ∃ t, t < p.k ∧ D.mentionsConstE (d.memberName t) = true := by
    obtain ⟨D, hD, hmt⟩ := hmention q (List.mem_of_getElem? hq)
    refine ⟨D, ?_, hmt⟩
    rw [hqp₀, Expr.getAppArgs_mkAppN] at hD
    simpa [Expr.getAppArgs] using hD
  -- ## the pins' shapes
  have hpinAll2 : ∀ (jq : Nat) (qq : NestedPin), st.pins[jq]? = some qq →
      ∃ (lvls' : List Level) (Ds' : List Expr),
        qq.pin = Expr.mkAppN (.const qq.container lvls') Ds' ∧
        (∀ a ∈ Ds', a.looseBVarsBounded 0 = true) := by
    intro jq qq hqq
    have hjq : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
    obtain ⟨⟨-, -, qq', I', ci', J', lvls', Ds', cvT', caps', hqq', -, -, -, -, -, -, hqpq, -,
      -, -, hDsWq, -, -, -, -, -, -, -⟩, -⟩ := hpins jq hjq
    obtain rfl : qq = qq' := Option.some.inj (hqq.symm.trans hqq')
    exact ⟨lvls', Ds', hqpq, fun a ha => (hDsWq a ha).2⟩
  have hpinShape : ∀ qq ∈ st.pins, ∃ (J' : Name) (lvls' : List Level) (Ds' : List Expr),
      qq.pin = Expr.mkAppN (.const J' lvls') Ds' ∧ qq.container = J' ∧
      Expr.LeavesIn params qq.pin ∧ qq.pin.looseBVarsBounded 0 = true := by
    intro qq hqq
    obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hqq
    obtain ⟨lvls', Ds', hsh, hDsB⟩ := hpinAll2 jq qq hjq
    exact ⟨qq.container, lvls', Ds', hsh, rfl, hpo qq hqq,
      by rw [hsh]; exact ConLeche.looseBVarsBounded_mkAppN rfl hDsB⟩
  -- ## the restore table
  have hRwf : (ConLeche.restoreTbl p st).WF :=
    ConLeche.restoreTbl_wf hpc (fun qq hqq => by
      obtain ⟨J', lvls', Ds', h1, -, -, -⟩ := hpinShape qq hqq
      exact ⟨J', lvls', Ds', h1⟩)
  have hRnP : (ConLeche.restoreTbl p st).nP = d.nP := by rw [hnP]; rfl
  have hrecNe : ∀ (qq : NestedPin), qq ∈ st.pins → ∀ q' ∈ st.pins, q'.aux.str "rec" ≠ qq.aux := by
    intro qq hqq q' hq' hEq
    obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hqq
    obtain ⟨jq', hjq'⟩ := List.getElem?_of_mem hq'
    have hlt : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hjq).1
    have hlt' : jq' < st.pins.length := (List.getElem?_eq_some_iff.mp hjq').1
    have hm : d.memberName (p.k + jq) ∈ b.memberNames ++ b.ctors.map (·.cv.name) :=
      List.mem_append_left _ (hmemNameB _ (by omega)).1
    have hr : (d.memberName (p.k + jq')).str "rec" ∈ (List.range b.k).map b.recName :=
      hrecNameB _ (by omega)
    refine hdisjMR _ hm _ hr ?_
    rw [hpinName jq qq hjq, hpinName jq' q' hjq']
    exact hEq.symm
  -- ## the table's entries at the two frames
  have hfvsPLen : (d.fvsPF (auxOfsOf st p.k cd j' Jc)).length = p.nP := by rw [hD.pLen, hnP]
  have hpF : ∀ z ∈ (ConLeche.restoreTbl p st).pins, z.2.hasFvar = false := by
    intro z hz
    simp only [ConLeche.restoreTbl] at hz
    obtain ⟨qq, hqq, rfl⟩ := List.mem_map.mp hz
    exact (ConLeche.pinsClosed_inv hpc qq hqq).1
  have hpB : ∀ z ∈ (ConLeche.restoreTbl p st).pins,
      z.2.looseBVarsBounded (ConLeche.restoreTbl p st).nP = true := by
    intro z hz
    simp only [ConLeche.restoreTbl] at hz
    obtain ⟨qq, hqq, rfl⟩ := List.mem_map.mp hz
    exact (ConLeche.pinsClosed_inv hpc qq hqq).2
  have hctorPinShape : ∀ z ∈ (ConLeche.restoreTbl p st).ctorPins,
      ∃ qq ∈ st.pins, z.2.1 = Expr.abstractRange qq.pin 0 p.nP 0 := by
    intro z hz
    simp only [ConLeche.restoreTbl] at hz
    obtain ⟨l, hl, hzl⟩ := List.mem_flatten.mp hz
    obtain ⟨⟨t, jt⟩, htj, rfl⟩ := List.mem_map.mp hl
    obtain ⟨-, hjlt, ht⟩ := List.mem_zipIdx htj
    cases hqq : st.pins[jt]? with
    | none => simp only [hqq] at hzl; exact nomatch hzl
    | some qq =>
      simp only [hqq] at hzl
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hzl
      exact ⟨qq, List.mem_of_getElem? hqq, rfl⟩
  have hcF : ∀ z ∈ (ConLeche.restoreTbl p st).ctorPins, z.2.1.hasFvar = false := by
    intro z hz
    obtain ⟨qq, hqq, hzE⟩ := hctorPinShape z hz
    rw [hzE]
    exact (ConLeche.pinsClosed_inv hpc qq hqq).1
  have hlookS : ∀ qq ∈ st.pins, ∃ pin',
      ((ConLeche.restoreTbl p st).instAt (d.fvsPF (auxOfsOf st p.k cd j' Jc))).pins.lookup qq.aux
        = some pin' ∧ Expr.ErasedEq pin' qq.pin ∧ pin'.looseBVarsBounded 0 = true := by
    intro qq hqq
    obtain ⟨-, -, -, -, -, -, hB⟩ := hpinShape qq hqq
    obtain ⟨pin', hlook, hE⟩ :=
      ConLeche.restoreTbl_instAt_lookup_erasedEq hauxNodup hfvsPLen hD.pIdx hqq hB
    exact ⟨pin', hlook, hE, (Expr.ErasedEq.looseBVarsBounded_iff hE 0).mpr hB⟩
  have hrecS : ∀ qq ∈ st.pins,
      ((ConLeche.restoreTbl p st).instAt (d.fvsPF (auxOfsOf st p.k cd j' Jc))).recMap.lookup qq.aux
        = none :=
    fun qq hqq => ConLeche.restoreTbl_instAt_recMap (fun q' hq' => hrecNe qq hqq q' hq')
  have hP : ∀ qq ∈ st.pins,
      ((ConLeche.restoreTbl p st).instAt params).pins.lookup qq.aux = some qq.pin ∧
      ((ConLeche.restoreTbl p st).instAt params).recMap.lookup qq.aux = none ∧
      ∀ z ∈ qq.pin.getAppArgs, z.looseBVarsBounded 0 = true := by
    intro qq hqq
    obtain ⟨J', lvls', Ds', hsh, -, hL, hB⟩ := hpinShape qq hqq
    obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hqq
    obtain ⟨lvls'', Ds'', hsh'', hDsB⟩ := hpinAll2 jq qq hjq
    refine ⟨ConLeche.restoreTbl_instAt_lookup hauxNodup hparamsLen hshape hqq hL hB,
      ConLeche.restoreTbl_instAt_recMap (fun q' hq' => hrecNe qq hqq q' hq'), ?_⟩
    rw [hsh'', Expr.getAppArgs_mkAppN]
    simpa [Expr.getAppArgs] using hDsB
  -- ## the container's recursive fields at the pin (§M.45's first piece)
  have hCshape := containerRecField_shape mpAux hDJ hlpsJnodup hlvlsLen' hDsLenE hDsC hcI' hJnf hopen
  -- ## the group exclusion (K.23 through the datum, §M.45's fourth piece)
  have hpinNameG : ∀ t, t < (cd j').dJ.k → ∃ q', st.pins[(cd j').base + t]? = some q' ∧
      q'.aux = d.memberName (p.k + ((cd j').base + t)) := by
    intro t ht
    obtain ⟨qq, hqq, -⟩ := hgroup t ht
    exact ⟨qq, hqq, (hpinName _ qq hqq).symm⟩
  obtain ⟨crestJ, hopPJ, hopFJ⟩ := hDJ.opens
  obtain ⟨bsJ, rJ, hsJ, -, -, -⟩ :=
    ConLeche.Verify.openPisAtFvars_stripPis ((cd j').dJ.nP + cAJ.2)
      (ConLeche.openPisAtFvars_add' _ hopPJ (by rw [Nat.zero_add]; exact hopFJ))
  have hcAname : cA.1.name = Name.replacePrefix J₂.name q₂.aux c.name := by
    rcases hstores with h | ⟨ty', h⟩ <;> rw [h]
  have hctorA : tyA.ctors[posIn (cd j').dJ Jc]?
      = some (cA.1.name, ConLeche.closeTelescope pbs' 0 body', c.nFields) := by
    rw [hcAname]; exact htyl
  have hexcl := groupExclusion_of_K23 (d := d) (dJ := (cd j').dJ) mpAux hK23 (hONR j' hj') hD hJc
    hDfacts.1 rfl hq₂ htyA hctorA hq₂b (by rw [hq₂s, hlenM]) hpinNameG hci'' hJ₂'' hq₂c.symm hcl
    htypeC.symm hnFC.symm (by rw [hnP'', hciNP]) hmemNames'' hsJ hnF
  -- ## K.17's pair at this constructor (§M.45's second piece)
  obtain ⟨hstLen, hstGet⟩ := ConLeche.auxStoredAll_get hstoredAll
  have hmIdxLt : p.k + ((cd j').base + (cd j').dJ.mems Jc) < b.k := by
    rw [← hkb]; have := pf.kA _ hmemsJ; omega
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, stored[p.k + ((cd j').base + (cd j').dJ.mems Jc)]? = some a₂ :=
    ⟨_, List.getElem?_eq_getElem (by rw [hstLen]; exact hmIdxLt)⟩
  obtain ⟨lOwn, hlOwn⟩ := List.getElem?_of_mem (ConLeche.ownCtors_mem hbl)
  obtain ⟨x, hx, hfx⟩ := ConLeche.auxStored?_ctors (hstGet _ _ ha₂) lOwn _ _ hlOwn
  have hpairMem := ConLeche.nestedCtorPairs_mem hmIdxLt ha₂ hlOwn hx
  have hxE : x = (cA.1, d.nP, cA.2) := by
    rw [← hcAname] at hfx
    obtain ⟨h1, h2, h3⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfx.symm.trans hDfacts.1))
    obtain ⟨x1, x2, x3⟩ := x
    simp only at h1 h2 h3
    rw [h1, h2, h3]
  rw [hxE] at hpairMem
  -- ## the processed and the stored constructor's closedness
  obtain ⟨hcvF, hcvB, -⟩ := ConLeche.checkMutualCtor_pre_input hrun
  obtain ⟨⟨tyS', hffS⟩, -, -⟩ := ConLeche.checkMutualCtor_front hrun
  have hst₀' : t₀.type.stripPis d.nP = some (pbs, body₀) := by rw [hnP]; exact hst₀
  have hop₀' : ConLeche.openPisAtFvars d.nP t₀.type 0 = some (params, bodyT) := by
    rw [hnP]; exact hop₀
  have hopenS : ConLeche.openPisAtFvars cA.2 cI d.nP = some (xFvsC, xrestC) := by
    rw [hnF]; exact hopen
  have hstrip'' : (ConLeche.closeTelescope pbs 0 cI).stripPis d.nP = some (pbs', rest) := by
    rw [hnP]; exact hstrip'
  have hK17' : ConLeche.nestedCtorsWhnfOk (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) d.nP
      (ConLeche.nestedCtorPairs b stored) = .ok () := by rw [hnP]; exact hK17
  have hfields := copyFields_of_whnfOk hRwf hRwf.toNamed hRnP hpF hcF hpB hRwf.ctorPinsBounded
    hst₀' hop₀' hnf₀ hP hK17' hpairMem rfl hstrip'' hinst hwalkC
    (fun qq hqq => hstb.subset hqq) hcvF hcvB hcIL hcIB
    (hnoAux j' hj' q lvls Ds hq hqp Jc cAJ hJc cI hcI) hopenS hop1 hop2 hffS.noFvar
  have hlpsT : cvT₀.levelParams = p.lps := by
    rw [← hDfacts.2.1]
    rcases hstores with h | ⟨ty', h⟩ <;> rw [h]
  -- ## the assembly
  exact copyCtorWalkFacts_of_stored (d := d) (dJ := (cd j').dJ) mpAux hD hlpsT hMO hnPb.symm hks hnF htgtLt hdk
    (fun t ht => hrealFresh t (by omega)) hcopyAux hDJ htgtJLt hstoredJ hopen hcIL hshape
    (by rw [hnP]; exact hparamsLen) hDsLenE hDsC hDsL hDsMention hCshape hgroup hnodupP hpinName
    hpinShape hpinLen (hRwf.toNamed.instAt _) hRnP hlookS hrecS hauxFresh hexcl hfields
    (hresidC j' hj' q lvls Ds hq hqp Jc cAJ hJc cI hcI xFvsC xrestC hopen)

end ConLeche.Model
