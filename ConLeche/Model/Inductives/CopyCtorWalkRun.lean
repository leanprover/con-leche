module

public import ConLeche.Model.Inductives.CopyCtorWalk

public section

/-!
# The constructor record at the RUN (task #279 M-B′ step 3p, DESIGN §M.42)

`CopyCtorWalk.lean` reads the record `CopyCtorAsRead` off
`CopyCtorWalkFacts` — what the walk and K.17 leave at one copy's
constructor — plus the `whnf` arm's content and the container field's
grading.  This module supplies the PLUMBING: every other hypothesis of
`copyCtorAsRead_of_walkFacts` comes from the run's own facts
(`PinRunFacts`, `CtorsChecked`, `MutualBlockReps`, `copiesFresh`,
`nestedContainersOk`), so that the record — and hence `CopyCtorsRead`,
the premise ψ and ψ⁻¹ carry — is a READ off `DeclNestedRun` modulo the
two named premises:

* **`CopyWalkFacts`** — the SYNTACTIC half, per pin and container
  constructor: the container's stored constructor instantiated at the
  pin opens at the copy's depth, and the walk leaves
  `CopyCtorWalkFacts` against the copy's own opened constructor;
* **`WhnfContent`** — the `whnf` arm's content at an abstract model of
  the environment holding the block's formers (M-D′ D2).

The container's instantiated constructor's READING is not a premise:
it is `ctor_peel`/`ctorInst_fields` at the pin's data, which the run
records (`PinRunFactsAt`'s level clauses, the components' guards and
their readings).
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

/-! ## The two named premises, at the run -/

/-- **What the walk leaves at every copy's constructor** (the syntactic
half of the constructor read): at every pin, for every constructor of
the pin's container datum, the container's stored constructor
instantiated at the pin's components opens at the block's parameter
depth over the constructor's fields, and `CopyCtorWalkFacts` holds of
the pair — the copy's stored constructor opened at the auxiliary
datum's own variables against it. -/
@[expose] def CopyWalkFacts (μ : CheckMode) (F : Nat) (env₁ : Env)
    (p : ConLeche.NestedParts) (st : ElimState) (R : ConLeche.RestoreTbl)
    (d : IndRepData V) (cd : Nat → CopyData V) : Prop :=
  ∀ (j' : Nat), j' < st.pins.length → ∀ (q : NestedPin) (lvls : List Level) (Ds : List Expr),
    st.pins[j']? = some q → q.pin = Expr.mkAppN (.const q.container lvls) Ds →
    ∀ (Jc : Nat) (cAJ : ConstantVal × Nat), (cd j').dJ.ctorsA[Jc]? = some cAJ →
    ∀ cI : Expr,
      Expr.instPis (cAJ.1.type.instantiateLevelParams cAJ.1.levelParams lvls) Ds = some cI →
      ∃ (xFvsC : List Expr) (xrestC : Expr),
        ConLeche.openPisAtFvars cAJ.2 cI d.nP = some (xFvsC, xrestC) ∧
        CopyCtorWalkFacts μ F env₁ R st p.k d.nP cAJ.2 (p.lps.map Level.param)
          (d.fvsPF (auxOfsOf st p.k cd j' Jc))
          (cd j').dJ Jc ((cd j').dJ.memberName ((cd j').dJ.mems Jc)) lvls Ds
          (d.xFvsF (auxOfsOf st p.k cd j' Jc)) xFvsC (d.xrestF (auxOfsOf st p.k cd j' Jc)) xrestC

/-- **The `whnf` arm's content** (M-D′ D2, DESIGN §M.44): at a field
the positivity normalisation reduced — the container's stored
constructor instantiated at the pin and opened at the block's parameter
depth, the copy's stored field against the container's opener `xC` —
the target's group exclusion and the reading of the RESTORED stored
field.  Quantified over the SAME opening `CopyWalkFacts` names, so that
the two premises speak of one pair of terms. -/
@[expose] def WhnfContent {μ : CheckMode} {envAux : Env} (F : Nat) (env₁ : Env)
    (p : ConLeche.NestedParts) (st : ElimState) (R : ConLeche.RestoreTbl)
    (mpAux : EnvModelM V μ envAux) (d : IndRepData V) (ψ : Name → Nat)
    (cd : Nat → CopyData V) : Prop :=
  ∀ (j' : Nat), j' < st.pins.length → ∀ (q : NestedPin) (lvls : List Level) (Ds : List Expr),
    st.pins[j']? = some q → q.pin = Expr.mkAppN (.const q.container lvls) Ds →
    ∀ (Jc : Nat) (cAJ : ConstantVal × Nat), (cd j').dJ.ctorsA[Jc]? = some cAJ →
    ∀ cI : Expr,
      Expr.instPis (cAJ.1.type.instantiateLevelParams cAJ.1.levelParams lvls) Ds = some cI →
    ∀ (xFvsC : List Expr) (xrestC : Expr),
      ConLeche.openPisAtFvars cAJ.2 cI d.nP = some (xFvsC, xrestC) →
    ∀ (i : Nat) (x xC : Expr), (d.xFvsF (auxOfsOf st p.k cd j' Jc))[i]? = some x →
      xFvsC[i]? = some xC →
      i ∉ ConLeche.recIdxOf ((cd j').dJ.ksF Jc) →
      WhnfField μ F env₁ R (d.fvsPF (auxOfsOf st p.k cd j' Jc)) (d.nP + i) x.fvarTypeD xC.fvarTypeD →
      (i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j' Jc)) →
        p.k ≤ d.tgtsR (auxOfsOf st p.k cd j' Jc) i →
        ¬ ((cd j').base ≤ d.tgtsR (auxOfsOf st p.k cd j' Jc) i - p.k ∧
          d.tgtsR (auxOfsOf st p.k cd j' Jc) i - p.k < (cd j').base + (cd j').dJ.k)) ∧
      ∀ (σ : Nat → V) (ws : List V), ws.length = i → Sat V (d.params ψ).reverse σ →
        SpineFit (consList ((cd j').DsA.map (interp V σ)) σ)
          (((((cd j').dJ.dsF Jc (cd j').ψ').drop (cd j').dJ.nP).take i).map (·.2.2)) ws →
        interp V (consList ws σ) (ConLeche.Model.AnnotTerm.instSeq (cd j').DsA
            ((cd j').dJ.nP + i - 1) (((cd j').dJ.dsF Jc (cd j').ψ').getD ((cd j').dJ.nP + i)
              default).2.2)
          = interp V (consList ws σ) (d.restoreAV mpAux.base2 ψ p.k (auxOfsOf st p.k cd j' Jc)
              (fun j'' => (cd j'').dJ.memberName (cd j'').mm) (fun j'' => (cd j'').ψ')
              (fun j'' => (cd j'').DsA) i) ∧
        WellDenotedV V (consList ws σ) (d.restoreAV mpAux.base2 ψ p.k
          (auxOfsOf st p.k cd j' Jc) (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
          (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA) i)

/-! ## The record, from the run -/

set_option maxHeartbeats 1600000 in
/-- **The constructor record at one pin's container constructor, from
the run** (DESIGN §M.42): every hypothesis of
`copyCtorAsRead_of_walkFacts` except the walk's facts and the `whnf`
arm's content is the run's own — the copy's constructor at the
auxiliary datum (`CtorsChecked` names the stage's list, the group-mate's
`CopyCtorsStored` its entry), the container's at its datum
(`PinFacts.repAll`), the pin's readings and level data
(`PinRunFactsAt`), the copies' freshness and names (`copiesFresh`, the
block's member names), the pins' distinctness (`nestedContainersOk`,
K.15) and the container's instantiated constructor's reading
(`ctor_peel`/`ctorInst_fields`). -/
theorem copyCtorAsRead_of_run {μ : CheckMode} {F : Nat} {env envAux env₁ : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V} {R : ConLeche.RestoreTbl}
    (hb : ConLeche.auxBlock p st = some b)
    (hlenSt : st.types.length = p.k + st.pins.length)
    (hcopies : ConLeche.copiesFresh env p.k st = true)
    (hcont : ConLeche.nestedContainersOk env st.pins = true)
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hpins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hwalk : CopyWalkFacts μ F env₁ p st R d cd)
    (hwhnfC : WhnfContent F env₁ p st R mpAux d ψ cd)
    {j' : Nat} (hj' : j' < st.pins.length) {Jc : Nat} {cAJ : ConstantVal × Nat}
    (hJc : (cd j').dJ.ctorsA[Jc]? = some cAJ) :
    d.CopyCtorAsRead mpAux.base2 (cd j').dJ ψ (cd j').ψ' (cd j').DsA p.k (cd j').base
      (fun j'' => (cd j'').dJ.memberName (cd j'').mm) (fun j'' => (cd j'').ψ')
      (fun j'' => (cd j'').DsA) Jc (auxOfsOf st p.k cd j' Jc) cAJ.2 := by
  -- the block's shape
  have hreps' := hreps
  obtain ⟨-, hkb, hkRb, hnPb, -, hviewAll, hnames, hall⟩ := hreps
  have hdk : d.k = p.k + st.pins.length := by rw [hkb, ConLeche.auxBlock_k hb, hlenSt]
  have hnP : d.nP = p.nP := by rw [hnPb, (ConLeche.auxBlock_inv hb).1]
  -- the pin's run facts
  obtain ⟨⟨pf, hbm, q, I, ci, J, lvls, Ds, cvTJ, capsJ, hq, hci, hJ, hJn, hmn, hlenM, hgrp, hqp,
      hgq, hfJ, hψ', hDsW, hsp, hcat, hcst, hlpsAll, hlvlsLen, hagLvl, hmemNames⟩, hgrpCd⟩ :=
    hpins j' hj'
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
  obtain rfl : q₂' = q₂ := Option.some.inj (hq₂'.symm.trans hq₂)
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
  obtain ⟨cI, cbody, body', pbs', rest, sta, stb, cA, hcI, hstrip', hinst, hwalkC, hsta, hstb, -, -,
    htyl, hbl, hcA, hnorm, hstores, hproj⟩ := hallC (posIn (cd j').dJ Jc) c hcl
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
  have hordRes : ∀ (i : Nat) (x : Expr), (d.xFvsF (auxOfsOf st p.k cd j' Jc))[i]? = some x →
      (d.ksF (auxOfsOf st p.k cd j' Jc)).getD i .ordinary = .ordinary →
      x.fvarTypeD.constsResolve env = true := by
    intro i x hx hk
    refine hMO.ord i x hx ?_
    have hi : i < ks.length := by
      rw [hksLen, ← hxLen]; exact (List.getElem?_eq_some_iff.mp hx).1
    rw [hksF _, hksEq, kindsOf_getD hi] at hk
    exact hk
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
  have hfresh : ∀ t, p.k ≤ t → t < d.k → env.find? (d.memberName t) = none := by
    intro t hkt ht
    obtain ⟨ty, hty, hmem⟩ := hdropMem t hkt ht
    rw [hmemberTy t ty hty ht]
    exact (hfreshCopies ty hmem).1
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
  have hnodupP : (st.pins.map (·.pin)).Nodup := by
    unfold ConLeche.nestedContainersOk at hcont
    rw [Bool.and_eq_true] at hcont
    exact of_decide_eq_true hcont.1
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
  have hgrpOk := pf.grp
  have hnIdxG : ∀ g, g < (cd j').dJ.k →
      d.nIdxAt (p.k + (cd j').base + g) = (cd j').dJ.nIdxAt g := by
    intro g hg
    have h1 := (hgrpOk g hg).idx.nIdx
    show d.nIdxAt (p.k + (cd j').base + g) = (cd j').dJ.nIdxAt g
    rw [show p.k + (cd j').base + g = p.k + ((cd j').base + g) by omega]
    exact h1.symm
  have hsort : (cd j').dJ.w (cd j').ψ' = d.w ψ := (hgrpOk _ hmemsJ).idx.sort
  have hspD : DenoteMetaSpine mpAux.base2.acval envAux ψ d.nP Ds (cd j').DsA := by
    rw [hnP]; exact hsp
  have hgroup : ∀ g, g < (cd j').dJ.k → ∃ qq, st.pins[(cd j').base + g]? = some qq ∧
      qq.pin = Expr.mkAppN (.const ((cd j').dJ.memberName g) lvls) Ds := by
    intro g hg
    obtain ⟨J', hJ'⟩ : ∃ J', ci.members[g]? = some J' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact hg)⟩
    obtain ⟨qq, hqq, -, hqqp, -, -⟩ := hgrp g J' hJ'
    exact ⟨qq, hqq, by rw [hqqp, (hmemNames g J' hJ').1]⟩
  -- every pin's target: container, levels, components, readings
  have hpinAll : ∀ (jq : Nat) (qq : NestedPin), st.pins[jq]? = some qq →
      ∃ (lvls' : List Level) (Ds' : List Expr) (cv : ConstantVal) (caps : IndCaps),
        qq.container = (cd jq).dJ.memberName (cd jq).mm ∧
        qq.pin = Expr.mkAppN (.const ((cd jq).dJ.memberName (cd jq).mm) lvls') Ds' ∧
        envAux.find? ((cd jq).dJ.memberName (cd jq).mm) = some (.indInfo cv caps) ∧
        lvls'.length = cv.levelParams.length ∧
        (∀ a ∈ Ds', Expr.WScoped d.nP a) ∧
        DenoteMetaSpine mpAux.base2.acval envAux ψ d.nP Ds' (cd jq).DsA ∧
        mpAux.base2.acval ((cd jq).dJ.memberName (cd jq).mm) ((cd jq).ψ')
          = mpAux.base2.acval ((cd jq).dJ.memberName (cd jq).mm)
              (Level.substFn ψ cv.levelParams lvls') := by
    intro jq qq hqq
    have hjq : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
    obtain ⟨⟨-, -, qq', I', ci', J', lvls', Ds', cvT', caps', hqq', -, hJq, -, hmnq, -, -, hqpq, -,
      hfJq, -, hDsWq, hspq, -, -, hlpsAllq, hlvlLenq, -, hmemNamesq⟩, -⟩ := hpins jq hjq
    obtain rfl : qq' = qq := Option.some.inj (hqq'.symm.trans hqq)
    obtain ⟨hnameq, hacvq⟩ := hmemNamesq _ J' hJq
    refine ⟨lvls', Ds', cvT', caps', hmnq.symm, by rw [hqpq, hmnq], by rw [hmnq]; exact hfJq,
      hlvlLenq, fun a ha => by rw [hnP]; exact (hDsWq a ha).1,
      by rw [hnP]; exact hspq, ?_⟩
    rw [hnameq, hacvq, hlpsAllq _ J' hJq]
  -- the container member's level parameters, and the pin's agreements
  have hfindM : envAux.find? ((cd j').dJ.memberName (cd j').mm) = some (.indInfo cvTJ capsJ) := by
    rw [hmn]; exact hfJ
  have hlpsJ : cvTJ.levelParams = cvTm.levelParams := hrepm.membersLps _ pf.mm cvTJ capsJ hfindM
  have hlpsC : cAJ.1.levelParams = cvTm.levelParams := hDJfacts.2.1
  have hJmLps : J₂.lps = cvTm.levelParams := by rw [hlpsAll _ J₂ hJm, hlpsJ]
  have hagJ : ∀ z ∈ cvTm.levelParams, (cd j').ψ' z = Level.substFn ψ cvTm.levelParams lvls z := by
    rw [← hlpsJ]; exact hagLvl
  have hacvJ : mpAux.base2.acval ((cd j').dJ.memberName ((cd j').dJ.mems Jc)) (cd j').ψ'
      = mpAux.base2.acval ((cd j').dJ.memberName ((cd j').dJ.mems Jc))
          (Level.substFn ψ cvTm.levelParams lvls) := by
    obtain ⟨hnm, hac⟩ := hmemNames _ J₂ hJm
    rw [hnm, hac, hJmLps]
  -- the walk, at the instantiation the mint performed
  have hcI' : Expr.instPis (cAJ.1.type.instantiateLevelParams cAJ.1.levelParams lvls) Ds
      = some cI := by rw [htypeC, hlpsC, ← hJmLps]; exact hcI
  obtain ⟨xFvsC, xrestC, hopen, hw⟩ := hwalk j' hj' q lvls Ds hq hqp Jc cAJ hJc cI hcI'
  -- the container's instantiated constructor, read
  have hDsLenE : Ds.length = (cd j').dJ.nP := by rw [DenoteMetaSpine.length hspD, pf.len]
  have hpeel := ctor_peel mpAux hDJfacts.1 hlpsC hDJ.toCtorDataI hagJ hacvJ hDsLenE
    (fun a ha => by rw [hnP]; exact hDsW a ha) hspD (by rw [← hlpsC]; exact hcI')
  have hlenDs := hDJ.len (cd j').ψ'
  have hΓ : (((cd j').dJ.dsF Jc (cd j').ψ').drop (cd j').dJ.nP).length = cAJ.2 := by
    rw [List.length_drop, hlenDs]; omega
  obtain ⟨hreadC₀, hreadRC⟩ := ctorInst_fields mpAux pf.len hΓ hpeel hopen
  have hdropGetD : ∀ i : Nat,
      ((((cd j').dJ.dsF Jc (cd j').ψ').drop (cd j').dJ.nP).getD i default).2.2
        = (((cd j').dJ.dsF Jc (cd j').ψ').getD ((cd j').dJ.nP + i) default).2.2 := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hreadC : ∀ (i : Nat) (xC : Expr), xFvsC[i]? = some xC →
      denoteMeta mpAux.base2.acval envAux ψ (d.nP + i) xC.fvarTypeD
        = some (ConLeche.Model.AnnotTerm.instSeq (cd j').DsA ((cd j').dJ.nP - 1 + i)
            (((cd j').dJ.dsF Jc (cd j').ψ').getD ((cd j').dJ.nP + i) default).2.2) := by
    intro i xC hxC
    rw [← hdropGetD i]
    exact hreadC₀ i xC hxC
  -- the container's field, graded at the record's frames
  have hgradeC := gradeC_of_okTy mpAux hDJ.toCtorDataI (hgrpOk _ pf.mm).ff (hgrpOk _ pf.mm).ls
    (hgrpOk _ pf.mm).pin (hgrpOk _ pf.mm).pIffM (hrepm.paramsIff Jc cAJ hJc (cd j').ψ')
  exact copyCtorAsRead_of_walkFacts mpAux hdk hD.pLen hD hview
    (by rw [hmemJa]; omega) hnF htgtLt hordRes hfresh hnodupM hcopyNames hDJ hmemsJ htgtJLt
    pf.kA hnIdxG hsort pf.len hspD hgroup hnodupP hpinName hpinAll hreadC hreadRC hw
    (fun i x xC hx hxC hnr hwf =>
      hwhnfC j' hj' q lvls Ds hq hqp Jc cAJ hJc cI hcI' xFvsC xrestC hopen i x xC hx hxC hnr hwf)
    hgradeC

/-- **`CopyCtorsRead` is a READ off `DeclNestedRun`**, modulo the walk's
facts and the `whnf` arm's content (DESIGN §M.42): at every pin and
every constructor of its container, the record ψ and ψ⁻¹ consume
(`psiFold_typed_of_read`, `invSetup_of_run`) holds. -/
theorem copyCtorsRead_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (order : List Nat),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
      st.types.length = p.k + st.pins.length ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧ AuxBlockAgree F mp mpAux b true d ∧
        ∃ (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta)),
          (ContainersRep env envAux mpAux.base2 → ∀ ψ : Name → Nat,
            ∃ cd : Nat → CopyData V,
              (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) ∧
              ∀ (env₁ : Env) (R : ConLeche.RestoreTbl),
                CopyWalkFacts μ F env₁ p st R d cd →
                WhnfContent F env₁ p st R mpAux d ψ cd →
                CopyCtorsRead mpAux d ψ st p.k st.pins.length cd) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, stored, order, hb, -, hord, hlenSt, hfreshC,
    hcontC, hparamsLen, -, -, -, -, -, -, -, -, mpAux, d, hreps, hchk, hag, hpins⟩ :=
    pinFacts_of_run hμ mp hE h
  refine ⟨st, b, envAux, order, hb, hord, hlenSt, mpAux, d, hreps, hchk, hag, params, pbs, ?_⟩
  intro hcr ψ
  obtain ⟨cd, hcd⟩ := hpins hcr ψ
  exact ⟨cd, hcd, fun env₁ R hwalk hwhnfC j' hj' Jc cAJ hJc =>
    copyCtorAsRead_of_run hb hlenSt hfreshC hcontC hreps hchk hcd hwalk hwhnfC hj' hJc⟩

end ConLeche.Model
