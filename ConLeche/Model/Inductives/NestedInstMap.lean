module

import ConLeche.Model.Inductives.NestedPins
import ConLeche.Model.Inductives.NestedCopyInst
import ConLeche.Verify.Inductives.NestedCopyKinds
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Model.Inductives.ContainerCross
import ConLeche.Model.Inductives.NestedOwnPinsRead
import ConLeche.Model.Inductives.NestedFieldRead
import ConLeche.Model.Annot.BitErase
import ConLeche.Verify.Inductives.NestedOpenSpine
import ConLeche.Verify.Inductives.NestedRecCtorPin
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedCopyInstU
public import ConLeche.Model.Inductives.NestedCopyIdx
public section

/-!
# The container instance map, at the model (task #315 K.61 and K.62)

The wide identification (`ofNested_pin_block_of_wide_inst`,
`NestedFit.lean`) is stated at an *instance map* `σ` — the function
taking a class of the container's own wide space (its members, then its
own pins) to the class of the block's auxiliary tuple that the
expansion minted for it.  The kernel records that map (K.61,
`nestedInstMapOk`) and records that a rewritten ordinary field leaves
its image (K.62, `nestedOrdOutsideOk`); this module is where the two
records meet the model's spelling.

The first step is the one the records were designed for: at a field of
the container that is nested into one of the container's OWN pins, the
copy's classification target IS `σ` of that pin.  The chain, which is
the one DESIGN records under "WIDE (2″) (c)":

* `ContainerModeled.nestPinSpineAbs` — the container field's abstract
  domain, cut at the pin's parameter count and read in the container's
  own scope, IS the recorded pin at that scope;
* `ContainerOwnPinsSyn`'s positional clause — the own-pin table's entry
  at a recorded pin's own index is that pin, at the same scope;
* K.61's `nestedInstMapOk_target` — the copy's field's target is the
  instance map's value at the table position the cut is FOUND at;
* `ContainerModeled.pinsDistinctAt` — the found position and the
  recorded index are one class: `findIdx?` is minimal, so the position
  is at most the recorded index and hence itself a recorded pin's, and
  the two entries are equal.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps ContainerInfo ContainerMember ContainerCtor
  AuxStored AuxType fueledOps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

section Assembly

variable {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {st : ElimState} {b : MutualBlock}
  {envAux : Env} {stored : List AuxStored} {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)}
  (R : NestedPinsRun V μ F mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁
    ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁')
include R

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)

variable {pinsS : List PinSyn}
  (SF : NestedPinSynFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (mp := mp) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
    (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
    (tssF := tssF) (ctorsR := ctorsR) (pinsS := pinsS) st mp₁')
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {q₀ kJ : Nat} {dJ : BlockModel V}
  (S : NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
    (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
    (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
    st mp₁'.base2 q₀ kJ dJ)
include SF S

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

omit SF S in
/-- **THE OWN-PIN TABLE IS READ THE SAME AT THE PREFIX ENVIRONMENT**
(task #315 WIDE (3′)) — `NestedPinsRun.contsCross`' twin for the table
`containerOwnPinsAt` reads.

The block's own formers are consed as `.indInfo`s at names fresh in
`env`, so the mimic walk can neither grow nor shrink
(`containerOwnPinsAtGo_ext`, whose `hmimOld` is discharged by the cons
being an `indInfo` and whose `hciEq` is
`containerInfo?_consMutualFormers`) and each step reads the same stored
type.  This is what lets a clause of `ContainerModeled` — which is
stated at the PREFIX model's environment — be consumed against K.61's
table, which the kernel reads at `env`. -/
theorem NestedPinsRun.ownPinsCross {C : Name} {lvls : List Level} {Ds : List Expr}
    (hC : (env.find? C).isSome = true) :
    ConLeche.containerOwnPinsAt (ENV₁) C lvls Ds
      = ConLeche.containerOwnPinsAt env C lvls Ds := by
  have hfr : ∀ f ∈ fms.take p.k, env.find? f.cvTa.name = none := by
    intro f hf'
    obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hf')
    exact R.h.fresh t f ht
  have hfreshN : ∀ n ∈ (fms.take p.k).map (·.cvTa.name), env.find? n = none := by
    intro n hn
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
    exact hfr f hf
  have hne : ∀ n : Name, n ∉ (fms.take p.k).map (·.cvTa.name) →
      (ENV₁).find? n = env.find? n := fun n hn =>
    consMutualFormers_find?_of_ne fun g hg heq => hn (heq ▸ List.mem_map_of_mem hg)
  have hstored : ∀ n : Name, (env.find? n).isSome = true →
      n ∉ (fms.take p.k).map (·.cvTa.name) := by
    intro n hn hmem
    rw [hfreshN n hmem] at hn
    exact nomatch hn
  have hext : ∀ (n : Name) (c : ConstantInfo),
      env.find? n = some c → (ENV₁).find? n = some c := by
    intro n c hf
    rw [hne n (hstored n (by rw [hf]; rfl))]
    exact hf
  have hnewN : ∀ (n : Name) (c : ConstantInfo), (ENV₁).find? n = some c →
      env.find? n = some c ∨ n ∈ (fms.take p.k).map (·.cvTa.name) := by
    intro n c hf
    by_cases hn : n ∈ (fms.take p.k).map (·.cvTa.name)
    · exact Or.inr hn
    · rw [hne n hn] at hf; exact Or.inl hf
  have hmimOld : ∀ (base : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      (ENV₁).find? (Name.appendIndexAfter base j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter base j ∉ (fms.take p.k).map (·.cvTa.name) := by
    intro base j cv mI rP rules hf hmem
    rcases consMutualFormers_find?_cases hf with h₁ | ⟨f, -, hc⟩
    · rw [hfreshN _ hmem] at h₁; exact nomatch h₁
    · exact nomatch hc
  have hciEq : ∀ K : Name, (env.find? K).isSome = true →
      ConLeche.containerInfo? (ENV₁) K = ConLeche.containerInfo? env K := fun K hK =>
    containerInfo?_consMutualFormers mp.base2.wf mp.base2.rec_ctors hfr hK
  have hhead : RecMajorHeadStored env := recMajorHeadStored_of_envWF mp.base2.wf
  cases hfC : env.find? C with
  | none => rw [hfC] at hC; exact nomatch hC
  | some cinfo =>
    have hfC₁ : (ENV₁).find? C = some cinfo := hext _ _ hfC
    cases cinfo with
    | indInfo cv caps =>
      cases hci : ConLeche.containerInfo? env C with
      | none =>
        unfold ConLeche.containerOwnPinsAt
        rw [hfC, hfC₁]
        simp only [bind, Option.bind, hci, hciEq C hC]
      | some ci =>
        cases hM : ci.members.head? with
        | none =>
          unfold ConLeche.containerOwnPinsAt
          rw [hfC, hfC₁]
          simp only [bind, Option.bind, hci, hciEq C hC, hM]
        | some M =>
          rw [containerOwnPinsAt_eq hfC₁ (by rw [hciEq C hC]; exact hci) hM,
            containerOwnPinsAt_eq hfC hci hM]
          exact congrArg some
            (containerOwnPinsAtGo_ext hext hnewN (hmimOld (M.name.str "rec")) hciEq hhead 64 0)
    | _ =>
      cases h1 : ConLeche.containerOwnPinsAt (ENV₁) C lvls Ds with
      | some ps =>
        obtain ⟨cv, caps, -, -, hff, -, -, -⟩ := containerOwnPinsAt_inv h1
        rw [hfC₁] at hff; exact nomatch hff
      | none =>
        cases h2 : ConLeche.containerOwnPinsAt env C lvls Ds with
        | none => rfl
        | some ps =>
          obtain ⟨cv, caps, -, -, hff, -, -, -⟩ := containerOwnPinsAt_inv h2
          rw [hfC] at hff; exact nomatch hff

/-- **K.61 AT THE COPY'S FIELD** (task #315 WIDE (3′)): at a field of
the container that is finitary recursive into one of the container's
OWN pins, the auxiliary block's classification target for the COPY's
field is `p.k +` the instance map's value at that pin.

`copyPinFKind`'s sibling — the same guard, discharged from the same
four model facts (the head through `BlockOpened.nestF` and
`blockCtorFieldHead`, the non-membership `pinsNotMembers`, the further
container `pinNP`/`contsEnv`, the mention `nestArgsMentionAbs`) — with
K.61's inversion in K.60's place, and the table position it answers
identified with the container's own pin INDEX.

The identification is the step the record could not make for itself:
`nestedInstMapOk_target` hands back the position `findIdx?` answers,
and the model indexes by `d.pinAt`.  `findIdx?` is MINIMAL and the
recorded pin's own entry matches, so the position is at most the pin's
index and hence itself below `d.nPins`; at two such positions the
table's entries are the two pins at one scope, and
`ContainerModeled.pinsDistinctAt` says equal entries are one pin. -/

theorem NestedPinsRun.copyPinFInstTgt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hrecC : (dJ.ksF i' j).getD l .ordinary = .recursive)
    (hpinT : ¬ dJ.tgts i' j l < dJ.k) :
    ∃ mm : List Nat, ConLeche.nestedInstMapAt env st (q₀ + i') = some mm ∧
      mm.getD (dJ.tgts i' j l - dJ.k) st.pins.length
        = ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, -⟩ := hCD.resid
  have hcbsLen : cbs.length = dJ.nP + cAJ.2 := Expr.stripPis_length _ hstripJ
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  -- K.26's kinds table at the pin, and the stored copy's constructor
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  -- the aux block's classification at that position
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk]
    simp only at hcv hnf' ⊢
    rw [hcv, hnf']
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, t⟩ := rt
  -- the container's member record at `i'`, positionally
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJ₂name : J₂.name = J.name := by
    rw [← (CMci.member i' J₂ hJ₂).1, hJname]
    exact hI.member
  have hJ₂mem : J₂ ∈ ci.members := List.mem_of_getElem? hJ₂
  have hjJ₂ : j < J₂.ctors.length := by
    have hmap := (CMci.member i' J₂ hJ₂).2.1
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, J₂.ctors[j]? = some cJ := ⟨_, List.getElem?_eq_getElem hjJ₂⟩
  have hccJ : cc = cJ :=
    (ConLeche.containerInfo?_member_ctor_det hciP hciP hJmem hJ₂mem hJ₂name.symm hcc hcJ).2.2.2
  -- the container's stored constructor, stripped
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hcJty : cJ.type = cAJ.1.type := by rw [hty, hccJ]
  have hcJnF : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
  obtain ⟨residJ, hsJ⟩ : ∃ residJ, cJ.type.stripPis (ci.nP + cJ.nFields) = some (cbs, residJ) :=
    ⟨_, by rw [hcJty, hcJnF, hnPci]; exact hstripJ⟩
  -- the pin the container's own classification names
  have hnestq : dJ.nestOf i' j l = some (dJ.tgts i' j l - dJ.k) := dJ.nestOf_some hpinT
  have hFssLen : ((dJ.Fss i' (fun _ => 0)).getD j []).length = cAJ.2 :=
    hI.Fss_length hj (fun _ => 0)
  have hqq : dJ.tgts i' j l - dJ.k < dJ.nPins :=
    CMci.reps.tgt_pin_lt hik hj l (by rw [hFssLen]; exact hlF) hpinT
  -- the container's field domain, abstract, and its head
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, cbs[dJ.nP + l]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hlF)⟩
  obtain ⟨hfnOp, -, -, -, -⟩ := hCD.opened.nestF l x _ hx hnestq hrecC
  have hdrop : (cbs.drop dJ.nP)[l]? = some domJ := by
    rw [List.getElem?_drop]; exact hdomJ
  have hheadA : domJ.1.getAppFn
      = Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
          (dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls :=
    blockCtorFieldHead hCD
      (show cAJ.1.type.stripPis (dJ.nP + cAJ.2)
          = some (cbs.take dJ.nP ++ cbs.drop dJ.nP, _) from by
        rw [List.take_append_drop]; exact hstripJ)
      (by rw [List.length_take]; omega) hx hdrop hfnOp
  -- the head is a FURTHER stored container, and no member of this group
  obtain ⟨ciK, hciK₀, hnPK⟩ := CMci.pinNP _ hqq
  have hciK : ConLeche.containerInfo? env (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J = some ciK :=
    S.contsEnv _ hqq ciK hciK₀
  have hnm : ((ci.members.map (·.name)).contains
      ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).J)) = false := by
    have hne : (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J ∉ ci.members.map (·.name) := by
      rw [← CMci.memberNames_eq]; exact CMci.pinsNotMembers _ hqq
    simpa using hne
  -- and its parameter part carries a member of the container's own group
  obtain ⟨e, he, hme⟩ := CMci.nestArgsMentionAbs i' j l cAJ cbs _ domJ _ hik hj hstripJ hdomJ
    hnestq hqq hrecC
  rw [hnPK] at he
  rw [CMci.memberNames_eq] at hme
  -- the container's own level parameters, and the group's first member
  obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, -, -, -, -, hmembers⟩ :=
    ConLeche.containerInfo?_inv hciP
  have hmem0 : 0 < ci.members.length := by omega
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, ci.members[0]? = some M₀ :=
    ⟨_, List.getElem?_eq_getElem hmem0⟩
  obtain ⟨cvC₀, capsC₀, cvRc₀, mIc₀, rulesC₀, -, -, hlps₀, -, hlpsT₀, -, -⟩ :=
    hmembers M₀ (List.mem_of_getElem? hM₀)
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfindC, -, hlpsC, -, hlpsT, -, -⟩ :=
    hmembers J₂ hJ₂mem
  have hlvlsEq : M₀.lps = cvC.levelParams := by rw [hlps₀, hlpsT₀, hlpsT]
  -- the own-pin table AT THE CONTAINER'S OWN SCOPE
  have hmemJ₂ : dJ.memberName i' = J₂.name := (CMci.member i' J₂ hJ₂).1
  have hJ₂J : J₂.name = (pinsS.getD (q₀ + i') default).J := by rw [hJ₂name, hJname]
  have hciJ₂ : ConLeche.containerInfo? env J₂.name = some ci := by rw [hJ₂J]; exact hciP
  have hhead0 : ci.members.head? = some M₀ := by
    rw [List.head?_eq_getElem?]; exact hM₀
  have hselfEq : ConLeche.containerOwnPinsSelf env J₂.name
      = ConLeche.containerOwnPinsAt env J₂.name (cvC.levelParams.map Level.param)
          (ConLeche.containerParamOpeners ci.nP) := by
    rw [← hlvlsEq]
    simp only [ConLeche.containerOwnPinsSelf, bind, Option.bind, hciJ₂, hhead0]
  have hownAt0 : ConLeche.containerOwnPinsAt env J₂.name (cvC.levelParams.map Level.param)
      (ConLeche.containerParamOpeners ci.nP)
      = some (ConLeche.containerOwnPinsAtGo env (M₀.name.str "rec") cvC.levelParams
          (cvC.levelParams.map Level.param) (ConLeche.containerParamOpeners ci.nP) ci.nP 64 0) :=
    containerOwnPinsAt_eq hfindC hciJ₂ hhead0
  obtain ⟨own0, hownAt⟩ : ∃ own0 : List Expr,
      ConLeche.containerOwnPinsAt env J₂.name (cvC.levelParams.map Level.param)
        (ConLeche.containerParamOpeners ci.nP) = some own0 := ⟨_, hownAt0⟩
  have hself : ConLeche.containerOwnPinsSelf env J₂.name = some own0 := hselfEq.trans hownAt
  -- the openers are closed
  have hclO : ∀ a ∈ ConLeche.containerParamOpeners ci.nP,
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    rfl
  have hlenO : (ConLeche.containerParamOpeners ci.nP).length = dJ.nP := by
    rw [← hnPci]; simp [ConLeche.containerParamOpeners]
  obtain ⟨hownMem, hownAtPos⟩ := CMci.ownPins i' cvC capsC (cvC.levelParams.map Level.param)
    (ConLeche.containerParamOpeners ci.nP) own0 hik
    (by rw [hmemJ₂]; exact R.cross.1 _ _ (fun _ _ _ _ hh => nomatch hh) hfindC) hclO
    (by rw [hmemJ₂, R.ownPinsCross (C := J₂.name) (by rw [hfindC]; rfl)]; exact hownAt)
  -- the container's own field spine, in the container's own scope
  have hspine := CMci.nestPinSpineAbs i' j l cAJ cbs _ domJ (dJ.tgts i' j l - dJ.k)
    cvC.levelParams hik hj hstripJ hdomJ hnestq hqq hrecC
  have hcut : Expr.instantiateList
      (Expr.mkAppN domJ.1.getAppFn (domJ.1.getAppArgs.take ciK.nP))
      (ConLeche.containerParamOpeners ci.nP).reverse l
      = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).ownAt dJ.nP cvC.levelParams
          (cvC.levelParams.map Level.param) (ConLeche.containerParamOpeners dJ.nP) := by
    rw [hnPci, ← hnPK]; exact hspine
  -- the table's entry at the pin's OWN index is that spine
  have hatq : own0[dJ.tgts i' j l - dJ.k]? = some
      (Expr.instantiateList (Expr.mkAppN domJ.1.getAppFn
        (domJ.1.getAppArgs.take ciK.nP)) (ConLeche.containerParamOpeners ci.nP).reverse l) := by
    rw [hcut, show ConLeche.containerParamOpeners dJ.nP
        = ConLeche.containerParamOpeners ci.nP from by rw [hnPci]]
    exact hownAtPos _ hqq (by rw [hlenO])
  -- K.61 at this field
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  obtain ⟨qK, e0, mm, hfi, he0, he0eq, hmapAt, hmapVal⟩ :=
    ConLeche.nestedInstMapOk_target R.hK61 hkP hq PD.pin hkq
      (by rw [hpinJ]; exact hciP)
      (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
      (by rw [hpinJ, ← hJ₂J]; exact hself)
      (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
      hkfj hcJ hsJ hrt (by rw [hnPci]; exact hdomJ) hheadA hnm hciK he hme
  -- `findIdx?` is minimal, so the position it answers is the pin's own index
  obtain ⟨hqKlt, hqKp, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
  obtain ⟨hclt, hcval⟩ := List.getElem?_eq_some_iff.mp hatq
  have hqKle : qK ≤ dJ.tgts i' j l - dJ.k := by
    refine Nat.not_lt.mp (fun hlt => ?_)
    have hmin' := hmin _ hlt
    simp [hcval] at hmin'
  have hqKpin : qK < dJ.nPins := by omega
  have hqKeq : qK = dJ.tgts i' j l - dJ.k := by
    refine CMci.pinsDistinctAt qK (dJ.tgts i' j l - dJ.k) cvC.levelParams hqKpin hqq ?_
    have hopen : ConLeche.containerParamOpeners dJ.nP
        = ConLeche.containerParamOpeners ci.nP := by rw [hnPci]
    have h1 : own0[qK]? = some ((dJ.pinAt qK).ownAt dJ.nP cvC.levelParams
        (cvC.levelParams.map Level.param) (ConLeche.containerParamOpeners dJ.nP)) := by
      rw [hopen]; exact hownAtPos _ hqKpin (by rw [hlenO])
    have h2 : own0[dJ.tgts i' j l - dJ.k]? = some
        ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).ownAt dJ.nP cvC.levelParams
          (cvC.levelParams.map Level.param) (ConLeche.containerParamOpeners dJ.nP)) := by
      rw [hopen]; exact hownAtPos _ hqq (by rw [hlenO])
    have h3 : own0[qK]? = own0[dJ.tgts i' j l - dJ.k]? := by
      rw [hatq, List.getElem?_eq_getElem hqKlt]
      exact congrArg some (by simpa using hqKp)
    rw [h1, h2] at h3
    exact Option.some.inj h3
  -- the target read off the block's own tables
  have htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = t := by
    rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hcAnF]; exact hlF)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = t
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  exact ⟨mm, hmapAt, by rw [htg, ← hqKeq]; exact hmapVal⟩

/-- **K.61's ARM AT A REFLEXIVE NESTED FIELD** (task #315 K.65's model
consumer): `copyPinFInstTgt` one `Π`-tower down.  Every step is the
finitary one with the domain read after `stripDomPis` and the cut moved
out by `domPiDepth`: the head comes from `BlockOpened.nestReflF`
through `Expr.piBinders_instSeq` (`copyPinFKindRefl`'s derivation), the
mention from `nestArgsMentionAbsRefl`, the spine from
`nestPinSpineAbsRefl`, and K.61 answers through
`nestedInstMapOk_target_refl`.

`findIdx?`'s minimality and `pinsDistinctAt` then identify the position
with the pin's own index exactly as they do on the finitary arm — the
table is the same table, and the two arms differ only in which cut is
looked up in it. -/
theorem NestedPinsRun.copyPinFInstTgtRefl {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hreflC : (dJ.ksF i' j).getD l .ordinary = .reflexive)
    (hpinT : ¬ dJ.tgts i' j l < dJ.k) :
    ∃ mm : List Nat, ConLeche.nestedInstMapAt env st (q₀ + i') = some mm ∧
      mm.getD (dJ.tgts i' j l - dJ.k) st.pins.length
        = ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, -⟩ := hCD.resid
  have hcbsLen : cbs.length = dJ.nP + cAJ.2 := Expr.stripPis_length _ hstripJ
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  -- K.26's kinds table at the pin, and the stored copy's constructor
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  -- the aux block's classification at that position
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk]
    simp only at hcv hnf' ⊢
    rw [hcv, hnf']
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, t⟩ := rt
  -- the container's member record at `i'`, positionally
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJ₂name : J₂.name = J.name := by
    rw [← (CMci.member i' J₂ hJ₂).1, hJname]
    exact hI.member
  have hJ₂mem : J₂ ∈ ci.members := List.mem_of_getElem? hJ₂
  have hjJ₂ : j < J₂.ctors.length := by
    have hmap := (CMci.member i' J₂ hJ₂).2.1
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, J₂.ctors[j]? = some cJ := ⟨_, List.getElem?_eq_getElem hjJ₂⟩
  have hccJ : cc = cJ :=
    (ConLeche.containerInfo?_member_ctor_det hciP hciP hJmem hJ₂mem hJ₂name.symm hcc hcJ).2.2.2
  -- the container's stored constructor, stripped
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hcJty : cJ.type = cAJ.1.type := by rw [hty, hccJ]
  have hcJnF : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
  obtain ⟨residJ, hsJ⟩ : ∃ residJ, cJ.type.stripPis (ci.nP + cJ.nFields) = some (cbs, residJ) :=
    ⟨_, by rw [hcJty, hcJnF, hnPci]; exact hstripJ⟩
  -- the pin the container's own classification names
  have hnestq : dJ.nestOf i' j l = some (dJ.tgts i' j l - dJ.k) := dJ.nestOf_some hpinT
  have hFssLen : ((dJ.Fss i' (fun _ => 0)).getD j []).length = cAJ.2 :=
    hI.Fss_length hj (fun _ => 0)
  have hqq : dJ.tgts i' j l - dJ.k < dJ.nPins :=
    CMci.reps.tgt_pin_lt hik hj l (by rw [hFssLen]; exact hlF) hpinT
  -- the container's field domain, abstract, and its head
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, cbs[dJ.nP + l]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hlF)⟩
  obtain ⟨afvs, bodyO, hopA, hafvs, -, hfnO, -, -, -, -⟩ :=
    hCD.opened.nestReflF l x _ hx hnestq hreflC
  have hdrop : (cbs.drop dJ.nP)[l]? = some domJ := by
    rw [List.getElem?_drop]; exact hdomJ
  -- **THE HEAD, ONE `Π`-TOWER DOWN** (task #315 K.65): `nestReflF`
  -- gives the OPENED domain as a telescope with a pin-headed body, and
  -- the tower's depth and body cross the opening because the openers
  -- are variables (`Expr.piBinders_instSeq`) — `copyPinFKindRefl`'s
  -- own derivation, at the same inputs.
  have hdomEq : x.fvarTypeD
      = Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) domJ.1 :=
    blockCtorFieldDomain hCD
      (show cAJ.1.type.stripPis (dJ.nP + cAJ.2)
          = some (cbs.take dJ.nP ++ cbs.drop dJ.nP, _) from by
        rw [List.take_append_drop]; exact hstripJ)
      (by rw [List.length_take]; omega) hx hdrop
  obtain ⟨crestA, hopPA, hopXA⟩ := hCD.opens
  obtain ⟨bodyA₀, hopAll⟩ : ∃ bodyA₀, ConLeche.openPisAtFvars (dJ.nP + cAJ.2) cAJ.1.type 0
      = some (dJ.fvsPF i' j ++ dJ.xFvsF i' j, bodyA₀) :=
    ⟨_, openPisAtFvars_add dJ.nP hopPA (by rw [Nat.zero_add]; exact hopXA)⟩
  have hfvAll : ∀ v ∈ dJ.fvsPF i' j ++ dJ.xFvsF i' j,
      ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty := by
    obtain ⟨-, -, -, hlenO', hIdxO, -⟩ :=
      ConLeche.Verify.openPisAtFvars_stripPis (dJ.nP + cAJ.2) hopAll
    intro v hv
    obtain ⟨iv, hiv, hvi⟩ := List.mem_iff_getElem.mp hv
    obtain ⟨tyv, hjv⟩ := hIdxO iv (by rw [← hlenO']; exact hiv)
    rw [List.getElem?_eq_getElem hiv] at hjv
    exact ⟨0 + iv, tyv, by rw [← hvi]; exact Option.some.inj hjv⟩
  have hfvL : ∀ v ∈ dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l,
      ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty := by
    intro v hv
    refine hfvAll v ?_
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_of_mem_take h)
  have hlenL : (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l).length ≤ dJ.nP + l - 1 + 1 := by
    rw [List.length_append, hCD.pLen, List.length_take]; omega
  have hafvsIdx : ∀ v ∈ afvs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty := by
    obtain ⟨-, -, -, hlenA', hIdxA, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hopA
    intro v hv
    obtain ⟨iv, hiv, hvi⟩ := List.mem_iff_getElem.mp hv
    obtain ⟨tyv, hjv⟩ := hIdxA iv (by rw [← hlenA']; exact hiv)
    rw [List.getElem?_eq_getElem hiv] at hjv
    exact ⟨dJ.nP + l + iv, tyv, by rw [← hvi]; exact Option.some.inj hjv⟩
  obtain ⟨hdepEq, hbodyEq⟩ := ConLeche.Model.Expr.piBinders_instSeq
    (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) domJ.1 hfvL hlenL
  rw [← hdomEq] at hdepEq hbodyEq
  have hbodyO : bodyO
      = Expr.instSeq afvs ((x.fvarTypeD.piBinders).1.length - 1) ((x.fvarTypeD.piBinders).2) :=
    openPisAtFvars_instSeq _ hopA
      (ConLeche.Model.Expr.stripPis_piBinders x.fvarTypeD)
  have hfnPB : ((x.fvarTypeD.piBinders).2).getAppFn
      = Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
          (dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls := by
    refine ConLeche.os_instSeq_getAppFn_const_inv afvs hafvsIdx
      ((x.fvarTypeD.piBinders).1.length - 1) _ ?_
    rw [← hbodyO]; exact hfnO
  have hheadPB : ((domJ.1.piBinders).2).getAppFn
      = Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
          (dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls := by
    refine ConLeche.os_instSeq_getAppFn_const_inv _ hfvL
      (dJ.nP + l - 1 + (domJ.1.piBinders).1.length) _ ?_
    rw [← hbodyEq]; exact hfnPB
  have hsd : ConLeche.stripDomPis domJ.1 = (domJ.1.piBinders).2 := by
    rw [ConLeche.stripDomPis_of_stripPis _ (ConLeche.Model.Expr.stripPis_piBinders domJ.1),
      ConLeche.stripDomPis_eq_self_of_getAppFn_const hheadPB]
  have hheadA : (ConLeche.stripDomPis domJ.1).getAppFn
      = Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
          (dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls := by
    rw [hsd]; exact hheadPB
  -- the head is a FURTHER stored container, and no member of this group
  obtain ⟨ciK, hciK₀, hnPK⟩ := CMci.pinNP _ hqq
  have hciK : ConLeche.containerInfo? env (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J = some ciK :=
    S.contsEnv _ hqq ciK hciK₀
  have hnm : ((ci.members.map (·.name)).contains
      ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).J)) = false := by
    have hne : (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J ∉ ci.members.map (·.name) := by
      rw [← CMci.memberNames_eq]; exact CMci.pinsNotMembers _ hqq
    simpa using hne
  -- and its parameter part carries a member of the container's own group
  obtain ⟨e, he, hme⟩ := CMci.nestArgsMentionAbsRefl i' j l cAJ cbs _ domJ _ hik hj hstripJ hdomJ
    hnestq hqq hreflC
  rw [hnPK] at he
  rw [CMci.memberNames_eq] at hme
  -- the container's own level parameters, and the group's first member
  obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, -, -, -, -, hmembers⟩ :=
    ConLeche.containerInfo?_inv hciP
  have hmem0 : 0 < ci.members.length := by omega
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, ci.members[0]? = some M₀ :=
    ⟨_, List.getElem?_eq_getElem hmem0⟩
  obtain ⟨cvC₀, capsC₀, cvRc₀, mIc₀, rulesC₀, -, -, hlps₀, -, hlpsT₀, -, -⟩ :=
    hmembers M₀ (List.mem_of_getElem? hM₀)
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfindC, -, hlpsC, -, hlpsT, -, -⟩ :=
    hmembers J₂ hJ₂mem
  have hlvlsEq : M₀.lps = cvC.levelParams := by rw [hlps₀, hlpsT₀, hlpsT]
  -- the own-pin table AT THE CONTAINER'S OWN SCOPE
  have hmemJ₂ : dJ.memberName i' = J₂.name := (CMci.member i' J₂ hJ₂).1
  have hJ₂J : J₂.name = (pinsS.getD (q₀ + i') default).J := by rw [hJ₂name, hJname]
  have hciJ₂ : ConLeche.containerInfo? env J₂.name = some ci := by rw [hJ₂J]; exact hciP
  have hhead0 : ci.members.head? = some M₀ := by
    rw [List.head?_eq_getElem?]; exact hM₀
  have hselfEq : ConLeche.containerOwnPinsSelf env J₂.name
      = ConLeche.containerOwnPinsAt env J₂.name (cvC.levelParams.map Level.param)
          (ConLeche.containerParamOpeners ci.nP) := by
    rw [← hlvlsEq]
    simp only [ConLeche.containerOwnPinsSelf, bind, Option.bind, hciJ₂, hhead0]
  have hownAt0 : ConLeche.containerOwnPinsAt env J₂.name (cvC.levelParams.map Level.param)
      (ConLeche.containerParamOpeners ci.nP)
      = some (ConLeche.containerOwnPinsAtGo env (M₀.name.str "rec") cvC.levelParams
          (cvC.levelParams.map Level.param) (ConLeche.containerParamOpeners ci.nP) ci.nP 64 0) :=
    containerOwnPinsAt_eq hfindC hciJ₂ hhead0
  obtain ⟨own0, hownAt⟩ : ∃ own0 : List Expr,
      ConLeche.containerOwnPinsAt env J₂.name (cvC.levelParams.map Level.param)
        (ConLeche.containerParamOpeners ci.nP) = some own0 := ⟨_, hownAt0⟩
  have hself : ConLeche.containerOwnPinsSelf env J₂.name = some own0 := hselfEq.trans hownAt
  -- the openers are closed
  have hclO : ∀ a ∈ ConLeche.containerParamOpeners ci.nP,
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    rfl
  have hlenO : (ConLeche.containerParamOpeners ci.nP).length = dJ.nP := by
    rw [← hnPci]; simp [ConLeche.containerParamOpeners]
  obtain ⟨hownMem, hownAtPos⟩ := CMci.ownPins i' cvC capsC (cvC.levelParams.map Level.param)
    (ConLeche.containerParamOpeners ci.nP) own0 hik
    (by rw [hmemJ₂]; exact R.cross.1 _ _ (fun _ _ _ _ hh => nomatch hh) hfindC) hclO
    (by rw [hmemJ₂, R.ownPinsCross (C := J₂.name) (by rw [hfindC]; rfl)]; exact hownAt)
  -- the container's own field spine, in the container's own scope
  have hspine := CMci.nestPinSpineAbsRefl i' j l cAJ cbs _ domJ (dJ.tgts i' j l - dJ.k)
    cvC.levelParams hik hj hstripJ hdomJ hnestq hqq hreflC
  have hcut : Expr.instantiateList
      (Expr.mkAppN (ConLeche.stripDomPis domJ.1).getAppFn
        ((ConLeche.stripDomPis domJ.1).getAppArgs.take ciK.nP))
      (ConLeche.containerParamOpeners ci.nP).reverse (l + ConLeche.domPiDepth domJ.1)
      = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).ownAt dJ.nP cvC.levelParams
          (cvC.levelParams.map Level.param) (ConLeche.containerParamOpeners dJ.nP) := by
    rw [hnPci, ← hnPK]; exact hspine
  -- the table's entry at the pin's OWN index is that spine
  have hatq : own0[dJ.tgts i' j l - dJ.k]? = some
      (Expr.instantiateList (Expr.mkAppN (ConLeche.stripDomPis domJ.1).getAppFn
        ((ConLeche.stripDomPis domJ.1).getAppArgs.take ciK.nP)) (ConLeche.containerParamOpeners ci.nP).reverse (l + ConLeche.domPiDepth domJ.1)) := by
    rw [hcut, show ConLeche.containerParamOpeners dJ.nP
        = ConLeche.containerParamOpeners ci.nP from by rw [hnPci]]
    exact hownAtPos _ hqq (by rw [hlenO])
  -- K.61 at this field
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  obtain ⟨qK, e0, mm, hfi, he0, he0eq, hmapAt, hmapVal⟩ :=
    ConLeche.nestedInstMapOk_target_refl R.hK61 hkP hq PD.pin hkq
      (by rw [hpinJ]; exact hciP)
      (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
      (by rw [hpinJ, ← hJ₂J]; exact hself)
      (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
      hkfj hcJ hsJ hrt (by rw [hnPci]; exact hdomJ) hheadA hnm hciK he hme
  -- `findIdx?` is minimal, so the position it answers is the pin's own index
  obtain ⟨hqKlt, hqKp, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
  obtain ⟨hclt, hcval⟩ := List.getElem?_eq_some_iff.mp hatq
  have hqKle : qK ≤ dJ.tgts i' j l - dJ.k := by
    refine Nat.not_lt.mp (fun hlt => ?_)
    have hmin' := hmin _ hlt
    simp [hcval] at hmin'
  have hqKpin : qK < dJ.nPins := by omega
  have hqKeq : qK = dJ.tgts i' j l - dJ.k := by
    refine CMci.pinsDistinctAt qK (dJ.tgts i' j l - dJ.k) cvC.levelParams hqKpin hqq ?_
    have hopen : ConLeche.containerParamOpeners dJ.nP
        = ConLeche.containerParamOpeners ci.nP := by rw [hnPci]
    have h1 : own0[qK]? = some ((dJ.pinAt qK).ownAt dJ.nP cvC.levelParams
        (cvC.levelParams.map Level.param) (ConLeche.containerParamOpeners dJ.nP)) := by
      rw [hopen]; exact hownAtPos _ hqKpin (by rw [hlenO])
    have h2 : own0[dJ.tgts i' j l - dJ.k]? = some
        ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).ownAt dJ.nP cvC.levelParams
          (cvC.levelParams.map Level.param) (ConLeche.containerParamOpeners dJ.nP)) := by
      rw [hopen]; exact hownAtPos _ hqq (by rw [hlenO])
    have h3 : own0[qK]? = own0[dJ.tgts i' j l - dJ.k]? := by
      rw [hatq, List.getElem?_eq_getElem hqKlt]
      exact congrArg some (by simpa using hqKp)
    rw [h1, h2] at h3
    exact Option.some.inj h3
  -- the target read off the block's own tables
  have htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = t := by
    rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hcAnF]; exact hlF)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = t
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  exact ⟨mm, hmapAt, by rw [htg, ← hqKeq]; exact hmapVal⟩

/-- **K.62 AND K.66 AT THE COPY'S FIELD** (task #315 WIDE (3′)): at a
field of the container that is ORDINARY and whose COPY the auxiliary
block classifies recursive-or-reflexive at a target outside the block's
own members — the `ordF`-RIGHT arm — that target is OUTSIDE the
instance map's image (K.62, the container's own pins' classes) AND
outside the mint GROUP (K.66, its members' classes).  `houtσ`
quantifies over both halves, which is why the record carries both.

The edge list is K.37's, unchanged: `nestedPinEdges_mem` says the field
IS a row of it, with the bit `mentionsMember` computes on the
CONTAINER's stored domain, and `ContainerModeled.ordFree` says that bit
is `false` — stated on the field's OPENED domain, which is the stored
one substituted (`blockCtorFieldDomain`), and a mention survives a
substitution, so the opened `false` gives the stored one
(`mentionsMember_instSeq_false`).  K.62 then answers at that row. -/
theorem NestedPinsRun.copyOrdFOutside {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    (hge : p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) :
    ∃ mm : List Nat, ConLeche.nestedInstMapAt env st (q₀ + i') = some mm ∧
      mm.contains (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k) = false ∧
      (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k < q₀ ∨
        q₀ + kJ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k) := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, -⟩ := hCD.resid
  have hcbsLen : cbs.length = dJ.nP + cAJ.2 := Expr.stripPis_length _ hstripJ
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk]
    simp only at hcv hnf' ⊢
    rw [hcv, hnf']
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, t⟩ := rt
  have htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = t := by
    rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hcAnF]; exact hlF)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = t
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  rw [htg] at hge ⊢
  -- the copy's field is recursive or reflexive
  have hrr : r = .recursive ∨ r = .reflexive := by
    rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map, hmutKs]; exact hlks),
      decide_eq_true_eq, kindsOf_getD', hmutKs] at hrss
    show r = _ ∨ r = _
    have hka : kindAt ksG l = r := by
      show (ksG.getD l (.ordinary, 0)).1 = r
      rw [List.getD_eq_getElem?_getD, hrt]; rfl
    rw [hka] at hrss
    exact hrss
  have hrecB : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true := by
    rcases hrr with rfl | rfl <;> rfl
  -- the container's member record at `i'`, positionally, and its constructor
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJ₂name : J₂.name = J.name := by
    rw [← (CMci.member i' J₂ hJ₂).1, hJname]
    exact hI.member
  have hJ₂mem : J₂ ∈ ci.members := List.mem_of_getElem? hJ₂
  have hjJ₂ : j < J₂.ctors.length := by
    have hmap := (CMci.member i' J₂ hJ₂).2.1
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, J₂.ctors[j]? = some cJ := ⟨_, List.getElem?_eq_getElem hjJ₂⟩
  have hccJ : cc = cJ :=
    (ConLeche.containerInfo?_member_ctor_det hciP hciP hJmem hJ₂mem hJ₂name.symm hcc hcJ).2.2.2
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hcJty : cJ.type = cAJ.1.type := by rw [hty, hccJ]
  have hcJnF : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
  obtain ⟨residJ, hsJ⟩ : ∃ residJ, cJ.type.stripPis (ci.nP + cJ.nFields) = some (cbs, residJ) :=
    ⟨_, by rw [hcJty, hcJnF, hnPci]; exact hstripJ⟩
  -- the container's abstract field domain, and the opened one it substitutes to
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, cbs[dJ.nP + l]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hlF)⟩
  have hdrop : (cbs.drop dJ.nP)[l]? = some domJ := by
    rw [List.getElem?_drop]; exact hdomJ
  have hopen : x.fvarTypeD
      = Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) domJ.1 :=
    blockCtorFieldDomain hCD
      (show cAJ.1.type.stripPis (dJ.nP + cAJ.2)
          = some (cbs.take dJ.nP ++ cbs.drop dJ.nP, _) from by
        rw [List.take_append_drop]; exact hstripJ)
      (by rw [List.length_take]; omega) hx hdrop
  -- an ordinary field mentions no member: on the opened domain, hence on the stored one
  have hmenAbs : ConLeche.mentionsMember (ci.members.map (·.name)) domJ.1 = false := by
    have hop := CMci.ordFree i' j l x hik hjlt hx hordC
    rw [hopen] at hop
    rw [← CMci.memberNames_eq]
    exact ConLeche.mentionsMember_instSeq_false _ _ hop
  -- the edge, and K.62 at it
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  cases hed : ConLeche.nestedPinEdges env p b st stored with
  | none =>
    have hK62 := R.hK62
    unfold ConLeche.nestedOrdOutsideOk ConLeche.nestedOrdOutsideAt at hK62
    rw [hed] at hK62
    cases hms : ConLeche.nestedInstMaps env st with
    | none => rw [hms] at hK62; simp at hK62
    | some maps => rw [hms] at hK62; simp at hK62
  | some edges =>
    have hmem := ConLeche.nestedPinEdges_mem hed hkP hq PD.pin hkq ha
      (by rw [hpinJ]; exact hciP)
      (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
      (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
      hkfj hac hcJ hsJ hlks hrt hrecB hge (by rw [hnPci]; exact hdomJ)
    rw [hmenAbs] at hmem
    obtain ⟨mm, hmap, hcon, hgrpOut⟩ :=
      ConLeche.nestedOrdOutsideOk_at R.hK62 hed hq PD.pin hmem rfl
    obtain ⟨hgb', hgs'⟩ := S.grp i' hi'
    rw [← pinAtE_eq] at hgb' hgs'
    rw [hgb', hgs'] at hgrpOut
    exact ⟨mm, hmap, hcon, hgrpOut⟩


/-- **K.67 AT THE COPY'S FIELD** (task #315 WIDE (3), session 2): the
positive twin of `copyOrdFOutside`, on the same scaffolding and at the
same guard.  Where that one says the block's target leaves the
instance, this says WHICH class of the OWNER it is the image of — the
owner being the container whose own pin number `qK` this copy is, read
off the instance map exactly as K.67's Bool reads it.

The scaffolding is `copyOrdFOutside`'s verbatim down to `hmenAbs`, the
`ordF` guard's bridge (`ContainerModeled.ordFree` on the OPENED domain,
carried to the stored one by `mentionsMember_instSeq_false`); only the
tail differs, because K.62 answers on the EDGE list and K.67 on K.61's
map and K.46's kinds. -/
theorem NestedPinsRun.instOrdTgtAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    (hge : p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
    {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    (hstrip : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (bs, rr))
    {dom : Expr × ConLeche.BinderMeta} (hdomM : bs[dJ.nP + l]? = some dom)
    {lpsC : List Name}
    (hlpsC : ∀ ciP : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciP →
      ∀ Jm : ContainerMember, ciP.members[i']? = some Jm → Jm.lps = lpsC)
    {g : Nat} (hg : g < st.pins.length) {gn : ConLeche.NestedPin}
    (hgn : st.pins[g]? = some gn)
    {ciO : ContainerInfo} (hciO : ConLeche.containerInfo? env gn.container = some ciO)
    {ownSelf : List Expr}
    (hown : ConLeche.containerOwnPinsSelf env gn.container = some ownSelf)
    {mapR : List Nat} (hmapR : ConLeche.nestedInstMapAt env st g = some mapR)
    {qK : Nat} (hqK : qK < ownSelf.length)
    (hqm : mapR.getD qK st.pins.length = q₀ + i')
    {M : Name} {us : List Level}
    (hhead : (ConLeche.ordTargetDom lpsC dJ.nP ownSelf qK l dom.1).getAppFn = .const M us) :
    (∀ mm, (ciO.members.map (·.name)).findIdx? (· == M) = some mm →
        ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + gn.grpBase + mm) ∧
    (∀ (ciM : ContainerInfo) (qJ : Nat),
      (ciO.members.map (·.name)).findIdx? (· == M) = none →
      ConLeche.containerInfo? env M = some ciM →
      ownSelf.findIdx? (fun e => e == Expr.mkAppN
          (ConLeche.ordTargetDom lpsC dJ.nP ownSelf qK l dom.1).getAppFn
          ((ConLeche.ordTargetDom lpsC dJ.nP ownSelf qK l dom.1).getAppArgs.take ciM.nP)) = some qJ →
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + mapR.getD qJ st.pins.length) := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, -⟩ := hCD.resid
  have hcbsLen : cbs.length = dJ.nP + cAJ.2 := Expr.stripPis_length _ hstripJ
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk]
    simp only at hcv hnf' ⊢
    rw [hcv, hnf']
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, t⟩ := rt
  have htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = t := by
    rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hcAnF]; exact hlF)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = t
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  rw [htg] at hge ⊢
  -- the copy's field is recursive or reflexive
  have hrr : r = .recursive ∨ r = .reflexive := by
    rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map, hmutKs]; exact hlks),
      decide_eq_true_eq, kindsOf_getD', hmutKs] at hrss
    show r = _ ∨ r = _
    have hka : kindAt ksG l = r := by
      show (ksG.getD l (.ordinary, 0)).1 = r
      rw [List.getD_eq_getElem?_getD, hrt]; rfl
    rw [hka] at hrss
    exact hrss
  have hrecB : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true := by
    rcases hrr with rfl | rfl <;> rfl
  -- the container's member record at `i'`, positionally, and its constructor
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJ₂name : J₂.name = J.name := by
    rw [← (CMci.member i' J₂ hJ₂).1, hJname]
    exact hI.member
  have hJ₂mem : J₂ ∈ ci.members := List.mem_of_getElem? hJ₂
  have hjJ₂ : j < J₂.ctors.length := by
    have hmap := (CMci.member i' J₂ hJ₂).2.1
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, J₂.ctors[j]? = some cJ := ⟨_, List.getElem?_eq_getElem hjJ₂⟩
  have hccJ : cc = cJ :=
    (ConLeche.containerInfo?_member_ctor_det hciP hciP hJmem hJ₂mem hJ₂name.symm hcc hcJ).2.2.2
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hcJty : cJ.type = cAJ.1.type := by rw [hty, hccJ]
  have hcJnF : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
  obtain ⟨residJ, hsJ⟩ : ∃ residJ, cJ.type.stripPis (ci.nP + cJ.nFields) = some (cbs, residJ) :=
    ⟨_, by rw [hcJty, hcJnF, hnPci]; exact hstripJ⟩
  -- the container's abstract field domain, and the opened one it substitutes to
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, cbs[dJ.nP + l]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  -- the model's spelling of the domain IS the scaffolding's
  have hbs : bs = cbs := congrArg Prod.fst (Option.some.inj (hstrip.symm.trans hstripJ))
  subst hbs
  have hdd : dom = domJ := Option.some.inj (hdomM.symm.trans hdomJ)
  subst hdd
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  have hlps' : J₂.lps = lpsC := hlpsC ci hciP J₂ hJ₂
  have hhead' : (ConLeche.ordTargetDom J₂.lps ci.nP ownSelf qK l dom.1).getAppFn
      = .const M us := by
    rw [hlps', hnPci]; exact hhead
  rw [← hnPci, ← hlps']
  exact ConLeche.nestedOrdTargetOk_at_refl R.hK67 hkP hg hgn hciO hown hmapR hqK hqm
    PD.pin hkq (by rw [hpinJ]; exact hciP)
    (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
    (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
    hkfj hcJ hsJ hrt (by rw [hnPci]; exact hdomJ) hrecB hge hhead'


/-- **K.70's ARM (A), THE MEMBER HALF, AT THE RUN** (task #315 K.70):
the OWNER's instance map takes its own pin group onto the block's,
member for member — so the owner's own pin for the container's member
`mm` maps to the block pin `q₀ + mm`.

It is the map fact a container-RECURSIVE field at a MEMBER target
needs, and nothing else: both copies' targets are exact there
(`CopyCtorShape.recF`), and this is what ties them. -/
theorem NestedPinsRun.instMapGrpAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    {g : Nat} (hg : g < st.pins.length) {gn : ConLeche.NestedPin}
    (hgn : st.pins[g]? = some gn)
    {ciO : ContainerInfo} (hciO : ConLeche.containerInfo? env gn.container = some ciO)
    {ownSelf : List Expr}
    (hown : ConLeche.containerOwnPinsSelf env gn.container = some ownSelf)
    {mapR : List Nat} (hmapR : ConLeche.nestedInstMapAt env st g = some mapR)
    {qK : Nat} (hqK : qK < ownSelf.length)
    (hqm : mapR.getD qK st.pins.length = q₀ + i')
    {mm : Nat} (hmm : mm < kJ) :
    mapR.getD (qK - i' + mm) st.pins.length = q₀ + mm := by
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨hgb₀, hgs₀⟩ := S.grp i' hi'
  have hgb : (pinAtE st (q₀ + i')).grpBase = q₀ := by
    rw [← pinAtE_eq] at hgb₀; exact hgb₀
  have hgs : (pinAtE st (q₀ + i')).grpSize = kJ := by
    rw [← pinAtE_eq] at hgs₀; exact hgs₀
  have hoff : q₀ + i' - (pinAtE st (q₀ + i')).grpBase = i' := by rw [hgb]; omega
  have hcell := ConLeche.nestedOrdTargetOk_grp_at R.hK67 hkP hg hgn hciO hown hmapR hqK hqm
    PD.pin hkq (mm := mm) (by rw [hgs]; exact hmm)
  rw [hoff, hgb] at hcell
  exact hcell

/-- **K.70's ARM (C) AT THE COPY'S FIELD** (task #315 K.70): the
NEGATIVE twin of `instOrdTgtAt`, one nesting level up from
`copyOrdFOutside`.

K.62/K.66 say a rewritten ordinary field's target leaves the COPY's own
instance — its own container's pins and its own mint group.  This says
the same of the OWNER's: where the owner's own recomputation did NOT
fire and the block's rewrite did, the target is in neither the image of
the OWNER's instance map nor the OWNER's own mint group.  That is the
arm `nestedFitc_pin`'s `hentOrd₁` speaks at, and the one the wide
identification's pin half closes with an entry.

The scaffolding is `instOrdTgtAt`'s verbatim, with the `ordF` guard's
bridge restored (`ContainerModeled.ordFree` on the OPENED domain,
carried to the stored one by `mentionsMember_instSeq_false`) — the
positive row lost it when K.70 widened it to the container-recursive
fields, and the negative one still needs it. -/
theorem NestedPinsRun.instOutOwnerAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    (hge : p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
    {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    (hstrip : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (bs, rr))
    {dom : Expr × ConLeche.BinderMeta} (hdomM : bs[dJ.nP + l]? = some dom)
    {lpsC : List Name}
    (hlpsC : ∀ ciP : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciP →
      ∀ Jm : ContainerMember, ciP.members[i']? = some Jm → Jm.lps = lpsC)
    {g : Nat} (hg : g < st.pins.length) {gn : ConLeche.NestedPin}
    (hgn : st.pins[g]? = some gn)
    {ciO : ContainerInfo} (hciO : ConLeche.containerInfo? env gn.container = some ciO)
    {ownSelf : List Expr}
    (hown : ConLeche.containerOwnPinsSelf env gn.container = some ownSelf)
    {mapR : List Nat} (hmapR : ConLeche.nestedInstMapAt env st g = some mapR)
    {qK : Nat} (hqK : qK < ownSelf.length)
    (hqm : mapR.getD qK st.pins.length = q₀ + i')
    (hnofire : ConLeche.ordRootFired env (ciO.members.map (·.name)) ownSelf
      (ConLeche.ordTargetDom lpsC dJ.nP ownSelf qK l dom.1) = false) :
    mapR.contains (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k) = false ∧
      (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k + gn.grpBase ∨
        p.k + gn.grpBase + gn.grpSize
          ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, -⟩ := hCD.resid
  have hcbsLen : cbs.length = dJ.nP + cAJ.2 := Expr.stripPis_length _ hstripJ
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk]
    simp only at hcv hnf' ⊢
    rw [hcv, hnf']
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, t⟩ := rt
  have htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = t := by
    rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hcAnF]; exact hlF)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = t
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  rw [htg] at hge ⊢
  -- the copy's field is recursive or reflexive
  have hrr : r = .recursive ∨ r = .reflexive := by
    rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map, hmutKs]; exact hlks),
      decide_eq_true_eq, kindsOf_getD', hmutKs] at hrss
    show r = _ ∨ r = _
    have hka : kindAt ksG l = r := by
      show (ksG.getD l (.ordinary, 0)).1 = r
      rw [List.getD_eq_getElem?_getD, hrt]; rfl
    rw [hka] at hrss
    exact hrss
  have hrecB : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true := by
    rcases hrr with rfl | rfl <;> rfl
  -- the container's member record at `i'`, positionally, and its constructor
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJ₂name : J₂.name = J.name := by
    rw [← (CMci.member i' J₂ hJ₂).1, hJname]
    exact hI.member
  have hJ₂mem : J₂ ∈ ci.members := List.mem_of_getElem? hJ₂
  have hjJ₂ : j < J₂.ctors.length := by
    have hmap := (CMci.member i' J₂ hJ₂).2.1
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, J₂.ctors[j]? = some cJ := ⟨_, List.getElem?_eq_getElem hjJ₂⟩
  have hccJ : cc = cJ :=
    (ConLeche.containerInfo?_member_ctor_det hciP hciP hJmem hJ₂mem hJ₂name.symm hcc hcJ).2.2.2
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hcJty : cJ.type = cAJ.1.type := by rw [hty, hccJ]
  have hcJnF : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
  obtain ⟨residJ, hsJ⟩ : ∃ residJ, cJ.type.stripPis (ci.nP + cJ.nFields) = some (cbs, residJ) :=
    ⟨_, by rw [hcJty, hcJnF, hnPci]; exact hstripJ⟩
  -- the container's abstract field domain, and the opened one it substitutes to
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, cbs[dJ.nP + l]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  -- an ordinary field mentions no member: on the opened domain, hence on the stored one
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hlF)⟩
  have hdrop : (cbs.drop dJ.nP)[l]? = some domJ := by
    rw [List.getElem?_drop]; exact hdomJ
  have hopen : x.fvarTypeD
      = Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) domJ.1 :=
    blockCtorFieldDomain hCD
      (show cAJ.1.type.stripPis (dJ.nP + cAJ.2)
          = some (cbs.take dJ.nP ++ cbs.drop dJ.nP, _) from by
        rw [List.take_append_drop]; exact hstripJ)
      (by rw [List.length_take]; omega) hx hdrop
  have hmenAbs : ConLeche.mentionsMember (ci.members.map (·.name)) domJ.1 = false := by
    have hop := CMci.ordFree i' j l x hik hjlt hx hordC
    rw [hopen] at hop
    rw [← CMci.memberNames_eq]
    exact ConLeche.mentionsMember_instSeq_false _ _ hop
  -- the model's spelling of the domain IS the scaffolding's
  have hbs : bs = cbs := congrArg Prod.fst (Option.some.inj (hstrip.symm.trans hstripJ))
  subst hbs
  have hdd : dom = domJ := Option.some.inj (hdomM.symm.trans hdomJ)
  subst hdd
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  have hlps' : J₂.lps = lpsC := hlpsC ci hciP J₂ hJ₂
  have hnofire' : ConLeche.ordRootFired env (ciO.members.map (·.name)) ownSelf
      (ConLeche.ordTargetDom J₂.lps ci.nP ownSelf qK l dom.1) = false := by
    rw [hlps', hnPci]; exact hnofire
  exact ConLeche.nestedOrdTargetOk_out_at R.hK67 hkP hg hgn hciO hown hmapR hqK hqm
    PD.pin hkq (by rw [hpinJ]; exact hciP)
    (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
    (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
    hkfj hcJ hsJ hrt (by rw [hnPci]; exact hdomJ) hrecB hge hmenAbs hnofire'


omit SF S in
/-- **THE PREFIX FORMERS ARE THE BLOCK'S MEMBERS, BY NAME** (task #315
WIDE (3), step 3): the run's first `p.k` formers carry exactly
`p.memberNames`, in order.  `membersFresh` used this inline; the
member arm of the field-data reading needs it on its own, to turn a
`findIdx?` hit in `p.memberNames` into the FORMER whose name it is —
which is what makes the positivity walk the identity there
(`normPosDomM_indApp_former`). -/
theorem NestedPinsRun.takeNames : (fms.take p.k).map (·.cvTa.name) = p.memberNames := by
  rw [List.map_take, R.h.names]
  exact ConLeche.auxBlock_memberNames R.hfA R.helim R.hb

omit SF S in
/-- **THE BLOCK'S MEMBER NAMES ARE FRESH** (task #315 WIDE (3), step 1):
`checkConstantVal`'s duplicate-declaration gate, read back at the run.
The auxiliary block's first `p.k` stored records ARE the block's own
annotated formers (`consNestedFormers_take_eq`), the formers' names are
the block's members' (`auxBlock_memberNames` through
`MutualFormersFacts.names`), and `hcaps` — the same Bool the nested
route records for the eta capability — says each of those names is
undeclared in `env`.

`DeclNestedCore.nestedMembersFresh` is the same fact at
`NestedCoreOut`; this one is at the RUN, where `hbk` supplies `O.bk`
and `h.names` the member-name half of `O.formers`, because the
consumers of the bound below (`ordGeAt`) hold `R` and not `O`. -/
theorem NestedPinsRun.membersFresh : ∀ n ∈ p.memberNames, env.find? n = none := by
  have hslen : stored.length = b.k := (ConLeche.auxStoredAll_get R.hstored).1
  have hkle : p.k ≤ b.k := by rw [R.hbk]; omega
  have hcv := (ConLeche.consNestedFormers_take_eq R.haux R.hformers R.hstored p.k hkle).2
  have hnames : (fms.take p.k).map (·.cvTa.name) = p.memberNames := R.takeNames
  intro n hn
  rw [← hnames] at hn
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hf
  have hilt : i < p.k := by
    have hl := (List.getElem?_eq_some_iff.mp hi).1
    rw [List.length_take] at hl
    omega
  have hfi : fms[i]? = some f := by
    rw [← List.getElem?_take_of_lt hilt]; exact hi
  have hsi : stored[i]? = some stored[i] := List.getElem?_eq_getElem (by omega)
  obtain ⟨f', hf', hcveq, -, -⟩ := hcv i _ hilt hsi
  obtain rfl : f' = f := Option.some.inj (hf'.symm.trans hfi)
  have hmem : stored[i] ∈ stored.take p.k :=
    List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hilt]; exact hsi)
  have hall := List.all_eq_true.mp R.hcaps _ hmem
  rw [Bool.and_eq_true] at hall
  rw [← congrArg (fun c : ConstantVal => c.name) hcveq]
  exact Option.isNone_iff_eq_none.mp hall.2

/-- **K.68 AT THE COPY'S FIELD** (task #315 WIDE (3), session 2): the
SELF-relative twin of `instOrdTgtAt`, on the same scaffolding.  Where
that one names the class the OWNER gave the field, this names the class
THIS block's own recomputation gives it — a member of the block by its
name, or a pin of the block by its term in the block's own table.  It
is what a LATER block reads of this one, and the container's side of
the wide correspondence is built from it. -/
theorem NestedPinsRun.instOrdSelfAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    (hstrip : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (bs, rr))
    {dom : Expr × ConLeche.BinderMeta} (hdomM : bs[dJ.nP + l]? = some dom)
    {lpsC : List Name}
    (hlpsC : ∀ ciP : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciP →
      ∀ Jm : ContainerMember, ciP.members[i']? = some Jm → Jm.lps = lpsC)
    {M : Name} {us : List Level}
    (hhead : (ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
      (q₀ + i') l dom.1).getAppFn = .const M us) :
    (∀ mm, p.memberNames.findIdx? (· == M) = some mm →
        ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = mm) ∧
    (p.memberNames.findIdx? (· == M) = none →
      ∃ (ciM : ContainerInfo) (z : Nat),
      ConLeche.containerInfo? env M = some ciM ∧
      (ConLeche.nestedPinTermsSelf p st).findIdx? (fun e => e == Expr.mkAppN
          (ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
            (q₀ + i') l dom.1).getAppFn
          ((ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
            (q₀ + i') l dom.1).getAppArgs.take ciM.nP)) = some z ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + z) := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, -⟩ := hCD.resid
  have hcbsLen : cbs.length = dJ.nP + cAJ.2 := Expr.stripPis_length _ hstripJ
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk]
    simp only at hcv hnf' ⊢
    rw [hcv, hnf']
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, t⟩ := rt
  have htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = t := by
    rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hcAnF]; exact hlF)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = t
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  -- the copy's field is recursive or reflexive
  have hrr : r = .recursive ∨ r = .reflexive := by
    rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map, hmutKs]; exact hlks),
      decide_eq_true_eq, kindsOf_getD', hmutKs] at hrss
    show r = _ ∨ r = _
    have hka : kindAt ksG l = r := by
      show (ksG.getD l (.ordinary, 0)).1 = r
      rw [List.getD_eq_getElem?_getD, hrt]; rfl
    rw [hka] at hrss
    exact hrss
  have hrecB : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true := by
    rcases hrr with rfl | rfl <;> rfl
  -- the container's member record at `i'`, positionally, and its constructor
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJ₂name : J₂.name = J.name := by
    rw [← (CMci.member i' J₂ hJ₂).1, hJname]
    exact hI.member
  have hJ₂mem : J₂ ∈ ci.members := List.mem_of_getElem? hJ₂
  have hjJ₂ : j < J₂.ctors.length := by
    have hmap := (CMci.member i' J₂ hJ₂).2.1
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, J₂.ctors[j]? = some cJ := ⟨_, List.getElem?_eq_getElem hjJ₂⟩
  have hccJ : cc = cJ :=
    (ConLeche.containerInfo?_member_ctor_det hciP hciP hJmem hJ₂mem hJ₂name.symm hcc hcJ).2.2.2
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hcJty : cJ.type = cAJ.1.type := by rw [hty, hccJ]
  have hcJnF : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
  obtain ⟨residJ, hsJ⟩ : ∃ residJ, cJ.type.stripPis (ci.nP + cJ.nFields) = some (cbs, residJ) :=
    ⟨_, by rw [hcJty, hcJnF, hnPci]; exact hstripJ⟩
  -- the container's abstract field domain, and the opened one it substitutes to
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, cbs[dJ.nP + l]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hbs : bs = cbs := congrArg Prod.fst (Option.some.inj (hstrip.symm.trans hstripJ))
  subst hbs
  have hdd : dom = domJ := Option.some.inj (hdomM.symm.trans hdomJ)
  subst hdd
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  have hlps' : J₂.lps = lpsC := hlpsC ci hciP J₂ hJ₂
  have hhead' : (ConLeche.ordTargetDom J₂.lps ci.nP (ConLeche.nestedPinTermsSelf p st)
      (q₀ + i') l dom.1).getAppFn = .const M us := by
    rw [hlps', hnPci]; exact hhead
  rw [htg, ← hnPci, ← hlps']
  exact ConLeche.nestedOrdSelfTargetOk_at_refl R.hK68 hkP hq PD.pin hkq
    (by rw [hpinJ]; exact hciP)
    (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
    (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
    hkfj hcJ hsJ hrt (by rw [hnPci]; exact hdomJ) hrecB hhead'


omit S in
/-- **THE MODEL'S OWN-PIN TABLE IS THE CHECKER'S** (task #315 K.68's
model side): `BlockModel.ownPinTerms` at the block's own model IS
`nestedPinTermsSelf` at the run.

Both are the recorded pin terms with the block's PARAMETERS abstracted
and re-opened at the parameter openers; they differ only in the
substitution idiom, `PinSyn.ownAt`'s `instSeq` against the kernel's
`instantiateList` (the kernel may not name `instSeq`, which lives in
`Verify`).  `instantiateList_openers_eq_instSeq` at cut `0` is that
identity, and its premise — a recorded pin is CLOSED, its parameters
riding as FVARS — is `NestedPinsRun.scoped`'s own clause. -/
theorem NestedPinsRun.ownPinTerms_eq (lps : List Name) :
    (D).ownPinTerms lps = ConLeche.nestedPinTermsSelf p st := by
  obtain ⟨-, fvs, o, -, hsc⟩ := R.scoped
  have hnP : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  have hlen : pinsS.length = st.pins.length := SF.pinsLen
  have hkey : ∀ (z : Nat) (pn : ConLeche.NestedPin), st.pins[z]? = some pn →
      ((D).pinAt z).ownAt b.nP lps (lps.map Level.param)
          (ConLeche.containerParamOpeners b.nP)
        = Expr.instantiateList (Expr.abstractRange pn.pin 0 p.nP 0)
            (ConLeche.containerParamOpeners p.nP).reverse 0 := by
    intro z pn hpz
    obtain ⟨hJ, hpin⟩ := SF.pinRec z pn hpz
    have hlvlId : ∀ us : List Level,
        us.map (Level.subst lps (lps.map Level.param)) = us := by
      intro us
      have h := Expr.instantiateLevelParams_self lps (Expr.const .anonymous us)
      simpa [Expr.instantiateLevelParams] using h
    have hstep : ((D).pinAt z).ownAt b.nP lps (lps.map Level.param)
          (ConLeche.containerParamOpeners b.nP)
        = Expr.instSeq (ConLeche.containerParamOpeners b.nP) (b.nP - 1)
            (Expr.abstractRange pn.pin 0 b.nP 0) := by
      show (pinsS.getD z default).ownAt b.nP lps (lps.map Level.param)
          (ConLeche.containerParamOpeners b.nP) = _
      unfold ConLeche.Model.PinSyn.ownAt
      rw [hpin, ← hJ, ConLeche.abstractRange_mkAppN, ConLeche.abstractRange_const,
        ConLeche.instSeq_mkAppN_const, hlvlId,
        show (ConLeche.containerParamOpeners b.nP).length = b.nP from by
          simp [ConLeche.containerParamOpeners]]
      simp only [List.map_map, Function.comp_def, Expr.instantiateLevelParams_self]
    have hcl : pn.pin.looseBVarsBounded 0 = true :=
      (hsc pn (List.mem_of_getElem? hpz)).1
    have hA : (Expr.abstractRange pn.pin 0 b.nP 0).looseBVarsBounded b.nP = true := by
      simpa using ConLeche.looseBVarsBounded_abstractRange pn.pin 0 b.nP 0 hcl
    rw [hstep, ← ConLeche.instantiateList_openers_eq_instSeq b.nP 0 hA,
      Expr.liftLooseBVars_zero, hnP]
  unfold BlockModel.ownPinTerms ConLeche.nestedPinTermsSelf
  refine List.ext_getElem? fun z => ?_
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hz : z < st.pins.length
  · have hz' : z < (D).nPins := by show z < pinsS.length; omega
    rw [List.getElem?_range hz', List.getElem?_eq_getElem hz]
    exact congrArg some (hkey z _ (List.getElem?_eq_getElem hz))
  · have hz' : (D).nPins ≤ z := by show pinsS.length ≤ z; omega
    rw [List.getElem?_eq_none (by simpa using hz'), List.getElem?_eq_none (by omega)]
    rfl

omit R SF S in
/-- The function part of a closed application is closed. -/
private theorem lbb_mkAppN_fn {k : Nat} : ∀ {xs : List Expr} {f : Expr},
    (Expr.mkAppN f xs).looseBVarsBounded k = true → f.looseBVarsBounded k = true := by
  intro xs
  induction xs with
  | nil => intro f h; exact h
  | cons x xs ih =>
    intro f h
    have h' : (f.looseBVarsBounded k && x.looseBVarsBounded k) = true := ih h
    cases hf : f.looseBVarsBounded k with
    | false => rw [hf, Bool.false_and] at h'; exact nomatch h'
    | true => rfl

omit R SF S in
/-- The arguments of a closed application are closed. -/
private theorem lbb_mkAppN_args {k : Nat} : ∀ {xs : List Expr} {f : Expr},
    (Expr.mkAppN f xs).looseBVarsBounded k = true → ∀ x ∈ xs, x.looseBVarsBounded k = true := by
  intro xs
  induction xs with
  | nil => intro f _ x hx; exact nomatch hx
  | cons x xs ih =>
    intro f h y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · have h' : (f.looseBVarsBounded k && y.looseBVarsBounded k) = true :=
        lbb_mkAppN_fn (xs := xs) (f := Expr.app f y) h
      cases hy2 : y.looseBVarsBounded k with
      | false => rw [hy2, Bool.and_false] at h'; exact nomatch h'
      | true => rfl
    · exact ih h y hy'

omit R in
/-- **A PIN'S LEVEL ARGUMENTS AND COMPONENTS, AS THE KERNEL READS
THEM** (task #315 WIDE (3′)): `nestedPinLvlsDs` at a pin of a group is
the pin's recorded `lvls` and `DsE` — the pin's term is the container
at them (`NestedPinSynFacts.pinRec`), the container's group is the
one the record names, and the components are `dJ.nP` in number so the
reader's `take` is the whole list. -/
theorem NestedPinsRun.pinLvlsDsAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    {ci : ContainerInfo}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (CM : ContainerModeled mp₁'.base2 ci dJ) :
    ConLeche.nestedPinLvlsDs env (pinAtE st (q₀ + i'))
      = some ((pinsS.getD (q₀ + i') default).lvls, (pinsS.getD (q₀ + i') default).DsE) := by
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have hqS : q₀ + i' < pinsS.length := by rw [SF.pinsLen]; exact hq
  have PD := hPD _ hq
  obtain ⟨hcname, hpinEq⟩ := SF.pinRec _ _ PD.pin
  have hDsLen : ((pinsS.getD (q₀ + i') default).DsE).length = dJ.nP := by
    rw [(SF.pinDs _ hqS (fun _ => 0)).length]
    exact S.pinDsLen i' hi' (fun _ => 0)
  unfold ConLeche.nestedPinLvlsDs
  rw [hpinEq]
  simp only [Expr.getAppFn_mkAppN, Expr.getAppArgs_mkAppN, bind, Option.bind, pure]
  rw [show (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J from hcname.symm,
    hciP]
  simp only [show (Expr.const (pinsS.getD (q₀ + i') default).J
      (pinsS.getD (q₀ + i') default).lvls).getAppFn
      = Expr.const (pinsS.getD (q₀ + i') default).J (pinsS.getD (q₀ + i') default).lvls from rfl,
    show (Expr.const (pinsS.getD (q₀ + i') default).J
      (pinsS.getD (q₀ + i') default).lvls).getAppArgs = [] from rfl,
    List.nil_append]
  rw [CM.nP.symm, ← hDsLen, List.take_length]

omit R in
/-- **THE INSTANCE MAP IS THE GROUP'S, NOT THE MEMBER'S** (task #315
WIDE (3′)): `nestedInstMapAt` agrees at any two pins of one group.

The assembly's `σ` is ONE function of the container's wide classes
while K.61's map is keyed by a BLOCK PIN, and the wide theorem's
`hstgt` quantifies over every member of the container — so the two are
the same object only if the member the map is read at does not matter.
It does not, and three facts say so: the group's pins share their
level arguments and components (`NestedPinGroupSyn.same`); two members
of one group name ONE container record, because both carry the same
block model, hence the same member names and parameter count
(`ContainerModeled.memberNames_eq`, `containerInfo?_eq_of_names`); and
a group's members share their level parameters
(`containerInfo?_inv`).  Those are exactly the four arguments
`containerOwnPinsAt` walks with. -/
theorem NestedPinsRun.instMapGroup {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i i' : Nat} (hi : i < kJ) (hi' : i' < kJ)
    {ci ci' : ContainerInfo}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i) default).J = some ci)
    (hciP' : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci')
    (CM : ContainerModeled mp₁'.base2 ci dJ) (CM' : ContainerModeled mp₁'.base2 ci' dJ) :
    ConLeche.nestedInstMapAt env st (q₀ + i) = ConLeche.nestedInstMapAt env st (q₀ + i') := by
  have hq : q₀ + i < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have hq' : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  obtain ⟨hcname, -⟩ := SF.pinRec _ _ (hPD _ hq).pin
  obtain ⟨hcname', -⟩ := SF.pinRec _ _ (hPD _ hq').pin
  -- one container record
  obtain rfl : ci = ci' :=
    ConLeche.containerInfo?_eq_of_names hciP hciP' (by rw [← CM.nP, CM'.nP])
      (CM.memberNames_eq.symm.trans CM'.memberNames_eq)
  -- one level-parameter list
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hf, hfr, hmem, hnd, hall⟩ :=
    ConLeche.containerInfo?_inv hciP
  obtain ⟨cvT', caps', cvR', mI', rP', rules', hf', hfr', hmem', hnd', hall'⟩ :=
    ConLeche.containerInfo?_inv hciP'
  obtain ⟨M', hM', hMn'⟩ := List.mem_map.mp hmem'
  obtain ⟨cvC', capsC', cvRc', mIc', rulesC', hfC', hrC', hlpsM', htyM', hlpsC', hlenC', hctC'⟩ :=
    hall M' hM'
  rw [hMn', hf'] at hfC'
  obtain rfl : cvC' = cvT' := (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj hfC'.symm)).1
  -- the shared level arguments and components
  have hlvls : (pinsS.getD (q₀ + i) default).lvls = (pinsS.getD (q₀ + i') default).lvls :=
    (S.same i hi).1.trans (S.same i' hi').1.symm
  have hDsE : (pinsS.getD (q₀ + i) default).DsE = (pinsS.getD (q₀ + i') default).DsE :=
    (S.same i hi).2.trans (S.same i' hi').2.symm
  unfold ConLeche.nestedInstMapAt
  rw [(hPD _ hq).pin, (hPD _ hq').pin]
  simp only [bind, Option.bind]
  rw [NestedPinsRun.pinLvlsDsAt SF S hPD hi hciP CM,
    NestedPinsRun.pinLvlsDsAt SF S hPD hi' hciP' CM', hlvls, hDsE]
  simp only []
  unfold ConLeche.containerOwnPinsAt
  rw [show (pinAtE st (q₀ + i)).container = (pinsS.getD (q₀ + i) default).J from hcname.symm,
    show (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J from hcname'.symm,
    hf, hf', hciP, hciP']
  simp only [bind, Option.bind, pure, hlpsC']

/-- **THE INSTANCE MAP'S VALUE IS THE CONTAINER'S OWN PIN, AT THE
BLOCK'S PIN TABLE** (task #315 WIDE (3′)): at every own pin `qK` of the
container of the block's pin `q₀ + i'`, the instance map is defined and
its value `σq` is a pin of the block whose container is `qK`'s, with
`qK`'s index universe and index telescope.

`hmemσ` and `hidxσ` — the two σ-facts of `rowsσ_of_pin_class` — are
read off this and nothing else.  `hmemσ` is the container NAME: an own
pin's container is no member of the container's own group
(`pinsNotMembers`) while a pin of the group's own segment has a member
for its container, so no member class shares a block pin with a pin
class.  `hidxσ` is the `u`/`Ids` pair at a COLLAPSED pair: two own pins
with one image have one block pin, hence one universe and one
telescope, hence one index-tuple set.

The two σ-facts take no READING of the own-pin table: the SYNTACTIC
clause `ownPins` places the container's own pin at the table position
and `NestedPinGroupSyn.pinOwn` (the block's pin and the container's own
pin are ONE pin's index data) reads `u` and `Ids` off the block's side.

**The last conjunct is the CORRESPONDENCE, and it does read the
table.**  `pinCorr_of_ownPins_at` at the reading form
`ContainerModeled.ownPinsRead` — whose two inputs about a STORED
container, its pins' components' scope and their readings, are now
clauses of `ContainerModeled` — hands `PinCorr` at the block pin the
map names, which is what the wide identification's `hρ` is read
through AT EVERY own-pin class, including the classes no field of the
container names.  The remaining premises are this proof's own: the
components' scope at the BLOCK's side is `NestedPinsRun.pinsWScoped`
through `WScoped_mkAppN_args`, the readings are `NestedPinSynFacts.pinDs`
at the two pins, the table entry is K.61's rewritten by the own-pin
clause, and `huIds` is `pinOwn` at the one pin
`pinCorr_of_pinEq` spends it at. -/
theorem NestedPinsRun.instMapPinOwn {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    {ci : ContainerInfo}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (CM : ContainerModeled mp₁'.base2 ci dJ)
    {qK : Nat} (hqK : qK < dJ.nPins)
    {cvT : ConstantVal} {caps : IndCaps}
    (hfind : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD (q₀ + i') default).J = some (.indInfo cvT caps)) :
    ∃ (mm : List Nat) (σq : Nat),
      ConLeche.nestedInstMapAt env st (q₀ + i') = some mm ∧
      mm[qK]? = some σq ∧ σq < pinsS.length ∧
      (pinsS.getD σq default).J = (dJ.pinAt qK).J ∧
      ∀ φ : Name → Nat,
        ((pinsS.getD σq default).u φ = (dJ.pinAt qK).u ((pinsS.getD (q₀ + i') default).ψJ φ) ∧
          (pinsS.getD σq default).Ids φ
            = (dJ.pinAt qK).Ids ((pinsS.getD (q₀ + i') default).ψJ φ)) ∧
        PinCorr ((D).targetView mp₁'.base2.acval φ) mp₁'.base2.acval dJ
          ((pinsS.getD (q₀ + i') default).ψJ φ) ((pinsS.getD (q₀ + i') default).Ds φ)
          cvT.levelParams ((pinsS.getD (q₀ + i') default).lvls) (p.k + σq) qK := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have hqS : q₀ + i' < pinsS.length := by rw [SF.pinsLen]; exact hq
  have PD := hPD _ hq
  obtain ⟨hcname, hpinEq⟩ := SF.pinRec _ _ PD.pin
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CM.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hmemJ₂ : dJ.memberName i' = J₂.name := (CM.member i' J₂ hJ₂).1
  obtain ⟨cvT', caps', cvR, mI, rP, rules, hfindP, hI, hψlaw⟩ := S.stored i' hi'
  have hcvT' : cvT' = cvT ∧ caps' = caps :=
    ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (hfindP.symm.trans hfind))
  rw [hcvT'.1, hcvT'.2] at hfindP
  have hψlaw' : ∀ φ : Name → Nat, (pinsS.getD (q₀ + i') default).ψJ φ
      = Level.substFn φ cvT.levelParams ((pinsS.getD (q₀ + i') default).lvls) := by
    intro φ; rw [← hcvT'.1]; exact hψlaw φ
  have hCname : (pinsS.getD (q₀ + i') default).J = J₂.name := by
    rw [← hmemJ₂]; exact hI.member.symm
  obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, -, -, -, -, hmembers⟩ :=
    ConLeche.containerInfo?_inv hciP
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfindC, -, -, -, -, -, -⟩ :=
    hmembers J₂ (List.mem_of_getElem? hJ₂)
  have hcvTC : cvT = cvC := by
    have h1 : (ConLeche.consMutualFormers (fms.take p.k) env).find?
        (pinsS.getD (q₀ + i') default).J = some (.indInfo cvT caps) := hfindP
    have h2 : (ConLeche.consMutualFormers (fms.take p.k) env).find?
        (pinsS.getD (q₀ + i') default).J = some (.indInfo cvC capsC) := by
      rw [hCname]
      exact R.cross.1 _ _ (fun _ _ _ _ hh => nomatch hh) hfindC
    exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (h1.symm.trans h2))).1
  have hmem0 : 0 < ci.members.length := by omega
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, ci.members[0]? = some M₀ :=
    ⟨_, List.getElem?_eq_getElem hmem0⟩
  have hhead0 : ci.members.head? = some M₀ := by
    rw [List.head?_eq_getElem?]; exact hM₀
  have hDsLen : ((pinsS.getD (q₀ + i') default).DsE).length = dJ.nP := by
    rw [(SF.pinDs _ hqS (fun _ => 0)).length]
    exact S.pinDsLen i' hi' (fun _ => 0)
  have hclosed : ∀ a ∈ (pinsS.getD (q₀ + i') default).DsE, a.looseBVarsBounded 0 = true := by
    obtain ⟨-, fvs, o, hop, hsc⟩ := R.scoped
    have hb := (hsc _ (List.mem_of_getElem? PD.pin)).1
    rw [hpinEq] at hb
    exact lbb_mkAppN_args hb
  have hnPci : ci.nP = dJ.nP := CM.nP.symm
  have hlds : ConLeche.nestedPinLvlsDs env (pinAtE st (q₀ + i'))
      = some ((pinsS.getD (q₀ + i') default).lvls, (pinsS.getD (q₀ + i') default).DsE) :=
    NestedPinsRun.pinLvlsDsAt SF S hPD hi' hciP CM
  obtain ⟨own, hown⟩ : ∃ own : List Expr,
      ConLeche.containerOwnPinsAt env (pinsS.getD (q₀ + i') default).J
        ((pinsS.getD (q₀ + i') default).lvls) ((pinsS.getD (q₀ + i') default).DsE)
        = some own :=
    ⟨_, containerOwnPinsAt_eq (by rw [hCname]; exact hfindC) hciP hhead0⟩
  have hfindM : (ConLeche.consMutualFormers (fms.take p.k) env).find? (dJ.memberName i')
      = some (.indInfo cvC capsC) := by
    rw [hmemJ₂, ← hCname]
    exact R.cross.1 _ _ (fun _ _ _ _ hh => nomatch hh) (by rw [hCname]; exact hfindC)
  have hpsM : ConLeche.containerOwnPinsAt (ConLeche.consMutualFormers (fms.take p.k) env)
      (dJ.memberName i') ((pinsS.getD (q₀ + i') default).lvls)
      ((pinsS.getD (q₀ + i') default).DsE) = some own := by
    rw [hmemJ₂, ← hCname, R.ownPinsCross (C := (pinsS.getD (q₀ + i') default).J)
      (by rw [hCname, hfindC]; rfl)]
    exact hown
  obtain ⟨-, hpos⟩ := CM.ownPins i' cvC capsC ((pinsS.getD (q₀ + i') default).lvls)
    ((pinsS.getD (q₀ + i') default).DsE) own hik hfindM hclosed hpsM
  have hat := hpos qK hqK hDsLen
  obtain ⟨mm, σq, rn, hmapAt, hmmqK, hσlt, hrn, hrnpin⟩ :=
    ConLeche.nestedInstMapOk_at R.hK61 hq PD.pin hlds
      (by rw [show (pinAtE st (q₀ + i')).container
            = (pinsS.getD (q₀ + i') default).J from hcname.symm]
          exact hown) hat
  have hσS : σq < pinsS.length := by rw [SF.pinsLen]; exact hσlt
  have PDσ := hPD σq hσlt
  obtain rfl : rn = pinAtE st σq := Option.some.inj (hrn.symm.trans PDσ.pin)
  obtain ⟨hcnameσ, hpinEqσ⟩ := SF.pinRec _ _ PDσ.pin
  rw [hpinEqσ] at hrnpin
  have hhead : (Expr.const (pinAtE st σq).container (pinsS.getD σq default).lvls)
      = .const (dJ.pinAt qK).J ((dJ.pinAt qK).lvls.map
          (Level.subst cvC.levelParams ((pinsS.getD (q₀ + i') default).lvls))) := by
    have h := congrArg Expr.getAppFn hrnpin
    unfold PinSyn.ownAt at h
    rwa [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at h
  have hJeq : (pinsS.getD σq default).J = (dJ.pinAt qK).J := by
    rw [hcnameσ]
    exact congrArg (fun e => match e with | .const n _ => n | _ => .anonymous) hhead
  have hlvlsEq : (pinsS.getD σq default).lvls
      = (dJ.pinAt qK).lvls.map (Level.subst cvC.levelParams
          ((pinsS.getD (q₀ + i') default).lvls)) :=
    congrArg (fun e => match e with | .const _ us => us | _ => []) hhead
  obtain ⟨cv, cp, hfK⟩ := hI.pinsFound qK hqK
  obtain ⟨hvlen, hlawK⟩ := CM.pinψ qK hqK cv cp hfK
  obtain ⟨aG, kkG, iG, dJG, hqeG, hiG, SG⟩ := SF.groups dsR xFvsR σq hσS
  obtain ⟨cvσ, capsσ, cvRσ, mIσ, rPσ, rulesσ, hfindσ, -, hψσ⟩ := SG.stored iG hiG
  rw [← hqeG] at hfindσ hψσ
  have hψσ' : ∀ φ : Name → Nat, (pinsS.getD σq default).ψJ φ
      = Level.substFn φ cvσ.levelParams ((pinsS.getD σq default).lvls) := hψσ
  have hcvσ : cvσ = cv := by
    have h1 : (ConLeche.consMutualFormers (fms.take p.k) env).find?
        (pinsS.getD σq default).J = some (.indInfo cvσ capsσ) := hfindσ
    rw [hJeq, hfK] at h1
    exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj h1)).1.symm
  have hpsi : ∀ pp ∈ cv.levelParams, ∀ φ : Name → Nat,
      (pinsS.getD σq default).ψJ φ pp
        = (dJ.pinAt qK).ψJ ((pinsS.getD (q₀ + i') default).ψJ φ) pp := by
    intro pp hpp φ
    rw [hψσ' φ, hcvσ, hlvlsEq, Level.substFn_map_subst hvlen hpp, hlawK, hψlaw' φ, hcvTC]
  have huIdsφ : ∀ φ : Name → Nat,
      (pinsS.getD σq default).u φ = (dJ.pinAt qK).u ((pinsS.getD (q₀ + i') default).ψJ φ) ∧
      (pinsS.getD σq default).Ids φ
        = (dJ.pinAt qK).Ids ((pinsS.getD (q₀ + i') default).ψJ φ) := fun φ =>
    S.pinOwn qK hqK σq hσS hJeq cv cp hfK φ ((pinsS.getD (q₀ + i') default).ψJ φ)
      (fun pp hpp => hpsi pp hpp φ)
  -- the table's entry at `qK` IS the block pin's recorded term
  have hatσ : own[qK]? = some (Expr.mkAppN
      (.const ((D).pinAt σq).J ((D).pinAt σq).lvls) ((D).pinAt σq).DsE) := by
    show own[qK]? = some (Expr.mkAppN
      (.const (pinsS.getD σq default).J (pinsS.getD σq default).lvls)
      (pinsS.getD σq default).DsE)
    rw [hat, hcnameσ, hrnpin]
  -- the outer pin's level assignment, as the substitution the table is read at
  have hψJC : ∀ φ : Name → Nat, (pinsS.getD (q₀ + i') default).ψJ φ
      = Level.substFn φ cvC.levelParams ((pinsS.getD (q₀ + i') default).lvls) := by
    intro φ; rw [hψlaw' φ, hcvTC]
  have hψDσ : ∀ (cv' : ConstantVal) (cp' : IndCaps),
      (ConLeche.consMutualFormers (fms.take p.k) env).find? ((D).pinAt σq).J
        = some (.indInfo cv' cp') →
      ∀ ψ' : Name → Nat, ((D).pinAt σq).ψJ ψ'
        = Level.substFn ψ' cv'.levelParams (((D).pinAt σq).lvls) := by
    intro cv' cp' hf' ψ'
    obtain ⟨rfl, -⟩ : cvσ = cv' ∧ capsσ = cp' :=
      ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (hfindσ.symm.trans hf'))
    exact hψσ' ψ'
  -- the components' SCOPE, K.30's at the scope predicate
  have hwsc : ∀ a ∈ (pinsS.getD (q₀ + i') default).DsE, Expr.WScoped b.nP a := by
    have hw := R.pinsWScoped _ (List.mem_of_getElem? PD.pin)
    rw [hpinEq] at hw
    exact WScoped_mkAppN_args hw
  refine ⟨mm, σq, hmapAt, hmmqK, hσS, hJeq, fun φ => ⟨huIdsφ φ, ?_⟩⟩
  have hc : PinCorr ((D).targetView mp₁'.base2.acval φ) mp₁'.base2.acval dJ
      (Level.substFn φ cvC.levelParams ((pinsS.getD (q₀ + i') default).lvls))
      ((pinsS.getD (q₀ + i') default).Ds φ) cvC.levelParams
      ((pinsS.getD (q₀ + i') default).lvls) ((D).k + σq) qK :=
    pinCorr_of_ownPins_at CM.ownPinsRead hik hfindM hpsM (SF.pinDs _ hqS φ) hqK hDsLen
      (fun a ha => ⟨hwsc a ha, hclosed a ha⟩) hatσ (SF.pinDs _ hσS φ) hψDσ CM.pinψ hI.pinsFound
      (fun _ => by rw [← hψJC φ]; exact huIdsφ φ)
  rw [hψJC φ, hcvTC]
  exact hc

/-- **THE TWO σ-FACTS, AND THE MAP'S RANGE** (task #315 WIDE (3′)):
`rowsσ_of_pin_class`'s `hmemσ` and `hidxσ` at the run's instance map,
read off `instMapPinOwn` at the group's BASE member and nothing else.

* `hσ` at the pin classes — the map's value is a pin of the block;
* `hmemσ` — no member class shares a block pin with a pin class: the
  block pin a pin class maps to has the container's OWN pin for its
  container (`instMapPinOwn`), a member class's block pin is the mimic
  of the container's member `c` and so has `dJ.memberName c` for its
  container (`IsBlockModel.member`), and a container's own pin is no
  member of its own group (`ContainerModeled.pinsNotMembers`);
* `hidxσ` at a COLLAPSED pair — two own pins with ONE block pin.  The
  `PinCorr` `instMapPinOwn` now hands is what closes it, and it takes
  all three of its data clauses, not the two the earlier reading
  counted: `u` and `Ids` are the pin's index sort and telescope, and
  `Ds` is the pin's FRAME, which `BlockModel.pinIdx` reads through
  `pinFrame`.  The two classes' components are equal only after the
  outer instantiation (`AnnotTerm.instAll`), which is exactly what
  `interp_instAll` removes at the pin's own frame. -/
theorem NestedPinsRun.instMapSigmaFacts {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hci : ∀ i', i' < kJ → ∃ ci : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci ∧
      ContainerModeled mp₁'.base2 ci dJ)
    {cvT : ConstantVal} {caps : IndCaps}
    (hfind : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD (q₀ + 0) default).J = some (.indInfo cvT caps))
    {mm : List Nat} (hmm : ConLeche.nestedInstMapAt env st (q₀ + 0) = some mm) :
    (∀ qK, qK < dJ.nPins → mm.getD qK 0 < pinsS.length) ∧
    (∀ c qK, c < dJ.k → qK < dJ.nPins → q₀ + c ≠ mm.getD qK 0) ∧
    (∀ qK qK', qK < dJ.nPins → qK' < dJ.nPins → mm.getD qK 0 = mm.getD qK' 0 →
      ∀ (φ : Name → Nat) (ρp : Nat → V),
        dJ.idx ((pinsS.getD (q₀ + 0) default).ψJ φ) ((D).pinFrame (q₀ + 0) φ ρp) (dJ.k + qK)
          = dJ.idx ((pinsS.getD (q₀ + 0) default).ψJ φ) ((D).pinFrame (q₀ + 0) φ ρp)
              (dJ.k + qK')) := by
  classical
  have hk0 : 0 < kJ := S.kpos
  obtain ⟨ci, hciP, CM⟩ := hci 0 hk0
  -- the map's entries, at every own pin
  have hat : ∀ qK, qK < dJ.nPins → ∃ σq, mm[qK]? = some σq ∧ σq < pinsS.length ∧
      (pinsS.getD σq default).J = (dJ.pinAt qK).J ∧
      ∀ φ : Name → Nat,
        PinCorr ((D).targetView mp₁'.base2.acval φ) mp₁'.base2.acval dJ
          ((pinsS.getD (q₀ + 0) default).ψJ φ) ((pinsS.getD (q₀ + 0) default).Ds φ)
          cvT.levelParams ((pinsS.getD (q₀ + 0) default).lvls) (p.k + σq) qK := by
    intro qK hqK
    obtain ⟨mm', σq, hmm', hmmqK, hσS, hJeq, hrest⟩ :=
      R.instMapPinOwn SF S hPD hk0 hciP CM hqK hfind
    obtain rfl : mm' = mm := Option.some.inj (hmm'.symm.trans hmm)
    exact ⟨σq, hmmqK, hσS, hJeq, fun φ => (hrest φ).2⟩
  have hgetD : ∀ qK, qK < dJ.nPins → ∀ σq, mm[qK]? = some σq → mm.getD qK 0 = σq := by
    intro qK _ σq h
    rw [List.getD_eq_getElem?_getD, h]; rfl
  refine ⟨fun qK hqK => ?_, fun c qK hc hqK => ?_, fun qK qK' hqK hqK' heq φ ρp => ?_⟩
  · obtain ⟨σq, hq, hlt, -, -⟩ := hat qK hqK
    rw [hgetD qK hqK σq hq]; exact hlt
  · -- a member class and a pin class never share a block pin
    obtain ⟨σq, hq, -, hJ, -⟩ := hat qK hqK
    rw [hgetD qK hqK σq hq]
    intro hcontra
    have hck : c < kJ := by rw [← S.kEq]; exact hc
    obtain ⟨cvTc, capsc, cvRc, mIc, rPc, rulesc, -, hIc, -⟩ := S.stored c hck
    have hname : (pinsS.getD (q₀ + c) default).J = dJ.memberName c := hIc.member.symm
    rw [← hcontra] at hJ
    have hmemName : (dJ.pinAt qK).J ∈ dJ.memberNames := by
      rw [← hJ, hname]
      show dJ.memberNames.getD c .anonymous ∈ dJ.memberNames
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show c < dJ.memberNames.length from by
          rw [CM.namesLen]; exact hc)]
      exact List.getElem_mem _
    exact CM.pinsNotMembers qK hqK hmemName
  · -- a collapsed pair: one block pin, hence one index-tuple set
    obtain ⟨σq, hq, -, -, hc⟩ := hat qK hqK
    obtain ⟨σq', hq', -, -, hc'⟩ := hat qK' hqK'
    obtain rfl : σq = σq' := by
      rw [hgetD qK hqK σq hq, hgetD qK' hqK' σq' hq'] at heq; exact heq
    obtain ⟨-, hDs, hu, hIds, -, -⟩ := hc φ
    obtain ⟨-, hDs', hu', hIds', -, -⟩ := hc' φ
    obtain ⟨cvT₀, cvR₀, mI₀, rP₀, rules₀, hI₀⟩ := S.reps 0 (by rw [← S.kEq] at hk0; exact hk0)
    rw [hI₀.auxPinIdx qK hqK, hI₀.auxPinIdx qK' hqK']
    show idxSet _ (dJ.pinFrame qK _ _) _ = idxSet _ (dJ.pinFrame qK' _ _) _
    have hmapEq : ((dJ.pinAt qK).Ds ((pinsS.getD (q₀ + 0) default).ψJ φ)).map
          (interp V ((D).pinFrame (q₀ + 0) φ ρp))
        = ((dJ.pinAt qK').Ds ((pinsS.getD (q₀ + 0) default).ψJ φ)).map
          (interp V ((D).pinFrame (q₀ + 0) φ ρp)) := by
      have h := hDs.symm.trans hDs'
      have h2 := congrArg (fun l => l.map (interp V ρp)) h
      simp only [List.map_map] at h2
      have hcomp : ∀ as : List AnnotTerm,
          as.map ((interp V ρp) ∘ (AnnotTerm.instAll
              ((pinsS.getD (q₀ + 0) default).Ds φ) 0))
            = as.map (interp V ((D).pinFrame (q₀ + 0) φ ρp)) := by
        intro as
        refine List.map_congr_left fun e _ => ?_
        show interp V ρp (AnnotTerm.instAll ((pinsS.getD (q₀ + 0) default).Ds φ) 0 e) = _
        exact interp_instAll ((pinsS.getD (q₀ + 0) default).Ds φ) [] ρp e
      rw [hcomp, hcomp] at h2
      exact h2
    have hframe : dJ.pinFrame qK ((pinsS.getD (q₀ + 0) default).ψJ φ)
          ((D).pinFrame (q₀ + 0) φ ρp)
        = dJ.pinFrame qK' ((pinsS.getD (q₀ + 0) default).ψJ φ)
            ((D).pinFrame (q₀ + 0) φ ρp) :=
      congrArg (fun l => consList l ((D).pinFrame (q₀ + 0) φ ρp)) hmapEq
    rw [hframe, hu.symm.trans hu', hIds.symm.trans hIds']

/-- **THE BLOCK'S PICK AT A COPY'S OWN-PIN FIELD, AS A PIN** (task
#315 WIDE, lane `uniform-carry`): `instTgtAt` with the block pin it
names KEPT rather than projected away — the copy's field lands on
`p.k + σq`, and `σq` is a pin of the block whose container is that of
the container's own pin, with the own pin's index universe, index
telescope and `PinCorr`.

`instTgtAt` below is this theorem's `getD` form, and the reason to
have both is the CONSUMER.  `hstgt` — the wide identification's
hypothesis — asks only for the map's VALUE, and that is `instTgtAt`.
The correspondence at an `ordF`-right field of a pin's copy (DESIGN
"WIDE (3′) `hent₂`", `docs/NESTED.md` §8's last item) asks something
strictly more: that the block's pick and the CONTAINER's pick at the
same field are one pin.  Neither side's index is a handle for that —
they index different lists, and two own pins that collapse at one
instantiation need not collapse at the other — so the comparison is
made at the pin's DATA, which is what this theorem hands back and
`instTgtAt` throws away.

Everything here is `copyPinFInstTgt`/`copyPinFInstTgtRefl` at the
field and `instMapPinOwn` at the own pin the field names; the two are
glued at the map's entry, which `instMapGroup` reads at the group's
base for both. -/
theorem NestedPinsRun.instTgtPin {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    {ci : ContainerInfo}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (CM : ContainerModeled mp₁'.base2 ci dJ)
    {ci0 : ContainerInfo}
    (hci0 : ConLeche.containerInfo? env (pinsS.getD (q₀ + 0) default).J = some ci0)
    (CM0 : ContainerModeled mp₁'.base2 ci0 dJ)
    {cvT : ConstantVal} {caps : IndCaps}
    (hfind : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD (q₀ + 0) default).J = some (.indInfo cvT caps))
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hrs : ((dJ.rss i').getD j []).getD l false = true)
    (hpinT : ¬ dJ.tgts i' j l < dJ.k) :
    ∃ (mm : List Nat) (σq : Nat),
      ConLeche.nestedInstMapAt env st (q₀ + 0) = some mm ∧
      mm[dJ.tgts i' j l - dJ.k]? = some σq ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + σq ∧
      σq < pinsS.length ∧
      (pinsS.getD σq default).J = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J ∧
      ∀ φ : Name → Nat,
        ((pinsS.getD σq default).u φ
            = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).u ((pinsS.getD (q₀ + 0) default).ψJ φ) ∧
          (pinsS.getD σq default).Ids φ
            = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ids ((pinsS.getD (q₀ + 0) default).ψJ φ)) ∧
        PinCorr ((D).targetView mp₁'.base2.acval φ) mp₁'.base2.acval dJ
          ((pinsS.getD (q₀ + 0) default).ψJ φ) ((pinsS.getD (q₀ + 0) default).Ds φ)
          cvT.levelParams ((pinsS.getD (q₀ + 0) default).lvls) (p.k + σq)
          (dJ.tgts i' j l - dJ.k) := by
  classical
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨cvT', caps', cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  -- `rss` is the two arms
  have hksl : l < (dJ.ksF i' j).length := by rw [hCD.ksLen]; exact hlF
  have hrr : (dJ.ksF i' j).getD l .ordinary = .recursive
      ∨ (dJ.ksF i' j).getD l .ordinary = .reflexive := by
    have h := hrs
    rw [show (dJ.rss i').getD j [] = rsOf (dJ.ksF i' j) from rssOfK_getD hjlt,
      rsOf_getD hksl, decide_eq_true_eq] at h
    exact h
  have hCMf : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ := by
    intro ciJ hciJ
    obtain rfl : ciJ = ci := Option.some.inj (hciJ.symm.trans hciP)
    exact CM
  -- K.61 at the field, on whichever arm, and the block target above `p.k`
  obtain ⟨mm', hmap', hval⟩ : ∃ mm : List Nat,
      ConLeche.nestedInstMapAt env st (q₀ + i') = some mm ∧
      mm.getD (dJ.tgts i' j l - dJ.k) st.pins.length
        = ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k := by
    rcases hrr with hrec | hrefl
    · exact R.copyPinFInstTgt SF S hPD hkindsRun hi' hgb hCMf hj hlF hrec hpinT
    · exact R.copyPinFInstTgtRefl SF S hPD hkindsRun hi' hgb hCMf hj hlF hrefl hpinT
  have hge : p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 := by
    rcases hrr with hrec | hrefl
    · exact (R.copyPinFKind SF S hPD hkindsRun hi' hgb hCMf hj hlF hrec hpinT).2
    · exact (R.copyPinFKindRefl SF S hPD hkindsRun hi' hgb hCMf hj hlF hrefl hpinT).2
  -- the map is the GROUP's, and it has an entry at this own pin
  have hmm0 : ConLeche.nestedInstMapAt env st (q₀ + 0) = some mm' := by
    rw [NestedPinsRun.instMapGroup SF S hPD S.kpos hi' hci0 hciP CM0 CM]; exact hmap'
  have hFssLen : ((dJ.Fss i' (fun _ => 0)).getD j []).length = cAJ.2 :=
    hI.Fss_length hj (fun _ => 0)
  have hqq : dJ.tgts i' j l - dJ.k < dJ.nPins :=
    CM.reps.tgt_pin_lt hik hj l (by rw [hFssLen]; exact hlF) hpinT
  obtain ⟨mm₂, σq, hmapAt, hmmqK, hσlt, hJeq, hrest⟩ :=
    R.instMapPinOwn SF S hPD S.kpos hci0 CM0 hqq hfind
  have hmmEq : mm₂ = mm' := Option.some.inj (hmapAt.symm.trans hmm0)
  rw [hmmEq] at hmmqK
  have hdef : List.getD mm' (dJ.tgts i' j l - dJ.k) st.pins.length = σq := by
    rw [List.getD_eq_getElem?_getD, hmmqK]; rfl
  exact ⟨mm', σq, hmm0, hmmqK, by rw [hdef] at hval; omega, hσlt, hJeq, hrest⟩

/-- **`hstgt` AT THE RUN, AT BOTH ARMS** (task #315 WIDE (3′)): a
container-RECURSIVE field of a pin's container whose target is one of
the container's OWN PINS lands, in the copy, on the block pin the
INSTANCE MAP names — whatever tower the field's domain wears.

`rss = true` is `.recursive ∨ .reflexive` (`rsOf`), which is exactly
the two arms: `copyPinFInstTgt` on the first, `copyPinFInstTgtRefl` on
the second.  The map is read at the GROUP's base rather than at the
member the field belongs to (`instMapGroup`), because the assembly's
`σ` is one function of the container's classes while K.61's map is
keyed by a block pin.

The `getD` default moves with it: the map has an entry at every own
pin of the container (`instMapPinOwn`), so `0` and `st.pins.length`
agree at this index, and the `- p.k` of K.61's own statement is
undone by `copyPinFKind`'s `p.k ≤ t`.  This is `instTgtPin` with the
pin projected away. -/
theorem NestedPinsRun.instTgtAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    {ci : ContainerInfo}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (CM : ContainerModeled mp₁'.base2 ci dJ)
    {ci0 : ContainerInfo}
    (hci0 : ConLeche.containerInfo? env (pinsS.getD (q₀ + 0) default).J = some ci0)
    (CM0 : ContainerModeled mp₁'.base2 ci0 dJ)
    {cvT : ConstantVal} {caps : IndCaps}
    (hfind : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD (q₀ + 0) default).J = some (.indInfo cvT caps))
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hrs : ((dJ.rss i').getD j []).getD l false = true)
    (hpinT : ¬ dJ.tgts i' j l < dJ.k) :
    ∃ mm : List Nat, ConLeche.nestedInstMapAt env st (q₀ + 0) = some mm ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0
        = p.k + mm.getD (dJ.tgts i' j l - dJ.k) 0 := by
  obtain ⟨mm, σq, hmm0, hmmqK, htg, -, -, -⟩ :=
    R.instTgtPin SF S hPD hkindsRun hi' hgb hciP CM hci0 CM0 hfind hj hlF hrs hpinT
  refine ⟨mm, hmm0, ?_⟩
  rw [htg, List.getD_eq_getElem?_getD, hmmqK]
  rfl

/-- **`houtσ` AT THE RUN, OVER BOTH HALVES OF THE INSTANCE** (task
#315 WIDE (3′), K.62 and K.66 consumed): a container-ORDINARY field
whose COPY the auxiliary block classifies recursive-or-reflexive lands
on no class of the container's instance at all — neither one of its
own pins (K.62, the map's image) nor one of its members (K.66, the
mint group).

The three cases are the three ways a class can be missed.  A target
BELOW `p.k` is a member of the block being installed, and every value
of `σ` is a block PIN, so nothing to prove.  A MEMBER class of the
container is the group's own mimic `p.k + q₀ + c` with `c < kJ`, which
K.66's disjunction excludes.  A PIN class is `p.k + mm.getD _ 0`, and
the map's entry at it is a member of the list
(`instMapPinOwn`), so K.62's `contains … = false` excludes it. -/
theorem NestedPinsRun.instOutAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    {ci : ContainerInfo}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (CM : ContainerModeled mp₁'.base2 ci dJ)
    {ci0 : ContainerInfo}
    (hci0 : ConLeche.containerInfo? env (pinsS.getD (q₀ + 0) default).J = some ci0)
    (CM0 : ContainerModeled mp₁'.base2 ci0 dJ)
    {cvT : ConstantVal} {caps : IndCaps}
    (hfind : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD (q₀ + 0) default).J = some (.indInfo cvT caps))
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hord : ((dJ.rss i').getD j []).getD l false = false)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true) :
    ∃ mm : List Nat, ConLeche.nestedInstMapAt env st (q₀ + 0) = some mm ∧
      ¬ ∃ c, c < dJ.k + dJ.nPins ∧
        (if c < dJ.k then p.k + q₀ + c else p.k + mm.getD (c - dJ.k) 0)
          = ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 := by
  classical
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨cvT', caps', cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hksl : l < (dJ.ksF i' j).length := by rw [hCD.ksLen]; exact hlF
  -- the container's field is ORDINARY: `rss` false rules the other two out
  have hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary := by
    have h := hord
    rw [show (dJ.rss i').getD j [] = rsOf (dJ.ksF i' j) from rssOfK_getD hjlt,
      rsOf_getD hksl] at h
    have hne : ¬ ((dJ.ksF i' j).getD l .ordinary = .recursive
        ∨ (dJ.ksF i' j).getD l .ordinary = .reflexive) := by
      intro hc; rw [decide_eq_true hc] at h; exact nomatch h
    rcases hCD.opened.kinds l (by rw [← hCD.ksLen]; exact hksl) with ho | hr | hrf
    · exact ho
    · exact absurd (Or.inl hr) hne
    · exact absurd (Or.inr hrf) hne
  have hCMf : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ := by
    intro ciJ hciJ
    obtain rfl : ciJ = ci := Option.some.inj (hciJ.symm.trans hciP)
    exact CM
  by_cases hge : p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0
  · obtain ⟨mm', hmap', hcon, hgrpOut⟩ :=
      R.copyOrdFOutside SF S hPD hkindsRun hi' hgb hCMf hj hlF hordC hrss hge
    have hmm0 : ConLeche.nestedInstMapAt env st (q₀ + 0) = some mm' := by
      rw [NestedPinsRun.instMapGroup SF S hPD S.kpos hi' hci0 hciP CM0 CM]; exact hmap'
    refine ⟨mm', hmm0, ?_⟩
    rintro ⟨c, hclt, hceq⟩
    by_cases hcm : c < dJ.k
    · -- a MEMBER class: K.66's disjunction
      rw [if_pos hcm] at hceq
      have hck : c < kJ := by rw [← S.kEq]; exact hcm
      omega
    · -- a PIN class: K.62's `contains`
      rw [if_neg hcm] at hceq
      have hqq : c - dJ.k < dJ.nPins := by omega
      obtain ⟨mm₂, σq, hmapAt, hmmqK, -, -, -⟩ :=
        R.instMapPinOwn SF S hPD S.kpos hci0 CM0 hqq hfind
      have hmmEq : mm₂ = mm' := Option.some.inj (hmapAt.symm.trans hmm0)
      rw [hmmEq] at hmmqK
      have hval : List.getD mm' (c - dJ.k) 0 = σq := by
        rw [List.getD_eq_getElem?_getD, hmmqK]; rfl
      have hmem : σq ∈ mm' := List.mem_of_getElem? hmmqK
      rw [hval] at hceq
      have hcontra : mm'.contains
          (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k) = true := by
        refine List.contains_iff_exists_mem_beq.mpr ⟨σq, hmem, ?_⟩
        simp only [beq_iff_eq]
        omega
      rw [hcon] at hcontra
      exact nomatch hcontra
  · -- the target is a MEMBER of the block being installed, and every
    -- value of `σ` is a block PIN
    have hq0 : q₀ + 0 < st.pins.length := by
      rw [← SF.pinsLen]; have := S.seg; have := S.kpos; omega
    obtain ⟨mm', hmap'⟩ : ∃ mm : List Nat,
        ConLeche.nestedInstMapAt env st (q₀ + 0) = some mm := by
      cases hms : ConLeche.nestedInstMaps env st with
      | none =>
        have hK61 := R.hK61
        unfold ConLeche.nestedInstMapOk ConLeche.nestedInstMapOkAt at hK61
        rw [hms] at hK61; simp at hK61
      | some maps =>
        obtain ⟨m, -, hm⟩ := ConLeche.mapM_option_inv hms (q₀ + 0) (q₀ + 0)
          (by rw [List.getElem?_range (by omega)])
        exact ⟨m, hm⟩
    refine ⟨mm', hmap', ?_⟩
    rintro ⟨c, hclt, hceq⟩
    by_cases hcm : c < dJ.k
    · rw [if_pos hcm] at hceq; omega
    · rw [if_neg hcm] at hceq; omega

omit R SF in
/-- **THE GROUP'S CONTAINER MEMBER AT `i'` IS NAMED AT ANY MEMBER OF THE
GROUP** (task #315 WIDE (3), step 1(a)): `hordσ`'s preamble, extracted
so that the `ordTgt` row below spends it instead of copying it.

A clause keyed by the container's stored constructor names its member
at an ARBITRARY pin of the group (`i₀`), while a consumer holds the
record at its OWN pin (`i'`); both models `dJ`
(`NestedPinGroupSyn.modeled`) and a container is determined by its
member names and parameter count (`containerInfo?_eq_of_names`), so
the two records are one and the member's level parameters are the
clause's. -/
private theorem NestedPinGroupSyn.groupMemberLps {i₀ i' : Nat} (hi₀ : i₀ < kJ) (hi' : i' < kJ)
    {ciC : ContainerInfo} {Jm : ContainerMember} {lpsC : List Name}
    (hciC : ConLeche.containerInfo? env (pinsS.getD (q₀ + i₀) default).J = some ciC)
    (hJmC : ciC.members[i']? = some Jm) (hlpsE : Jm.lps = lpsC)
    {ciP : ContainerInfo}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciP)
    {Jm' : ContainerMember} (hJm' : ciP.members[i']? = some Jm') : Jm'.lps = lpsC := by
  have CMP := S.modeled i' hi' ciP hciP
  have CMC := S.modeled i₀ hi₀ ciC hciC
  obtain rfl : ciP = ciC :=
    ConLeche.containerInfo?_eq_of_names hciP hciC (CMP.nP.symm.trans CMC.nP)
      (CMP.memberNames_eq.symm.trans CMC.memberNames_eq)
  obtain rfl : Jm' = Jm := Option.some.inj (hJm'.symm.trans hJmC)
  exact hlpsE

/-- **THE σ CLAUSE, ASSEMBLED AT ONE GROUP** (task #315 WIDE (3′)):
`PinGroupInst` from the four run halves and nothing else — `hroot` is
σ's own definition, `hσ`/`hmemσ`/`hidxσ` are `instMapSigmaFacts`,
`hstgt` is `instTgtAt` and `houtσ` is `instOutAt`.

σ is the kernel's instance map at the group's BASE pin, lifted over
the container's members by `hroot`:

    fun c => if c < dJ.k then p.k + q₀ + c else p.k + mm.getD (c - dJ.k) 0

and that it may be read at the base rather than at the member whose
field is in hand is `instMapGroup`, which the two target halves
already spend. -/
theorem NestedPinsRun.pinGroupInst_of {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds) :
    PinGroupInst (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
      (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
      (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
      (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) q₀ kJ dJ := by
  classical
  -- the pins of the group, their container records and their models
  have hqAt : ∀ i', i' < kJ → q₀ + i' < st.pins.length := by
    intro i' hi'; rw [← SF.pinsLen]; have := S.seg; omega
  have hci : ∀ i', i' < kJ → ∃ ci : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci ∧
      ContainerModeled mp₁'.base2 ci dJ := by
    intro i' hi'
    obtain ⟨hcname, -⟩ := SF.pinRec _ _ (hPD _ (hqAt i' hi')).pin
    obtain ⟨ci, hci0, -⟩ := (hPD _ (hqAt i' hi')).own
    have hciJ : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci := by
      rw [hcname]; exact hci0
    exact ⟨ci, hciJ, S.modeled i' hi' ci hciJ⟩
  obtain ⟨ci0, hci0, CM0⟩ := hci 0 S.kpos
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI0, -⟩ := S.stored 0 S.kpos
  -- the group's own instance map
  have hq0 : q₀ + 0 < st.pins.length := hqAt 0 S.kpos
  obtain ⟨mm, hmm⟩ : ∃ mm : List Nat, ConLeche.nestedInstMapAt env st (q₀ + 0) = some mm := by
    cases hms : ConLeche.nestedInstMaps env st with
    | none =>
      have hK61 := R.hK61
      unfold ConLeche.nestedInstMapOk ConLeche.nestedInstMapOkAt at hK61
      rw [hms] at hK61; simp at hK61
    | some maps =>
      obtain ⟨m, -, hm⟩ := ConLeche.mapM_option_inv hms (q₀ + 0) (q₀ + 0)
        (by rw [List.getElem?_range (by omega)])
      exact ⟨m, hm⟩
  obtain ⟨hrange, hmem, hidx⟩ := R.instMapSigmaFacts SF S hPD hci hfind hmm
  have hgb : ∀ i', i' < kJ → (pinAtE st (q₀ + i')).grpBase = q₀ := by
    intro i' hi'
    have h := (S.grp i' hi').1
    rw [← pinAtE_eq] at h
    exact h
  refine ⟨fun c => if c < dJ.k then p.k + q₀ + c else p.k + mm.getD (c - dJ.k) 0,
    fun c hc => if_pos hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hσ`
    intro c hc
    dsimp only
    by_cases hcm : c < dJ.k
    · rw [if_pos hcm]
      have hck : c < kJ := by rw [← S.kEq]; exact hcm
      have := S.seg
      omega
    · rw [if_neg hcm]
      have := hrange (c - dJ.k) (by omega)
      omega
  · -- `hmemσ`
    intro c c' hcm hc'm hc'
    dsimp only
    rw [if_pos hcm, if_neg hc'm]
    have := hmem c (c' - dJ.k) hcm (by omega)
    omega
  · -- `hidxσ`
    intro c c' hcm hc hc'm hc' heq ψ ρp
    dsimp only at heq
    rw [if_neg hcm, if_neg hc'm] at heq
    have hv : mm.getD (c - dJ.k) 0 = mm.getD (c' - dJ.k) 0 := by omega
    have h := hidx (c - dJ.k) (c' - dJ.k) (by omega) (by omega) hv ψ ρp
    rw [show dJ.k + (c - dJ.k) = c from by omega, show dJ.k + (c' - dJ.k) = c' from by omega] at h
    exact h
  · -- `hstgt`
    intro ψ i' hi' j hj l hl hrs hpinT
    dsimp only
    obtain ⟨cAJ, hjA⟩ : ∃ cAJ, (dJ.ctorsM i')[j]? = some cAJ :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := S.stored i' hi'
    have hlF : l < cAJ.2 := by rw [← hI'.Fss_length hjA ((pinsS.getD q₀ default).ψJ ψ)]; exact hl
    obtain ⟨ci, hciP, CM⟩ := hci i' hi'
    obtain ⟨mm', hmm', hval⟩ :=
      R.instTgtAt SF S hPD hkindsRun hi' (hgb i' hi') hciP CM hci0 CM0 hfind hjA hlF hrs hpinT
    obtain rfl : mm' = mm := Option.some.inj (hmm'.symm.trans hmm)
    rw [hval, if_neg hpinT]
  · -- `houtσ`
    intro ψ i' hi' j hj l hl hord hrss
    dsimp only
    obtain ⟨cAJ, hjA⟩ : ∃ cAJ, (dJ.ctorsM i')[j]? = some cAJ :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := S.stored i' hi'
    have hlF : l < cAJ.2 := by rw [← hI'.Fss_length hjA ((pinsS.getD q₀ default).ψJ ψ)]; exact hl
    obtain ⟨ci, hciP, CM⟩ := hci i' hi'
    obtain ⟨mm', hmm', hout⟩ :=
      R.instOutAt SF S hPD hkindsRun hi' (hgb i' hi') hciP CM hci0 CM0 hfind hjA hlF hord hrss
    obtain rfl : mm' = mm := Option.some.inj (hmm'.symm.trans hmm)
    exact hout
  · -- `hpinσ`: `instTgtPin`, whose block pin is exactly `σ`'s value at
    -- this class — the map's entry at the container's own pin — with
    -- the pin data `instTgtAt` projects away.  `PinCorr`'s `Ds` clause
    -- IS the components' conjunct, because `targetView.Ds` at a pin
    -- class is that pin's own `Ds` (`BlockModel.targetView`).
    intro ψ i' hi' j hj l hl hrs hpinT
    dsimp only
    obtain ⟨cAJ, hjA⟩ : ∃ cAJ, (dJ.ctorsM i')[j]? = some cAJ :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := S.stored i' hi'
    have hlF : l < cAJ.2 := by rw [← hI'.Fss_length hjA ((pinsS.getD q₀ default).ψJ ψ)]; exact hl
    obtain ⟨ci, hciP, CM⟩ := hci i' hi'
    obtain ⟨mm', σq, hmm', hmmqK, -, hσlt, hJeq, hrest⟩ :=
      R.instTgtPin SF S hPD hkindsRun hi' (hgb i' hi') hciP CM hci0 CM0 hfind hjA hlF hrs hpinT
    obtain rfl : mm' = mm := Option.some.inj (hmm'.symm.trans hmm)
    refine ⟨σq, hσlt, ?_, hJeq, fun φ => ?_⟩
    · rw [if_neg hpinT, List.getD_eq_getElem?_getD, hmmqK]; rfl
    · obtain ⟨⟨hu, hIds⟩, hcorr⟩ := hrest φ
      refine ⟨hu, hIds, ?_⟩
      have hDs := hcorr.2.1
      show ((D).pinAt σq).Ds φ = _
      rw [show ((D).pinAt σq).Ds φ
          = ((D).targetView mp₁'.base2.acval φ).Ds ((D).k + σq) from by
        show _ = ((D).pinAt ((D).k + σq - (D).k)).Ds φ
        rw [Nat.add_sub_cancel_left]]
      exact hDs
  · -- `hownσ`: the same data at an ARBITRARY own pin, which is
    -- `instMapPinOwn` at the group's BASE member — the map is the
    -- group's (`instMapGroup`), so the base member's map is the one
    -- σ is built from
    intro x hx
    dsimp only
    obtain ⟨mm', σq, hmm', hmmqK, hσlt, hJeq, hrest⟩ :=
      R.instMapPinOwn SF S hPD S.kpos hci0 CM0 hx hfind
    obtain rfl : mm' = mm := Option.some.inj (hmm'.symm.trans hmm)
    refine ⟨σq, hσlt, ?_, hJeq, fun φ => ?_⟩
    · rw [if_neg (by omega : ¬ dJ.k + x < dJ.k), Nat.add_sub_cancel_left,
        List.getD_eq_getElem?_getD, hmmqK]
      rfl
    · obtain ⟨⟨hu, hIds⟩, hcorr⟩ := hrest φ
      refine ⟨hu, hIds, ?_⟩
      have hDs := hcorr.2.1
      show ((D).pinAt σq).Ds φ = _
      rw [show ((D).pinAt σq).Ds φ
          = ((D).targetView mp₁'.base2.acval φ).Ds ((D).k + σq) from by
        show _ = ((D).pinAt ((D).k + σq - (D).k)).Ds φ
        rw [Nat.add_sub_cancel_left]]
      exact hDs
  · -- `hordσ`: K.68's row, `instOrdSelfAt` with the two tables and the
    -- two member-name lists identified (`ownPinTerms_eq`, the block's
    -- own names)
    intro ψ i' hi' j hj l hl hrss cA bs rr dom lps hjA hstrip hdom
      lpsC i₀ hi₀ ciC Jm hciC hJmC hlpsE M us hhead
    obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := S.stored i' hi'
    have hlF : l < cA.2 := by rw [← hI'.Fss_length hjA ((pinsS.getD q₀ default).ψJ ψ)]; exact hl
    obtain ⟨ci, hciP, CM⟩ := hci i' hi'
    have hnames : (D).memberNames = p.memberNames := by
      show (fms.take p.k).map (·.cvTa.name) = p.memberNames
      rw [List.map_take, R.h.names]
      exact ConLeche.auxBlock_memberNames R.hfA R.helim R.hb
    rw [R.ownPinTerms_eq SF lps] at hhead ⊢
    rw [hnames]
    -- the guard's container is named at an ARBITRARY member of the
    -- group; it is THIS member's, because both model `dJ`
    -- (`NestedPinGroupSyn.modeled`) and a container is determined by
    -- its member names and parameter count
    have hlpsC : ∀ ciP : ContainerInfo,
        ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciP →
        ∀ Jm' : ContainerMember, ciP.members[i']? = some Jm' → Jm'.lps = lpsC :=
      fun ciP hciP' Jm' hJm' => S.groupMemberLps hi₀ hi' hciC hJmC hlpsE hciP' hJm'
    have hbase := R.instOrdSelfAt SF S hPD hkindsRun hi' (hgb i' hi') (fun ciJ hh => by
        rw [hciP] at hh; obtain rfl := Option.some.inj hh; exact CM)
      hjA hlF hrss hstrip hdom hlpsC hhead
    refine ⟨hbase.1, fun hnm => ?_⟩
    -- the STRENGTHENED arms give the answer POSITIVELY (task #315
    -- WIDE (3)): the head's container reads, and its own-pin term is
    -- in the block's table.  The matched entry's container IS the head
    -- `M`, and `pinNP` at that pin turns the `ContainerInfo`'s own
    -- parameter count into the clause's `nPJ`.
    obtain ⟨ciM, z, hciM, hfi, htgz⟩ := hbase.2 hnm
    obtain ⟨hzlt, hm₀, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hzS : z < pinsS.length := by
      have : z < (ConLeche.nestedPinTermsSelf p st).length := hzlt
      unfold ConLeche.nestedPinTermsSelf at this
      rw [SF.pinsLen]; simpa using this
    have hzD : z < (D).nPins := by show z < pinsS.length; exact hzS
    have hentry : (ConLeche.nestedPinTermsSelf p st).getD z default
        = ((D).pinAt z).ownAt b.nP lps (lps.map Level.param)
            (ConLeche.containerParamOpeners b.nP) := by
      rw [← R.ownPinTerms_eq SF lps]
      unfold BlockModel.ownPinTerms
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hzD]
      rfl
    have hterm : (((D).pinAt z).ownAt b.nP lps (lps.map Level.param)
        (ConLeche.containerParamOpeners b.nP) == Expr.mkAppN
          (ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
            (q₀ + i') l dom.1).getAppFn
          ((ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
            (q₀ + i') l dom.1).getAppArgs.take ciM.nP)) = true := by
      rw [← hentry, show (ConLeche.nestedPinTermsSelf p st).getD z default
          = (ConLeche.nestedPinTermsSelf p st)[z]'hzlt from by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hzlt]; rfl]
      exact hm₀
    have hJM : ((D).pinAt z).J = M := by
      have hfn := congrArg Expr.getAppFn (of_decide_eq_true hterm)
      unfold ConLeche.Model.PinSyn.ownAt at hfn
      rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN, hhead] at hfn
      exact (Expr.const.inj hfn).1
    obtain ⟨ciz, hciz, -⟩ := (hPD z (by rw [← SF.pinsLen]; exact hzS)).own
    have hcizJ : ConLeche.containerInfo? env ((D).pinAt z).J = some ciz := by
      show ConLeche.containerInfo? env (pinsS.getD z default).J = some ciz
      rw [(SF.pinRec z _ (hPD z (by rw [← SF.pinsLen]; exact hzS)).pin).1]; exact hciz
    have hnPz : ((D).pinAt z).nPJ = ciz.nP := by
      obtain ⟨q₀z, kJz, iz, hqez, hiz, Sz⟩ := SF.groupsAt dsR xFvsR z hzS ciz hcizJ
      have hp := Sz.pinNP iz hiz
      have hm := (Sz.modeled iz hiz ciz (by
        show ConLeche.containerInfo? env (pinsS.getD (q₀z + iz) default).J = some ciz
        rw [← hqez]; exact hcizJ)).nP
      show (pinsS.getD z default).nPJ = ciz.nP
      rw [hqez]
      exact hp.trans hm
    have hcizM : ConLeche.containerInfo? env ((D).pinAt z).J = some ciM := by
      rw [hJM]; exact hciM
    obtain rfl : ciz = ciM := Option.some.inj (hcizJ.symm.trans hcizM)
    exact ⟨z, hzD, by rw [hnPz]; exact hfi, htgz⟩

/-! ## The owner's half of the two copies' field-data tie -/

omit [SetTheory V] R SF S in
/-- **A CONSTANT HEAD SURVIVES `instantiateList`** (task #315 WIDE (3),
step 1(a)): `Expr.getAppFn_instantiate1_const` for the list form, and
what carries `ordTargetDomL`'s head to `ordTargetDom`'s — the step the
kernel's own K.67/K.68 row takes as a second hypothesis because it has
no model to derive it in. -/
private theorem getAppFn_instantiateList_const {vs : List Expr} {n : Name} {us : List Level} :
    ∀ {e : Expr} {d : Nat}, e.getAppFn = .const n us →
      (e.instantiateList vs d).getAppFn = .const n us := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro d h
    simp only [Expr.instantiateList, Expr.getAppFn]
    exact ihf (by simpa only [Expr.getAppFn] using h)
  | const m vs' => intro d h; simpa only [Expr.instantiateList] using h
  | _ => intro d h; simp [Expr.getAppFn] at h

omit S in
/-- **A COPY'S RECORDED INDEX EXPRESSIONS ARE AS MANY AS ITS TARGET
PIN'S INDICES** (task #315 WIDE (3), step 3): at a field of an
auxiliary constructor whose kind is recursive or reflexive and whose
recorded target is the copy former of pin `z`, the block's recorded
index expressions at that field are as many as the pin's container has
indices.

It is the LENGTH the two copies' field-data tie is split at: the tie
concludes an equation between two applications, and `AnnotTerm.mkAppN`
is injective only at equal arity — the head container's parameter
counts come from `hownσ`, and this is the other half, ON BOTH SIDES.
The block's side reads it at `GroupFacts.ordRead`; the OWNER's side
reads it at the `PinShapes` conjunct this same run fact discharges
(`NestedPinGroupSyn.ordTgt`), because the owner's `Eiss` at its own
install ARE this list.

Nothing here is nested-specific: `MutualCtorDataI.eisLen` (and its
reflexive twin) already say a recursive field's readings are as many
as its TARGET MEMBER's indices, and the auxiliary block's member
`p.k + z` is pin `z`'s copy, whose index count is the pin's
(`NestedPinSynFacts.pinNIdx`). -/
theorem NestedPinsRun.copyEisLen {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (ψ : Name → Nat) {G l z : Nat} {cA : ConstantVal × Nat}
    (hcA : ctorsA[G]? = some cA) (hlF : l < cA.2)
    (hk : kindAt (mutKsOf kinds G) l = RecFieldKind.recursive ∨
      kindAt (mutKsOf kinds G) l = RecFieldKind.reflexive)
    (hz : z < pinsS.length)
    (htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD G []).getD l 0
      = p.k + z) :
    (((mutEiss0 ctorsA.length eissF ψ).getD G []).getD l []).length = ((D).pinAt z).nIdx := by
  have hGlt : G < ctorsA.length := (List.getElem?_eq_some_iff.mp hcA).1
  have hnFs : l < mutNFOf ctorsA G := by
    show l < (ctorsA.getD G default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlF
  have htgA : tgtAt (mutKsOf kinds G) l = p.k + z := by
    rw [← mutTgts_getD hGlt hnFs]; exact htg
  rw [mutEiss0_getD hGlt]
  have hlen : ((eissF G ψ).getD l []).length
      = mutualNIdxOf b.members3 (tgtAt (mutKsOf kinds G) l) := by
    rcases hk with hk | hk
    · exact (R.h.CD G _ hcA).eisLen ψ l hk hlF
    · exact (R.h.CD G _ hcA).eisLenRefl ψ l hk hlF
  rw [hlen, htgA]
  have hzst : z < st.pins.length := by rw [← SF.pinsLen]; exact hz
  obtain ⟨fM, -, hfM, -, -, -, -, -⟩ := R.groupCopyFormer hPD hzst
  have hfMd : fms.getD (p.k + z) default = fM := by
    rw [List.getD_eq_getElem?_getD, hfM]; rfl
  have hp := SF.pinNIdx z hz
  rw [hfMd] at hp
  rw [(R.h.memT _ _ hfM).2]
  exact hp

/-- **A REWRITTEN ORDINARY FIELD'S TARGET IS A PIN, NOT A MEMBER**
(task #315 WIDE (3), step 1): at a field the pin's container calls
ORDINARY and the block's rewrite made recursive, whose recomputed head
`K` is a constant DECLARED IN `env`, the recorded target is at least
`p.k` — the bound K.67's guard and `GroupFacts.ordRead`'s assume.

It is K.68's row (`instOrdSelfAt`) and nothing else: that row is the
one WITHOUT the `p.k ≤ t` bound in its guard, and it splits on whether
the recomputation's head is a MEMBER NAME of the block.  A member
answer makes the target a member index; but the block's member names
are fresh in `env` (`membersFresh`, `checkConstantVal`'s duplicate
gate) and `K` is declared there, so that arm is empty and the other
arm produces the target as `p.k + z`.

**K.67 cannot serve and neither can `GroupFacts.ordRead`**: the bound
is literally part of K.67's kernel guard
(`nestedOrdTargetAt`, `(r == .recursive || r == .reflexive) && p.k ≤ t`)
and `ordRead`'s is the same fact negated, so both presuppose what this
row produces.  `CopyCtorShape.ordF`'s right arm bounds the target only
from ABOVE.  The declaredness of `K` is the consumer's to supply: at
the correspondence it is the OWNER's own row that gives it — a head
that is one of the owner container's members, or the container of one
of its own pins, is a stored inductive either way. -/
theorem NestedPinsRun.ordGeAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j l : Nat}
    (hord : ((dJ.rss i').getD j []).getD l false = false)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    {cA : ConstantVal × Nat} {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    {dom : Expr × ConLeche.BinderMeta} (lpsC : List Name)
    (hjA : (dJ.ctorsM i')[j]? = some cA)
    (hlF : l < cA.2)
    (hstrip : cA.1.type.stripPis (dJ.nP + cA.2) = some (bs, rr))
    (hdom : bs[dJ.nP + l]? = some dom)
    {i₀ : Nat} (hi₀ : i₀ < kJ) {ciC : ContainerInfo} {Jm : ContainerMember}
    (hciC : ConLeche.containerInfo? env (pinsS.getD (q₀ + i₀) default).J = some ciC)
    (hJmC : ciC.members[i']? = some Jm) (hlpsE : Jm.lps = lpsC)
    {K : Name} {usK : List Level}
    (hfin : (Expr.instantiateLevelParams lpsC (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn
      = .const K usK)
    (hfindK : (env.find? K).isSome = true) :
    p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 := by
  classical
  obtain ⟨cc, J, ci, cI₀, cAB, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj,
    hcAB, hbc, hnFB⟩ := R.ctorPair SF S hPD hi' hjA
  obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := S.stored i' hi'
  have hpinAt : ∀ n : Nat, ((D).pinAt n) = pinsS.getD n default := fun _ => rfl
  rw [hpinAt] at hI'
  have hcimem : i' < ci.members.length := by
    have CMci := S.modeled i' hi' ci (by rw [hpinAt]; exact hciP)
    have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
    rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ := ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJeq : J = J₂ := by
    have CMci := S.modeled i' hi' ci (by rw [hpinAt]; exact hciP)
    have hJ₂name : J₂.name = J.name := by
      rw [← (CMci.member i' J₂ hJ₂).1, hJname]
      exact hI'.member
    exact ConLeche.containerInfo?_member_det hciP hciP rfl hJmem (List.mem_of_getElem? hJ₂)
      hJ₂name.symm
  have hlpsJ : J.lps = lpsC := by
    rw [hJeq]
    exact S.groupMemberLps hi₀ hi' hciC hJmC hlpsE hciP hJ₂
  have hqst : q₀ + i' < st.pins.length := by rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hLv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have h := congrArg Expr.getAppFn hpin
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at h
    exact (ConLeche.Expr.const.inj h).2
  have hlvlsT : ConLeche.ordTargetLvls (ConLeche.nestedPinTermsSelf p st) (q₀ + i')
      = (pinsS.getD (q₀ + i') default).lvls := by
    unfold ConLeche.ordTargetLvls
    rw [ConLeche.nestedPinTermsSelf_shape PD.pin PD.pinEq, Expr.getAppFn_mkAppN, hLv]
    rfl
  have hDL : ConLeche.ordTargetDomL J.lps (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1
      = Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 := by
    unfold ConLeche.ordTargetDomL; rw [hlvlsT]
  have hfinJ : (Expr.instantiateLevelParams J.lps
      (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn = .const K usK := by
    rw [hlpsJ]; exact hfin
  have hstripId : ConLeche.stripDomPis (Expr.instantiateLevelParams J.lps
      (pinsS.getD (q₀ + i') default).lvls dom.1)
      = Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 := by
    cases hd : Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 with
    | forallE ty bo bm =>
      rw [hd] at hfinJ
      exact nomatch (hfinJ : Expr.forallE ty bo bm = Expr.const K usK)
    | _ => rfl
  have hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary := by
    obtain ⟨-, -, hCD⟩ := hI'.ctors i' j cA hI'.memberLt hjA
    have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hjA).1
    have hksl : l < (dJ.ksF i' j).length := by rw [hCD.ksLen]; exact hlF
    have hh := hord
    rw [show (dJ.rss i').getD j [] = rsOf (dJ.ksF i' j) from rssOfK_getD hjlt,
      rsOf_getD hksl] at hh
    have hne : ¬ ((dJ.ksF i' j).getD l .ordinary = .recursive
        ∨ (dJ.ksF i' j).getD l .ordinary = .reflexive) := by
      intro hc; rw [decide_eq_true hc] at hh; exact nomatch hh
    rcases hCD.opened.kinds l (by rw [← hCD.ksLen]; exact hksl) with ho | hr | hrf
    · exact ho
    · exact absurd (Or.inl hr) hne
    · exact absurd (Or.inr hrf) hne
  have hgbE : (pinAtE st (q₀ + i')).grpBase = q₀ := by
    obtain ⟨hgb', -⟩ := S.grp i' hi'
    rw [← pinAtE_eq] at hgb'
    exact hgb'
  have hstripDL : ConLeche.stripDomPis (ConLeche.ordTargetDomL J.lps
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1)
      = ConLeche.ordTargetDomL J.lps (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1 := by
    rw [hDL]; exact hstripId
  have hhead : (ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
      (q₀ + i') l dom.1).getAppFn = .const K usK := by
    rw [← hlpsJ]
    unfold ConLeche.ordTargetDom
    rw [hstripDL]
    refine getAppFn_instantiateList_const (e := ConLeche.ordTargetDomL J.lps
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1) ?_
    rw [hDL]; exact hfinJ
  have hbase := R.instOrdSelfAt SF S hPD R.h.classify hi' hgbE
    (fun ciJ hh => by
      rw [hciP] at hh
      obtain rfl := Option.some.inj hh
      exact S.modeled i' hi' ci hciP)
    hjA hlF hrss hstrip hdom
    (fun _ hciP' Jm' hJm' => S.groupMemberLps hi₀ hi' hciC hJmC hlpsE hciP' hJm') hhead
  cases hfi : p.memberNames.findIdx? (· == K) with
  | some mm =>
    exfalso
    obtain ⟨hmmlt, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hmem : K ∈ p.memberNames := by
      have h := List.getElem_mem hmmlt
      rwa [eq_of_beq hbeq] at h
    rw [R.membersFresh K hmem] at hfindK
    exact nomatch hfindK
  | none =>
    obtain ⟨ciM, z, -, -, htgz⟩ := hbase.2 hfi
    omega

/-- **THE OWNER'S HALF OF THE TWO COPIES' FIELD-DATA TIE, AT THE RUN**
(task #315 WIDE (3), step 1(a)): at a field the pin's container calls
ORDINARY and the block's rewrite made recursive, whose block target is
NOT a member of the block, the owner's own recomputation of the field's
target reads as an application whose arguments past the head
container's parameters are the copy's index expressions
(`OrdTargetRead`).

The two wrappers `copyOrdFRightPinOrdTargetReadAt` and `…AtRefl` are
the content; this is the dispatch and the tables.  The dispatch is by
the copy field's KIND, which the block's `blkRss` bit gives
(`blkRss_getD`/`rsOf_getD_iff`), and the wrappers' positivity run is
`copyOrdFRightPinRun` at either kind.  The tables are identified as
`hordσ`'s are: the container's own-pin table is the block's
(`ownPinTerms_eq`), the clause's `lpsC` is the group's member's
(`groupMemberLps`), and `dJ.nP` is the container's (`ctorsOf`).

**THE GUARD IS THE STORED DOMAIN'S HEAD AT THE PIN'S LEVELS** (`hfin`)
and not `ordTargetDom`'s: `instSeq_getAppFn_const` carries a constant
head forward through the components' instantiation and not back.  A
constant-headed domain is not a `Π`, so the reflexive arm's tower is
empty here and the cut is the field's own `l` — the statement is
carried at the general cut anyway, so that relaxing the guard to the
stripped head later moves nothing else.

**THE HEAD'S CONTAINER-HOOD IS PRODUCED HERE AND NOT CONSUMED** (task
#315 WIDE (3), step 1(a) part 3): the consumer of this row — the
`PinShapes` clause it is carried to — may not take an environment fact
as a hypothesis, so the container record `ciK` the statement's cut
needs is EXISTENTIAL and its `containerInfo?` a conclusion.  Its
source is the instance map's own row `instOrdSelfAt` (K.67/K.68): at a
container-ordinary field the block's rewrite made recursive, that row
splits on whether the recomputation's head is a member of the block —
excluded here by the target guard `hpinT`, since a member answer makes
the target a member index — and on the other arm it PRODUCES both the
head's container record and the own-pin position of the target.  K.60
and K.63 cannot serve: their guard is a container-RECURSIVE field, and
both are silent where `containerInfo?` answers `none`. -/
theorem NestedPinsRun.ordTgtReadAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp)
    {i' : Nat} (hi' : i' < kJ) {j l : Nat}
    (hl : l < ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j []).length)
    (hord : ((dJ.rss i').getD j []).getD l false = false)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    (hpinT : ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    {cA : ConstantVal × Nat} {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    {dom : Expr × ConLeche.BinderMeta} (lps lpsC : List Name)
    (hjA : (dJ.ctorsM i')[j]? = some cA)
    (hstrip : cA.1.type.stripPis (dJ.nP + cA.2) = some (bs, rr))
    (hdom : bs[dJ.nP + l]? = some dom)
    {i₀ : Nat} (hi₀ : i₀ < kJ) {ciC : ContainerInfo} {Jm : ContainerMember}
    (hciC : ConLeche.containerInfo? env (pinsS.getD (q₀ + i₀) default).J = some ciC)
    (hJmC : ciC.members[i']? = some Jm) (hlpsE : Jm.lps = lpsC)
    {K : Name} {usK : List Level}
    (hfin : (Expr.instantiateLevelParams lpsC (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn
      = .const K usK) :
    ∃ z : Nat, z < pinsS.length ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + z ∧
      (((mutEiss0 ctorsA.length eissF ψ).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).length = ((D).pinAt z).nIdx ∧
      ((D).pinAt z).J = K ∧
      (∀ ci : ContainerInfo, ConLeche.containerInfo? env K = some ci →
        ((D).pinAt z).nPJ = ci.nP) ∧
      (∀ ci : ContainerInfo, ConLeche.containerInfo? env K = some ci →
        ∃ mem ∈ ci.members, mem.name = K ∧
          ∃ (bsz : List (Expr × ConLeche.BinderMeta)) (sz : Level),
            mem.type.stripPis (ci.nP + ((D).pinAt z).nIdx) = some (bsz, .sort sz)) ∧
      OrdTargetRead (V := V) mp₁'.base2.acval (ENV₁) ψ ρp b.nP l
        ((pinsS.getD q₀ default).Ds ψ)
        ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j [])
        (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
        (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
        ((D).pinAt z).nPJ lpsC dJ.nP (q₀ + i') ((D).ownPinTerms lps) dom.1 := by
  classical
  -- the container record at this pin, its member and the block's own constructor
  obtain ⟨cc, J, ci, cI₀, cAB, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj,
    hcAB, hbc, hnFB⟩ := R.ctorPair SF S hPD hi' hjA
  obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := S.stored i' hi'
  have hpinAt : ∀ n : Nat, ((D).pinAt n) = pinsS.getD n default := fun _ => rfl
  rw [hpinAt] at hI'
  have hlF : l < cA.2 := by rw [← hI'.Fss_length hjA ((pinsS.getD q₀ default).ψJ ψ)]; exact hl
  -- the copy's field is recursive or reflexive
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcAB).1
  have hrr : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.recursive ∨
      kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.reflexive := by
    rw [blkRss_getD hGlt] at hrss
    have hlt := rsOf_getD_true_lt hrss
    rw [rsOf_getD_iff hlt, kindsOf_getD'] at hrss
    exact hrss
  -- the tables: the container's `nP`, its member's level parameters, the own-pin table
  have hnPci : dJ.nP = ci.nP := (S.ctorsOf i' hi' ci J (by rw [hpinAt]; exact hciP) hJmem
    (by rw [hpinAt]; exact hJname)).2
  have hcimem : i' < ci.members.length := by
    have CMci := S.modeled i' hi' ci (by rw [hpinAt]; exact hciP)
    have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
    rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ := ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJeq : J = J₂ := by
    have CMci := S.modeled i' hi' ci (by rw [hpinAt]; exact hciP)
    have hJ₂name : J₂.name = J.name := by
      rw [← (CMci.member i' J₂ hJ₂).1, hJname]
      exact hI'.member
    exact ConLeche.containerInfo?_member_det hciP hciP rfl hJmem (List.mem_of_getElem? hJ₂)
      hJ₂name.symm
  have hlpsJ : J.lps = lpsC := by
    rw [hJeq]
    exact S.groupMemberLps hi₀ hi' hciC hJmC hlpsE hciP hJ₂
  -- the group's shared level assignment and components
  have h0 : q₀ + 0 = q₀ := Nat.add_zero q₀
  have hψ : (pinsS.getD q₀ default).ψJ ψ = (pinsS.getD (q₀ + i') default).ψJ ψ := by
    have h := S.ψJEq 0 i' S.kpos hi' ψ
    rw [hpinAt, hpinAt, h0] at h
    exact h
  have hDs : (pinsS.getD q₀ default).Ds ψ = (pinsS.getD (q₀ + i') default).Ds ψ := by
    have a := S.sameDs 0 S.kpos ψ
    have bb := S.sameDs i' hi' ψ
    rw [hpinAt, hpinAt, h0] at a
    rw [hpinAt, hpinAt] at bb
    rw [a, bb]
  -- the own-pin table is the run's, and the recomputation's levels are the pin's
  have hqst : q₀ + i' < st.pins.length := by rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hLv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have h := congrArg Expr.getAppFn hpin
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at h
    exact (ConLeche.Expr.const.inj h).2
  have hlvlsT : ConLeche.ordTargetLvls (ConLeche.nestedPinTermsSelf p st) (q₀ + i')
      = (pinsS.getD (q₀ + i') default).lvls := by
    unfold ConLeche.ordTargetLvls
    rw [ConLeche.nestedPinTermsSelf_shape PD.pin PD.pinEq, Expr.getAppFn_mkAppN, hLv]
    rfl
  have hDL : ConLeche.ordTargetDomL J.lps (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1
      = Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 := by
    unfold ConLeche.ordTargetDomL; rw [hlvlsT]
  -- a constant-headed domain is not a `Π`, so the tower is empty
  have hfinJ : (Expr.instantiateLevelParams J.lps
      (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn = .const K usK := by
    rw [hlpsJ]; exact hfin
  have hdep : ConLeche.domPiDepth (ConLeche.ordTargetDomL J.lps
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1) = 0 := by
    rw [hDL]
    cases hd : Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 with
    | forallE ty bo bm =>
      rw [hd] at hfinJ
      exact nomatch (hfinJ : Expr.forallE ty bo bm = Expr.const K usK)
    | _ => rfl
  have hstripId : ConLeche.stripDomPis (Expr.instantiateLevelParams J.lps
      (pinsS.getD (q₀ + i') default).lvls dom.1)
      = Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 := by
    cases hd : Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 with
    | forallE ty bo bm =>
      rw [hd] at hfinJ
      exact nomatch (hfinJ : Expr.forallE ty bo bm = Expr.const K usK)
    | _ => rfl
  -- THE HEAD'S CONTAINER, OFF THE INSTANCE MAP'S OWN ROW (task #315
  -- WIDE (3), step 1(a) part 3): `instOrdSelfAt` at THIS field.  Its
  -- member arm is excluded by `hpinT` — a member answer makes the
  -- recorded target a member INDEX, below `p.k` — and the other arm
  -- produces the container record of the recomputation's head.
  have hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary := by
    obtain ⟨-, -, hCD⟩ := hI'.ctors i' j cA hI'.memberLt hjA
    have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hjA).1
    have hksl : l < (dJ.ksF i' j).length := by rw [hCD.ksLen]; exact hlF
    have hh := hord
    rw [show (dJ.rss i').getD j [] = rsOf (dJ.ksF i' j) from rssOfK_getD hjlt,
      rsOf_getD hksl] at hh
    have hne : ¬ ((dJ.ksF i' j).getD l .ordinary = .recursive
        ∨ (dJ.ksF i' j).getD l .ordinary = .reflexive) := by
      intro hc; rw [decide_eq_true hc] at hh; exact nomatch hh
    rcases hCD.opened.kinds l (by rw [← hCD.ksLen]; exact hksl) with ho | hr | hrf
    · exact ho
    · exact absurd (Or.inl hr) hne
    · exact absurd (Or.inr hrf) hne
  have hgbE : (pinAtE st (q₀ + i')).grpBase = q₀ := by
    obtain ⟨hgb', -⟩ := S.grp i' hi'
    rw [← pinAtE_eq] at hgb'
    exact hgb'
  have hstripDL : ConLeche.stripDomPis (ConLeche.ordTargetDomL J.lps
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1)
      = ConLeche.ordTargetDomL J.lps (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1 := by
    rw [hDL]; exact hstripId
  have hhead : (ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
      (q₀ + i') l dom.1).getAppFn = .const K usK := by
    rw [← hlpsJ]
    unfold ConLeche.ordTargetDom
    rw [hstripDL]
    refine getAppFn_instantiateList_const (e := ConLeche.ordTargetDomL J.lps
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1) ?_
    rw [hDL]; exact hfinJ
  have hbase := R.instOrdSelfAt SF S hPD R.h.classify hi' hgbE
    (fun ciJ hh => by
      rw [hciP] at hh
      obtain rfl := Option.some.inj hh
      exact S.modeled i' hi' ci hciP)
    hjA hlF hrss hstrip hdom
    (fun _ hciP' Jm' hJm' => S.groupMemberLps hi₀ hi' hciC hJmC hlpsE hciP' hJm') hhead
  have hnm : p.memberNames.findIdx? (· == K) = none := by
    cases hfi : p.memberNames.findIdx? (· == K) with
    | none => rfl
    | some mm =>
      obtain ⟨hmmlt, -, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
      have hnames : p.memberNames.length = p.k := by
        show (p.formers.map (·.1.name)).length = p.formers.length
        rw [List.length_map]
      have heq := hbase.1 mm hfi
      exact absurd (by rw [heq]; omega) hpinT
  -- THE TARGET PIN AND ITS PARAMETER COUNT (task #315 WIDE (3), step
  -- 1(a) part 3): the row's own-pin position `z`, and the identity of
  -- ITS container's parameter count with the head's — `pinNP` at `z`
  -- composed with the group's `modeled`, exactly as `hordσ`'s arm
  -- reads it.  Naming `z` and not the head's container record is what
  -- makes the clause ENVIRONMENT-FREE, so it crosses in a word.
  obtain ⟨ciM, z, hciM, hfi, htgz⟩ := hbase.2 hnm
  obtain ⟨hzlt, hm₀, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
  have hzS : z < pinsS.length := by
    have hzl : z < (ConLeche.nestedPinTermsSelf p st).length := hzlt
    unfold ConLeche.nestedPinTermsSelf at hzl
    rw [SF.pinsLen]; simpa using hzl
  have hzD : z < (D).nPins := by show z < pinsS.length; exact hzS
  have hentry : (ConLeche.nestedPinTermsSelf p st).getD z default
      = ((D).pinAt z).ownAt b.nP lps (lps.map Level.param)
          (ConLeche.containerParamOpeners b.nP) := by
    rw [← R.ownPinTerms_eq SF lps]
    unfold BlockModel.ownPinTerms
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hzD]
    rfl
  have hterm : (((D).pinAt z).ownAt b.nP lps (lps.map Level.param)
      (ConLeche.containerParamOpeners b.nP) == Expr.mkAppN
        (ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
          (q₀ + i') l dom.1).getAppFn
        ((ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
          (q₀ + i') l dom.1).getAppArgs.take ciM.nP)) = true := by
    rw [← hentry, show (ConLeche.nestedPinTermsSelf p st).getD z default
        = (ConLeche.nestedPinTermsSelf p st)[z]'hzlt from by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hzlt]; rfl]
    exact hm₀
  have hJM : ((D).pinAt z).J = K := by
    have hfn := congrArg Expr.getAppFn (of_decide_eq_true hterm)
    unfold ConLeche.Model.PinSyn.ownAt at hfn
    rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN, hhead] at hfn
    exact (Expr.const.inj hfn).1
  obtain ⟨ciz, hciz, -⟩ := (hPD z (by rw [← SF.pinsLen]; exact hzS)).own
  have hcizJ : ConLeche.containerInfo? env ((D).pinAt z).J = some ciz := by
    show ConLeche.containerInfo? env (pinsS.getD z default).J = some ciz
    rw [(SF.pinRec z _ (hPD z (by rw [← SF.pinsLen]; exact hzS)).pin).1]; exact hciz
  obtain ⟨q₀z, kJz, iz, hqez, hiz, Sz⟩ := SF.groupsAt dsR xFvsR z hzS ciz hcizJ
  have CMz := Sz.modeled iz hiz ciz (by
    show ConLeche.containerInfo? env (pinsS.getD (q₀z + iz) default).J = some ciz
    rw [← hqez]; exact hcizJ)
  have hnPz : ((D).pinAt z).nPJ = ciz.nP := by
    show (pinsS.getD z default).nPJ = ciz.nP
    rw [hqez]
    exact (Sz.pinNP iz hiz).trans CMz.nP
  -- AND ITS INDEX COUNT, AS THE MEMBER'S STORED TYPE RECORDS IT (task
  -- #315 WIDE (3), step 2): `IsBlockModel.strip` at the group's own
  -- model, read off the container RECORD — the form in which a pin of
  -- another block carrying the same container can meet it.
  have hStripz : ∃ mem ∈ ciz.members, mem.name = ((D).pinAt z).J ∧
      ∃ (bsz : List (Expr × ConLeche.BinderMeta)) (sz : Level),
        mem.type.stripPis (ciz.nP + ((D).pinAt z).nIdx) = some (bsz, .sort sz) := by
    obtain ⟨cvTz, cvRz, mIz, rPz, rulesz, hIz, -⟩ := Sz.rep iz hiz
    rw [show ((D).pinAt z) = ((D).pinAt (q₀z + iz)) from by rw [hqez]]
    exact CMz.memberStrip (by rw [Sz.kEq]; exact hiz) hIz.member (Sz.pinNIdx iz hiz)
  have hcizM : ConLeche.containerInfo? env ((D).pinAt z).J = some ciM := by
    rw [hJM]; exact hciM
  obtain rfl : ciz = ciM := Option.some.inj (hcizJ.symm.trans hcizM)
  have hlB : l < cAB.2 := by rw [hnFB, ← hnf]; exact hlF
  refine ⟨z, hzS, htgz, R.copyEisLen SF hPD ψ hcAB hlB hrr hzS htgz, hJM,
    fun ci hci => by
      obtain rfl := Option.some.inj (hci.symm.trans hciM)
      exact hnPz,
    fun ci hci => by
      obtain rfl := Option.some.inj (hci.symm.trans hciM)
      rw [← hJM]; exact hStripz, ?_⟩
  rw [hnPz]
  -- the goal, in the run's own spelling
  intro fs₁ hfs hfit
  rw [hDs, hψ] at hfit
  rw [show ((D).ownPinTerms lps) = ConLeche.nestedPinTermsSelf p st from R.ownPinTerms_eq SF lps,
    ← hlpsJ, hnPci, hdep, Nat.add_zero, mutTlss_getD hGlt]
  rcases hrr with hkA | hkA
  · exact R.copyOrdFRightPinOrdTargetReadAt SF S hPD hi' hjA hlF
      (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => by
        obtain ⟨prms, pb₀, ww, stt, hA, hB, hC, -, hE⟩ :=
          R.copyOrdFRightPinRun SF S hPD R.hK51 hi' hjA hlF
            (by rw [hkA]; exact fun hc => nomatch hc) hpinT h1 h2 h3 h4 h5 h6 h7
        exact ⟨prms, pb₀, ww, stt, hA, hB, hC, Nat.le_of_eq hE⟩)
      hkA hpinT hciP hJmem hJname (hnPci ▸ hstrip) (hnPci ▸ hdom) hfinJ hciM
      ψ ρp hsat fs₁ hfs hfit
  · have hres := R.copyOrdFRightPinOrdTargetReadAtRefl SF S hPD hi' hjA hlF
      (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => by
        obtain ⟨prms, pb₀, ww, stt, hA, hB, hC, -, hE⟩ :=
          R.copyOrdFRightPinRun SF S hPD R.hK51 hi' hjA hlF
            (by rw [hkA]; exact fun hc => nomatch hc) hpinT h1 h2 h3 h4 h5 h6 h7
        exact ⟨prms, pb₀, ww, stt, hA, hB, hC, Nat.le_of_eq hE⟩)
      hkA hpinT hciP hJmem hJname (hnPci ▸ hstrip) (hnPci ▸ hdom)
      (by rw [hstripId]; exact hfinJ) hciM
      ψ ρp hsat fs₁ hfs hfit
    rw [hdep, Nat.add_zero] at hres
    exact hres

/-- **THE OWNER'S HALF OF THE TWO COPIES' FIELD-DATA TIE AT A MEMBER
TARGET, AT THE RUN** (task #315 WIDE (3), step 3): `ordTgtReadAt`'s
sibling at the other arm of the instance map's row — the field the
pin's container calls ORDINARY and the block's rewrite made recursive
lands on one of the BLOCK's own members, and the owner's own
recomputation of its target reads as an application whose arguments
past the BLOCK's parameters are the copy's index expressions.

`Tree α := node (List (Tree α))` is the case: the copy of `List` has
its element field targeting the member `Tree`, and nothing about that
field is a pin's.  The dispatch is `ordTgtReadAt`'s — the copy field's
kind off `blkRss` — but the run is K.42's (`copyOrdFLeftRun` at its
member-target disjunct) and not K.51's, because at a member target the
positivity normalisation lands on the copy's stored domain with no
rewrite in between.

The two counts are the MEMBER's own: the head container's parameters
are the block's `b.nP` (a member is applied to the block's parameters)
and the index expressions are as many as the member's index telescope
(`(D).nIdxAt mm`, through `MutualCtorDataI.eisLen` and the member
table `memT`). -/
theorem NestedPinsRun.ordTgtMemReadAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp)
    {i' : Nat} (hi' : i' < kJ) {j l : Nat}
    (hl : l < ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j []).length)
    (hord : ((dJ.rss i').getD j []).getD l false = false)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    (hmemT : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    {cA : ConstantVal × Nat} {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    {dom : Expr × ConLeche.BinderMeta} (lps lpsC : List Name)
    (hjA : (dJ.ctorsM i')[j]? = some cA)
    (hstrip : cA.1.type.stripPis (dJ.nP + cA.2) = some (bs, rr))
    (hdom : bs[dJ.nP + l]? = some dom)
    {i₀ : Nat} (hi₀ : i₀ < kJ) {ciC : ContainerInfo} {Jm : ContainerMember}
    (hciC : ConLeche.containerInfo? env (pinsS.getD (q₀ + i₀) default).J = some ciC)
    (hJmC : ciC.members[i']? = some Jm) (hlpsE : Jm.lps = lpsC)
    {K : Name} {usK : List Level}
    (hfin : (Expr.instantiateLevelParams lpsC (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn
      = .const K usK) :
    ∃ mm : Nat, mm < p.k ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = mm ∧
      (((mutEiss0 ctorsA.length eissF ψ).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).length = (D).nIdxAt mm ∧
      OrdTargetRead (V := V) mp₁'.base2.acval (ENV₁) ψ ρp b.nP l
        ((pinsS.getD q₀ default).Ds ψ)
        ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j [])
        (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
        (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
        b.nP lpsC dJ.nP (q₀ + i') ((D).ownPinTerms lps) dom.1 := by
  classical
  -- the container record at this pin, its member and the block's own constructor
  obtain ⟨cc, J, ci, cI₀, cAB, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj,
    hcAB, hbc, hnFB⟩ := R.ctorPair SF S hPD hi' hjA
  obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := S.stored i' hi'
  have hpinAt : ∀ n : Nat, ((D).pinAt n) = pinsS.getD n default := fun _ => rfl
  rw [hpinAt] at hI'
  have hlF : l < cA.2 := by rw [← hI'.Fss_length hjA ((pinsS.getD q₀ default).ψJ ψ)]; exact hl
  -- the copy's field is recursive or reflexive
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcAB).1
  have hrr : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.recursive ∨
      kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.reflexive := by
    rw [blkRss_getD hGlt] at hrss
    have hlt := rsOf_getD_true_lt hrss
    rw [rsOf_getD_iff hlt, kindsOf_getD'] at hrss
    exact hrss
  -- the tables: the container's `nP`, its member's level parameters, the own-pin table
  have hnPci : dJ.nP = ci.nP := (S.ctorsOf i' hi' ci J (by rw [hpinAt]; exact hciP) hJmem
    (by rw [hpinAt]; exact hJname)).2
  have hcimem : i' < ci.members.length := by
    have CMci := S.modeled i' hi' ci (by rw [hpinAt]; exact hciP)
    have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
    rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ := ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJeq : J = J₂ := by
    have CMci := S.modeled i' hi' ci (by rw [hpinAt]; exact hciP)
    have hJ₂name : J₂.name = J.name := by
      rw [← (CMci.member i' J₂ hJ₂).1, hJname]
      exact hI'.member
    exact ConLeche.containerInfo?_member_det hciP hciP rfl hJmem (List.mem_of_getElem? hJ₂)
      hJ₂name.symm
  have hlpsJ : J.lps = lpsC := by
    rw [hJeq]
    exact S.groupMemberLps hi₀ hi' hciC hJmC hlpsE hciP hJ₂
  -- the group's shared level assignment and components
  have h0 : q₀ + 0 = q₀ := Nat.add_zero q₀
  have hψ : (pinsS.getD q₀ default).ψJ ψ = (pinsS.getD (q₀ + i') default).ψJ ψ := by
    have h := S.ψJEq 0 i' S.kpos hi' ψ
    rw [hpinAt, hpinAt, h0] at h
    exact h
  have hDs : (pinsS.getD q₀ default).Ds ψ = (pinsS.getD (q₀ + i') default).Ds ψ := by
    have a := S.sameDs 0 S.kpos ψ
    have bb := S.sameDs i' hi' ψ
    rw [hpinAt, hpinAt, h0] at a
    rw [hpinAt, hpinAt] at bb
    rw [a, bb]
  -- the own-pin table is the run's, and the recomputation's levels are the pin's
  have hqst : q₀ + i' < st.pins.length := by rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hLv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have h := congrArg Expr.getAppFn hpin
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at h
    exact (ConLeche.Expr.const.inj h).2
  have hlvlsT : ConLeche.ordTargetLvls (ConLeche.nestedPinTermsSelf p st) (q₀ + i')
      = (pinsS.getD (q₀ + i') default).lvls := by
    unfold ConLeche.ordTargetLvls
    rw [ConLeche.nestedPinTermsSelf_shape PD.pin PD.pinEq, Expr.getAppFn_mkAppN, hLv]
    rfl
  have hDL : ConLeche.ordTargetDomL J.lps (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1
      = Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 := by
    unfold ConLeche.ordTargetDomL; rw [hlvlsT]
  -- a constant-headed domain is not a `Π`, so the tower is empty
  have hfinJ : (Expr.instantiateLevelParams J.lps
      (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn = .const K usK := by
    rw [hlpsJ]; exact hfin
  have hdep : ConLeche.domPiDepth (ConLeche.ordTargetDomL J.lps
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1) = 0 := by
    rw [hDL]
    cases hd : Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 with
    | forallE ty bo bm =>
      rw [hd] at hfinJ
      exact nomatch (hfinJ : Expr.forallE ty bo bm = Expr.const K usK)
    | _ => rfl
  have hstripId : ConLeche.stripDomPis (Expr.instantiateLevelParams J.lps
      (pinsS.getD (q₀ + i') default).lvls dom.1)
      = Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 := by
    cases hd : Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls dom.1 with
    | forallE ty bo bm =>
      rw [hd] at hfinJ
      exact nomatch (hfinJ : Expr.forallE ty bo bm = Expr.const K usK)
    | _ => rfl
  -- THE HEAD'S CONTAINER, OFF THE INSTANCE MAP'S OWN ROW (task #315
  -- WIDE (3), step 1(a) part 3): `instOrdSelfAt` at THIS field.  Its
  -- member arm is excluded by `hpinT` — a member answer makes the
  -- recorded target a member INDEX, below `p.k` — and the other arm
  -- produces the container record of the recomputation's head.
  have hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary := by
    obtain ⟨-, -, hCD⟩ := hI'.ctors i' j cA hI'.memberLt hjA
    have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hjA).1
    have hksl : l < (dJ.ksF i' j).length := by rw [hCD.ksLen]; exact hlF
    have hh := hord
    rw [show (dJ.rss i').getD j [] = rsOf (dJ.ksF i' j) from rssOfK_getD hjlt,
      rsOf_getD hksl] at hh
    have hne : ¬ ((dJ.ksF i' j).getD l .ordinary = .recursive
        ∨ (dJ.ksF i' j).getD l .ordinary = .reflexive) := by
      intro hc; rw [decide_eq_true hc] at hh; exact nomatch hh
    rcases hCD.opened.kinds l (by rw [← hCD.ksLen]; exact hksl) with ho | hr | hrf
    · exact ho
    · exact absurd (Or.inl hr) hne
    · exact absurd (Or.inr hrf) hne
  have hgbE : (pinAtE st (q₀ + i')).grpBase = q₀ := by
    obtain ⟨hgb', -⟩ := S.grp i' hi'
    rw [← pinAtE_eq] at hgb'
    exact hgb'
  have hstripDL : ConLeche.stripDomPis (ConLeche.ordTargetDomL J.lps
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1)
      = ConLeche.ordTargetDomL J.lps (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1 := by
    rw [hDL]; exact hstripId
  have hhead : (ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st)
      (q₀ + i') l dom.1).getAppFn = .const K usK := by
    rw [← hlpsJ]
    unfold ConLeche.ordTargetDom
    rw [hstripDL]
    refine getAppFn_instantiateList_const (e := ConLeche.ordTargetDomL J.lps
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1) ?_
    rw [hDL]; exact hfinJ
  have hbase := R.instOrdSelfAt SF S hPD R.h.classify hi' hgbE
    (fun ciJ hh => by
      rw [hciP] at hh
      obtain rfl := Option.some.inj hh
      exact S.modeled i' hi' ci hciP)
    hjA hlF hrss hstrip hdom
    (fun _ hciP' Jm' hJm' => S.groupMemberLps hi₀ hi' hciC hJmC hlpsE hciP' hJm') hhead
  -- THE TARGET IS A MEMBER, so the instance map's row answers `some`:
  -- its other arm makes the recorded target a PIN index, at or above
  -- `p.k`, which the guard excludes.
  obtain ⟨mm, hfi⟩ : ∃ mm, p.memberNames.findIdx? (· == K) = some mm := by
    cases hfiK : p.memberNames.findIdx? (· == K) with
    | some mm => exact ⟨mm, rfl⟩
    | none =>
      obtain ⟨-, z, -, -, htgz⟩ := hbase.2 hfiK
      rw [htgz] at hmemT
      omega
  have hnames : p.memberNames.length = p.k := by
    show (p.formers.map (·.1.name)).length = p.formers.length
    rw [List.length_map]
  obtain ⟨hmmlt₀, hm₀, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
  have hmmlt : mm < p.k := by omega
  have htgm : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = mm := hbase.1 mm hfi
  -- the head is the member's own FORMER, which is what makes the
  -- positivity walk the identity at it
  have hlB : l < cAB.2 := by rw [hnFB, ← hnf]; exact hlF
  have hCDB := R.h.CD _ _ hcAB
  obtain ⟨-, -, htgtLt⟩ := R.h.ksJ _ _ hcAB
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcAB, Option.getD_some]
    exact hlB
  have htgtEq : tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = mm := by
    rw [← mutTgts_getD hGlt hnFs]; exact htgm
  obtain ⟨ft, hft⟩ : ∃ ft,
      fms[tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l]? = some ft :=
    ⟨_, List.getElem?_eq_getElem (htgtLt l)⟩
  obtain ⟨hnameT, hnIdxT⟩ := R.h.memT _ _ hft
  rw [htgtEq] at hft hnameT hnIdxT
  have hftTake : (fms.take p.k)[mm]? = some ft := by
    rw [List.getElem?_take_of_lt hmmlt]; exact hft
  have hKname : ft.cvTa.name = K := by
    have hgd : p.memberNames.getD mm .anonymous = ft.cvTa.name := by
      rw [← R.takeNames, List.getD_eq_getElem?_getD, List.getElem?_map, hftTake]
      rfl
    rw [← hgd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmmlt₀]
    exact eq_of_beq hm₀
  have hKmem : ∃ f ∈ fms.take p.k, f.cvTa.name = K :=
    ⟨ft, List.mem_of_getElem? hftTake, hKname⟩
  -- the index count is the MEMBER's own
  have hEl : (((mutEiss0 ctorsA.length eissF ψ).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).length = (D).nIdxAt mm := by
    rw [mutEiss0_getD hGlt]
    have hcount : ((eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length
        = mutualNIdxOf b.members3
            (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) := by
      rcases hrr with hkA | hkA
      · exact hCDB.eisLen ψ l hkA hlB
      · exact hCDB.eisLenRefl ψ l hkA hlB
    rw [hcount, htgtEq, hnIdxT]
    show ft.nIdx = ((fms.take p.k).map (·.nIdx)).getD mm 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hftTake]
    rfl
  refine ⟨mm, hmmlt, htgm, hEl, ?_⟩
  -- the goal, in the run's own spelling
  intro fs₁ hfs hfit
  rw [hDs, hψ] at hfit
  rw [show ((D).ownPinTerms lps) = ConLeche.nestedPinTermsSelf p st from R.ownPinTerms_eq SF lps,
    ← hlpsJ, hnPci, hdep, Nat.add_zero, mutTlss_getD hGlt]
  rcases hrr with hkA | hkA
  · exact R.copyOrdFRightMemOrdTargetReadAt SF S hPD hi' hjA hlF
      (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
        R.copyOrdFLeftRun SF S hPD R.hK42 hi' hjA hlF (Or.inr hmemT) h1 h2 h3 h4 h5 h6 h7)
      hkA hciP hJmem hJname (hnPci ▸ hstrip) (hnPci ▸ hdom) hfinJ hKmem
      ψ ρp hsat fs₁ hfs hfit
  · have hres := R.copyOrdFRightMemOrdTargetReadAtRefl SF S hPD hi' hjA hlF
      (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
        R.copyOrdFLeftRun SF S hPD R.hK42 hi' hjA hlF (Or.inr hmemT) h1 h2 h3 h4 h5 h6 h7)
      hkA hciP hJmem hJname (hnPci ▸ hstrip) (hnPci ▸ hdom)
      (by rw [hstripId]; exact hfinJ) hKmem
      ψ ρp hsat fs₁ hfs hfit
    rw [hdep, Nat.add_zero] at hres
    exact hres


/-- **K.69 AT THE COPY'S FIELD** (task #315 WIDE (3), step 1): the
run's spelling of the two copies' field DOMAINS, one substitution
apart.

`instOrdTgtAt` (K.67) and `instOrdSelfAt` (K.68) name the CLASS the two
recomputations give a field the container calls ordinary; this names
the TERM.  At the owner's firing guard the BLOCK's recomputation of the
field's domain IS the owner's, at the owner's level parameters
instantiated at the block pin's levels and the owner's parameter
openers instantiated at the block pin's components — `ordRootInst`'s
spelling, which is the left-hand side of the model's own reading law
(`denoteMeta_ordRootInst_read`, `NestedFieldRead.lean`).

The scaffolding is `instOrdTgtAt`'s verbatim — the same container
record, member, constructor, `stripPis` and field kind, derived the
same way — and only the tail differs, because K.67 answers with a
class and this with a term.  Two things the target rows carry are
ABSENT here: `hge` (`p.k ≤ t`), because the equation is about terms
and a block member target is covered too, and the head guard is on the
STRIPPED recomputations (`stripDomPis`), which is the reflexive arm's
form and specialises to the finitary one where `stripDomPis` is the
identity.

It is not consumed yet: its consumer is the assembly-tier two-block
field-data theorem, whose other inputs (the owner's recomputation's
scoping) are the lane's next step. -/
theorem NestedPinsRun.ordNormAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    (hstrip : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (bs, rr))
    {dom : Expr × ConLeche.BinderMeta} (hdomM : bs[dJ.nP + l]? = some dom)
    {lpsC : List Name}
    (hlpsC : ∀ ciP : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciP →
      ∀ Jm : ContainerMember, ciP.members[i']? = some Jm → Jm.lps = lpsC)
    {g : Nat} (hg : g < st.pins.length) {gn : ConLeche.NestedPin}
    (hgn : st.pins[g]? = some gn)
    {ciO : ContainerInfo} (hciO : ConLeche.containerInfo? env gn.container = some ciO)
    {m₀ : ContainerMember} (hm₀ : ciO.members.head? = some m₀)
    {ownSelf : List Expr}
    (hown : ConLeche.containerOwnPinsSelf env gn.container = some ownSelf)
    {mapR : List Nat} (hmapR : ConLeche.nestedInstMapAt env st g = some mapR)
    {qK : Nat} (hqK : qK < ownSelf.length)
    (hqm : mapR.getD qK st.pins.length = q₀ + i')
    {K : Name} {usK : List Level}
    (hfin : (ConLeche.stripDomPis
      (ConLeche.ordTargetDomL lpsC ownSelf qK dom.1)).getAppFn = .const K usK)
    {KB : Name} {usB : List Level}
    (hfinB : (ConLeche.stripDomPis (ConLeche.ordTargetDomL lpsC
      (ConLeche.nestedPinTermsSelf p st) (q₀ + i') dom.1)).getAppFn = .const KB usB)
    (hfire : ConLeche.ordRootFired env (ciO.members.map (·.name)) ownSelf
      (ConLeche.ordTargetDom lpsC dJ.nP ownSelf qK l dom.1) = true)
    {Wb : Expr}
    (hrootInst : ConLeche.ordRootInst m₀.lps ciO.nP
        (l + ConLeche.domPiDepth (ConLeche.ordTargetDomL lpsC ownSelf qK dom.1))
        ((ConLeche.nestedPinTermsSelf p st).getD g default)
        (ConLeche.ordTargetDom lpsC dJ.nP ownSelf qK l dom.1) = some Wb) :
    ConLeche.ordTargetDom lpsC dJ.nP (ConLeche.nestedPinTermsSelf p st) (q₀ + i') l dom.1
      = Wb := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, -⟩ := hCD.resid
  have hcbsLen : cbs.length = dJ.nP + cAJ.2 := Expr.stripPis_length _ hstripJ
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk]
    simp only at hcv hnf' ⊢
    rw [hcv, hnf']
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, t⟩ := rt
  -- the copy's field is recursive or reflexive
  have hrr : r = .recursive ∨ r = .reflexive := by
    rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map, hmutKs]; exact hlks),
      decide_eq_true_eq, kindsOf_getD', hmutKs] at hrss
    show r = _ ∨ r = _
    have hka : kindAt ksG l = r := by
      show (ksG.getD l (.ordinary, 0)).1 = r
      rw [List.getD_eq_getElem?_getD, hrt]; rfl
    rw [hka] at hrss
    exact hrss
  have hrecB : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true := by
    rcases hrr with rfl | rfl <;> rfl
  -- the container's member record at `i'`, positionally, and its constructor
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJ₂name : J₂.name = J.name := by
    rw [← (CMci.member i' J₂ hJ₂).1, hJname]
    exact hI.member
  have hJ₂mem : J₂ ∈ ci.members := List.mem_of_getElem? hJ₂
  have hjJ₂ : j < J₂.ctors.length := by
    have hmap := (CMci.member i' J₂ hJ₂).2.1
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, J₂.ctors[j]? = some cJ := ⟨_, List.getElem?_eq_getElem hjJ₂⟩
  have hccJ : cc = cJ :=
    (ConLeche.containerInfo?_member_ctor_det hciP hciP hJmem hJ₂mem hJ₂name.symm hcc hcJ).2.2.2
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hcJty : cJ.type = cAJ.1.type := by rw [hty, hccJ]
  have hcJnF : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
  obtain ⟨residJ, hsJ⟩ : ∃ residJ, cJ.type.stripPis (ci.nP + cJ.nFields) = some (cbs, residJ) :=
    ⟨_, by rw [hcJty, hcJnF, hnPci]; exact hstripJ⟩
  -- the container's abstract field domain, and the opened one it substitutes to
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, cbs[dJ.nP + l]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hlF)⟩
  have hdrop : (cbs.drop dJ.nP)[l]? = some domJ := by
    rw [List.getElem?_drop]; exact hdomJ
  have hopen : x.fvarTypeD
      = Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) domJ.1 :=
    blockCtorFieldDomain hCD
      (show cAJ.1.type.stripPis (dJ.nP + cAJ.2)
          = some (cbs.take dJ.nP ++ cbs.drop dJ.nP, _) from by
        rw [List.take_append_drop]; exact hstripJ)
      (by rw [List.length_take]; omega) hx hdrop
  -- an ordinary field mentions no member: on the opened domain, hence on the stored one
  have hmenAbs : ConLeche.mentionsMember (ci.members.map (·.name)) domJ.1 = false := by
    have hop := CMci.ordFree i' j l x hik hjlt hx hordC
    rw [hopen] at hop
    rw [← CMci.memberNames_eq]
    exact ConLeche.mentionsMember_instSeq_false _ _ hop
  -- the model's spelling of the domain IS the scaffolding's
  have hbs : bs = cbs := congrArg Prod.fst (Option.some.inj (hstrip.symm.trans hstripJ))
  subst hbs
  have hdd : dom = domJ := Option.some.inj (hdomM.symm.trans hdomJ)
  subst hdd
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  have hlps' : J₂.lps = lpsC := hlpsC ci hciP J₂ hJ₂

  rw [← hlps'] at hfin hfinB
  rw [← hnPci, ← hlps'] at hfire hrootInst
  rw [← hnPci, ← hlps']
  exact ConLeche.nestedOrdNormOk_at_pi R.hK69 hkP hg hgn hciO hown hm₀ hmapR hqK hqm
    PD.pin hkq (by rw [hpinJ]; exact hciP)
    (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
    (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
    hkfj hcJ hsJ hrt (by rw [hnPci]; exact hdomJ) hrecB hmenAbs hfin hfinB hfire hrootInst

/-- **THE OWNER'S FIRING FORCES THE BLOCK'S, AT THE RUN** (task #315
WIDE (f3)): K.69 STRENGTHENED in the run's spelling, and the producer
of the model's `hfireOrd`.

At a field the pin's container calls ORDINARY, where the OWNER's
recomputation of the field's domain FIRED — its head is one of the
owner's group members or the container of one of the owner's own pins
— the BLOCK's rewrite made the field recursive or reflexive, which is
the `blkRss` bit every other row of this family ASSUMES.

`ordNormAt` (K.69's term equation), `instOrdTgtAt` (K.67) and
`instOrdSelfAt` (K.68) are all GUARDED by that bit, so none of them
can produce it; the strengthened arm of `nestedOrdNormOk` is where it
lives, and this is its inversion at the run's tables.  The scaffolding
is `ordNormAt`'s verbatim — the same container record, member,
constructor, `stripPis` and stored domain, derived the same way — with
the field-kind step run BACKWARDS: `nestedOrdNormOk_fire_at` gives the
kind and `blkRss_getD`/`rsOf_getD` carry it to the bit.

**It takes no head guard**, unlike its neighbours: a firing root IS
constant-headed (`getAppFn_const_of_ordRootFired` — every other head
answers `false`), so the firing carries the guard with it. -/
theorem NestedPinsRun.ordFireAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary)
    {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    (hstrip : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (bs, rr))
    {dom : Expr × ConLeche.BinderMeta} (hdomM : bs[dJ.nP + l]? = some dom)
    {lpsC : List Name}
    (hlpsC : ∀ ciP : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciP →
      ∀ Jm : ContainerMember, ciP.members[i']? = some Jm → Jm.lps = lpsC)
    {g : Nat} (hg : g < st.pins.length) {gn : ConLeche.NestedPin}
    (hgn : st.pins[g]? = some gn)
    {ciO : ContainerInfo} (hciO : ConLeche.containerInfo? env gn.container = some ciO)
    {m₀ : ContainerMember} (hm₀ : ciO.members.head? = some m₀)
    {ownSelf : List Expr}
    (hown : ConLeche.containerOwnPinsSelf env gn.container = some ownSelf)
    {mapR : List Nat} (hmapR : ConLeche.nestedInstMapAt env st g = some mapR)
    {qK : Nat} (hqK : qK < ownSelf.length)
    (hqm : mapR.getD qK st.pins.length = q₀ + i')
    (hfire : ConLeche.ordRootFired env (ciO.members.map (·.name)) ownSelf
      (ConLeche.ordTargetDom lpsC dJ.nP ownSelf qK l dom.1) = true) :
    ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, -⟩ := hCD.resid
  have hcbsLen : cbs.length = dJ.nP + cAJ.2 := Expr.stripPis_length _ hstripJ
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hq
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk]
    simp only at hcv hnf' ⊢
    rw [hcv, hnf']
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, t⟩ := rt
  -- the container's member record at `i'`, positionally, and its constructor
  have hik : i' < dJ.k := by rw [S.kEq]; exact hi'
  have hcimem : i' < ci.members.length := by rw [← CMci.k]; exact hik
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂, ci.members[i']? = some J₂ :=
    ⟨_, List.getElem?_eq_getElem hcimem⟩
  have hJ₂name : J₂.name = J.name := by
    rw [← (CMci.member i' J₂ hJ₂).1, hJname]
    exact hI.member
  have hJ₂mem : J₂ ∈ ci.members := List.mem_of_getElem? hJ₂
  have hjJ₂ : j < J₂.ctors.length := by
    have hmap := (CMci.member i' J₂ hJ₂).2.1
    have hlen := congrArg List.length hmap
    simp only [List.length_map] at hlen
    omega
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, J₂.ctors[j]? = some cJ := ⟨_, List.getElem?_eq_getElem hjJ₂⟩
  have hccJ : cc = cJ :=
    (ConLeche.containerInfo?_member_ctor_det hciP hciP hJmem hJ₂mem hJ₂name.symm hcc hcJ).2.2.2
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hcJty : cJ.type = cAJ.1.type := by rw [hty, hccJ]
  have hcJnF : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
  obtain ⟨residJ, hsJ⟩ : ∃ residJ, cJ.type.stripPis (ci.nP + cJ.nFields) = some (cbs, residJ) :=
    ⟨_, by rw [hcJty, hcJnF, hnPci]; exact hstripJ⟩
  -- the container's abstract field domain, and the opened one it substitutes to
  obtain ⟨domJ, hdomJ⟩ : ∃ domJ, cbs[dJ.nP + l]? = some domJ :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hlF)⟩
  have hdrop : (cbs.drop dJ.nP)[l]? = some domJ := by
    rw [List.getElem?_drop]; exact hdomJ
  have hopen : x.fvarTypeD
      = Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) domJ.1 :=
    blockCtorFieldDomain hCD
      (show cAJ.1.type.stripPis (dJ.nP + cAJ.2)
          = some (cbs.take dJ.nP ++ cbs.drop dJ.nP, _) from by
        rw [List.take_append_drop]; exact hstripJ)
      (by rw [List.length_take]; omega) hx hdrop
  -- an ordinary field mentions no member: on the opened domain, hence on the stored one
  have hmenAbs : ConLeche.mentionsMember (ci.members.map (·.name)) domJ.1 = false := by
    have hop := CMci.ordFree i' j l x hik hjlt hx hordC
    rw [hopen] at hop
    rw [← CMci.memberNames_eq]
    exact ConLeche.mentionsMember_instSeq_false _ _ hop
  -- the model's spelling of the domain IS the scaffolding's
  have hbs : bs = cbs := congrArg Prod.fst (Option.some.inj (hstrip.symm.trans hstripJ))
  subst hbs
  have hdd : dom = domJ := Option.some.inj (hdomM.symm.trans hdomJ)
  subst hdd
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  have hlps' : J₂.lps = lpsC := hlpsC ci hciP J₂ hJ₂
  rw [← hnPci, ← hlps'] at hfire
  have hrecB : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true :=
    ConLeche.nestedOrdNormOk_fire_at R.hK69 hkP hg hgn hciO hown hm₀ hmapR hqK hqm
      PD.pin hkq (by rw [hpinJ]; exact hciP)
      (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
      (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
      hkfj hcJ hsJ hrt (by rw [hnPci]; exact hdomJ) hmenAbs hfire
  have hrr : r = RecFieldKind.recursive ∨ r = RecFieldKind.reflexive := by
    revert hrecB; cases r <;> decide
  have hka : kindAt ksG l = r := by
    show (ksG.getD l (.ordinary, 0)).1 = r
    rw [List.getD_eq_getElem?_getD, hrt]; rfl
  rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map, hmutKs]; exact hlks),
    decide_eq_true_eq, kindsOf_getD', hmutKs, hka]
  exact hrr



omit R SF S in
/-- **A CONSTANT HEAD IS READ OFF THE UNINSTANTIATED TERM** (task #315
WIDE (3), step 2): level instantiation rewrites a head's LEVELS and
never its shape (`Expr.getAppFn_instantiateLevelParams`), so a domain
whose head is a constant at ONE level assignment is constant-headed at
every other — which is what lets the block's guard (`ordTgtReadAt`'s
`hfin`, at the BLOCK pin's levels) serve K.69's two, at the OWNER's
levels and stripped. -/
private theorem getAppFn_const_of_ilp {e : Expr} {ks : List Name} {us : List Level}
    {K : Name} {usK : List Level}
    (h : (Expr.instantiateLevelParams ks us e).getAppFn = .const K usK) :
    ∃ vs : List Level, e.getAppFn = .const K vs := by
  rw [Expr.getAppFn_instantiateLevelParams] at h
  cases hE : e.getAppFn with
  | const c vs =>
    rw [hE] at h
    simp only [Expr.instantiateLevelParams, Expr.const.injEq] at h
    exact ⟨vs, by rw [h.1]⟩
  | _ => rw [hE] at h; simp [Expr.instantiateLevelParams] at h

omit R SF S in
/-- **AT A CONSTANT-HEADED DOMAIN THE RECOMPUTATION'S CUT IS THE
FIELD'S OWN** (task #315 WIDE (3), step 2): `stripDomPis` peels only
`∀` nodes and a constant spine is none, so the tower is empty and
`domPiDepth` is `0` — at EVERY table, because the head's shape does
not move under the level instantiation the table supplies. -/
private theorem ordTargetDomL_flat {lpsC : List Name} {dom : Expr} {K : Name} {vs : List Level}
    (hK : dom.getAppFn = .const K vs) (t : List Expr) (q : Nat) :
    ConLeche.stripDomPis (ConLeche.ordTargetDomL lpsC t q dom)
        = ConLeche.ordTargetDomL lpsC t q dom ∧
      ConLeche.domPiDepth (ConLeche.ordTargetDomL lpsC t q dom) = 0 ∧
      (ConLeche.ordTargetDomL lpsC t q dom).getAppFn
        = .const K (vs.map (Level.subst lpsC (ConLeche.ordTargetLvls t q))) := by
  have hh : (ConLeche.ordTargetDomL lpsC t q dom).getAppFn
      = .const K (vs.map (Level.subst lpsC (ConLeche.ordTargetLvls t q))) := by
    rw [ConLeche.ordTargetDomL, Expr.getAppFn_instantiateLevelParams, hK]
    rfl
  exact ⟨ConLeche.stripDomPis_eq_self_of_getAppFn_const hh,
    ConLeche.domPiDepth_eq_zero_of_getAppFn_const hh, hh⟩


omit S in
/-- **THE BLOCK'S OWN-PIN TERM, AS A SPINE** (task #315 WIDE (3), step
2): the entry `nestedPinTermsSelf` writes at a pin is that pin's
container applied to the pin's recorded components, each closed over
the block's parameters and re-opened at the openers — so its head
carries the pin's own name and levels, and its arguments are as many as
the components, scoped at the block's parameter depth and reading as
the pin's recorded readings.

The three inputs `ordRootInst`'s bridge asks of the components it
substitutes (`hDlen`, `hDs`, `hspine`) are exactly these, and this is
where they are FREE: `NestedPinSynFacts.pinDs` reads a pin's components
at every level assignment, and the openers' round trip changes nothing
a reading can see (`instantiateList_openers_abstractRange_erasedEq`,
`DenoteMetaSpine.eraseAnnots`). -/
theorem NestedPinsRun.pinTermSpine {gp : Nat} (hgp : gp < pinsS.length)
    {gn : ConLeche.NestedPin} (hgn : st.pins[gp]? = some gn) :
    ((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppFn
        = .const (pinsS.getD gp default).J (pinsS.getD gp default).lvls ∧
      ((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs.length
        = (pinsS.getD gp default).DsE.length ∧
      (∀ a ∈ ((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs,
        Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true) ∧
      ∀ ψ : Name → Nat,
        DenoteMetaSpine mp₁'.base2.acval (ENV₁) ψ b.nP
          ((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs
          ((pinsS.getD gp default).Ds ψ) := by
  classical
  obtain ⟨-, fvs, o, hop, hsc⟩ := R.scoped
  have hnP : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  obtain ⟨hJ, hpin⟩ := SF.pinRec gp gn hgn
  have hpinMem : gn ∈ st.pins := List.mem_of_getElem? hgn
  have hcl : gn.pin.looseBVarsBounded 0 = true := (hsc gn hpinMem).1
  have hlv : ∀ le ∈ gn.pin.fvarLeaves, Expr.fvar le.1 le.2 ∈ fvs := (hsc gn hpinMem).2
  have hfvsLen : fvs.length = b.nP := openPisAtFvars_length b.nP hop
  have hfvsIdx : ∀ jj, jj < b.nP → ∃ ty, fvs[jj]? = some (Expr.fvar jj ty) := by
    intro jj hjj
    have hjl : jj < fvs.length := by rw [hfvsLen]; exact hjj
    obtain ⟨ty, hty⟩ := openPisAtFvars_index b.nP f₀.cvTa.type 0 hop jj _
      (List.getElem?_eq_getElem hjl)
    rw [Nat.zero_add] at hty
    exact ⟨ty, by rw [List.getElem?_eq_getElem hjl, hty]⟩
  -- the entry, spelled out
  have hentry : (ConLeche.nestedPinTermsSelf p st).getD gp default
      = Expr.instantiateList (Expr.abstractRange gn.pin 0 p.nP 0)
          (ConLeche.containerParamOpeners p.nP).reverse 0 := by
    unfold ConLeche.nestedPinTermsSelf
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hgn]
    rfl
  have hlenO : (ConLeche.containerParamOpeners p.nP).length = p.nP := by
    simp [ConLeche.containerParamOpeners]
  have hoclo : ∀ a ∈ ConLeche.containerParamOpeners p.nP, a.looseBVarsBounded 0 = true := by
    intro a ha
    rw [ConLeche.containerParamOpeners] at ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    rfl
  have hosc : ∀ a ∈ ConLeche.containerParamOpeners p.nP, Expr.WScoped p.nP a := by
    intro a ha
    rw [ConLeche.containerParamOpeners] at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hi
    simp only [Expr.WScoped]
    exact ⟨hi, by simp⟩
  -- the entry distributes over the spine
  have hspineForm : (ConLeche.nestedPinTermsSelf p st).getD gp default
      = Expr.mkAppN (.const (pinsS.getD gp default).J (pinsS.getD gp default).lvls)
          ((pinsS.getD gp default).DsE.map fun x =>
            Expr.instantiateList (Expr.abstractRange x 0 p.nP 0)
              (ConLeche.containerParamOpeners p.nP).reverse 0) :=
    ConLeche.nestedPinTermsSelf_shape hgn (by rw [hpin, hJ])
  have hargs : ((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs
      = (pinsS.getD gp default).DsE.map fun x =>
          Expr.instantiateList (Expr.abstractRange x 0 p.nP 0)
            (ConLeche.containerParamOpeners p.nP).reverse 0 := by
    rw [hspineForm, Expr.getAppArgs_mkAppN]
    simp [Expr.getAppArgs]
  -- each component is closed and stands at the openers
  have hcomp : ∀ x ∈ (pinsS.getD gp default).DsE,
      x.looseBVarsBounded 0 = true ∧ ∀ le ∈ x.fvarLeaves, Expr.fvar le.1 le.2 ∈ fvs := by
    intro x hx
    have hmem : x ∈ gn.pin.getAppArgs := by
      rw [hpin, Expr.getAppArgs_mkAppN]
      simpa [Expr.getAppArgs] using hx
    exact ⟨ConLeche.looseBVarsBounded_getAppArgs hcl x hmem,
      fun le hle => hlv le (fvarLeaves_getAppArgs hmem hle)⟩
  refine ⟨by rw [hspineForm, Expr.getAppFn_mkAppN]; rfl,
    by rw [hargs, List.length_map], ?_, ?_⟩
  · intro a ha
    rw [hargs] at ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have hA : (Expr.abstractRange x 0 p.nP 0).looseBVarsBounded p.nP = true := by
      simpa using ConLeche.looseBVarsBounded_abstractRange x 0 p.nP 0 (hcomp x hx).1
    have hstep : Expr.instantiateList (Expr.abstractRange x 0 p.nP 0)
        (ConLeche.containerParamOpeners p.nP).reverse 0
        = Expr.instSeq (ConLeche.containerParamOpeners p.nP) (p.nP - 1)
            (Expr.abstractRange x 0 p.nP 0) := by
      have h := ConLeche.instantiateList_openers_eq_instSeq p.nP 0 hA
      rwa [Expr.liftLooseBVars_zero] at h
    have hAF : (Expr.abstractRange x 0 p.nP 0).hasFvar = false :=
      hasFvar_abstractRange_of_leaves x p.nP 0 (by
        intro le hle
        obtain ⟨i, hi⟩ := List.getElem?_of_mem ((hcomp x hx).2 le hle)
        have hib : i < fvs.length := by
          rcases Nat.lt_or_ge i fvs.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hi; exact nomatch hi
        obtain ⟨tyi, htyi⟩ := hfvsIdx i (by omega)
        rw [hi] at htyi
        have : le.1 = i := by simpa using (by simpa using htyi : le.1 = i ∧ le.2 = tyi).1
        omega)
    refine ⟨?_, ?_⟩
    · rw [hstep, hnP]
      exact Expr.instSeq_WScoped _ _ hosc (Expr.WScoped.of_not_hasFvar hAF)
    · rw [hstep]
      have h := looseBVarsBounded_instSeq_openers (nP := p.nP) hA
      rwa [hlenO] at h
  · intro ψ
    have hbase := SF.pinDs gp hgp ψ
    rw [hargs]
    refine (DenoteMetaSpine.eraseAnnots (as := _)).mp ?_
    have hmapEq : ((pinsS.getD gp default).DsE.map fun x =>
          Expr.instantiateList (Expr.abstractRange x 0 p.nP 0)
            (ConLeche.containerParamOpeners p.nP).reverse 0).map Expr.eraseAnnots
        = (pinsS.getD gp default).DsE.map Expr.eraseAnnots := by
      rw [List.map_map]
      refine List.map_congr_left fun x hx => ?_
      exact Expr.erasedEq_iff_eraseAnnots.mp
        (ConLeche.instantiateList_openers_abstractRange_erasedEq p.nP fvs x
          (hcomp x hx).1 (by rw [hfvsLen, hnP]) (by rw [← hnP]; exact hfvsIdx) (hcomp x hx).2)
    rw [hmapEq]
    exact (DenoteMetaSpine.eraseAnnots (as := (pinsS.getD gp default).DsE)).mpr hbase


/-- **THE TWO COPIES' FIELD DATA, AT THE RUN** (task #315 WIDE (3),
step 2): the BLOCK-side half of the tie — the block's own reading of
its recomputation IS the OWNER's reading, carried across `ordRootInst`
by the block pin's levels and components.

Three landed pieces compose, and nothing else is needed here:

* `ordTgtReadAt` reads the BLOCK's recomputation at the block's
  parameter openers and names the target pin `z` (the owner's half's
  mirror, at the run's own tables);
* `ordNormAt` (K.69 at the copy's field) says that recomputation IS
  `ordRootInst` of the OWNER's, under the owner's firing guard;
* `denoteMeta_ordRootInst_read` reads `ordRootInst`'s output as the
  owner's reading with the block pin's components substituted at the
  cut — its three component inputs free from `pinTermSpine`, which is
  why the whole block-side half is stated HERE and not at the
  assembly, where the components' readings are a hypothesis nobody
  holds.

**The cut is the field's own `l`.** `ordTgtReadAt`'s guard is the
stored domain's head at the pin's LEVELS, and a constant head is not a
`Π`, so both tables' towers are empty (`ordTargetDomL_flat`) and the
two sides' cuts agree without an argument.  The reflexive Π-prefix is
a separate object and is not in this statement.

**The owner's reading and the owner's scoping are HYPOTHESES**, per
the re-price: they are `PinShapes`' conjunct and `ordTargetDom_scoped`
at the OWNER's container model, neither of which exists at this tier. -/
theorem NestedPinsRun.ordReadAt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j l : Nat}
    (hl : l < ((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j []).length)
    (hord : ((dJ.rss i').getD j []).getD l false = false)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true)
    (hpinT : ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    {cA : ConstantVal × Nat} {bs : List (Expr × ConLeche.BinderMeta)} {rr : Expr}
    {dom : Expr × ConLeche.BinderMeta} (lps lpsC : List Name)
    (hjA : (dJ.ctorsM i')[j]? = some cA)
    (hlF : l < cA.2)
    (hordC : (dJ.ksF i' j).getD l .ordinary = .ordinary)
    (hstrip : cA.1.type.stripPis (dJ.nP + cA.2) = some (bs, rr))
    (hdomM : bs[dJ.nP + l]? = some dom)
    {i₀ : Nat} (hi₀ : i₀ < kJ) {ciC : ContainerInfo} {Jm : ContainerMember}
    (hciC : ConLeche.containerInfo? env (pinsS.getD (q₀ + i₀) default).J = some ciC)
    (hJmC : ciC.members[i']? = some Jm) (hlpsE : Jm.lps = lpsC)
    (hlpsC : ∀ ciP : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciP →
      ∀ Jm' : ContainerMember, ciP.members[i']? = some Jm' → Jm'.lps = lpsC)
    {K : Name} {usK : List Level}
    (hfin : (Expr.instantiateLevelParams lpsC (pinsS.getD (q₀ + i') default).lvls dom.1).getAppFn
      = .const K usK)
    -- the OWNER
    {gp : Nat} (hgp : gp < st.pins.length) {gn : ConLeche.NestedPin}
    (hgn : st.pins[gp]? = some gn)
    {ciO : ContainerInfo} (hciO : ConLeche.containerInfo? env gn.container = some ciO)
    {m₀ : ContainerMember} (hm₀ : ciO.members.head? = some m₀)
    {ownT : List Expr} (hownT : ConLeche.containerOwnPinsSelf env gn.container = some ownT)
    {mapR : List Nat} (hmapR : ConLeche.nestedInstMapAt env st gp = some mapR)
    {qK : Nat} (hqK : qK < ownT.length) (hqm : mapR.getD qK st.pins.length = q₀ + i')
    (hfire : ConLeche.ordRootFired env (ciO.members.map (·.name)) ownT
      (ConLeche.ordTargetDom lpsC dJ.nP ownT qK l dom.1) = true)
    (hnPO : (pinsS.getD gp default).DsE.length = ciO.nP)
    -- the owner's recomputation, scoped and read
    (hxb : (ConLeche.ordTargetDom lpsC dJ.nP ownT qK l dom.1).looseBVarsBounded l = true)
    (hxlv : ∀ le ∈ (ConLeche.ordTargetDom lpsC dJ.nP ownT qK l dom.1).fvarLeaves,
      Expr.fvar le.1 le.2 ∈ ConLeche.containerParamOpeners ciO.nP)
    {rx : AnnotTerm}
    (hreadO : denoteMeta mp₁'.base2.acval (ENV₁)
        (Level.substFn ψ m₀.lps (pinsS.getD gp default).lvls) (ciO.nP + l)
        (Expr.instSeq (ConLeche.Verify.openFvars ciO.nP l) (l - 1)
          (ConLeche.ordTargetDom lpsC dJ.nP ownT qK l dom.1)) = some rx) :
    ∃ z : Nat, z < pinsS.length ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + z ∧
      (((mutEiss0 ctorsA.length eissF ψ).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).length = (pinsS.getD z default).nIdx ∧
      (pinsS.getD z default).J = K ∧
      (∀ ci : ContainerInfo, ConLeche.containerInfo? env K = some ci →
        (pinsS.getD z default).nPJ = ci.nP) ∧
      (∀ ci : ContainerInfo, ConLeche.containerInfo? env K = some ci →
        ∃ mem ∈ ci.members, mem.name = K ∧
          ∃ (bsz : List (Expr × ConLeche.BinderMeta)) (sz : Level),
            mem.type.stripPis (ci.nP + (pinsS.getD z default).nIdx) = some (bsz, .sort sz)) ∧
      ∀ fs₁ : List V, fs₁.length = l →
        SpineFit (consList (((pinsS.getD q₀ default).Ds ψ).map (interp V ρp)) ρp)
          (((dJ.Fss i' ((pinsS.getD q₀ default).ψJ ψ)).getD j []).take l) fs₁ →
        ((mutTlss ctorsA.length tssF ψ).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l [] = [] ∧
        ∃ (fb : AnnotTerm) (Ps : List AnnotTerm), Ps.length = (pinsS.getD z default).nPJ ∧
          AnnotTerm.mkAppN fb (Ps ++ (((mutEiss0 ctorsA.length eissF ψ).getD
              (b.ownOffset (p.k + q₀ + i') + j) []).getD l []))
            = AnnotTerm.instAll ((pinsS.getD gp default).Ds ψ) l rx := by
  classical
  have hgpS : gp < pinsS.length := by rw [SF.pinsLen]; exact hgp
  obtain ⟨vs, hK⟩ := getAppFn_const_of_ilp hfin
  obtain ⟨hstripB, hdpB, hhdB⟩ :=
    ordTargetDomL_flat (lpsC := lpsC) hK (ConLeche.nestedPinTermsSelf p st) (q₀ + i')
  obtain ⟨hstripO, hdpO, hhdO⟩ := ordTargetDomL_flat (lpsC := lpsC) hK ownT qK
  obtain ⟨hhd, hlenA, hscA, hspA⟩ := R.pinTermSpine SF hgpS hgn
  have hown_eq : (D).ownPinTerms lps = ConLeche.nestedPinTermsSelf p st := R.ownPinTerms_eq SF lps
  -- the substitution `ordRootInst` writes, computed
  have hDlen : (((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs.take
      ciO.nP).length = ciO.nP := by
    rw [List.length_take, hlenA, hnPO]; omega
  have htakeAll : ((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs.take ciO.nP
      = ((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs :=
    List.take_of_length_le (by rw [hlenA, hnPO]; omega)
  have hrootInst : ConLeche.ordRootInst m₀.lps ciO.nP
      (l + ConLeche.domPiDepth (ConLeche.ordTargetDomL lpsC ownT qK dom.1))
      ((ConLeche.nestedPinTermsSelf p st).getD gp default)
      (ConLeche.ordTargetDom lpsC dJ.nP ownT qK l dom.1)
      = some (Expr.instantiateList
          (Expr.abstractRange (Expr.instantiateLevelParams m₀.lps
            (pinsS.getD gp default).lvls
            (ConLeche.ordTargetDom lpsC dJ.nP ownT qK l dom.1)) 0 ciO.nP l)
          ((((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs.take
            ciO.nP).reverse) l) := by
    rw [hdpO, Nat.add_zero]
    unfold ConLeche.ordRootInst
    rw [hhd]
  -- K.69 at the copy's field
  have hK69 := R.ordNormAt SF S hPD hkindsRun hi' hgb CM hjA hlF hordC hrss hstrip hdomM hlpsC
    hgp hgn hciO hm₀ hownT hmapR hqK hqm
    (by rw [hstripO]; exact hhdO) (by rw [hstripB]; exact hhdB) hfire hrootInst
  -- the block's own reading, and its target
  obtain ⟨z, hz, htg, hEl, hJz, hnPz, hStz, hOT⟩ := R.ordTgtReadAt SF S hPD ψ ρp hsat hi' hl hord hrss
    hpinT lps lpsC hjA hstrip hdomM hi₀ hciC hJmC hlpsE hfin
  refine ⟨z, hz, htg, hEl, hJz, hnPz, hStz, fun fs₁ hfs hspf => ?_⟩
  obtain ⟨htl, fb, Ps, hPs, hread⟩ := hOT fs₁ hfs hspf
  rw [hown_eq, hdpB] at htl
  refine ⟨List.eq_nil_of_length_eq_zero htl, fb, Ps, hPs, ?_⟩
  -- the bridge: `ordRootInst`'s output is the owner's reading, instantiated
  have hbr := denoteMeta_ordRootInst_read (V := V) mp₁'.base2 (ψ := ψ)
    (lps := m₀.lps) (lvls := (pinsS.getD gp default).lvls) (nP := ciO.nP) (dp := b.nP) (cut := l)
    (params := ConLeche.containerParamOpeners ciO.nP)
    (DsE := ((ConLeche.nestedPinTermsSelf p st).getD gp default).getAppArgs.take ciO.nP)
    (Ds := (pinsS.getD gp default).Ds ψ)
    (x := ConLeche.ordTargetDom lpsC dJ.nP ownT qK l dom.1) (rx := rx)
    (by simp [ConLeche.containerParamOpeners])
    (fun jj hjj => ⟨Expr.sort Level.zero, ConLeche.containerParamOpeners_getElem? hjj⟩)
    hxb hxlv hDlen
    (by rw [htakeAll]; exact hscA)
    (by rw [htakeAll]; exact hspA ψ)
    hreadO
  rw [hown_eq, hdpB, Nat.add_zero, hK69] at hread
  rw [hbr] at hread
  exact (Option.some.inj hread).symm

end Assembly

/-- **THE σ RESIDUAL, DISCHARGED** (task #315 WIDE (3′)):
`NestedPinsInst` at every run and every pin group, from
`NestedPinsRun.pinGroupInst_of`.  The chain's fourth named residual,
and the last one the instance map owes — K.61, K.62 and K.66 reach
the assembly through exactly this. -/
theorem nestedPinsInst_of {F : Nat} : NestedPinsInst V μ F := by
  intro env mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
  obtain ⟨pbs, -, hPD⟩ := R.pinData
  exact R.pinGroupInst_of SF S hPD R.h.classify

/-- **THE OWNER-HALF RESIDUAL, DISCHARGED** (task #315 WIDE (3), step
1(a)): `NestedPinsOrdTgt` at every run and every pin group, from
`NestedPinsRun.ordTgtReadAt`. -/
theorem nestedPinsOrdTgt_of {F : Nat} : NestedPinsOrdTgt V μ F := by
  intro env mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
  intro ψ ρp hsat i' hi' j hj l hl hord hrss hpinT cA bs rr dom lps lpsC hjA hstrip hdom
    i₀ hi₀ ciC Jm hciC hJmC hlpsE K usK hfin
  obtain ⟨pbs, -, hPD⟩ := R.pinData
  obtain ⟨z, hz, htg, hEl, -, -, -, hOT⟩ := R.ordTgtReadAt SF S hPD ψ ρp hsat hi' hl hord hrss hpinT
    lps lpsC hjA hstrip hdom hi₀ hciC hJmC hlpsE hfin
  exact ⟨z, hz, htg, hEl, hOT⟩

/-- **THE OWNER-HALF RESIDUAL AT A MEMBER TARGET, DISCHARGED** (task
#315 WIDE (3), step 3): `NestedPinsOrdTgtMem` at every run and every
pin group, from `NestedPinsRun.ordTgtMemReadAt`. -/
theorem nestedPinsOrdTgtMem_of {F : Nat} : NestedPinsOrdTgtMem V μ F := by
  intro env mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
  intro ψ ρp hsat i' hi' j hj l hl hord hrss hmemT cA bs rr dom lps lpsC hjA hstrip hdom
    i₀ hi₀ ciC Jm hciC hJmC hlpsE K usK hfin
  obtain ⟨pbs, -, hPD⟩ := R.pinData
  exact R.ordTgtMemReadAt SF S hPD ψ ρp hsat hi' hl hord hrss hmemT lps lpsC hjA hstrip hdom
    hi₀ hciC hJmC hlpsE hfin

end ConLeche.Model
