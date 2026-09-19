module

public import ConLeche.Model.Inductives.NestedPins
import ConLeche.Model.Inductives.NestedCopyInst
import ConLeche.Verify.Inductives.NestedCopyKinds
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Model.Inductives.ContainerCross
import ConLeche.Model.Inductives.NestedOwnPinsRead
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

/-- **K.62 AT THE COPY'S FIELD** (task #315 WIDE (3′)): at a field of
the container that is ORDINARY and whose COPY the auxiliary block
classifies recursive-or-reflexive at a target outside the block's own
members — the `ordF`-RIGHT arm — that target is OUTSIDE the instance
map's image.

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
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 - p.k) = false := by
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
    exact ConLeche.nestedOrdOutsideOk_at R.hK62 hed hq hmem rfl

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

end Assembly

end ConLeche.Model
