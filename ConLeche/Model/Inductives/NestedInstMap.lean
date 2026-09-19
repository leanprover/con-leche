module

public import ConLeche.Model.Inductives.NestedCopyInst
import ConLeche.Verify.Inductives.NestedCopyKinds
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Model.Inductives.ContainerCross
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

end Assembly

end ConLeche.Model
