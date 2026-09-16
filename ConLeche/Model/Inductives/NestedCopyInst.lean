module

public import ConLeche.Model.Inductives.NestedCopyRead
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedCopyGlue
import ConLeche.Verify.Inductives.NestedCopyProv
import ConLeche.Verify.Inductives.NestedCopyInstU
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.Inductives.NestedCopyRewrite
import ConLeche.Verify.Inductives.NestedOpenSpine
public section

/-!
# The copies' constructor identities, assembled (task #315 L-B, DESIGN §U.32)

`NestedCopyIdx.lean` discharged `NestedPinsIdent`'s `idx` half and
named `inst` (`NestedPinsInst`).  This module builds the assembly
`inst` asks for, one arm of `CopyCtorInst` at a time, over the kit
`NestedCopyRead.lean` hangs.

The first step is the one both halves share: **the copy's constructor
`j` and the container's are the same record, instantiated**.  A pin
records its OWN container's `containerInfo?` group; the group's block
model is the BASE pin's; `NestedPinGroupSyn.ctorsOf` (DESIGN §U.32)
identifies the two member records, so the block model's constructor
`j` at member `i'` IS the container member's `j`-th entry — same name,
same type, same field count — which is what `mkCopy` copied.
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

/-! ## B1 at a container's constructor (PLAN §3/§4's bridge)

Every arm below but `len` and `es` has to cross ONE systematic
mismatch twice: what the tree knows about a container's field `l` is
`BlockOpened.recF`/`.reflF`/`.ord`/`.nestF`, stated at the OPENED
domain `xFvs[l].fvarTypeD`, while what `copyFields` hands over is the
CLOSED one, `fcs[l].1`, with `bvar`s for the parameters and the
earlier fields.  `os_field_domain`
(`ConLeche/Verify/Inductives/NestedOpenSpine.lean`, on
`openPisAtFvars_domain`) is that bridge; this is it plugged into
`BlockCtorData`, whose `opens` field carries exactly the two-stage
opening it wants. -/

/-- **The container's field `l`, opened and closed.**  `BlockCtorData`'s
opened field variable carries the closed domain instantiated at the
parameter openers followed by the earlier field openers — on the nose,
which is what the arms need: they read the domain's head and argument
spine syntactically. -/
theorem blockCtorFieldDomain {m : EnvModel V env} {env₀ : Env} {T : Name}
    {Tof : Nat → Name} {nIdxOf : Nat → Nat} {nest : Nat → Option Nat} {pins : Nat → PinSyn}
    {lps : List Name} {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List RecFieldKind} {fvsP xFvs : List Expr} {xrest : Expr}
    {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : BlockCtorData m env₀ T Tof nIdxOf nest pins lps cvC nP nF nIdx resSort isProp large
      idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    {pcs fcs : List (Expr × ConLeche.BinderMeta)} {resid : Expr}
    (hstrip : cvC.type.stripPis (nP + nF) = some (pcs ++ fcs, resid))
    (hpcs : pcs.length = nP)
    {l : Nat} {x : Expr} {bd : Expr × ConLeche.BinderMeta}
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some bd) :
    x.fvarTypeD = Expr.instSeq (fvsP ++ xFvs.take l) (nP + l - 1) bd.1 := by
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  exact ConLeche.os_field_domain nP nF l
    (openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX))
    hstrip hD.pLen hpcs hx hb


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
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
    (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
    (tssF := tssF) (ctorsR := ctorsR) (pinsS := pinsS) st mp₁')
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {q₀ kJ : Nat} {dJ : BlockModel V}
  (S : NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
    (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
    (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
    mp₁'.base2 q₀ kJ dJ)
include SF S

omit SF in
/-- **The container's constructor record, at the block model**: the
block model's constructor `j` of member `i'` is the pin's own
container member's `j`-th entry — same name, same type, same field
count (`NestedPinGroupSyn.ctorsOf` at the group, `BlockCtorFacts`'
stored `ctorInfo` against `containerInfo?`'s). -/
theorem NestedPinsRun.ctorRecord
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {ciJ : ContainerInfo} {J : ContainerMember}
    (hciJ : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ)
    (hJmem : J ∈ ciJ.members) (hJname : J.name = (pinsS.getD (q₀ + i') default).J) :
    ∃ cc : ContainerCtor, J.ctors[j]? = some cc ∧
      cAJ.1.name = cc.name ∧ cAJ.1.type = cc.type ∧ cAJ.2 = cc.nFields := by
  classical
  have hpinAt : ∀ n, (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
      srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt n = pinsS.getD n default :=
    fun _ => rfl
  obtain ⟨hnames, hnP⟩ := S.ctorsOf i' hi' ciJ J (by rw [hpinAt]; exact hciJ) hJmem
    (by rw [hpinAt]; exact hJname)
  -- the positions line up
  have hjl : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hlen : (dJ.ctorsM i').length = J.ctors.length := by
    have := congrArg List.length hnames; simpa using this
  obtain ⟨cc, hcc⟩ : ∃ cc, J.ctors[j]? = some cc :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hname : cAJ.1.name = cc.name := by
    have h1 : ((dJ.ctorsM i').map (·.1.name))[j]? = some cAJ.1.name := by
      rw [List.getElem?_map, hj]; rfl
    rw [hnames, List.getElem?_map, hcc] at h1
    exact (Option.some.inj h1).symm ▸ rfl
  -- the two stored `ctorInfo`s
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  rw [hpinAt] at hI
  obtain ⟨hfind, -, -⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, -, -, -, -, hall⟩ :=
    ConLeche.containerInfo?_inv hciJ
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, -, -, -, -, -, -, hct⟩ := hall J hJmem
  obtain ⟨r, cvc, hrj, hccn, hfc, htc⟩ := hct j cc hcc
  obtain ⟨hF, -, -, -⟩ := R.cross
  have hfc₁ : (ENV₁).find? cc.name = some (.ctorInfo cvc ciJ.nP cc.nFields) := by
    refine hF _ _ (fun _ _ _ _ h => nomatch h) ?_
    rw [hccn]; exact hfc
  rw [hname, hfc₁] at hfind
  rw [hnP] at hfind
  obtain ⟨rfl, -, hnf⟩ := ConLeche.ConstantInfo.ctorInfo.inj (Option.some.inj hfind.symm)
  exact ⟨cc, hcc, hname, htc.symm, hnf⟩

/-- **THE COPY'S CONSTRUCTOR, PAIRED WITH THE CONTAINER'S**: at member
`i'` of the group and constructor `j`, the auxiliary block's
constructor at the global position `b.ownOffset (p.k + q₀ + i') + j`
is the mint's copy of the container member's `j`-th constructor —
`mkCopy`'s output at the recorded source, whose type is the
container's instantiated at the pin's components and closed over the
block's parameter binders — and the two carry the same field count.
(`PinData.own` = K.28 at the pin, `mkCopy_inv`, the block's flattening
`auxBlock_ctors_getElem?` under the grouping guard, and the
constructors' stage `MutualFormersFacts.runC`.) -/
theorem NestedPinsRun.ctorPair {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) :
    ∃ (cc : ContainerCtor) (J : ContainerMember) (ci : ContainerInfo) (cI : Expr)
      (cA : ConstantVal × Nat) (cname : Name),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci ∧
      J ∈ ci.members ∧
      J.ctors[j]? = some cc ∧
      cAJ.1.name = cc.name ∧ cAJ.1.type = cc.type ∧ cAJ.2 = cc.nFields ∧
      J.name = (pinsS.getD (q₀ + i') default).J ∧
      Expr.instPis (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls cc.type)
          (srcAtE st p (q₀ + i')).2.2 = some cI ∧
      (copyAtE st p (q₀ + i')).ctors[j]? = some (cname, (copyAtE st p (q₀ + i')).ctors[j]!.2.1,
        cc.nFields) ∧
      ctorsA[b.ownOffset (p.k + q₀ + i') + j]? = some cA ∧
      b.ctors[b.ownOffset (p.k + q₀ + i') + j]?
        = some ⟨⟨cname, p.lps, (copyAtE st p (q₀ + i')).ctors[j]!.2.1⟩, cc.nFields,
            p.k + q₀ + i'⟩ ∧
      cA.2 = cc.nFields := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨ci, hci, -, -, -, -, J, hJfind, hJn, c, hmk, hcty, hccm⟩ := PD.own
  have hJmem : J ∈ ci.members := List.mem_of_find?_eq_some hJfind
  obtain ⟨hJc, hpinEq⟩ := SF.pinRec _ _ PD.pin
  have hJname : J.name = (pinsS.getD (q₀ + i') default).J := by rw [hJn, hJc]
  have hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci := by
    rw [hJc]; exact hci
  obtain ⟨cc, hcc, hn, hty, hnf⟩ := R.ctorRecord S hi' hj hciP hJmem hJname
  -- the mint's own constructor at `j`
  obtain ⟨-, -, -, -, -, hall⟩ := ConLeche.mkCopy_inv hmk
  obtain ⟨cI, hinst, hcj⟩ := hall j cc hcc
  -- the copy's stored constructor has that name and field count
  have hmapj : ((copyAtE st p (q₀ + i')).ctors.map (fun x => (x.1, x.2.2)))[j]?
      = some (Name.replacePrefix J.name (copyAtE st p (q₀ + i')).name cc.name, cc.nFields) := by
    rw [← hccm, List.getElem?_map, hcj]; rfl
  rw [List.getElem?_map] at hmapj
  cases hcj' : (copyAtE st p (q₀ + i')).ctors[j]? with
  | none => rw [hcj'] at hmapj; exact nomatch hmapj
  | some cj =>
    rw [hcj'] at hmapj
    obtain ⟨hn1, hn2⟩ := Prod.mk.inj (Option.some.inj hmapj)
    have hbang : (copyAtE st p (q₀ + i')).ctors[j]! = cj := by
      rw [List.getElem!_eq_getElem?_getD, hcj']; rfl
    have hcjEq : cj = (cj.1, cj.2.1, cj.2.2) := rfl
    -- the block's flattening
    have hty' : st.types[p.k + (q₀ + i')]? = some (copyAtE st p (q₀ + i')) := PD.ty
    have hbc := ConLeche.auxBlock_ctors_getElem? R.hb R.h3 (p.k + (q₀ + i')) j _ cj hty' hcj'
    rw [show p.k + (q₀ + i') = p.k + q₀ + i' from by omega] at hbc
    -- the constructors' stage at that position
    have hblt : b.ownOffset (p.k + q₀ + i') + j < b.ctors.length :=
      (List.getElem?_eq_some_iff.mp hbc).1
    obtain ⟨cA, hcA⟩ : ∃ cA, ctorsA[b.ownOffset (p.k + q₀ + i') + j]? = some cA :=
      ⟨_, List.getElem?_eq_getElem (by rw [R.h.lenA]; exact hblt)⟩
    obtain ⟨hnF, -⟩ := R.h.runC _ _ hcA
    refine ⟨cc, J, ci, cI, cA, cj.1, hciP, hJmem, hcc, hn, hty, hnf, hJname, ?_, ?_, ?_, ?_, ?_⟩
    · have hlv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
        have hfn := congrArg Expr.getAppFn (hpinEq.symm.trans PD.pinEq)
        simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at hfn
        exact (ConLeche.Expr.const.inj hfn).2
      rw [hlv]; exact hinst
    · rw [hbang, ← hn2]
    · exact hcA
    · rw [hbang, hbc, ← hn2]
    · rw [hnF, List.getD_eq_getElem?_getD, hbc]
      exact hn2

/-- **`CopyCtorInst.len`**: the copy's constructor has the container's
field count.  The block's shadow chain is as long as the constructor
has fields (`shadowFs_length`), the stage records that count
(`MutualFormersFacts.runC`), and the mint copied it off the container's
constructor record (`ctorPair`). -/
theorem NestedPinsRun.copyLen {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) (ψ ψJ : Name → Nat) :
    ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).length
      = ((dJ.Fss i' ψJ).getD j []).length := by
  obtain ⟨cc, J, ci, cI, cA, cname, -, -, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA, hbc, hnF⟩ :=
    R.ctorPair SF S hPD hi' hj
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  rw [hI.Fss_length hj ψJ, hnf]
  have hlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  show ((mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ).getD
    (b.ownOffset (p.k + q₀ + i') + j) []).length = _
  rw [mutFss0_getD hlt, shadowFs_length]
  show (ctorsA.getD (b.ownOffset (p.k + q₀ + i') + j) default).2 = _
  rw [List.getD_eq_getElem?_getD, hcA]
  exact hnF

/-- **THE COPY'S CONSTRUCTOR BODY** (DESIGN §U.33 (c), stages 1–5):
the auxiliary block's constructor at the copy of member `i'`'s
constructor `j` is the elimination's REWRITE of the container's own
constructor type — level-substituted, its parameters instantiated at
the pin's components (`cI`) — closed over the block's own parameter
binders `pbs₀`.  The two side conditions the round trip needs come
with it: `cI` carries no loose bound variable and every `fvar` leaf it
has is one of the block's parameter openers (`instPisILP_frame` over
K.30's scope of the pin).

The chain: `elimNested_copyCtors` at the copy's position
(`nestedTypes0_length` + `nestedAnnotFormers_length` put it at
`p.k + q₀ + i'`, which is `PinData.ty`), `mkCopy_inv` at the
container's constructor record, `containerInfo?_member_ctor_det` to
replace the ELIMINATION's group by the PIN's own (the two records
share only the member's name), then `closeTelescope_eq_mkPisB` +
`stripPis_mkPisB_self` + `instPis_mkPisB` +
`instSeq_abstractRange_fvs`, which give the re-opened body as `cI` ON
THE NOSE. -/
theorem NestedPinsRun.copyBody {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) :
    ∃ (cc : ContainerCtor) (J : ContainerMember) (cI cbody' o : Expr) (params : List Expr)
      (pbs₀ : List (Expr × ConLeche.BinderMeta)) (st₁ st₂ : ElimState)
      (cA : ConstantVal × Nat) (cname : Name),
      J.ctors[j]? = some cc ∧
      cAJ.1.name = cc.name ∧ cAJ.1.type = cc.type ∧ cAJ.2 = cc.nFields ∧
      J.name = (pinsS.getD (q₀ + i') default).J ∧
      (srcAtE st p (q₀ + i')).2.2.length = dJ.nP ∧
      ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (params, o) ∧
      Expr.instPis (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls cc.type)
          (srcAtE st p (q₀ + i')).2.2 = some cI ∧
      cI.looseBVarsBounded 0 = true ∧
      (∀ l ∈ cI.fvarLeaves, Expr.fvar l.1 l.2 ∈ params) ∧
      ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st₁ cI
        = .ok (cbody', st₂) ∧
      st₁.pins <+: st₂.pins ∧ st₂.pins <+: st.pins ∧
      ctorsA[b.ownOffset (p.k + q₀ + i') + j]? = some cA ∧ cA.2 = cc.nFields ∧
      b.ctors[b.ownOffset (p.k + q₀ + i') + j]?
        = some ⟨⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩, cc.nFields, p.k + q₀ + i'⟩ := by
  classical
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  -- the elimination's provenance, at the copy's position
  obtain ⟨t₀, params, o, pbs₀, o', hhead, hop, hstrip, hall⟩ :=
    ConLeche.elimNested_copyCtors R.helim
  have hk : (ConLeche.nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length R.hfA]; rfl
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  have hty0 : st.types[(ConLeche.nestedTypes0 p fmsA ctorsA₀).length + (q₀ + i')]?
      = some (copyAtE st p (q₀ + i')) := by rw [hk]; exact PD.ty
  obtain ⟨I', ci', m', J', lvls', Ds', c', hci', hJ', hsrc', hmk', hcty', hclen', hany', hloose',
    hallj⟩ := hall (q₀ + i') _ hty0
  -- the source record is ONE value: the elimination's and the pin's agree
  obtain ⟨hJc, hpinEq⟩ := SF.pinRec _ _ PD.pin
  have hsrcEq := hsrc'.symm.trans PD.src
  obtain ⟨hJn', hlv', hDs'⟩ : J'.name = (pinAtE st (q₀ + i')).container ∧
      lvls' = (srcAtE st p (q₀ + i')).2.1 ∧ Ds' = (srcAtE st p (q₀ + i')).2.2 := by
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hsrcEq)
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    exact ⟨h1, h3, h4⟩
  subst hlv' hDs'
  -- the copy's stored constructor at `j`
  obtain ⟨c₀, pbs', rest, cbody, cbody', st₁, st₂, hc0, hstrip0, hinstp, hrep, hcjEq, hp1, hp2,
    -⟩ := hallj j _ hcj
  -- `mkCopy`'s own pre-image at the ELIMINATION's container record
  obtain ⟨-, -, -, -, hclen'', hallc⟩ := ConLeche.mkCopy_inv hmk'
  have hjlt : j < J'.ctors.length := by
    have := (List.getElem?_eq_some_iff.mp hc0).1
    omega
  obtain ⟨cc', hcc'⟩ : ∃ cc', J'.ctors[j]? = some cc' :=
    ⟨_, List.getElem?_eq_getElem hjlt⟩
  obtain ⟨cI', hinst', hc0'⟩ := hallc j cc' hcc'
  -- the two container records are one (the nP-free determinacy, DESIGN §U.33 (b))
  have hJmem' : J' ∈ ci'.members := List.mem_of_getElem? hJ'
  have hnameEq : J'.name = J.name := by rw [hJn', hJname, hJc]
  obtain ⟨hlps, -, -, rfl⟩ := ConLeche.containerInfo?_member_ctor_det hciP hci' hJmem hJmem'
    hnameEq.symm hcc hcc'
  have hlvls : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have hfn := congrArg Expr.getAppFn (hpinEq.symm.trans PD.pinEq)
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at hfn
    exact (ConLeche.Expr.const.inj hfn).2
  have hcIeq : cI' = cI := by
    rw [← hlps, ← hlvls] at hinst'; exact Option.some.inj (hinst'.symm.trans hinst)
  rw [hcIeq] at hc0'
  -- the mint's body, stripped and re-instantiated, is `cI` on the nose
  have hnPb : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  obtain ⟨-, hf0, hb0, -⟩ := R.former0
  have ht₀ty : f₀.cvTa.type = t₀.type := by
    have hh : (ConLeche.nestedTypes0 p fmsA ctorsA₀)[0]? = some t₀ := by
      rw [← List.head?_eq_getElem?]; exact hhead
    obtain ⟨t', ht', -, ht'ty, -, -⟩ := ConLeche.elimNested_types_prefix R.helim 0 t₀ hh
    obtain ⟨hcvTa, -⟩ := R.formerType 0 f₀ R.h.first t' ht'
    rw [hcvTa, ht'ty]
  have hopb : ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (params, o) := by
    rw [hnPb, ht₀ty]; exact hop
  have hplen : params.length = p.nP := openPisAtFvars_length _ hop
  have hpbs₀f : ∀ x ∈ pbs₀, x.1.hasFvar = false :=
    (ConLeche.stripPis_not_hasFvar _ hstrip (by rw [← ht₀ty]; exact hf0)).1
  have hpbs₀len : pbs₀.length = p.nP := Expr.stripPis_length _ hstrip
  -- `cI`'s frame: closed, and scoped at the openers
  obtain ⟨hccb, hccf⟩ : cc.type.looseBVarsBounded 0 = true ∧ cc.type.hasFvar = false := by
    obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, -, -, -, -, hallM⟩ :=
      ConLeche.containerInfo?_inv hciP
    obtain ⟨cvC, capsC, cvRc, mIc, rulesC, -, -, -, -, -, -, hct⟩ := hallM J hJmem
    obtain ⟨r, cvc, hrj, hccn, hfc, htc⟩ := hct j cc hcc
    obtain ⟨hwf1, -, -, hwf4, -⟩ :=
      mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfc)
    exact ⟨by rw [htc]; exact hwf4, by rw [htc]; exact hwf1⟩
  obtain ⟨-, fvs, o₂, hop₂, hsc⟩ := R.scoped
  have hfvs : fvs = params := (Prod.mk.inj (Option.some.inj (hop₂.symm.trans hopb))).1
  rw [hfvs] at hsc
  have hDsLeaf : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2,
      ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ params := by
    intro a ha l hl
    have hmem : pinAtE st (q₀ + i') ∈ st.pins := List.mem_of_getElem? PD.pin
    exact (hsc _ hmem).2 l (by rw [PD.pinEq]; exact ConLeche.fvarLeaves_mkAppN_arg _ ha hl)
  obtain ⟨hcIb, hcIl⟩ := ConLeche.instPisILP_frame (params := params) hinst hccb hccf
    hloose' hDsLeaf
  -- stages 3–4: the strip and the re-instantiation
  rw [ConLeche.closeTelescope_eq_mkPisB pbs₀ 0 cI hpbs₀f, hpbs₀len] at hc0'
  obtain rfl : c₀ = (Name.replacePrefix J'.name (copyAtE st p (q₀ + i')).name cc.name,
      ConLeche.mkPisB pbs₀ (cI.abstractRange 0 p.nP 0), cc.nFields) :=
    Option.some.inj (hc0.symm.trans hc0')
  have hstrip1 : (ConLeche.mkPisB pbs₀ (cI.abstractRange 0 p.nP 0)).stripPis p.nP
      = some (pbs₀, cI.abstractRange 0 p.nP 0) := by
    rw [← hpbs₀len]; exact ConLeche.stripPis_mkPisB_self _ _
  have hpbs' : pbs' = pbs₀ :=
    (Prod.mk.inj (Option.some.inj (hstrip0.symm.trans hstrip1))).1
  have hcbody : cbody = cI := by
    have hi1 := ConLeche.instPis_mkPisB pbs₀ params (cI.abstractRange 0 p.nP 0) (by omega)
    rw [hi1] at hinstp
    rw [Option.some.inj hinstp.symm, hplen]
    refine ConLeche.instSeq_abstractRange_fvs p.nP params cI hcIb hplen ?_ hcIl
    intro jj hjj
    obtain ⟨ty, hty'⟩ := openPisAtFvars_index _ _ _ hop jj _
      (List.getElem?_eq_getElem (show jj < params.length by omega))
    refine ⟨ty, ?_⟩
    rw [List.getElem?_eq_getElem (show jj < params.length by omega), hty', Nat.zero_add]
  rw [hcbody] at hrep
  rw [hpbs'] at hcjEq
  have hDsnP : (srcAtE st p (q₀ + i')).2.2.length = dJ.nP := by
    obtain ⟨ci₂, hci₂, hDsLen, -, -, -, -, -, -, -, -, -, -⟩ := PD.own
    obtain ⟨-, hnPJ⟩ := S.ctorsOf i' hi' ci J hciP hJmem hJname
    rw [hDsLen, hnPJ]
    exact congrArg ContainerInfo.nP (Option.some.inj (((by rw [← hJc] at hci₂; exact hci₂ :
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci₂)).symm.trans hciP))
  refine ⟨cc, J, cI, cbody', o, params, pbs₀, st₁, st₂, cA, cname, hcc, hn, hty, hnf, hJname,
    hDsnP, hopb, hinst, hcIb, hcIl, hrep, hp1, hp2, hcA, hnF, ?_⟩
  rw [hbc]
  have : (copyAtE st p (q₀ + i')).ctors[j]!.2.1 = closeTelescope pbs₀ 0 cbody' := by
    have hb2 : (copyAtE st p (q₀ + i')).ctors[j]! = (cname,
        (copyAtE st p (q₀ + i')).ctors[j]!.2.1, cc.nFields) := by
      rw [List.getElem!_eq_getElem?_getD, hcj]; rfl
    have := congrArg (fun x => x.2.1) hcjEq
    simpa using this
  rw [this]

/-- **THE COPY'S FIELDS, ONE BY ONE** (DESIGN §U.33 (c) stage 5): the
stored copy constructor's telescope is the CONTAINER's constructor
telescope past its parameters — each field domain level-substituted
and instantiated at the pin's components at the cut its own depth
gives (`instPis_ilp_mkPisB`, `instTeleSeq_getD`) — run through the
elimination's rewrite domain by domain (`replaceAllNested_mkPisB`),
with the residual last.  This is the frame the four remaining arms of
`CopyCtorInst` are stated at: they differ only in what they make of
ONE `replaceAllNested` run on ONE instantiated domain. -/
theorem NestedPinsRun.copyFields {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) :
    ∃ (cc : ContainerCtor) (J : ContainerMember) (lpsJ : List Name)
      (pcs fcs Fs' : List (Expr × ConLeche.BinderMeta)) (esJ : List Expr)
      (cbody' resid' o : Expr) (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta))
      (cA : ConstantVal × Nat) (cname : Name),
      cAJ.1.name = cc.name ∧ cAJ.1.type = cc.type ∧ cAJ.2 = cc.nFields ∧
      J.name = (pinsS.getD (q₀ + i') default).J ∧
      (srcAtE st p (q₀ + i')).2.2.length = dJ.nP ∧
      -- the container's constructor as a telescope: parameters, fields,
      -- and the residual at its own member
      cc.type.stripPis (dJ.nP + cc.nFields) = some (pcs ++ fcs,
        Expr.mkAppN (.const (dJ.memberName i') (lpsJ.map Level.param))
          (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ)) ∧
      pcs.length = dJ.nP ∧ fcs.length = cc.nFields ∧ esJ.length = dJ.nIdxAt i' ∧
      -- the block's parameter openers
      ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (params, o) ∧
      -- the copy's fields: one rewrite run per instantiated domain
      Fs'.length = cc.nFields ∧
      (∀ l, l < cc.nFields → ∃ st₁ st₂ : ElimState,
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st₁
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
                (fcs.getD l default).1))
          = .ok ((Fs'.getD l default).1, st₂) ∧ st₂.pins <+: st.pins) ∧
      (∃ st₁ st₂ : ElimState,
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st₁
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
                (Expr.mkAppN (.const (dJ.memberName i') (lpsJ.map Level.param))
                  (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ))))
          = .ok (resid', st₂) ∧ st₂.pins <+: st.pins) ∧
      -- the block's entry, the rewritten telescope closed over `pbs₀`
      cbody'.stripPis cc.nFields = some (Fs', resid') ∧
      ctorsA[b.ownOffset (p.k + q₀ + i') + j]? = some cA ∧ cA.2 = cc.nFields ∧
      b.ctors[b.ownOffset (p.k + q₀ + i') + j]?
        = some ⟨⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩, cc.nFields, p.k + q₀ + i'⟩ := by
  classical
  obtain ⟨cc, J, cI, cbody', o, params, pbs₀, stA, stB, cA, cname, hcc, hn, hty, hnf, hJname,
    hDsnP, hopb, hinst, -, -, hrep, -, hp2, hcA, hnF, hbc⟩ := R.copyBody SF S hPD hi' hj
  -- the container's constructor telescope, off the block model
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  obtain ⟨cbs, esJ, hstripJ, hesJ⟩ := hCD.resid
  rw [hty, hnf] at hstripJ
  have hcbsLen : cbs.length = dJ.nP + cc.nFields := Expr.stripPis_length _ hstripJ
  have hpl : (cbs.take dJ.nP).length = dJ.nP := by rw [List.length_take]; omega
  have hfl : (cbs.drop dJ.nP).length = cc.nFields := by rw [List.length_drop]; omega
  have hsplit : cbs.take dJ.nP ++ cbs.drop dJ.nP = cbs := List.take_append_drop _ _
  have hmkJ := ConLeche.stripPis_mkPisB _ hstripJ
  -- the mint's body, as the fields' telescope
  have hinst2 := ConLeche.instPis_ilp_mkPisB J.lps (pinsS.getD (q₀ + i') default).lvls
    (srcAtE st p (q₀ + i')).2.2 (cbs.take dJ.nP) (cbs.drop dJ.nP)
    (Expr.mkAppN (.const (dJ.memberName i') (cvT.levelParams.map Level.param))
      (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ)) (by rw [hpl, hDsnP])
  rw [hsplit, ← hmkJ] at hinst2
  obtain rfl : cI = ConLeche.mkPisB
      (ConLeche.instTeleSeq (srcAtE st p (q₀ + i')).2.2
        ((srcAtE st p (q₀ + i')).2.2.length - 1)
        ((cbs.drop dJ.nP).map fun bb =>
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bb.1,
            (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bb.2.pw⟩ : ConLeche.BinderMeta))))
      (Expr.instSeq (srcAtE st p (q₀ + i')).2.2
        ((srcAtE st p (q₀ + i')).2.2.length - 1 + (cbs.drop dJ.nP).length)
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
          (Expr.mkAppN (.const (dJ.memberName i') (cvT.levelParams.map Level.param))
            (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ)))) :=
    Option.some.inj (hinst.symm.trans hinst2)
  -- the rewrite, domain by domain
  obtain ⟨Fs', resid', hcb, hlenF, hfields, stC, stD, hres, -, hresP, -⟩ :=
    ConLeche.replaceAllNested_mkPisB _ hrep
  have hmapGet : ∀ (L : List (Expr × ConLeche.BinderMeta)) (l : Nat), l < L.length →
      ((L.map fun bb =>
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bb.1,
            (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bb.2.pw⟩
              : ConLeche.BinderMeta))).getD l default).1
        = Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
            (L.getD l default).1 := by
    intro L l hl
    have hgd : L.getD l default = L[l] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
      Option.map_some, hgd]
    rfl
  have hbsLen : (ConLeche.instTeleSeq (srcAtE st p (q₀ + i')).2.2
      ((srcAtE st p (q₀ + i')).2.2.length - 1)
      ((cbs.drop dJ.nP).map fun bb =>
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bb.1,
          (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bb.2.pw⟩
            : ConLeche.BinderMeta)))).length = cc.nFields := by
    rw [ConLeche.instTeleSeq_length, List.length_map, hfl]
  have hlenF' : Fs'.length = cc.nFields := by rw [hlenF, hbsLen]
  refine ⟨cc, J, cvT.levelParams, cbs.take dJ.nP, cbs.drop dJ.nP, Fs', esJ, cbody', resid', o,
    params, pbs₀, cA, cname, hn, hty, hnf, hJname, hDsnP, by rw [hsplit]; exact hstripJ, hpl, hfl,
    hesJ, hopb, hlenF', ?_, ⟨stC, stD, ?_, hresP.trans hp2⟩, ?_, hcA, hnF, hbc⟩
  · intro l hl
    obtain ⟨-, st₁, st₂, hrun, -, hpre, -⟩ := hfields l (by rw [hbsLen]; exact hl)
    refine ⟨st₁, st₂, ?_, hpre.trans hp2⟩
    rw [ConLeche.instTeleSeq_getD _ _ _ _ (by rw [List.length_map, hfl]; exact hl),
      hmapGet _ l (by rw [hfl]; exact hl), hDsnP] at hrun
    exact hrun
  · rw [hDsnP, List.length_drop, show cbs.length - dJ.nP = cc.nFields from by omega] at hres
    exact hres
  · rw [hcb, ← hlenF']
    exact ConLeche.stripPis_mkPisB_self _ _

end Assembly

end ConLeche.Model

