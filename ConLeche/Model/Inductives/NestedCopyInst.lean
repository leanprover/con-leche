module

public import ConLeche.Model.Inductives.NestedCopyRead
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedCopyGlue
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
    ∃ (cc : ContainerCtor) (J : ContainerMember) (cI : Expr) (cA : ConstantVal × Nat)
      (cname : Name),
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
    refine ⟨cc, J, cI, cA, cj.1, hcc, hn, hty, hnf, hJname, ?_, ?_, ?_, ?_, ?_⟩
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
  obtain ⟨cc, J, cI, cA, cname, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA, hbc, hnF⟩ :=
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

end Assembly

end ConLeche.Model
