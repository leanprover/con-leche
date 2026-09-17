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
import ConLeche.Verify.Inductives.NestedCopyKinds
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Model.Inductives.BlockRepCross
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


/-- **B1's mention corollary at a container's field**: a constant the
CLOSED field domain mentions is mentioned by the OPENED one, which is
the side `ContainerModeled.ordFree` speaks of. -/
theorem blockCtorFieldMentions {m : EnvModel V env} {env₀ : Env} {T : Name}
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
    {l : Nat} {x : Expr} {bd : Expr × ConLeche.BinderMeta} {n : Name}
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some bd)
    (hm : bd.1.mentionsConst n = true) :
    x.fvarTypeD.mentionsConst n = true := by
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  exact ConLeche.os_field_domain_mentions nP nF l
    (openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX))
    hstrip hD.pLen hpcs hx hb hm

/-- An instantiation sequence keeps a constant head. -/
theorem os_instSeq_head {e : Expr} {n : Name} {us : List Level}
    (h : e.getAppFn = Expr.const n us) (as : List Expr) (t : Nat) :
    (Expr.instSeq as t e).getAppFn = Expr.const n us := by
  have he : Expr.mkAppN (Expr.const n us) e.getAppArgs = e := by
    rw [← h]; exact Expr.mkAppN_getApp e
  rw [← he, ConLeche.instSeq_mkAppN_const, Expr.getAppFn_mkAppN]
  rfl

/-- The formers are consed in order, so a prefix's environment is a
stage of the whole list's. -/
theorem consMutualFormers_append :
    ∀ (l₁ l₂ : List MutualFormerA) (env : Env),
      ConLeche.consMutualFormers (l₁ ++ l₂) env
        = ConLeche.consMutualFormers l₂ (ConLeche.consMutualFormers l₁ env)
  | [], _, _ => rfl
  | g :: gs, l₂, env => by
    show ConLeche.consMutualFormers (gs ++ l₂) ⟨.indInfo g.cvTa {} :: env.consts⟩ = _
    rw [consMutualFormers_append gs l₂]
    rfl

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

omit SF S in
/-- **THE PREFIX MODEL'S READINGS, AT THE WHOLE BLOCK'S** (task #315
L-B): everything the group's syntactic facts read — the container's
constructor types, the pins' components — is read at the model of the
environment holding the block's OWN `p.k` formers, while the copies'
constructors are read at the model holding all of them.  The two agree
wherever the first reads: the extra constants are the copies' formers,
which are fresh in the prefix environment, and the two models carry
the SAME value at every constant the prefix environment holds — the
block's members by `mutMemberLeaf` (`MutualFormersFacts.leaf` against
`NestedPinsRun.hleafM'`), everything else by both agreeing with the
pre-block model. -/
theorem NestedPinsRun.crossUp :
    ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ dp e = some ea →
      denoteMeta mp₁.base2.acval (ConLeche.consMutualFormers fms env) ψ dp e = some ea := by
  classical
  have hndAll : (fms.map (·.cvTa.name)).Nodup := by
    have h0 := R.hnd
    unfold ConLeche.MutualBlock.blockNames at h0
    rw [R.h.names]
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  -- the names of the two halves are disjoint
  have hsplitNd : ((fms.take p.k).map (·.cvTa.name)
      ++ (fms.drop p.k).map (·.cvTa.name)).Nodup := by
    rw [← List.map_append, List.take_append_drop]; exact hndAll
  have hne : ∀ g ∈ fms.drop p.k, ∀ f ∈ fms.take p.k, f.cvTa.name ≠ g.cvTa.name := by
    intro g hg f hf heq
    exact (List.nodup_append.mp hsplitNd).2.2 f.cvTa.name (List.mem_map_of_mem hf)
      g.cvTa.name (List.mem_map_of_mem hg) heq
  have hfresh : ∀ g ∈ fms.drop p.k,
      (ConLeche.consMutualFormers (fms.take p.k) env).find? g.cvTa.name = none := by
    intro g hg
    rw [ConLeche.consMutualFormers_find?_of_ne (fun f hf => hne g hg f hf)]
    obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_drop hg)
    exact R.h.fresh t g ht
  have hndDrop : ((fms.drop p.k).map (·.cvTa.name)).Nodup := by
    refine List.Nodup.sublist ?_ hndAll
    exact List.Sublist.map _ (List.drop_sublist _ _)
  obtain ⟨hF, hG, hP⟩ := consMutualFormers_ext hfresh hndDrop
  -- the two models' values agree at every constant the prefix holds
  have hag : ∀ n, ((ConLeche.consMutualFormers (fms.take p.k) env).find? n).isSome = true →
      mp₁.base2.acval n = mp₁'.base2.acval n := by
    intro n hn
    by_cases hmem : ∃ (t : Nat) (f : MutualFormerA), t < p.k ∧ fms[t]? = some f ∧
        n = f.cvTa.name
    · obtain ⟨t, f, ht, hft, rfl⟩ := hmem
      rw [R.h.leaf t f hft, R.hleafM' t f ht hft]
    · have hmem' : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
          n ≠ f.cvTa.name := fun t f ht hft heq => hmem ⟨t, f, ht, hft, heq⟩
      have hne' : ∀ f ∈ fms.take p.k, f.cvTa.name ≠ n := by
        intro f hf heq
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
        have htlt : t < p.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1
          simp only [List.length_take] at this
          omega
        exact hmem' t f htlt (by rw [List.getElem?_take_of_lt htlt] at ht; exact ht) heq.symm
      rw [ConLeche.consMutualFormers_find?_of_ne hne'] at hn
      have hoff : mp₁.base2.acval n = mp.base2.acval n := by
        refine R.h.off n (fun t f hft heq => ?_)
        rcases Nat.lt_or_ge t p.k with hlt | hge
        · exact hmem' t f hlt hft heq
        · -- a copy's former is fresh in the pre-block environment
          rw [heq, R.h.fresh t f hft] at hn
          exact nomatch hn
      obtain ⟨-, -, hac, -⟩ := R.cross
      rw [hoff, hac n hn]
  intro ψ dp e ea he
  -- the model's valuation as a plain function, so the environment may be rewritten
  have key : ∀ A : Name → (Name → Nat) → AnnotTerm,
      (∀ n, ((ConLeche.consMutualFormers (fms.take p.k) env).find? n).isSome = true →
        A n = mp₁'.base2.acval n) →
      denoteMeta A (ConLeche.consMutualFormers fms env) ψ dp e = some ea := by
    intro A hA
    rw [show ConLeche.consMutualFormers fms env
        = ConLeche.consMutualFormers (fms.drop p.k)
            (ConLeche.consMutualFormers (fms.take p.k) env) from by
      rw [← consMutualFormers_append, List.take_append_drop]]
    refine denoteMeta_env_mono hF hG hP dp e ?_
    rw [denoteMeta_acval_congr
      (env := ConLeche.consMutualFormers (fms.take p.k) env) (φ := ψ) hA]
    exact he
  exact key _ hag

omit SF S in
/-- **A pin is scoped at the block's parameters**: its free variables
are the first former's openers, whose own annotations are scoped at
their own depth (`openPisAtFvars_typeWScoped`), so `WScoped_of_leaves`
applies.  `pinRead_of_inferAt` derives this internally; the copies'
readings need it as a fact, because `instPisILP_read` asks it of the
pin's COMPONENTS. -/
theorem NestedPinsRun.pinWScoped {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {q : Nat} (hq : q < st.pins.length) :
    Expr.WScoped b.nP (pinAtE st q).pin ∧ (pinAtE st q).pin.looseBVarsBounded 0 = true := by
  classical
  obtain ⟨-, hcl, -, -⟩ := R.former0
  obtain ⟨-, params, o, hop, hsc⟩ := R.scoped
  have hmem : pinAtE st q ∈ st.pins := List.mem_of_getElem? (hPD q hq).pin
  obtain ⟨hb, hleaf⟩ := hsc _ hmem
  refine ⟨?_, hb⟩
  have hlen : params.length = b.nP := openPisAtFvars_length _ hop
  have hwT : Expr.WScoped 0 f₀.cvTa.type := Expr.WScoped.of_not_hasFvar hcl
  refine WScoped_of_leaves _ fun l hl => ?_
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem (hleaf l hl)
  obtain ⟨ty', hx⟩ := ConLeche.openPisAtFvars_index b.nP f₀.cvTa.type 0 hop pos _ hpos
  rw [Nat.zero_add] at hx
  have hl1 : l.1 = pos := by
    have hx' := hx
    simp only [Expr.fvar.injEq] at hx'
    exact hx'.1
  have hws := openPisAtFvars_typeWScoped b.nP hop hwT pos _ hpos
  refine ⟨by rw [hl1, ← hlen]; exact (List.getElem?_eq_some_iff.mp hpos).1, ?_⟩
  rw [hl1]
  simpa [Expr.fvarTypeD] using hws

omit R SF in
/-- **THE MINTED CONSTRUCTOR, READ** (task #315 L-B, DESIGN §U.38 (e)):
the container's constructor type level-substituted at the pin's levels
and instantiated at its components reads, at the block's parameter
depth, as the CONTAINER's own reading with its parameters peeled at the
components' readings — the fields' telescope instantiated from cut `0`
and the body instantiated at the fields' depth.  Its body is
`ctorBodyAVI` instantiated, whose index arguments are
`CopyCtorInst.es`' right-hand side.

`instPisILP_read` (§U.23) does the work; what this adds is its side
conditions at a container's constructor: the tower's closedness comes
from the reading of a closed type at depth `0`
(`bvarsBelow_of_reading` + `bvarsBelow_mkPisAV_inv`), and the
components' length is the group's (`NestedPinGroupSyn.pinDsLen`). -/
theorem mintRead
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {ks : List Name}
    (hks : ∀ ψ : Name → Nat, (pinsS.getD (q₀ + i') default).ψJ ψ
      = Level.substFn ψ ks (pinsS.getD (q₀ + i') default).lvls)
    (hcl : cAJ.1.type.hasFvar = false) (hbcl : cAJ.1.type.looseBVarsBounded 0 = true)
    {Ds : List Expr}
    (hDsSc : ∀ a ∈ Ds, Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true)
    (ψ : Name → Nat)
    (hspine : DenoteMetaSpine mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env)
      ψ b.nP Ds ((pinsS.getD (q₀ + i') default).Ds ψ))
    {cI : Expr}
    (hinst : Expr.instPis (Expr.instantiateLevelParams ks
      (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) Ds = some cI) :
    denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ b.nP cI
      = some (mkPisAV
          (instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) 0
            ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP))
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) cAJ.2
            (ctorBodyAVI mp₁'.base2 (dJ.memberName i') dJ.nP cAJ.2
              ((pinsS.getD (q₀ + i') default).ψJ ψ)
              (dJ.esF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ))))) := by
  classical
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hlenD : ((pinsS.getD (q₀ + i') default).Ds ψ).length = dJ.nP := S.pinDsLen i' hi' ψ
  have hlenP := hCD.len ((pinsS.getD (q₀ + i') default).ψJ ψ)
  obtain ⟨hbelow, hC⟩ := bvarsBelow_mkPisAV_inv
    (bvarsBelow_of_reading (Expr.WScoped.of_not_hasFvar hcl) hbcl
      (hCD.read ((pinsS.getD (q₀ + i') default).ψJ ψ)))
  rw [Nat.zero_add] at hC
  have hread := instPisILP_read mp₁'.base2 hcl (hks ψ)
    (hCD.read ((pinsS.getD (q₀ + i') default).ψJ ψ)) hbelow hC
    (by rw [hlenD, hlenP]; omega) hDsSc hspine hinst
  rw [hread, hlenD, hlenP, Nat.add_sub_cancel_left]

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
      ((srcAtE st p (q₀ + i')).2.2.any fun a =>
        st₁.newNames.any fun T => a.mentionsConst T) = true ∧
      (∀ a ∈ (srcAtE st p (q₀ + i')).2.2, a.looseBVarsBounded 0 = true) ∧
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
    -, hmint⟩ := hallj j _ hcj
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
    hDsnP, hopb, hinst, hcIb, hcIl, hrep, hmint, hloose', hp1, hp2, hcA, hnF, ?_⟩
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
      -- the pin's components: closed, and mentioning a minted name
      (∀ a ∈ (srcAtE st p (q₀ + i')).2.2, a.looseBVarsBounded 0 = true) ∧
      -- the copy's fields: one rewrite run per instantiated domain
      Fs'.length = cc.nFields ∧
      (∀ l, l < cc.nFields → ∃ st₁ st₂ : ElimState,
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st₁
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
                (fcs.getD l default).1))
          = .ok ((Fs'.getD l default).1, st₂) ∧ st₂.pins <+: st.pins ∧
        ((srcAtE st p (q₀ + i')).2.2.any fun a =>
          st₁.newNames.any fun T => a.mentionsConst T) = true) ∧
      (∃ st₁ st₂ : ElimState,
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st₁
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
                (Expr.mkAppN (.const (dJ.memberName i') (lpsJ.map Level.param))
                  (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ))))
          = .ok (resid', st₂) ∧ st₂.pins <+: st.pins ∧
        ((srcAtE st p (q₀ + i')).2.2.any fun a =>
          st₁.newNames.any fun T => a.mentionsConst T) = true) ∧
      -- the block's entry, the rewritten telescope closed over `pbs₀`
      cbody'.stripPis cc.nFields = some (Fs', resid') ∧
      ctorsA[b.ownOffset (p.k + q₀ + i') + j]? = some cA ∧ cA.2 = cc.nFields ∧
      b.ctors[b.ownOffset (p.k + q₀ + i') + j]?
        = some ⟨⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩, cc.nFields, p.k + q₀ + i'⟩ := by
  classical
  obtain ⟨cc, J, cI, cbody', o, params, pbs₀, stA, stB, cA, cname, hcc, hn, hty, hnf, hJname,
    hDsnP, hopb, hinst, -, -, hrep, hmint, hDsB, -, hp2, hcA, hnF, hbc⟩ :=
    R.copyBody SF S hPD hi' hj
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
  obtain ⟨Fs', resid', hcb, hlenF, hfields, stC, stD, hres, -, hresP, hresN⟩ :=
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
    hesJ, hopb, hDsB, hlenF', ?_,
    ⟨stC, stD, ?_, hresP.trans hp2, ConLeche.elimMint_mono hresN hmint⟩, ?_, hcA, hnF, hbc⟩
  · intro l hl
    obtain ⟨-, st₁, st₂, hrun, -, hpre, hnm⟩ := hfields l (by rw [hbsLen]; exact hl)
    refine ⟨st₁, st₂, ?_, hpre.trans hp2, ConLeche.elimMint_mono hnm hmint⟩
    rw [ConLeche.instTeleSeq_getD _ _ _ _ (by rw [List.length_map, hfl]; exact hl),
      hmapGet _ l (by rw [hfl]; exact hl), hDsnP] at hrun
    exact hrun
  · rw [hDsnP, List.length_drop, show cbs.length - dJ.nP = cc.nFields from by omega] at hres
    exact hres
  · rw [hcb, ← hlenF']
    exact ConLeche.stripPis_mkPisB_self _ _

/-! ## The residual, identified (task #315 L-B, DESIGN §U.37 (e))

A copy's constructor RESIDUAL is the container's — its own member at
the parameter spine, followed by the constructor's index arguments —
instantiated at the pin's components, and the elimination's rewrite
fires at its ROOT: the occurrence test reads only the PARAMETER
arguments, which the instantiation turns into the components, and the
components mention a minted name already at the state the rewrite
starts from (the mint verdict `copyFields` now carries).
`replaceAllNested_occurrence` then says what the residual IS — the
mimic of a pin at the block's parameter openers followed by **the
container's index arguments instantiated, verbatim**: the walk returns
the firing's result unchanged and never descends into them.  That is
the syntactic half of `CopyCtorInst.es`.

No level bookkeeping is needed: the occurrence lemma takes the head's
level arguments as they come, so the substitution `J.lps ↦ lvls` never
has to be computed. -/

/-- **THE COPY'S RESIDUAL** (task #315 L-B): `copyFields`' package with
the residual computed — the mimic of a pin of the elimination, applied
to the block's parameter openers and to the CONTAINER's own index
arguments, level-substituted and instantiated at the pin's components
at the telescope's own cut. -/
theorem NestedPinsRun.copyResid {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) :
    ∃ (cc : ContainerCtor) (J : ContainerMember) (lpsJ : List Name)
      (pcs fcs Fs' : List (Expr × ConLeche.BinderMeta)) (esJ : List Expr)
      (cbody' o : Expr) (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta))
      (cA : ConstantVal × Nat) (cname : Name) (qn : NestedPin) (usJ : List Level),
      cAJ.1.name = cc.name ∧ cAJ.1.type = cc.type ∧ cAJ.2 = cc.nFields ∧
      J.name = (pinsS.getD (q₀ + i') default).J ∧
      (srcAtE st p (q₀ + i')).2.2.length = dJ.nP ∧
      cc.type.stripPis (dJ.nP + cc.nFields) = some (pcs ++ fcs,
        Expr.mkAppN (.const (dJ.memberName i') (lpsJ.map Level.param))
          (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ)) ∧
      pcs.length = dJ.nP ∧ fcs.length = cc.nFields ∧ esJ.length = dJ.nIdxAt i' ∧
      ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (params, o) ∧
      (∀ a ∈ (srcAtE st p (q₀ + i')).2.2, a.looseBVarsBounded 0 = true) ∧
      Fs'.length = cc.nFields ∧
      (∀ l, l < cc.nFields → ∃ st₁ st₂ : ElimState,
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st₁
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
                (fcs.getD l default).1))
          = .ok ((Fs'.getD l default).1, st₂) ∧ st₂.pins <+: st.pins ∧
        ((srcAtE st p (q₀ + i')).2.2.any fun a =>
          st₁.newNames.any fun T => a.mentionsConst T) = true) ∧
      -- the pin the residual's occurrence resolved to
      qn ∈ st.pins ∧
      qn.pin = Expr.mkAppN (.const (dJ.memberName i') usJ) (srcAtE st p (q₀ + i')).2.2 ∧
      -- **the residual**: the mimic at the block's parameters, then the
      -- container's index arguments instantiated, verbatim
      cbody'.stripPis cc.nFields = some (Fs',
        Expr.mkAppN (Expr.mkAppN (.const qn.aux (p.lps.map Level.param)) params)
          (esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
            (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e))) ∧
      ctorsA[b.ownOffset (p.k + q₀ + i') + j]? = some cA ∧ cA.2 = cc.nFields ∧
      b.ctors[b.ownOffset (p.k + q₀ + i') + j]?
        = some ⟨⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩, cc.nFields, p.k + q₀ + i'⟩ := by
  classical
  obtain ⟨cc, J, lpsJ, pcs, fcs, Fs', esJ, cbody', resid', o, params, pbs₀, cA, cname,
    hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hopb, hDsB, hlenF, hfields,
    ⟨stC, stD, hres, hresP, hresM⟩, hcb, hcA, hnF, hbc⟩ := R.copyFields SF S hPD hi' hj
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  have hmemJ : dJ.memberName i' = J.name := by rw [hJname]; exact hI.member
  -- the pin's own container group, read at the member's name
  obtain ⟨-, -, ci, -, -, -, hciP, -⟩ := R.ctorPair SF S hPD hi' hj
  have hciJ : ConLeche.containerInfo? env (dJ.memberName i') = some ci := by
    rw [hmemJ, hJname]; exact hciP
  obtain ⟨cvT₂, caps₂, cvR₂, mI₂, rP₂, rules₂, hfindJ, -, hmemName, -, -⟩ :=
    ConLeche.containerInfo?_inv hciJ
  obtain ⟨M, hM, hMname⟩ : ∃ M ∈ ci.members, M.name = dJ.memberName i' :=
    List.mem_map.mp hmemName
  have hnPci : ci.nP = dJ.nP :=
    (S.ctorsOf i' hi' ci M hciP hM (by rw [hMname, hmemJ]; exact hJname)).2.symm
  -- a pinned container has parameters: its components mention a minted name
  have hDsNe : 0 < (srcAtE st p (q₀ + i')).2.2.length := by
    rcases hDsE : (srcAtE st p (q₀ + i')).2.2 with _ | ⟨d, ds⟩
    · rw [hDsE] at hresM; simp at hresM
    · simp
  have hcut : dJ.nP - 1 + cc.nFields
      = cc.nFields + (srcAtE st p (q₀ + i')).2.2.length - 1 := by
    rw [hDsnP]; omega
  -- the residual's input, as a constant-headed spine at the components
  have hshape : Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
      (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
        (Expr.mkAppN (.const (dJ.memberName i') (lpsJ.map Level.param))
          (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ)))
      = Expr.mkAppN (.const (dJ.memberName i')
          ((lpsJ.map Level.param).map
            (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls)))
          ((srcAtE st p (q₀ + i')).2.2 ++
            esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)) := by
    rw [ConLeche.ilp_mkAppN,
      show Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
          (.const (dJ.memberName i') (lpsJ.map Level.param))
        = .const (dJ.memberName i')
            ((lpsJ.map Level.param).map
              (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls)) from rfl,
      List.map_append, ConLeche.ilp_structPsAt, ConLeche.instSeq_mkAppN_const, List.map_append,
      List.map_map]
    congr 2
    · rw [← hDsnP, show (srcAtE st p (q₀ + i')).2.2.length - 1 + cc.nFields
        = cc.nFields + (srcAtE st p (q₀ + i')).2.2.length - 1 from by omega]
      exact ConLeche.instSeq_structPsAt _ cc.nFields hDsB
    · rw [List.map_map]; rfl
  rw [hshape] at hres
  -- the occurrence: the root fires, and the index arguments come back verbatim
  have htake : ((srcAtE st p (q₀ + i')).2.2 ++
      esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)).take ci.nP
      = (srcAtE st p (q₀ + i')).2.2 := List.take_left' (by rw [hnPci, hDsnP])
  have hdrop : ((srcAtE st p (q₀ + i')).2.2 ++
      esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)).drop ci.nP
      = esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e) :=
    List.drop_left' (by rw [hnPci, hDsnP])
  obtain ⟨qn, hqnMem, hqnPin, hqnEq⟩ :=
    ConLeche.replaceAllNested_occurrence rfl hfindJ hciJ
      (by rw [List.length_append, hnPci, hDsnP]; omega)
      (by rw [htake]; exact hresM) (by rw [htake]; exact hDsB) hres
  rw [htake] at hqnPin
  rw [hdrop] at hqnEq
  subst hqnEq
  exact ⟨cc, J, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, _,
    hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hopb, hDsB, hlenF, hfields,
    hresP.subset hqnMem, hqnPin, hcb, hcA, hnF, hbc⟩

/-! ## The group-internal target, and the two shape arms (task #315 L-B)

`CopyCtorInst.ordF`'s RIGHT arm and `CopyCtorInst.pinF` both claim
that a copy field the auxiliary block classified recursive or
reflexive targets a member OUTSIDE the group's own copies.  The lever
is K.32 (`nestedCopyTargetsOk`, a run conjunct): a group-INTERNAL
target forces the container's own field `l`, its `Π`-prefix peeled, to
be headed by the group member the target names.  `copyGroupTargetHead`
is that conclusion transported to the OPENED domain — the side
`ContainerModeled`'s `ordFree` and `BlockOpened`'s `nestF`/`nestReflF`
speak of — through B1; the two arms then contradict it, the ordinary
one by a MENTION, the nested one by the HEAD (a nested field's domain
mentions members legitimately, inside the pin's components). -/

/-- **K.32 at the copy's field, transported to the CONTAINER's OPENED
domain**: if the auxiliary block classifies the copy's field `l`
recursive or reflexive at a target inside the group's own copies, then
the container's field `l` — as `BlockOpened` sees it — is a
`∀`-telescope (possibly empty) whose body is headed by a member of the
container's own block.

Besides the group's syntactic facts the proof reads three run
conjuncts — the kinds' classification (`classifyMutualKinds`), K.32,
and K.26 through `NestedPinsRun` — the pin's group alignment
(`grpBase`/`grpSize`, which `NestedPinGroupSyn` does not record), and
the container's `ContainerModeled` at the pin's own group together
with the length of its member-name list. -/
theorem NestedPinsRun.copyGroupTargetHead {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    (hK32 : ConLeche.nestedCopyTargetsOk env p b st stored = true)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    (hmn : dJ.memberNames.length = dJ.k)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false
      = true)
    (hlo : p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
    (hhi : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k + q₀ + kJ) :
    ∃ (x : Expr) (d : Nat) (Tl : List (Expr × ConLeche.BinderMeta)) (body : Expr) (nm : Name)
      (us : List Level),
      (dJ.xFvsF i' j)[l]? = some x ∧
      (x.fvarTypeD.piBinders).1.length = d ∧
      x.fvarTypeD.stripPis d = some (Tl, body) ∧
      body.getAppFn = Expr.const nm us ∧
      nm ∈ dJ.memberNames := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  -- the container's own constructor data and closed telescope
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
  -- the target read off the kinds
  have htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = t := by
    rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hcAnF]; exact hlF)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = t
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  rw [htg] at hlo hhi
  -- the copy's kind is recursive or reflexive
  have hrr : r = .recursive ∨ r = .reflexive := by
    rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map, hmutKs]; exact hlks),
      decide_eq_true_eq, kindsOf_getD', hmutKs] at hrss
    show r = _ ∨ r = _
    have hka : kindAt ksG l = r := by
      show (ksG.getD l (.ordinary, 0)).1 = r
      rw [List.getD_eq_getElem?_getD, hrt]; rfl
    rw [hka] at hrss
    exact hrss
  -- the group's member record the target names, and the pin's own
  have hcimem : i' < ci.members.length := by rw [← CMci.k, S.kEq]; exact hi'
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
  -- K.32 at the copy's field
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  obtain ⟨jbs, rJ, domJ, Jt, dK, tbs, jres, us, hsJ, hdJ, hJt, hpk, hfn⟩ :=
    ConLeche.nestedCopyTargetsOk_head hK32 hkP hq PD.pin hkq ha
      (by rw [hpinJ]; exact hciP)
      (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
      (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
      hkfj hac hcJ hrt hrr (by rw [hgb]; exact hlo) (by rw [hgb, hgs]; exact hhi)
  rw [hgb] at hJt
  -- the target IS a member of the container's block
  have hn2 : t - p.k - q₀ < dJ.k := by rw [S.kEq]; omega
  have hJtname : dJ.memberName (t - p.k - q₀) = Jt.name := (CMci.member _ Jt hJt).1
  have hJtmem : Jt.name ∈ dJ.memberNames := by
    rw [← hJtname]
    show dJ.memberNames.getD (t - p.k - q₀) .anonymous ∈ _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  -- the container's closed field domain at `l`, and B1's opened twin
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hsJ' : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (jbs, rJ) := by
    have h1 : cJ.type = cAJ.1.type := by rw [hty, hccJ]
    have h2 : cJ.nFields = cAJ.2 := by rw [hnf, hccJ]
    rw [← h1, ← h2, ← hnPci]
    exact hsJ
  have hjbs : jbs = cbs := (Prod.mk.inj (Option.some.inj (hsJ'.symm.trans hstripJ))).1
  rw [hjbs] at hdJ
  have hdrop : (cbs.drop dJ.nP)[l]? = some domJ := by
    rw [List.getElem?_drop, ← hnPci]; exact hdJ
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen]; exact hlF)⟩
  have hopen : x.fvarTypeD
      = Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) domJ.1 :=
    blockCtorFieldDomain hCD
      (show cAJ.1.type.stripPis (dJ.nP + cAJ.2)
          = some (cbs.take dJ.nP ++ cbs.drop dJ.nP, _) from by
        rw [List.take_append_drop]; exact hstripJ)
      (by rw [List.length_take]; omega) hx hdrop
  -- the closed domain is the peeled telescope; instantiation keeps it
  have hmk : domJ.1 = ConLeche.mkPisB tbs jres := ConLeche.stripPis_mkPisB _ hpk
  have htbs : tbs.length = dK := Expr.stripPis_length _ hpk
  have hopenLen : (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l).length ≤ dJ.nP + l - 1 + 1 := by
    rw [List.length_append, hCD.pLen, List.length_take]; omega
  have hx2 : x.fvarTypeD
      = ConLeche.mkPisB
          (ConLeche.instTeleSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) tbs)
          (Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l)
            (dJ.nP + l - 1 + tbs.length) jres) := by
    rw [hopen, hmk, ConLeche.instSeq_mkPisB _ _ _ _ hopenLen]
  have hbodyHead : (Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l)
      (dJ.nP + l - 1 + tbs.length) jres).getAppFn = Expr.const Jt.name us :=
    os_instSeq_head hfn _ _
  have hTlLen : (ConLeche.instTeleSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l)
      (dJ.nP + l - 1) tbs).length = tbs.length := ConLeche.instTeleSeq_length _ _ _
  refine ⟨x, tbs.length,
    ConLeche.instTeleSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) tbs,
    Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1 + tbs.length) jres,
    Jt.name, us, hx, ?_, ?_, hbodyHead, hJtmem⟩
  · rw [hx2, ConLeche.rk_piBinders_mkPisB_length _ _ hbodyHead, hTlLen]
  · rw [hx2, ← hTlLen]
    exact ConLeche.stripPis_mkPisB_self _ _

/-- **`CopyCtorInst.ordF`'s right arm, the target conjunct**: a copy
field that the auxiliary block classified recursive or reflexive while
the CONTAINER's field `l` is ORDINARY targets a member outside the
group's own copies `[p.k + q₀, p.k + q₀ + kJ)` — otherwise the
container's ordinary field would mention a member of its own block,
which `ContainerModeled.ordFree` excludes. -/
theorem NestedPinsRun.copyOrdFRight_shape {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    (hK32 : ConLeche.nestedCopyTargetsOk env p b st stored = true)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    (hmn : dJ.memberNames.length = dJ.k)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {ψJ : Name → Nat} {l : Nat} (hl : l < ((dJ.Fss i' ψJ).getD j []).length)
    (hord : ((dJ.rss i').getD j []).getD l false = false)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false
      = true) :
    ¬ (p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 ∧
        ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k + q₀ + kJ) := by
  classical
  rintro ⟨hlo, hhi⟩
  have hlF : l < cAJ.2 := by
    obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
    rw [hI.Fss_length hj ψJ] at hl; exact hl
  obtain ⟨x, d, Tl, body, nm, us, hx, -, hstr, hhead, hnm⟩ :=
    R.copyGroupTargetHead SF S hPD hkindsRun hK32 hi' hgb hgs CM hmn hj hlF hrss hlo hhi
  -- the container's ordinary field would mention a member
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hmention : x.fvarTypeD.mentionsConst nm = true := by
    rw [ConLeche.stripPis_mkPisB _ hstr]
    refine ConLeche.mentionsConst_mkPisB Tl body ?_
    have := ConLeche.mentionsConst_mkAppN_of_fn (T := nm) body.getAppArgs body.getAppFn
      (by rw [hhead]; simp [Expr.mentionsConst])
    rw [Expr.mkAppN_getApp body] at this
    exact this
  have hkindOrd : (dJ.ksF i' j).getD l .ordinary = .ordinary := by
    have hlen : l < (dJ.ksF i' j).length := by rw [hCD.ksLen]; exact hlF
    have hrs : ((dJ.rss i').getD j []).getD l false
        = decide ((dJ.ksF i' j).getD l .ordinary = .recursive ∨
            (dJ.ksF i' j).getD l .ordinary = .reflexive) := by
      rw [show (dJ.rss i').getD j [] = rsOf (dJ.ksF i' j) from rssOfK_getD hjlt,
        rsOf_getD hlen]
    rw [hrs, decide_eq_false_iff_not] at hord
    rcases hCD.opened.kinds l hlF with h | h | h
    · exact h
    · exact absurd (Or.inl h) hord
    · exact absurd (Or.inr h) hord
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, -⟩ := R.ctorPair SF S hPD hi' hj
  have hF := (CM ci hciP).ordFree i' j l x (by rw [S.kEq]; exact hi') hjlt hx hkindOrd
  rw [ConLeche.mentionsMember, List.any_eq_false] at hF
  exact absurd hmention (by simpa using hF nm hnm)

/-- **`CopyCtorInst.pinF`'s target conjunct**: a copy field that the
auxiliary block classified recursive or reflexive while the
CONTAINER's field `l` is recursive at one of the container's OWN PINS
targets a member outside the group's own copies — the container's
field is headed, under its own telescope, by the pin's container, and
`ContainerModeled.pinsNotMembers` says that is no member of the
container's block.

(The arm's first conjunct — the copy's field IS recursive — is the
elimination's occurrence chain and is not proved here.) -/
theorem NestedPinsRun.copyPinF_shape {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    (hK32 : ConLeche.nestedCopyTargetsOk env p b st stored = true)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    (hmn : dJ.memberNames.length = dJ.k)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {ψJ : Name → Nat} {l : Nat} (hl : l < ((dJ.Fss i' ψJ).getD j []).length)
    (hrecC : ((dJ.rss i').getD j []).getD l false = true)
    (hnest : ¬ dJ.tgts i' j l < dJ.k)
    (hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false
      = true) :
    ¬ (p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 ∧
        ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k + q₀ + kJ) := by
  classical
  rintro ⟨hlo, hhi⟩
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hlF : l < cAJ.2 := by rw [hI.Fss_length hj ψJ] at hl; exact hl
  obtain ⟨x, d, Tl, body, nm, us, hx, hpb, hstr, hhead, hnm⟩ :=
    R.copyGroupTargetHead SF S hPD hkindsRun hK32 hi' hgb hgs CM hmn hj hlF hrss hlo hhi
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, -⟩ := R.ctorPair SF S hPD hi' hj
  have hCM : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  -- the container's field is nested at one of its own pins
  have hnestOf : dJ.nestOf i' j l = some (dJ.tgts i' j l - dJ.k) := by
    show (if dJ.tgts i' j l < dJ.k then none else some _) = _
    rw [if_neg hnest]
  have hqlt : dJ.tgts i' j l - dJ.k < dJ.nPins := by
    have := hI.tgtsLt i' j l hI.memberLt hjlt (by rw [hCD.ksLen]; exact hlF)
    omega
  have hnotmem := hCM.pinsNotMembers _ hqlt
  -- the container's field's head is the pin's container, not a member
  have hkindLen : l < (dJ.ksF i' j).length := by rw [hCD.ksLen]; exact hlF
  have hkinds : (dJ.ksF i' j).getD l .ordinary = .recursive ∨
      (dJ.ksF i' j).getD l .ordinary = .reflexive := by
    rw [show (dJ.rss i').getD j [] = rsOf (dJ.ksF i' j) from rssOfK_getD hjlt,
      rsOf_getD hkindLen, decide_eq_true_eq] at hrecC
    exact hrecC
  have hmkb : x.fvarTypeD = ConLeche.mkPisB Tl body := ConLeche.stripPis_mkPisB _ hstr
  have hclash : nm = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J := by
    rcases hkinds with hk | hk
    · -- finitary: the opened domain is the application itself
      obtain ⟨hfn, -⟩ := hCD.opened.nestF l x _ hx hnestOf hk
      have hbody : body = x.fvarTypeD := by
        rcases Tl with _ | ⟨t0, ts⟩
        · rw [hmkb, ConLeche.mkPisB_nil]
        · exfalso
          rw [hmkb, ConLeche.mkPisB_cons,
            show (Expr.forallE t0.1 (ConLeche.mkPisB ts body) t0.2).getAppFn
              = Expr.forallE t0.1 (ConLeche.mkPisB ts body) t0.2 from rfl] at hfn
          exact nomatch hfn
      rw [hbody, hfn] at hhead
      exact (ConLeche.Expr.const.inj hhead).1.symm
    · -- reflexive: the opened domain's telescope is `Tl`
      obtain ⟨afvs, body', hopA, -, -, hfn, -⟩ := hCD.opened.nestReflF l x _ hx hnestOf hk
      rw [hpb] at hopA
      rw [openPisAtFvars_instSeq d hopA hstr, os_instSeq_head hhead afvs (d - 1)] at hfn
      exact (ConLeche.Expr.const.inj hfn).1
  rw [hclash] at hnm
  exact absurd hnm hnotmem


end Assembly

end ConLeche.Model

