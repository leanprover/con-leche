module

public import ConLeche.Model.Inductives.NestedCopyRead
import ConLeche.Model.Inductives.NestedCopyFound
import ConLeche.Model.Inductives.BlockRecFrames
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedCopyGlue
import ConLeche.Verify.Inductives.NestedCopyProv
import ConLeche.Verify.Inductives.NestedCopyInstU
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.Inductives.NestedCopyRewrite
import ConLeche.Verify.Inductives.NestedCopyNorm
import ConLeche.Verify.Inductives.NestedOpenSpine
import ConLeche.Verify.Inductives.NestedCopyKinds
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedAuxFormers
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Model.Inductives.FixRecReadDefs
import ConLeche.Model.Inductives.MutualNorm
import ConLeche.Model.Inductives.BlockRecBridge
import ConLeche.Model.Inductives.BlockRecValid
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

/-- **B1's HEAD corollary at a container's field**: the closed field
domain has the head the OPENED one shows — the substitution puts
`fvar`s where the `bvar`s stood and can never manufacture a `const`
head (`os_field_domain_head`). -/
theorem blockCtorFieldHead {m : EnvModel V env} {env₀ : Env} {T : Name}
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
    {l : Nat} {x : Expr} {bd : Expr × ConLeche.BinderMeta} {n : Name} {us : List Level}
    (hx : xFvs[l]? = some x) (hb : fcs[l]? = some bd)
    (hhead : x.fvarTypeD.getAppFn = Expr.const n us) :
    bd.1.getAppFn = Expr.const n us := by
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  exact ConLeche.os_field_domain_head nP nF l
    (openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX))
    hstrip hD.pLen hpcs hx hb hhead

/-- **B1's SPINE corollary at a container's field**: the opened
domain's arguments are the closed one's, instantiated one for one, so
the two spines have the same length (`os_field_domain_args`). -/
theorem blockCtorFieldArgs {m : EnvModel V env} {env₀ : Env} {T : Name}
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
    x.fvarTypeD.getAppArgs.length = bd.1.getAppArgs.length := by
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  rw [ConLeche.os_field_domain_args nP nF l
    (openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX))
    hstrip hD.pLen hpcs hx hb, List.length_map]

/-- An instantiation sequence keeps a constant head. -/
theorem os_instSeq_head {e : Expr} {n : Name} {us : List Level}
    (h : e.getAppFn = Expr.const n us) (as : List Expr) (t : Nat) :
    (Expr.instSeq as t e).getAppFn = Expr.const n us := by
  have he : Expr.mkAppN (Expr.const n us) e.getAppArgs = e := by
    rw [← h]; exact Expr.mkAppN_getApp e
  rw [← he, ConLeche.instSeq_mkAppN_const, Expr.getAppFn_mkAppN]
  rfl

omit [SetTheory V] in
/-- **AN INSTANTIATION ABOVE A LIFT COMMUTES WITH IT** (task #315 L-B):
`AVExprSubst.inst_liftN_comm` iterated over the list — instantiating a
lift-of-`B` at the cut the lift made is the lift of the instantiation
at the bottom.  This is the step from a container's NESTED FIELD
reading, where the pin's components are lifted over the field binders,
to the block pin's components, which carry no lift. -/
theorem instAll_liftN0 : ∀ (ds : List AnnotTerm) (l : Nat) (B : AnnotTerm),
    AnnotTerm.instAll ds l (AnnotTerm.liftN l B 0)
      = AnnotTerm.liftN l (AnnotTerm.instAll ds 0 B) 0
  | [], _, _ => rfl
  | d :: ds, l, B => by
    show AnnotTerm.instAll ds l (AnnotTerm.inst (AnnotTerm.liftN l B 0) d (l + ds.length)) = _
    rw [AVExprSubst.inst_liftN_comm B (by omega) d,
      show l + ds.length - l = ds.length from by omega,
      instAll_liftN0 ds l (AnnotTerm.inst B d ds.length)]
    show _ = AnnotTerm.liftN l (AnnotTerm.instAll ds 0
      (AnnotTerm.inst B d (0 + ds.length))) 0
    rw [Nat.zero_add]


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
/-- `crossUp` along a READ SPINE: a spine read at the prefix formers'
model is read the same at the whole block's. -/
theorem NestedPinsRun.crossUpSpine (ψ : Name → Nat) (dp : Nat) :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ dp as vs →
      DenoteMetaSpine mp₁.base2.acval (ConLeche.consMutualFormers fms env) ψ dp as vs := by
  intro as vs h
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (R.crossUp ψ dp _ ha) ih

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

omit R SF in
/-- **THE MINTED CONSTRUCTOR'S RESIDUAL, READ** (task #315 L-B, DESIGN
§U.38 (e) step 5): the minted constructor opened at its FIELD binders
reads as the container's constructor body instantiated at the pin's
components — the member's own value applied to the parameter variables
and to **the container's index readings instantiated**, which is
`CopyCtorInst.es`' right-hand side.  `denoteMeta` on a `∀` already
reads its body opened (`denoteMeta_openPisAtFvars`), so nothing stands
between `mintRead` and this. -/
theorem mintResidRead
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
      (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) Ds = some cI)
    {xf : List Expr} {cIbody : Expr}
    (hop : ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xf, cIbody)) :
    denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env)
        ψ (b.nP + cAJ.2) cIbody
      = some (AnnotTerm.mkAppN
          (mp₁'.base2.acval (dJ.memberName i') ((pinsS.getD (q₀ + i') default).ψJ ψ))
          ((paramBvars dJ.nP cAJ.2).map
              (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) cAJ.2)
            ++ (dJ.esF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).map
              (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) cAJ.2))) := by
  classical
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hlenT : (instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) 0
      ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP)).length = cAJ.2 := by
    rw [instTeleP_length, List.length_drop, hCD.len ((pinsS.getD (q₀ + i') default).ψJ ψ)]
    omega
  have hstrip := stripPisAV_mkPisAV
    (instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) 0
      ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP))
    (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) cAJ.2
      (ctorBodyAVI mp₁'.base2 (dJ.memberName i') dJ.nP cAJ.2
        ((pinsS.getD (q₀ + i') default).ψJ ψ)
        (dJ.esF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ))))
  rw [hlenT] at hstrip
  have hbody := denoteMeta_openPisAtFvars cAJ.2 hop
    (mintRead S hi' hj hks hcl hbcl hDsSc ψ hspine hinst) hstrip
  rw [hbody]
  congr 1
  show AnnotTerm.instAll _ cAJ.2
      (AnnotTerm.mkAppN (mp₁'.base2.acval (dJ.memberName i') _) (paramBvars dJ.nP cAJ.2 ++ _)) = _
  rw [AnnotTerm.instAll_mkAppN, List.map_append,
    AnnotTerm.instAll_eq_self (fun y k => acval_inst_self mp₁'.base2 _ _ y k)]

omit R SF in
/-- **THE MINTED CONSTRUCTOR'S FIELD DOMAINS, READ** (task #315 L-B):
the minted constructor opened at its FIELD binders reads its `l`-th
domain as the CONTAINER's own `l`-th field domain reading, instantiated
at the pin's components at the field's own cut.  `mintRead` names the
whole tower, `denoteMeta_openPisAtFvars_dom` picks the binder out of
it, and `instTeleP` at `l` is that instantiation. -/
theorem mintFieldRead
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
      (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) Ds = some cI)
    {xf : List Expr} {cIbody : Expr}
    (hop : ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xf, cIbody))
    {l : Nat} (hl : l < cAJ.2) {x : Expr} (hx : xf[l]? = some x) :
    denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env)
        ψ (b.nP + l) x.fvarTypeD
      = some (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l
          ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD (dJ.nP + l) default).2.2) := by
  classical
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hlenDrop : ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP).length
      = cAJ.2 := by
    rw [List.length_drop, hCD.len ((pinsS.getD (q₀ + i') default).ψJ ψ)]
    omega
  have hlenT : (instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) 0
      ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP)).length = cAJ.2 := by
    rw [instTeleP_length, hlenDrop]
  have hstrip := stripPisAV_mkPisAV
    (instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) 0
      ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP))
    (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) cAJ.2
      (ctorBodyAVI mp₁'.base2 (dJ.memberName i') dJ.nP cAJ.2
        ((pinsS.getD (q₀ + i') default).ψJ ψ)
        (dJ.esF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ))))
  rw [hlenT] at hstrip
  have hdom := denoteMeta_openPisAtFvars_dom cAJ.2 hop
    (mintRead S hi' hj hks hcl hbcl hDsSc ψ hspine hinst) hstrip l x hx
  rw [hdom]
  congr 1
  -- the tower's `l`-th datum IS the container's, instantiated at cut `l`
  have hmapGetD : ∀ (L : List (Nat × Nat × AnnotTerm)) (n : Nat), n < L.length →
      (L.map (·.2.2)).getD n default = (L.getD n default).2.2 := by
    intro L n hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl
  have h1 : ((instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) 0
        ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP)).getD l default).2.2
      = AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l
          (((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP).getD l default).2.2 := by
    rw [← hmapGetD _ l (by rw [hlenT]; exact hl), instTeleP_map, instTele_getD _ 0 _ l
      (by rw [List.length_map, hlenDrop]; exact hl), Nat.zero_add,
      hmapGetD _ l (by rw [hlenDrop]; exact hl)]
  rw [h1, getD_dropD]

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
    ∃ (cc : ContainerCtor) (J : ContainerMember) (ci : ContainerInfo) (cI cbody' o : Expr)
      (params : List Expr)
      (pbs₀ : List (Expr × ConLeche.BinderMeta)) (st₁ st₂ : ElimState)
      (cA : ConstantVal × Nat) (cname : Name),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci ∧
      J ∈ ci.members ∧ J.ctors[j]? = some cc ∧
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
      -- the container's constructor type, and the pin's level substitution
      -- at the container member's OWN parameters
      cc.type.hasFvar = false ∧ cc.type.looseBVarsBounded 0 = true ∧
      (∀ ψ : Name → Nat, (pinsS.getD (q₀ + i') default).ψJ ψ
        = Level.substFn ψ J.lps (pinsS.getD (q₀ + i') default).lvls) ∧
      -- the block's parameter frame, and the rewrite's output in it
      params.length = b.nP ∧
      (∀ l, l < b.nP → ∃ ty, params[l]? = some (Expr.fvar l ty)) ∧
      pbs₀.length = b.nP ∧ (∀ x ∈ pbs₀, x.1.hasFvar = false) ∧
      (∃ o' : Expr, f₀.cvTa.type.stripPis b.nP = some (pbs₀, o')) ∧
      cbody'.looseBVarsBounded 0 = true ∧
      (∀ l ∈ cbody'.fvarLeaves, Expr.fvar l.1 l.2 ∈ params) ∧
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
  obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, hfT₀, -, -, -, hallM⟩ :=
    ConLeche.containerInfo?_inv hciP
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, -, -, hlpsJ, -, hlpsEq, -, hct⟩ := hallM J hJmem
  obtain ⟨hccb, hccf⟩ : cc.type.looseBVarsBounded 0 = true ∧ cc.type.hasFvar = false := by
    obtain ⟨r, cvc, hrj, hccn, hfc, htc⟩ := hct j cc hcc
    obtain ⟨hwf1, -, -, hwf4, -⟩ :=
      mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfc)
    exact ⟨by rw [htc]; exact hwf4, by rw [htc]; exact hwf1⟩
  -- the pin's level substitution, at the container member's own parameters
  have hksJ : ∀ ψ : Name → Nat, (pinsS.getD (q₀ + i') default).ψJ ψ
      = Level.substFn ψ J.lps (pinsS.getD (q₀ + i') default).lvls := by
    have hpinAt : ∀ n, (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
        srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt n = pinsS.getD n default :=
      fun _ => rfl
    obtain ⟨cvTs, capss, -, -, -, -, hfinds, -, hψJs⟩ := S.stored i' hi'
    rw [hpinAt] at hfinds hψJs
    obtain ⟨hFc, -, -, -⟩ := R.cross
    have h₁ := hFc _ (.indInfo cvT₀ caps₀) (fun _ _ _ _ h => nomatch h) hfT₀
    obtain rfl : cvT₀ = cvTs :=
      (ConstantInfo.indInfo.inj (Option.some.inj (h₁.symm.trans hfinds))).1
    intro ψ
    rw [hψJs ψ, hlpsJ, hlpsEq]
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
  -- the openers, positionally, and the frame they define
  have hidxP : ∀ l, l < params.length → ∃ ty, params[l]? = some (Expr.fvar l ty) := by
    intro l hl
    obtain ⟨ty, hty'⟩ := openPisAtFvars_index _ _ _ hop l _ (List.getElem?_eq_getElem hl)
    refine ⟨ty, ?_⟩
    rw [List.getElem?_eq_getElem hl, hty', Nat.zero_add]
  have hpb : ∀ a ∈ params, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨l, hl⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, hty'⟩ := hidxP l (List.getElem?_eq_some_iff.mp hl).1
    obtain rfl : a = Expr.fvar l ty := Option.some.inj (hl.symm.trans hty')
    rfl
  have hpl : ∀ a ∈ params, ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ params := by
    intro a ha l hl
    rcases openPisAtFvars_leaves _ hopb l (Or.inr ⟨a, ha, hl⟩) with h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hf0] at h0
      exact nomatch h0
    · exact h0
  obtain ⟨hcbb, hcbl⟩ := ConLeche.replaceAllNested_frame hpb hpl cI hrep hcIb hcIl
  refine ⟨cc, J, ci, cI, cbody', o, params, pbs₀, st₁, st₂, cA, cname, hciP, hJmem, hcc, hn, hty,
    hnf, hJname,
    hDsnP, hopb, hinst, hcIb, hcIl, hrep, hmint, hloose', hp1, hp2, hccf, hccb, hksJ,
    by rw [hnPb]; exact hplen, fun l hl => hidxP l (by rw [hplen, ← hnPb]; exact hl),
    by rw [hnPb]; exact hpbs₀len, hpbs₀f, ⟨o', by rw [hnPb, ht₀ty]; exact hstrip⟩,
    hcbb, hcbl, hcA, hnF, ?_⟩
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
    ∃ (cc : ContainerCtor) (J : ContainerMember) (ci : ContainerInfo) (lpsJ : List Name)
      (pcs fcs Fs' : List (Expr × ConLeche.BinderMeta)) (esJ : List Expr)
      (cbody' resid' o : Expr) (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta))
      (cA : ConstantVal × Nat) (cname : Name),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci ∧
      J ∈ ci.members ∧ J.ctors[j]? = some cc ∧
      cAJ.1.name = cc.name ∧ cAJ.1.type = cc.type ∧ cAJ.2 = cc.nFields ∧
      J.name = (pinsS.getD (q₀ + i') default).J ∧
      (srcAtE st p (q₀ + i')).2.2.length = dJ.nP ∧
      -- the container's constructor as a telescope: parameters, fields,
      -- and the residual at its own member
      cc.type.stripPis (dJ.nP + cc.nFields) = some (pcs ++ fcs,
        Expr.mkAppN (.const (dJ.memberName i') (lpsJ.map Level.param))
          (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ)) ∧
      pcs.length = dJ.nP ∧ fcs.length = cc.nFields ∧ esJ.length = dJ.nIdxAt i' ∧
      cc.type.hasFvar = false ∧ cc.type.looseBVarsBounded 0 = true ∧
      (∀ ψ : Name → Nat, (pinsS.getD (q₀ + i') default).ψJ ψ
        = Level.substFn ψ J.lps (pinsS.getD (q₀ + i') default).lvls) ∧
      -- the block's parameter openers
      ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (params, o) ∧
      params.length = b.nP ∧
      (∀ l, l < b.nP → ∃ ty, params[l]? = some (Expr.fvar l ty)) ∧
      pbs₀.length = b.nP ∧ (∀ x ∈ pbs₀, x.1.hasFvar = false) ∧
      (∃ o' : Expr, f₀.cvTa.type.stripPis b.nP = some (pbs₀, o')) ∧
      cbody'.looseBVarsBounded 0 = true ∧
      (∀ l ∈ cbody'.fvarLeaves, Expr.fvar l.1 l.2 ∈ params) ∧
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
      -- the MINTED constructor, stripped: its telescope and the
      -- container's residual instantiated at the pin's components
      (∃ (cI : Expr) (fcs' : List (Expr × ConLeche.BinderMeta)),
        Expr.instPis (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls cc.type)
            (srcAtE st p (q₀ + i')).2.2 = some cI ∧
        cI.stripPis cc.nFields = some (fcs',
          Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
            (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
              (Expr.mkAppN (.const (dJ.memberName i') (lpsJ.map Level.param))
                (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ)))) ∧
        ∀ l, l < cc.nFields → (fcs'.getD l default).1
          = Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
                (fcs.getD l default).1)) ∧
      -- the block's entry, the rewritten telescope closed over `pbs₀`
      cbody'.stripPis cc.nFields = some (Fs', resid') ∧
      ctorsA[b.ownOffset (p.k + q₀ + i') + j]? = some cA ∧ cA.2 = cc.nFields ∧
      b.ctors[b.ownOffset (p.k + q₀ + i') + j]?
        = some ⟨⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩, cc.nFields, p.k + q₀ + i'⟩ := by
  classical
  obtain ⟨cc, J, ci, cI, cbody', o, params, pbs₀, stA, stB, cA, cname, hciP, hJmem, hcc, hn, hty,
    hnf, hJname,
    hDsnP, hopb, hinst, -, -, hrep, hmint, hDsB, -, hp2, hccf, hccb, hksJ, hplenB, hidxP,
    hpbs₀len, hpbs₀f, hstripF, hcbb, hcbl, hcA, hnF, hbc⟩ := R.copyBody SF S hPD hi' hj
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
  have hcut : (srcAtE st p (q₀ + i')).2.2.length - 1 + (cbs.drop dJ.nP).length
      = dJ.nP - 1 + cc.nFields := by rw [hDsnP, List.length_drop]; omega
  rw [hcut] at hinst
  refine ⟨cc, J, ci, cvT.levelParams, cbs.take dJ.nP, cbs.drop dJ.nP, Fs', esJ, cbody', resid', o,
    params, pbs₀, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hDsnP, by rw [hsplit]; exact hstripJ, hpl, hfl,
    hesJ, hccf, hccb, hksJ, hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, hstripF, hcbb, hcbl,
    hDsB, hlenF', ?_,
    ⟨stC, stD, ?_, hresP.trans hp2, ConLeche.elimMint_mono hresN hmint⟩,
    ⟨_, _, hinst, by rw [← hbsLen]; exact ConLeche.stripPis_mkPisB_self _ _, ?_⟩,
    ?_, hcA, hnF, hbc⟩
  · intro l hl
    obtain ⟨-, st₁, st₂, hrun, -, hpre, hnm⟩ := hfields l (by rw [hbsLen]; exact hl)
    refine ⟨st₁, st₂, ?_, hpre.trans hp2, ConLeche.elimMint_mono hnm hmint⟩
    rw [ConLeche.instTeleSeq_getD _ _ _ _ (by rw [List.length_map, hfl]; exact hl),
      hmapGet _ l (by rw [hfl]; exact hl), hDsnP] at hrun
    exact hrun
  · rw [hDsnP, List.length_drop, show cbs.length - dJ.nP = cc.nFields from by omega] at hres
    exact hres
  · intro l hl
    rw [ConLeche.instTeleSeq_getD _ _ _ _ (by rw [List.length_map, hfl]; exact hl),
      hmapGet _ l (by rw [hfl]; exact hl), hDsnP]
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
    ∃ (cc : ContainerCtor) (J : ContainerMember) (ci : ContainerInfo) (lpsJ : List Name)
      (pcs fcs Fs' : List (Expr × ConLeche.BinderMeta)) (esJ : List Expr)
      (cbody' o : Expr) (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta))
      (cA : ConstantVal × Nat) (cname : Name) (qn : NestedPin) (usJ : List Level),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci ∧
      J ∈ ci.members ∧ J.ctors[j]? = some cc ∧
      cAJ.1.name = cc.name ∧ cAJ.1.type = cc.type ∧ cAJ.2 = cc.nFields ∧
      J.name = (pinsS.getD (q₀ + i') default).J ∧
      (srcAtE st p (q₀ + i')).2.2.length = dJ.nP ∧
      cc.type.stripPis (dJ.nP + cc.nFields) = some (pcs ++ fcs,
        Expr.mkAppN (.const (dJ.memberName i') (lpsJ.map Level.param))
          (ConLeche.structPsAt cc.nFields dJ.nP ++ esJ)) ∧
      pcs.length = dJ.nP ∧ fcs.length = cc.nFields ∧ esJ.length = dJ.nIdxAt i' ∧
      cc.type.hasFvar = false ∧ cc.type.looseBVarsBounded 0 = true ∧
      (∀ ψ : Name → Nat, (pinsS.getD (q₀ + i') default).ψJ ψ
        = Level.substFn ψ J.lps (pinsS.getD (q₀ + i') default).lvls) ∧
      ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some (params, o) ∧
      params.length = b.nP ∧
      (∀ l, l < b.nP → ∃ ty, params[l]? = some (Expr.fvar l ty)) ∧
      pbs₀.length = b.nP ∧ (∀ x ∈ pbs₀, x.1.hasFvar = false) ∧
      (∃ o' : Expr, f₀.cvTa.type.stripPis b.nP = some (pbs₀, o')) ∧
      cbody'.looseBVarsBounded 0 = true ∧
      (∀ l ∈ cbody'.fvarLeaves, Expr.fvar l.1 l.2 ∈ params) ∧
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
      -- the MINTED constructor, stripped: the container's own member at
      -- the components followed by the SAME index arguments
      (∃ (cI : Expr) (fcs' : List (Expr × ConLeche.BinderMeta)),
        Expr.instPis (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls cc.type)
            (srcAtE st p (q₀ + i')).2.2 = some cI ∧
        cI.stripPis cc.nFields = some (fcs',
          Expr.mkAppN (.const (dJ.memberName i') usJ)
            ((srcAtE st p (q₀ + i')).2.2 ++
              esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
                (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e))) ∧
        ∀ l, l < cc.nFields → (fcs'.getD l default).1
          = Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
                (fcs.getD l default).1)) ∧
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
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', resid', o, params, pbs₀, cA, cname,
    hciP, hJmem, hJcc,
    hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ, hopb, hplenB,
    hidxP, hpbs₀len, hpbs₀f, hstripF, hcbb, hcbl, hDsB, hlenF, hfields,
    ⟨stC, stD, hres, hresP, hresM⟩, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ :=
    R.copyFields SF S hPD hi' hj
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  have hmemJ : dJ.memberName i' = J.name := by rw [hJname]; exact hI.member
  -- the pin's own container group, read at the member's name
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
  rw [hshape] at hres hstripCI
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
  exact ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, _,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ, hopb, hplenB,
    hidxP, hpbs₀len, hpbs₀f, hstripF, hcbb, hcbl, hDsB, hlenF, hfields,
    hresP.subset hqnMem, hqnPin, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩

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

/-- **K.60 AT THE COPY'S FIELD** (task #315 PINF, DESIGN "K.60
LANDED"): `copyGroupTargetHead`'s converse.  That one runs from the
auxiliary block's classification to the container's field; this one
runs the other way — from a CONTAINER field that is finitary recursive
at one of the container's OWN pins to the copy's corresponding field
being classified `.recursive` into a PIN of the block.

Nothing derives it: the copies come from `mkCopy` + `replaceAllNested`,
a rewrite the model tier has no theorem about, so the fact is the
kernel's record K.60 (`nestedCopyPinFieldsOk`) and this is its
inversion plumbed to the model's spelling.

**Every part of K.60's guard is a fact the model holds**, and that is
what the record was designed for: the head is
`ContainerModeled.nestArgsMentionAbs`' own (through `BlockOpened.nestF`
and `blockCtorFieldHead`), the head's non-membership is
`pinsNotMembers`, the further container is `pinNP`/`pinConts`, and the
mention in the parameter part is `nestArgsMentionAbs` — the ABSTRACT
clause, because K.60 reads the stored constructor stripped and the
opened spelling does not travel that way.

Its two conclusions are `NestedPinsShapePinF`'s conjunct 1 and
`copyPinFCorr`'s `hkA`. -/
theorem NestedPinsRun.copyPinFKind {pbs : List (Expr × ConLeche.BinderMeta)}
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
    kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = .recursive ∧
    p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 := by
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
  -- K.60, inverted
  have hpinJ : (pinAtE st (q₀ + i')).container = (pinsS.getD (q₀ + i') default).J :=
    (SF.pinRec _ _ PD.pin).1.symm
  obtain ⟨hrEq, hpk⟩ := ConLeche.nestedCopyPinFieldsOk_head R.hK60 hkP hq PD.pin hkq
    (by rw [hpinJ]; exact hciP)
    (by rw [hgb, Nat.add_sub_cancel_left]; exact hJ₂)
    (show j < (kindsP[q₀ + i']'hkqlt).length from (List.getElem?_eq_some_iff.mp hkfj).1)
    hkfj hcJ hsJ hrt (by rw [hnPci]; exact hdomJ) hheadA hnm hciK he hme
  -- read the two conclusions off the block's own tables
  have hka : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = r := by
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).1 = r
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  have htg : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = t := by
    rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hcAnF]; exact hlF)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = t
    rw [hmutKs, List.getD_eq_getElem?_getD, hrt]; rfl
  exact ⟨by rw [hka, hrEq], by rw [htg]; exact hpk⟩

/-- **A COPY FIELD'S TARGET IS A TARGET OF THE AUXILIARY BLOCK** (task
#315 L-B): the block's members are its own `p.k` formers followed by
one mimic per pin, and the classification's targets are members
(`MutualFormersFacts.ksJ`), so a copy's field targets below
`p.k + pinsS.length` — the bound `CopyCtorShape`'s two rewritten arms
ask for (`TargetView.k + TargetView.n` at `nestedTV`). -/
theorem NestedPinsRun.copyTgtLt {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) (l : Nat) :
    ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k + pinsS.length := by
  classical
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hJcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hfmsLen : fms.length = p.k + pinsS.length := by
    rw [R.h.lenFms, R.hbk, SF.pinsLen]
  rcases Nat.lt_or_ge l (mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j)) with hlt | hge
  · rw [mutTgts_getD hGlt hlt]
    have := (R.h.ksJ _ _ hcA).2.2 l
    rw [hfmsLen] at this
    exact this
  · have hz : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = 0 := by
      have hlen : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).length
          = mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
        simp [mutTgts, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hGlt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hz]
    have hkpos : 0 < pinsS.length := by
      have := S.seg
      have := S.kpos
      omega
    omega

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


/-! ## The recursive field at one of the CONTAINER'S OWN pins — step
one (task #315 L-B, DESIGN "the telescope the positivity `whnf`
MAKES" (d))

`CopyCtorShape.pinF` claims that a container field recursive at one of
the CONTAINER's own pins becomes, in the copy, a field recursive at the
BLOCK pin corresponding to it.  The route has four steps and this is
the first: what the MINTED domain looks like, before the elimination
has been asked whether it fires.

It is `copyRecFDom`'s twin, and it is shorter, because at a nested
field the container's own record says the head outright:
`BlockOpened.nestF` gives the head `(pinAt q).J` WITH its level
arguments and the argument count `nPJ + nIdx`, where the member case
had to reconstruct the head from K.14's uniformity.  B1 carries both
from the OPENED domain to the CLOSED one (`blockCtorFieldHead`,
`blockCtorFieldArgs` — the opening substitutes `fvar`s for `bvar`s and
can neither make nor unmake a `const` head), and the two substitutions
the mint applies distribute over the spine (`ilp_mkAppN`,
`instSeq_mkAppN_const`), leaving the head's NAME fixed and its level
arguments substituted.

What this step does NOT say is that the elimination FIRES there.  That
is step two, it needs the mention (`ContainerModeled.nestMention`)
moved across the instantiation by the group's uniformity, and it is the
step this lane flagged as the route's risk. -/

omit R SF in
/-- **THE COPY'S NESTED FIELD, MINTED** (task #315 L-B): at a container
field `l` of member `i'` constructor `j` that is finitary recursive at
one of the CONTAINER's own pins, the closed field domain is that pin's
container applied to `nPJ + nIdx` arguments, and the minted domain —
the closed one level-substituted and instantiated at any components —
is the same application with the head's level arguments substituted and
the spine mapped. -/
theorem copyPinFDom
    {i' : Nat} (hi' : i' < kJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {cc : ContainerCtor} (hty : cAJ.1.type = cc.type) (hnf : cAJ.2 = cc.nFields)
    {pcs fcs : List (Expr × ConLeche.BinderMeta)} {residJ : Expr}
    (hstripJ : cc.type.stripPis (dJ.nP + cc.nFields) = some (pcs ++ fcs, residJ))
    (hpl : pcs.length = dJ.nP) (hfl : fcs.length = cc.nFields)
    {l : Nat} (hlF : l < cc.nFields)
    (hnest : ¬ dJ.tgts i' j l < dJ.k)
    (hrec : (dJ.ksF i' j).getD l .ordinary = .recursive) :
    dJ.tgts i' j l - dJ.k < dJ.nPins ∧
    (fcs.getD l default).1.getAppFn
        = Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            (dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls ∧
    (fcs.getD l default).1.getAppArgs.length
        = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).nPJ
          + (dJ.pinAt (dJ.tgts i' j l - dJ.k)).nIdx ∧
    ∀ (lps : List Name) (lvls : List Level) (Ds : List Expr) (c : Nat),
      Expr.instSeq Ds c (Expr.instantiateLevelParams lps lvls (fcs.getD l default).1)
        = Expr.mkAppN
            (.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
              ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map (Level.subst lps lvls)))
            (((fcs.getD l default).1.getAppArgs.map
                (Expr.instantiateLevelParams lps lvls)).map (Expr.instSeq Ds c)) := by
  classical
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCDJ⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hlA : l < cAJ.2 := by rw [hnf]; exact hlF
  have hkindLen : l < (dJ.ksF i' j).length := by rw [hCDJ.ksLen]; exact hlA
  -- the target is a PIN of the container's own block
  have hqlt : dJ.tgts i' j l - dJ.k < dJ.nPins := by
    have h := hI.tgtsLt i' j l hI.memberLt hjlt hkindLen
    omega
  have hnestOf : dJ.nestOf i' j l = some (dJ.tgts i' j l - dJ.k) := dJ.nestOf_some hnest
  -- the OPENED domain: the pin's container, at its own level arguments
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCDJ.xLen]; exact hlA)⟩
  obtain ⟨hfn, hlen, -, -, -⟩ := hCDJ.opened.nestF l x _ hx hnestOf hrec
  -- B1: the CLOSED domain has the same head and the same arity
  have hstrip' : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (pcs ++ fcs, residJ) := by
    rw [hty, hnf]; exact hstripJ
  obtain ⟨bd, hbd⟩ : ∃ bd, fcs[l]? = some bd :=
    ⟨_, List.getElem?_eq_getElem (by rw [hfl]; exact hlF)⟩
  have hbdD : fcs.getD l default = bd := by
    rw [List.getD_eq_getElem?_getD, hbd]; rfl
  have hheadC := blockCtorFieldHead hCDJ hstrip' hpl hx hbd hfn
  have hargsC := blockCtorFieldArgs hCDJ hstrip' hpl hx hbd
  rw [hbdD]
  refine ⟨hqlt, hheadC, ?_, ?_⟩
  · rw [← hargsC]; exact hlen
  · -- the mint's two substitutions, over the spine
    intro lps lvls Ds c
    have hsplit : bd.1 = Expr.mkAppN (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
        (dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls) bd.1.getAppArgs := by
      rw [← hheadC]; exact (Expr.mkAppN_getApp bd.1).symm
    rw [hsplit, ConLeche.ilp_mkAppN, show Expr.instantiateLevelParams lps lvls
        (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
          (dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls)
        = Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map (Level.subst lps lvls)) from rfl,
      ConLeche.instSeq_mkAppN_const]
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append]

omit [SetTheory V] R SF S in
/-- **`mutualOpenedOk`'s `.recursive` clause, read** (task #315 L-B):
the kernel re-checks the classification on the ANNOTATED constructor
opened at variables, and at a recursive field that re-check says the
domain is headed by its TARGET member's constant.  It is the reader
the pin route's fire needs, and it means no inversion of
`mutualCtorKinds` itself is required. -/
private theorem mutualOpenedOk_recHead {env₀ : Env} {members : List (Name × Nat × Nat)}
    {lps : List Name} {nP nF : Nat} {cty : Expr} {ks : List (RecFieldKind × Nat)}
    (h : ConLeche.mutualOpenedOk env₀ members lps nP cty nF ks = true)
    {fvsP xFvs : List Expr} {crest xrest : Expr}
    (hop1 : ConLeche.openPisAtFvars nP cty 0 = some (fvsP, crest))
    (hop2 : ConLeche.openPisAtFvars nF crest nP = some (xFvs, xrest))
    {l : Nat} {x' : Expr} (hx' : xFvs[l]? = some x')
    (hk : kindAt ks l = RecFieldKind.recursive) :
    x'.fvarTypeD.getAppFn
      = Expr.const (mutualNameOf members (tgtAt ks l)) (lps.map Level.param) := by
  classical
  rw [ConLeche.mutualOpenedOk] at h
  simp only at h
  rw [hop1] at h
  simp only at h
  rw [hop2] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hfields⟩ := h
  have hlt : l < nF := by
    have h1 := ConLeche.openPisAtFvars_len _ hop2
    have h2 := (List.getElem?_eq_some_iff.mp hx').1
    omega
  have hcell := (List.all_eq_true.mp hfields) l (by simpa using List.mem_range.mpr hlt)
  rw [hx'] at hcell
  rcases hks : ks.getD l (.ordinary, 0) with ⟨r, t⟩
  rw [hks] at hcell
  have hr : r = RecFieldKind.recursive := by
    simp only [kindAt, hks] at hk
    exact hk
  subst hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hcell
  simp only [tgtAt, hks]
  exact hcell.1.1.1.1.1

omit [SetTheory V] R SF S in
/-- A `Nodup` list's positions are determined by their entries. -/
private theorem nodup_getElem?_inj {α : Type} : ∀ {L : List α}, L.Nodup →
    ∀ {i₁ i₂ : Nat} {a : α}, L[i₁]? = some a → L[i₂]? = some a → i₁ = i₂
  | [], _, i₁, _, _, hi, _ => by simp at hi
  | c :: cs, h, i₁, i₂, a, hi, hj => by
    obtain ⟨hnm, hnd⟩ := List.nodup_cons.mp h
    cases i₁ with
    | zero =>
      cases i₂ with
      | zero => rfl
      | succ i₂ =>
        exfalso
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        rw [List.getElem?_cons_succ] at hj
        subst hi
        exact hnm (List.mem_of_getElem? hj)
    | succ i₁ =>
      cases i₂ with
      | zero =>
        exfalso
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        rw [List.getElem?_cons_succ] at hi
        subst hj
        exact hnm (List.mem_of_getElem? hi)
      | succ i₂ =>
        rw [List.getElem?_cons_succ] at hi hj
        exact congrArg (· + 1) (nodup_getElem?_inj hnd hi hj)


/-! ## The result's index readings (task #315 L-B, DESIGN §U.38 (e))

`CopyCtorShape.es` is the one arm with no kinds and no targets in it:
the copy's constructor RESIDUAL is the container's, instantiated at the
pin's components, and the elimination's rewrite never descends into its
index arguments (`copyResid`).  So the two sides read the SAME
expressions, and all that stands between them is the crossing every
copy-reading step makes:

* the copy's stored type is the elimination's output `cbody'` closed
  over the block's parameter binders and then NORMALISED
  (`normCtorValM`), and what the block model reads is that stored type
  opened again in two stages.  The normalisation leaves the residual
  alone (`normCtorValM_openResid`), and the closing is undone by
  `instSeq_abstractRange_fvs` over the rewrite's frame
  (`replaceAllNested_frame`), so the opened residual is `cbody'`'s own —
  up to `Expr.ErasedEq`, which is all an interpretation reads;
* the MINTED constructor is opened at the same binders
  (`mintResidRead`), and its residual carries the very same index
  arguments;
* the two readings sit at two models, which `crossUp` identifies. -/

/-- **`CopyCtorShape.es`** (task #315 L-B): the copy's constructor's
result index readings are the container's, instantiated at the pin's
components under the fields. -/
theorem NestedPinsRun.copyEs {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) (ψ : Name → Nat) :
    (mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []
      = (dJ.esF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).map
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) cAJ.2) := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    -, -, -, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ, hopb, hplenB,
    hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    hqnMem, hqnPin, ⟨cI, fcs', hinstCI, hstripCI, -⟩, hcb, hcA, hnF, hbc⟩ :=
    R.copyResid SF S hPD hi' hj
  -- the copy's constructor data at the block
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  obtain ⟨crest, hopP, hopX⟩ := hCD.opens
  rw [mutEss0_getD hGlt]
  -- stage 1: the parameters are the block's openers, and give `cbody'` back
  obtain ⟨fvsA, -, -, hlawA⟩ := ConLeche.openPisAtFvars_mkPisB b.nP pbs₀ hpbs₀len 0
  have hfvsA : fvsA = params := by
    have hlaw := hlawA o'
    rw [← ConLeche.stripPis_mkPisB _ hstripF] at hlaw
    exact (Prod.mk.inj (Option.some.inj (hlaw.symm.trans hopb))).1
  have hop1 : ConLeche.openPisAtFvars b.nP (closeTelescope pbs₀ 0 cbody') 0
      = some (params, cbody') := by
    rw [ConLeche.closeTelescope_eq_mkPisB pbs₀ 0 cbody' hpbs₀f, hpbs₀len, hlawA, hfvsA,
      ConLeche.instSeq_abstractRange_fvs b.nP params cbody' hcbb hplenB hidxP hcbl]
  -- stage 2: the fields, on both sides
  obtain ⟨xfvs, -, -, hlawX⟩ := ConLeche.openPisAtFvars_mkPisB cc.nFields Fs' hlenF b.nP
  have hop2 : ConLeche.openPisAtFvars cc.nFields cbody' b.nP
      = some (xfvs, Expr.instSeq xfvs (cc.nFields - 1)
        (Expr.mkAppN (Expr.mkAppN (.const qn.aux (p.lps.map Level.param)) params)
          (esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
            (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)))) := by
    rw [ConLeche.stripPis_mkPisB _ hcb]
    exact hlawX _
  obtain ⟨xfvs', -, -, hlawX'⟩ :=
    ConLeche.openPisAtFvars_mkPisB cc.nFields fcs'
      (Expr.stripPis_length _ hstripCI) b.nP
  have hopM : ConLeche.openPisAtFvars cc.nFields cI b.nP
      = some (xfvs', Expr.instSeq xfvs' (cc.nFields - 1)
        (Expr.mkAppN (.const (dJ.memberName i') usJ)
          ((srcAtE st p (q₀ + i')).2.2 ++
            esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)))) := by
    rw [ConLeche.stripPis_mkPisB _ hstripCI]
    exact hlawX' _
  -- the normalisation leaves the residual alone
  obtain ⟨-, sorts, -, hCtor⟩ := R.h.runC _ _ hcA
  obtain ⟨hnorm, -, hbndC⟩ := ConLeche.checkMutualCtor_true_norm hCtor
  have hcvC : (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).cv
      = ⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩ := by
    rw [List.getD_eq_getElem?_getD, hbc]
    rfl
  rw [hcvC] at hnorm hbndC
  rw [hnF] at hnorm hopX
  have herX := ConLeche.normCtorValM_openResid mp₁.base2.wf hnorm hbndC hop1 hop2 hopP hopX
  -- the pin's components: scoped at the block's parameters, and read
  have hqst : q₀ + i' < st.pins.length := by rw [← SF.pinsLen]; have := S.seg; omega
  have hq : q₀ + i' < pinsS.length := by have := S.seg; omega
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hDsE : (pinsS.getD (q₀ + i') default).DsE = (srcAtE st p (q₀ + i')).2.2 := by
    have hA := congrArg Expr.getAppArgs hpin
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at hA
    exact hA
  have hspine := SF.pinDs _ hq ψ
  rw [hDsE] at hspine
  obtain ⟨-, hcl₀, hbt₀, hFD₀⟩ := R.former0
  obtain ⟨-, fvsS, oS, hopS, hsc⟩ := R.scoped
  obtain ⟨hbnd, hleaf⟩ := hsc _ (List.mem_of_getElem? PD.pin)
  have hws := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hopS hleaf ψ
  rw [PD.pinEq] at hbnd hws
  obtain ⟨-, hwsD⟩ := ConLeche.WScoped_of_mkAppN hws
  obtain ⟨-, hbndD⟩ := ConLeche.looseBVarsBounded_of_mkAppN hbnd
  have hDsSc : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2,
      Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true :=
    fun a ha => ⟨hwsD a ha, hbndD a ha⟩
  -- the minted constructor's residual, read at the whole block's model
  have hmr := mintResidRead S hi' hj hksJ (by rw [hty]; exact hccf) (by rw [hty]; exact hccb)
    hDsSc ψ hspine (by rw [hty]; exact hinstCI) (by rw [hnf]; exact hopM)
  have hmrU := R.crossUp ψ (b.nP + cAJ.2) _ hmr
  rw [hnf, ConLeche.instSeq_mkAppN_const, List.map_append] at hmrU
  obtain ⟨fa, vs, -, hspM, heqA⟩ := denoteMeta_mkAppN_inv hmrU
  obtain ⟨vs₁, vs₂, rfl, hspP, hspE⟩ := DenoteMetaSpine.append_inv hspM
  -- the two index spines are the same expressions, under two openings
  have hxflen : xfvs.length = xfvs'.length := by
    rw [openPisAtFvars_length _ hop2, openPisAtFvars_length _ hopM]
  have hxf : ∀ (k : Nat) (a₁ a₂ : Expr), xfvs[k]? = some a₁ → xfvs'[k]? = some a₂ →
      Expr.ErasedEq a₁ a₂ := by
    intro k a₁ a₂ h1 h2
    obtain ⟨ty₁, rfl⟩ := openPisAtFvars_index _ _ _ hop2 k a₁ h1
    obtain ⟨ty₂, rfl⟩ := openPisAtFvars_index _ _ _ hopM k a₂ h2
    rfl
  have hmapGetD : ∀ (L : List Expr) (g : Expr → Expr) (l : Nat), l < L.length →
      (L.map g).getD l default = g (L.getD l default) := by
    intro L g l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    rfl
  -- the copy's read spine, transported to the minted opening
  obtain ⟨-, hlenArgs, hargsEq⟩ := ConLeche.ErasedEq.getApp herX
  have hargsC : (Expr.instSeq xfvs (cc.nFields - 1)
        (Expr.mkAppN (Expr.mkAppN (.const qn.aux (p.lps.map Level.param)) params)
          (esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
            (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)))).getAppArgs
      = params.map (Expr.instSeq xfvs (cc.nFields - 1))
        ++ (esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)).map
            (Expr.instSeq xfvs (cc.nFields - 1)) := by
    rw [Expr.instSeq_mkAppN, ConLeche.instSeq_mkAppN_const, Expr.getAppArgs_mkAppN,
      Expr.getAppArgs_mkAppN]
    rfl
  rw [hargsC] at hlenArgs hargsEq
  have hlenPm : (params.map (Expr.instSeq xfvs (cc.nFields - 1))).length = b.nP := by
    rw [List.length_map]; exact hplenB
  have hidxRead := hCD.idxRead ψ
  rw [hCD.idxEq, hnF] at hidxRead
  have hlenDrop : ((xrestF (b.ownOffset (p.k + q₀ + i') + j)).getAppArgs.drop b.nP).length
      = ((esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
            (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)).map
          (Expr.instSeq xfvs' (cc.nFields - 1))).length := by
    rw [List.length_drop, hlenArgs, List.length_append, hlenPm]
    simp
  have hptDrop : ∀ l, l < ((xrestF (b.ownOffset (p.k + q₀ + i') + j)).getAppArgs.drop b.nP).length →
      Expr.ErasedEq
        (((xrestF (b.ownOffset (p.k + q₀ + i') + j)).getAppArgs.drop b.nP).getD l default)
        (((esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + cc.nFields)
            (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)).map
          (Expr.instSeq xfvs' (cc.nFields - 1))).getD l default) := by
    intro l hl
    have hlES : l < (esJ.map fun e => Expr.instSeq (srcAtE st p (q₀ + i')).2.2
        (dJ.nP - 1 + cc.nFields)
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls e)).length := by
      rw [List.length_drop, hlenArgs, List.length_append, hlenPm] at hl
      simp only [List.length_map] at hl ⊢
      omega
    have hlt : b.nP + l < (xrestF (b.ownOffset (p.k + q₀ + i') + j)).getAppArgs.length := by
      rw [List.length_drop] at hl; omega
    rw [getD_dropD]
    refine Expr.ErasedEq.trans (hargsEq (b.nP + l) hlt) ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlenPm]; omega), hlenPm,
      Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD, hmapGetD _ _ l hlES,
      hmapGetD _ _ l hlES]
    exact Expr.instSeq_erasedEq_args xfvs xfvs' (cc.nFields - 1) (Expr.ErasedEq.rfl _)
      hxf hxflen
  have hsp1 := DenoteMetaSpine.erasedEq hidxRead hlenDrop hptDrop
  -- the two spines read the same list
  have hlenPB : ((paramBvars dJ.nP cc.nFields).map
      (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) cc.nFields)).length = vs₁.length := by
    rw [List.length_map, paramBvars, List.length_map, List.length_range, ← hspP.length,
      List.length_map, hDsnP]
  have hlenEs : (dJ.esF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).length = esJ.length := by
    obtain ⟨cvTJ, capsJ, cvRJ, mIJ, rPJ, rulesJ, -, hIJ, -⟩ := S.stored i' hi'
    obtain ⟨-, -, hCDJ⟩ := hIJ.ctors i' j cAJ hIJ.memberLt hj
    rw [hCDJ.lenE, hesJ]
  obtain ⟨-, happ⟩ := AnnotTerm.mkAppN_inj heqA (by rw [List.length_append, List.length_append,
    hlenPB, ← hspE.length, List.length_map, List.length_map, List.length_map, hlenEs])
  obtain ⟨-, rfl⟩ := List.append_inj happ hlenPB
  rw [hnf]
  exact DenoteMetaSpine.unique hsp1 hspE

/-! ## The recursive field at a member target (task #315 L-B)

`CopyCtorShape.recF` claims that a container field recursive at one of
the container's OWN members becomes, in the copy, a field recursive at
the group's copy of that member.  The syntactic half of that claim is
the elimination's occurrence chain, and this is it: the container's
field domain, level-substituted and instantiated at the pin's
components, IS the targeted member applied to the components and to the
field's index arguments — a nested occurrence at the group's own pin,
which `replaceAllNested_occurrence` rewrites to that pin's MIMIC.

Three facts beyond `copyFields`' package carry it:

* the closed domain's head and spine (B1, `blockCtorFieldHead` and
  `blockCtorFieldArgs` over `NestedOpenSpine`'s inversions);
* K.14's UNIFORMITY (`nestedContainersOk_memberSpine`): a stored
  container constructor's field headed by a member of its own block
  carries the block's parameters at the field's own depth, so the
  instantiation puts the pin's components exactly there — the
  `containerFieldOk` trichotomy does NOT give this (its nested arm
  accepts any stored inductive head, a member included), the uniform
  occurrence walk does;
* K.29 through `PinData.grp`: the group's pin `q₀ + m` records the
  SAME level arguments and components as the pin `q₀ + i'` being
  copied, so its pin expression is exactly the occurrence's, and
  `pinsDistinct` identifies the two. -/

omit [SetTheory V] R SF S in
/-- `Name.nodup`'s `Bool` is the list's `Nodup`. -/
private theorem nodup_of_nameNodup : ∀ {l : List Name}, ConLeche.Name.nodup l = true → l.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    exact List.nodup_cons.mpr ⟨by simpa using h.1, nodup_of_nameNodup h.2⟩

/-- **THE COPY'S RECURSIVE FIELD, REWRITTEN** (task #315 L-B): at a
container field `l` of member `i'` constructor `j` that is FINITARY
RECURSIVE at one of the container's own members, the elimination's
rewrite turns the instantiated domain into the MIMIC of the group's
pin at that member, applied to the block's parameter openers and to
the field's own index arguments, level-substituted and instantiated at
the pin's components.  Stated at `copyFields`' frame: the caller hands
the one `replaceAllNested` run at field `l` and the container's
telescope, both of which `copyResid` returns. -/
theorem NestedPinsRun.copyRecFDom {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {ci : ContainerInfo} {J : ContainerMember} {cc : ContainerCtor}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (hJmem : J ∈ ci.members) (hJcc : J.ctors[j]? = some cc)
    (hJname : J.name = (pinsS.getD (q₀ + i') default).J)
    (hty : cAJ.1.type = cc.type) (hnf : cAJ.2 = cc.nFields)
    {pcs fcs : List (Expr × ConLeche.BinderMeta)} {residJ : Expr}
    (hstripJ : cc.type.stripPis (dJ.nP + cc.nFields) = some (pcs ++ fcs, residJ))
    (hpl : pcs.length = dJ.nP) (hfl : fcs.length = cc.nFields)
    (hDsnP : (srcAtE st p (q₀ + i')).2.2.length = dJ.nP)
    (hDsB : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2, a.looseBVarsBounded 0 = true)
    {params : List Expr} {pbs₀ : List (Expr × ConLeche.BinderMeta)}
    {l : Nat} (hlF : l < cc.nFields)
    (hmem : dJ.tgts i' j l < dJ.k)
    (hrec : (dJ.ksF i' j).getD l .ordinary = .recursive)
    {Fl : Expr} {st₁ st₂ : ElimState}
    (hrun : ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st₁
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
            (fcs.getD l default).1))
      = .ok (Fl, st₂))
    (hpre : st₂.pins <+: st.pins)
    (hmint : ((srcAtE st p (q₀ + i')).2.2.any fun a =>
      st₁.newNames.any fun T => a.mentionsConst T) = true) :
    Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
          (fcs.getD l default).1)
      = Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
          (pinsS.getD (q₀ + i') default).lvls)
        ((srcAtE st p (q₀ + i')).2.2 ++
          (((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))) ∧
    (fcs.getD l default).1.getAppArgs.length = dJ.nP + dJ.nIdxAt (dJ.tgts i' j l) ∧
    Fl = Expr.mkAppN (Expr.mkAppN
        (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param)) params)
      ((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))) := by
  classical
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hpinMem : pinAtE st (q₀ + i') ∈ st.pins := List.mem_of_getElem? PD.pin
  obtain ⟨hJc, hpinEq⟩ := SF.pinRec _ _ PD.pin
  have hciC : ConLeche.containerInfo? env (pinAtE st (q₀ + i')).container = some ci := by
    rw [← hJc]; exact hciP
  have hlv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have hfn := congrArg Expr.getAppFn (hpinEq.symm.trans PD.pinEq)
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at hfn
    exact (ConLeche.Expr.const.inj hfn).2
  obtain ⟨ciP, hciPown, -, -, -, hnamesP, J', hJ'find, hJ'n, cCopy, hmk, -, -⟩ := PD.own
  have hciEq : ciP = ci := Option.some.inj (hciPown.symm.trans hciC)
  have hJ'mem : J' ∈ ci.members := by
    rw [← hciEq]; exact List.mem_of_find?_eq_some hJ'find
  rw [hciEq] at hnamesP
  obtain rfl : J = J' :=
    ConLeche.containerInfo?_member_det hciP hciP rfl hJmem hJ'mem (by rw [hJname, hJc, hJ'n])
  -- the container's constructor data at member `i'`, constructor `j`
  obtain ⟨cvT, capsT, cvR, mI, rP, rules, hfindT, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hnest : dJ.nestOf i' j l = none := dJ.nestOf_none hmem
  -- the member's level parameters ARE the stored constant's
  obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, hfT₀, -, -, -, hallM⟩ :=
    ConLeche.containerInfo?_inv hciP
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, -, -, hlpsJ, -, hlpsEq, -, -⟩ := hallM _ hJmem
  have hlpsJEq : J.lps = cvT.levelParams := by
    obtain ⟨hFc, -, -, -⟩ := R.cross
    have h₁ := hFc _ (.indInfo cvT₀ caps₀) (fun _ _ _ _ h => nomatch h) hfT₀
    obtain rfl : cvT₀ = cvT :=
      (ConstantInfo.indInfo.inj (Option.some.inj (h₁.symm.trans hfindT))).1
    rw [hlpsJ, hlpsEq]
  -- the field's opener, and the OPENED domain's head and spine
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnf]; exact hlF)⟩
  obtain ⟨hhead, -, hlenO, -, -, -⟩ := hCD.opened.recF l x hx hnest hrec
  have hfcsl : fcs[l]? = some (fcs.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hfl]; exact hlF)]; rfl
  have hstripA : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (pcs ++ fcs, residJ) := by
    rw [hty, hnf]; exact hstripJ
  have hcHead : (fcs.getD l default).1.getAppFn
      = Expr.const (dJ.memberName (dJ.tgts i' j l)) (cvT.levelParams.map Level.param) :=
    blockCtorFieldHead hCD hstripA hpl hx hfcsl hhead
  have hcLen : (fcs.getD l default).1.getAppArgs.length
      = dJ.nP + dJ.nIdxAt (dJ.tgts i' j l) := by
    rw [← blockCtorFieldArgs hCD hstripA hpl hx hfcsl]; exact hlenO
  -- the target IS a member of the container's group
  have hmLt : dJ.tgts i' j l < ci.members.length := by rw [← CMci.k]; exact hmem
  obtain ⟨Mt, hMt⟩ : ∃ Mt, ci.members[dJ.tgts i' j l]? = some Mt :=
    ⟨_, List.getElem?_eq_getElem hmLt⟩
  have hMtName : dJ.memberName (dJ.tgts i' j l) = Mt.name := (CMci.member _ Mt hMt).1
  have hMtMem : Mt ∈ ci.members := List.mem_of_getElem? hMt
  -- K.14's UNIFORMITY: the field's parameter arguments are the block's own
  have hbdIdx : (pcs ++ fcs)[ci.nP + l]? = some (fcs.getD l default) := by
    have hidx : ci.nP + l - pcs.length = l := by rw [hpl, hnPci]; omega
    rw [List.getElem?_append_right (by rw [hpl, hnPci]; omega), hidx]
    exact hfcsl
  have hstripCi : cc.type.stripPis (ci.nP + cc.nFields) = some (pcs ++ fcs, residJ) := by
    rw [hnPci]; exact hstripJ
  obtain ⟨-, hTake⟩ := ConLeche.nestedContainersOk_memberSpine R.hcont hpinMem hciC hJmem hJcc
    hstripCi hbdIdx hcHead (by rw [hMtName]; exact List.mem_map_of_mem hMtMem)
    (by rw [hcLen, hnPci]; omega)
  rw [hnPci] at hTake
  obtain ⟨hNodupJ, -⟩ := ConLeche.nestedContainersOk_uniform R.hcont hpinMem hciC hJmem
  -- the components: non-empty, and as many as the member's level parameters
  have hDsNe : 0 < (srcAtE st p (q₀ + i')).2.2.length := by
    rcases hDsE : (srcAtE st p (q₀ + i')).2.2 with _ | ⟨d, ds⟩
    · rw [hDsE] at hmint; simp at hmint
    · simp
  have hLvlLen : J.lps.length = (pinsS.getD (q₀ + i') default).lvls.length := by
    obtain ⟨hlen, -, -, -, -, -⟩ := ConLeche.mkCopy_inv hmk
    rw [hlv]; exact hlen.symm
  -- the instantiated domain, as a spine at the components
  have hshape : Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
      (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
        (fcs.getD l default).1)
      = Expr.mkAppN (.const Mt.name (pinsS.getD (q₀ + i') default).lvls)
          ((srcAtE st p (q₀ + i')).2.2 ++
            (((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
              (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))) := by
    have hsplit : (fcs.getD l default).1
        = Expr.mkAppN (.const Mt.name (J.lps.map Level.param))
            (ConLeche.structPsAt l dJ.nP ++ (fcs.getD l default).1.getAppArgs.drop dJ.nP) := by
      have hargs : ConLeche.structPsAt l dJ.nP ++ (fcs.getD l default).1.getAppArgs.drop dJ.nP
          = (fcs.getD l default).1.getAppArgs := by rw [← hTake, List.take_append_drop]
      rw [hargs, hlpsJEq, ← hMtName, ← hcHead]
      exact (Expr.mkAppN_getApp _).symm
    rw [hsplit, ConLeche.ilp_mkAppN,
      ConLeche.ilp_const_params J.lps _ Mt.name (nodup_of_nameNodup hNodupJ) hLvlLen,
      List.map_append, ConLeche.ilp_structPsAt, ConLeche.instSeq_mkAppN_const, List.map_append,
      List.map_map]
    congr 2
    · rw [← hDsnP,
        show (srcAtE st p (q₀ + i')).2.2.length - 1 + l
          = l + (srcAtE st p (q₀ + i')).2.2.length - 1 from by omega]
      exact ConLeche.instSeq_structPsAt _ l hDsB
    · simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append]
      rw [List.drop_left' (ConLeche.structPsAt_length l dJ.nP), List.map_map]
  rw [hshape] at hrun
  -- the target member's own container record
  obtain ⟨hndPins, hgrpAll⟩ := ConLeche.nestedContainersOk_group R.hcont
  obtain ⟨ci₁, hci₁, hmem₁⟩ := hgrpAll _ hpinMem
  have hci₁Eq : ci₁ = ci := Option.some.inj (hci₁.symm.trans hciC)
  obtain ⟨ciM, hciM, hciMnP, -⟩ := hmem₁ Mt (by rw [hci₁Eq]; exact hMtMem)
  obtain ⟨cvM, capsM, -, -, -, -, hfindM, -, -, -, -⟩ := ConLeche.containerInfo?_inv hciM
  have hnPM : ciM.nP = dJ.nP := by rw [hciMnP, hci₁Eq, hnPci]
  have htakeD : ((srcAtE st p (q₀ + i')).2.2 ++
      (((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).take ciM.nP
      = (srcAtE st p (q₀ + i')).2.2 := List.take_left' (by rw [hnPM, hDsnP])
  have hdropD : ((srcAtE st p (q₀ + i')).2.2 ++
      (((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).drop ciM.nP
      = (((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
          (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)) :=
    List.drop_left' (by rw [hnPM, hDsnP])
  obtain ⟨qn, hqnMem, hqnPin, hqnEq⟩ :=
    ConLeche.replaceAllNested_occurrence rfl hfindM hciM
      (by rw [List.length_append, hnPM, hDsnP]; omega)
      (by rw [htakeD]; exact hmint) (by rw [htakeD]; exact hDsB) hrun
  rw [htakeD] at hqnPin
  rw [hdropD] at hqnEq
  -- the group's pin at the target member carries the same source
  have hmkJ : dJ.tgts i' j l < kJ := by rw [← S.kEq]; exact hmem
  have hplen : q₀ + dJ.tgts i' j l < st.pins.length := by
    obtain ⟨-, -, h3⟩ := PD.seg
    rw [hgb, hgs] at h3; omega
  have PDm := hPD _ hplen
  obtain ⟨hcontm, -, -, hsrcm, hmemm⟩ := PD.grp (dJ.tgts i' j l) (by rw [hgs]; exact hmkJ)
  rw [hgb] at hcontm hsrcm
  have hsrcPair := Option.some.inj (PDm.src.symm.trans hsrcm)
  have hsrc1 : (srcAtE st p (q₀ + dJ.tgts i' j l)).2.1 = (srcAtE st p (q₀ + i')).2.1 :=
    (Prod.mk.inj (Prod.mk.inj hsrcPair).2).1
  have hsrc2 : (srcAtE st p (q₀ + dJ.tgts i' j l)).2.2 = (srcAtE st p (q₀ + i')).2.2 :=
    (Prod.mk.inj (Prod.mk.inj hsrcPair).2).2
  have hmemName : (memberOf env st (q₀ + i') (dJ.tgts i' j l)).name = Mt.name := by
    have h1 : (ci.members.map (·.name))[dJ.tgts i' j l]? = some Mt.name := by
      rw [List.getElem?_map, hMt]; rfl
    have h2 : ((baseInfo env st (q₀ + i')).members.map (·.name))[dJ.tgts i' j l]?
        = some (memberOf env st (q₀ + i') (dJ.tgts i' j l)).name := by
      rw [List.getElem?_map, hmemm]; rfl
    rw [hnamesP] at h1
    exact Option.some.inj (h2.symm.trans h1)
  have hpinm : (pinAtE st (q₀ + dJ.tgts i' j l)).pin
      = Expr.mkAppN (.const Mt.name (pinsS.getD (q₀ + i') default).lvls)
          (srcAtE st p (q₀ + i')).2.2 := by
    rw [PDm.pinEq, hcontm, hsrc1, hsrc2, hmemName, hlv]
  obtain rfl : qn = pinAtE st (q₀ + dJ.tgts i' j l) := by
    have h1 := ConLeche.find?_pin_of_nodup hndPins (hpre.subset hqnMem) hqnPin
    have h2 := ConLeche.find?_pin_of_nodup hndPins (List.mem_of_getElem? PDm.pin) hpinm
    exact Option.some.inj (h1.symm.trans h2)
  exact ⟨by rw [hMtName]; exact hshape, hcLen, hqnEq⟩

/-! ## The auxiliary block's classification at a member-headed field
(task #315 L-B)

`copyRecFDom` says what the elimination's rewrite leaves at a
container-recursive field: the mimic of the group's pin, which IS a
member of the AUXILIARY block.  `CopyCtorShape.recF`'s first two
conjuncts ask what the auxiliary block's install MADE of that —
`blkRss` and `mutTgts` read the kinds table `classifyMutualKinds`
computed on the STORED (positivity-normalised) constructors.

Two steps stand between: the normalisation, crossed at a DOMAIN by
`normCtorValM_domHead` (`Verify/Inductives/NestedCopyNorm.lean` — a
stuck inductive-headed domain survives it), and the classification,
read off by `mutualCtorKinds_memberHead` below. -/

omit [SetTheory V] R SF S in
/-- An entry's kind witnesses the table's `any`. -/
private theorem kinds_any_of_getD {ks : List (RecFieldKind × Nat)} {l : Nat}
    (hl : l < ks.length) {k : RecFieldKind}
    (h : (ks.getD l (.ordinary, 0)).1 = k) : ks.any (·.1 == k) = true := by
  refine List.any_eq_true.mpr ⟨ks.getD l (.ordinary, 0), ?_, by rw [h]; simp⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  exact List.getElem_mem _

omit [SetTheory V] R SF S in
/-- **`mutualPositivity` at a non-`Π` term**, unfolded once: the walk's
second arm, which every constructor but `.forallE` takes. -/
private theorem mutualPositivity_notPi (members : List (Name × Nat × Nat)) (lps : List Name)
    (nP o k : Nat) : ∀ {e : Expr}, (∀ d bo bm, e ≠ Expr.forallE d bo bm) →
      ConLeche.mutualPositivity members lps nP o e k
        = (if !ConLeche.mentionsMember (members.map (·.1)) e then (RecFieldKind.ordinary, 0) else
            match e.getAppFn with
            | .const T' us =>
              match members.find? (·.1 == T') with
              | some (_, m', nIdx') =>
                if us == lps.map .param && e.getAppArgs.length == nP + nIdx' &&
                    e.getAppArgs.take nP == ConLeche.structPsAt (o + k) nP &&
                    (e.getAppArgs.drop nP).all
                      (fun a => !ConLeche.mentionsMember (members.map (·.1)) a) then
                  ((if k == 0 then RecFieldKind.recursive else .reflexive), m')
                else (.negative, 0)
              | none => (.unsupported, 0)
            | _ => (.unsupported, 0)) := by
  intro e h
  cases e
  case forallE d bo bm => exact absurd rfl (h d bo bm)
  all_goals rfl

omit [SetTheory V] R SF S in
/-- **A field headed by a BLOCK MEMBER is classified `.recursive` at
that member** (task #315 L-B): the closed domain is not a `Π`, so the
positivity walk takes its constant arm, finds the member and answers
`.recursive` at the member's own index — unless one of its four guards
fails, and every failure answers `.negative`, or the later-use test
answers `.unsupported`; the classification's own run rules both out
(`classifyMutualKinds_inv`'s second and third conjuncts), so the
guards need not be proved, only the arm reached. -/
private theorem mutualCtorKinds_memberHead {members : List (Name × Nat × Nat)}
    {lps : List Name} {nP : Nat} {c : ConstantVal × Nat} {ks : List (RecFieldKind × Nat)}
    (h : ConLeche.mutualCtorKinds members lps nP c = some ks)
    (hneg : ks.any (·.1 == .negative) = false)
    (huns : ks.any (·.1 == .unsupported) = false)
    {cbs : List (Expr × ConLeche.BinderMeta)} {cbody : Expr}
    (hstrip : c.1.type.stripPis (nP + c.2) = some (cbs, cbody))
    {l : Nat} (hl : l < c.2)
    {T : Name} {us : List Level} {args : List Expr}
    (hdom : (cbs.getD (nP + l) default).1 = Expr.mkAppN (.const T us) args)
    (hT : T ∈ members.map (·.1))
    {e₀ : Name × Nat × Nat} (hfind : members.find? (·.1 == T) = some e₀) :
    ks.getD l (.ordinary, 0) = (.recursive, e₀.2.1) := by
  classical
  unfold ConLeche.mutualCtorKinds at h
  rw [hstrip] at h
  simp only at h
  have hment : ConLeche.mentionsMember (members.map (·.1)) (cbs.getD (nP + l) default).1 = true := by
    rw [hdom]; exact ConLeche.mentionsMember_mkAppN_const hT us args
  have hpos : ConLeche.mutualPositivity members lps nP l (cbs.getD (nP + l) default).1 0
        = (.recursive, e₀.2.1) ∨
      ConLeche.mutualPositivity members lps nP l (cbs.getD (nP + l) default).1 0
        = (.negative, 0) := by
    rw [hdom, mutualPositivity_notPi members lps nP l 0
      (fun d bo bm hE => ConLeche.mkAppN_const_ne_forallE T us args d bo bm hE),
      if_neg (by rw [← hdom, hment]; simp)]
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn, hfind]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  split at h
  · simp only [Option.some.injEq] at h
    have hlen : ks.length = c.2 := by rw [← h]; simp
    have hget : ks.getD l (.ordinary, 0)
        = (if !ConLeche.mentionsMember (members.map (·.1)) (cbs.getD (nP + l) default).1 then
              (RecFieldKind.ordinary, 0)
            else
              match ConLeche.mutualPositivity members lps nP l (cbs.getD (nP + l) default).1 0 with
              | (.recursive, m') =>
                if ConLeche.structUsedLater c.1.type nP l then (.unsupported, 0)
                else (.recursive, m')
              | (.reflexive, m') =>
                if ConLeche.structUsedLater c.1.type nP l then (.unsupported, 0)
                else (.reflexive, m')
              | kk => kk) := by
      rw [← h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
      rfl
    rw [if_neg (by rw [hment]; simp)] at hget
    rcases hpos with hp | hp
    · rw [hp] at hget
      dsimp only at hget
      by_cases hsu : ConLeche.structUsedLater c.1.type nP l = true
      · rw [if_pos hsu] at hget
        exact absurd (kinds_any_of_getD (by rw [hlen]; exact hl) (by rw [hget])) (by
          rw [huns]; simp)
      · rw [if_neg hsu] at hget
        exact hget
    · rw [hp] at hget
      dsimp only at hget
      exact absurd (kinds_any_of_getD (by rw [hlen]; exact hl) (by rw [hget])) (by
        rw [hneg]; simp)
  · exfalso
    simp only [Option.some.injEq] at h
    have hlen : ks.length = c.2 := by rw [← h]; simp
    have hget : ks.getD l (.ordinary, 0) = (RecFieldKind.negative, 0) := by
      rw [← h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
        List.getElem?_range hl]
      rfl
    exact absurd (kinds_any_of_getD (by rw [hlen]; exact hl) (by rw [hget])) (by
      rw [hneg]; simp)


omit [SetTheory V] R SF S in
/-- **The positivity walk descends a `∀`-telescope**: its Π arm peels
one binder and counts it, and the only other answer it can give on the
way is `.negative` — the guard it applies at each binder is that the
domain mentions no member. -/
private theorem mutualPositivity_piTower (members : List (Name × Nat × Nat)) (lps : List Name)
    (nP o : Nat) :
    ∀ (bs : List (Expr × ConLeche.BinderMeta)) (body : Expr) (k : Nat),
      ConLeche.mutualPositivity members lps nP o (ConLeche.mkPisB bs body) k
          = (.negative, 0) ∨
        ConLeche.mutualPositivity members lps nP o (ConLeche.mkPisB bs body) k
          = ConLeche.mutualPositivity members lps nP o body (k + bs.length)
  | [], body, k => Or.inr (by rw [ConLeche.mkPisB_nil, List.length_nil, Nat.add_zero])
  | bd :: bs, body, k => by
    by_cases hd : ConLeche.mentionsMember (members.map (·.1)) bd.1 = true
    · refine Or.inl ?_
      rw [ConLeche.mkPisB_cons]
      show (if ConLeche.mentionsMember (members.map (·.1)) bd.1 then (RecFieldKind.negative, 0)
          else ConLeche.mutualPositivity members lps nP o (ConLeche.mkPisB bs body) (k + 1))
          = (RecFieldKind.negative, 0)
      rw [if_pos hd]
    · have hstep : ConLeche.mutualPositivity members lps nP o
            (ConLeche.mkPisB (bd :: bs) body) k
          = ConLeche.mutualPositivity members lps nP o (ConLeche.mkPisB bs body) (k + 1) := by
        rw [ConLeche.mkPisB_cons]
        show (if ConLeche.mentionsMember (members.map (·.1)) bd.1 then (RecFieldKind.negative, 0)
            else ConLeche.mutualPositivity members lps nP o (ConLeche.mkPisB bs body) (k + 1)) = _
        rw [if_neg hd]
      rcases mutualPositivity_piTower members lps nP o bs body (k + 1) with h | h
      · exact Or.inl (by rw [hstep, h])
      · refine Or.inr ?_
        rw [hstep, h, List.length_cons]
        congr 1
        omega

omit [SetTheory V] R SF S in
/-- **A `∀`-TOWER OVER A BLOCK MEMBER IS CLASSIFIED `.reflexive` AT
THAT MEMBER** (task #315 L-B): `mutualCtorKinds_memberHead` under the
field's own binders.  The walk peels the tower, lands on the member
application with a NON-ZERO peel count and answers `.reflexive` at the
member's own index — unless a binder domain mentions a member or one of
the four guards fails, and every such failure answers `.negative`, or
the later-use test answers `.unsupported`; the classification's own run
rules both out. -/
private theorem mutualCtorKinds_memberHeadPi {members : List (Name × Nat × Nat)}
    {lps : List Name} {nP : Nat} {c : ConstantVal × Nat} {ks : List (RecFieldKind × Nat)}
    (h : ConLeche.mutualCtorKinds members lps nP c = some ks)
    (hneg : ks.any (·.1 == .negative) = false)
    (huns : ks.any (·.1 == .unsupported) = false)
    {cbs : List (Expr × ConLeche.BinderMeta)} {cbody : Expr}
    (hstrip : c.1.type.stripPis (nP + c.2) = some (cbs, cbody))
    {l : Nat} (hl : l < c.2)
    {tbs : List (Expr × ConLeche.BinderMeta)} {T : Name} {us : List Level} {args : List Expr}
    (hdom : (cbs.getD (nP + l) default).1
      = ConLeche.mkPisB tbs (Expr.mkAppN (.const T us) args))
    (hne : tbs.length ≠ 0)
    (hT : T ∈ members.map (·.1))
    {e₀ : Name × Nat × Nat} (hfind : members.find? (·.1 == T) = some e₀) :
    ks.getD l (.ordinary, 0) = (.reflexive, e₀.2.1) := by
  classical
  unfold ConLeche.mutualCtorKinds at h
  rw [hstrip] at h
  simp only at h
  have hment : ConLeche.mentionsMember (members.map (·.1)) (cbs.getD (nP + l) default).1
      = true := by
    rw [hdom]
    refine List.any_eq_true.mpr ?_
    obtain ⟨T', hT', hT'eq⟩ :=
      List.any_eq_true.mp (ConLeche.mentionsMember_mkAppN_const hT us args)
    exact ⟨T', hT', ConLeche.mentionsConst_mkPisB tbs _ hT'eq⟩
  have hpos : ConLeche.mutualPositivity members lps nP l (cbs.getD (nP + l) default).1 0
        = (.reflexive, e₀.2.1) ∨
      ConLeche.mutualPositivity members lps nP l (cbs.getD (nP + l) default).1 0
        = (.negative, 0) := by
    rw [hdom]
    rcases mutualPositivity_piTower members lps nP l tbs
      (Expr.mkAppN (.const T us) args) 0 with hw | hw
    · exact Or.inr hw
    rw [hw, mutualPositivity_notPi members lps nP l (0 + tbs.length)
        (fun d bo bm hE => ConLeche.mkAppN_const_ne_forallE T us args d bo bm hE),
      if_neg (by
        rw [ConLeche.mentionsMember_mkAppN_const hT us args]; exact fun h => nomatch h)]
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn, hfind]
    split
    · rw [show ((0 + tbs.length) == 0) = false from by
        simp only [beq_eq_false_iff_ne, ne_eq, Nat.zero_add]; exact hne]
      exact Or.inl rfl
    · exact Or.inr rfl
  split at h
  · simp only [Option.some.injEq] at h
    have hlen : ks.length = c.2 := by rw [← h]; simp
    have hget : ks.getD l (.ordinary, 0)
        = (if !ConLeche.mentionsMember (members.map (·.1)) (cbs.getD (nP + l) default).1 then
              (RecFieldKind.ordinary, 0)
            else
              match ConLeche.mutualPositivity members lps nP l (cbs.getD (nP + l) default).1 0 with
              | (.recursive, m') =>
                if ConLeche.structUsedLater c.1.type nP l then (.unsupported, 0)
                else (.recursive, m')
              | (.reflexive, m') =>
                if ConLeche.structUsedLater c.1.type nP l then (.unsupported, 0)
                else (.reflexive, m')
              | kk => kk) := by
      rw [← h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
      rfl
    rw [if_neg (by rw [hment]; simp)] at hget
    rcases hpos with hp | hp
    · rw [hp] at hget
      dsimp only at hget
      by_cases hsu : ConLeche.structUsedLater c.1.type nP l = true
      · rw [if_pos hsu] at hget
        exact absurd (kinds_any_of_getD (by rw [hlen]; exact hl) (by rw [hget])) (by
          rw [huns]; simp)
      · rw [if_neg hsu] at hget
        exact hget
    · rw [hp] at hget
      dsimp only at hget
      exact absurd (kinds_any_of_getD (by rw [hlen]; exact hl) (by rw [hget])) (by
        rw [hneg]; simp)
  · exfalso
    simp only [Option.some.injEq] at h
    have hlen : ks.length = c.2 := by rw [← h]; simp
    have hget : ks.getD l (.ordinary, 0) = (RecFieldKind.negative, 0) := by
      rw [← h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
        List.getElem?_range hl]
      rfl
    exact absurd (kinds_any_of_getD (by rw [hlen]; exact hl) (by rw [hget])) (by
      rw [hneg]; simp)

omit SF S in
/-- **THE GROUP'S COPY, AS A BLOCK MEMBER** (task #315 L-B): pin
`q₀ + m`'s copy is the auxiliary block's member `p.k + (q₀ + m)` — its
former is stored at the formers' environment under the pin's auxiliary
name, and the member table finds it there (`PinsAligned` names the copy
after its pin's auxiliary, `members3_find?_name` places it). -/
theorem NestedPinsRun.groupCopyFormer {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {qq : Nat} (hqq : qq < st.pins.length) :
    ∃ (fM : MutualFormerA) (nIdxM : Nat),
      fms[p.k + qq]? = some fM ∧
      fM.cvTa.name = (pinAtE st qq).aux ∧
      (ConLeche.consMutualFormers fms env).find? (pinAtE st qq).aux
        = some (.indInfo fM.cvTa {}) ∧
      b.members3.find? (·.1 == (pinAtE st qq).aux)
        = some ((pinAtE st qq).aux, p.k + qq, nIdxM) ∧
      (pinAtE st qq).aux ∈ b.members3.map (·.1) ∧
      (pinAtE st qq).aux ∈ b.memberNames := by
  classical
  have PDm := hPD _ hqq
  have hal : ConLeche.PinsAligned p.k st := by
    refine ConLeche.elimNested_aligned ?_ R.helim
    rw [ConLeche.nestedTypes0_length, ConLeche.nestedAnnotFormers_length R.hfA]; rfl
  have hcopyName : (copyAtE st p qq).name = (pinAtE st qq).aux := by
    obtain ⟨t, ht, htn⟩ := hal.2 qq _ PDm.pin
    obtain rfl : t = copyAtE st p qq := Option.some.inj (ht.symm.trans PDm.ty)
    exact htn
  obtain ⟨nIdxM, hformM, -⟩ := (ConLeche.auxBlock_former R.hb).2 (p.k + qq) _ PDm.ty
  have hkF : p.k + qq < fms.length := by
    rw [R.h.lenFms, R.hbk]; omega
  obtain ⟨fM, hfM⟩ : ∃ fM, fms[p.k + qq]? = some fM :=
    ⟨_, List.getElem?_eq_getElem hkF⟩
  obtain ⟨hcvM, -⟩ := R.formerType _ _ hfM _ PDm.ty
  have hauxName : fM.cvTa.name = (pinAtE st qq).aux := by rw [hcvM]; exact hcopyName
  have hmemNd : b.memberNames.Nodup := by
    have h0 := R.hnd
    rw [ConLeche.MutualBlock.blockNames] at h0
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  have hmemN : (pinAtE st qq).aux ∈ b.memberNames := by
    rw [← R.h.names, ← hauxName]
    exact List.mem_map_of_mem (List.mem_of_getElem? hfM)
  refine ⟨fM, nIdxM, hfM, hauxName, by rw [← hauxName]; exact R.h.find _ _ hfM, ?_, ?_, hmemN⟩
  · rw [← hcopyName]
    exact ConLeche.members3_find?_name hmemNd hformM
  · rw [ConLeche.members3_map_fst]
    exact hmemN

/-! ## The nested field's PIN, read off the CLASSIFICATION — step two,
finished (task #315 L-B, DESIGN "the head survives the rewrite")

The mention `replaceAllNested_occurrence` wants is not available from
any record — the clause that carries it is spelled on a pin's
COMPONENTS and what the fire needs is the FIELD's arguments, and
nothing in the model tier ties the two (DESIGN §U.82 (d)).  It is
available from the CLASSIFICATION instead, by contradiction:

* suppose no parameter argument of the minted domain mentions a name
  of the growing list.  Then `nestedOccOk` answers `false` at the
  spine and at every PREFIX of it — its verdict is a function of
  `args.take ci.nP` alone, which every prefix long enough to be tested
  shares, and the shorter prefixes decline on the length test first;
* so `replaceAllNested_head_const` applies and the rewrite's output
  keeps the container's head.  That output IS the given constructor's
  `l`-th field binder, `os_instSeq_head` carries the head to the
  constructor's OPENED domain, and `normCtorValM_domHead` carries it
  across the positivity normalisation to the STORED one;
* but `mutualOpenedOk` — the kernel's own re-check of the
  classification, on the annotated constructor opened at variables —
  says a `.recursive` field's stored domain is headed by the TARGET
  MEMBER's constant.  So the container would be a member of the
  auxiliary block, while it is found in `env` and the block's formers
  are fresh there.

`hloose` is the run's too (`replaceIfNested_loose`), so the fire needs
no input beyond the pin's container record — which is
`NestedPinGroupSyn.contsEnv` since integration 3r, the monotonicity
clause this lane asked for in place of the environment EQUATION.

The conclusion is stated WITHOUT `copyResid`'s existentials: the
container member `J` travels as a binder with `copyResid`'s own three
clauses (the §U.78 (b) lesson), and what comes out is the block pin the
fire landed on, in `st.pins`, with the container's pin's head and level
arguments and the right number of components — the syntactic seed of
`PinCorr`'s `J` and `lvls` clauses. -/

/-- **THE COPY'S NESTED FIELD LANDS ON A BLOCK PIN** (task #315 L-B):
at a container field finitary-recursive at one of the CONTAINER's own
pins, whose copy the auxiliary block also classified `.recursive`, the
elimination minted (or reused) a pin of the block whose container is
the container's pin's container at the substituted level arguments. -/
theorem copyPinFCorr {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hnest : ¬ dJ.tgts i' j l < dJ.k)
    (hrec : (dJ.ksF i' j).getD l .ordinary = .recursive)
    (hkA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.recursive)
    {ci : ContainerInfo} {J : ContainerMember}
    (hci : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (hJmem : J ∈ ci.members) (hJn : J.name = (pinsS.getD (q₀ + i') default).J)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ) (ψ : Name → Nat) :
    ∃ (ci' : ContainerInfo) (qn : ConLeche.NestedPin) (qq : Nat),
      ConLeche.containerInfo? env (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J = some ci' ∧
      (dJ.pinAt (dJ.tgts i' j l - dJ.k)).nPJ = ci'.nP ∧
      st.pins[qq]? = some qn ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + qq ∧
      qn.pin.getAppFn = Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
        ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
          (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls)) ∧
      qn.pin.getAppArgs.length = ci'.nP ∧
      (pinsS.getD qq default).J = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J ∧
      (pinsS.getD qq default).lvls = ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls).map
        (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls) ∧
      (pinsS.getD qq default).DsE = qn.pin.getAppArgs ∧
      (∀ (cvT : ConstantVal) (caps : IndCaps),
        (ConLeche.consMutualFormers (fms.take p.k) env).find?
            (pinsS.getD (q₀ + i') default).J = some (.indInfo cvT caps) →
        J.lps = cvT.levelParams) ∧
      (pinsS.getD qq default).Ds ψ
        = ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ds
            ((pinsS.getD (q₀ + i') default).ψJ ψ)).map
            (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) 0) ∧
      (∃ (cvQ : ConstantVal) (capsQ : IndCaps),
        (ConLeche.consMutualFormers (fms.take p.k) env).find?
            (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J = some (.indInfo cvQ capsQ) ∧
        ∀ pp ∈ cvQ.levelParams,
          (pinsS.getD qq default).ψJ ψ pp
            = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).ψJ
                ((pinsS.getD (q₀ + i') default).ψJ ψ) pp) ∧
      (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
            ((fms.take p.k).map (·.cvTa.name)) ψ).EA (p.k + qq)
        = AnnotTerm.mkAppN (mp₁'.base2.acval (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).ψJ
              ((pinsS.getD (q₀ + i') default).ψJ ψ)))
            (((dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ds
              ((pinsS.getD (q₀ + i') default).ψJ ψ)).map
              (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) 0)) := by
  classical
  obtain ⟨cc, JR, ciR, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciPR, hJmemR, hJccR, hn, hty, hnf, hJnameR, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    -, -, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ := R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  obtain ⟨st₁, st₂, hrun, hpre, hmint⟩ := hfields l hlcc
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlA
  have hlks : l < (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).length := by
    obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
    rw [hksLen]; exact hlA
  -- the given type's two-stage opening, and the field's domain in it
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  obtain ⟨-, sorts, -, hCtor⟩ := R.h.runC _ _ hcA
  obtain ⟨hnorm, -, hbndC⟩ := ConLeche.checkMutualCtor_true_norm hCtor
  have hcvC : (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).cv
      = ⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩ := by
    rw [List.getD_eq_getElem?_getD, hbc]; rfl
  rw [hcvC] at hnorm hbndC
  rw [hnF] at hnorm hopX'
  obtain ⟨fvsA, -, -, hlawA⟩ := ConLeche.openPisAtFvars_mkPisB b.nP pbs₀ hpbs₀len 0
  have hfvsA : fvsA = params := by
    have hlaw := hlawA o'
    rw [← ConLeche.stripPis_mkPisB _ hstripF] at hlaw
    exact (Prod.mk.inj (Option.some.inj (hlaw.symm.trans hopb))).1
  have hop1 : ConLeche.openPisAtFvars b.nP (closeTelescope pbs₀ 0 cbody') 0
      = some (params, cbody') := by
    rw [ConLeche.closeTelescope_eq_mkPisB pbs₀ 0 cbody' hpbs₀f, hpbs₀len, hlawA, hfvsA,
      ConLeche.instSeq_abstractRange_fvs b.nP params cbody' hcbb hplenB hidxP hcbl]
  obtain ⟨xfvs, hxflen, -, hlawX⟩ := ConLeche.openPisAtFvars_mkPisB cc.nFields Fs' hlenF b.nP
  obtain ⟨resB, hcb'⟩ : ∃ r, cbody'.stripPis cc.nFields = some (Fs', r) := ⟨_, hcb⟩
  have hop2 : ConLeche.openPisAtFvars cc.nFields cbody' b.nP
      = some (xfvs, Expr.instSeq xfvs (cc.nFields - 1) resB) := by
    rw [ConLeche.stripPis_mkPisB _ hcb']; exact hlawX resB
  obtain ⟨x, hx⟩ : ∃ x, xfvs[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxflen]; exact hlcc)⟩
  -- the given opened domain, at the field's own cut
  have hstripC : (closeTelescope pbs₀ 0 cbody').stripPis (b.nP + cc.nFields)
      = some (pbs₀ ++ ConLeche.abstractTele 0 pbs₀.length 0 Fs',
          resB.abstractRange 0 pbs₀.length Fs'.length) := by
    rw [ConLeche.stripPis_mkPisB _ hcb']
    rw [show b.nP + cc.nFields = pbs₀.length + Fs'.length from by rw [hpbs₀len, hlenF]]
    exact ConLeche.closeTelescope_mkPisB_strip hpbs₀f
  have habs : (ConLeche.abstractTele 0 pbs₀.length 0 Fs')[l]?
      = some ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show l < (ConLeche.abstractTele 0 pbs₀.length 0 Fs').length from by
        rw [ConLeche.abstractTele_length, hlenF]; exact hlcc)]
    rfl
  have hxdom : x.fvarTypeD = Expr.instSeq (params ++ xfvs.take l) (b.nP + l - 1)
      ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default).1 :=
    ConLeche.os_field_domain b.nP cc.nFields l
      (openPisAtFvars_add b.nP hop1 (by rw [Nat.zero_add]; exact hop2))
      hstripC hplenB hpbs₀len hx habs
  have hFsl : Fs'[l]? = some (Fs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenF]; exact hlcc)]
    rfl
  have hFlBnd : (Fs'.getD l default).1.looseBVarsBounded l = true := by
    have h := ConLeche.stripPis_binder_bounded cc.nFields hcb' hcbb l _ hFsl
    simpa using h
  have hFlLeaves : ∀ lf ∈ (Fs'.getD l default).1.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ params :=
    fun lf hlf => hcbl lf (ConLeche.stripPis_binder_leaves cc.nFields hcb' l _ hFsl lf hlf)
  have hxdom2 : x.fvarTypeD = Expr.instSeq (xfvs.take l) (l - 1) (Fs'.getD l default).1 := by
    rw [hxdom, ConLeche.abstractTele_getD 0 pbs₀.length Fs' 0 l (by rw [hlenF]; exact hlcc),
      Expr.instSeq_append, hplenB, show b.nP + l - 1 - b.nP = l - 1 from by omega, hpbs₀len]
    simp only [Nat.zero_add]
    rw [ConLeche.instSeq_abstractRange_fvs_at b.nP l params _ hFlBnd hplenB hidxP hFlLeaves]
  -- copyResid's container member IS the one that travelled in
  obtain rfl : ci = ciR := Option.some.inj (hci.symm.trans hciPR)
  obtain rfl : J = JR :=
    ConLeche.containerInfo?_member_det hci hci rfl hJmem hJmemR (hJn.trans hJnameR.symm)
  -- the minted domain's shape, and the pin's container at `env`
  obtain ⟨hqlt, hheadC, harity, hshape⟩ :=
    copyPinFDom S hi' hj hty hnf hstripJ hpl hfl hlcc hnest hrec
  obtain ⟨ci', hci'₁, hnPeq⟩ := (CM ci hciPR).pinNP _ hqlt
  have hci'₀ := S.contsEnv _ hqlt ci' hci'₁
  obtain ⟨cvq, capsq, -, -, -, -, hfindq, -, -, -, -⟩ := ConLeche.containerInfo?_inv hci'₀
  obtain ⟨x', hx'⟩ : ∃ x', (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnF]; exact hlcc)⟩
  refine ⟨ci', ?_⟩
  -- the minted domain, as the spine step one names
  rw [hshape J.lps (pinsS.getD (q₀ + i') default).lvls
    (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)] at hrun
  obtain ⟨AS, hAS⟩ : ∃ AS : List Expr, AS = (((fcs.getD l default).1.getAppArgs.map
      (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
      (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))) := ⟨_, rfl⟩
  rw [← hAS] at hrun
  have hASlen : AS.length = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).nPJ
      + (dJ.pinAt (dJ.tgts i' j l - dJ.k)).nIdx := by
    rw [hAS, List.length_map, List.length_map, harity]
  have hnPle : ci'.nP ≤ AS.length := by rw [hASlen, ← hnPeq]; omega
  -- the container is not a former of the block
  have hne : ∀ g ∈ fms, g.cvTa.name ≠ (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J := by
    intro g hg heq
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hg
    have hfr := R.h.fresh t g ht
    rw [heq, hfindq] at hfr
    exact nomatch hfr
  have hIq : ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).J == ConLeche.quotName) = false := by
    cases hq : (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J == ConLeche.quotName with
    | false => rfl
    | true =>
      exfalso
      have hnone : ConLeche.containerInfo? env (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J = none := by
        unfold ConLeche.containerInfo?
        simp [hq]
      rw [hnone] at hci'₀
      simp at hci'₀
  -- ==== THE MENTION, read off the CLASSIFICATION ====
  have hment : ((AS.take ci'.nP).any
      (fun a => st₁.newNames.any fun T => a.mentionsConst T)) = true := by
    cases hno : ((AS.take ci'.nP).any (fun a => st₁.newNames.any fun T => a.mentionsConst T)) with
    | true => rfl
    | false =>
      exfalso
      -- every prefix of the spine declines
      have hnone : ∀ k : Nat, ConLeche.replaceIfNested env (p.lps.map Level.param) params pbs₀ st₁
          (Expr.mkAppN (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
              (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls))) (AS.take k)) = .ok none := by
        intro k
        rcases hnil : AS.take k with _ | ⟨a₀, as₀⟩
        · rfl
        · obtain ⟨u, v, huv⟩ := ConLeche.mkAppN_app (a₀ :: as₀) (by simp) (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
              (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls)))
          -- the mention fails on this prefix too, whether it is longer or
          -- shorter than the parameter count
          have hsub : ((a₀ :: as₀).take ci'.nP).any
              (fun a => st₁.newNames.any fun T => a.mentionsConst T) = false := by
            rcases hb : ((a₀ :: as₀).take ci'.nP).any
                (fun a => st₁.newNames.any fun T => a.mentionsConst T) with _ | _
            · rfl
            · exfalso
              obtain ⟨a₁, ha₁, hm₁⟩ := List.any_eq_true.mp hb
              rw [← hnil, List.take_take] at ha₁
              have ha₂ : a₁ ∈ AS.take ci'.nP := by
                rcases Nat.le_total ci'.nP k with hle | hle
                · rw [Nat.min_eq_left hle] at ha₁
                  exact ha₁
                · rw [Nat.min_eq_right hle,
                    show AS.take k = (AS.take ci'.nP).take k from by
                      rw [List.take_take, Nat.min_eq_left hle]] at ha₁
                  exact List.mem_of_mem_take ha₁
              have hcon : (AS.take ci'.nP).any
                  (fun a => st₁.newNames.any fun T => a.mentionsConst T) = true :=
                List.any_eq_true.mpr ⟨a₁, ha₂, hm₁⟩
              rw [hno] at hcon
              exact nomatch hcon
          have hocc : ConLeche.nestedOccOk (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J st₁.newNames
              ci'.nP (a₀ :: as₀) = .ok false := by
            simp only [ConLeche.nestedOccOk, hsub, Bool.false_and, Bool.false_eq_true, if_false]
          rw [huv, ConLeche.replaceIfNested]
          simp only
          rw [← huv, Expr.getAppFn_mkAppN, Expr.getAppArgs_mkAppN]
          simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append]
          rw [hfindq]
          simp only
          rw [hIq]
          simp only [Bool.false_eq_true, if_false]
          rw [hci'₀]
          simp only
          rw [hocc]
          simp only [bind, Except.bind, Bool.not_false]
          rw [if_pos trivial, ite_self]
          rfl
      -- so the container's head survives, and the STORED domain carries it
      have hFlHead := ConLeche.replaceAllNested_head_const AS hnone hrun
      have hxHead : x.fvarTypeD.getAppFn = (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
              (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls))) := by
        rw [hxdom2]
        exact os_instSeq_head hFlHead _ _
      have hfindF : (ConLeche.consMutualFormers fms env).find?
          (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J = some (.indInfo cvq capsq) := by
        rw [ConLeche.consMutualFormers_find?_of_ne hne]
        exact hfindq
      obtain ⟨args', hx'head⟩ := ConLeche.normCtorValM_domHead mp₁.base2.wf hnorm hbndC hop1 hop2
        hopP' hopX' hx hx' hfindF
        (by rw [← Expr.mkAppN_getApp x.fvarTypeD, hxHead])
      -- but the classification's own re-check says the head is the TARGET MEMBER's
      obtain ⟨-, hopen, htgtLt⟩ := R.h.ksJ _ _ hcA
      have hmemHead := mutualOpenedOk_recHead hopen hopP' (by rw [hnF]; exact hopX') hx' hkA
      rw [hx'head, Expr.getAppFn_mkAppN] at hmemHead
      simp only [Expr.getAppFn] at hmemHead
      obtain ⟨ft, hft⟩ : ∃ ft, fms[tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l]?
          = some ft := ⟨_, List.getElem?_eq_getElem (htgtLt l)⟩
      obtain ⟨hnameT, -⟩ := R.h.memT _ _ hft
      refine hne ft (List.mem_of_getElem? hft) ?_
      rw [← hnameT]
      exact ((ConLeche.Expr.const.inj hmemHead).1).symm
  -- ==== the fire ====
  have hriOk : ∃ r, ConLeche.replaceIfNested env (p.lps.map Level.param) params pbs₀ st₁
      (Expr.mkAppN (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
              (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls))) AS) = .ok r := by
    cases hri : ConLeche.replaceIfNested env (p.lps.map Level.param) params pbs₀ st₁
        (Expr.mkAppN (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
              (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls))) AS) with
    | ok r => exact ⟨r, rfl⟩
    | error err =>
      exfalso
      obtain ⟨a₁, ha₁, hm₁⟩ := List.any_eq_true.mp hment
      obtain ⟨T₁, hT₁, hmT₁⟩ := List.any_eq_true.mp hm₁
      have hmention : (st₁.newNames.any fun T => Expr.mentionsConst T
          (Expr.mkAppN (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
              (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls))) AS)) = true :=
        List.any_eq_true.mpr ⟨T₁, hT₁,
          ConLeche.mentionsConst_mkAppN_of_arg (List.mem_of_mem_take ha₁) hmT₁ _⟩
      rw [ConLeche.replaceAllNested.eq_def] at hrun
      simp only [hmention, Bool.not_true, Bool.false_eq_true, if_false, hri] at hrun
      exact nomatch hrun
  obtain ⟨r₀, hri⟩ := hriOk
  have hloose := ConLeche.replaceIfNested_loose rfl hfindq hci'₀ hnPle hment hri
  obtain ⟨qn', hqnMem, hqnPin, hqnEq⟩ :=
    ConLeche.replaceAllNested_occurrence rfl hfindq hci'₀ hnPle hment hloose hrun
  -- ==== the pin's INDEX: the mimic's NAME is the target member's ====
  obtain ⟨qq, hqq⟩ := List.getElem?_of_mem (hpre.subset hqnMem)
  have hqqLt : qq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
  -- `pinAtE`'s body is not exposed here; the run's own record reads it
  have hpinAtE : pinAtE st qq = qn' :=
    Option.some.inj ((hPD qq hqqLt).pin.symm.trans hqq)
  obtain ⟨fM, nIdxM, hfM, hauxM, hfindM, -, -, -⟩ := R.groupCopyFormer hPD hqqLt
  rw [hpinAtE] at hauxM hfindM
  -- the rewritten domain is the MIMIC applied, so the given constructor's
  -- opened domain is mimic-headed, and so is the stored one
  have hFlHead' : (Fs'.getD l default).1.getAppFn
      = Expr.const qn'.aux (p.lps.map Level.param) := by
    rw [hqnEq, Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN]
    rfl
  have hxHead' : x.fvarTypeD.getAppFn = Expr.const qn'.aux (p.lps.map Level.param) := by
    rw [hxdom2]
    exact os_instSeq_head hFlHead' _ _
  obtain ⟨argsM, hx'headM⟩ := ConLeche.normCtorValM_domHead mp₁.base2.wf hnorm hbndC hop1 hop2
    hopP' hopX' hx hx' hfindM (by rw [← Expr.mkAppN_getApp x.fvarTypeD, hxHead'])
  obtain ⟨-, hopen, htgtLt⟩ := R.h.ksJ _ _ hcA
  have hmemHead := mutualOpenedOk_recHead hopen hopP' (by rw [hnF]; exact hopX') hx' hkA
  rw [hx'headM, Expr.getAppFn_mkAppN] at hmemHead
  simp only [Expr.getAppFn] at hmemHead
  -- the two names are one, and the block's member names are `Nodup`
  obtain ⟨ft, hft⟩ : ∃ ft, fms[tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l]?
      = some ft := ⟨_, List.getElem?_eq_getElem (htgtLt l)⟩
  obtain ⟨hnameT, -⟩ := R.h.memT _ _ hft
  have hnameEq : ft.cvTa.name = fM.cvTa.name := by
    rw [hauxM, ← hnameT]
    exact ((ConLeche.Expr.const.inj hmemHead).1).symm
  have hmemNd : (fms.map (·.cvTa.name)).Nodup := by
    have h0 := R.hnd
    unfold ConLeche.MutualBlock.blockNames at h0
    rw [R.h.names]
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  have hidx : tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = p.k + qq := by
    refine nodup_getElem?_inj hmemNd (a := ft.cvTa.name) ?_ ?_
    · rw [List.getElem?_map, hft]; rfl
    · rw [List.getElem?_map, hfM, hnameEq]; rfl
  -- the BLOCK pin's own record at that index: its container and its level
  -- arguments are `PinCorr`'s two syntactic clauses
  obtain ⟨hJsyn, hpinSyn⟩ := SF.pinRec _ _ hqq
  have hhead : qn'.pin.getAppFn = Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
      ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
        (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls)) := by
    rw [hqnPin, Expr.getAppFn_mkAppN]
    rfl
  have hheadS : qn'.pin.getAppFn
      = Expr.const qn'.container (pinsS.getD qq default).lvls := by
    rw [hpinSyn, Expr.getAppFn_mkAppN]
    rfl
  obtain ⟨hcname, hclvls⟩ := ConLeche.Expr.const.inj (hheadS.symm.trans hhead)
  -- the container's group shares its level parameters, and the pin's
  -- container is stored at `env` (so at the formers' environment too)
  obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, hfI, -, -, -, hMall⟩ :=
    ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, capsC, -, -, -, -, -, hlpsJ, -, hlpsT, -, -⟩ := hMall J hJmem
  have hneJ : ∀ g ∈ fms.take p.k, g.cvTa.name ≠ (pinsS.getD (q₀ + i') default).J := by
    intro g hg heq
    obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hg)
    have hfr := R.h.fresh t g ht
    rw [heq, hfI] at hfr
    exact nomatch hfr
  -- ==== THE COMPONENTS' READING ====
  -- the minted constructor, opened at its field binders
  obtain ⟨resM, hstripCI'⟩ : ∃ r, cI.stripPis cc.nFields = some (fcs', r) := ⟨_, hstripCI⟩
  have hfcs'len : fcs'.length = cc.nFields := Expr.stripPis_length _ hstripCI'
  obtain ⟨xfvs', hxf'len, -, hlawX'⟩ :=
    ConLeche.openPisAtFvars_mkPisB cc.nFields fcs' hfcs'len b.nP
  have hopM : ConLeche.openPisAtFvars cc.nFields cI b.nP
      = some (xfvs', Expr.instSeq xfvs' (cc.nFields - 1) resM) := by
    rw [ConLeche.stripPis_mkPisB _ hstripCI']; exact hlawX' _
  obtain ⟨xI, hxI⟩ : ∃ x, xfvs'[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxf'len]; exact hlcc)⟩
  have hfcsl' : fcs'[l]? = some (fcs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hfcs'len]; exact hlcc)]
    rfl
  have hxIdom : xI.fvarTypeD = Expr.instSeq (xfvs'.take l) (l - 1) (fcs'.getD l default).1 :=
    Verify.openPisAtFvars_domain cc.nFields hopM hstripCI' l xI (fcs'.getD l default) hxI hfcsl'
  -- the two pins' components, scoped and read
  have hqstO : q₀ + i' < st.pins.length := by rw [← SF.pinsLen]; have := S.seg; omega
  have hqSO : q₀ + i' < pinsS.length := by have := S.seg; omega
  have hqSq : qq < pinsS.length := by rw [SF.pinsLen]; exact hqqLt
  have PDo := hPD _ hqstO
  obtain ⟨hJcO, hpinSO⟩ := SF.pinRec _ _ PDo.pin
  have hpinO := PDo.pinEq
  rw [hpinSO] at hpinO
  have hDsEO : (pinsS.getD (q₀ + i') default).DsE = (srcAtE st p (q₀ + i')).2.2 := by
    have hA := congrArg Expr.getAppArgs hpinO
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at hA
    exact hA
  have hspineO := SF.pinDs _ hqSO ψ
  rw [hDsEO] at hspineO
  obtain ⟨-, hcl₀, hbt₀, hFD₀⟩ := R.former0
  obtain ⟨hpinsE, fvsS, oS, hopS, hsc⟩ := R.scoped
  obtain ⟨hbndO, hleafO⟩ := hsc _ (List.mem_of_getElem? PDo.pin)
  have hwsO := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hopS hleafO ψ
  rw [PDo.pinEq] at hbndO hwsO
  obtain ⟨-, hwsDO⟩ := ConLeche.WScoped_of_mkAppN hwsO
  obtain ⟨-, hbndDO⟩ := ConLeche.looseBVarsBounded_of_mkAppN hbndO
  have hDsScO : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2,
      Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true :=
    fun a ha => ⟨hwsDO a ha, hbndDO a ha⟩
  -- the BLOCK pin's components ARE the minted spine's first arguments
  have hDsEq : (pinsS.getD qq default).DsE = AS.take ci'.nP := by
    have h1 := congrArg Expr.getAppArgs (hpinSyn.symm.trans hqnPin)
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at h1
    exact h1
  -- the BLOCK pin's own components, scoped the same way
  obtain ⟨hbndQ, hleafQ⟩ := hsc _ (List.mem_of_getElem? hqq)
  have hwsQ := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hopS hleafQ ψ
  rw [hpinSyn] at hbndQ hwsQ
  obtain ⟨-, hwsDQ⟩ := ConLeche.WScoped_of_mkAppN hwsQ
  have hDsScQ : ∀ a ∈ (pinsS.getD qq default).DsE, Expr.WScoped b.nP a := hwsDQ
  -- the minted domain's reading, at the container's NESTED-FIELD form
  have hmfr := mintFieldRead S hi' hj hksJ (by rw [hty]; exact hccf) (by rw [hty]; exact hccb)
    hDsScO ψ hspineO (by rw [hty]; exact hinstCI) (by rw [hnf]; exact hopM) hlF hxI
  obtain ⟨cvTJ, capsJ, cvRJ, mIJ, rPJ, rulesJ, hfindJ₂, hIJ, hψJ⟩ := S.stored i' hi'
  obtain ⟨-, -, hCDJ⟩ := hIJ.ctors i' j cAJ hIJ.memberLt hj
  have hnestOf : dJ.nestOf i' j l = some (dJ.tgts i' j l - dJ.k) := dJ.nestOf_some hnest
  rw [hCDJ.nestEntry ((pinsS.getD (q₀ + i') default).ψJ ψ) l _ hnestOf hrec hlF,
    AnnotTerm.instAll_mkAppN, List.map_append] at hmfr
  -- the minted domain IS step one's spine; the SECOND instantiation layer is
  -- the identity on the pin's components, which is step two's `hloose`
  have hxIspine : xI.fvarTypeD
      = Expr.mkAppN (Expr.const (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
          ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).lvls.map
            (Level.subst J.lps (pinsS.getD (q₀ + i') default).lvls))) (AS.map (Expr.instSeq (xfvs'.take l) (l - 1))) := by
    rw [hxIdom, hfcs' l hlcc, hshape J.lps (pinsS.getD (q₀ + i') default).lvls
      (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l), ← hAS, ConLeche.instSeq_mkAppN_const]
  have htakeId : (AS.take ci'.nP).map (Expr.instSeq (xfvs'.take l) (l - 1))
      = AS.take ci'.nP := by
    have h1 : (AS.take ci'.nP).map (Expr.instSeq (xfvs'.take l) (l - 1))
        = (AS.take ci'.nP).map id :=
      List.map_congr_left (fun a ha => Expr.instSeq_eq_self _ _ (hloose a ha))
    rw [h1, List.map_id]
  rw [hxIspine] at hmfr
  obtain ⟨fa, vs, -, hspM, heaM⟩ := denoteMeta_mkAppN_inv hmfr
  have hsplen : ∀ {as : List Expr} {vs' : List AnnotTerm},
      DenoteMetaSpine mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ
        (b.nP + l) as vs' → as.length = vs'.length := by
    intro as vs' h
    induction h with
    | nil => rfl
    | cons _ _ ih => simp only [List.length_cons, ih]
  have hcompsLen : ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ds ((pinsS.getD (q₀ + i') default).ψJ ψ)).length = ci'.nP := by
    rw [(hIJ.pinShape _ hqlt _).2.1, hnPeq]
  have hvsLen : ((((dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ds ((pinsS.getD (q₀ + i') default).ψJ ψ)).map (·.liftN l 0)).map (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l)
      ++ ((dJ.eissF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l []).map
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l)).length = vs.length := by
    rw [List.length_append, List.length_map, List.length_map, List.length_map, hcompsLen,
      hCDJ.nestEisLen _ l _ hnestOf hrec hlF, ← hsplen hspM, List.length_map, hASlen, ← hnPeq]
  obtain ⟨-, hvs⟩ := AnnotTerm.mkAppN_inj heaM hvsLen
  -- the spine splits at the components, and the block pin's reading LIFTS
  rw [← List.take_append_drop ci'.nP AS, List.map_append] at hspM
  obtain ⟨vs₁, vs₂, hvsSplit, hsp₁, -⟩ := DenoteMetaSpine.append_inv hspM
  rw [htakeId] at hsp₁
  have hspQ : DenoteMetaSpine mp₁'.base2.acval
      (ConLeche.consMutualFormers (fms.take p.k) env) ψ (b.nP + l) (AS.take ci'.nP)
      (((pinsS.getD qq default).Ds ψ).map (fun X => AnnotTerm.liftN l X 0)) := by
    have hbase := SF.pinDs _ hqSq ψ
    rw [hDsEq] at hbase
    have hstep : ∀ (a : Expr) (v : AnnotTerm), a ∈ AS.take ci'.nP →
        denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ b.nP
            (id a) = some v →
        denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ
            (b.nP + l) (id a) = some (AnnotTerm.liftN l v 0) := by
      intro a v ha hv
      have hl := denoteMeta_lift (acval := mp₁'.base2.acval)
        (env := ConLeche.consMutualFormers (fms.take p.k) env) (φ := ψ)
        mp₁'.base2.acval_closed (hDsScQ a (by rw [hDsEq]; exact ha)) (b.nP + l) (by omega)
      simp only [id] at hv ⊢
      rw [hv] at hl
      simp only [Option.map_some, Nat.add_sub_cancel_left] at hl
      exact hl
    have hmm := DenoteMetaSpine.map_map (f := id) (g := id)
      (h := fun X => AnnotTerm.liftN l X 0) (by rw [List.map_id]; exact hbase) hstep
    rw [List.map_id] at hmm
    exact hmm
  have hcomp := DenoteMetaSpine.unique hsp₁ hspQ
  -- the lift cancels
  have hmapInj : ∀ L₁ L₂ : List AnnotTerm,
      L₁.map (fun X => AnnotTerm.liftN l X 0) = L₂.map (fun X => AnnotTerm.liftN l X 0) →
      L₁ = L₂ := by
    intro L₁ L₂ h
    have hlen : L₁.length = L₂.length := by
      have h0 := congrArg List.length h
      simpa using h0
    refine List.ext_getElem hlen (fun n h1 h2 => ?_)
    refine AVExprSubst.liftN0_inj l ?_
    have h0 := congrArg (fun L => L[n]?) h
    simp only [List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq] at h0
    exact h0
  -- the block pin's container, and its components' reading
  have hJQ : (pinsS.getD qq default).J = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J := by
    rw [hJsyn]; exact hcname
  have hDsQ : (pinsS.getD qq default).Ds ψ
      = ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ds
          ((pinsS.getD (q₀ + i') default).ψJ ψ)).map
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) 0) := by
    -- the components' reading: the lift cancels on both sides
    refine (hmapInj _ _ ?_).symm
    have hlen₁ : ((((dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ds ((pinsS.getD (q₀ + i') default).ψJ ψ)).map (·.liftN l 0)).map (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l)).length
        = vs₁.length := by
      rw [List.length_map, List.length_map, hcompsLen, ← hsplen hsp₁, List.length_take]
      omega
    have hsplit := hvs.trans hvsSplit
    obtain ⟨hfirst, -⟩ := List.append_inj hsplit hlen₁
    rw [← hcomp, ← hfirst, List.map_map, List.map_map]
    refine List.map_congr_left (fun X _ => ?_)
    exact (instAll_liftN0 ((pinsS.getD (q₀ + i') default).Ds ψ) l X).symm
  -- ==== THE TWO PINS' LEVEL ASSIGNMENTS ====
  -- the pin's container is stored at `env`, so at the formers' environment too
  have hneQ : ∀ g ∈ fms.take p.k, g.cvTa.name ≠ (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J := by
    intro g hg heq
    obtain ⟨t, ht⟩ := List.getElem?_of_mem (List.mem_of_mem_take hg)
    have hfr := R.h.fresh t g ht
    rw [heq, hfindq] at hfr
    exact nomatch hfr
  have hfindq₂ : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J = some (.indInfo cvq capsq) := by
    rw [ConLeche.consMutualFormers_find?_of_ne hneQ]; exact hfindq
  -- the CONTAINER's own pin: its assignment is the substitution at its
  -- container's level parameters (`ContainerModeled.pinψ`)
  obtain ⟨hlenQ, hψQ⟩ := (CM ci hciPR).pinψ _ hqlt cvq capsq hfindq₂
  -- the BLOCK's pin: the same, off ITS OWN group's record
  obtain ⟨q₀', kJ', i'', hqqEq, hi'', S'⟩ := SF.groupsAt dsR xFvsR qq hqSq ci'
    (by rw [hJQ]; exact hci'₀)
  obtain ⟨cvQ', capsQ', -, -, -, -, hfindQ'₀, -, hψQ'₀⟩ := S'.stored i'' hi''
  -- the group record spells the pin through the block model's `pinAt`,
  -- which is `pinsS.getD` by definition; `rw` needs the spelling the
  -- consumers use
  have hfindQ' : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD (q₀' + i'') default).J = some (.indInfo cvQ' capsQ') := hfindQ'₀
  have hψQ' : ∀ ψ : Name → Nat, (pinsS.getD (q₀' + i'') default).ψJ ψ
      = Level.substFn ψ cvQ'.levelParams (pinsS.getD (q₀' + i'') default).lvls := hψQ'₀
  rw [← hqqEq] at hfindQ' hψQ'
  have hcvQ : cvQ' = cvq := by
    have hfq : (ConLeche.consMutualFormers (fms.take p.k) env).find?
        (pinsS.getD qq default).J = some (.indInfo cvq capsq) := by
      rw [hJQ]; exact hfindq₂
    have h := hfindQ'.symm.trans hfq
    simp only [Option.some.injEq, ConLeche.ConstantInfo.indInfo.injEq] at h
    exact h.1
  rw [hcvQ] at hψQ'
  -- the group's OWN pin's assignment, and the container member's level
  -- parameters (ITS constant's)
  have hψJ' : ∀ ψ : Name → Nat, (pinsS.getD (q₀ + i') default).ψJ ψ
      = Level.substFn ψ cvTJ.levelParams (pinsS.getD (q₀ + i') default).lvls := hψJ
  have hlpsQ : J.lps = cvTJ.levelParams := by
    have hfindT : (ConLeche.consMutualFormers (fms.take p.k) env).find?
        (pinsS.getD (q₀ + i') default).J = some (.indInfo cvTJ capsJ) := hfindJ₂
    rw [ConLeche.consMutualFormers_find?_of_ne hneJ] at hfindT
    obtain rfl : cvTJ = cvT₀ := by
      have h := hfI.symm.trans hfindT
      simp only [Option.some.injEq, ConLeche.ConstantInfo.indInfo.injEq] at h
      exact h.1.symm
    rw [hlpsJ, hlpsT]
  -- the two assignments agree AT the container's own level parameters —
  -- `Level.substFn_map_subst`, which is pointwise and not an equality of
  -- assignments (the copies' level arguments are the container's pin's
  -- SUBSTITUTED, so the composition is the group's own assignment)
  have hagree : ∀ pp ∈ cvq.levelParams,
      (pinsS.getD qq default).ψJ ψ pp
        = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).ψJ
            ((pinsS.getD (q₀ + i') default).ψJ ψ) pp := by
    intro pp hpp
    rw [hψQ' ψ, hclvls, Level.substFn_map_subst hlenQ hpp, hψQ, hψJ' ψ, hlpsQ]
  refine ⟨qn', qq, hci'₀, hnPeq, hqq, ?_, hhead, ?_, hJQ, hclvls, ?_, ?_, hDsQ,
    ⟨cvq, capsq, hfindq₂, hagree⟩, ?_⟩
  · rw [mutTgts_getD hGlt hnFs]
    exact hidx
  · rw [hqnPin, Expr.getAppArgs_mkAppN]
    simp only [Expr.getAppArgs, List.nil_append, List.length_take]
    rw [hASlen, ← hnPeq]
    omega
  · rw [hpinSyn, Expr.getAppArgs_mkAppN]
    simp only [Expr.getAppArgs, List.nil_append]
  · intro cvT caps hfindT
    rw [ConLeche.consMutualFormers_find?_of_ne hneJ] at hfindT
    obtain rfl : cvT = cvT₀ := by
      have h := hfI.symm.trans hfindT
      simp only [Option.some.injEq, ConLeche.ConstantInfo.indInfo.injEq] at h
      exact h.1.symm
    rw [hlpsJ, hlpsT]
  · -- the TARGET'S READING at the block pin: the pin branch of
    -- `targetRead`, with the head's assignment moved by `acval_params`
    have hheadEA : mp₁'.base2.acval (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
          ((pinsS.getD qq default).ψJ ψ)
        = mp₁'.base2.acval (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J
          ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).ψJ
            ((pinsS.getD (q₀ + i') default).ψJ ψ)) :=
      mp₁'.base2.acval_params _ _ hfindq₂ _ _ (fun pp hpp => hagree pp hpp)
    show targetRead mp₁'.base2.acval ((fms.take p.k).map (·.cvTa.name)) pinsS b.nP p.k ψ
        (p.k + qq) = _
    rw [targetRead_of_pin (by omega), show p.k + qq - p.k = qq from by omega, hJQ, hDsQ,
      hheadEA]

/-- **THE COPY'S TARGET'S INDEX DATA AT A PIN TARGET** (task #315 L-B):
at the block pin the nested field landed on, the target view's index
universe and index telescope are the pin's CONTAINER GROUP's block
model's, at the group-relative index the pin table's own `grpBase`
names, and at the CONTAINER's pin's level assignment.

This is the block half of `PinCorr`'s `u` and `Ids` clauses, and it is
everything those clauses need that this tree carries.  The index data
come off `NestedPinSynFacts.groupsAt` at the pin — the group syn at the
NAMED model `blockOf mp.base2 ci'`, which is the same content lane
L-E's derived `NestedPinSynFacts.pinSem` exposes per pin — through
`pinU`, `pinPps` and `pinNP`; the ASSIGNMENT moves by the two models'
level-parameter congruences (`IsBlockModel.uParams` for the universe,
`FormerData.params` for the telescope), which is what the pointwise
agreement of `copyPinFCorr` supplies: the two pins' assignments agree
AT the container's own level parameters and not as functions, which is
why the congruences are stated over a membership.

What is left of `PinCorr`'s two clauses after this is exactly

    (dJ.pinAt qK).u   ψK = (blockOf mp.base2 ci').uM   i₂ ψK
    (dJ.pinAt qK).Ids ψK = (blockOf mp.base2 ci').IdsM i₂ ψK

at `ψK = (dJ.pinAt qK).ψJ ((pinsS.getD (q₀ + i') default).ψJ ψ)` — the
CONTAINER's own pin read against ITS container's block model at the
same group-relative index.  That is a `PinGroupView` at `dJ`
(`PinGroupView.pinU`, `pinPps`/`pinNP`, which is how
`pinCorr_of_ownPins`'s `huIds` premise is meant to be discharged).

**It is `PinShapes`' first component, and `PinShapes` takes the
container model family ABSTRACTLY** (`B : ContainerInfo → BlockModel V`,
not `blockOf`): at every pin `q` it hands back a
`PinGroupView d (B ci) q₀ kJ` at the pin's own container record, whose
`name` field forces the index by the pin's name rather than by
position.  An earlier revision of this comment said the view was
available only at the concrete `blockOf` and only where the run holds
`PinsModeled`; that was wrong, and wrong in the direction that helps —
the view is at the abstract family the shape is parameterised by, one
level out from the per-`dJ` records swept below.

Those records are still the wrong place to look for it:
`NestedPinGroupSyn`'s `modeled` gives `ContainerModeled`, whose pin
clauses are `pinψ`, `pinNP`, `pinConts`, `pinParams`, `nestMention` and
`pinsNotMembers`, and `IsBlockModels` constrains a pin's `u`/`Ids` only
through `pinShape`, `pinMem`/`pinMono` and `pinLeaf` — properties of
`dJ`'s own carriers rather than a tie to the pin's container's model.
The derivation off the shape record is landing on the entry lane's
branch as a single named lemma, with the universe restated at the pin's
own assignment (the form these clauses want), and arrives with the
positivity record at the next integration. -/
theorem copyPinFUIds {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hnest : ¬ dJ.tgts i' j l < dJ.k)
    (hrec : (dJ.ksF i' j).getD l .ordinary = .recursive)
    (hkA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.recursive)
    {ci : ContainerInfo} {J : ContainerMember}
    (hci : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (hJmem : J ∈ ci.members) (hJn : J.name = (pinsS.getD (q₀ + i') default).J)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ) (ψ : Name → Nat) :
    ∃ (ci' : ContainerInfo) (qq q₀₂ kJ₂ i₂ : Nat),
      ConLeche.containerInfo? env (dJ.pinAt (dJ.tgts i' j l - dJ.k)).J = some ci' ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + qq ∧
      qq = q₀₂ + i₂ ∧ i₂ < kJ₂ ∧ (st.pins.getD qq default).grpBase = q₀₂ ∧
      (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).u (p.k + qq)
        = (blockOf mp.base2 ci').uM i₂
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).ψJ
              ((pinsS.getD (q₀ + i') default).ψJ ψ)) ∧
      (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).Ids (p.k + qq)
        = (blockOf mp.base2 ci').IdsM i₂
            ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).ψJ
              ((pinsS.getD (q₀ + i') default).ψJ ψ)) := by
  classical
  obtain ⟨ci', qn, qq, hci', hnPeq, hqq, hidx, hhead, hargsLen, hJQ, hclvls, hDsE, hlps, hDsQ,
    ⟨cvQ, capsQ, hfindQ, hagree⟩, -⟩ :=
    copyPinFCorr R SF S hPD hi' hj hlF hnest hrec hkA hci hJmem hJn CM ψ
  have hqqLt : qq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
  have hqSq : qq < pinsS.length := by rw [SF.pinsLen]; exact hqqLt
  -- the pin's own group, at the NAMED model of its container
  obtain ⟨q₀₂, kJ₂, i₂, hqqEq, hi₂, S₂⟩ :=
    SF.groupsAt dsR xFvsR qq hqSq ci' (by rw [hJQ]; exact hci')
  -- the group's record at the pin, and its container's constant
  obtain ⟨cvQ', capsQ', cvR₂, mI₂, rP₂, rules₂, hfindQ'₀, hI₂, -⟩ := S₂.stored i₂ hi₂
  have hfindQ' : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD (q₀₂ + i₂) default).J = some (.indInfo cvQ' capsQ') := hfindQ'₀
  rw [← hqqEq] at hfindQ'
  have hcvQ : cvQ' = cvQ := by
    have hfq : (ConLeche.consMutualFormers (fms.take p.k) env).find?
        (pinsS.getD qq default).J = some (.indInfo cvQ capsQ) := by
      rw [hJQ]; exact hfindQ
    have h := hfindQ'.symm.trans hfq
    simp only [Option.some.injEq, ConLeche.ConstantInfo.indInfo.injEq] at h
    exact h.1
  subst hcvQ
  -- the group's index data at the pin, spelled at `pinsS`
  have hpinU : (pinsS.getD qq default).u ψ
      = (blockOf mp.base2 ci').uM i₂ ((pinsS.getD qq default).ψJ ψ) := by
    have h := S₂.pinU i₂ hi₂ ψ i₂ hi₂
    rw [← hqqEq] at h
    exact h
  have hpinPps : (pinsS.getD qq default).pps = (blockOf mp.base2 ci').ppsM i₂ := by
    have h := S₂.pinPps i₂ hi₂
    rw [← hqqEq] at h
    exact h
  have hpinNP : (pinsS.getD qq default).nPJ = (blockOf mp.base2 ci').nP := by
    have h := S₂.pinNP i₂ hi₂
    rw [← hqqEq] at h
    exact h
  -- the two assignments agree AT the container's own level parameters
  have hi₂k : i₂ < (blockOf mp.base2 ci').k := by rw [S₂.kEq]; exact hi₂
  have huC := hI₂.uParams i₂ hi₂k ((pinsS.getD qq default).ψJ ψ)
    ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).ψJ ((pinsS.getD (q₀ + i') default).ψJ ψ)) hagree
  have hppsC := (hI₂.former.params ((pinsS.getD qq default).ψJ ψ)
    ((dJ.pinAt (dJ.tgts i' j l - dJ.k)).ψJ ((pinsS.getD (q₀ + i') default).ψJ ψ)) hagree).1
  refine ⟨ci', qq, q₀₂, kJ₂, i₂, hci', hidx, hqqEq, hi₂, ?_, ?_, ?_⟩
  · have h := (S₂.grp i₂ hi₂).1
    rw [← hqqEq] at h
    exact h
  · -- the index UNIVERSE
    show nestedU p.k W pinsS ψ (p.k + qq) = _
    rw [nestedU_pin, hpinU, huC]
  · -- the index TELESCOPE
    show (if p.k + qq < p.k then blockIds b.nP ppsF ψ (p.k + qq)
      else (pinsS.getD (p.k + qq - p.k) default).Ids ψ) = _
    rw [if_neg (by omega), show p.k + qq - p.k = qq from by omega]
    show (((pinsS.getD qq default).pps ((pinsS.getD qq default).ψJ ψ)).drop
      (pinsS.getD qq default).nPJ).map (·.2.2) = _
    rw [hpinPps, hpinNP, hppsC]
    rfl

/-- **`PinCorr`'s `u` AND `Ids` CLAUSES AT A PIN TARGET** (task #315
PINF): `copyPinFUIds` lands the block pin's index data on the CONTAINER
GROUP's block model at the named family `blockOf mp.base2`, which is one
step short of `PinCorr` — the clauses ask for the CONTAINER'S OWN PIN's
data.  `NestedPinGroupSyn.pinOwn` is that step, and it is the whole of
what the two records' identification costs: both sides read one family
at one container record, so the comparison needs no equality of choices.

The hypotheses are `copyPinFCorr`'s own — the target pin's name and the
two assignments' POINTWISE agreement on the container's own level
parameters — so this consumes nothing the arm does not already have. -/
theorem copyPinFUIdsCorr {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hnest : ¬ dJ.tgts i' j l < dJ.k)
    (hrec : (dJ.ksF i' j).getD l .ordinary = .recursive)
    (hkA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.recursive)
    {ci : ContainerInfo} {J : ContainerMember}
    (hci : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (hJmem : J ∈ ci.members) (hJn : J.name = (pinsS.getD (q₀ + i') default).J)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ) (ψ : Name → Nat) :
    ∃ qq : Nat,
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + qq ∧
      (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).u (p.k + qq)
        = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).u ((pinsS.getD (q₀ + i') default).ψJ ψ) ∧
      (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).Ids (p.k + qq)
        = (dJ.pinAt (dJ.tgts i' j l - dJ.k)).Ids ((pinsS.getD (q₀ + i') default).ψJ ψ) := by
  classical
  obtain ⟨ci', qn, qq, hci', hnPeq, hqq, hidx, hhead, hargsLen, hJQ, hclvls, hDsE, hlps, hDsQ,
    ⟨cvQ, capsQ, hfindQ, hagree⟩, -⟩ :=
    copyPinFCorr R SF S hPD hi' hj hlF hnest hrec hkA hci hJmem hJn CM ψ
  have hqqLt : qq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
  have hqSq : qq < pinsS.length := by rw [SF.pinsLen]; exact hqqLt
  -- the container's own pin index is in range
  have hqlt : dJ.tgts i' j l - dJ.k < dJ.nPins := by
    obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
    have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
    have := hI.tgtsLt i' j l hI.memberLt hjlt (by rw [hCD.ksLen]; exact hlF)
    omega
  have hown := S.pinOwn _ hqlt qq hqSq hJQ cvQ capsQ hfindQ ψ _ hagree
  refine ⟨qq, hidx, ?_, ?_⟩
  · show nestedU p.k W pinsS ψ (p.k + qq) = _
    rw [nestedU_pin]
    exact hown.1
  · show (if p.k + qq < p.k then blockIds b.nP ppsF ψ (p.k + qq)
      else (pinsS.getD (p.k + qq - p.k) default).Ids ψ) = _
    rw [if_neg (by omega), show p.k + qq - p.k = qq from by omega]
    exact hown.2

/-- **THE `pinF` ARM'S FIRST THREE CONJUNCTS** (task #315 PINF): at a
container field that is FINITARY RECURSIVE at one of the container's
own pins, the copy's corresponding field is recursive-or-reflexive
(conjunct 1), its target is a PIN of the block (conjunct 2), and the
pin it lands on CORRESPONDS to the container's (conjunct 3,
`PinCorr`).

The three come from three places and this is the joint: K.60's
inversion `copyPinFKind` gives conjuncts 1 and 2 together with
`copyPinFCorr`'s own `hkA` — the hypothesis that used to have no
producer — `copyPinFCorr` gives `PinCorr`'s `EA`, `Ds`, `J` and `lvls`
clauses off the fire, and `copyPinFUIdsCorr` gives its `u` and `Ids`
through `NestedPinGroupSyn.pinOwn`.

What `NestedPinsShapePinF` still wants beyond this is its telescope and
index-expression conjuncts — the pin-target twins of
`copyRecFRead`/`copyRecFReadRefl` — and the REFLEXIVE arm of all five. -/
theorem NestedPinsRun.copyPinFPinCorr {pbs : List (Expr × ConLeche.BinderMeta)}
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
    (hpinT : ¬ dJ.tgts i' j l < dJ.k)
    {cvT : ConstantVal} {caps : IndCaps}
    (hfind : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD (q₀ + i') default).J = some (.indInfo cvT caps))
    (ψ : Name → Nat) :
    ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true ∧
    p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 ∧
    PinCorr (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ)
      mp₁'.base2.acval dJ ((pinsS.getD (q₀ + i') default).ψJ ψ)
      ((pinsS.getD (q₀ + i') default).Ds ψ)
      cvT.levelParams (pinsS.getD (q₀ + i') default).lvls
      (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) (dJ.tgts i' j l - dJ.k) := by
  classical
  obtain ⟨hkA, hle⟩ := R.copyPinFKind SF S hPD hkindsRun hi' hgb CM hj hlF hrecC hpinT
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hJcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hksLen : (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).length = cAJ.2 := by
    rw [(R.h.ksJ _ _ hcA).1, hcAnF]
  -- conjunct 1: the copy's field is recursive-or-reflexive
  have hrss : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false
      = true := by
    rw [blkRss_getD hGlt,
      rsOf_getD (show l < (kindsOf (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j))).length from by
        rw [kindsOf, List.length_map, hksLen]; exact hlF),
      kindsOf_getD', decide_eq_true_eq]
    exact Or.inl hkA
  -- conjunct 3: the pin correspondence, off the fire and the own-pin tie
  obtain ⟨ci', qn, qq, hci', hnPeq, hqq, hidx, hhead, hargsLen, hJQ, hclvls, hDsE, hlps, hDsQ,
    ⟨cvQ, capsQ, hfindQ, hagree⟩, hEA⟩ :=
    copyPinFCorr R SF S hPD hi' hj hlF hpinT hrecC hkA hciP hJmem hJname CM ψ
  obtain ⟨qq', hidx', hu, hIds⟩ :=
    copyPinFUIdsCorr R SF S hPD hi' hj hlF hpinT hrecC hkA hciP hJmem hJname CM ψ
  have hqEq : qq' = qq := by omega
  rw [hqEq] at hu hIds
  refine ⟨hrss, by rw [hidx]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hidx]; exact hEA
  · show (pinsS.getD ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k) default).Ds ψ = _
    rw [hidx, show p.k + qq - p.k = qq from by omega]
    exact hDsQ
  · rw [hidx]; exact hu
  · rw [hidx]; exact hIds
  · show (if (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) < p.k then _
      else (pinsS.getD ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k) default).J) = _
    rw [hidx, if_neg (by omega), show p.k + qq - p.k = qq from by omega]
    exact hJQ
  · show (if (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) < p.k then ([] : List Level)
      else (pinsS.getD ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) - p.k) default).lvls) = _
    rw [hidx, if_neg (by omega), show p.k + qq - p.k = qq from by omega, hclvls,
      hlps cvT caps hfind]

/-- **THE AUXILIARY BLOCK'S KIND AT A COPY'S RECURSIVE FIELD** (task
#315 L-B): a container field that is FINITARY RECURSIVE at one of the
container's own members `m` is classified by the auxiliary block's
install as RECURSIVE at the group's copy of that member — the block
member `p.k + q₀ + m`.

`copyRecFDom` gives the rewritten domain (the mimic of the group's pin
at `m`, at the block's parameters); closing the telescope back up
(`closeTelescope_mkPisB_strip`, `abstractTele_getD`,
`abstractRange_params`) and re-opening it (`os_field_domain`) keeps
its constant head, `normCtorValM_domHead` carries that head across the
positivity normalisation, `os_field_domain_head` brings it back to the
CLOSED stored domain the classification reads, and
`mutualCtorKinds_memberHead` answers `.recursive` at the member table's
index for the copy's own name (`members3_find?_name` over
`PinsAligned`, which names the copy after its pin's auxiliary). -/
theorem NestedPinsRun.copyRecFKind {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hmem : dJ.tgts i' j l < dJ.k)
    (hrec : (dJ.ksF i' j).getD l .ordinary = .recursive) :
    (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)
      = (.recursive, p.k + (q₀ + dJ.tgts i' j l)) := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    -, -, ⟨cI, fcs', hinstCI, hstripCI, -⟩, hcb, hcA, hnF, hbc⟩ := R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  obtain ⟨st₁, st₂, hrun, hpre, hmint⟩ := hfields l hlcc
  obtain ⟨-, -, hFl⟩ := R.copyRecFDom SF S hPD hi' hgb hgs CM hj hciP hJmem hJcc hJname hty hnf
    hstripJ hpl hfl hDsnP hDsB hlcc hmem hrec hrun hpre hmint
  -- the group's target pin, and the block former it minted
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  have hmkJ : dJ.tgts i' j l < kJ := by rw [← S.kEq]; exact hmem
  have hplen : q₀ + dJ.tgts i' j l < st.pins.length := by
    obtain ⟨-, -, h3⟩ := PD.seg
    rw [hgb, hgs] at h3; omega
  obtain ⟨fM, nIdxM, hfM, -, hauxFind, hfind3, hauxMem, -⟩ := R.groupCopyFormer hPD hplen
  -- the copy's stored constructor, and the normalisation it came from
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  obtain ⟨-, sorts, -, hCtor⟩ := R.h.runC _ _ hcA
  obtain ⟨hnorm, -, hbndC⟩ := ConLeche.checkMutualCtor_true_norm hCtor
  have hcvC : (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).cv
      = ⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩ := by
    rw [List.getD_eq_getElem?_getD, hbc]; rfl
  rw [hcvC] at hnorm hbndC
  rw [hnF] at hnorm hopX'
  -- the GIVEN type's two-stage opening (the rewrite's output, closed and re-opened)
  obtain ⟨fvsA, -, -, hlawA⟩ := ConLeche.openPisAtFvars_mkPisB b.nP pbs₀ hpbs₀len 0
  have hfvsA : fvsA = params := by
    have hlaw := hlawA o'
    rw [← ConLeche.stripPis_mkPisB _ hstripF] at hlaw
    exact (Prod.mk.inj (Option.some.inj (hlaw.symm.trans hopb))).1
  have hop1 : ConLeche.openPisAtFvars b.nP (closeTelescope pbs₀ 0 cbody') 0
      = some (params, cbody') := by
    rw [ConLeche.closeTelescope_eq_mkPisB pbs₀ 0 cbody' hpbs₀f, hpbs₀len, hlawA, hfvsA,
      ConLeche.instSeq_abstractRange_fvs b.nP params cbody' hcbb hplenB hidxP hcbl]
  obtain ⟨xfvs, hxflen, -, hlawX⟩ := ConLeche.openPisAtFvars_mkPisB cc.nFields Fs' hlenF b.nP
  obtain ⟨resB, hcb'⟩ : ∃ r, cbody'.stripPis cc.nFields = some (Fs', r) := ⟨_, hcb⟩
  have hcbodyEq := ConLeche.stripPis_mkPisB _ hcb'
  have hop2 : ConLeche.openPisAtFvars cc.nFields cbody' b.nP
      = some (xfvs, Expr.instSeq xfvs (cc.nFields - 1) resB) := by
    rw [hcbodyEq]; exact hlawX resB
  obtain ⟨x, hx⟩ : ∃ x, xfvs[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxflen]; exact hlcc)⟩
  -- the opened domain at `l`: the closed telescope's entry, instantiated
  have hstripC : (closeTelescope pbs₀ 0 cbody').stripPis (b.nP + cc.nFields)
      = some (pbs₀ ++ ConLeche.abstractTele 0 pbs₀.length 0 Fs',
          resB.abstractRange 0 pbs₀.length Fs'.length) := by
    rw [hcbodyEq]
    rw [show b.nP + cc.nFields = pbs₀.length + Fs'.length from by rw [hpbs₀len, hlenF]]
    exact ConLeche.closeTelescope_mkPisB_strip hpbs₀f
  have habs : (ConLeche.abstractTele 0 pbs₀.length 0 Fs')[l]?
      = some ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show l < (ConLeche.abstractTele 0 pbs₀.length 0 Fs').length from by
        rw [ConLeche.abstractTele_length, hlenF]; exact hlcc)]
    rfl
  have hxdom : x.fvarTypeD = Expr.instSeq (params ++ xfvs.take l) (b.nP + l - 1)
      ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default).1 :=
    ConLeche.os_field_domain b.nP cc.nFields l
      (openPisAtFvars_add b.nP hop1 (by rw [Nat.zero_add]; exact hop2))
      hstripC hplenB hpbs₀len hx habs
  have hxhead : x.fvarTypeD.getAppFn
      = Expr.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param) := by
    rw [hxdom]
    refine os_instSeq_head ?_ _ _
    rw [ConLeche.abstractTele_getD 0 pbs₀.length Fs' 0 l (by rw [hlenF]; exact hlcc), hFl]
    simp only [ConLeche.abstractRange_mkAppN, ConLeche.abstractRange_const,
      Expr.getAppFn_mkAppN, Expr.getAppFn]
  -- the normalisation keeps that head, and the STORED opened domain has it too
  obtain ⟨x', hx'⟩ : ∃ x', (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnF]; exact hlcc)⟩
  obtain ⟨args', hx'head⟩ := ConLeche.normCtorValM_domHead mp₁.base2.wf hnorm hbndC hop1 hop2
    hopP' hopX' hx hx' hauxFind (by rw [← Expr.mkAppN_getApp x.fvarTypeD, hxhead])
  -- the CLOSED stored domain the classification reads
  obtain ⟨cbsA, esA, hstripA, -⟩ := hCD.resid
  rw [hnF] at hstripA
  have hcbsAlen : cbsA.length = b.nP + cc.nFields := Expr.stripPis_length _ hstripA
  have htakeLen : (cbsA.take b.nP).length = b.nP := by
    rw [List.length_take, hcbsAlen]; omega
  obtain ⟨resA, hstripAx⟩ : ∃ r, cA.1.type.stripPis (b.nP + cc.nFields) = some (cbsA, r) :=
    ⟨_, hstripA⟩
  have hstripA' : cA.1.type.stripPis (b.nP + cc.nFields)
      = some (cbsA.take b.nP ++ cbsA.drop b.nP, resA) := by
    rw [List.take_append_drop]; exact hstripAx
  have hdropA : (cbsA.drop b.nP)[l]? = some ((cbsA.drop b.nP).getD l default) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show l < (cbsA.drop b.nP).length from by
        rw [List.length_drop, hcbsAlen]; omega)]
    rfl
  have hclHead : ((cbsA.drop b.nP).getD l default).1.getAppFn
      = Expr.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param) :=
    ConLeche.os_field_domain_head b.nP cc.nFields l
      (openPisAtFvars_add b.nP hopP' (by rw [Nat.zero_add]; exact hopX'))
      hstripA' hCD.pLen htakeLen hx' hdropA (by rw [hx'head]; simp [Expr.getAppFn_mkAppN,
        Expr.getAppFn])
  have hdomA : (cbsA.getD (b.nP + l) default).1
      = Expr.mkAppN (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
          (cbsA.getD (b.nP + l) default).1.getAppArgs := by
    rw [← hclHead, ← getD_dropD, Expr.mkAppN_getApp]
  -- the classification at that field
  obtain ⟨hmapM, hnegAll, hunsAll, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hksNeg : ksG.any (·.1 == .negative) = false := by
    rcases hb0 : ksG.any (·.1 == .negative) with _ | _
    · rfl
    · exact absurd (List.any_eq_true.mpr ⟨ksG, List.mem_of_getElem? hksG, hb0⟩)
        (by rw [hnegAll]; simp)
  have hksUns : ksG.any (·.1 == .unsupported) = false := by
    rcases hb0 : ksG.any (·.1 == .unsupported) with _ | _
    · rfl
    · exact absurd (List.any_eq_true.mpr ⟨ksG, List.mem_of_getElem? hksG, hb0⟩)
        (by rw [hunsAll]; simp)
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hstripA2 : cA.1.type.stripPis (b.nP + cA.2) = some (cbsA, resA) := by
    rw [hnF]; exact hstripAx
  have hkindEntry := mutualCtorKinds_memberHead hmk hksNeg hksUns hstripA2 hlA hdomA
    hauxMem hfind3
  rw [hmutKs]
  exact hkindEntry

/-- **`CopyCtorShape.recF`'s first two conjuncts** (task #315 L-B): the
kind table's entry (`copyRecFKind`) read back through the block's own
accessors — the copy's field `l` is recursive, at the block member
`p.k + q₀ + m`. -/
theorem NestedPinsRun.copyRecF {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hmem : dJ.tgts i' j l < dJ.k)
    (hrec : (dJ.ksF i' j).getD l .ordinary = .recursive) :
    ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + q₀ + dJ.tgts i' j l := by
  classical
  obtain ⟨cc, -, -, -, -, -, -, -, -, -, -, -, cA, -, -, -,
    -, -, -, -, -, hnf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hcA, hnF, -⟩ := R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hkindEntry := R.copyRecFKind SF S hPD hkindsRun hi' hgb hgs CM hj hlF hmem hrec
  have hlks : l < (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).length := by
    obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
    rw [hksLen]; exact hlA
  refine ⟨?_, ?_⟩
  · rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map]; exact hlks),
      decide_eq_true_eq, kindsOf_getD']
    left
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).1 = _
    rw [hkindEntry]
  · rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]; exact hlA)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = _
    rw [hkindEntry]
    show p.k + (q₀ + dJ.tgts i' j l) = _
    omega

/-! ## The arm's READINGS at a finitary recursive field (task #315 L-B)

`copyRecFKind` says WHAT the auxiliary block made of the copy's field;
`CopyCtorShape.recF`'s last two conjuncts say what its DATA are — the
copy's reflexive telescope and its index expressions.  At a finitary
recursive field the telescope is empty on both sides, and the index
expressions are the container's instantiated at the pin's components:

* the MINTED constructor's `l`-th opened field domain reads as the
  container's instantiated (`mintFieldRead`), and syntactically it is
  the targeted member applied to the components and to the field's own
  index arguments (`copyRecFDom`'s first conjunct) — so its index
  arguments READ as the container's index readings instantiated;
* the copy's STORED domain is the elimination's rewrite of that very
  domain, up to the openers' annotations: the rewrite replaces the
  member head by the group's mimic and leaves the index arguments
  alone (`copyRecFDom`), the open/close round trip at the field's own
  cut is exact (`instSeq_abstractRange_fvs_at`), and the positivity
  normalisation is the identity on the mimic's application
  (`normCtorValM_domErased`);
* so the two index spines are pointwise erasure-equal, and a read
  spine transports along that (`DenoteMetaSpine.erasedEq`, `.unique`). -/

/-- **`CopyCtorShape.recF`'s telescope and index-expression conjuncts**
at a FINITARY recursive field (task #315 L-B): the copy's reflexive
telescope is the container's instantiated (both empty), and the copy's
index expressions are the container's instantiated at the pin's
components at the field's own depth. -/
theorem NestedPinsRun.copyRecFRead {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hmem : dJ.tgts i' j l < dJ.k)
    (hrec : (dJ.ksF i' j).getD l .ordinary = .recursive)
    (ψ : Name → Nat) :
    (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).map
        (·.2.2)
      = instTele ((pinsS.getD (q₀ + i') default).Ds ψ) l
          ((((dJ.tlss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l []).map
            (·.2.2)) ∧
    ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
      = (((dJ.Eiss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l []).map
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ)
            (l + (((dJ.tlss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l
              []).length)) := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    -, -, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ := R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  obtain ⟨st₁, st₂, hrun, hpre, hmint⟩ := hfields l hlcc
  obtain ⟨hshape, hcLen, hFl⟩ := R.copyRecFDom SF S hPD hi' hgb hgs CM hj hciP hJmem hJcc hJname
    hty hnf hstripJ hpl hfl hDsnP hDsB hlcc hmem hrec hrun hpre hmint
  -- the container's constructor data, and the copy's
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCDJ⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hnest : dJ.nestOf i' j l = none := dJ.nestOf_none hmem
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hkindEntry := R.copyRecFKind SF S hPD hkindsRun hi' hgb hgs CM hj hlF hmem hrec
  have hkindA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l
      = RecFieldKind.recursive := by
    show ((mutKsOf kinds _).getD l (.ordinary, 0)).1 = _
    rw [hkindEntry]
  have htlsJ : ((dJ.tlss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l [] = [] := by
    rw [IsBlockModel.tlss_getD hj,
      hCDJ.tssNone _ l (by rw [hrec]; exact fun h => nomatch h)]
  refine ⟨?_, ?_⟩
  · rw [mutTlss_getD hGlt, hCD.tssNone ψ l (by rw [hkindA]; exact fun h => nomatch h), htlsJ]
    rfl
  rw [htlsJ, List.length_nil, Nat.add_zero, mutEiss0_getD hGlt, IsBlockModel.Eiss_getD hj]
  -- the pin's components: scoped at the block's parameters, and read
  have hqst : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have hq : q₀ + i' < pinsS.length := by have := S.seg; omega
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hDsE : (pinsS.getD (q₀ + i') default).DsE = (srcAtE st p (q₀ + i')).2.2 := by
    have hA := congrArg Expr.getAppArgs hpin
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at hA
    exact hA
  have hspine := SF.pinDs _ hq ψ
  rw [hDsE] at hspine
  obtain ⟨-, hcl₀, hbt₀, hFD₀⟩ := R.former0
  obtain ⟨-, fvsS, oS, hopS, hsc⟩ := R.scoped
  obtain ⟨hbnd, hleaf⟩ := hsc _ (List.mem_of_getElem? PD.pin)
  have hws := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hopS hleaf ψ
  rw [PD.pinEq] at hbnd hws
  obtain ⟨-, hwsD⟩ := ConLeche.WScoped_of_mkAppN hws
  obtain ⟨-, hbndD⟩ := ConLeche.looseBVarsBounded_of_mkAppN hbnd
  have hDsSc : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2,
      Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true :=
    fun a ha => ⟨hwsD a ha, hbndD a ha⟩
  -- (1) THE MINTED SIDE: the `l`-th field domain, opened
  obtain ⟨resM, hstripCI'⟩ : ∃ r, cI.stripPis cc.nFields = some (fcs', r) := ⟨_, hstripCI⟩
  have hfcs'len : fcs'.length = cc.nFields := Expr.stripPis_length _ hstripCI'
  obtain ⟨xfvs', hxf'len, -, hlawX'⟩ :=
    ConLeche.openPisAtFvars_mkPisB cc.nFields fcs' hfcs'len b.nP
  have hopM : ConLeche.openPisAtFvars cc.nFields cI b.nP
      = some (xfvs', Expr.instSeq xfvs' (cc.nFields - 1) resM) := by
    rw [ConLeche.stripPis_mkPisB _ hstripCI']; exact hlawX' _
  obtain ⟨xI, hxI⟩ : ∃ x, xfvs'[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxf'len]; exact hlcc)⟩
  have hfcsl' : fcs'[l]? = some (fcs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hfcs'len]; exact hlcc)]
    rfl
  have hxIdom : xI.fvarTypeD = Expr.instSeq (xfvs'.take l) (l - 1) (fcs'.getD l default).1 :=
    Verify.openPisAtFvars_domain cc.nFields hopM hstripCI' l xI (fcs'.getD l default) hxI hfcsl'
  have hmfr := mintFieldRead S hi' hj hksJ (by rw [hty]; exact hccf) (by rw [hty]; exact hccb)
    hDsSc ψ hspine (by rw [hty]; exact hinstCI) (by rw [hnf]; exact hopM) hlF hxI
  rw [hCDJ.recEntry _ l hnest hrec hlF, AnnotTerm.instAll_mkAppN, List.map_append] at hmfr
  have hxIshape : xI.fvarTypeD
      = Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
          (pinsS.getD (q₀ + i') default).lvls)
        (((srcAtE st p (q₀ + i')).2.2 ++
            (((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
                (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
              (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).map
          (Expr.instSeq (xfvs'.take l) (l - 1))) := by
    rw [hxIdom, hfcs' l hlcc, hshape, ConLeche.instSeq_mkAppN_const]
  rw [hxIshape, List.map_append] at hmfr
  obtain ⟨fa, vs, -, hspM, heqA⟩ := denoteMeta_mkAppN_inv hmfr
  obtain ⟨vs₁, vs₂, rfl, hspP, hspE⟩ := DenoteMetaSpine.append_inv hspM
  have hlenIDX : ((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
      (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).length
      = dJ.nIdxAt (dJ.tgts i' j l) := by
    rw [List.length_map, List.length_map, List.length_drop, hcLen]
    omega
  have hEisLen : ((dJ.eissF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l []).length
      = dJ.nIdxAt (dJ.tgts i' j l) := hCDJ.eisLen _ l hnest hrec hlF
  have hPBlen : (paramBvarsAt dJ.nP (dJ.nP + l)).length = dJ.nP := by
    simp [paramBvarsAt]
  have hvs₁len : ((paramBvarsAt dJ.nP (dJ.nP + l)).map
      (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l)).length = vs₁.length := by
    rw [List.length_map, hPBlen, ← hspP.length, List.length_map, hDsnP]
  obtain ⟨-, happ⟩ := AnnotTerm.mkAppN_inj heqA (by
    rw [List.length_append, List.length_append, hvs₁len, ← hspE.length, List.length_map,
      List.length_map, hEisLen, hlenIDX])
  obtain ⟨-, rfl⟩ := List.append_inj happ hvs₁len
  -- (2) THE COPY SIDE: the given type's opening, and the stored one
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  obtain ⟨-, sorts, -, hCtor⟩ := R.h.runC _ _ hcA
  obtain ⟨hnorm, -, hbndC⟩ := ConLeche.checkMutualCtor_true_norm hCtor
  have hcvC : (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).cv
      = ⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩ := by
    rw [List.getD_eq_getElem?_getD, hbc]; rfl
  rw [hcvC] at hnorm hbndC
  rw [hnF] at hnorm hopX'
  obtain ⟨fvsA, -, -, hlawA⟩ := ConLeche.openPisAtFvars_mkPisB b.nP pbs₀ hpbs₀len 0
  have hfvsA : fvsA = params := by
    have hlaw := hlawA o'
    rw [← ConLeche.stripPis_mkPisB _ hstripF] at hlaw
    exact (Prod.mk.inj (Option.some.inj (hlaw.symm.trans hopb))).1
  have hop1 : ConLeche.openPisAtFvars b.nP (closeTelescope pbs₀ 0 cbody') 0
      = some (params, cbody') := by
    rw [ConLeche.closeTelescope_eq_mkPisB pbs₀ 0 cbody' hpbs₀f, hpbs₀len, hlawA, hfvsA,
      ConLeche.instSeq_abstractRange_fvs b.nP params cbody' hcbb hplenB hidxP hcbl]
  obtain ⟨xfvs, hxflen, -, hlawX⟩ := ConLeche.openPisAtFvars_mkPisB cc.nFields Fs' hlenF b.nP
  obtain ⟨resB, hcb'⟩ : ∃ r, cbody'.stripPis cc.nFields = some (Fs', r) := ⟨_, hcb⟩
  have hop2 : ConLeche.openPisAtFvars cc.nFields cbody' b.nP
      = some (xfvs, Expr.instSeq xfvs (cc.nFields - 1) resB) := by
    rw [ConLeche.stripPis_mkPisB _ hcb']; exact hlawX resB
  obtain ⟨x, hx⟩ : ∃ x, xfvs[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxflen]; exact hlcc)⟩
  have hstripC : (closeTelescope pbs₀ 0 cbody').stripPis (b.nP + cc.nFields)
      = some (pbs₀ ++ ConLeche.abstractTele 0 pbs₀.length 0 Fs',
          resB.abstractRange 0 pbs₀.length Fs'.length) := by
    rw [ConLeche.stripPis_mkPisB _ hcb']
    rw [show b.nP + cc.nFields = pbs₀.length + Fs'.length from by rw [hpbs₀len, hlenF]]
    exact ConLeche.closeTelescope_mkPisB_strip hpbs₀f
  have habs : (ConLeche.abstractTele 0 pbs₀.length 0 Fs')[l]?
      = some ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show l < (ConLeche.abstractTele 0 pbs₀.length 0 Fs').length from by
        rw [ConLeche.abstractTele_length, hlenF]; exact hlcc)]
    rfl
  have hxdom : x.fvarTypeD = Expr.instSeq (params ++ xfvs.take l) (b.nP + l - 1)
      ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default).1 :=
    ConLeche.os_field_domain b.nP cc.nFields l
      (openPisAtFvars_add b.nP hop1 (by rw [Nat.zero_add]; exact hop2))
      hstripC hplenB hpbs₀len hx habs
  -- the round trip at the field's own cut: the given domain, verbatim
  have hFsl : Fs'[l]? = some (Fs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenF]; exact hlcc)]
    rfl
  have hFlBnd : (Fs'.getD l default).1.looseBVarsBounded l = true := by
    have h := ConLeche.stripPis_binder_bounded cc.nFields hcb' hcbb l _ hFsl
    simpa using h
  have hFlLeaves : ∀ lf ∈ (Fs'.getD l default).1.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ params :=
    fun lf hlf => hcbl lf (ConLeche.stripPis_binder_leaves cc.nFields hcb' l _ hFsl lf hlf)
  have hxdom2 : x.fvarTypeD = Expr.instSeq (xfvs.take l) (l - 1) (Fs'.getD l default).1 := by
    rw [hxdom, ConLeche.abstractTele_getD 0 pbs₀.length Fs' 0 l (by rw [hlenF]; exact hlcc),
      Expr.instSeq_append, hplenB, show b.nP + l - 1 - b.nP = l - 1 from by omega, hpbs₀len]
    simp only [Nat.zero_add]
    rw [ConLeche.instSeq_abstractRange_fvs_at b.nP l params _ hFlBnd hplenB hidxP hFlLeaves]
  -- the given domain is the group's mimic applied
  have hxArgs : x.fvarTypeD.getAppArgs
      = params.map (Expr.instSeq (xfvs.take l) (l - 1))
        ++ ((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).map
          (Expr.instSeq (xfvs.take l) (l - 1)) := by
    rw [hxdom2, hFl, Expr.instSeq_mkAppN, ConLeche.instSeq_mkAppN_const,
      Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN]
    rfl
  have hxHead : x.fvarTypeD.getAppFn
      = Expr.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param) := by
    rw [hxdom2, hFl, Expr.instSeq_mkAppN, ConLeche.instSeq_mkAppN_const]
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn]
  have hxfull : x.fvarTypeD
      = Expr.mkAppN (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
          x.fvarTypeD.getAppArgs := by
    rw [← hxHead, Expr.mkAppN_getApp]
  -- the target pin's copy IS a block member, stored
  have hmkJ : dJ.tgts i' j l < kJ := by rw [← S.kEq]; exact hmem
  have hplen : q₀ + dJ.tgts i' j l < st.pins.length := by
    obtain ⟨-, -, h3⟩ := PD.seg
    rw [hgb, hgs] at h3; omega
  obtain ⟨fM, -, hfM, -, hauxFind, -, -, -⟩ := R.groupCopyFormer hPD hplen
  obtain ⟨x', hx'⟩ : ∃ x', (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnF]; exact hlcc)⟩
  have her := ConLeche.normCtorValM_domErased mp₁.base2.wf hnorm hbndC hop1 hop2 hopP' hopX'
    hx hx' hauxFind hxfull
  obtain ⟨-, hlenArgs, hargsEq⟩ := ConLeche.ErasedEq.getApp her
  rw [hxArgs] at hlenArgs hargsEq
  -- (3) the two index spines meet
  have hplenMap : (params.map (Expr.instSeq (xfvs.take l) (l - 1))).length = b.nP := by
    rw [List.length_map]; exact hplenB
  have hxfEr : ∀ (k : Nat) (a₁ a₂ : Expr), (xfvs'.take l)[k]? = some a₁ →
      (xfvs.take l)[k]? = some a₂ → Expr.ErasedEq a₁ a₂ := by
    intro k a₁ a₂ h1 h2
    have hk1 : xfvs'[k]? = some a₁ := by
      rw [List.getElem?_take] at h1
      split at h1
      · exact h1
      · exact nomatch h1
    have hk2 : xfvs[k]? = some a₂ := by
      rw [List.getElem?_take] at h2
      split at h2
      · exact h2
      · exact nomatch h2
    obtain ⟨ty₁, rfl⟩ := openPisAtFvars_index _ _ _ hopM k a₁ hk1
    obtain ⟨ty₂, rfl⟩ := openPisAtFvars_index _ _ _ hop2 k a₂ hk2
    rfl
  have hxfLen : (xfvs'.take l).length = (xfvs.take l).length := by
    rw [List.length_take, List.length_take, hxf'len, hxflen]
  have hlenPt : (((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
      (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).map
      (Expr.instSeq (xfvs'.take l) (l - 1))).length
      = (x'.fvarTypeD.getAppArgs.drop b.nP).length := by
    rw [List.length_drop, hlenArgs, List.length_append, hplenMap]
    simp only [List.length_map]
    omega
  have hptEq : ∀ k, k < (((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
      (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).map
      (Expr.instSeq (xfvs'.take l) (l - 1))).length →
      Expr.ErasedEq
        ((((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
            (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
          (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).map
          (Expr.instSeq (xfvs'.take l) (l - 1))).getD k default)
        ((x'.fvarTypeD.getAppArgs.drop b.nP).getD k default) := by
    intro k hk
    have hkIDX : k < ((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).length := by
      rw [List.length_map] at hk; exact hk
    have hmapGetD : ∀ (L : List Expr) (g : Expr → Expr) (n : Nat), n < L.length →
        (L.map g).getD n default = g (L.getD n default) := by
      intro L g n hn
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hn,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
      rfl
    have hlt : b.nP + k < x'.fvarTypeD.getAppArgs.length := by
      rw [hlenArgs, List.length_append, hplenMap, List.length_map]
      omega
    have hsplit : (params.map (Expr.instSeq (xfvs.take l) (l - 1))
          ++ ((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
                (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
              (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).map
            (Expr.instSeq (xfvs.take l) (l - 1))).getD (b.nP + k) default
        = (((((fcs.getD l default).1.getAppArgs.drop dJ.nP).map
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l))).map
          (Expr.instSeq (xfvs.take l) (l - 1))).getD k default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hplenMap]; omega),
        hplenMap, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
    rw [getD_dropD]
    refine Expr.ErasedEq.trans ?_ (Expr.ErasedEq.symm (hargsEq (b.nP + k) hlt))
    rw [hsplit, hmapGetD _ _ k hkIDX, hmapGetD _ _ k hkIDX]
    exact Expr.instSeq_erasedEq_args (xfvs'.take l) (xfvs.take l) (l - 1)
      (Expr.ErasedEq.rfl _) hxfEr hxfLen
  exact DenoteMetaSpine.unique (hCD.eisRead ψ l x' hx' hkindA)
    (DenoteMetaSpine.erasedEq (R.crossUpSpine ψ (b.nP + l) hspE) hlenPt hptEq)

/-! ## The reflexive field (task #315 L-B, DESIGN §U.53 (d))

`copyRecFDom` is stated at a FINITARY recursive field.  A REFLEXIVE
one differs in exactly one place: the member application sits under the
field's own `Π` binders.  Everything the finitary chain does happens
under them — the uniformity walk carried through the peel
(`nestedContainersOk_memberSpineRefl`), the level substitution and the
components at the deeper cut `l + d`, and `replaceAllNested`'s descent
into a `∀`-telescope (`replaceAllNested_mkPisB`) — and the TELESCOPE
itself is left alone: at a field the positivity walk accepted, every
binder domain of the REWRITTEN tower mentions no member
(`normPosDomM_piDomsFree`), so the rewrite's own prune
(`replaceAllNested_unchanged_or_aux` against `groupCopyFormer`) says it
was the identity there. -/

omit [SetTheory V] R SF S in
/-- A `∀`-telescope over an application spine peels exactly its own
binders (`rk_piBinders_mkPisB_length` with the body). -/
private theorem piBinders_mkPisB_of_head :
    ∀ (bs : List (Expr × ConLeche.BinderMeta)) {res : Expr} {c : Name} {us : List Level},
      res.getAppFn = Expr.const c us → (ConLeche.mkPisB bs res).piBinders = (bs, res)
  | [], res, c, us, h => by
    show res.piBinders = ([], res)
    have h1 : (res.piBinders).1 = [] := Expr.piBinders_nil_of_getAppFn_const h
    have h2 : (res.piBinders).2 = res := Expr.piBinders_nil_body h1
    exact Prod.ext h1 h2
  | b :: bs, res, c, us, h => by
    show (Expr.forallE b.1 (ConLeche.mkPisB bs res) b.2).piBinders = _
    rw [Expr.piBinders_forallE, piBinders_mkPisB_of_head bs h]

omit [SetTheory V] R SF S in
/-- Two binder lists of equal length agreeing at every position are
equal. -/
private theorem tele_ext {L L' : List (Expr × ConLeche.BinderMeta)}
    (hlen : L'.length = L.length)
    (h : ∀ k, k < L.length →
      (L'.getD k default).1 = (L.getD k default).1 ∧
        (L'.getD k default).2 = (L.getD k default).2) :
    L' = L := by
  refine List.ext_getElem hlen fun k hk hk' => ?_
  obtain ⟨h1, h2⟩ := h k hk'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at h1 h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some] at h1 h2
  exact Prod.ext h1 h2

/-- **THE COPY'S REFLEXIVE FIELD, REWRITTEN** (task #315 L-B): at a
container field `l` of member `i'` constructor `j` that is REFLEXIVE at
one of the container's own members, the container's closed domain is a
`Π`-telescope over that member applied to the block's parameters (at
the telescope's own depth) and to the field's index arguments; the
elimination's rewrite leaves the telescope alone and turns the body
into the MIMIC of the group's pin at the target, applied to the
block's parameter openers and to those index arguments,
level-substituted and instantiated at the pin's components at the
telescope's cut.  `copyRecFDom` under the field's own binders. -/
theorem NestedPinsRun.copyRecFDomRefl {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {ci : ContainerInfo} {J : ContainerMember} {cc : ContainerCtor}
    (hciP : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (hJmem : J ∈ ci.members) (hJcc : J.ctors[j]? = some cc)
    (hJname : J.name = (pinsS.getD (q₀ + i') default).J)
    (hty : cAJ.1.type = cc.type) (hnf : cAJ.2 = cc.nFields)
    {pcs fcs : List (Expr × ConLeche.BinderMeta)} {residJ : Expr}
    (hstripJ : cc.type.stripPis (dJ.nP + cc.nFields) = some (pcs ++ fcs, residJ))
    (hpl : pcs.length = dJ.nP) (hfl : fcs.length = cc.nFields)
    (hDsnP : (srcAtE st p (q₀ + i')).2.2.length = dJ.nP)
    (hDsB : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2, a.looseBVarsBounded 0 = true)
    {params : List Expr} {pbs₀ : List (Expr × ConLeche.BinderMeta)}
    {l : Nat} (hlF : l < cc.nFields)
    (hmem : dJ.tgts i' j l < dJ.k)
    (hrefl : (dJ.ksF i' j).getD l .ordinary = .reflexive)
    {Fl : Expr} {st₁ st₂ : ElimState}
    (hrun : ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st₁
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
            (fcs.getD l default).1))
      = .ok (Fl, st₂))
    (hpre : st₂.pins <+: st.pins)
    (hmint : ((srcAtE st p (q₀ + i')).2.2.any fun a =>
      st₁.newNames.any fun T => a.mentionsConst T) = true)
    (hfree : ∀ k, k < ((Fl.piBinders).1).length →
      ConLeche.mentionsMember b.memberNames (((Fl.piBinders).1).getD k default).1 = false) :
    ∃ (tbs TL : List (Expr × ConLeche.BinderMeta)) (idxs IDXS : List Expr),
      (fcs.getD l default).1.stripPis tbs.length
          = some (tbs, Expr.mkAppN
              (.const (dJ.memberName (dJ.tgts i' j l)) (J.lps.map Level.param))
              (ConLeche.structPsAt (l + tbs.length) dJ.nP ++ idxs)) ∧
      tbs.length ≠ 0 ∧
      idxs.length = dJ.nIdxAt (dJ.tgts i' j l) ∧
      (∀ ψJ : Name → Nat, (((dJ.tlss i' ψJ).getD j []).getD l []).length = tbs.length) ∧
      IDXS = (idxs.map (Expr.instantiateLevelParams J.lps
            (pinsS.getD (q₀ + i') default).lvls)).map
          (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length)) ∧
      (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
            (fcs.getD l default).1)).stripPis tbs.length
        = some (TL, Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
            (pinsS.getD (q₀ + i') default).lvls) ((srcAtE st p (q₀ + i')).2.2 ++ IDXS)) ∧
      Fl.stripPis tbs.length
        = some (TL, Expr.mkAppN (Expr.mkAppN
            (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param)) params) IDXS) := by
  classical
  -- the frame, as in `copyRecFDom`
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  have CMci : ContainerModeled mp₁'.base2 ci dJ := CM ci hciP
  have hnPci : ci.nP = dJ.nP := CMci.nP.symm
  have hpinMem : pinAtE st (q₀ + i') ∈ st.pins := List.mem_of_getElem? PD.pin
  obtain ⟨hJc, hpinEq⟩ := SF.pinRec _ _ PD.pin
  have hciC : ConLeche.containerInfo? env (pinAtE st (q₀ + i')).container = some ci := by
    rw [← hJc]; exact hciP
  have hlv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have hfn := congrArg Expr.getAppFn (hpinEq.symm.trans PD.pinEq)
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at hfn
    exact (ConLeche.Expr.const.inj hfn).2
  obtain ⟨ciP, hciPown, -, -, -, hnamesP, J', hJ'find, hJ'n, cCopy, hmk, -, -⟩ := PD.own
  have hciEq : ciP = ci := Option.some.inj (hciPown.symm.trans hciC)
  have hJ'mem : J' ∈ ci.members := by
    rw [← hciEq]; exact List.mem_of_find?_eq_some hJ'find
  rw [hciEq] at hnamesP
  obtain rfl : J = J' :=
    ConLeche.containerInfo?_member_det hciP hciP rfl hJmem hJ'mem (by rw [hJname, hJc, hJ'n])
  obtain ⟨cvT, capsT, cvR, mI, rP, rules, hfindT, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hnest : dJ.nestOf i' j l = none := dJ.nestOf_none hmem
  obtain ⟨cvT₀, caps₀, cvR₀, mI₀, rP₀, rules₀, hfT₀, -, -, -, hallM⟩ :=
    ConLeche.containerInfo?_inv hciP
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, -, -, hlpsJ, -, hlpsEq, -, -⟩ := hallM _ hJmem
  have hlpsJEq : J.lps = cvT.levelParams := by
    obtain ⟨hFc, -, -, -⟩ := R.cross
    have h₁ := hFc _ (.indInfo cvT₀ caps₀) (fun _ _ _ _ h => nomatch h) hfT₀
    obtain rfl : cvT₀ = cvT :=
      (ConstantInfo.indInfo.inj (Option.some.inj (h₁.symm.trans hfindT))).1
    rw [hlpsJ, hlpsEq]
  -- the components: non-empty, and as many as the member's level parameters
  have hDsNe : 0 < (srcAtE st p (q₀ + i')).2.2.length := by
    rcases hDsE : (srcAtE st p (q₀ + i')).2.2 with _ | ⟨d, ds⟩
    · rw [hDsE] at hmint; simp at hmint
    · simp
  have hLvlLen : J.lps.length = (pinsS.getD (q₀ + i') default).lvls.length := by
    obtain ⟨hlen, -, -, -, -, -⟩ := ConLeche.mkCopy_inv hmk
    rw [hlv]; exact hlen.symm
  obtain ⟨hNodupJ, -⟩ := ConLeche.nestedContainersOk_uniform R.hcont hpinMem hciC hJmem
  -- the field's opener and the container's OPENED domain
  obtain ⟨x, hx⟩ : ∃ x, (dJ.xFvsF i' j)[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnf]; exact hlF)⟩
  obtain ⟨afvs, bodyO, hopA, hafne, -, hheadO, htakeO, hlenO, -, -⟩ :=
    hCD.opened.reflF l x hx hnest hrefl
  have hfcsl : fcs[l]? = some (fcs.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hfl]; exact hlF)]; rfl
  have hstripA : cAJ.1.type.stripPis (dJ.nP + cAJ.2) = some (pcs ++ fcs, residJ) := by
    rw [hty, hnf]; exact hstripJ
  have hopen : x.fvarTypeD
      = Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1)
        (fcs.getD l default).1 :=
    blockCtorFieldDomain hCD hstripA hpl hx hfcsl
  -- the openers are free variables, and there are few enough of them
  have hfv : ∀ a ∈ (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l),
      ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨k, hk⟩ := List.getElem?_of_mem h
      obtain ⟨ty, hty2⟩ := hCD.pIdx k a hk
      exact ⟨k, ty, hty2⟩
    · obtain ⟨k, hk⟩ := List.getElem?_of_mem (List.take_subset _ _ h)
      obtain ⟨ty, hty2⟩ := hCD.xIdx k a hk
      exact ⟨dJ.nP + k, ty, hty2⟩
  have hlenLe : (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l).length ≤ dJ.nP + l - 1 + 1 := by
    rw [List.length_append, hCD.pLen, List.length_take]; omega
  -- the container's closed field domain, peeled at its own binders
  obtain ⟨tbs, cbody, hpb⟩ :
      ∃ tbs cbody, ((fcs.getD l default).1.piBinders) = (tbs, cbody) := ⟨_, _, rfl⟩
  obtain ⟨hpbLen, hpbBody⟩ :=
    Expr.piBinders_instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1)
      (fcs.getD l default).1 hfv hlenLe
  rw [hpb] at hpbLen hpbBody
  have hFclPis : (fcs.getD l default).1.stripPis tbs.length = some (tbs, cbody) := by
    have h := Expr.stripPis_piBinders (fcs.getD l default).1
    rw [hpb] at h; exact h
  have hFclMk : (fcs.getD l default).1 = ConLeche.mkPisB tbs cbody :=
    ConLeche.stripPis_mkPisB _ hFclPis
  -- the OPENED domain is that telescope instantiated
  have hxMk : x.fvarTypeD
      = ConLeche.mkPisB
          (ConLeche.instTeleSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) tbs)
          (Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l)
            (dJ.nP + l - 1 + tbs.length) cbody) := by
    rw [hopen, hFclMk, ConLeche.instSeq_mkPisB _ _ _ _ hlenLe]
  obtain ⟨fvs2, hfvs2len, -, hlaw2⟩ :=
    ConLeche.openPisAtFvars_mkPisB tbs.length
      (ConLeche.instTeleSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l) (dJ.nP + l - 1) tbs)
      (ConLeche.instTeleSeq_length _ _ _) (dJ.nP + l)
  have hopen2 : ConLeche.openPisAtFvars tbs.length x.fvarTypeD (dJ.nP + l)
      = some (fvs2, Expr.instSeq fvs2 (tbs.length - 1)
          (Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l)
            (dJ.nP + l - 1 + tbs.length) cbody)) := by
    rw [hxMk]; exact hlaw2 _
  rw [hopen, hpbLen, ← hopen] at hopA
  obtain ⟨hafvsEq, hbodyO⟩ := Prod.mk.inj (Option.some.inj (hopA.symm.trans hopen2))
  -- the body's head and spine, reflected through the two instantiations
  have hfv2 : ∀ a ∈ fvs2, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, hty2⟩ := ConLeche.openPisAtFvars_index _ _ _ hopen2 k a hk
    exact ⟨_, ty, hty2⟩
  have hcbodyHead : cbody.getAppFn
      = Expr.const (dJ.memberName (dJ.tgts i' j l)) (cvT.levelParams.map Level.param) := by
    have hin : (Expr.instSeq (dJ.fvsPF i' j ++ (dJ.xFvsF i' j).take l)
          (dJ.nP + l - 1 + tbs.length) cbody).getAppFn
        = Expr.const (dJ.memberName (dJ.tgts i' j l)) (cvT.levelParams.map Level.param) := by
      refine ConLeche.os_instSeq_getAppFn_const_inv fvs2 hfv2 (tbs.length - 1) _ ?_
      rw [← hbodyO]; exact hheadO
    exact ConLeche.os_instSeq_getAppFn_const_inv _ hfv (dJ.nP + l - 1 + tbs.length) _ hin
  have hcbodyArgs : cbody.getAppArgs.length = dJ.nP + dJ.nIdxAt (dJ.tgts i' j l) := by
    have h1 := hlenO
    rw [hbodyO, ConLeche.os_instSeq_getAppArgs _ hfv2, ConLeche.os_instSeq_getAppArgs _ hfv,
      List.length_map, List.length_map] at h1
    exact h1
  -- the target IS a member of the container's group
  have hmLt : dJ.tgts i' j l < ci.members.length := by rw [← CMci.k]; exact hmem
  obtain ⟨Mt, hMt⟩ : ∃ Mt, ci.members[dJ.tgts i' j l]? = some Mt :=
    ⟨_, List.getElem?_eq_getElem hmLt⟩
  have hMtName : dJ.memberName (dJ.tgts i' j l) = Mt.name := (CMci.member _ Mt hMt).1
  have hMtMem : Mt ∈ ci.members := List.mem_of_getElem? hMt
  -- K.14's UNIFORMITY under the field's own binders
  have hbdIdx : (pcs ++ fcs)[ci.nP + l]? = some (fcs.getD l default) := by
    have hidx : ci.nP + l - pcs.length = l := by rw [hpl, hnPci]; omega
    rw [List.getElem?_append_right (by rw [hpl, hnPci]; omega), hidx]
    exact hfcsl
  have hstripCi : cc.type.stripPis (ci.nP + cc.nFields) = some (pcs ++ fcs, residJ) := by
    rw [hnPci]; exact hstripJ
  obtain ⟨-, hTake⟩ := ConLeche.nestedContainersOk_memberSpineRefl R.hcont hpinMem hciC hJmem
    hJcc hstripCi hbdIdx hFclPis hcbodyHead (by rw [hMtName]; exact List.mem_map_of_mem hMtMem)
    (by rw [hcbodyArgs, hnPci]; omega)
  rw [hnPci] at hTake
  -- the container's closed domain, as the member at the parameter spine
  have hcbodySplit : cbody
      = Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l)) (J.lps.map Level.param))
        (ConLeche.structPsAt (l + tbs.length) dJ.nP ++ cbody.getAppArgs.drop dJ.nP) := by
    have hargs : ConLeche.structPsAt (l + tbs.length) dJ.nP ++ cbody.getAppArgs.drop dJ.nP
        = cbody.getAppArgs := by rw [← hTake, List.take_append_drop]
    rw [hargs, hlpsJEq, ← hcbodyHead]
    exact (Expr.mkAppN_getApp _).symm
  -- the instantiated domain is the instantiated telescope over the instantiated body
  have hGmk : Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
          (fcs.getD l default).1)
      = ConLeche.mkPisB
          (ConLeche.instTeleSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
            (tbs.map fun bd =>
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bd.1,
                (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bd.2.pw⟩ :
                  ConLeche.BinderMeta))))
          (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length)
            (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls cbody)) := by
    rw [hFclMk, ConLeche.ilp_mkPisB,
      ConLeche.instSeq_mkPisB _ _ _ _ (by rw [hDsnP]; omega), List.length_map]
  have hBody : Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length)
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls cbody)
      = Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
          (pinsS.getD (q₀ + i') default).lvls)
        ((srcAtE st p (q₀ + i')).2.2 ++
          ((cbody.getAppArgs.drop dJ.nP).map
              (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
            (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length))) := by
    rw [hcbodySplit, ConLeche.ilp_mkAppN,
      ConLeche.ilp_const_params J.lps _ (dJ.memberName (dJ.tgts i' j l))
        (nodup_of_nameNodup hNodupJ) hLvlLen,
      List.map_append, ConLeche.ilp_structPsAt, ConLeche.instSeq_mkAppN_const, List.map_append,
      List.map_map]
    congr 2
    · rw [← hDsnP,
        show (srcAtE st p (q₀ + i')).2.2.length - 1 + l + tbs.length
          = l + tbs.length + (srcAtE st p (q₀ + i')).2.2.length - 1 from by omega]
      exact ConLeche.instSeq_structPsAt _ (l + tbs.length) hDsB
    · simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append]
      rw [List.drop_left' (ConLeche.structPsAt_length (l + tbs.length) dJ.nP), List.map_map]
  rw [hGmk, hBody] at hrun
  -- the rewrite descends the telescope
  obtain ⟨bs', res', hFlEq, hbslen, hbinds, stR₁, stR₂, hresRun, hp1, hp2, hn1⟩ :=
    ConLeche.replaceAllNested_mkPisB
      (ConLeche.instTeleSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
        (tbs.map fun bd =>
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bd.1,
            (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bd.2.pw⟩ :
              ConLeche.BinderMeta)))) hrun
  -- the BODY's occurrence: the mimic of the group's pin at the target
  obtain ⟨hndPins, hgrpAll⟩ := ConLeche.nestedContainersOk_group R.hcont
  obtain ⟨ci₁, hci₁, hmem₁⟩ := hgrpAll _ hpinMem
  have hci₁Eq : ci₁ = ci := Option.some.inj (hci₁.symm.trans hciC)
  obtain ⟨ciM, hciM, hciMnP, -⟩ := hmem₁ Mt (by rw [hci₁Eq]; exact hMtMem)
  obtain ⟨cvM, capsM, -, -, -, -, hfindM, -, -, -, -⟩ := ConLeche.containerInfo?_inv hciM
  have hnPM : ciM.nP = dJ.nP := by rw [hciMnP, hci₁Eq, hnPci]
  have htakeD : ((srcAtE st p (q₀ + i')).2.2 ++
      ((cbody.getAppArgs.drop dJ.nP).map
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length))).take ciM.nP
      = (srcAtE st p (q₀ + i')).2.2 := List.take_left' (by rw [hnPM, hDsnP])
  have hdropD : ((srcAtE st p (q₀ + i')).2.2 ++
      ((cbody.getAppArgs.drop dJ.nP).map
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length))).drop ciM.nP
      = ((cbody.getAppArgs.drop dJ.nP).map
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length)) :=
    List.drop_left' (by rw [hnPM, hDsnP])
  have hmintR : ((srcAtE st p (q₀ + i')).2.2.any fun a =>
      stR₁.newNames.any fun T => a.mentionsConst T) = true := by
    obtain ⟨a, ha, hT⟩ := List.any_eq_true.mp hmint
    obtain ⟨T, hTm, hTc⟩ := List.any_eq_true.mp hT
    exact List.any_eq_true.mpr ⟨a, ha, List.any_eq_true.mpr ⟨T, hn1.subset hTm, hTc⟩⟩
  rw [hMtName] at hresRun
  have hnPargs : ciM.nP ≤ ((srcAtE st p (q₀ + i')).2.2 ++ ((cbody.getAppArgs.drop dJ.nP).map
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length))).length := by
    rw [List.length_append, hnPM, hDsnP]; omega
  have hmentArgs : ((((srcAtE st p (q₀ + i')).2.2 ++ ((cbody.getAppArgs.drop dJ.nP).map
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length))).take ciM.nP).any fun a =>
      stR₁.newNames.any fun T => a.mentionsConst T) = true := by
    rw [htakeD]; exact hmintR
  have hlooseArgs : ∀ a ∈ ((srcAtE st p (q₀ + i')).2.2 ++ ((cbody.getAppArgs.drop dJ.nP).map
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls)).map
        (Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l + tbs.length))).take ciM.nP,
      a.looseBVarsBounded 0 = true := by
    rw [htakeD]; exact hDsB
  obtain ⟨qn, hqnMem, hqnPin, hqnEq⟩ :=
    ConLeche.replaceAllNested_occurrence rfl hfindM hciM hnPargs hmentArgs hlooseArgs hresRun
  rw [htakeD] at hqnPin
  rw [hdropD] at hqnEq
  -- the group's pin at the target member carries the same source
  have hmkJ : dJ.tgts i' j l < kJ := by rw [← S.kEq]; exact hmem
  have hplen : q₀ + dJ.tgts i' j l < st.pins.length := by
    obtain ⟨-, -, h3⟩ := PD.seg
    rw [hgb, hgs] at h3; omega
  have PDm := hPD _ hplen
  obtain ⟨hcontm, -, -, hsrcm, hmemm⟩ := PD.grp (dJ.tgts i' j l) (by rw [hgs]; exact hmkJ)
  rw [hgb] at hcontm hsrcm
  have hsrcPair := Option.some.inj (PDm.src.symm.trans hsrcm)
  have hsrc1 : (srcAtE st p (q₀ + dJ.tgts i' j l)).2.1 = (srcAtE st p (q₀ + i')).2.1 :=
    (Prod.mk.inj (Prod.mk.inj hsrcPair).2).1
  have hsrc2 : (srcAtE st p (q₀ + dJ.tgts i' j l)).2.2 = (srcAtE st p (q₀ + i')).2.2 :=
    (Prod.mk.inj (Prod.mk.inj hsrcPair).2).2
  have hmemName : (memberOf env st (q₀ + i') (dJ.tgts i' j l)).name = Mt.name := by
    have h1 : (ci.members.map (·.name))[dJ.tgts i' j l]? = some Mt.name := by
      rw [List.getElem?_map, hMt]; rfl
    have h2 : ((baseInfo env st (q₀ + i')).members.map (·.name))[dJ.tgts i' j l]?
        = some (memberOf env st (q₀ + i') (dJ.tgts i' j l)).name := by
      rw [List.getElem?_map, hmemm]; rfl
    rw [hnamesP] at h1
    exact Option.some.inj (h2.symm.trans h1)
  have hpinm : (pinAtE st (q₀ + dJ.tgts i' j l)).pin
      = Expr.mkAppN (.const Mt.name (pinsS.getD (q₀ + i') default).lvls)
          (srcAtE st p (q₀ + i')).2.2 := by
    rw [PDm.pinEq, hcontm, hsrc1, hsrc2, hmemName, hlv]
  obtain rfl : qn = pinAtE st (q₀ + dJ.tgts i' j l) := by
    have h1 := ConLeche.find?_pin_of_nodup hndPins
      ((hp2.trans hpre).subset hqnMem) hqnPin
    have h2 := ConLeche.find?_pin_of_nodup hndPins (List.mem_of_getElem? PDm.pin) hpinm
    exact Option.some.inj (h1.symm.trans h2)
  -- the TELESCOPE: the prune at every binder
  have hresHead : res'.getAppFn
      = Expr.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param) := by
    rw [hqnEq]
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn]
  have hFlPis : Fl.piBinders = (bs', res') := by
    rw [hFlEq]; exact piBinders_mkPisB_of_head bs' hresHead
  rw [hFlPis] at hfree
  have hbsEq : bs' = ConLeche.instTeleSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
      (tbs.map fun bd =>
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bd.1,
          (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bd.2.pw⟩ :
            ConLeche.BinderMeta))) := by
    refine tele_ext hbslen fun k hk => ?_
    obtain ⟨hbm, stB₁, stB₂, hrunB, -, hpb2, -⟩ := hbinds k hk
    refine ⟨?_, hbm⟩
    rcases ConLeche.replaceAllNested_unchanged_or_aux _ hrunB with heq | ⟨qq, hqqMem, hqqM⟩
    · exact heq
    · exfalso
      have hkb : k < bs'.length := by rw [hbslen]; exact hk
      obtain ⟨qi, hqi⟩ := List.getElem?_of_mem ((hpb2.trans hpre).subset hqqMem)
      have hqiLt : qi < st.pins.length := (List.getElem?_eq_some_iff.mp hqi).1
      obtain ⟨-, -, -, -, -, -, -, hauxN⟩ := R.groupCopyFormer hPD hqiLt
      have hpinEq2 : pinAtE st qi = qq := Option.some.inj ((hPD _ hqiLt).pin.symm.trans hqi)
      rw [hpinEq2] at hauxN
      have hmm : ConLeche.mentionsMember b.memberNames (bs'.getD k default).1 = true :=
        List.any_eq_true.mpr ⟨qq.aux, hauxN, hqqM⟩
      rw [hfree k hkb] at hmm
      exact nomatch hmm
  rw [hbsEq] at hFlEq
  -- the telescope's length, at the container's own readings
  have htlsLen : ∀ ψJ : Name → Nat,
      (((dJ.tlss i' ψJ).getD j []).getD l []).length = tbs.length := by
    intro ψJ
    obtain ⟨-, -, -, hlenT, -, -⟩ := hCD.reflOpen ψJ l x hx hnest hrefl
    rw [IsBlockModel.tlss_getD hj, hlenT, hopen, hpbLen]
  refine ⟨tbs, ConLeche.instTeleSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
      (tbs.map fun bd =>
        (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bd.1,
          (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bd.2.pw⟩ :
            ConLeche.BinderMeta))),
    cbody.getAppArgs.drop dJ.nP, _, ?_, ?_, ?_, htlsLen, rfl, ?_, ?_⟩
  · rw [hFclPis, ← hcbodySplit]
  · rw [← hfvs2len, ← hafvsEq]
    exact hafne
  · rw [List.length_drop, hcbodyArgs]; omega
  · rw [hGmk, hBody,
      show tbs.length = (ConLeche.instTeleSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
        (tbs.map fun bd =>
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bd.1,
            (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bd.2.pw⟩ :
              ConLeche.BinderMeta)))).length from by
        rw [ConLeche.instTeleSeq_length, List.length_map]]
    exact ConLeche.stripPis_mkPisB_self _ _
  · rw [hFlEq, hqnEq,
      show tbs.length = (ConLeche.instTeleSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
        (tbs.map fun bd =>
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls bd.1,
            (⟨Level.substPW J.lps (pinsS.getD (q₀ + i') default).lvls bd.2.pw⟩ :
              ConLeche.BinderMeta)))).length from by
        rw [ConLeche.instTeleSeq_length, List.length_map]]
    exact ConLeche.stripPis_mkPisB_self _ _

omit [SetTheory V] R SF S in
/-- Two application spines in a row are one. -/
private theorem mkAppN_append' : ∀ (as : List Expr) (f : Expr) (bs : List Expr),
    Expr.mkAppN (Expr.mkAppN f as) bs = Expr.mkAppN f (as ++ bs)
  | [], f, bs => rfl
  | a :: as, f, bs => by
    show Expr.mkAppN (Expr.mkAppN (.app f a) as) bs = Expr.mkAppN f ((a :: as) ++ bs)
    rw [mkAppN_append' as (.app f a) bs]
    rfl

omit [SetTheory V] R SF S in
/-- An erasure-equal partner of a constant IS that constant. -/
private theorem erasedEq_const_invD {T : Name} {lvls : List Level} {e : Expr}
    (h : Expr.ErasedEq e (.const T lvls)) : e = .const T lvls := by
  match e, h with
  | .const n us, h =>
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- **THE AUXILIARY BLOCK'S KIND AT A COPY'S REFLEXIVE FIELD** (task
#315 L-B): `copyRecFKind` under the field's own binders.  The
elimination left a `∀`-tower over the mimic of the group's pin
(`copyRecFDomRefl`, over the walk's own Π guard
`normCtorValM_domPiFree`), the positivity normalisation carries the
tower across (`normCtorValM_domErasedPi`), and the classification
answers `.reflexive` at the copy's own block member
(`mutualCtorKinds_memberHeadPi`). -/
theorem NestedPinsRun.copyRecFKindRefl {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hmem : dJ.tgts i' j l < dJ.k)
    (hrefl : (dJ.ksF i' j).getD l .ordinary = .reflexive) :
    (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)
      = (.reflexive, p.k + (q₀ + dJ.tgts i' j l)) := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    -, -, ⟨cI, fcs', hinstCI, hstripCI, -⟩, hcb, hcA, hnF, hbc⟩ := R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  obtain ⟨st₁, st₂, hrun, hpre, hmint⟩ := hfields l hlcc
  -- the copy's stored constructor, and the normalisation it came from
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  obtain ⟨-, sorts, -, hCtor⟩ := R.h.runC _ _ hcA
  obtain ⟨hnorm, -, hbndC⟩ := ConLeche.checkMutualCtor_true_norm hCtor
  have hcvC : (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).cv
      = ⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩ := by
    rw [List.getD_eq_getElem?_getD, hbc]; rfl
  rw [hcvC] at hnorm hbndC
  rw [hnF] at hnorm hopX'
  -- the GIVEN type's two-stage opening, and the field's domain in it
  obtain ⟨fvsA, -, -, hlawA⟩ := ConLeche.openPisAtFvars_mkPisB b.nP pbs₀ hpbs₀len 0
  have hfvsA : fvsA = params := by
    have hlaw := hlawA o'
    rw [← ConLeche.stripPis_mkPisB _ hstripF] at hlaw
    exact (Prod.mk.inj (Option.some.inj (hlaw.symm.trans hopb))).1
  have hop1 : ConLeche.openPisAtFvars b.nP (closeTelescope pbs₀ 0 cbody') 0
      = some (params, cbody') := by
    rw [ConLeche.closeTelescope_eq_mkPisB pbs₀ 0 cbody' hpbs₀f, hpbs₀len, hlawA, hfvsA,
      ConLeche.instSeq_abstractRange_fvs b.nP params cbody' hcbb hplenB hidxP hcbl]
  obtain ⟨xfvs, hxflen, -, hlawX⟩ := ConLeche.openPisAtFvars_mkPisB cc.nFields Fs' hlenF b.nP
  obtain ⟨resB, hcb'⟩ : ∃ r, cbody'.stripPis cc.nFields = some (Fs', r) := ⟨_, hcb⟩
  have hcbodyEq := ConLeche.stripPis_mkPisB _ hcb'
  have hop2 : ConLeche.openPisAtFvars cc.nFields cbody' b.nP
      = some (xfvs, Expr.instSeq xfvs (cc.nFields - 1) resB) := by
    rw [hcbodyEq]; exact hlawX resB
  obtain ⟨x, hx⟩ : ∃ x, xfvs[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxflen]; exact hlcc)⟩
  have hstripC : (closeTelescope pbs₀ 0 cbody').stripPis (b.nP + cc.nFields)
      = some (pbs₀ ++ ConLeche.abstractTele 0 pbs₀.length 0 Fs',
          resB.abstractRange 0 pbs₀.length Fs'.length) := by
    rw [hcbodyEq]
    rw [show b.nP + cc.nFields = pbs₀.length + Fs'.length from by rw [hpbs₀len, hlenF]]
    exact ConLeche.closeTelescope_mkPisB_strip hpbs₀f
  have habs : (ConLeche.abstractTele 0 pbs₀.length 0 Fs')[l]?
      = some ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show l < (ConLeche.abstractTele 0 pbs₀.length 0 Fs').length from by
        rw [ConLeche.abstractTele_length, hlenF]; exact hlcc)]
    rfl
  have hxdom : x.fvarTypeD = Expr.instSeq (params ++ xfvs.take l) (b.nP + l - 1)
      ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default).1 :=
    ConLeche.os_field_domain b.nP cc.nFields l
      (openPisAtFvars_add b.nP hop1 (by rw [Nat.zero_add]; exact hop2))
      hstripC hplenB hpbs₀len hx habs
  have hFsl : Fs'[l]? = some (Fs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenF]; exact hlcc)]
    rfl
  have hFlBnd : (Fs'.getD l default).1.looseBVarsBounded l = true := by
    have h := ConLeche.stripPis_binder_bounded cc.nFields hcb' hcbb l _ hFsl
    simpa using h
  have hFlLeaves : ∀ lf ∈ (Fs'.getD l default).1.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ params :=
    fun lf hlf => hcbl lf (ConLeche.stripPis_binder_leaves cc.nFields hcb' l _ hFsl lf hlf)
  have hxdom2 : x.fvarTypeD = Expr.instSeq (xfvs.take l) (l - 1) (Fs'.getD l default).1 := by
    rw [hxdom, ConLeche.abstractTele_getD 0 pbs₀.length Fs' 0 l (by rw [hlenF]; exact hlcc),
      Expr.instSeq_append, hplenB, show b.nP + l - 1 - b.nP = l - 1 from by omega, hpbs₀len]
    simp only [Nat.zero_add]
    rw [ConLeche.instSeq_abstractRange_fvs_at b.nP l params _ hFlBnd hplenB hidxP hFlLeaves]
  -- the openers of the field stage are free variables
  have hxfvsFv : ∀ a ∈ xfvs.take l, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem (List.take_subset _ _ ha)
    obtain ⟨ty, hty2⟩ := ConLeche.openPisAtFvars_index _ _ _ hop2 k a hk
    exact ⟨_, ty, hty2⟩
  have hxfvsLe : (xfvs.take l).length ≤ l - 1 + 1 := by
    rw [List.length_take]; omega
  -- the rewritten field's own telescope, and the walk's Π guard on it
  obtain ⟨tbs0, cbodyFl, hpbFl⟩ :
      ∃ tbs0 cbodyFl, ((Fs'.getD l default).1.piBinders) = (tbs0, cbodyFl) := ⟨_, _, rfl⟩
  have hFlPis : (Fs'.getD l default).1.stripPis tbs0.length = some (tbs0, cbodyFl) := by
    have h := Expr.stripPis_piBinders (Fs'.getD l default).1
    rw [hpbFl] at h; exact h
  have hFlMk : (Fs'.getD l default).1 = ConLeche.mkPisB tbs0 cbodyFl :=
    ConLeche.stripPis_mkPisB _ hFlPis
  have hxpeel : x.fvarTypeD.stripPis tbs0.length
      = some (ConLeche.instTeleSeq (xfvs.take l) (l - 1) tbs0,
          Expr.instSeq (xfvs.take l) (l - 1 + tbs0.length) cbodyFl) := by
    rw [hxdom2, hFlMk, ConLeche.instSeq_mkPisB _ _ _ _ hxfvsLe,
      show tbs0.length = (ConLeche.instTeleSeq (xfvs.take l) (l - 1) tbs0).length from
        (ConLeche.instTeleSeq_length _ _ _).symm]
    exact ConLeche.stripPis_mkPisB_self _ _
  have hfreeOpened := ConLeche.normCtorValM_domPiFree hnorm hop1 hop2 hx hxpeel
  have hfree : ∀ k, k < ((Fs'.getD l default).1.piBinders).1.length →
      ConLeche.mentionsMember b.memberNames
        (((Fs'.getD l default).1.piBinders).1.getD k default).1 = false := by
    simp only [hpbFl]
    intro k hk
    have h1 := hfreeOpened k hk
    rw [ConLeche.instTeleSeq_getD _ tbs0 (l - 1) k hk] at h1
    refine List.any_eq_false.mpr fun T hT => ?_
    have h2 := List.any_eq_false.mp h1 T hT
    simp only [Bool.not_eq_true] at h2 ⊢
    exact ConLeche.mentionsConst_instSeq_false _ _ (by simpa using h2)
  -- the elimination's occurrence chain under the field's binders
  obtain ⟨tbs, TL, idxs, IDXS, -, hneTbs, -, -, -, -, hFlStrip⟩ :=
    R.copyRecFDomRefl SF S hPD hi' hgb hgs CM hj hciP hJmem hJcc hJname hty hnf hstripJ hpl hfl
      hDsnP hDsB hlcc hmem hrefl hrun hpre hmint hfree
  -- the group's target pin, and the block former it minted
  have hq : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have PD := hPD _ hq
  have hmkJ : dJ.tgts i' j l < kJ := by rw [← S.kEq]; exact hmem
  have hplen : q₀ + dJ.tgts i' j l < st.pins.length := by
    obtain ⟨-, -, h3⟩ := PD.seg
    rw [hgb, hgs] at h3; omega
  obtain ⟨fM, nIdxM, hfM, -, hauxFind, hfind3, hauxMem, -⟩ := R.groupCopyFormer hPD hplen
  -- the GIVEN domain, as a tower over the mimic
  have hFlMk2 : (Fs'.getD l default).1
      = ConLeche.mkPisB TL (Expr.mkAppN (Expr.mkAppN
          (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param)) params) IDXS) :=
    ConLeche.stripPis_mkPisB _ hFlStrip
  have hTLlen : TL.length = tbs.length := by
    have := Expr.stripPis_length _ hFlStrip
    omega
  have hxMk : x.fvarTypeD
      = ConLeche.mkPisB (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL)
          (Expr.instSeq (xfvs.take l) (l - 1 + TL.length)
            (Expr.mkAppN (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
              (params ++ IDXS))) := by
    rw [hxdom2, hFlMk2, mkAppN_append', ConLeche.instSeq_mkPisB _ _ _ _ hxfvsLe]
  obtain ⟨afvs2, hafvs2len, -, hlawA2⟩ :=
    ConLeche.openPisAtFvars_mkPisB TL.length (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL)
      (ConLeche.instTeleSeq_length _ _ _) (b.nP + l)
  have hopA : ConLeche.openPisAtFvars TL.length x.fvarTypeD (b.nP + l)
      = some (afvs2, Expr.mkAppN
          (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
          (((params ++ IDXS).map (Expr.instSeq (xfvs.take l) (l - 1 + TL.length))).map
            (Expr.instSeq afvs2 (TL.length - 1)))) := by
    rw [hxMk, hlawA2 _, ConLeche.instSeq_mkAppN_const, ConLeche.instSeq_mkAppN_const]
  -- the stored constructor's own opened field domain
  obtain ⟨x', hx'⟩ : ∃ x', (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnF]; exact hlcc)⟩
  have hfbC : Expr.fvarsBelow b.nP cbody' := by
    refine ConLeche.fvarsBelow_of_leaves fun lf hlf => ?_
    obtain ⟨k, hk⟩ := List.getElem?_of_mem (hcbl lf hlf)
    have hklt : k < b.nP := by
      rw [← hplenB]; exact (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨ty, hty2⟩ := hidxP k hklt
    rw [hk] at hty2
    have := (ConLeche.Expr.fvar.inj (Option.some.inj hty2)).1
    omega
  have her := ConLeche.normCtorValM_domErasedPi mp₁.base2.wf hnorm hbndC hop1 hop2 hfbC
    hopP' hopX' hx hx' hauxFind hopA
  -- the stored domain is that tower, up to annotations
  have hxpeel2 : x.fvarTypeD.stripPis TL.length
      = some (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL,
          Expr.instSeq (xfvs.take l) (l - 1 + TL.length)
            (Expr.mkAppN (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
              (params ++ IDXS))) := by
    rw [hxMk, show TL.length = (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL).length from
      (ConLeche.instTeleSeq_length _ _ _).symm]
    exact ConLeche.stripPis_mkPisB_self _ _
  obtain ⟨bs₁, body₁, hstrip₁, hlen₁, -, hbody₁⟩ :=
    Expr.ErasedEq.stripPis_inv TL.length her hxpeel2
  have hbody₁head : body₁.getAppFn
      = Expr.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param) := by
    rw [ConLeche.instSeq_mkAppN_const] at hbody₁
    obtain ⟨hfn, -, -⟩ := ConLeche.ErasedEq.getApp hbody₁
    rw [Expr.getAppFn_mkAppN] at hfn
    exact erasedEq_const_invD hfn
  have hx'Mk : x'.fvarTypeD = ConLeche.mkPisB bs₁ body₁ := ConLeche.stripPis_mkPisB _ hstrip₁
  -- the CLOSED stored domain the classification reads
  obtain ⟨cbsA, esA, hstripA, -⟩ := hCD.resid
  rw [hnF] at hstripA
  have hcbsAlen : cbsA.length = b.nP + cc.nFields := Expr.stripPis_length _ hstripA
  have htakeLen : (cbsA.take b.nP).length = b.nP := by
    rw [List.length_take, hcbsAlen]; omega
  obtain ⟨resA, hstripAx⟩ : ∃ r, cA.1.type.stripPis (b.nP + cc.nFields) = some (cbsA, r) :=
    ⟨_, hstripA⟩
  have hstripA' : cA.1.type.stripPis (b.nP + cc.nFields)
      = some (cbsA.take b.nP ++ cbsA.drop b.nP, resA) := by
    rw [List.take_append_drop]; exact hstripAx
  have hdropA : (cbsA.drop b.nP)[l]? = some ((cbsA.drop b.nP).getD l default) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show l < (cbsA.drop b.nP).length from by
        rw [List.length_drop, hcbsAlen]; omega)]
    rfl
  have hopenA : x'.fvarTypeD
      = Expr.instSeq (fvsPF (b.ownOffset (p.k + q₀ + i') + j)
          ++ (xFvsF (b.ownOffset (p.k + q₀ + i') + j)).take l) (b.nP + l - 1)
        ((cbsA.drop b.nP).getD l default).1 :=
    ConLeche.os_field_domain b.nP cc.nFields l
      (openPisAtFvars_add b.nP hopP' (by rw [Nat.zero_add]; exact hopX'))
      hstripA' hCD.pLen htakeLen hx' hdropA
  have hfvA : ∀ a ∈ (fvsPF (b.ownOffset (p.k + q₀ + i') + j)
      ++ (xFvsF (b.ownOffset (p.k + q₀ + i') + j)).take l),
      ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨k, hk⟩ := List.getElem?_of_mem h
      obtain ⟨ty, hty2⟩ := hCD.pIdx k a hk
      exact ⟨k, ty, hty2⟩
    · obtain ⟨k, hk⟩ := List.getElem?_of_mem (List.take_subset _ _ h)
      obtain ⟨ty, hty2⟩ := hCD.xIdx k a hk
      exact ⟨b.nP + k, ty, hty2⟩
  have hfvALe : (fvsPF (b.ownOffset (p.k + q₀ + i') + j)
      ++ (xFvsF (b.ownOffset (p.k + q₀ + i') + j)).take l).length ≤ b.nP + l - 1 + 1 := by
    rw [List.length_append, hCD.pLen, List.length_take]; omega
  obtain ⟨hpbLenA, hpbBodyA⟩ :=
    Expr.piBinders_instSeq (fvsPF (b.ownOffset (p.k + q₀ + i') + j)
      ++ (xFvsF (b.ownOffset (p.k + q₀ + i') + j)).take l) (b.nP + l - 1)
      ((cbsA.drop b.nP).getD l default).1 hfvA hfvALe
  rw [← hopenA] at hpbLenA hpbBodyA
  have hx'pb : x'.fvarTypeD.piBinders = (bs₁, body₁) := by
    rw [hx'Mk]; exact piBinders_mkPisB_of_head bs₁ hbody₁head
  rw [hx'pb] at hpbLenA hpbBodyA
  -- the closed stored domain: a tower of the same length over the mimic
  obtain ⟨tbsA, bodyA, hpbA⟩ :
      ∃ tbsA bodyA, (((cbsA.drop b.nP).getD l default).1.piBinders) = (tbsA, bodyA) :=
    ⟨_, _, rfl⟩
  rw [hpbA] at hpbLenA hpbBodyA
  have hbodyAhead : bodyA.getAppFn
      = Expr.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param) := by
    refine ConLeche.os_instSeq_getAppFn_const_inv _ hfvA (b.nP + l - 1 + tbsA.length) _ ?_
    rw [← hpbBodyA]; exact hbody₁head
  have hdomA : (cbsA.getD (b.nP + l) default).1
      = ConLeche.mkPisB tbsA (Expr.mkAppN
          (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
          bodyA.getAppArgs) := by
    rw [← getD_dropD]
    have h1 : ((cbsA.drop b.nP).getD l default).1 = ConLeche.mkPisB tbsA bodyA := by
      have h := Expr.stripPis_piBinders ((cbsA.drop b.nP).getD l default).1
      rw [hpbA] at h
      exact ConLeche.stripPis_mkPisB _ h
    rw [h1, ← hbodyAhead, Expr.mkAppN_getApp]
  have hneA : tbsA.length ≠ 0 := by
    rw [← hpbLenA, hlen₁, ConLeche.instTeleSeq_length, hTLlen]; exact hneTbs
  -- the classification at that field
  obtain ⟨hmapM, hnegAll, hunsAll, -⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hksNeg : ksG.any (·.1 == .negative) = false := by
    rcases hb0 : ksG.any (·.1 == .negative) with _ | _
    · rfl
    · exact absurd (List.any_eq_true.mpr ⟨ksG, List.mem_of_getElem? hksG, hb0⟩)
        (by rw [hnegAll]; simp)
  have hksUns : ksG.any (·.1 == .unsupported) = false := by
    rcases hb0 : ksG.any (·.1 == .unsupported) with _ | _
    · rfl
    · exact absurd (List.any_eq_true.mpr ⟨ksG, List.mem_of_getElem? hksG, hb0⟩)
        (by rw [hunsAll]; simp)
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hstripA2 : cA.1.type.stripPis (b.nP + cA.2) = some (cbsA, resA) := by
    rw [hnF]; exact hstripAx
  have hkindEntry := mutualCtorKinds_memberHeadPi hmk hksNeg hksUns hstripA2 hlA hdomA hneA
    hauxMem hfind3
  rw [hmutKs]
  exact hkindEntry

/-- **`CopyCtorShape.recF`'s first two conjuncts at a REFLEXIVE field**
(task #315 L-B): `copyRecF`'s twin over `copyRecFKindRefl` — the copy's
field `l` is recursive (the `rss` table records `.reflexive` as
recursive too), at the block member `p.k + q₀ + m`. -/
theorem NestedPinsRun.copyRecFRefl {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hmem : dJ.tgts i' j l < dJ.k)
    (hrefl : (dJ.ksF i' j).getD l .ordinary = .reflexive) :
    ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + q₀ + dJ.tgts i' j l := by
  classical
  obtain ⟨cc, -, -, -, -, -, -, -, -, -, -, -, cA, -, -, -,
    -, -, -, -, -, hnf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hcA, hnF, -⟩ := R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hkindEntry := R.copyRecFKindRefl SF S hPD hkindsRun hi' hgb hgs CM hj hlF hmem hrefl
  have hlks : l < (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).length := by
    obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
    rw [hksLen]; exact hlA
  refine ⟨?_, ?_⟩
  · rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map]; exact hlks),
      decide_eq_true_eq, kindsOf_getD']
    right
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).1 = _
    rw [hkindEntry]
  · rw [mutTgts_getD hGlt (show l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) from by
      show l < (ctorsA.getD _ default).2
      rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]; exact hlA)]
    show ((mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).getD l (.ordinary, 0)).2 = _
    rw [hkindEntry]
    show p.k + (q₀ + dJ.tgts i' j l) = _
    omega

/-- **`CopyCtorShape.recF`'s telescope and index-expression conjuncts**
at a REFLEXIVE field (task #315 L-B): the copy's telescope is the
container's instantiated entry by entry, and its index expressions are
the container's instantiated at the field's depth PAST the telescope.
`copyRecFRead` one layer deeper: the MINTED constructor's `l`-th opened
field domain is the container's instantiated (`mintFieldRead`), whose
reading is a Π-tower (`BlockCtorData.reflEntry`) that parameter
instantiation distributes over (`AnnotTerm.instAll_mkPisAV`), so its
openers read as the container's telescope instantiated and its body's
spine as the container's index readings; and the copy's STORED domain
is the elimination's rewrite of that very domain, which keeps the
telescope (`copyRecFDomRefl`) and is carried across the normalisation
up to the openers' annotations (`normCtorValM_domErasedPi`). -/
theorem NestedPinsRun.copyRecFReadRefl {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    {i' : Nat} (hi' : i' < kJ)
    (hgb : (pinAtE st (q₀ + i')).grpBase = q₀)
    (hgs : (pinAtE st (q₀ + i')).grpSize = kJ)
    (CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hmem : dJ.tgts i' j l < dJ.k)
    (hrefl : (dJ.ksF i' j).getD l .ordinary = .reflexive)
    (ψ : Name → Nat) :
    (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).map
        (·.2.2)
      = instTele ((pinsS.getD (q₀ + i') default).Ds ψ) l
          ((((dJ.tlss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l []).map
            (·.2.2)) ∧
    ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
      = (((dJ.Eiss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l []).map
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ)
            (l + (((dJ.tlss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l
              []).length)) := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    -, -, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ := R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  obtain ⟨st₁, st₂, hrun, hpre, hmint⟩ := hfields l hlcc
  -- the container's constructor data, and the copy's
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  obtain ⟨-, -, hCDJ⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hnest : dJ.nestOf i' j l = none := dJ.nestOf_none hmem
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hkindEntry := R.copyRecFKindRefl SF S hPD hkindsRun hi' hgb hgs CM hj hlF hmem hrefl
  have hkindA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l
      = RecFieldKind.reflexive := by
    show ((mutKsOf kinds _).getD l (.ordinary, 0)).1 = _
    rw [hkindEntry]
  -- the copy's stored constructor, and the normalisation it came from
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  obtain ⟨-, sorts, -, hCtor⟩ := R.h.runC _ _ hcA
  obtain ⟨hnorm, -, hbndC⟩ := ConLeche.checkMutualCtor_true_norm hCtor
  have hcvC : (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).cv
      = ⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩ := by
    rw [List.getD_eq_getElem?_getD, hbc]; rfl
  rw [hcvC] at hnorm hbndC
  rw [hnF] at hnorm hopX'
  -- the GIVEN type's two-stage opening, and the field's domain in it
  obtain ⟨fvsA, -, -, hlawA⟩ := ConLeche.openPisAtFvars_mkPisB b.nP pbs₀ hpbs₀len 0
  have hfvsA : fvsA = params := by
    have hlaw := hlawA o'
    rw [← ConLeche.stripPis_mkPisB _ hstripF] at hlaw
    exact (Prod.mk.inj (Option.some.inj (hlaw.symm.trans hopb))).1
  have hop1 : ConLeche.openPisAtFvars b.nP (closeTelescope pbs₀ 0 cbody') 0
      = some (params, cbody') := by
    rw [ConLeche.closeTelescope_eq_mkPisB pbs₀ 0 cbody' hpbs₀f, hpbs₀len, hlawA, hfvsA,
      ConLeche.instSeq_abstractRange_fvs b.nP params cbody' hcbb hplenB hidxP hcbl]
  obtain ⟨xfvs, hxflen, -, hlawX⟩ := ConLeche.openPisAtFvars_mkPisB cc.nFields Fs' hlenF b.nP
  obtain ⟨resB, hcb'⟩ : ∃ r, cbody'.stripPis cc.nFields = some (Fs', r) := ⟨_, hcb⟩
  have hcbodyEq := ConLeche.stripPis_mkPisB _ hcb'
  have hop2 : ConLeche.openPisAtFvars cc.nFields cbody' b.nP
      = some (xfvs, Expr.instSeq xfvs (cc.nFields - 1) resB) := by
    rw [hcbodyEq]; exact hlawX resB
  obtain ⟨x, hx⟩ : ∃ x, xfvs[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxflen]; exact hlcc)⟩
  have hstripC : (closeTelescope pbs₀ 0 cbody').stripPis (b.nP + cc.nFields)
      = some (pbs₀ ++ ConLeche.abstractTele 0 pbs₀.length 0 Fs',
          resB.abstractRange 0 pbs₀.length Fs'.length) := by
    rw [hcbodyEq]
    rw [show b.nP + cc.nFields = pbs₀.length + Fs'.length from by rw [hpbs₀len, hlenF]]
    exact ConLeche.closeTelescope_mkPisB_strip hpbs₀f
  have habs : (ConLeche.abstractTele 0 pbs₀.length 0 Fs')[l]?
      = some ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show l < (ConLeche.abstractTele 0 pbs₀.length 0 Fs').length from by
        rw [ConLeche.abstractTele_length, hlenF]; exact hlcc)]
    rfl
  have hxdom : x.fvarTypeD = Expr.instSeq (params ++ xfvs.take l) (b.nP + l - 1)
      ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default).1 :=
    ConLeche.os_field_domain b.nP cc.nFields l
      (openPisAtFvars_add b.nP hop1 (by rw [Nat.zero_add]; exact hop2))
      hstripC hplenB hpbs₀len hx habs
  have hFsl : Fs'[l]? = some (Fs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenF]; exact hlcc)]
    rfl
  have hFlBnd : (Fs'.getD l default).1.looseBVarsBounded l = true := by
    have h := ConLeche.stripPis_binder_bounded cc.nFields hcb' hcbb l _ hFsl
    simpa using h
  have hFlLeaves : ∀ lf ∈ (Fs'.getD l default).1.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ params :=
    fun lf hlf => hcbl lf (ConLeche.stripPis_binder_leaves cc.nFields hcb' l _ hFsl lf hlf)
  have hxdom2 : x.fvarTypeD = Expr.instSeq (xfvs.take l) (l - 1) (Fs'.getD l default).1 := by
    rw [hxdom, ConLeche.abstractTele_getD 0 pbs₀.length Fs' 0 l (by rw [hlenF]; exact hlcc),
      Expr.instSeq_append, hplenB, show b.nP + l - 1 - b.nP = l - 1 from by omega, hpbs₀len]
    simp only [Nat.zero_add]
    rw [ConLeche.instSeq_abstractRange_fvs_at b.nP l params _ hFlBnd hplenB hidxP hFlLeaves]
  have hxfvsFv : ∀ a ∈ xfvs.take l, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem (List.take_subset _ _ ha)
    obtain ⟨ty, hty2⟩ := ConLeche.openPisAtFvars_index _ _ _ hop2 k a hk
    exact ⟨_, ty, hty2⟩
  have hxfvsLe : (xfvs.take l).length ≤ l - 1 + 1 := by
    rw [List.length_take]; omega
  -- the walk's Π guard on the rewritten field's own telescope
  obtain ⟨tbs0, cbodyFl, hpbFl⟩ :
      ∃ tbs0 cbodyFl, ((Fs'.getD l default).1.piBinders) = (tbs0, cbodyFl) := ⟨_, _, rfl⟩
  have hFlPis : (Fs'.getD l default).1.stripPis tbs0.length = some (tbs0, cbodyFl) := by
    have h := Expr.stripPis_piBinders (Fs'.getD l default).1
    rw [hpbFl] at h; exact h
  have hFlMk : (Fs'.getD l default).1 = ConLeche.mkPisB tbs0 cbodyFl :=
    ConLeche.stripPis_mkPisB _ hFlPis
  have hxpeel : x.fvarTypeD.stripPis tbs0.length
      = some (ConLeche.instTeleSeq (xfvs.take l) (l - 1) tbs0,
          Expr.instSeq (xfvs.take l) (l - 1 + tbs0.length) cbodyFl) := by
    rw [hxdom2, hFlMk, ConLeche.instSeq_mkPisB _ _ _ _ hxfvsLe,
      show tbs0.length = (ConLeche.instTeleSeq (xfvs.take l) (l - 1) tbs0).length from
        (ConLeche.instTeleSeq_length _ _ _).symm]
    exact ConLeche.stripPis_mkPisB_self _ _
  have hfreeOpened := ConLeche.normCtorValM_domPiFree hnorm hop1 hop2 hx hxpeel
  have hfree : ∀ k, k < ((Fs'.getD l default).1.piBinders).1.length →
      ConLeche.mentionsMember b.memberNames
        (((Fs'.getD l default).1.piBinders).1.getD k default).1 = false := by
    simp only [hpbFl]
    intro k hk
    have h1 := hfreeOpened k hk
    rw [ConLeche.instTeleSeq_getD _ tbs0 (l - 1) k hk] at h1
    refine List.any_eq_false.mpr fun T hT => ?_
    have h2 := List.any_eq_false.mp h1 T hT
    simp only [Bool.not_eq_true] at h2 ⊢
    exact ConLeche.mentionsConst_instSeq_false _ _ (by simpa using h2)
  -- the elimination's occurrence chain under the field's binders
  obtain ⟨tbs, TL, idxs, IDXS, hcPeel, hneTbs, hidxsLen, htlsLen, hIDXS, hmPeel, hFlStrip⟩ :=
    R.copyRecFDomRefl SF S hPD hi' hgb hgs CM hj hciP hJmem hJcc hJname hty hnf hstripJ hpl hfl
      hDsnP hDsB hlcc hmem hrefl hrun hpre hmint hfree
  -- the pin's components: scoped at the block's parameters, and read
  have hqst : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have hq : q₀ + i' < pinsS.length := by have := S.seg; omega
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hDsE : (pinsS.getD (q₀ + i') default).DsE = (srcAtE st p (q₀ + i')).2.2 := by
    have hA := congrArg Expr.getAppArgs hpin
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at hA
    exact hA
  have hspine := SF.pinDs _ hq ψ
  rw [hDsE] at hspine
  obtain ⟨-, hcl₀, hbt₀, hFD₀⟩ := R.former0
  obtain ⟨-, fvsS, oS, hopS, hsc⟩ := R.scoped
  obtain ⟨hbnd, hleaf⟩ := hsc _ (List.mem_of_getElem? PD.pin)
  have hws := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hopS hleaf ψ
  rw [PD.pinEq] at hbnd hws
  obtain ⟨-, hwsD⟩ := ConLeche.WScoped_of_mkAppN hws
  obtain ⟨-, hbndD⟩ := ConLeche.looseBVarsBounded_of_mkAppN hbnd
  have hDsSc : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2,
      Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true :=
    fun a ha => ⟨hwsD a ha, hbndD a ha⟩
  -- (A) THE MINTED SIDE: the `l`-th field domain, opened at the tower
  obtain ⟨resM, hstripCI'⟩ : ∃ r, cI.stripPis cc.nFields = some (fcs', r) := ⟨_, hstripCI⟩
  have hfcs'len : fcs'.length = cc.nFields := Expr.stripPis_length _ hstripCI'
  obtain ⟨xfvs', hxf'len, -, hlawX'⟩ :=
    ConLeche.openPisAtFvars_mkPisB cc.nFields fcs' hfcs'len b.nP
  have hopM : ConLeche.openPisAtFvars cc.nFields cI b.nP
      = some (xfvs', Expr.instSeq xfvs' (cc.nFields - 1) resM) := by
    rw [ConLeche.stripPis_mkPisB _ hstripCI']; exact hlawX' _
  obtain ⟨xI, hxI⟩ : ∃ x, xfvs'[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxf'len]; exact hlcc)⟩
  have hfcsl' : fcs'[l]? = some (fcs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hfcs'len]; exact hlcc)]
    rfl
  have hxIdom : xI.fvarTypeD = Expr.instSeq (xfvs'.take l) (l - 1) (fcs'.getD l default).1 :=
    Verify.openPisAtFvars_domain cc.nFields hopM hstripCI' l xI (fcs'.getD l default) hxI hfcsl'
  have hTLlen : TL.length = tbs.length := by
    have := Expr.stripPis_length _ hmPeel; omega
  have hmPeel' : (fcs'.getD l default).1.stripPis TL.length
      = some (TL, Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
          (pinsS.getD (q₀ + i') default).lvls) ((srcAtE st p (q₀ + i')).2.2 ++ IDXS)) := by
    rw [hfcs' l hlcc, hTLlen]; exact hmPeel
  have hmMk : (fcs'.getD l default).1
      = ConLeche.mkPisB TL (Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
          (pinsS.getD (q₀ + i') default).lvls) ((srcAtE st p (q₀ + i')).2.2 ++ IDXS)) :=
    ConLeche.stripPis_mkPisB _ hmPeel'
  have hxfvs'Fv : ∀ a ∈ xfvs'.take l, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem (List.take_subset _ _ ha)
    obtain ⟨ty, hty2⟩ := ConLeche.openPisAtFvars_index _ _ _ hopM k a hk
    exact ⟨_, ty, hty2⟩
  have hxfvs'Le : (xfvs'.take l).length ≤ l - 1 + 1 := by
    rw [List.length_take]; omega
  have hxIMk : xI.fvarTypeD
      = ConLeche.mkPisB (ConLeche.instTeleSeq (xfvs'.take l) (l - 1) TL)
          (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length)
            (Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
              (pinsS.getD (q₀ + i') default).lvls)
              ((srcAtE st p (q₀ + i')).2.2 ++ IDXS))) := by
    rw [hxIdom, hmMk, ConLeche.instSeq_mkPisB _ _ _ _ hxfvs'Le]
  obtain ⟨mfvs, hmfvsLen, -, hlawM⟩ :=
    ConLeche.openPisAtFvars_mkPisB TL.length
      (ConLeche.instTeleSeq (xfvs'.take l) (l - 1) TL)
      (ConLeche.instTeleSeq_length _ _ _) (b.nP + l)
  have hopMl : ConLeche.openPisAtFvars TL.length xI.fvarTypeD (b.nP + l)
      = some (mfvs, Expr.instSeq mfvs (TL.length - 1)
          (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length)
            (Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
              (pinsS.getD (q₀ + i') default).lvls)
              ((srcAtE st p (q₀ + i')).2.2 ++ IDXS)))) := by
    rw [hxIMk]; exact hlawM _
  -- the minted domain's READING, as a Π-tower
  have hmfr := mintFieldRead S hi' hj hksJ (by rw [hty]; exact hccf) (by rw [hty]; exact hccb)
    hDsSc ψ hspine (by rw [hty]; exact hinstCI) (by rw [hnf]; exact hopM) hlF hxI
  rw [hCDJ.reflEntry _ l hnest hrefl hlF, AnnotTerm.instAll_mkPisAV] at hmfr
  have htlsLenψ := htlsLen ((pinsS.getD (q₀ + i') default).ψJ ψ)
  rw [IsBlockModel.tlss_getD hj] at htlsLenψ
  have hstripAV : ∀ (T : List (Nat × Nat × AnnotTerm)) (C : AnnotTerm),
      T.length = TL.length → stripPisAV TL.length (mkPisAV T C) = some (T, C) := by
    intro T C hT
    rw [← hT]
    exact stripPisAV_mkPisAV _ _
  have hdomReadM := denoteMeta_openPisAtFvars_dom TL.length hopMl hmfr
    (hstripAV _ _ (by rw [instTeleP_length, htlsLenψ, hTLlen]))
  have hbodyReadM := denoteMeta_openPisAtFvars TL.length hopMl hmfr
    (hstripAV _ _ (by rw [instTeleP_length, htlsLenψ, hTLlen]))
  -- (B) THE COPY SIDE: the stored domain, opened at the same tower
  obtain ⟨x', hx'⟩ : ∃ x', (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnF]; exact hlcc)⟩
  have hmkJ : dJ.tgts i' j l < kJ := by rw [← S.kEq]; exact hmem
  have hplen : q₀ + dJ.tgts i' j l < st.pins.length := by
    obtain ⟨-, -, h3⟩ := PD.seg
    rw [hgb, hgs] at h3; omega
  obtain ⟨fM, nIdxM, hfM, -, hauxFind, hfind3, hauxMem, -⟩ := R.groupCopyFormer hPD hplen
  have hfbC : Expr.fvarsBelow b.nP cbody' := by
    refine ConLeche.fvarsBelow_of_leaves fun lf hlf => ?_
    obtain ⟨k, hk⟩ := List.getElem?_of_mem (hcbl lf hlf)
    have hklt : k < b.nP := by
      rw [← hplenB]; exact (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨ty, hty2⟩ := hidxP k hklt
    rw [hk] at hty2
    have := (ConLeche.Expr.fvar.inj (Option.some.inj hty2)).1
    omega
  have hFlMk2 : (Fs'.getD l default).1
      = ConLeche.mkPisB TL (Expr.mkAppN (Expr.mkAppN
          (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param)) params) IDXS) :=
    ConLeche.stripPis_mkPisB _ hFlStrip
  have hxMk : x.fvarTypeD
      = ConLeche.mkPisB (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL)
          (Expr.instSeq (xfvs.take l) (l - 1 + TL.length)
            (Expr.mkAppN (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
              (params ++ IDXS))) := by
    rw [hxdom2, hFlMk2, mkAppN_append', ConLeche.instSeq_mkPisB _ _ _ _ hxfvsLe]
  obtain ⟨afvs2, hafvs2len, -, hlawA2⟩ :=
    ConLeche.openPisAtFvars_mkPisB TL.length (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL)
      (ConLeche.instTeleSeq_length _ _ _) (b.nP + l)
  have hopAg : ConLeche.openPisAtFvars TL.length x.fvarTypeD (b.nP + l)
      = some (afvs2, Expr.mkAppN
          (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
          (((params ++ IDXS).map (Expr.instSeq (xfvs.take l) (l - 1 + TL.length))).map
            (Expr.instSeq afvs2 (TL.length - 1)))) := by
    rw [hxMk, hlawA2 _, ConLeche.instSeq_mkAppN_const, ConLeche.instSeq_mkAppN_const]
  have her := ConLeche.normCtorValM_domErasedPi mp₁.base2.wf hnorm hbndC hop1 hop2 hfbC
    hopP' hopX' hx hx' hauxFind hopAg
  have hxpeel2 : x.fvarTypeD.stripPis TL.length
      = some (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL,
          Expr.instSeq (xfvs.take l) (l - 1 + TL.length)
            (Expr.mkAppN (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
              (params ++ IDXS))) := by
    rw [hxMk, show TL.length = (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL).length from
      (ConLeche.instTeleSeq_length _ _ _).symm]
    exact ConLeche.stripPis_mkPisB_self _ _
  obtain ⟨bs₁, body₁, hstrip₁, hlen₁, hdoms₁, hbody₁⟩ :=
    Expr.ErasedEq.stripPis_inv TL.length her hxpeel2
  have hbody₁head : body₁.getAppFn
      = Expr.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param) := by
    rw [ConLeche.instSeq_mkAppN_const] at hbody₁
    obtain ⟨hfn, -, -⟩ := ConLeche.ErasedEq.getApp hbody₁
    rw [Expr.getAppFn_mkAppN] at hfn
    exact erasedEq_const_invD hfn
  have hx'Mk : x'.fvarTypeD = ConLeche.mkPisB bs₁ body₁ := ConLeche.stripPis_mkPisB _ hstrip₁
  have hbs₁len : bs₁.length = TL.length := by
    rw [hlen₁, ConLeche.instTeleSeq_length]
  obtain ⟨cfvs2, hcfvs2len, -, hlawC⟩ :=
    ConLeche.openPisAtFvars_mkPisB TL.length bs₁ hbs₁len (b.nP + l)
  have hopC2 : ConLeche.openPisAtFvars TL.length x'.fvarTypeD (b.nP + l)
      = some (cfvs2, Expr.instSeq cfvs2 (TL.length - 1) body₁) := by
    rw [hx'Mk]; exact hlawC _
  obtain ⟨cfvs, cbodyC, hopC, hlenC, hdomC, hspineC⟩ := hCD.reflOpen ψ l x' hx' hkindA
  have hx'pb : x'.fvarTypeD.piBinders = (bs₁, body₁) := by
    rw [hx'Mk]; exact piBinders_mkPisB_of_head bs₁ hbody₁head
  have hlenC' : ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length = TL.length := by
    rw [hlenC, hx'pb, hbs₁len]
  rw [hlenC'] at hopC
  obtain ⟨hcfvsEq, hcbodyEq2⟩ := Prod.mk.inj (Option.some.inj (hopC.symm.trans hopC2))
  -- (C) the two openings' binder domains, up to annotations
  have hfvC : ∀ (k : Nat) (a : Expr), cfvs[k]? = some a → ∃ ty, a = Expr.fvar (b.nP + l + k) ty :=
    fun k a ha => ConLeche.openPisAtFvars_index _ _ _ hopC k a ha
  have hfvM : ∀ (k : Nat) (a : Expr), mfvs[k]? = some a → ∃ ty, a = Expr.fvar (b.nP + l + k) ty :=
    fun k a ha => ConLeche.openPisAtFvars_index _ _ _ hopMl k a ha
  have hxIpeel : xI.fvarTypeD.stripPis TL.length
      = some (ConLeche.instTeleSeq (xfvs'.take l) (l - 1) TL,
          Expr.instSeq (xfvs'.take l) (l - 1 + TL.length)
            (Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
              (pinsS.getD (q₀ + i') default).lvls)
              ((srcAtE st p (q₀ + i')).2.2 ++ IDXS))) := by
    rw [hxIMk, show TL.length = (ConLeche.instTeleSeq (xfvs'.take l) (l - 1) TL).length from
      (ConLeche.instTeleSeq_length _ _ _).symm]
    exact ConLeche.stripPis_mkPisB_self _ _
  have hxfEr : ∀ (k : Nat) (a₁ a₂ : Expr), (xfvs.take l)[k]? = some a₁ →
      (xfvs'.take l)[k]? = some a₂ → Expr.ErasedEq a₁ a₂ := by
    intro k a₁ a₂ h1 h2
    have hk1 : xfvs[k]? = some a₁ := by
      rw [List.getElem?_take] at h1
      split at h1
      · exact h1
      · exact nomatch h1
    have hk2 : xfvs'[k]? = some a₂ := by
      rw [List.getElem?_take] at h2
      split at h2
      · exact h2
      · exact nomatch h2
    obtain ⟨ty₁, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hop2 k a₁ hk1
    obtain ⟨ty₂, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hopM k a₂ hk2
    rfl
  have hxfLen : (xfvs.take l).length = (xfvs'.take l).length := by
    rw [List.length_take, List.length_take, hxf'len, hxflen]
  have hopenerEr : ∀ (k : Nat) (a m : Expr), cfvs[k]? = some a → mfvs[k]? = some m →
      Expr.ErasedEq a.fvarTypeD m.fvarTypeD := by
    intro k a m ha hm
    have hklt : k < TL.length := by
      rw [← hcfvs2len, ← hcfvsEq]
      exact (List.getElem?_eq_some_iff.mp ha).1
    have hb₁ : bs₁[k]? = some (bs₁.getD k default) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hbs₁len]; exact hklt)]
      rfl
    have hg₁ : (ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL)[k]?
        = some ((ConLeche.instTeleSeq (xfvs.take l) (l - 1) TL).getD k default) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [ConLeche.instTeleSeq_length]; exact hklt)]
      rfl
    have hm₁ : (ConLeche.instTeleSeq (xfvs'.take l) (l - 1) TL)[k]?
        = some ((ConLeche.instTeleSeq (xfvs'.take l) (l - 1) TL).getD k default) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [ConLeche.instTeleSeq_length]; exact hklt)]
      rfl
    have hda : a.fvarTypeD = Expr.instSeq (cfvs.take k) (k - 1) (bs₁.getD k default).1 := by
      rw [hcfvsEq] at ha ⊢
      exact Verify.openPisAtFvars_domain TL.length hopC2 hstrip₁ k a
        (bs₁.getD k default) ha hb₁
    have hdm : m.fvarTypeD = Expr.instSeq (mfvs.take k) (k - 1)
        ((ConLeche.instTeleSeq (xfvs'.take l) (l - 1) TL).getD k default).1 :=
      Verify.openPisAtFvars_domain TL.length hopMl hxIpeel k m _ hm hm₁
    have hmid : Expr.ErasedEq (bs₁.getD k default).1
        ((ConLeche.instTeleSeq (xfvs'.take l) (l - 1) TL).getD k default).1 := by
      refine (hdoms₁ k _ _ hb₁ hg₁).1.trans ?_
      rw [ConLeche.instTeleSeq_getD _ TL (l - 1) k hklt,
        ConLeche.instTeleSeq_getD _ TL (l - 1) k hklt]
      exact Expr.instSeq_erasedEq_args (xfvs.take l) (xfvs'.take l) (l - 1 + k)
        (Expr.ErasedEq.rfl _) hxfEr hxfLen
    rw [hda, hdm]
    refine Expr.instSeq_erasedEq_args (cfvs.take k) (mfvs.take k) (k - 1) hmid ?_ ?_
    · intro n a₁ a₂ h1 h2
      have hk1 : cfvs[n]? = some a₁ := by
        rw [List.getElem?_take] at h1
        split at h1
        · exact h1
        · exact nomatch h1
      have hk2 : mfvs[n]? = some a₂ := by
        rw [List.getElem?_take] at h2
        split at h2
        · exact h2
        · exact nomatch h2
      obtain ⟨ty₁, rfl⟩ := hfvC n a₁ hk1
      obtain ⟨ty₂, rfl⟩ := hfvM n a₂ hk2
      rfl
    · rw [List.length_take, List.length_take, hmfvsLen, hcfvsEq, hcfvs2len]
  refine ⟨?_, ?_⟩
  · -- the TELESCOPE conjunct
    rw [mutTlss_getD hGlt, IsBlockModel.tlss_getD hj, ← instTeleP_map]
    refine List.ext_getElem (by
      rw [List.length_map, List.length_map, instTeleP_length, hlenC', htlsLenψ, hTLlen]) ?_
    intro k hk hk'
    have hklt : k < TL.length := by
      rw [List.length_map, hlenC'] at hk; exact hk
    obtain ⟨a, ha⟩ : ∃ a, cfvs[k]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by rw [hcfvsEq, hcfvs2len]; exact hklt)⟩
    obtain ⟨m, hm⟩ : ∃ m, mfvs[k]? = some m :=
      ⟨_, List.getElem?_eq_getElem (by rw [hmfvsLen]; exact hklt)⟩
    have h1 := hdomC k a ha
    have h2 := R.crossUp ψ (b.nP + l + k) _ (hdomReadM k m hm)
    rw [denoteMeta_erasedEq (hopenerEr k a m ha hm) (b.nP + l + k)] at h1
    rw [h2] at h1
    have hEntry := Option.some.inj h1.symm
    have hkA : k < ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length := by
      rw [hlenC']; exact hklt
    have hkB : k < (instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) l
        ((dJ.tssF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l [])).length := by
      rw [instTeleP_length, htlsLenψ, ← hTLlen]; exact hklt
    have hA : ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).getD k default
        = ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [])[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkA, Option.getD_some]
    have hB : (instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) l
          ((dJ.tssF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l [])).getD k default
        = (instTeleP ((pinsS.getD (q₀ + i') default).Ds ψ) l
          ((dJ.tssF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l []))[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkB, Option.getD_some]
    rw [List.getElem_map, List.getElem_map, ← hA, ← hB]
    exact hEntry
  · -- the INDEX-EXPRESSION conjunct
    rw [mutEiss0_getD hGlt, IsBlockModel.Eiss_getD hj, IsBlockModel.tlss_getD hj]
    -- the MINTED body, as a spine at the components
    rw [AnnotTerm.instAll_mkAppN, List.map_append] at hbodyReadM
    have hmbShape : Expr.instSeq mfvs (TL.length - 1)
          (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length)
            (Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
              (pinsS.getD (q₀ + i') default).lvls)
              ((srcAtE st p (q₀ + i')).2.2 ++ IDXS)))
        = Expr.mkAppN (.const (dJ.memberName (dJ.tgts i' j l))
            (pinsS.getD (q₀ + i') default).lvls)
          ((((srcAtE st p (q₀ + i')).2.2.map
                (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length))).map
              (Expr.instSeq mfvs (TL.length - 1)))
            ++ ((IDXS.map (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length))).map
              (Expr.instSeq mfvs (TL.length - 1)))) := by
      rw [ConLeche.instSeq_mkAppN_const, ConLeche.instSeq_mkAppN_const, List.map_append,
        List.map_append]
    rw [hmbShape] at hbodyReadM
    obtain ⟨fa, vs, -, hspM, heqA⟩ := denoteMeta_mkAppN_inv hbodyReadM
    obtain ⟨vs₁, vs₂, rfl, hspP, hspE⟩ := DenoteMetaSpine.append_inv hspM
    have hPBlen : (paramBvarsAt dJ.nP (dJ.nP + l +
        ((dJ.tssF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l []).length)).length
        = dJ.nP := by simp [paramBvarsAt]
    have hvs₁len : ((paramBvarsAt dJ.nP (dJ.nP + l +
          ((dJ.tssF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l []).length)).map
        (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ)
          (l + ((dJ.tssF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l []).length))).length
        = vs₁.length := by
      rw [List.length_map, hPBlen, ← hspP.length, List.length_map, List.length_map, hDsnP]
    have hEisLenRefl : ((dJ.eissF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD l []).length
        = dJ.nIdxAt (dJ.tgts i' j l) := hCDJ.eisLenRefl _ l hnest hrefl hlF
    have hlenIDXm : ((IDXS.map (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length))).map
        (Expr.instSeq mfvs (TL.length - 1))).length = dJ.nIdxAt (dJ.tgts i' j l) := by
      rw [List.length_map, List.length_map, hIDXS, List.length_map, List.length_map, hidxsLen]
    obtain ⟨-, happ⟩ := AnnotTerm.mkAppN_inj heqA (by
      rw [List.length_append, List.length_append, hvs₁len, ← hspE.length, List.length_map,
        hEisLenRefl, hlenIDXm])
    obtain ⟨-, rfl⟩ := List.append_inj happ hvs₁len
    -- the COPY's stored body, and the two spines' arguments
    have hfvCfull : ∀ a ∈ cfvs, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty := by
      intro a ha
      obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
      obtain ⟨ty, hty2⟩ := hfvC k a hk
      exact ⟨_, ty, hty2⟩
    have hcArgs : cbodyC.getAppArgs
        = body₁.getAppArgs.map (Expr.instSeq cfvs (TL.length - 1)) := by
      rw [hcbodyEq2, ← hcfvsEq]
      exact ConLeche.os_instSeq_getAppArgs cfvs hfvCfull _ _
    have hgArgs : (Expr.instSeq (xfvs.take l) (l - 1 + TL.length)
          (Expr.mkAppN (.const (pinAtE st (q₀ + dJ.tgts i' j l)).aux (p.lps.map Level.param))
            (params ++ IDXS))).getAppArgs
        = (params ++ IDXS).map (Expr.instSeq (xfvs.take l) (l - 1 + TL.length)) := by
      rw [ConLeche.instSeq_mkAppN_const]
      simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append]
    obtain ⟨-, hlenArgs, hargsEq⟩ := ConLeche.ErasedEq.getApp hbody₁
    rw [hgArgs] at hlenArgs hargsEq
    have hmapGetD : ∀ (L : List Expr) (g : Expr → Expr) (n : Nat), n < L.length →
        (L.map g).getD n default = g (L.getD n default) := by
      intro L g n hn
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hn,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
      rfl
    have hlenPt : ((IDXS.map (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length))).map
          (Expr.instSeq mfvs (TL.length - 1))).length
        = (cbodyC.getAppArgs.drop b.nP).length := by
      simp only [List.length_map, List.length_drop, hcArgs, hlenArgs, List.length_append,
        hplenB]
      omega
    have hptEq : ∀ k, k < ((IDXS.map (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length))).map
          (Expr.instSeq mfvs (TL.length - 1))).length →
        Expr.ErasedEq
          (((IDXS.map (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length))).map
            (Expr.instSeq mfvs (TL.length - 1))).getD k default)
          ((cbodyC.getAppArgs.drop b.nP).getD k default) := by
      intro k hk
      have hkI : k < IDXS.length := by
        rw [List.length_map, List.length_map] at hk; exact hk
      have hlt : b.nP + k < body₁.getAppArgs.length := by
        rw [hlenArgs, List.length_map, List.length_append, hplenB]
        omega
      have hsplitG : ((params ++ IDXS).map
            (Expr.instSeq (xfvs.take l) (l - 1 + TL.length))).getD (b.nP + k) default
          = Expr.instSeq (xfvs.take l) (l - 1 + TL.length) (IDXS.getD k default) := by
        rw [hmapGetD _ _ (b.nP + k) (by rw [List.length_append, hplenB]; omega),
          List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hplenB]; omega),
          hplenB, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
      rw [getD_dropD, hcArgs, hmapGetD _ _ (b.nP + k) hlt,
        hmapGetD _ _ k (show k < (IDXS.map
            (Expr.instSeq (xfvs'.take l) (l - 1 + TL.length))).length from by
          rw [List.length_map]; exact hkI),
        hmapGetD _ _ k hkI]
      have hga := hargsEq (b.nP + k) hlt
      rw [hsplitG] at hga
      refine Expr.instSeq_erasedEq_args mfvs cfvs (TL.length - 1) ?_ ?_ ?_
      · exact (hga.trans (Expr.instSeq_erasedEq_args (xfvs.take l) (xfvs'.take l)
          (l - 1 + TL.length) (Expr.ErasedEq.rfl _) hxfEr hxfLen)).symm
      · intro n a₁ a₂ h1 h2
        obtain ⟨ty₁, rfl⟩ := hfvM n a₁ h1
        obtain ⟨ty₂, rfl⟩ := hfvC n a₂ h2
        rfl
      · rw [hmfvsLen, hcfvsEq, hcfvs2len]
    rw [hlenC'] at hspineC
    exact DenoteMetaSpine.unique hspineC
      (DenoteMetaSpine.erasedEq (R.crossUpSpine ψ (b.nP + l + TL.length) hspE) hlenPt hptEq)

/-! ## The ordinary field, THE RUN'S OWN NORMALISATION (task #315 L-B, DESIGN §U.78)

K.42's record — the kernel's `nestedOrdDomPairs`/`nestedOrdNorms` pair
— says that at every field of every copy constructor the record's
filter admits — ORDINARY, **or** with a target below `p.k`, i.e. at one
of the block's own MEMBERS (the kernel lane's widening of 2026-09-18,
DESIGN "THE `mintedAt` FIX, AND TWO MEASUREMENTS" (d), which this lane
requested) — the positivity normalisation of the MINTED domain returns
the STORED one.
Its two inversions (`nestedOrdDomPairs_mem`, `nestedOrdNorms_job`,
`ConLeche/Verify/Inductives/NestedCopyNorm.lean`) address the record
positionally, and every hypothesis they take is one of the kernel
walk's own lookups.  This theorem discharges all of them from the
run's own reads, at THIS pin, THIS constructor and THIS field:

* the pin's type, its `src` record and its `mkCopy` call are
  `PinData`'s (`ty`, `src`, `own`);
* the field kinds are K.26's table (`nestedPinKindsOk_inv` +
  `nestedPinKinds_get`), identified with the block's own
  classification through `auxStored_ctor_eq` (the stored constructor
  IS `ctorsA[b.ownOffset … + j]`) and `classifyMutualKinds_inv` — so
  the arm's `kindAt (mutKsOf kinds …) l = .ordinary`, or its target
  below `p.k`, IS the walk's own filter at `kf[l]?`;
* the container's member and its `j`-th constructor are `copyResid`'s;
* the STORED side's two openings are the constructors' stage's own
  (`MutualFormersFacts.CD`'s `opens`), so the walk's `xS` is the
  block's `xFvsF` at `l` — the arm's `x'` — by the openers'
  determinism;
* the environment is rewritten from the restore's spelling to the
  model's with `consNestedFormers_take_eq`, and `b.nP = p.nP` is
  `auxBlock_former`.

**The member travels as a variable.**  `J.lps` cannot be recovered
from the level assignment: `copyResid`'s clause equates two
`Level.substFn`s, which is a statement about VALUATIONS, not about the
name list, and two different `lps` lists can induce the same
substitution function.  So the member itself is a binder here, with
the two clauses that determine it — `J ∈ ci.members` and
`J.name = the pin's container` — which is exactly what a caller that
has just run `copyResid` holds; `containerInfo?_member_det` then
identifies it with the walk's `find?` answer inside the proof. -/

/-- **K.42 AT THE ARM'S OWN FIELD** (task #315 L-B): at a field `l` of
the copy's constructor `j` that the record's filter admits — ORDINARY,
or with a target at one of the block's own MEMBERS — the positivity
normalisation of the MINTED domain (the container's field at the pin's
components, before `replaceAllNested`) returns the block's own stored
domain, `xFvsF`'s field variable at `l`.

`hkindA` is the walk's filter, in the form the assembly holds it: both
disjuncts are read there (`Or.inl` on the `ordF`-LEFT arm, `Or.inr` on
the `ordF`-RIGHT arm at a member target), and the member-target
disjunct is what retired lane L-B's `NestedPinsShapeRunM` residual at
integration 3r. -/
theorem NestedPinsRun.copyOrdFLeftRun {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hK42 : ∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
      ConLeche.nestedOrdDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobs ∧
      ConLeche.nestedOrdNorms (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
      ws = jobs.map (·.2.2))
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hkindA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = .ordinary ∨
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    {ci : ContainerInfo} {J : ContainerMember}
    (hci : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (hJmem : J ∈ ci.members) (hJn : J.name = (pinsS.getD (q₀ + i') default).J)
    {cI : Expr}
    (hinstCI : Expr.instPis (Expr.instantiateLevelParams J.lps
      (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI)
    {xfvs' : List Expr} {restM : Expr}
    (hopM : ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM))
    {xI : Expr} (hxI : xfvs'[l]? = some xI)
    {x' : Expr} (hx' : (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x') :
    ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
        xI.fvarTypeD
      = .ok x'.fvarTypeD := by
  classical
  obtain ⟨jobs, ws, hpairs, hnorms, heqws⟩ := hK42
  have hnPb : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  -- the container's constructor record at this position
  obtain ⟨cc, J₂, ci₂, -, -, -, -, -, -, -, -, -, cA, -, -, -,
    hciP₂, hJmem₂, hJcc, -, hty, hnf, hJname₂, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hcA, hnF, -⟩ := R.copyResid SF S hPD hi' hj
  obtain rfl : ci = ci₂ := Option.some.inj (hci.symm.trans hciP₂)
  obtain rfl : J = J₂ :=
    ConLeche.containerInfo?_member_det hci hci rfl hJmem hJmem₂ (hJn.trans hJname₂.symm)
  -- the pin, and its records read at the elimination's own spelling
  have hqS : q₀ + i' < pinsS.length := by have := S.seg; omega
  have hqst : q₀ + i' < st.pins.length := by rw [← SF.pinsLen]; exact hqS
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hLv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have := congrArg Expr.getAppFn hpin
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at this
    exact (Expr.const.inj this).2
  rw [hJc] at hci hJn
  -- the member the walk's `find?` answers with IS the arm's
  obtain ⟨ciP, hciP, -, -, -, -, J₀, hfindJ₀, hJ₀n, cpy, hmkc, -, -⟩ := PD.own
  obtain rfl : ci = ciP := Option.some.inj (hci.symm.trans hciP)
  obtain rfl : J = J₀ :=
    ConLeche.containerInfo?_member_det hci hci rfl hJmem (List.mem_of_find?_eq_some hfindJ₀)
      (hJn.trans hJ₀n.symm)
  have hlvls : (srcAtE st p (q₀ + i')).2.1.length = J.lps.length := (ConLeche.mkCopy_inv hmkc).1
  -- K.26's kinds table at the pin, and the stored copy's constructor
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  rw [hkP] at hpairs
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hqst
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  have hcvE : acv = cA.1 := hcv
  have hnfE : acnF = cA.2 := hnf'
  -- the aux block's classification at that position
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv R.h.classify
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk, hcvE, hnfE]
  -- the field's kind, at the walk's spelling
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, tt⟩ := rt
  -- the walk's own filter at this field, from the arm's
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hnF, ← hnf]
    exact hlF
  have hwide : r = RecFieldKind.ordinary ∨ tt < p.k := by
    rcases hkindA with h0 | h0
    · refine Or.inl ?_
      have h1 : kindAt ksG l = RecFieldKind.ordinary := by rw [← hmutKs]; exact h0
      simpa only [kindAt, List.getD_eq_getElem?_getD, hrt, Option.getD_some] using h1
    · refine Or.inr ?_
      rw [mutTgts_getD hGlt hnFs, hmutKs] at h0
      simpa only [tgtAt, List.getD_eq_getElem?_getD, hrt, Option.getD_some] using h0
  -- the three telescopes: the MINTED one, and the STORED one's two stages
  have hnFeq : acnF = cAJ.2 := by rw [hnfE, hnF, hnf]
  have hcIw : Expr.instPis
      (Expr.instantiateLevelParams J.lps (srcAtE st p (q₀ + i')).2.1 cc.type)
      (srcAtE st p (q₀ + i')).2.2 = some cI := by
    rw [← hLv, ← hty]; exact hinstCI
  have hopMw : ConLeche.openPisAtFvars acnF cI p.nP = some (xfvs', restM) := by
    rw [hnFeq, ← hnPb]; exact hopM
  have hCD := R.h.CD _ _ hcA
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  have hopSw : ConLeche.openPisAtFvars p.nP acv.type 0
      = some (fvsPF (b.ownOffset (p.k + q₀ + i') + j), crest') := by
    rw [hcvE, ← hnPb]; exact hopP'
  have hopS2w : ConLeche.openPisAtFvars acnF crest' p.nP
      = some (xFvsF (b.ownOffset (p.k + q₀ + i') + j), xrestF (b.ownOffset (p.k + q₀ + i') + j)) := by
    rw [hnfE, ← hnPb]; exact hopX'
  -- the job, and the record's run at it
  have hmem := ConLeche.nestedOrdDomPairs_mem hpairs hqst PD.ty PD.src ha hkq hci hfindJ₀ hlvls
    hkfj hJcc hac hcIw hopMw hopSw hopS2w hrt hwide hxI hx'
  have hrun := ConLeche.nestedOrdNorms_job hnorms heqws hmem
  obtain ⟨henv, -⟩ :=
    ConLeche.consNestedFormers_take_eq R.haux R.hformers R.hstored p.k (by rw [R.hbk]; omega)
  rw [henv, ← hnPb] at hrun
  exact hrun

/-- **THE PIN TARGETS' POSITIVITY RUN, AT ONE FIELD** (task #315 L-B,
K.51): `copyOrdFLeftRun`'s twin at the fields K.42's filter leaves out —
a copy field the auxiliary block classified recursive or reflexive at a
target AT OR ABOVE `p.k`, i.e. at a MIMIC.  The addressing is the same
(the record's job list is `nestedOrdDomPairs` with the filter's other
branch), so the body is that lemma's: the pin's records at the
elimination's own spelling, K.26's kinds table at the pin, the aux
block's classification at the position, and the three telescopes.

What differs is the ANSWER.  At an ordinary or member target the stored
domain IS the normalisation of the minted one; at a pin target it is
the normalisation REWRITTEN — by the elimination's own
`replaceAllNested` at the FINAL state, which therefore mints nothing
(the two length equations).  So the conclusion carries the intermediate
term `w`: the container-headed normalisation, which is what the model
reads the target off, since the stored domain is headed by the MIMIC
and identifying the two is `pinLeaf` and circular. -/
theorem NestedPinsRun.copyOrdFRightPinRun {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hK51 : ∃ (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta))
        (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
      ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
      ConLeche.nestedPinDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobsP ∧
      ConLeche.nestedPinNorms (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobsP = .ok wsP ∧
      ConLeche.nestedPinRewrites env p st params pbs₀ jobsP wsP = true)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hkindP : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l ≠ .ordinary)
    (hpinT : ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    {ci : ContainerInfo} {J : ContainerMember}
    (hci : ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci)
    (hJmem : J ∈ ci.members) (hJn : J.name = (pinsS.getD (q₀ + i') default).J)
    {cI : Expr}
    (hinstCI : Expr.instPis (Expr.instantiateLevelParams J.lps
      (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI)
    {xfvs' : List Expr} {restM : Expr}
    (hopM : ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM))
    {xI : Expr} (hxI : xfvs'[l]? = some xI)
    {x' : Expr} (hx' : (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x') :
    ∃ (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta)) (w : Expr)
      (st' : ConLeche.ElimState),
      ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
      ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
          xI.fvarTypeD
        = .ok w ∧
      ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st w
        = .ok (x'.fvarTypeD, st') ∧
      st'.types.length = st.types.length ∧ st'.pins.length = st.pins.length := by
  classical
  obtain ⟨params, pbs₀, jobs, ws, hrwd, hpairs, hnorms, hrew⟩ := hK51
  have hnPb : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  -- the container's constructor record at this position
  obtain ⟨cc, J₂, ci₂, -, -, -, -, -, -, -, -, -, cA, -, -, -,
    hciP₂, hJmem₂, hJcc, -, hty, hnf, hJname₂, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hcA, hnF, -⟩ := R.copyResid SF S hPD hi' hj
  obtain rfl : ci = ci₂ := Option.some.inj (hci.symm.trans hciP₂)
  obtain rfl : J = J₂ :=
    ConLeche.containerInfo?_member_det hci hci rfl hJmem hJmem₂ (hJn.trans hJname₂.symm)
  -- the pin, and its records read at the elimination's own spelling
  have hqS : q₀ + i' < pinsS.length := by have := S.seg; omega
  have hqst : q₀ + i' < st.pins.length := by rw [← SF.pinsLen]; exact hqS
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hLv : (pinsS.getD (q₀ + i') default).lvls = (srcAtE st p (q₀ + i')).2.1 := by
    have := congrArg Expr.getAppFn hpin
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at this
    exact (Expr.const.inj this).2
  rw [hJc] at hci hJn
  -- the member the walk's `find?` answers with IS the arm's
  obtain ⟨ciP, hciP, -, -, -, -, J₀, hfindJ₀, hJ₀n, cpy, hmkc, -, -⟩ := PD.own
  obtain rfl : ci = ciP := Option.some.inj (hci.symm.trans hciP)
  obtain rfl : J = J₀ :=
    ConLeche.containerInfo?_member_det hci hci rfl hJmem (List.mem_of_find?_eq_some hfindJ₀)
      (hJn.trans hJ₀n.symm)
  have hlvls : (srcAtE st p (q₀ + i')).2.1.length = J.lps.length := (ConLeche.mkCopy_inv hmkc).1
  -- K.26's kinds table at the pin, and the stored copy's constructor
  obtain ⟨kindsP, hkP, hkPlen⟩ := ConLeche.nestedPinKindsOk_inv R.hkinds
  rw [hkP] at hpairs
  have hkqlt : q₀ + i' < kindsP.length := by rw [hkPlen]; exact hqst
  have hkq : kindsP[q₀ + i']? = some (kindsP[q₀ + i']'hkqlt) :=
    List.getElem?_eq_getElem hkqlt
  obtain ⟨a, ha, hkget⟩ := ConLeche.nestedPinKinds_get hkP hkq
  have ha' : stored[p.k + q₀ + i']? = some a := by
    rw [show p.k + q₀ + i' = p.k + (q₀ + i') from by omega]; exact ha
  obtain ⟨hactor, hall⟩ :=
    ConLeche.auxStored_ctor_eq R.haux R.hformers R.hctorsA R.h3 R.hstored ha'
  have hjlt : j < (dJ.ctorsM i').length := (List.getElem?_eq_some_iff.mp hj).1
  have hjA : j < a.ctors.length := by rw [hactor, ← S.ctorCount i' hi']; exact hjlt
  obtain ⟨ac, hac⟩ : ∃ c, a.ctors[j]? = some c := ⟨_, List.getElem?_eq_getElem hjA⟩
  obtain ⟨acv, acnP, acnF⟩ := ac
  obtain ⟨cA', hcA', hcv, -, hnf'⟩ := hall j _ hac
  have hcAeq : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
  rw [hcAeq] at hcv hnf'
  have hcvE : acv = cA.1 := hcv
  have hnfE : acnF = cA.2 := hnf'
  -- the aux block's classification at that position
  obtain ⟨hmapM, -, -, -⟩ := ConLeche.classifyMutualKinds_inv R.h.classify
  obtain ⟨ksG, hksG, hmk⟩ :=
    ConLeche.mapM_option_inv hmapM (b.ownOffset (p.k + q₀ + i') + j) cA hcA
  have hmutKs : mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j) = ksG := by
    show kinds.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hksG]; rfl
  have hkfj : (kindsP[q₀ + i']'hkqlt)[j]? = some ksG := by
    rw [hkget j acv acnP acnF hac, ← hmk, hcvE, hnfE]
  -- the field's kind, at the walk's spelling
  obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hlks : l < ksG.length := by rw [← hmutKs, hksLen, hcAnF]; exact hlF
  obtain ⟨rt, hrt⟩ : ∃ rt, ksG[l]? = some rt := ⟨_, List.getElem?_eq_getElem hlks⟩
  obtain ⟨r, tt⟩ := rt
  -- the walk's own filter at this field, from the arm's
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some, hnF, ← hnf]
    exact hlF
  have hpinF : r ≠ RecFieldKind.ordinary ∧ ¬ tt < p.k := by
    refine ⟨fun h0 => hkindP ?_, fun h0 => hpinT ?_⟩
    · rw [hmutKs]
      simpa only [kindAt, List.getD_eq_getElem?_getD, hrt, Option.getD_some] using h0
    · rw [mutTgts_getD hGlt hnFs, hmutKs]
      simpa only [tgtAt, List.getD_eq_getElem?_getD, hrt, Option.getD_some] using h0
  -- the three telescopes: the MINTED one, and the STORED one's two stages
  have hnFeq : acnF = cAJ.2 := by rw [hnfE, hnF, hnf]
  have hcIw : Expr.instPis
      (Expr.instantiateLevelParams J.lps (srcAtE st p (q₀ + i')).2.1 cc.type)
      (srcAtE st p (q₀ + i')).2.2 = some cI := by
    rw [← hLv, ← hty]; exact hinstCI
  have hopMw : ConLeche.openPisAtFvars acnF cI p.nP = some (xfvs', restM) := by
    rw [hnFeq, ← hnPb]; exact hopM
  have hCD := R.h.CD _ _ hcA
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  have hopSw : ConLeche.openPisAtFvars p.nP acv.type 0
      = some (fvsPF (b.ownOffset (p.k + q₀ + i') + j), crest') := by
    rw [hcvE, ← hnPb]; exact hopP'
  have hopS2w : ConLeche.openPisAtFvars acnF crest' p.nP
      = some (xFvsF (b.ownOffset (p.k + q₀ + i') + j), xrestF (b.ownOffset (p.k + q₀ + i') + j)) := by
    rw [hnfE, ← hnPb]; exact hopX'
  -- the job, and the record's run at it
  have hmem := ConLeche.nestedPinDomPairs_mem hpairs hqst PD.ty PD.src ha hkq hci hfindJ₀ hlvls
    hkfj hJcc hac hcIw hopMw hopSw hopS2w hrt hpinF hxI hx'
  -- the job's index, at which the run and the rewrite are read
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hmem
  obtain ⟨w, hwn, hrun⟩ := ConLeche.nestedPinNorms_job hnorms hn
  obtain ⟨st', hrep, htys, hpinsLen⟩ := ConLeche.nestedPinRewrites_job hrew hn hwn
  obtain ⟨henv, -⟩ :=
    ConLeche.consNestedFormers_take_eq R.haux R.hformers R.hstored p.k (by rw [R.hbk]; omega)
  rw [henv, ← hnPb] at hrun
  exact ⟨params, pbs₀, w, st', hrwd, hrun, hrep, htys, hpinsLen⟩
/-! ## The ordinary field, LEFT arm (task #315 L-B, DESIGN §U.44 (f))

`CopyCtorShape.ordF`'s left arm says a copy field the auxiliary block
classifies ORDINARY reads as the container's field domain instantiated
at the pin's components.  Two steps, in the order §U.44 (f) named:

* **the prune.**  `replaceAllNested_unchanged_or_aux` says the
  elimination's rewrite either returned its input or left a pin's
  auxiliary in the result — and a pin's auxiliary IS a member of the
  auxiliary block (`groupCopyFormer`).  So at a field whose REWRITTEN
  domain mentions no member the rewrite was the identity: the copy's
  given domain is the minted one, whose reading `mintFieldRead` names.
* **the normalisation.**  `normPosDomM`'s own first guard is that
  mention test, so at such a field the positivity normalisation is the
  identity too (`normCtorValM_domUnchanged`), and the copy's STORED
  domain reads as the given one.

What is left is the case the mention test fails on the REWRITTEN
domain while the STORED one is member-free — `whnf` DROPPED a member
mention (PLAN §4's B6, the λ-pin `(fun _ => Nat) (List T)`).  The arm
carries it as its second disjunct, stated on the block's own data: the
constructor type the stage was GIVEN has a field domain that mentions
a member.  Nothing weaker is available syntactically, and closing it
needs the rewrite's own interp law, not a reading law. -/

/-- **`CopyCtorShape.ordF`'s LEFT arm** (task #315 L-B): at a copy
field the auxiliary block classifies ordinary, the copy's recursive
flag is `false`, and its field domain READS as the container's
instantiated at the pin's components — unless the constructor type the
block was given mentions a member at that field, which the positivity
normalisation's `whnf` then dropped (PLAN §4's B6). -/
theorem NestedPinsRun.copyOrdFLeft {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ)
    {j : Nat} {cAJ : ConstantVal × Nat} (hj : (dJ.ctorsM i')[j]? = some cAJ)
    {l : Nat} (hlF : l < cAJ.2)
    (hordA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = .ordinary)
    (ψ : Name → Nat) :
    ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = false ∧
    (((mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l default
        = AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l
            (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l default)
      ∨ ∃ (fvs xFvs : List Expr) (crest xrest x : Expr),
          ConLeche.openPisAtFvars b.nP
              (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).cv.type 0
            = some (fvs, crest) ∧
          ConLeche.openPisAtFvars cAJ.2 crest b.nP = some (xFvs, xrest) ∧
          xFvs[l]? = some x ∧
          ConLeche.mentionsMember b.memberNames x.fvarTypeD = true) := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    -, -, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ := R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  obtain ⟨st₁, st₂, hrun, hpre, hmint⟩ := hfields l hlcc
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlA
  have hlks : l < (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).length := by
    obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
    rw [hksLen]; exact hlA
  -- the recursive flag is false at an ordinary kind
  have hrsFalse : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false
      = false := by
    rw [blkRss_getD hGlt, rsOf_getD (by rw [kindsOf, List.length_map]; exact hlks),
      kindsOf_getD', hordA]
    simp
  refine ⟨hrsFalse, ?_⟩
  -- the given type's two-stage opening, and the field's domain in it
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  obtain ⟨-, sorts, -, hCtor⟩ := R.h.runC _ _ hcA
  obtain ⟨hnorm, -, hbndC⟩ := ConLeche.checkMutualCtor_true_norm hCtor
  have hcvC : (b.ctors.getD (b.ownOffset (p.k + q₀ + i') + j) default).cv
      = ⟨cname, p.lps, closeTelescope pbs₀ 0 cbody'⟩ := by
    rw [List.getD_eq_getElem?_getD, hbc]; rfl
  rw [hcvC] at hnorm hbndC
  rw [hnF] at hnorm hopX'
  obtain ⟨fvsA, -, -, hlawA⟩ := ConLeche.openPisAtFvars_mkPisB b.nP pbs₀ hpbs₀len 0
  have hfvsA : fvsA = params := by
    have hlaw := hlawA o'
    rw [← ConLeche.stripPis_mkPisB _ hstripF] at hlaw
    exact (Prod.mk.inj (Option.some.inj (hlaw.symm.trans hopb))).1
  have hop1 : ConLeche.openPisAtFvars b.nP (closeTelescope pbs₀ 0 cbody') 0
      = some (params, cbody') := by
    rw [ConLeche.closeTelescope_eq_mkPisB pbs₀ 0 cbody' hpbs₀f, hpbs₀len, hlawA, hfvsA,
      ConLeche.instSeq_abstractRange_fvs b.nP params cbody' hcbb hplenB hidxP hcbl]
  obtain ⟨xfvs, hxflen, -, hlawX⟩ := ConLeche.openPisAtFvars_mkPisB cc.nFields Fs' hlenF b.nP
  obtain ⟨resB, hcb'⟩ : ∃ r, cbody'.stripPis cc.nFields = some (Fs', r) := ⟨_, hcb⟩
  have hop2 : ConLeche.openPisAtFvars cc.nFields cbody' b.nP
      = some (xfvs, Expr.instSeq xfvs (cc.nFields - 1) resB) := by
    rw [ConLeche.stripPis_mkPisB _ hcb']; exact hlawX resB
  obtain ⟨x, hx⟩ : ∃ x, xfvs[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxflen]; exact hlcc)⟩
  by_cases hm : ConLeche.mentionsMember b.memberNames x.fvarTypeD = true
  · -- the residue: the GIVEN constructor type mentions a member at this field
    exact Or.inr ⟨params, xfvs, cbody', _, x, by rw [hcvC]; exact hop1,
      by rw [hnf]; exact hop2, hx, hm⟩
  rw [Bool.not_eq_true] at hm
  refine Or.inl ?_
  -- the given opened domain, at the field's own cut
  have hstripC : (closeTelescope pbs₀ 0 cbody').stripPis (b.nP + cc.nFields)
      = some (pbs₀ ++ ConLeche.abstractTele 0 pbs₀.length 0 Fs',
          resB.abstractRange 0 pbs₀.length Fs'.length) := by
    rw [ConLeche.stripPis_mkPisB _ hcb']
    rw [show b.nP + cc.nFields = pbs₀.length + Fs'.length from by rw [hpbs₀len, hlenF]]
    exact ConLeche.closeTelescope_mkPisB_strip hpbs₀f
  have habs : (ConLeche.abstractTele 0 pbs₀.length 0 Fs')[l]?
      = some ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show l < (ConLeche.abstractTele 0 pbs₀.length 0 Fs').length from by
        rw [ConLeche.abstractTele_length, hlenF]; exact hlcc)]
    rfl
  have hxdom : x.fvarTypeD = Expr.instSeq (params ++ xfvs.take l) (b.nP + l - 1)
      ((ConLeche.abstractTele 0 pbs₀.length 0 Fs').getD l default).1 :=
    ConLeche.os_field_domain b.nP cc.nFields l
      (openPisAtFvars_add b.nP hop1 (by rw [Nat.zero_add]; exact hop2))
      hstripC hplenB hpbs₀len hx habs
  have hFsl : Fs'[l]? = some (Fs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenF]; exact hlcc)]
    rfl
  have hFlBnd : (Fs'.getD l default).1.looseBVarsBounded l = true := by
    have h := ConLeche.stripPis_binder_bounded cc.nFields hcb' hcbb l _ hFsl
    simpa using h
  have hFlLeaves : ∀ lf ∈ (Fs'.getD l default).1.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ params :=
    fun lf hlf => hcbl lf (ConLeche.stripPis_binder_leaves cc.nFields hcb' l _ hFsl lf hlf)
  have hxdom2 : x.fvarTypeD = Expr.instSeq (xfvs.take l) (l - 1) (Fs'.getD l default).1 := by
    rw [hxdom, ConLeche.abstractTele_getD 0 pbs₀.length Fs' 0 l (by rw [hlenF]; exact hlcc),
      Expr.instSeq_append, hplenB, show b.nP + l - 1 - b.nP = l - 1 from by omega, hpbs₀len]
    simp only [Nat.zero_add]
    rw [ConLeche.instSeq_abstractRange_fvs_at b.nP l params _ hFlBnd hplenB hidxP hFlLeaves]
  -- THE PRUNE: the rewrite left the domain alone
  have hmClosed : ConLeche.mentionsMember b.memberNames (Fs'.getD l default).1 = false :=
    ConLeche.mentionsMember_instSeq_false _ _ (by rw [← hxdom2]; exact hm)
  have hquiet : (Fs'.getD l default).1
      = Expr.instSeq (srcAtE st p (q₀ + i')).2.2 (dJ.nP - 1 + l)
          (Expr.instantiateLevelParams J.lps (pinsS.getD (q₀ + i') default).lvls
            (fcs.getD l default).1) := by
    rcases ConLeche.replaceAllNested_unchanged_or_aux _ hrun with heq | ⟨qq, hqqMem, hqqM⟩
    · exact heq
    · exfalso
      obtain ⟨qi, hqi⟩ := List.getElem?_of_mem (hpre.subset hqqMem)
      have hqiLt : qi < st.pins.length := (List.getElem?_eq_some_iff.mp hqi).1
      obtain ⟨-, -, -, -, -, -, -, hauxN⟩ := R.groupCopyFormer hPD hqiLt
      have hpinEq : pinAtE st qi = qq := Option.some.inj ((hPD _ hqiLt).pin.symm.trans hqi)
      rw [hpinEq] at hauxN
      have : ConLeche.mentionsMember b.memberNames (Fs'.getD l default).1 = true :=
        List.any_eq_true.mpr ⟨qq.aux, hauxN, hqqM⟩
      rw [hmClosed] at this; exact nomatch this
  -- the MINTED constructor's `l`-th opened field domain, and its reading
  obtain ⟨resM, hstripCI'⟩ : ∃ r, cI.stripPis cc.nFields = some (fcs', r) := ⟨_, hstripCI⟩
  have hfcs'len : fcs'.length = cc.nFields := Expr.stripPis_length _ hstripCI'
  obtain ⟨xfvs', hxf'len, -, hlawX'⟩ :=
    ConLeche.openPisAtFvars_mkPisB cc.nFields fcs' hfcs'len b.nP
  have hopM : ConLeche.openPisAtFvars cc.nFields cI b.nP
      = some (xfvs', Expr.instSeq xfvs' (cc.nFields - 1) resM) := by
    rw [ConLeche.stripPis_mkPisB _ hstripCI']; exact hlawX' _
  obtain ⟨xI, hxI⟩ : ∃ x, xfvs'[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxf'len]; exact hlcc)⟩
  have hfcsl' : fcs'[l]? = some (fcs'.getD l default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hfcs'len]; exact hlcc)]
    rfl
  have hxIdom : xI.fvarTypeD = Expr.instSeq (xfvs'.take l) (l - 1) (fcs'.getD l default).1 :=
    Verify.openPisAtFvars_domain cc.nFields hopM hstripCI' l xI (fcs'.getD l default) hxI hfcsl'
  -- the pin's components: scoped at the block's parameters, and read
  have hqst : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have hq : q₀ + i' < pinsS.length := by have := S.seg; omega
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hDsE : (pinsS.getD (q₀ + i') default).DsE = (srcAtE st p (q₀ + i')).2.2 := by
    have hA := congrArg Expr.getAppArgs hpin
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at hA
    exact hA
  have hspine := SF.pinDs _ hq ψ
  rw [hDsE] at hspine
  obtain ⟨-, hcl₀, hbt₀, hFD₀⟩ := R.former0
  obtain ⟨-, fvsS, oS, hopS, hsc⟩ := R.scoped
  obtain ⟨hbnd, hleaf⟩ := hsc _ (List.mem_of_getElem? PD.pin)
  have hws := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hopS hleaf ψ
  rw [PD.pinEq] at hbnd hws
  obtain ⟨-, hwsD⟩ := ConLeche.WScoped_of_mkAppN hws
  obtain ⟨-, hbndD⟩ := ConLeche.looseBVarsBounded_of_mkAppN hbnd
  have hDsSc : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2,
      Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true :=
    fun a ha => ⟨hwsD a ha, hbndD a ha⟩
  have hmfr := mintFieldRead S hi' hj hksJ (by rw [hty]; exact hccf) (by rw [hty]; exact hccb)
    hDsSc ψ hspine (by rw [hty]; exact hinstCI) (by rw [hnf]; exact hopM) hlF hxI
  -- the three domains: stored, given, minted — the same up to annotations
  obtain ⟨x', hx'⟩ : ∃ x', (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnF]; exact hlcc)⟩
  have herStored := ConLeche.normCtorValM_domUnchanged mp₁.base2.wf hnorm hbndC hop1 hop2
    hopP' hopX' hx hx' hm
  have hxfEr : ∀ (k : Nat) (a₁ a₂ : Expr), (xfvs.take l)[k]? = some a₁ →
      (xfvs'.take l)[k]? = some a₂ → Expr.ErasedEq a₁ a₂ := by
    intro k a₁ a₂ h1 h2
    have hk1 : xfvs[k]? = some a₁ := by
      rw [List.getElem?_take] at h1
      split at h1
      · exact h1
      · exact nomatch h1
    have hk2 : xfvs'[k]? = some a₂ := by
      rw [List.getElem?_take] at h2
      split at h2
      · exact h2
      · exact nomatch h2
    obtain ⟨ty₁, rfl⟩ := openPisAtFvars_index _ _ _ hop2 k a₁ hk1
    obtain ⟨ty₂, rfl⟩ := openPisAtFvars_index _ _ _ hopM k a₂ hk2
    rfl
  have hxfLen : (xfvs.take l).length = (xfvs'.take l).length := by
    rw [List.length_take, List.length_take, hxf'len, hxflen]
  have herGiven : Expr.ErasedEq x.fvarTypeD xI.fvarTypeD := by
    rw [hxdom2, hxIdom, hquiet, hfcs' l hlcc]
    exact Expr.instSeq_erasedEq_args (xfvs.take l) (xfvs'.take l) (l - 1)
      (Expr.ErasedEq.rfl _) hxfEr hxfLen
  have hread : denoteMeta mp₁.base2.acval (ConLeche.consMutualFormers fms env) ψ (b.nP + l)
      x'.fvarTypeD
      = some (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l
          ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD (dJ.nP + l) default).2.2) := by
    rw [denoteMeta_erasedEq (herStored.trans herGiven) (b.nP + l)]
    exact R.crossUp ψ (b.nP + l) _ hmfr
  -- the two sides, read off the data
  have hmapGetD : ∀ (L : List (Nat × Nat × AnnotTerm)) (n : Nat), n < L.length →
      (L.map (·.2.2)).getD n default = (L.getD n default).2.2 := by
    intro L n hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl
  have hlenDropA : (((dsF (b.ownOffset (p.k + q₀ + i') + j) ψ).drop b.nP)).length = cA.2 := by
    rw [List.length_drop, hCD.len ψ]; omega
  have hlenDropJ : (((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP)).length
      = cAJ.2 := by
    obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
    obtain ⟨-, -, hCDJ⟩ := hI.ctors i' j cAJ hI.memberLt hj
    rw [List.length_drop, hCDJ.len _]; omega
  rw [mutFss0_getD hGlt, shadowFs_getD hnFs,
    if_neg (show ¬ recAt b.nP (kindsOf (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)))
        (b.nP + l) from by
      intro hr
      obtain ⟨-, hcase⟩ := hr
      rw [Nat.add_sub_cancel_left, kindsOf_getD', hordA] at hcase
      rcases hcase with h | h <;> exact nomatch h),
    hmapGetD _ l (by rw [hlenDropA]; exact hlA), getD_dropD,
    IsBlockModel.Fss_getD hj, hmapGetD _ l (by rw [hlenDropJ]; exact hlF), getD_dropD]
  exact Option.some.inj ((hCD.domRead ψ l x' hx').symm.trans hread)


/-! ## The ordinary field's LEFT arm, READ (task #315 L-B, DESIGN §U.78)

`copyOrdFLeft` proves the arm's TERM equality at a field the
positivity `whnf` left alone, and carries the other case as its second
disjunct: the rewritten domain mentions a member the `whnf` then
DROPPED, and there the copy's stored domain is no longer the minted
one as a term.  It still READS the same, which is all the arm's
consumer wants — so this is the arm's semantic half, stated at EVERY
ordinary field, with no residue hypothesis.

The route is `normPosDomM`'s own reading law at the run
`copyOrdFLeftRun` names.  Its inputs are: the MINTED domain's reading
(`mintFieldRead`); the frame — the block's parameter context with the
earlier MINTED field readings on top, whose `CtxOk` is
`ctxOk_of_openers` over the first former's openers followed by the
minted constructor's; and the grading, which is the CONTAINER's own
(`IsBlockModel.ctor_okB`/`ctor_validV` at the pin's parameter frame,
`NestedPinGroupSyn.DsFit`) carried across the instantiation by
`wellDenoted_instAll` and its `AnnotValid` twin.  The output's reading
is then the run's own stored domain (`BlockCtorData.domRead` after
`crossUp`), and the arm's left-hand side is rewritten onto it by
`copyOrdFLeft`'s own tail. -/

/-! ## The ordinary/recursive field's reading, THE COMMON CORE
(task #315 L-B, DESIGN "the telescope the positivity `whnf` MAKES")

`copyOrdFLeftRead` and the `ordF`-RIGHT arm differ in TWO lines of
their proofs and in nothing else: where the run comes from, and how
the finished equation is packaged.  Everything between — the minted
constructor's opening, the pin's components scoped and read, the first
former's opened context, the CONTAINER's grading carried across the
instantiation, and the `CtxOk` tower over the block's parameter
openers and the earlier minted fields — never looks at the field's
KIND.  So it is one theorem, with the run as a hypothesis in the shape
`copyOrdFLeftRun` (and its `ordF`-right twin) deliver it.

It returns the GRADING of the stored domain's reading beside the
equation: `normPosDomM_reads` computes it, and `ordF`-right reads its
target's index fit off it (`leafSpineFit`), which is the one thing the
left arm never needed. -/

/-- **THE COPY FIELD'S READING, AT ANY KIND** (task #315 L-B): the
container's field domain instantiated at the pin's components and the
copy's STORED domain have the same interpretation at every prefix
fitting the container's own earlier domains — and the stored domain's
reading is GRADED there.  The positivity run is the hypothesis; the
arms supply it. -/
theorem NestedPinsRun.copyFieldReadCoreQ {pbs : List (Expr × ConLeche.BinderMeta)}
    {Q : Expr → Expr → Prop}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hrunAll : ∀ (ci : ContainerInfo) (J : ContainerMember) (cI : Expr) (xfvs' : List Expr)
        (restM xI x' : Expr),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci →
      J ∈ ci.members → J.name = (pinsS.getD (q₀ + i') default).J →
      Expr.instPis (Expr.instantiateLevelParams J.lps
        (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI →
      ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM) →
      xfvs'[l]? = some xI →
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' →
      ∃ w : Expr,
        ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
            (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
            xI.fvarTypeD
          = .ok w ∧ Q x' w)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp)
    (fs₁ : List V) (hfs : fs₁.length = l)
    (hfit : SpineFit (consList (((pinsS.getD (q₀ + i') default).Ds ψ).map (interp V ρp)) ρp)
      (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l) fs₁) :
    ∃ (x' w : Expr) (ea' : AnnotTerm),
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' ∧ Q x' w ∧
      denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ (b.nP + l) w
        = some ea' ∧
      interp V (consList fs₁ ρp)
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l
            (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l default))
        = interp V (consList fs₁ ρp) ea' ∧
      WellDenotedV V (consList fs₁ ρp) ea' := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    hqnMem, hqnPin, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ :=
    R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlA
  have hlks : l < (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).length := by
    obtain ⟨hksLen, -, -⟩ := R.h.ksJ _ _ hcA
    rw [hksLen]; exact hlA
  -- ==== the MINTED constructor, opened at its field binders ====
  obtain ⟨resM, hstripCI'⟩ : ∃ r, cI.stripPis cc.nFields = some (fcs', r) := ⟨_, hstripCI⟩
  have hfcs'len : fcs'.length = cc.nFields := Expr.stripPis_length _ hstripCI'
  obtain ⟨xfvs', hxf'len, -, hlawX'⟩ :=
    ConLeche.openPisAtFvars_mkPisB cc.nFields fcs' hfcs'len b.nP
  have hopM : ConLeche.openPisAtFvars cc.nFields cI b.nP
      = some (xfvs', Expr.instSeq xfvs' (cc.nFields - 1) resM) := by
    rw [ConLeche.stripPis_mkPisB _ hstripCI']; exact hlawX' _
  obtain ⟨xI, hxI⟩ : ∃ x, xfvs'[l]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hxf'len]; exact hlcc)⟩
  obtain ⟨x', hx'⟩ : ∃ x', (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.xLen, hnF]; exact hlcc)⟩
  -- ==== the pin: the components, scoped and read ====
  have hqst : q₀ + i' < st.pins.length := by
    rw [← SF.pinsLen]; have := S.seg; omega
  have hqS : q₀ + i' < pinsS.length := by have := S.seg; omega
  have PD := hPD _ hqst
  obtain ⟨hJc, hpinS⟩ := SF.pinRec _ _ PD.pin
  have hpin := PD.pinEq
  rw [hpinS] at hpin
  have hDsE : (pinsS.getD (q₀ + i') default).DsE = (srcAtE st p (q₀ + i')).2.2 := by
    have hA := congrArg Expr.getAppArgs hpin
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at hA
    exact hA
  have hspine := SF.pinDs _ hqS ψ
  rw [hDsE] at hspine
  obtain ⟨-, hcl₀, hbt₀, hFD₀⟩ := R.former0
  obtain ⟨hpinsE, fvsS, oS, hopS, hsc⟩ := R.scoped
  have hfvsS : fvsS = params :=
    congrArg Prod.fst (Option.some.inj (hopS.symm.trans hopb))
  obtain ⟨hbnd, hleafPin⟩ := hsc _ (List.mem_of_getElem? PD.pin)
  have hwsPin := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hopS hleafPin ψ
  rw [PD.pinEq] at hbnd hwsPin
  obtain ⟨-, hwsD⟩ := ConLeche.WScoped_of_mkAppN hwsPin
  obtain ⟨-, hbndD⟩ := ConLeche.looseBVarsBounded_of_mkAppN hbnd
  have hDsSc : ∀ a ∈ (srcAtE st p (q₀ + i')).2.2,
      Expr.WScoped b.nP a ∧ a.looseBVarsBounded 0 = true :=
    fun a ha => ⟨hwsD a ha, hbndD a ha⟩
  -- the minted constructor's scope and bounds
  have hwsCI : Expr.WScoped b.nP cI :=
    instPis_WScoped hinstCI
      (Expr.WScoped.of_not_hasFvar
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hccf))
      (fun x hx => (hDsSc x hx).1)
  have hbCI : cI.looseBVarsBounded 0 = true :=
    looseBVarsBounded_instPis _ _ _
      (by rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hccb)
      (fun a ha => (hDsSc a ha).2) hinstCI
  -- every field domain of the minted constructor, read
  have hmfr : ∀ l₀ : Nat, l₀ < cAJ.2 → ∀ y : Expr, xfvs'[l₀]? = some y →
      denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ (b.nP + l₀)
          (Expr.fvarTypeD y)
        = some (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l₀
            ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD (dJ.nP + l₀) default).2.2) :=
    fun l₀ hl₀ y hy =>
      mintFieldRead S hi' hj hksJ (by rw [hty]; exact hccf) (by rw [hty]; exact hccb)
        hDsSc ψ hspine (by rw [hty]; exact hinstCI) (by rw [hnf]; exact hopM) hl₀ hy
  -- ==== the first former's opened context ====
  obtain ⟨Γ₀, R₀, htele, O⟩ := opened_of (V := V) hopb hcl₀ hbt₀ (hFD₀.read ψ) (hFD₀.okTy ψ)
  have hΓeq : Γ₀ = (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse :=
    (PiTeleAV.unique htele
      (piTeleAV_mkPisAV_take (ppsF 0 ψ) (hFD₀.len ψ) (.sort (f₀.s.eval ψ)))).1
  have hΓlen : Γ₀.length = b.nP := htele.length
  rw [← hΓeq] at hsat
  -- the pin's components are graded at every frame satisfying that context
  obtain ⟨eaP, heaP, hokP⟩ := R.pinRead hpinsE hopS hsc hqst ψ
  rw [← hΓeq] at hokP
  rw [hpinS, hDsE] at heaP
  obtain ⟨fa, vs, -, hsp, hea⟩ := denoteMeta_mkAppN_inv heaP
  obtain rfl : vs = (pinsS.getD (q₀ + i') default).Ds ψ := DenoteMetaSpine.unique hsp hspine
  have hDsGr : ∀ ρ : Nat → V, Sat V Γ₀ ρ →
      ∀ d ∈ (pinsS.getD (q₀ + i') default).Ds ψ, WellDenoted V ρ d ∧ AnnotValid V ρ d := by
    intro ρ hρ d hd
    obtain ⟨hw, hv⟩ := hokP ρ hρ
    rw [hea] at hw hv
    exact ⟨wellDenoted_of_mkAppN_arg hw d hd, (AnnotValid.mkAppN_inv hv).2 d hd⟩
  -- ==== the container's block model at this member ====
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i' hi'
  have hmapGetD : ∀ (L : List (Nat × Nat × AnnotTerm)) (n : Nat), n < L.length →
      (L.map (·.2.2)).getD n default = (L.getD n default).2.2 := by
    intro L n hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl
  obtain ⟨-, -, hCDJ⟩ := hI.ctors i' j cAJ hI.memberLt hj
  have hlenDropJ : ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).drop dJ.nP).length
      = cAJ.2 := by
    rw [List.length_drop, hCDJ.len _]; omega
  have hFsLen : ((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).length = cAJ.2 :=
    hI.Fss_length hj _
  have hFsEntry : ∀ l₀, l₀ < cAJ.2 →
      ((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l₀ default
        = ((dJ.dsF i' j ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD (dJ.nP + l₀) default).2.2 := by
    intro l₀ hl₀
    rw [IsBlockModel.Fss_getD hj, hmapGetD _ l₀ (by rw [hlenDropJ]; exact hl₀), getD_dropD]
  -- ==== two pure kit facts: `instTele` commutes with `take`, and the
  -- `AnnotValid` twin of `wellDenoted_instAll` ====
  have hinstTeleTake : ∀ (ts : List AnnotTerm) (c n : Nat),
      (instTele ((pinsS.getD (q₀ + i') default).Ds ψ) c ts).take n
        = instTele ((pinsS.getD (q₀ + i') default).Ds ψ) c (ts.take n) := by
    intro ts
    induction ts with
    | nil => intro c n; simp [instTele]
    | cons t ts ih =>
      intro c n
      cases n with
      | zero => simp [instTele]
      | succ n => simp only [instTele, List.take_succ_cons, ih (c + 1) n]
  have hAVinstAll : ∀ (ds : List AnnotTerm) (fsv : List V) (ρ : Nat → V) (e : AnnotTerm),
      (∀ d ∈ ds, AnnotValid V ρ d) →
      (AnnotValid V (consList fsv (consList (ds.map (interp V ρ)) ρ)) e ↔
        AnnotValid V (consList fsv ρ) (AnnotTerm.instAll ds fsv.length e)) := by
    intro ds
    induction ds with
    | nil => intro fsv ρ e _; exact Iff.rfl
    | cons d ds ih =>
      intro fsv ρ e hds
      simp only [AnnotTerm.instAll, List.map_cons, consList_cons]
      rw [← ih fsv ρ (e.inst d (fsv.length + ds.length))
        (fun x hx => hds x (List.mem_cons_of_mem _ hx))]
      have hsh : shiftE (fsv.length + ds.length) 0
          (consList fsv (consList (ds.map (interp V ρ)) ρ)) = ρ := by
        have h0 := shiftE_consList (ds.map (interp V ρ)) ρ
        rw [List.length_map] at h0
        rw [shiftE_consList_add, h0]
      have hin := instE_consList (interp V ρ d) fsv (ds.map (interp V ρ)).length
        (consList (ds.map (interp V ρ)) ρ)
      rw [instE_consList', List.length_map] at hin
      rw [AnnotValid_inst (V := V) e d (fsv.length + ds.length)
        (consList fsv (consList (ds.map (interp V ρ)) ρ))
        (by rw [hsh]; exact hds d List.mem_cons_self), hsh, hin]
  -- ==== the grading of the minted field readings ====
  have hpinAt : ∀ n, (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
      srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt n = pinsS.getD n default :=
    fun _ => rfl
  have hDparams : (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
      srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).params ψ
      = ((ppsF 0 ψ).take b.nP).map (·.2.2) := rfl
  have hparSat : ∀ ρ₀ : Nat → V, Sat V Γ₀ ρ₀ →
      Sat V (dJ.params ((pinsS.getD (q₀ + i') default).ψJ ψ)).reverse
        (consList (((pinsS.getD (q₀ + i') default).Ds ψ).map (interp V ρ₀)) ρ₀) := by
    intro ρ₀ hρ₀
    have hfitP : SpineFit (fun jj => ρ₀ (jj + b.nP))
        ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
          srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).params ψ)
        ((List.range b.nP).reverse.map ρ₀) := by
      rw [hDparams]
      refine spineFit_of_sat_len ?_ ?_
      · have hlenP := hFD₀.len ψ
        simp only [List.length_map, List.length_reverse, List.length_range, List.length_take]
        omega
      · rw [consList_range_reverse, ← hΓeq]
        exact hρ₀
    have hDf := S.DsFit i' hi' ψ (fun jj => ρ₀ (jj + b.nP)) ((List.range b.nP).reverse.map ρ₀) hfitP
    rw [consList_range_reverse, hpinAt] at hDf
    have hs := sat_of_spineFit (Δ₀ := []) (Sat_nil (V := V) _) hDf
    rwa [List.append_nil] at hs
  have hgrade : ∀ l₀, l₀ < cAJ.2 → ∀ ρ : Nat → V,
      Sat V ((instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
          (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l₀)).reverse
        ++ Γ₀) ρ →
      WellDenotedV V ρ (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l₀
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l₀ default)) := by
    intro l₀ hl₀ ρ hρ
    have hTlen : (instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l₀)).length = l₀ := by
      rw [instTele_length, List.length_take, hFsLen]; omega
    have hAlen : ((instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l₀)).reverse).length
        = l₀ := by rw [List.length_reverse]; exact hTlen
    have hρ0 : Sat V Γ₀ (fun jj => ρ (jj + l₀)) := by
      have hd := Sat_drop hρ l₀
      rwa [List.drop_left' hAlen] at hd
    have hsatA : Sat V ((instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l₀)).reverse) ρ :=
      fun n Aa hn =>
        hρ n Aa (by rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp hn).1)]; exact hn)
    have hfsvlen : ((List.range l₀).reverse.map ρ).length = l₀ := by simp
    have hcons : consList ((List.range l₀).reverse.map ρ) (fun jj => ρ (jj + l₀)) = ρ :=
      consList_range_reverse l₀ ρ
    have hfitI : SpineFit (fun jj => ρ (jj + l₀))
        (instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
          (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l₀))
        ((List.range l₀).reverse.map ρ) :=
      spineFit_of_sat_len (by rw [hfsvlen, hTlen]) (by rw [hcons]; exact hsatA)
    have hfitF : SpineFit
        (consList (((pinsS.getD (q₀ + i') default).Ds ψ).map (interp V (fun jj => ρ (jj + l₀))))
          (fun jj => ρ (jj + l₀)))
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l₀)
        ((List.range l₀).reverse.map ρ) := by
      have h := (spineFit_instTele ((pinsS.getD (q₀ + i') default).Ds ψ) (fun jj => ρ (jj + l₀))
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l₀) []
        ((List.range l₀).reverse.map ρ)).mp (by
          simpa only [List.length_nil, consList_nil] using hfitI)
      simpa only [consList_nil] using h
    have hρp' := hparSat _ hρ0
    have hfok := (hI.ctor_okB hj hρp').1
    have hfvl := (hI.ctor_validV hj hρp').1
    have hw := fieldsOkB_getD hfok (by rw [hFsLen]; exact hl₀) hfitF
    have hv := fieldsValid_getD hfvl (by rw [hFsLen]; exact hl₀) hfitF
    refine ⟨?_, ?_⟩
    · have h1 := (wellDenoted_instAll ((pinsS.getD (q₀ + i') default).Ds ψ)
        ((List.range l₀).reverse.map ρ) (fun jj => ρ (jj + l₀))
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l₀ default)
        (fun d hd => (hDsGr _ hρ0 d hd).1)).mp hw
      rw [hfsvlen, hcons] at h1
      exact h1
    · have h1 := (hAVinstAll ((pinsS.getD (q₀ + i') default).Ds ψ)
        ((List.range l₀).reverse.map ρ) (fun jj => ρ (jj + l₀))
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l₀ default)
        (fun d hd => (hDsGr _ hρ0 d hd).2)).mp hv
      rw [hfsvlen, hcons] at h1
      exact h1
  -- ==== list kit, generically (the goals below carry `getD`s the
  -- rewrites would otherwise confuse with the block model's own) ====
  have hgetSome : ∀ (L : List AnnotTerm) (n : Nat), n < L.length →
      L[n]? = some (L.getD n default) := by
    intro L n hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl
  have htakeGetD : ∀ (L : List AnnotTerm) (n m : Nat), m < n →
      (L.take n).getD m default = L.getD m default := by
    intro L n m hm
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hm]
  have hrevdrop : ∀ (T : List AnnotTerm) (m : Nat),
      T.reverse.drop (T.length - m) = (T.take m).reverse := by
    intro T m
    have hsplit : T.reverse = (T.drop m).reverse ++ (T.take m).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [hsplit, List.drop_left' (by rw [List.length_reverse, List.length_drop])]
  have hdropRevP : ∀ (T B : List AnnotTerm) (n m : Nat), T.reverse.length = n →
      (T.reverse ++ B).drop (n + m) = B.drop m := by
    intro T B n m hT
    rw [← List.drop_drop, List.drop_left' hT]
  have hdropRevN : ∀ (T B : List AnnotTerm) (n m : Nat), T.length = n → m ≤ n →
      (T.reverse ++ B).drop (n - m) = (T.take m).reverse ++ B := by
    intro T B n m hT hm
    rw [List.drop_append_of_le_length (by rw [List.length_reverse, hT]; omega), ← hT, hrevdrop]
  -- ==== the opened frame's `CtxOk` at the minted domain ====
  have hwsxI : Expr.WScoped (b.nP + l) (Expr.fvarTypeD xI) :=
    openPisAtFvars_typeWScoped cc.nFields hopM hwsCI l xI hxI
  have hltXI := Expr.fvarLeaves_lt_of_wscoped hwsxI
  have hbxI : (Expr.fvarTypeD xI).looseBVarsBounded 0 = true := by
    have h := (openPisAtFvars_bounded cc.nFields hopM hbCI).2 _ (List.mem_of_getElem? hxI)
    simpa [Expr.fvarTypeD] using h
  have hcIleaf : ∀ lf ∈ cI.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ params := by
    intro lf hlf
    obtain ⟨dsI, hdsI⟩ := instPis_instPisAt _ _ _ hinstCI
    rcases instPisAt_leaves _ hdsI lf (Or.inr hlf) with h0 | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hccf)] at h0
      exact absurd h0 List.not_mem_nil
    · have hargs : a ∈ qn.pin.getAppArgs := by
        rw [hqnPin]
        simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append]
        exact ha
      have hmemPin : lf ∈ qn.pin.fvarLeaves := fvarLeaves_getAppArgs hargs lf hla
      have h1 := (hsc qn hqnMem).2 lf hmemPin
      rw [hfvsS] at h1
      exact h1
  have hleafXI : ∀ lf ∈ (Expr.fvarTypeD xI).fvarLeaves,
      Expr.fvar lf.1 lf.2 ∈ params ++ xfvs'.take l := by
    intro lf hlf
    have hxIfv : lf ∈ xI.fvarLeaves := by
      obtain ⟨ty, hty'⟩ := ConLeche.openPisAtFvars_index cc.nFields cI b.nP hopM l xI hxI
      rw [hty'] at hlf ⊢
      simp only [Expr.fvarTypeD] at hlf
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hlf
    rcases openPisAtFvars_leaves cc.nFields hopM lf
      (Or.inr ⟨xI, List.mem_of_getElem? hxI, hxIfv⟩) with h0 | h0
    · exact List.mem_append_left _ (hcIleaf lf h0)
    · obtain ⟨pos, hpos⟩ := List.getElem?_of_mem h0
      obtain ⟨ty, hty'⟩ := ConLeche.openPisAtFvars_index cc.nFields cI b.nP hopM pos _ hpos
      have hpl' : lf.1 = b.nP + pos := by
        have h1 := hty'
        simp only [Expr.fvar.injEq] at h1
        exact h1.1
      have hlt : lf.1 < b.nP + l := hltXI lf hlf
      have hpt : (xfvs'.take l)[pos]? = some (Expr.fvar lf.1 lf.2) := by
        rw [List.getElem?_take_of_lt (show pos < l from by omega)]
        exact hpos
      exact List.mem_append_right _ (List.mem_of_getElem? hpt)
  have hbdFvs : ∀ y ∈ params ++ xfvs'.take l,
      (Expr.fvarTypeD y).looseBVarsBounded 0 = true := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hy
      obtain ⟨-, -, hb2, -, -⟩ := O.var pos _ hpos
      exact hb2
    · have hy' : y ∈ xfvs' := List.mem_of_mem_take hy
      have h := (openPisAtFvars_bounded cc.nFields hopM hbCI).2 _ hy'
      simpa [Expr.fvarTypeD] using h
  have hLxI : Expr.LeavesBounded (Expr.fvarTypeD xI) := by
    intro lf hlf
    have h := hbdFvs _ (hleafXI lf hlf)
    simpa [Expr.fvarTypeD] using h
  have hTlenL : (instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
      (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l)).length = l := by
    rw [instTele_length, List.length_take, hFsLen]; omega
  have hArevlen : ((instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
      (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l)).reverse).length
      = l := by rw [List.length_reverse]; exact hTlenL
  have hCtx : CtxOk mp₁'.base2 ψ (b.nP + l)
      ((instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
        (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l)).reverse ++ Γ₀)
      (Expr.fvarTypeD xI) := by
    refine ctxOk_of_openers mp₁'.base2.acval_closed (fvs := params ++ xfvs'.take l)
      (Aa := fun i₀ => if i₀ < b.nP then Γ₀.getD (b.nP - 1 - i₀) default
        else AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) (i₀ - b.nP)
          (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD (i₀ - b.nP) default))
      (n := b.nP + l) ?_ ?_ ?_ ?_ hleafXI hltXI ?_ ?_
    · rw [List.length_append, hArevlen, hΓlen]; omega
    · -- the openers are indexed by position
      intro i₀ x hx
      by_cases hlt : i₀ < b.nP
      · rw [List.getElem?_append_left (by omega)] at hx
        obtain ⟨ty, hty'⟩ := ConLeche.openPisAtFvars_index b.nP f₀.cvTa.type 0 hopb i₀ x hx
        exact ⟨ty, by rw [hty', Nat.zero_add]⟩
      · rw [List.getElem?_append_right (by omega)] at hx
        have hlt2 : i₀ - params.length < l := by
          have h1 := (List.getElem?_eq_some_iff.mp hx).1
          rw [List.length_take] at h1; omega
        rw [List.getElem?_take_of_lt hlt2] at hx
        obtain ⟨ty, hty'⟩ :=
          ConLeche.openPisAtFvars_index cc.nFields cI b.nP hopM _ x hx
        exact ⟨ty, by rw [hty']; congr 1; omega⟩
    · -- the openers are well-scoped at the frame
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hx
        have hposlt : pos < b.nP := by
          have h1 := (List.getElem?_eq_some_iff.mp hpos).1
          omega
        obtain ⟨ty, hty'⟩ := ConLeche.openPisAtFvars_index b.nP f₀.cvTa.type 0 hopb pos x hpos
        have hsc' := openPisAtFvars_typeWScoped b.nP hopb
          (Expr.WScoped.of_not_hasFvar hcl₀) pos x hpos
        rw [hty'] at hsc' ⊢
        simp only [Expr.fvarTypeD, Nat.zero_add] at hsc' ⊢
        simp only [Expr.WScoped]
        exact ⟨by omega, hsc'⟩
      · obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hx
        have hposlt : pos < l := by
          have h1 := (List.getElem?_eq_some_iff.mp hpos).1
          rw [List.length_take] at h1; omega
        rw [List.getElem?_take_of_lt hposlt] at hpos
        obtain ⟨ty, hty'⟩ := ConLeche.openPisAtFvars_index cc.nFields cI b.nP hopM pos x hpos
        have hsc' := openPisAtFvars_typeWScoped cc.nFields hopM hwsCI pos x hpos
        rw [hty'] at hsc' ⊢
        simp only [Expr.fvarTypeD] at hsc' ⊢
        simp only [Expr.WScoped]
        exact ⟨by omega, hsc'⟩
    · -- the openers' annotations read to the context's entries
      intro i₀ x hx
      by_cases hlt : i₀ < b.nP
      · rw [if_pos hlt]
        rw [List.getElem?_append_left (by omega)] at hx
        exact O.doms i₀ x hx
      · rw [if_neg hlt]
        rw [List.getElem?_append_right (by omega)] at hx
        have hlt2 : i₀ - params.length < l := by
          have h1 := (List.getElem?_eq_some_iff.mp hx).1
          rw [List.length_take] at h1; omega
        rw [List.getElem?_take_of_lt hlt2] at hx
        have h := hmfr (i₀ - b.nP) (by omega) x (by rw [← hplenB]; exact hx)
        rw [show b.nP + (i₀ - b.nP) = i₀ from by omega] at h
        rw [h, hFsEntry (i₀ - b.nP) (by omega)]
    · -- the context's entries, positionally
      intro i₀ hi₀
      by_cases hlt : i₀ < b.nP
      · rw [if_pos hlt,
          List.getElem?_append_right (by rw [hArevlen]; omega), hArevlen,
          show b.nP + l - 1 - i₀ - l = b.nP - 1 - i₀ from by omega]
        exact hgetSome Γ₀ _ (by rw [hΓlen]; omega)
      · have hidx : i₀ - b.nP < l := by omega
        have hgetD : (instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
              (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l)).getD
                (i₀ - b.nP) default
            = AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) (i₀ - b.nP)
              (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD
                (i₀ - b.nP) default) := by
          rw [instTele_getD _ 0 _ (i₀ - b.nP) (by rw [List.length_take, hFsLen]; omega),
            Nat.zero_add, htakeGetD _ l (i₀ - b.nP) hidx]
        rw [if_neg hlt,
          List.getElem?_append_left (by rw [hArevlen]; omega),
          List.getElem?_reverse (by rw [hTlenL]; omega), hTlenL,
          show l - 1 - (b.nP + l - 1 - i₀) = i₀ - b.nP from by omega,
          hgetSome _ _ (by rw [hTlenL]; exact hidx), hgetD]
    · -- the entries are graded under the earlier ones
      intro i₀ hi₀ ρ hρ
      have hd := Sat_drop hρ (b.nP + l - i₀)
      by_cases hlt : i₀ < b.nP
      · rw [show b.nP + l - i₀ = l + (b.nP - i₀) from by omega,
          hdropRevP _ _ l (b.nP - i₀) hArevlen] at hd
        rw [if_pos hlt, show (fun jj => ρ (jj + (b.nP + l - 1 - i₀) + 1))
            = (fun jj : Nat => ρ (jj + (l + (b.nP - i₀)))) from by funext jj; congr 1; omega]
        exact O.okΓ i₀ hlt _ hd
      · rw [show b.nP + l - i₀ = l - (i₀ - b.nP) from by omega,
          hdropRevN _ _ l (i₀ - b.nP) hTlenL (by omega),
          hinstTeleTake _ 0 (i₀ - b.nP), List.take_take,
          show min (i₀ - b.nP) l = i₀ - b.nP from by omega] at hd
        rw [if_neg hlt, show (fun jj => ρ (jj + (b.nP + l - 1 - i₀) + 1))
            = (fun jj : Nat => ρ (jj + (l - (i₀ - b.nP)))) from by funext jj; congr 1; omega]
        exact hgrade (i₀ - b.nP) (by omega) _ hd
  -- ==== the run, and the reading law ====
  obtain ⟨w, hrun, hQ⟩ := hrunAll ci J cI xfvs' _ xI x' hciP hJmem hJname
    (by rw [hty]; exact hinstCI) (by rw [hnf]; exact hopM) hxI hx'
  obtain ⟨ea', hea', hokOut, heq⟩ := normPosDomM_readEq_of R.hμ mp₁' ψ F hrun hwsxI hbxI hLxI hCtx
    (hmfr l hlF xI hxI)
    (by
      have h := hgrade l hlF
      intro ρ hρ
      have h1 := h ρ hρ
      rw [hFsEntry l hlF] at h1
      exact h1)
  -- the frame: the theorem's own spine fits the instantiated telescope
  have hsatΔ : Sat V ((instTele ((pinsS.getD (q₀ + i') default).Ds ψ) 0
      (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l)).reverse ++ Γ₀)
      (consList fs₁ ρp) := by
    refine sat_of_spineFit hsat ?_
    have h := (spineFit_instTele ((pinsS.getD (q₀ + i') default).Ds ψ) ρp
      (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l) [] fs₁).mpr
      (by simpa only [consList_nil] using hfit)
    simpa only [List.length_nil, consList_nil] using h
  exact ⟨x', w, ea', hx', hQ, hea',
    by rw [hFsEntry l hlF]; exact heq (consList fs₁ ρp) hsatΔ,
    hokOut (consList fs₁ ρp) hsatΔ⟩

/-- **THE COPY'S FIELD READING, at a run whose output IS the stored
domain** (task #315 L-B): `copyFieldReadCoreQ` at `Q x' w := w =
x'.fvarTypeD` — the shape K.42's record has, where the positivity
normalisation of the minted domain is the stored one on the nose, so
the output's reading is the model's own `dsF` entry
(`BlockCtorData.domRead`, crossed up).  The `ordF`-LEFT arm and the two
member-target `ordF`-RIGHT arms read it. -/
theorem NestedPinsRun.copyFieldReadCore {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hrunAll : ∀ (ci : ContainerInfo) (J : ContainerMember) (cI : Expr) (xfvs' : List Expr)
        (restM xI x' : Expr),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci →
      J ∈ ci.members → J.name = (pinsS.getD (q₀ + i') default).J →
      Expr.instPis (Expr.instantiateLevelParams J.lps
        (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI →
      ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM) →
      xfvs'[l]? = some xI →
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' →
      ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
          xI.fvarTypeD
        = .ok x'.fvarTypeD)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp)
    (fs₁ : List V) (hfs : fs₁.length = l)
    (hfit : SpineFit (consList (((pinsS.getD (q₀ + i') default).Ds ψ).map (interp V ρp)) ρp)
      (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l) fs₁) :
    interp V (consList fs₁ ρp)
        (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l
          (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l default))
      = interp V (consList fs₁ ρp)
          (((dsF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD (b.nP + l) default).2.2) ∧
    WellDenotedV V (consList fs₁ ρp)
      (((dsF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD (b.nP + l) default).2.2) := by
  classical
  obtain ⟨x', w, ea', hx', hQ, hea', heq, hok⟩ :=
    R.copyFieldReadCoreQ (Q := fun x' w => w = x'.fvarTypeD) SF S hPD hi' hj hlF
      (fun ci J cI xfvs' restM xI x'' h1 h2 h3 h4 h5 h6 h7 =>
        ⟨x''.fvarTypeD, hrunAll ci J cI xfvs' restM xI x'' h1 h2 h3 h4 h5 h6 h7, rfl⟩)
      ψ ρp hsat fs₁ hfs hfit
  subst hQ
  -- the output's reading IS the run's own stored domain
  obtain ⟨_cc, _J, _ci, _cI, _cA, _cname, -, -, -, -, -, -, -, -, -, hcA, -, -⟩ :=
    R.ctorPair SF S hPD hi' hj
  have hCD := R.h.CD _ _ hcA
  have hcross := R.crossUp ψ (b.nP + l) _ hea'
  obtain rfl : ea'
      = ((dsF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD (b.nP + l) default).2.2 :=
    Option.some.inj (hcross.symm.trans (hCD.domRead ψ l x' hx'))
  exact ⟨heq, hok⟩

/-- **THE COPY'S FIELD READING AT A PIN TARGET** (task #315 L-B, K.51):
`copyFieldReadCoreQ` at the record's own answer — the positivity
normalisation of the minted domain is `w`, and the STORED domain is
`w`'s image under the elimination's own `replaceAllNested` at the final
state (which therefore mints nothing).

So what comes back is `w`'s reading, not the model's `dsF` entry: the
container's field domain, instantiated at the pin's components and read
at the copy's frame, IS the reading of `w`.  That is the term the arm
reads the target off — it is headed by the CONTAINER (the mimic appears
only after the rewrite), and identifying the mimic's leaf with the
container's is `pinLeaf`, which is downstream of this very shape. -/
theorem NestedPinsRun.copyFieldReadPin {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hrunAll : ∀ (ci : ContainerInfo) (J : ContainerMember) (cI : Expr) (xfvs' : List Expr)
        (restM xI x' : Expr),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci →
      J ∈ ci.members → J.name = (pinsS.getD (q₀ + i') default).J →
      Expr.instPis (Expr.instantiateLevelParams J.lps
        (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI →
      ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM) →
      xfvs'[l]? = some xI →
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' →
      ∃ (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta)) (w : Expr)
        (st' : ConLeche.ElimState),
        ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
        ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
            (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
            xI.fvarTypeD
          = .ok w ∧
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st w
          = .ok (x'.fvarTypeD, st') ∧ st'.pins.length ≤ st.pins.length)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp)
    (fs₁ : List V) (hfs : fs₁.length = l)
    (hfit : SpineFit (consList (((pinsS.getD (q₀ + i') default).Ds ψ).map (interp V ρp)) ρp)
      (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l) fs₁) :
    ∃ (x' w : Expr) (ea' : AnnotTerm) (params : List Expr)
      (pbs₀ : List (Expr × ConLeche.BinderMeta)) (st' : ConLeche.ElimState),
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' ∧
      ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
      ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st w
        = .ok (x'.fvarTypeD, st') ∧ st'.pins.length ≤ st.pins.length ∧
      (∀ (n : Nat) (bs : List (Expr × ConLeche.BinderMeta)) (res : Expr),
        w.stripPis n = some (bs, res) →
        ∀ bb ∈ bs, ConLeche.mentionsMember b.memberNames bb.1 = false) ∧
      denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ (b.nP + l) w
        = some ea' ∧
      interp V (consList fs₁ ρp)
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l
            (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l default))
        = interp V (consList fs₁ ρp) ea' ∧
      WellDenotedV V (consList fs₁ ρp) ea' := by
  classical
  obtain ⟨x', w, ea', hx', hQ, hea', heq, hok⟩ :=
    R.copyFieldReadCoreQ
      (Q := fun x' w => ∃ (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta))
        (st' : ConLeche.ElimState),
        ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st w
          = .ok (x'.fvarTypeD, st') ∧ st'.pins.length ≤ st.pins.length ∧
        ∀ (n : Nat) (bs : List (Expr × ConLeche.BinderMeta)) (res : Expr),
          w.stripPis n = some (bs, res) →
          ∀ bb ∈ bs, ConLeche.mentionsMember b.memberNames bb.1 = false)
      SF S hPD hi' hj hlF
      (fun ci J cI xfvs' restM xI x'' h1 h2 h3 h4 h5 h6 h7 => by
        obtain ⟨params, pbs₀, w, st', hrwd, hrun, hrep, hst⟩ :=
          hrunAll ci J cI xfvs' restM xI x'' h1 h2 h3 h4 h5 h6 h7
        exact ⟨w, hrun, params, pbs₀, st', hrwd, hrep, hst,
          fun n bs res hw =>
            ConLeche.normPosDomM_mkPisB_free hrun (ConLeche.stripPis_mkPisB n hw)⟩)
      ψ ρp hsat fs₁ hfs hfit
  obtain ⟨params, pbs₀, st', hrwd, hrep, hst, hfreeW⟩ := hQ
  exact ⟨x', w, ea', params, pbs₀, st', hx', hrwd, hrep, hst, hfreeW, hea', heq, hok⟩

/-! ## The `ordF`-RIGHT field's PIN TARGET, IDENTIFIED (task #315 L-B,
DESIGN "the backwards inversion")

At a field the auxiliary block classified `.recursive` at a target AT OR
ABOVE `p.k` — a MIMIC — the stored domain is headed by that target
member's constant, and the rewrite sent `w` there.  Read backwards that
identifies `w`: its head is a RECORDED CONTAINER, and the pin the fire
landed on is the block pin at the classification's own target index.

**The subject is `w` — the CONTAINER-headed normalisation of the minted
domain** — and nothing here is about a target's reading.  Three inputs,
each already a theorem:

* the CLASSIFICATION names the stored domain's head
  (`mutualOpenedOk_recHead`);
* `w` names no copy, because `w` READS at the members-only environment
  (`denoteMeta_head_ne_fresh`) and a copy is not stored there — no
  preservation property of the positivity walk is involved;
* the rewrite's backwards inversion
  (`replaceAllNested_container_head_stable`) then gives the container,
  the pin and the mimic, the last of which the block's `Nodup` member
  names turn into the pin's INDEX. -/

/-- **THE PIN TARGET, IDENTIFIED** (task #315 L-B): at an `ordF`-right
field whose copy the auxiliary block classified `.recursive` at a pin
target, the field's normalised minted domain `w` is a recorded
container's application, the target is the block pin `p.k + qq`, and
that pin's recorded application is `w`'s head at `w`'s own parameter
arguments. -/
theorem NestedPinsRun.copyOrdFRightPinCorr {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hpinT : ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    {params : List Expr} {pbs₀ : List (Expr × ConLeche.BinderMeta)} {w : Expr}
    {st' : ConLeche.ElimState} {xt : Expr}
    (hheadS : xt.getAppFn = Expr.const (mutualNameOf b.members3
        (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l))
      (b.lps.map Level.param))
    (hrep : ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st w
      = .ok (xt, st'))
    (hstable : st'.pins.length ≤ st.pins.length)
    {fvs : List Expr} {tsq : Nat}
    {ψ : Name → Nat} {t : Nat} {ea' : AnnotTerm}
    (hea' : denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ t
      (Expr.instSeq fvs tsq w) = some ea') :
    ∃ (I : Name) (lvls : List Level) (ci' : ConLeche.ContainerInfo) (qq : Nat),
      qq < st.pins.length ∧
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + qq ∧
      w.getAppFn = Expr.const I lvls ∧
      ConLeche.containerInfo? env I = some ci' ∧
      ci'.nP ≤ w.getAppArgs.length ∧
      (pinAtE st qq).pin = Expr.mkAppN (.const I lvls) (w.getAppArgs.take ci'.nP) ∧
      xt = Expr.mkAppN
        (Expr.mkAppN (.const (pinAtE st qq).aux (p.lps.map Level.param)) params)
        (w.getAppArgs.drop ci'.nP) := by
  classical
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinstCI,
    hcj, hcA, hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlA
  obtain ⟨-, -, htgtLt⟩ := R.h.ksJ _ _ hcA
  have htgtEq : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0
      = tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l := mutTgts_getD hGlt hnFs
  obtain ⟨ft, hft⟩ : ∃ ft, fms[tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l]?
      = some ft := ⟨_, List.getElem?_eq_getElem (htgtLt l)⟩
  obtain ⟨hnameT, -⟩ := R.h.memT _ _ hft
  have hmemNd : (fms.map (·.cvTa.name)).Nodup := by
    have h0 := R.hnd
    unfold ConLeche.MutualBlock.blockNames at h0
    rw [R.h.names]
    exact (List.nodup_append.mp (List.nodup_append.mp h0).1).1
  have htk : ¬ tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l < p.k := by
    rw [htgtEq] at hpinT; exact hpinT
  -- ==== `w` names no copy: it READS at the members-only environment ====
  have hne : ∀ g ∈ fms.take p.k, g.cvTa.name ≠ ft.cvTa.name := by
    intro g hg heq
    obtain ⟨s, hs⟩ := List.getElem?_of_mem hg
    have hslt : s < (fms.take p.k).length := (List.getElem?_eq_some_iff.mp hs).1
    have hsk : s < p.k := by rw [List.length_take] at hslt; omega
    rw [List.getElem?_take_of_lt hsk] at hs
    have hseq : s = tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l :=
      nodup_getElem?_inj hmemNd (a := ft.cvTa.name)
        (by rw [List.getElem?_map, hs, ← heq]; rfl)
        (by rw [List.getElem?_map, hft]; rfl)
    omega
  have hfindNone : (ConLeche.consMutualFormers (fms.take p.k) env).find? ft.cvTa.name = none := by
    rw [ConLeche.consMutualFormers_find?_of_ne hne]
    exact R.h.fresh _ _ hft
  have hfree : w.getAppFn ≠ Expr.const ft.cvTa.name (b.lps.map Level.param) := fun hc =>
    denoteMeta_head_ne_fresh hea' hfindNone
      (ConLeche.instSeq_getAppFn_const fvs tsq w hc)
  have hhead : xt.getAppFn = Expr.const ft.cvTa.name (b.lps.map Level.param) := by
    rw [hheadS, hnameT]
  -- ==== the rewrite, backwards ====
  obtain ⟨I, lvls, cv, caps, ci', qn, hfn, hfind, hci', hnP, hqm, hqp, hqe⟩ :=
    ConLeche.replaceAllNested_container_head_stable hrep hhead hfree hstable
  have hauxHead : xt.getAppFn = Expr.const qn.aux (p.lps.map Level.param) := by
    rw [hqe, Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN]
    rfl
  have hqaux : ft.cvTa.name = qn.aux := (ConLeche.Expr.const.inj (hhead.symm.trans hauxHead)).1
  -- ==== the pin's INDEX, off the block's `Nodup` member names ====
  obtain ⟨qq, hqq⟩ := List.getElem?_of_mem hqm
  have hqqLt : qq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
  have hpinAtE : pinAtE st qq = qn := Option.some.inj ((hPD qq hqqLt).pin.symm.trans hqq)
  obtain ⟨fM, nIdxM, hfM, hauxM, -, -, -, -⟩ := R.groupCopyFormer hPD hqqLt
  rw [hpinAtE] at hauxM
  have hnameEq : ft.cvTa.name = fM.cvTa.name := by rw [hauxM]; exact hqaux
  have hidx : tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = p.k + qq :=
    nodup_getElem?_inj hmemNd (a := ft.cvTa.name)
      (by rw [List.getElem?_map, hft]; rfl)
      (by rw [List.getElem?_map, hfM]; simp only [Option.map_some]; rw [hnameEq])
  exact ⟨I, lvls, ci', qq, hqqLt, by rw [htgtEq, hidx], hfn, hci', hnP,
    by rw [hpinAtE]; exact hqp, by rw [hpinAtE]; exact hqe⟩

omit R SF S in
/-- **A BLOCK FORMER'S INDEX ARGUMENTS FIT ITS INDEX TELESCOPE, AT
GENERAL PARAMETER ARGUMENTS AND A FREE FIT FRAME** (task #315 L-B):
`IsBlockModels.former_app_fit` with two generalisations, and both are
forced by a block PIN.

* the parameter arguments are FREE — a pin's container is applied to
  the pin's COMPONENTS, not to the block's parameter variables, so the
  index fit lands at the components' frame, which is what
  `TargetView.frame` is at a pin target;
* the FIT's frame `σ` is free of the READING's frame `ρ` — the copy's
  field reads one binder-depth down (under the constructor's earlier
  fields) while the target's telescope is read at the block's parameter
  frame.  The engine already separates them
  (`spineFit_of_wellDenoted_mkAppN_pis` takes `σ` and `ρ` apart), and
  the former's own value is closed, so nothing has to be transported. -/
theorem blockFormer_ids_fit_gen {env : Env} {m : EnvModel V env} {d : BlockModel V}
    (hreps : IsBlockModels m d) {ψ : Name → Nat} (hfT : FormersTyped m d ψ)
    {t : Nat} (ht : t < d.k) {σ ρ : Nat → V} {Ds Eis : List AnnotTerm}
    (hDl : Ds.length = d.nP) (hEl : Eis.length = d.nIdxAt t)
    (hwd : WellDenoted V ρ (AnnotTerm.mkAppN (m.acval (d.memberName t) ψ) (Ds ++ Eis))) :
    SpineFit (consList (Ds.map (interp V ρ)) σ) (d.IdsM t ψ) (Eis.map (interp V ρ)) := by
  obtain ⟨cvT, cvR, mI, rP, rules, ht'⟩ := hreps t ht
  have hfit := spineFit_of_wellDenoted_mkAppN_pis (C := .sort (d.w ψ)) (ds := d.ppsM t ψ)
    (σ := σ) (ρ := ρ) (fv := interp V σ (m.acval (d.memberName t) ψ))
    (fun d' hd' => ht'.former.bits ψ d' hd')
    (by rw [List.length_append, hDl, hEl, ht'.ppsM_length]; exact Nat.le_refl _)
    hwd (interp_closed (V := V) (m.cval_closedL _ ψ) _ _) (hfT t ht _)
  rw [List.length_append, hDl, hEl, ← ht'.ppsM_length ψ, List.take_length,
    ← List.take_append_drop d.nP (d.ppsM t ψ), List.map_append, List.map_append] at hfit
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
  have hlen₁ : as₁.length = (Ds.map (interp V ρ)).length := by
    rw [h1.length_eq, List.length_map, List.length_take, ht'.ppsM_length, List.length_map, hDl]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hlen₁.symm
  exact h2

/-- **THE PIN TARGET'S READING** (task #315 L-B, step (iv)): at an
`ordF`-right field at a pin target, the reading of `w` — the
container-headed normalisation of the minted domain — is the BLOCK
PIN's stored reading applied to the field's recorded index readings.

The subject is `w`'s READING; the shape it stands on is
`copyOrdFRightPinCorr`'s.  Four existing laws do the work and none of
them is new: `MutualCtorDataI.eisRead` (the copy's recorded index
expressions ARE the denotation spine of the stored domain's arguments
past the parameters — which is why no arity bookkeeping is needed),
`NestedPinSynFacts.pinDs` with `denoteMeta_lift` (the pin's components
read the same one binder-depth down), `DenoteMetaSpine.unique` at both
splits, and the group record's own level assignment
(`NestedPinGroupSyn.stored`) for the head. -/
theorem NestedPinsRun.copyOrdFRightPinRead {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hpinT : ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    {params : List Expr} {pbs₀ : List (Expr × ConLeche.BinderMeta)} {w : Expr}
    {st' : ConLeche.ElimState} {xt : Expr} {t : Nat} {Eis : List AnnotTerm}
    (hheadS : xt.getAppFn = Expr.const (mutualNameOf b.members3
        (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l))
      (b.lps.map Level.param))
    (hrwd : ConLeche.nestedRewriteData p st = some (params, pbs₀))
    (hrep : ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st w
      = .ok (xt, st'))
    (hstable : st'.pins.length ≤ st.pins.length)
    (hnIdx : ∀ q, q < pinsS.length →
      (fms.getD (p.k + q) default).nIdx = (pinsS.getD q default).nIdx)
    {fvs : List Expr} {tsq : Nat}
    (hallF : ∀ v ∈ fvs, ∃ (idx : Nat) (ty : Expr), v = Expr.fvar idx ty)
    {ψ : Name → Nat} {ea' : AnnotTerm}
    (heisRead : DenoteMetaSpine mp₁.base2.acval (ConLeche.consMutualFormers fms env) ψ
      (b.nP + t) ((Expr.instSeq fvs tsq xt).getAppArgs.drop b.nP) Eis)
    (hEisLen : Eis.length = mutualNIdxOf b.members3
      (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l))
    (hea' : denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ
      (b.nP + t) (Expr.instSeq fvs tsq w) = some ea')
    (ρp : Nat → V) (fs₁ : List V) (hfs : fs₁.length = t)
    (hok : WellDenoted V (consList fs₁ ρp) ea') :
    ∃ qq : Nat,
      ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 = p.k + qq ∧
      interp V (consList fs₁ ρp) ea'
        = (Eis.map (interp V (consList fs₁ ρp))).foldl SetTheory.app
            (interp V ρp ((nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
              ((fms.take p.k).map (·.cvTa.name)) ψ).EA (p.k + qq))) ∧
      SpineFit ((nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
            ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp (p.k + qq))
        ((nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
            ((fms.take p.k).map (·.cvTa.name)) ψ).Ids (p.k + qq))
        (Eis.map (interp V (consList fs₁ ρp))) := by
  classical
  obtain ⟨I, lvls, ci', qq, hqqLt, hidx, hfn, hci', hnP, hpinEq, hqe⟩ :=
    R.copyOrdFRightPinCorr SF S hPD hi' hj hlF hpinT hheadS hrep hstable hea'
  have hnPb : b.nP = p.nP := (ConLeche.auxBlock_former R.hb).1
  -- ==== the walk's parameters are the block's ====
  have hplen : params.length = b.nP := by
    unfold ConLeche.nestedRewriteData at hrwd
    obtain ⟨t₀, -, hrwd⟩ := Option.bind_eq_some_iff.mp hrwd
    obtain ⟨pr, hop, hrwd⟩ := Option.bind_eq_some_iff.mp hrwd
    obtain ⟨prs, o⟩ := pr
    obtain ⟨br, -, hrwd⟩ := Option.bind_eq_some_iff.mp hrwd
    obtain ⟨bs, o'⟩ := br
    have hrwd' : (some (prs, bs) : Option (List Expr × List (Expr × ConLeche.BinderMeta)))
        = some (params, pbs₀) := hrwd
    simp only [Option.some.injEq, Prod.mk.injEq] at hrwd'
    rw [hnPb, ← hrwd'.1]
    exact ConLeche.openPisAtFvars_len _ hop
  -- ==== the stored domain's arguments past the parameters ARE `w`'s indices ====
  have hargsX : xt.getAppArgs.drop b.nP = w.getAppArgs.drop ci'.nP := by
    rw [hqe, Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN]
    simp only [Expr.getAppArgs, List.nil_append]
    rw [List.drop_left' hplen]
  -- ==== the same one telescope deeper: opening maps the spine ====
  have hargsO : (Expr.instSeq fvs tsq xt).getAppArgs.drop b.nP
      = (Expr.instSeq fvs tsq w).getAppArgs.drop ci'.nP := by
    rw [ConLeche.instSeq_getAppArgs fvs hallF tsq xt,
      ConLeche.instSeq_getAppArgs fvs hallF tsq w, ← List.map_drop, ← List.map_drop, hargsX]
  have hfnO : (Expr.instSeq fvs tsq w).getAppFn = Expr.const I lvls :=
    ConLeche.instSeq_getAppFn_const fvs tsq w hfn
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hcc, hn, hty, hnf, hJname, hinstCI,
    hcj, hcA, hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlA
  have htgt : tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = p.k + qq := by
    rw [← mutTgts_getD hGlt hnFs]; exact hidx
  rw [hargsO] at heisRead
  -- ==== `w`'s own spine, split at the container's parameters ====
  have hwsp : Expr.instSeq fvs tsq w
      = Expr.mkAppN (.const I lvls) (Expr.instSeq fvs tsq w).getAppArgs := by
    rw [← hfnO]; exact (Expr.mkAppN_getApp _).symm
  rw [hwsp] at hea'
  obtain ⟨fa, vs, hfa, hspM, rfl⟩ := denoteMeta_mkAppN_inv hea'
  rw [← List.take_append_drop ci'.nP (Expr.instSeq fvs tsq w).getAppArgs] at hspM
  obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.append_inv hspM
  have hvs₂ : vs₂ = Eis :=
    DenoteMetaSpine.unique (R.crossUpSpine ψ (b.nP + t) hsp₂) heisRead
  -- ==== the components: the pin's own reading, one depth down ====
  have hqSq : qq < pinsS.length := by rw [SF.pinsLen]; exact hqqLt
  obtain ⟨hJsyn, hpinSyn⟩ := SF.pinRec _ _ (hPD qq hqqLt).pin
  have hDsEq : (pinsS.getD qq default).DsE = w.getAppArgs.take ci'.nP := by
    have h1 := congrArg Expr.getAppArgs (hpinSyn.symm.trans hpinEq)
    simp only [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.nil_append] at h1
    exact h1
  have hlvlsEq : (pinsS.getD qq default).lvls = lvls := by
    have h1 := congrArg Expr.getAppFn (hpinSyn.symm.trans hpinEq)
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at h1
    exact (ConLeche.Expr.const.inj h1).2
  have hJeq : (pinsS.getD qq default).J = I := by
    have h1 := congrArg Expr.getAppFn (hpinSyn.symm.trans hpinEq)
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn] at h1
    rw [hJsyn]
    exact (ConLeche.Expr.const.inj h1).1
  obtain ⟨hpinsE, fvsS, oS, hopS, hsc⟩ := R.scoped
  obtain ⟨-, hcl₀, hbt₀, hFD₀⟩ := R.former0
  obtain ⟨hbndQ, hleafQ⟩ := hsc _ (List.mem_of_getElem? (hPD qq hqqLt).pin)
  have hwsQ := WScoped_of_openers mp₁' hFD₀ hcl₀ hbt₀ hopS hleafQ ψ
  rw [hpinSyn] at hwsQ hbndQ
  obtain ⟨-, hwsDQ⟩ := ConLeche.WScoped_of_mkAppN hwsQ
  -- ==== the components carry no loose variable, so the opening skips them ====
  have hbndDs : ∀ a ∈ (pinsS.getD qq default).DsE, a.looseBVarsBounded 0 = true :=
    (ConLeche.looseBVarsBounded_of_mkAppN hbndQ).2
  have hDsEqO : (pinsS.getD qq default).DsE
      = (Expr.instSeq fvs tsq w).getAppArgs.take ci'.nP := by
    have hid : List.map (fun x => Expr.instSeq fvs tsq x) (pinsS.getD qq default).DsE
        = (pinsS.getD qq default).DsE := by
      have h1 := List.map_congr_left (l := (pinsS.getD qq default).DsE) (g := fun x => x)
        (fun a ha => ConLeche.instSeq_eq_self fvs tsq (hbndDs a ha))
      simpa using h1
    rw [ConLeche.instSeq_getAppArgs fvs hallF tsq w, ← List.map_take, ← hDsEq, hid]
  have hspQ : DenoteMetaSpine mp₁'.base2.acval
      (ConLeche.consMutualFormers (fms.take p.k) env) ψ (b.nP + t)
      ((Expr.instSeq fvs tsq w).getAppArgs.take ci'.nP)
      (((pinsS.getD qq default).Ds ψ).map (fun X => AnnotTerm.liftN t X 0)) := by
    have hbase := SF.pinDs _ hqSq ψ
    rw [hDsEqO] at hbase
    have hstep : ∀ (a : Expr) (v : AnnotTerm),
        a ∈ (Expr.instSeq fvs tsq w).getAppArgs.take ci'.nP →
        denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ b.nP
            (id a) = some v →
        denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ
            (b.nP + t) (id a) = some (AnnotTerm.liftN t v 0) := by
      intro a v ha hv
      have hl := denoteMeta_lift (acval := mp₁'.base2.acval)
        (env := ConLeche.consMutualFormers (fms.take p.k) env) (φ := ψ)
        mp₁'.base2.acval_closed (hwsDQ a (by rw [hDsEqO]; exact ha)) (b.nP + t) (by omega)
      simp only [id] at hv ⊢
      rw [hv] at hl
      simp only [Option.map_some, Nat.add_sub_cancel_left] at hl
      exact hl
    have hmm := DenoteMetaSpine.map_map (f := id) (g := id)
      (h := fun X => AnnotTerm.liftN t X 0) (by rw [List.map_id]; exact hbase) hstep
    rw [List.map_id] at hmm
    exact hmm
  have hvs₁ : vs₁ = ((pinsS.getD qq default).Ds ψ).map (fun X => AnnotTerm.liftN t X 0) :=
    DenoteMetaSpine.unique hsp₁ hspQ
  -- ==== the head: the block pin's own level assignment ====
  obtain ⟨q₀', kJ', i'', hqqEq, hi'', S'⟩ := SF.groupsAt dsR xFvsR qq hqSq ci' (by
    rw [hJeq]; exact hci')
  obtain ⟨cvQ, capsQ, -, -, -, -, hfindQ₀, -, hψQ₀⟩ := S'.stored i'' hi''
  have hfindQ : (ConLeche.consMutualFormers (fms.take p.k) env).find?
      (pinsS.getD qq default).J = some (.indInfo cvQ capsQ) := by
    rw [hqqEq]; exact hfindQ₀
  have hψQ : (pinsS.getD qq default).ψJ ψ
      = Level.substFn ψ cvQ.levelParams (pinsS.getD qq default).lvls := by
    rw [hqqEq]; exact hψQ₀ ψ
  have hfaEq : fa = mp₁'.base2.acval (pinsS.getD qq default).J
      ((pinsS.getD qq default).ψJ ψ) := by
    rw [hJeq] at hfindQ
    by_cases hlen : lvls.length
        = (ConLeche.ConstantInfo.indInfo cvQ capsQ).toConstantVal.levelParams.length
    · rw [denoteMeta_const hfindQ hlen] at hfa
      simp only [Option.some.injEq] at hfa
      rw [← hfa, hJeq, hψQ, hlvlsEq]
      rfl
    · exfalso
      simp [denoteMeta, hfindQ, hlen] at hfa
  -- ==== the head's value, and the components' lift ====
  have hhd : interp V (consList fs₁ ρp) fa = interp V ρp fa := by
    rw [hfaEq]
    exact interp_closed (V := V)
      (mp₁'.base2.cval_closedL (pinsS.getD qq default).J ((pinsS.getD qq default).ψJ ψ))
      (consList fs₁ ρp) ρp
  have hcomp : ((pinsS.getD qq default).Ds ψ).map
        ((interp V (consList fs₁ ρp)) ∘ (fun X => AnnotTerm.liftN t X 0))
      = ((pinsS.getD qq default).Ds ψ).map (interp V ρp) := by
    refine List.map_congr_left (fun X _ => ?_)
    show interp V (consList fs₁ ρp) (AnnotTerm.liftN t X 0) = interp V ρp X
    rw [← hfs]
    exact interp_liftN_consList X fs₁ ρp
  have hEA : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ).EA (p.k + qq)
      = AnnotTerm.mkAppN (mp₁'.base2.acval (pinsS.getD qq default).J
          ((pinsS.getD qq default).ψJ ψ)) ((pinsS.getD qq default).Ds ψ) := by
    show targetRead mp₁'.base2.acval ((fms.take p.k).map (·.cvTa.name)) pinsS b.nP p.k ψ
        (p.k + qq) = _
    rw [targetRead_of_pin (by omega : ¬ p.k + qq < p.k), Nat.add_sub_cancel_left]
  -- ==== the INDEX FIT: the container former's own index telescope ====
  obtain ⟨cvT'', cvR'', mI'', rP'', rules'', hI'', -⟩ := S'.rep i'' hi''
  have hmemName : (pinsS.getD qq default).J = (blockOf mp.base2 ci').memberName i'' := by
    rw [hqqEq]; exact hI''.member.symm
  have hDl : vs₁.length = (blockOf mp.base2 ci').nP := by
    rw [hvs₁, List.length_map, hqqEq]; exact S'.pinDsLen i'' hi'' ψ
  obtain ⟨fM, nIdxM, hfM, -, -, -, -, -⟩ := R.groupCopyFormer hPD hqqLt
  have hElen : vs₂.length = (blockOf mp.base2 ci').nIdxAt i'' := by
    rw [hvs₂, hEisLen, htgt]
    obtain ⟨-, hnI⟩ := R.h.memT _ _ hfM
    rw [hnI, show fM = fms.getD (p.k + qq) default from by
      rw [List.getD_eq_getElem?_getD, hfM]; rfl, hnIdx qq hqSq, hqqEq]
    exact S'.pinNIdx i'' hi''
  have hwdA : WellDenoted V (consList fs₁ ρp)
      (AnnotTerm.mkAppN (mp₁'.base2.acval ((blockOf mp.base2 ci').memberName i'')
        ((pinsS.getD qq default).ψJ ψ)) (vs₁ ++ vs₂)) := by
    rw [← hmemName, ← hfaEq]; exact hok
  have hfitFull := blockFormer_ids_fit_gen (m := mp₁'.base2) S'.reps
    (S'.typed ((pinsS.getD qq default).ψJ ψ)) (t := i'') (by rw [S'.kEq]; exact hi'')
    (σ := ρp) (ρ := consList fs₁ ρp) hDl hElen hwdA
  rw [hvs₁, hvs₂, List.map_map, hcomp] at hfitFull
  refine ⟨qq, hidx, ?_, ?_⟩
  · rw [interp_mkAppN_foldl, List.map_append, List.foldl_append, hvs₁, hvs₂, List.map_map,
      hhd, hcomp, hEA, interp_mkAppN_foldl, ← hfaEq]
  · have hIds : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).Ids (p.k + qq)
        = (blockOf mp.base2 ci').IdsM i'' ((pinsS.getD qq default).ψJ ψ) := by
      show (if p.k + qq < p.k then _ else (pinsS.getD (p.k + qq - p.k) default).Ids ψ) = _
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      have h : ((pinsS.getD (q₀' + i'') default).Ids ψ)
          = (blockOf mp.base2 ci').IdsM i''
            ((pinsS.getD (q₀' + i'') default).ψJ ψ) := by
        have hpps : (pinsS.getD (q₀' + i'') default).pps
            = (blockOf mp.base2 ci').ppsM i'' := S'.pinPps i'' hi''
        have hnp : (pinsS.getD (q₀' + i'') default).nPJ
            = (blockOf mp.base2 ci').nP := S'.pinNP i'' hi''
        unfold PinSyn.Ids
        rw [hpps, hnp]
        rfl
      rw [← hqqEq] at h
      exact h
    have hfr : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp (p.k + qq)
        = consList (((pinsS.getD qq default).Ds ψ).map (interp V ρp)) ρp := by
      rw [TargetView.frame_of_pin _ _ (by omega : ¬ p.k + qq < p.k)]
      show consList (((pinsS.getD (p.k + qq - p.k) default).Ds ψ).map (interp V ρp)) ρp = _
      rw [Nat.add_sub_cancel_left]
    rw [hIds, hfr]
    exact hfitFull

/-- **`CopyCtorShape.ordF`'s RIGHT arm AT A PIN TARGET** (task #315 L-B,
step (iv) assembled): at a container-ordinary field the auxiliary block
classified `.recursive` at a target AT OR ABOVE `p.k` — a MIMIC — the
copy's entry is the BLOCK PIN's stored reading applied to the copy's
index expressions, and those fit the pin's index telescope at the pin's
frame.

**The member arm's twin, and every step has a counterpart.**  Where
`copyOrdFRightReadM` reads the target off `BlockCtorData.recEntry` and
gets its fit from `leafSpineFit` (a block member's LEAF applied to the
parameter variables), this arm reads it off the rewrite's backwards
inversion (`copyOrdFRightPinCorr`) and its reading
(`copyOrdFRightPinRead`), and gets the fit from
`blockFormer_ids_fit_gen` — because at a pin the head is the
CONTAINER's reading applied to the pin's COMPONENTS, not a leaf applied
to parameter variables.

The left-hand side is `copyFieldReadPin`'s: the container's field domain
instantiated at the pin's components reads as `w`, the CONTAINER-headed
normalisation, which is where the target is read off (the stored domain
is headed by the mimic, and identifying the two is `pinLeaf`). -/
theorem NestedPinsRun.copyOrdFRightReadP {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hrunAll : ∀ (ci : ContainerInfo) (J : ContainerMember) (cI : Expr) (xfvs' : List Expr)
        (restM xI x' : Expr),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci →
      J ∈ ci.members → J.name = (pinsS.getD (q₀ + i') default).J →
      Expr.instPis (Expr.instantiateLevelParams J.lps
        (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI →
      ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM) →
      xfvs'[l]? = some xI →
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' →
      ∃ (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta)) (w : Expr)
        (st' : ConLeche.ElimState),
        ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
        ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
            (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
            xI.fvarTypeD
          = .ok w ∧
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st w
          = .ok (x'.fvarTypeD, st') ∧ st'.pins.length ≤ st.pins.length)
    (hkA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.recursive)
    (hpinT : ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    (hnIdx : ∀ q, q < pinsS.length →
      (fms.getD (p.k + q) default).nIdx = (pinsS.getD q default).nIdx)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp) :
    EntryRead
      (nestedTV b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ)
      dJ ((pinsS.getD (q₀ + i') default).ψJ ψ) ((pinsS.getD (q₀ + i') default).Ds ψ)
      (fun l => ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
      ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) [])
      ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []) ρp i' j l := by
  classical
  obtain ⟨_cc, _J, _ci, _cI, cA, _cname, -, -, -, -, -, hnf, -, -, -, hcA, -, hnF⟩ :=
    R.ctorPair SF S hPD hi' hj
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hlcc : l < _cc.nFields := by rw [← hnf]; exact hlF
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  -- the copy's telescope is EMPTY at a finitary recursive field
  have htls : ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
      = [] := by
    rw [mutTlss_getD hGlt, hCD.tssNone ψ l (by rw [hkA]; exact fun h => nomatch h)]
  have hEis : ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
      = (eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [] := by
    rw [mutEiss0_getD hGlt]
  intro Z hZ
  intro fs₁ hfs hfit
  -- the reading of the CONTAINER's field domain, and the pin it lands on
  obtain ⟨x', w, ea', params, pbs₀, st', hx', hrwd, hrep, hstable, -, hea', heq, hok⟩ :=
    R.copyFieldReadPin SF S hPD hi' hj hlF hrunAll ψ ρp hsat fs₁ hfs hfit
  -- the CLASSIFICATION names the stored domain's head, and its index readings
  obtain ⟨crest', hopP', hopX'⟩ := hCD.opens
  obtain ⟨-, hopen, -⟩ := R.h.ksJ _ _ hcA
  obtain ⟨qq, hidx, hread, hfitI⟩ :=
    R.copyOrdFRightPinRead SF S hPD hi' hj hlF hpinT
      (mutualOpenedOk_recHead hopen hopP' hopX' hx' hkA) hrwd hrep hstable hnIdx
      (fvs := []) (tsq := 0) (fun _ hv => nomatch hv)
      (hCD.eisRead ψ l x' hx' hkA) (hCD.eisLen ψ l hkA hlA) hea' ρp fs₁ hfs hok.1
  simp only [htls, hEis]
  rw [slotSet_nil]
  have hfitZ : SpineFit
      ((nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp
        (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0))
      ((nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ).Ids
        (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0))
      (((eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).map
        (interp V (consList fs₁ ρp))) := by
    rw [hidx]; exact hfitI
  rw [hZ _ hfitZ]
  simp only [hidx]
  rw [← interp_instAll _ fs₁ ρp _, hfs, heq, hread]
/-- **`CopyCtorShape.ordF`'s LEFT arm, SEMANTICALLY** (task #315 L-B):
at every field the auxiliary block classifies ordinary, the copy's
STORED field domain and the CONTAINER's field domain instantiated at
the pin's components have the same interpretation at every prefix
fitting the container's own earlier domains.  The reading is
`copyFieldReadCore`'s; K.42's run is what this arm brings to it. -/
theorem NestedPinsRun.copyOrdFLeftRead {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    (hK42 : ∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
      ConLeche.nestedOrdDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobs ∧
      ConLeche.nestedOrdNorms (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
      ws = jobs.map (·.2.2))
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hordA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = .ordinary)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp)
    (fs₁ : List V) (hfs : fs₁.length = l)
    (hfit : SpineFit (consList (((pinsS.getD (q₀ + i') default).Ds ψ).map (interp V ρp)) ρp)
      (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).take l) fs₁) :
    interp V (consList fs₁ ρp)
        (((mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l default)
      = interp V (consList fs₁ ρp)
          (AnnotTerm.instAll ((pinsS.getD (q₀ + i') default).Ds ψ) l
            (((dJ.Fss i' ((pinsS.getD (q₀ + i') default).ψJ ψ)).getD j []).getD l default)) := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    hqnMem, hqnPin, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ :=
    R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlA
  have hmapGetD : ∀ (L : List (Nat × Nat × AnnotTerm)) (n : Nat), n < L.length →
      (L.map (·.2.2)).getD n default = (L.getD n default).2.2 := by
    intro L n hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl
  have hlenDropA : (((dsF (b.ownOffset (p.k + q₀ + i') + j) ψ).drop b.nP)).length = cA.2 := by
    rw [List.length_drop, hCD.len ψ]; omega
  have hcore := R.copyFieldReadCore SF S hPD hi' hj hlF
    (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
      R.copyOrdFLeftRun SF S hPD hK42 hi' hj hlF (Or.inl hordA) h1 h2 h3 h4 h5 h6 h7)
    ψ ρp hsat fs₁ hfs hfit
  rw [mutFss0_getD hGlt, shadowFs_getD hnFs,
    if_neg (show ¬ recAt b.nP (kindsOf (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)))
        (b.nP + l) from by
      intro hr
      obtain ⟨-, hcase⟩ := hr
      rw [Nat.add_sub_cancel_left, kindsOf_getD', hordA] at hcase
      rcases hcase with h | h <;> exact nomatch h),
    hmapGetD _ l (by rw [hlenDropA]; exact hlA), getD_dropD]
  exact hcore.1.symm

/-! ## The ordinary field, RIGHT arm at a MEMBER target (task #315
L-B, DESIGN "the telescope the positivity `whnf` MAKES")

At a container-ORDINARY field the auxiliary block may classify the
copy's field RECURSIVE — the instantiation put a member of the block
where the container had none — and then `CopyCtorShape.ordF`'s right
disjunct asks for `EntryRead`.  At a FINITARY copy field (`.recursive`,
so the copy's telescope is empty by `BlockCtorData.tssNone`) the
Π-tower clauses are discharged by `tlsJ := []`, and what is left is the
reading and the index FIT:

* the reading is `copyFieldReadCore`'s, composed with the copy's own
  `BlockCtorData.recEntry` — the stored domain reads as the TARGET
  member's leaf applied to the parameter variables and the copy's index
  expressions — and with `targetRead_of_mem`, which is that same leaf
  at the block's parameter depth.  The two parameter spines read alike
  (`map_paramBvarsAt_interp` at the two cuts) and the leaf is closed,
  so the two `foldl`s agree;
* the FIT is what the core's second component is for.  `WellDenoted` of
  an application IS the fit of its arguments (`leafSpineFit`), and the
  stored domain's reading is graded at the CONTAINER's own prefix frame
  only because `normPosDomM_reads` carries the grading across the
  positivity walk.  No record and no other law supplies it there.

The PIN-target case is not here: the target's reading is then the
container's, the stored domain's head is the MIMIC, and identifying
them is `pinLeaf`, which is downstream of the shape (DESIGN §U.62 (a)).
It waits on the kernel record this lane requested. -/

/-- **`CopyCtorShape.ordF`'s RIGHT arm at a MEMBER target** (task #315
L-B): at a container-ordinary field the auxiliary block classified
RECURSIVE at one of the block's own members, the copy's entry is that
member's stored reading applied to the copy's index expressions, and
those fit the member's index telescope. -/
theorem NestedPinsRun.copyOrdFRightReadM {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hrunAll : ∀ (ci : ContainerInfo) (J : ContainerMember) (cI : Expr) (xfvs' : List Expr)
        (restM xI x' : Expr),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci →
      J ∈ ci.members → J.name = (pinsS.getD (q₀ + i') default).J →
      Expr.instPis (Expr.instantiateLevelParams J.lps
        (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI →
      ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM) →
      xfvs'[l]? = some xI →
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' →
      ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
          xI.fvarTypeD
        = .ok x'.fvarTypeD)
    (hrecA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = .recursive)
    (hmemT : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp) :
    EntryRead
      (nestedTV b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ)
      dJ ((pinsS.getD (q₀ + i') default).ψJ ψ) ((pinsS.getD (q₀ + i') default).Ds ψ)
      (fun l => ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
      ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) [])
      ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []) ρp i' j l := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    hqnMem, hqnPin, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ :=
    R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlA
  -- ==== the target: a member of the block, its former and its leaf ====
  have htgt : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0
      = tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l := by
    rw [mutTgts_getD hGlt hnFs]
  obtain ⟨-, -, htgtLt⟩ := R.h.ksJ _ _ hcA
  obtain ⟨ft, hft⟩ : ∃ ft, fms[tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l]? = some ft :=
    ⟨_, List.getElem?_eq_getElem (htgtLt l)⟩
  have hTk : tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l < p.k := by
    rw [htgt] at hmemT; exact hmemT
  obtain ⟨hnameT, hnIdxT⟩ := R.h.memT _ _ hft
  -- the two models' leaves at a REAL member agree
  have hacv : mp₁'.base2.acval ft.cvTa.name = mp₁.base2.acval ft.cvTa.name := by
    rw [R.hleafM' _ _ hTk hft, R.h.leaf _ _ hft]
  have hnameTake : ((fms.take p.k).map (·.cvTa.name)).getD
      (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) .anonymous = ft.cvTa.name := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hTk, hft]
    rfl
  -- ==== the copy's telescope is EMPTY at a finitary recursive field ====
  have htls : ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
      = [] := by
    rw [mutTlss_getD hGlt, hCD.tssNone ψ l (by rw [hrecA]; exact fun h => nomatch h)]
  -- ==== the copy's index expressions, and the stored domain's reading ====
  have hEis : ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
      = (eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [] := by
    rw [mutEiss0_getD hGlt]
  have hentry := hCD.recEntry ψ l hrecA hlA
  rw [hnameT] at hentry
  -- **THE PREDICATE, APPLIED** (integration 3r): lane L-E's repaired
  -- `EntryRead` takes the tuple and its reading law and asks for the
  -- ENTRY IDENTITY, so what this arm proves — the reading and the index
  -- FIT — is consumed the other way round: at the copy's EMPTY
  -- telescope the slot is one application (`slotSet_nil`), `hZ` turns it
  -- into the target's stored reading applied to the copy's index
  -- expressions, and its own hypothesis IS the fit.
  intro Z hZ
  · intro fs₁ hfs hfit
    -- the core: the two readings, and the stored one's GRADING
    have hcore := R.copyFieldReadCore SF S hPD hi' hj hlF hrunAll ψ ρp hsat fs₁ hfs hfit
    -- the parameter spines read alike at the two cuts
    have hσ : ∀ i : Nat, consList fs₁ ρp (i + l) = ρp i := by
      intro i
      rw [← hfs]
      exact consList_apply_add fs₁ ρp i
    have hpar1 : (paramBvarsAt b.nP (b.nP + l)).map (interp V (consList fs₁ ρp))
        = (List.range b.nP).reverse.map ρp := map_paramBvarsAt_interp hσ
    have hpar0 : (paramBvarsAt b.nP b.nP).map (interp V ρp)
        = (List.range b.nP).reverse.map ρp := by
      have h := map_paramBvarsAt_interp (V := V) (nP := b.nP) (e := 0) (ρp := ρp) (σ := ρp)
        (fun i => by rw [Nat.add_zero])
      rwa [Nat.add_zero] at h
    have hhead : interp V (consList fs₁ ρp) (mp₁.base2.acval ft.cvTa.name ψ)
        = interp V ρp (mp₁'.base2.acval ft.cvTa.name ψ) := by
      rw [hacv]
      exact interp_closed (V := V) (mp₁.base2.cval_closedL _ ψ) _ _
    have hEA : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).EA
          (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l)
        = AnnotTerm.mkAppN (mp₁'.base2.acval
            (((fms.take p.k).map (·.cvTa.name)).getD
              (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) .anonymous) ψ)
            (paramBvarsAt b.nP b.nP) :=
      targetRead_of_mem hTk
    have hIds : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).Ids
          (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l)
        = blockIds b.nP ppsF ψ (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) := by
      show (if tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l < p.k then
          blockIds b.nP ppsF ψ (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l)
        else _) = _
      rw [if_pos hTk]
    have hfr : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp
          (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) = ρp :=
      TargetView.frame_of_mem _ _ hTk
    rw [htls, slotSet_nil, hZ]
    · -- the reading: the container's field domain IS the target's leaf
      -- applied (the `simp only` is a BETA step: the predicate's `tg` is a
      -- λ and `rw` matches syntactically)
      simp only [htgt]
      rw [hEA, hnameTake, hEis, ← interp_instAll _ fs₁ ρp _, hfs, hcore.1, hentry,
        interp_mkAppN_foldl, List.map_append, List.foldl_append, hpar1, hhead,
        interp_mkAppN_foldl, hpar0]
    · -- the index fit: `WellDenoted` of the application IS the fit, and it
      -- is `hZ`'s own hypothesis
      have hokA := hcore.2.1
      rw [hentry] at hokA
      simp only [htgt]
      rw [hfr, hIds, hEis]
      simp only [blockIds]
      exact (leafSpineFit ((R.h.FD _ _ hft).len ψ) (mp₁.base2.cval_closedL _ ψ)
        (R.h.leafT hft ψ) hfs
        (by rw [hCD.eisLen ψ l hrecA hlA, hnIdxT]) hokA).2
/-! ## The ordinary field, RIGHT arm at a MEMBER target, REFLEXIVE
(task #315 L-B, DESIGN "does the refutation survive the repair")

The reflexive twin of `copyOrdFRightReadM`, writable because lane
L-E's repaired `EntryRead` asks for the copy's SLOT rather than a
syntactic Π-tower on the container's side — the shape against which
this lane's refutation dissolves.  Three substitutions on that arm:
`MutualCtorDataI.reflEntry` for `recEntry` (a reflexive field's stored
domain reads as the Π-tower over its OWN telescope ending in the
target applied), `interp_mkPisAV_piTele` for `slotSet_nil` (the
tower's interpretation IS the slot — the step the repair absorbed from
`copyEntryAt_of_read`), and both the reading and the index fit taken
one frame deeper, under the telescope's own spine. -/

/-- **`CopyCtorShape.ordF`'s RIGHT arm at a MEMBER target, REFLEXIVE**
(task #315 L-B): at a container-ordinary field the auxiliary block
classified REFLEXIVE at one of the block's own members, the copy's
entry is its slot — the Π-tower over the copy's telescope of the
target's stored reading applied to the copy's index expressions. -/
theorem NestedPinsRun.copyOrdFRightReadRefl {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hrunAll : ∀ (ci : ContainerInfo) (J : ContainerMember) (cI : Expr) (xfvs' : List Expr)
        (restM xI x' : Expr),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci →
      J ∈ ci.members → J.name = (pinsS.getD (q₀ + i') default).J →
      Expr.instPis (Expr.instantiateLevelParams J.lps
        (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI →
      ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM) →
      xfvs'[l]? = some xI →
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' →
      ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
          xI.fvarTypeD
        = .ok x'.fvarTypeD)
    (hreflA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = .reflexive)
    (hmemT : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp) :
    EntryRead
      (nestedTV b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ)
      dJ ((pinsS.getD (q₀ + i') default).ψJ ψ) ((pinsS.getD (q₀ + i') default).Ds ψ)
      (fun l => ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
      ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) [])
      ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []) ρp i' j l := by
  classical
  obtain ⟨cc, J, ci, lpsJ, pcs, fcs, Fs', esJ, cbody', o, params, pbs₀, cA, cname, qn, usJ,
    hciP, hJmem, hJcc, hn, hty, hnf, hJname, hDsnP, hstripJ, hpl, hfl, hesJ, hccf, hccb, hksJ,
    hopb, hplenB, hidxP, hpbs₀len, hpbs₀f, ⟨o', hstripF⟩, hcbb, hcbl, hDsB, hlenF, hfields,
    hqnMem, hqnPin, ⟨cI, fcs', hinstCI, hstripCI, hfcs'⟩, hcb, hcA, hnF, hbc⟩ :=
    R.copyResid SF S hPD hi' hj
  have hlcc : l < cc.nFields := by rw [← hnf]; exact hlF
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  have hnFs : l < mutNFOf ctorsA (b.ownOffset (p.k + q₀ + i') + j) := by
    show l < (ctorsA.getD _ default).2
    rw [List.getD_eq_getElem?_getD, hcA, Option.getD_some]
    exact hlA
  -- the target: a member of the block, its former and its leaf
  have htgt : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0
      = tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l := by
    rw [mutTgts_getD hGlt hnFs]
  obtain ⟨-, -, htgtLt⟩ := R.h.ksJ _ _ hcA
  obtain ⟨ft, hft⟩ : ∃ ft, fms[tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l]?
      = some ft := ⟨_, List.getElem?_eq_getElem (htgtLt l)⟩
  have hTk : tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l < p.k := by
    rw [htgt] at hmemT; exact hmemT
  obtain ⟨hnameT, hnIdxT⟩ := R.h.memT _ _ hft
  have hacv : mp₁'.base2.acval ft.cvTa.name = mp₁.base2.acval ft.cvTa.name := by
    rw [R.hleafM' _ _ hTk hft, R.h.leaf _ _ hft]
  have hnameTake : ((fms.take p.k).map (·.cvTa.name)).getD
      (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) .anonymous = ft.cvTa.name := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hTk, hft]
    rfl
  -- the copy's telescope and index expressions, off the block's tables
  have htls : ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) [])
      = tssF (b.ownOffset (p.k + q₀ + i') + j) ψ := by
    rw [mutTlss_getD hGlt]
  have hEis : ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
      = (eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [] := by
    rw [mutEiss0_getD hGlt]
  have hentry := hCD.reflEntry ψ l hreflA hlA
  rw [hnameT] at hentry
  -- the block's sort at this constructor's member is the first member's
  have hmotLt := R.h.motLt _ hGlt
  have hsEq : (fms.getD (mutMemF b (b.ownOffset (p.k + q₀ + i') + j)) default).s.eval ψ
      = f₀.s.eval ψ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmotLt]
    exact R.h.sEq _ _ (List.getElem?_eq_getElem hmotLt) ψ
  intro Z hZ
  intro fs₁ hfs hfit
  have hcore := R.copyFieldReadCore SF S hPD hi' hj hlF hrunAll ψ ρp hsat fs₁ hfs hfit
  have hEA : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ).EA
        (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l)
      = AnnotTerm.mkAppN (mp₁'.base2.acval
          (((fms.take p.k).map (·.cvTa.name)).getD
            (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) .anonymous) ψ)
          (paramBvarsAt b.nP b.nP) :=
    targetRead_of_mem hTk
  have hIds : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ).Ids
        (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l)
      = blockIds b.nP ppsF ψ (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) := by
    show (if tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l < p.k then
        blockIds b.nP ppsF ψ (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l)
      else _) = _
    rw [if_pos hTk]
  have hfr : (nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp
        (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l) = ρp :=
    TargetView.frame_of_mem _ _ hTk
  have hpar0 : (paramBvarsAt b.nP b.nP).map (interp V ρp)
      = (List.range b.nP).reverse.map ρp := by
    have h := map_paramBvarsAt_interp (V := V) (nP := b.nP) (e := 0) (ρp := ρp) (σ := ρp)
      (fun i => by rw [Nat.add_zero])
    rwa [Nat.add_zero] at h
  -- the tower's interpretation IS the slot
  rw [← interp_instAll _ fs₁ ρp _, hfs, hcore.1, hentry, hEis, htls]
  simp only [slotSet]
  refine interp_mkPisAV_piTele (fun d hd => ?_) (fun as hasFit => ?_)
  · have hb := hCD.tssBits ψ l d hd
    rw [hsEq] at hb
    exact hb
  · -- the tower's BODY, at the telescope's own frame
    have hlenAs : as.length = ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length := by
      rw [hasFit.length_eq, List.length_map]
    have hσ' : ∀ i : Nat,
        consList as (consList fs₁ ρp) (i + (l + as.length)) = ρp i := by
      intro i
      rw [show i + (l + as.length) = i + l + as.length from by omega,
        consList_apply_add as (consList fs₁ ρp) (i + l), ← hfs]
      exact consList_apply_add fs₁ ρp i
    have hpar1 : (paramBvarsAt b.nP
        (b.nP + l + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length)).map
        (interp V (consList as (consList fs₁ ρp)))
        = (List.range b.nP).reverse.map ρp := by
      rw [show b.nP + l + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length = b.nP + (l + as.length) from by
        rw [← hlenAs]; omega]
      exact map_paramBvarsAt_interp hσ'
    have hhead : interp V (consList as (consList fs₁ ρp)) (mp₁.base2.acval ft.cvTa.name ψ)
        = interp V ρp (mp₁'.base2.acval ft.cvTa.name ψ) := by
      rw [hacv]
      exact interp_closed (V := V) (mp₁.base2.cval_closedL _ ψ) _ _
    -- the index fit, under the telescope
    have hokTower := hcore.2.1
    rw [hentry] at hokTower
    obtain ⟨-, hokBody⟩ := WellDenoted_mkPisAV_inv hokTower
    have hokA := hokBody as hasFit
    have hfitZ : SpineFit ρp
        (blockIds b.nP ppsF ψ (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l))
        (((eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).map
          (interp V (consList as (consList fs₁ ρp)))) := by
      simp only [blockIds]
      have hokA' : WellDenoted V (consList (fs₁ ++ as) ρp)
          (AnnotTerm.mkAppN (mp₁.base2.acval ft.cvTa.name ψ)
            (paramBvarsAt b.nP (b.nP + (fs₁ ++ as).length)
              ++ (eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [])) := by
        rw [consList_append,
          show b.nP + (fs₁ ++ as).length
              = b.nP + l + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length from by
            rw [List.length_append, hfs, ← hlenAs]; omega]
        exact hokA
      rw [show consList as (consList fs₁ ρp) = consList (fs₁ ++ as) ρp from
        (consList_append fs₁ as ρp).symm]
      exact (leafSpineFit ((R.h.FD _ _ hft).len ψ) (mp₁.base2.cval_closedL _ ψ)
        (R.h.leafT hft ψ) rfl
        (by rw [hCD.eisLenRefl ψ l hreflA hlA, hnIdxT]) hokA').2
    -- the predicate's `tg` is a λ: the `simp only`s are BETA steps, since
    -- `rw` matches syntactically
    rw [List.nil_append, hZ _ (by simp only [htgt]; rw [hfr, hIds]; exact hfitZ)]
    simp only [htgt]
    rw [hEA, hnameTake,
      interp_mkAppN_foldl, List.map_append, List.foldl_append, hpar1, hhead,
      interp_mkAppN_foldl, hpar0]

/-! ## The ordinary field, RIGHT arm at a PIN TARGET, REFLEXIVE
(task #315 R3)

The last of the four `ordF`-right cases.  At a REFLEXIVE copy field the
target sits under the field's OWN `∀`-telescope, so both sides have to
be peeled and the peels aligned before the pin-target reading can run
at all.  Four steps, each a brick:

* the STORED domain is a `∀`-tower whose length is the copy's recorded
  telescope (`MutualCtorDataI.reflOpen`, `openPisAtFvars_stripPis`,
  `stripPis_mkPisB`);
* so is the NORMALISATION `w` (`replaceAllNested_mkPisB_inv`), and its
  binder domains are member-free (`normPosDomM_mkPisB_free`, carried out
  of K.51's run by `copyFieldReadPin`), so the rewrite is INERT on them
  (`replaceAllNested_mkPisB_inert`) and the two towers are towers over
  the SAME binder list;
* two telescopes over the same binders therefore read with the same
  `Π`-prefix (`denoteMeta_mkPisB_prefix`), and the stored side's prefix
  IS the copy's telescope (`domRead` composed with `reflEntry`) — so
  `w` reads as the `Π`-tower over the copy's own telescope and the
  tower's interpretation is the slot (`interp_mkPisAV_piTele`);
* and the tower's BODY is `copyOrdFRightPinRead`'s situation one
  telescope deeper, with the head off `MutualOpened.reflF` (read back
  through the opening) and the index spine off `reflOpen`'s own clause.

Nothing here identifies the mimic's leaf with the container's: exactly
as at the finitary field, both sides of the entry are read on the
CONTAINER's side and the mimic only names the pin's INDEX. -/

omit R SF S in
/-- **TWO TELESCOPES OVER THE SAME BINDERS READ WITH THE SAME
`Π`-PREFIX** (task #315 R3): `denoteMeta` descends a `∀` into its
domain and its opened body, so the prefix of the reading depends on the
binder list alone — the domains' readings and the binders' bits are the
same whatever the two bodies are.  That is the alignment the reflexive
pin arm needs: the stored domain and the normalisation differ only
below the telescope. -/
private theorem denoteMeta_mkPisB_prefix {acval : Name → (Name → Nat) → AnnotTerm}
    {env₀ : Env} {φ : Name → Nat} :
    ∀ (bs : List (Expr × ConLeche.BinderMeta)) {d : Nat} {r₁ r₂ : Expr}
      {ea₁ ea₂ : AnnotTerm} {pps₁ pps₂ : List (Nat × Nat × AnnotTerm)} {b₁ b₂ : AnnotTerm},
      denoteMeta acval env₀ φ d (ConLeche.mkPisB bs r₁) = some ea₁ →
      denoteMeta acval env₀ φ d (ConLeche.mkPisB bs r₂) = some ea₂ →
      stripPisAV bs.length ea₁ = some (pps₁, b₁) →
      stripPisAV bs.length ea₂ = some (pps₂, b₂) →
      pps₁ = pps₂
  | [], _, _, _, _, _, _, _, _, _, _, _, hst₁, hst₂ => by
    simp only [List.length_nil, stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst₁ hst₂
    rw [← hst₁.1, ← hst₂.1]
  | b₀ :: bs, d, r₁, r₂, ea₁, ea₂, pps₁, pps₂, b₁, b₂, hden₁, hden₂, hst₁, hst₂ => by
    obtain ⟨ta₁, ba₁, hta₁, hba₁, rfl⟩ := denoteMeta_forallE_inv hden₁
    obtain ⟨ta₂, ba₂, hta₂, hba₂, rfl⟩ := denoteMeta_forallE_inv hden₂
    obtain rfl : ta₂ = ta₁ := Option.some.inj (hta₂.symm.trans hta₁)
    simp only [List.length_cons, stripPisAV, Option.map_eq_some_iff] at hst₁ hst₂
    obtain ⟨⟨pps₁', b₁'⟩, hs₁, he₁⟩ := hst₁
    obtain ⟨⟨pps₂', b₂'⟩, hs₂, he₂⟩ := hst₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨rfl, -⟩ := he₁
    obtain ⟨rfl, -⟩ := he₂
    rw [ConLeche.mkPisB_instantiate1] at hba₁ hba₂
    have hlen : (ConLeche.instTeleB (Expr.fvar d b₀.1) 0 bs).length = bs.length :=
      ConLeche.instTeleB_length _ _ _
    rw [← hlen] at hs₁ hs₂
    rw [denoteMeta_mkPisB_prefix _ hba₁ hba₂ hs₁ hs₂]

/-- **`CopyCtorShape.ordF`'s RIGHT arm AT A PIN TARGET, REFLEXIVE**
(task #315 R3): at a container-ordinary field the auxiliary block
classified `.reflexive` at a target AT OR ABOVE `p.k` — a MIMIC — the
copy's entry is its SLOT: the `Π`-set over the copy's telescope of the
block pin's stored reading applied to the copy's index expressions. -/
theorem NestedPinsRun.copyOrdFRightReadReflP {pbs : List (Expr × ConLeche.BinderMeta)}
    (hPD : ∀ q, q < st.pins.length → PinData env st p pbs q)
    {i' : Nat} (hi' : i' < kJ) {j : Nat} {cAJ : ConstantVal × Nat}
    (hj : (dJ.ctorsM i')[j]? = some cAJ) {l : Nat} (hlF : l < cAJ.2)
    (hrunAll : ∀ (ci : ContainerInfo) (J : ContainerMember) (cI : Expr) (xfvs' : List Expr)
        (restM xI x' : Expr),
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ci →
      J ∈ ci.members → J.name = (pinsS.getD (q₀ + i') default).J →
      Expr.instPis (Expr.instantiateLevelParams J.lps
        (pinsS.getD (q₀ + i') default).lvls cAJ.1.type) (srcAtE st p (q₀ + i')).2.2 = some cI →
      ConLeche.openPisAtFvars cAJ.2 cI b.nP = some (xfvs', restM) →
      xfvs'[l]? = some xI →
      (xFvsF (b.ownOffset (p.k + q₀ + i') + j))[l]? = some x' →
      ∃ (params : List Expr) (pbs₀ : List (Expr × ConLeche.BinderMeta)) (w : Expr)
        (st' : ConLeche.ElimState),
        ConLeche.nestedRewriteData p st = some (params, pbs₀) ∧
        ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
            (ConLeche.consMutualFormers (fms.take p.k) env) b.memberNames (b.nP + l) 1024
            xI.fvarTypeD
          = .ok w ∧
        ConLeche.replaceAllNested env (p.lps.map Level.param) params pbs₀ st w
          = .ok (x'.fvarTypeD, st') ∧ st'.pins.length ≤ st.pins.length)
    (hkA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.reflexive)
    (hpinT : ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
      (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k)
    (hnIdx : ∀ q, q < pinsS.length →
      (fms.getD (p.k + q) default).nIdx = (pinsS.getD q default).nIdx)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hsat : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp) :
    EntryRead
      (nestedTV b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
        ((fms.take p.k).map (·.cvTa.name)) ψ)
      dJ ((pinsS.getD (q₀ + i') default).ψJ ψ) ((pinsS.getD (q₀ + i') default).Ds ψ)
      (fun l => ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
      ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) [])
      ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []) ρp i' j l := by
  classical
  obtain ⟨_cc, _J, _ci, _cI, cA, _cname, -, -, -, -, -, hnf, -, -, -, hcA, -, hnF⟩ :=
    R.ctorPair SF S hPD hi' hj
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hCD := R.h.CD _ _ hcA
  have hlcc : l < _cc.nFields := by rw [← hnf]; exact hlF
  have hlA : l < cA.2 := by rw [hnF]; exact hlcc
  -- the copy's telescope and index expressions, off the block's tables
  have htls : ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) [])
      = tssF (b.ownOffset (p.k + q₀ + i') + j) ψ := by
    rw [mutTlss_getD hGlt]
  have hEis : ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
      = (eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [] := by
    rw [mutEiss0_getD hGlt]
  -- the block's sort at this constructor's member is the first member's
  have hmotLt := R.h.motLt _ hGlt
  have hsEq : (fms.getD (mutMemF b (b.ownOffset (p.k + q₀ + i') + j)) default).s.eval ψ
      = f₀.s.eval ψ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmotLt]
    exact R.h.sEq _ _ (List.getElem?_eq_getElem hmotLt) ψ
  intro Z hZ
  intro fs₁ hfs hfit
  obtain ⟨x', w, ea', params, pbs₀, st', hx', hrwd, hrep, hstable, hfreeW, hea', heq, hok⟩ :=
    R.copyFieldReadPin SF S hPD hi' hj hlF hrunAll ψ ρp hsat fs₁ hfs hfit
  -- ==== the stored domain's telescope ====
  obtain ⟨afvs, bodyX, hopX, hlenT, -, hspineX⟩ := hCD.reflOpen ψ l x' hx' hkA
  obtain ⟨bsX, resX, hstripX, -, -, -⟩ := Verify.openPisAtFvars_stripPis _ hopX
  have hbsXlen : bsX.length
      = ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length :=
    ConLeche.Expr.stripPis_length _ hstripX
  have hmkX : x'.fvarTypeD = ConLeche.mkPisB bsX resX := ConLeche.stripPis_mkPisB _ hstripX
  -- ==== the normalisation's telescope, and the rewrite's INERTNESS on it ====
  obtain ⟨bsW, resW, hmkW, hbsWlen⟩ :=
    ConLeche.replaceAllNested_mkPisB_inv _ (by rw [hmkX] at hrep; exact hrep) hbsXlen
  have hfreeBs : ∀ bb ∈ bsW, (st.newNames.any fun T => bb.1.mentionsConst T) = false :=
    fun bb hbb => ConLeche.newNames_no_mention_of_memberFree R.hb
      (hfreeW bsW.length bsW resW
        (by rw [hmkW]; exact ConLeche.stripPis_mkPisB_self bsW resW) bb hbb)
  obtain ⟨resX', houtW, hrunBody⟩ :=
    ConLeche.replaceAllNested_mkPisB_inert bsW hfreeBs (by rw [← hmkW]; exact hrep)
  obtain ⟨hbsEq, hresEq⟩ : bsW = bsX ∧ resX' = resX := by
    have h1 : ConLeche.mkPisB bsW resX' = ConLeche.mkPisB bsX resX := by rw [← houtW, hmkX]
    have h2 := ConLeche.stripPis_mkPisB_self bsW resX'
    rw [h1, show bsW.length = bsX.length from by rw [hbsWlen, hbsXlen],
      ConLeche.stripPis_mkPisB_self bsX resX] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1.symm, h2.2.symm⟩
  rw [hbsEq] at hmkW
  rw [hresEq] at hrunBody
  -- ==== the two openings share their openers ====
  obtain ⟨fvs, -, hallF, hlaw⟩ :=
    ConLeche.openPisAtFvars_mkPisB ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length
      bsX hbsXlen (b.nP + l)
  have hopXf := hlaw resX
  rw [← hmkX] at hopXf
  have hbodyX := (Prod.mk.injEq .. ▸ Option.some.inj (hopX.symm.trans hopXf) :
    (afvs, bodyX) = (fvs, Expr.instSeq fvs
      (((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length - 1) resX))
  have hbodyXeq : bodyX = Expr.instSeq fvs
      (((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length - 1) resX :=
    congrArg Prod.snd hbodyX
  rw [hbodyXeq] at hspineX
  have hopW : ConLeche.openPisAtFvars
      ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length w (b.nP + l)
      = some (fvs, Expr.instSeq fvs
        (((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length - 1) resW) := by
    rw [hmkW]; exact hlaw resW
  -- ==== the reading of `w` peels into the COPY's own telescope ====
  obtain ⟨ppsW, bW, hstAV, hbW, -, -⟩ := denoteMeta_openPis _ hopW hea'
  have hdomX := hCD.domRead ψ l x' hx'
  have hentry := hCD.reflEntry ψ l hkA hlA
  have hstX : stripPisAV ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length
      (((dsF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD (b.nP + l) default).2.2)
      = some ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [],
        AnnotTerm.mkAppN (mp₁.base2.acval
          (mutualNameOf b.members3
            (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l)) ψ)
          (paramBvarsAt b.nP (b.nP + l
              + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length)
            ++ (eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [])) := by
    rw [hentry]; exact stripPisAV_mkPisAV _ _
  have hppsEq : ppsW = (tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l [] := by
    have h1 : denoteMeta mp₁.base2.acval (ConLeche.consMutualFormers fms env) ψ (b.nP + l)
        (ConLeche.mkPisB bsX resW) = some ea' := by
      rw [← hmkW]; exact R.crossUp ψ (b.nP + l) _ hea'
    have h2 : denoteMeta mp₁.base2.acval (ConLeche.consMutualFormers fms env) ψ (b.nP + l)
        (ConLeche.mkPisB bsX resX)
        = some (((dsF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD (b.nP + l) default).2.2) := by
      rw [← hmkX]; exact hdomX
    have h3 := hstAV
    have h4 := hstX
    rw [← hbsXlen] at h3 h4
    exact denoteMeta_mkPisB_prefix bsX h1 h2 h3 h4
  obtain ⟨hea'Eq, -⟩ := stripPisAV_eq_mkPis hstAV
  rw [hppsEq] at hea'Eq
  -- ==== the entry: the tower's interpretation IS the slot ====
  rw [← interp_instAll _ fs₁ ρp _, hfs, heq, hea'Eq, hEis, htls]
  simp only [slotSet]
  refine interp_mkPisAV_piTele (fun d hd => ?_) (fun as hasFit => ?_)
  · have hb := hCD.tssBits ψ l d hd
    rw [hsEq] at hb
    exact hb
  · -- the tower's BODY: the pin target's reading, one telescope deeper
    have hlenAs : as.length = ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length := by
      rw [hasFit.length_eq, List.length_map]
    have hcons : consList (fs₁ ++ as) ρp = consList as (consList fs₁ ρp) :=
      consList_append fs₁ as ρp
    have hfsas : (fs₁ ++ as).length
        = l + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length := by
      rw [List.length_append, hfs, hlenAs]
    have hokTower := hok.1
    rw [hea'Eq] at hokTower
    obtain ⟨-, hokBody⟩ := WellDenoted_mkPisAV_inv hokTower
    have hokB : WellDenoted V (consList (fs₁ ++ as) ρp) bW := by
      rw [hcons]; exact hokBody as hasFit
    -- the classification's head at the tower's BODY, read back to the closed one
    obtain ⟨afvs₂, bodyX₂, hopX₂, -, -, hheadO, -, -, -, -, -⟩ := hCD.opened.reflF l x' hx' hkA
    rw [← hlenT] at hopX₂
    have hb2 := (Prod.mk.injEq .. ▸ Option.some.inj (hopX₂.symm.trans hopXf) :
      (afvs₂, bodyX₂) = (fvs, Expr.instSeq fvs
        (((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length - 1) resX))
    have hbodyX₂ : bodyX₂ = Expr.instSeq fvs
        (((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length - 1) resX :=
      congrArg Prod.snd hb2
    rw [hbodyX₂] at hheadO
    have hheadRaw : resX.getAppFn
        = Expr.const (mutualNameOf b.members3
            (tgtAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l))
          (b.lps.map Level.param) :=
      ConLeche.instSeq_getAppFn_const_inv fvs hallF _ resX hheadO
    have hdepth : b.nP + (l + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length)
        = b.nP + l + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length := by omega
    have hspineD : DenoteMetaSpine mp₁.base2.acval (ConLeche.consMutualFormers fms env) ψ
        (b.nP + (l + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length))
        ((Expr.instSeq fvs
            (((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length - 1)
            resX).getAppArgs.drop b.nP)
        ((eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []) := by
      rw [hdepth]; exact hspineX
    have hbWD : denoteMeta mp₁'.base2.acval (ConLeche.consMutualFormers (fms.take p.k) env) ψ
        (b.nP + (l + ((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length))
        (Expr.instSeq fvs
          (((tssF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).length - 1) resW)
        = some bW := by
      rw [hdepth]; exact hbW
    obtain ⟨qq, hidx, hread, hfitI⟩ :=
      R.copyOrdFRightPinRead SF S hPD hi' hj hlF hpinT hheadRaw hrwd hrunBody hstable hnIdx
        hallF hspineD (hCD.eisLenRefl ψ l hkA hlA) hbWD ρp (fs₁ ++ as) hfsas hokB
    have hfitZ : SpineFit
        ((nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp
          (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0))
        ((nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ).Ids
          (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0))
        (((eissF (b.ownOffset (p.k + q₀ + i') + j) ψ).getD l []).map
          (interp V (consList as (consList fs₁ ρp)))) := by
      rw [hidx, ← hcons]; exact hfitI
    rw [List.nil_append, hZ _ hfitZ, ← hcons]
    simp only [hidx]
    exact hread

end Assembly

/-! ## THE FIVE ARMS, ASSEMBLED (task #315 L-B, DESIGN §U.58)

`NestedPinsShape` (`NestedCopyIdx.lean`, lane L-E's name for this
lane's deliverable) is `CopyShapeA` at every constructor of every copy
of a pin group.  Its five fields are the arms proved above — `len`
(`copyLen`), `recF` (`copyRecF`/`copyRecFRefl` with their readings),
`ordF`'s left arm (`copyOrdFLeft`), `ordF`'s right arm and `pinF`
(their target conjuncts, `copyOrdFRight_shape`/`copyPinF_shape`) and
`es` (`copyEs`) — with ONE residual left, `NestedPinsShapePinF`, named
below at exactly the conjunct that is open.  The `ordF`-right reading
at a PIN target was the other one and is now a theorem
(`nestedPinsShapeOrdRight_of`, task #315 R3).  K.42's own conjunct is no residual any
more: lane L-E threaded it onto the run's bundle and
`nestedPinsShape_of` reads `R.hK42` (integration 3r). -/

/-- **`ordF`'s right arm at the READING, at a PIN TARGET** — a
RESIDUAL no longer (task #315 R3, `nestedPinsShapeOrdRight_of` below;
lane L-E's `EntryRead`, DESIGN §U.36/§U.51): at a
container-ORDINARY field the auxiliary block classified RECURSIVE OR
REFLEXIVE, whose target is one of the block's PINS, the copy's entry is
the target's STORED reading — the container's domain read fibre-wise
under its own telescope, and NOTHING about the target's head since the
`TargetHead` conjunct was refuted at an accepted block (DESIGN §U.61).
The arm's TARGET conjunct (outside the group) is
`copyOrdFRight_shape`.

**ONE residual over BOTH field kinds** (task #315 L-B, the session that
proved the reflexive half): the two kinds' conclusions are the SAME
`EntryRead` call — what differed was only the kind hypothesis, and the
two arms at a MEMBER target are now both proved
(`NestedPinsRun.copyOrdFRightReadM` at `.recursive`,
`NestedPinsRun.copyOrdFRightReadRefl` at `.reflexive`).  So the
hypothesis here is the DISJUNCTION, which is also what the assembly
has at both branches (`blkRss`' bit is `true` at exactly these two
kinds).  The proof, when the kernel record lands, will still split:
at a RECURSIVE copy field the copy's telescope is empty
(`BlockCtorData.tssNone`) and `EntryRead`'s tower is `slotSet_nil`,
while at a REFLEXIVE one the positivity `whnf` MADE a telescope
(`BlockCtorData.reflOpen` off `piBinders`, and `mutualOpenedOk`
rejects an empty one) and the tower is `interp_mkPisAV_piTele` — the
same two substitutions that separated the member-target arms.

The REFUTATION this residual's reflexive half used to carry is
DISSOLVED: what was false was the OLD `EntryRead`'s two SYNTACTIC
Π-tower clauses, at a container field that is a λ-redex
(`tests/e2e/nested_lam_pin_refl.ndjson`, kept as a regression fixture
— `Wrap (f : True → Type) | mk : f True.intro → Wrap f` nested at
`f := fun _ : True => True → T`, where the copy's field is REFLEXIVE at
the member `T` with a one-entry telescope while the container's own
field is the APPLICATION `f True.intro`).  Lane L-E's repaired
predicate asks instead for what the consumer produces — the
container's field domain, read at the pin's frame, IS the copy's SLOT
— and the witness that broke the old clauses satisfies the new one,
because a λ-redex respects a semantic equality (DESIGN "does the
refutation survive the repair").

**AND THE PIN TARGET IS PROVED AT BOTH KINDS** (task #315 R3):
`copyOrdFRightReadP` at `.recursive` and `copyOrdFRightReadReflP` at
`.reflexive`, dispatched by `nestedPinsShapeOrdRight_of`, so this
predicate is a theorem and `nestedPinsShape_of` no longer takes it.

**The circularity this docstring used to record DOES NOT ARISE**, and
recording why is the point.  It read: at a pin target `TargetView.EA`
is the CONTAINER's reading while the stored domain's head is the
MIMIC, and identifying them is `pinLeaf`, which is downstream of this
very shape.  Neither arm identifies them.  `TargetView.EA` at a pin
index IS the container's leaf at the pin's components
(`targetRead_of_pin`), and the entry's other side is the reading of
`w` — K.51's CONTAINER-headed normalisation of the minted domain, not
the stored mimic-headed one (`copyFieldReadPin`).  So both sides are
read on the container's side and no leaf is identified.  The mimic
enters SYNTACTICALLY and only to name the pin's INDEX: the
classification names the stored domain's head, the rewrite's backwards
inversion (`replaceAllNested_container_head_stable`) names the
container and the pin the fire landed on, and the block's `Nodup`
member names turn the mimic into `p.k + qq`
(`copyOrdFRightPinCorr`). -/
@[expose] def NestedPinsShapeOrdRight (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  NestedPinsIdsAt V μ F fun {env} _ p _ b fms f₀ ctorsA kinds ppsF W _ _ _ _ _ _ eissF tssF _
      _ _ pinsS mp₁' q₀ kJ dJ =>
    ∀ i, i < kJ → ∀ (cvT : ConstantVal) (caps : IndCaps),
      (ConLeche.consMutualFormers (fms.take p.k) env).find? (pinsS.getD (q₀ + i) default).J
        = some (.indInfo cvT caps) →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      ∀ l, l < ((dJ.Fss i' ((pinsS.getD (q₀ + i) default).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      (kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.recursive ∨
        kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = RecFieldKind.reflexive) →
      ¬ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k →
      EntryRead
        (nestedTV b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ)
        dJ ((pinsS.getD (q₀ + i) default).ψJ ψ) ((pinsS.getD (q₀ + i) default).Ds ψ)
        (fun l => ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)
        ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) [])
        ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []) ρp i' j l

/-- **RESIDUAL 3 — `pinF` at the container's OWN pin** (lane L-E's
`PinCorr`, DESIGN §U.36/§U.51): at a container-recursive field nested
at one of the container's own pins, the copy's field is recursive at
the block pin CORRESPONDING to the container's, with its telescope and
index expressions instantiated.  The arm's TARGET conjunct (outside the
group) is `copyPinF_shape`. -/
@[expose] def NestedPinsShapePinF (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  NestedPinsIdsAt V μ F fun {env} _ p _ b fms f₀ ctorsA kinds ppsF W _ _ _ _ _ _ eissF tssF _
      _ _ pinsS mp₁' q₀ kJ dJ =>
    ∀ i, i < kJ → ∀ (cvT : ConstantVal) (caps : IndCaps),
      (ConLeche.consMutualFormers (fms.take p.k) env).find? (pinsS.getD (q₀ + i) default).J
        = some (.indInfo cvT caps) →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ i', i' < kJ → ∀ j, j < (dJ.ctorsM i').length →
      ∀ l, l < ((dJ.Fss i' ((pinsS.getD (q₀ + i) default).ψJ ψ)).getD j []).length →
      ((dJ.rss i').getD j []).getD l false = true → ¬ dJ.tgts i' j l < dJ.k →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true ∧
      p.k ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 ∧
      PinCorr
        (nestedTV b.nP p.k f₀.s ppsF W pinsS mp₁'.base2.acval
          ((fms.take p.k).map (·.cvTa.name)) ψ)
        mp₁'.base2.acval dJ ((pinsS.getD (q₀ + i) default).ψJ ψ)
        ((pinsS.getD (q₀ + i) default).Ds ψ)
        cvT.levelParams (pinsS.getD (q₀ + i) default).lvls
        (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0) (dJ.tgts i' j l - dJ.k) ∧
      (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []).map
          (·.2.2)
        = instTele ((pinsS.getD (q₀ + i) default).Ds ψ) l
            ((((dJ.tlss i' ((pinsS.getD (q₀ + i) default).ψJ ψ)).getD j []).getD l []).map
              (·.2.2)) ∧
      ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l []
        = (((dJ.Eiss i' ((pinsS.getD (q₀ + i) default).ψJ ψ)).getD j []).getD l []).map
            (AnnotTerm.instAll ((pinsS.getD (q₀ + i) default).Ds ψ)
              (l + (((dJ.tlss i' ((pinsS.getD (q₀ + i) default).ψJ ψ)).getD j []).getD l
                []).length))

omit [SetTheory V] in
/-- The classification rejects a negative or unsupported field, so no
kind entry of an accepted block carries one. -/
private theorem kindAt_ne_of {members : List (Name × Nat × Nat)} {lps : List Name} {nP : Nat}
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))}
    (hkindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) members lps nP ctorsA
      = .ok kinds)
    {J : Nat} (hJ : J < ctorsA.length) (l : Nat) :
    kindAt (mutKsOf kinds J) l ≠ .negative ∧ kindAt (mutKsOf kinds J) l ≠ .unsupported := by
  classical
  obtain ⟨-, hnegAll, hunsAll, hlenK⟩ := ConLeche.classifyMutualKinds_inv hkindsRun
  have hJk : J < kinds.length := by rw [hlenK]; exact hJ
  have hmut : mutKsOf kinds J = kinds[J]'hJk := by
    show kinds.getD J [] = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJk]; rfl
  have key : ∀ kk : RecFieldKind, kk ≠ .ordinary →
      kinds.any (fun ks => ks.any (·.1 == kk)) = false → kindAt (mutKsOf kinds J) l ≠ kk := by
    intro kk hord hall hc
    rcases Nat.lt_or_ge l (mutKsOf kinds J).length with hlt | hge
    · have hmem : (mutKsOf kinds J).getD l (.ordinary, 0) ∈ mutKsOf kinds J := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact List.getElem_mem _
      have hin : (mutKsOf kinds J).any (·.1 == kk) = true := by
        refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
        show (((mutKsOf kinds J).getD l (.ordinary, 0)).1 == kk) = true
        rw [show ((mutKsOf kinds J).getD l (.ordinary, 0)).1 = kk from hc]
        simp
      rw [hmut] at hin
      have hany : kinds.any (fun ks => ks.any (·.1 == kk)) = true :=
        List.any_eq_true.mpr ⟨_, List.getElem_mem _, hin⟩
      rw [hall] at hany
      exact nomatch hany
    · have hd : kindAt (mutKsOf kinds J) l = .ordinary := by
        show ((mutKsOf kinds J).getD l (.ordinary, 0)).1 = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
      rw [hd] at hc
      exact hord hc.symm
  exact ⟨key _ (fun h => nomatch h) hnegAll, key _ (fun h => nomatch h) hunsAll⟩

section Assembly2

/-- **RESIDUAL 2, DISCHARGED** (task #315 R3): `NestedPinsShapeOrdRight`
is a theorem.  The dispatch is by the copy field's KIND — the
disjunction the predicate carries, which is also what `blkRss`' bit
says — and each branch is its own arm at a PIN target
(`copyOrdFRightReadP` at `.recursive`, `copyOrdFRightReadReflP` at
`.reflexive`), fed K.51's positivity run (`copyOrdFRightPinRun`, which
is stated at either kind: its guard is only that the field is not
ordinary) and the pins' index count (`NestedPinSynFacts.pinNIdx`).

The MEMBER-target halves are elsewhere: they are the two arms
`nestedPinsShape_of` applies directly, and the predicate here is
narrowed to the pin target.  What made this residual wait was the
reflexive half's tower peel, not the dispatch. -/
theorem nestedPinsShapeOrdRight_of {F : Nat} : NestedPinsShapeOrdRight V μ F := by
  intro env mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
  intro i hi cvT caps hfind ψ ρp hsat i' hi' j hj l hl hrs hrsT hkind hpinT
  obtain ⟨pbs, hpbs, hpfree, hPD⟩ := R.pinDataFree
  obtain ⟨cAJ, hj'⟩ : ∃ cAJ, (dJ.ctorsM i')[j]? = some cAJ :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨cvTJ, capsJ, cvRJ, mIJ, rPJ, rulesJ, -, hI, -⟩ := S.stored i' hi'
  have hpinAt : ∀ n : Nat, (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF
      esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt n = pinsS.getD n default :=
    fun _ => rfl
  rw [hpinAt] at hI
  have hFssLen : ∀ ψJ : Name → Nat, ((dJ.Fss i' ψJ).getD j []).length = cAJ.2 :=
    fun ψJ => hI.Fss_length hj' ψJ
  have hlF : l < cAJ.2 := by rw [hFssLen] at hl; exact hl
  have hψ := S.ψJEq i i' hi hi' ψ
  rw [hpinAt, hpinAt] at hψ
  have hDs : (pinsS.getD (q₀ + i) default).Ds ψ = (pinsS.getD (q₀ + i') default).Ds ψ := by
    have a := S.sameDs i hi ψ
    have bb := S.sameDs i' hi' ψ
    rw [hpinAt, hpinAt] at a
    rw [hpinAt, hpinAt] at bb
    rw [a, bb]
  rw [hψ, hDs]
  rcases hkind with hkA | hkA
  · exact R.copyOrdFRightReadP SF S hPD hi' hj' hlF
      (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => by
        obtain ⟨prms, pb₀, ww, stt, hA, hB, hC, -, hE⟩ :=
          R.copyOrdFRightPinRun SF S hPD R.hK51 hi' hj' hlF
            (by rw [hkA]; exact fun hc => nomatch hc) hpinT h1 h2 h3 h4 h5 h6 h7
        exact ⟨prms, pb₀, ww, stt, hA, hB, hC, Nat.le_of_eq hE⟩)
      hkA hpinT SF.pinNIdx ψ ρp hsat
  · exact R.copyOrdFRightReadReflP SF S hPD hi' hj' hlF
      (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 => by
        obtain ⟨prms, pb₀, ww, stt, hA, hB, hC, -, hE⟩ :=
          R.copyOrdFRightPinRun SF S hPD R.hK51 hi' hj' hlF
            (by rw [hkA]; exact fun hc => nomatch hc) hpinT h1 h2 h3 h4 h5 h6 h7
        exact ⟨prms, pb₀, ww, stt, hA, hB, hC, Nat.le_of_eq hE⟩)
      hkA hpinT SF.pinNIdx ψ ρp hsat

/-- **THE COPIES' SHAPES, ASSEMBLED** (task #315 L-B, DESIGN §U.60):
`NestedPinsShape` — `CopyShapeA` at every constructor of every copy of
every pin group — from the arms proved above.  `len` is `copyLen`;
`recF` is `copyRecF`/`copyRecFRefl` with `copyRecFRead`/
`copyRecFReadRefl` at the two field kinds; `ordF` splits on the
AUXILIARY block's kind at the field (`kindAt_ne_of` excludes the two
rejecting kinds) into `copyOrdFLeft` and `copyOrdFRight_shape`; `pinF`
is `copyPinF_shape`; `es` is `copyEs`.  ONE residual remains,
`NestedPinsShapePinF`.  The `ordF`-right reading is complete at all
four cases: the MEMBER targets by `copyOrdFRightReadM` and
`copyOrdFRightReadRefl` (the second under lane L-E's repaired
`EntryRead`, DESIGN "does the refutation survive the repair"), the PIN
targets by `copyOrdFRightReadP` and `copyOrdFRightReadReflP` through
`nestedPinsShapeOrdRight_of` (task #315 R3).  K.42's
record is read off the run (`NestedPinsRun.hK42`, lane L-E), and
K.32's `nestedCopyTargetsOk`, which the
bookkeeping predicate `NestedPinsKindsRun` stood for until lane L-E
threaded it (`NestedPinsRun.hK32`, DESIGN §U.64 (f)), is now read off
the run record itself. -/
theorem nestedPinsShape_of {F : Nat}
    (hPin : NestedPinsShapePinF V μ F) :
    NestedPinsShape V μ F := by
  intro env mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
  intro i hi cvT caps hfind ψ ρp hsat i' hi' j hj
  have hK32 := R.hK32
  have hkindsRun := R.h.classify
  have hres1 := R.hK42
  have hres2 := nestedPinsShapeOrdRight_of (V := V) (μ := μ) (F := F)
    mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁
    ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
    i hi cvT caps hfind ψ ρp hsat i' hi' j hj
  have hres3 := hPin mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁
    ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
    i hi cvT caps hfind ψ ρp hsat i' hi' j hj
  -- the group's pins, and the copy's own constructor record
  have hpinAt : ∀ n : Nat, (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
      srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt n = pinsS.getD n default :=
    fun _ => rfl
  have hψ := S.ψJEq i i' hi hi' ψ
  rw [hpinAt, hpinAt] at hψ
  have hDs : (pinsS.getD (q₀ + i) default).Ds ψ = (pinsS.getD (q₀ + i') default).Ds ψ := by
    have a := S.sameDs i hi ψ
    have bb := S.sameDs i' hi' ψ
    rw [hpinAt, hpinAt] at a
    rw [hpinAt, hpinAt] at bb
    rw [a, bb]
  obtain ⟨pbs, hpbs, hpfree, hPD⟩ := R.pinDataFree
  obtain ⟨hgb, hgs⟩ := S.grp i' hi'
  rw [← pinAtE_eq] at hgb hgs
  have CM : ∀ ciJ : ContainerInfo,
      ConLeche.containerInfo? env (pinsS.getD (q₀ + i') default).J = some ciJ →
      ContainerModeled mp₁'.base2 ciJ dJ := by
    intro ciJ hciJ
    exact S.modeled i' hi' ciJ (by rw [hpinAt]; exact hciJ)
  obtain ⟨cAJ, hj'⟩ : ∃ cAJ, (dJ.ctorsM i')[j]? = some cAJ :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨cvTJ, capsJ, cvRJ, mIJ, rPJ, rulesJ, -, hI, -⟩ := S.stored i' hi'
  rw [hpinAt] at hI
  obtain ⟨cc, J, ci, cI, cA, cname, hciP, hJmem, hJcc, hn, hty, hnf, hJname, hinst, hcj, hcA,
    hbc, hnF⟩ := R.ctorPair SF S hPD hi' hj'
  have hmn : dJ.memberNames.length = dJ.k := (CM ci hciP).namesLen
  have hFssLen : ∀ ψJ : Name → Nat, ((dJ.Fss i' ψJ).getD j []).length = cAJ.2 :=
    fun ψJ => hI.Fss_length hj' ψJ
  -- the copy's own constructor record, and the kind table's entry
  obtain ⟨-, -, hCD⟩ := hI.ctors i' j cAJ hI.memberLt hj'
  have hGlt : b.ownOffset (p.k + q₀ + i') + j < ctorsA.length :=
    (List.getElem?_eq_some_iff.mp hcA).1
  have hcAnF : cA.2 = cAJ.2 := by rw [hnF, hnf]
  have hksLen : (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)).length = cAJ.2 := by
    rw [(R.h.ksJ _ _ hcA).1, hcAnF]
  have hrsAt : ∀ l, l < cAJ.2 →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false
        = decide (kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = .recursive ∨
            kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l = .reflexive) := by
    intro l hl
    rw [blkRss_getD hGlt,
      rsOf_getD (show l < (kindsOf (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j))).length from by
        rw [kindsOf, List.length_map, hksLen]; exact hl),
      kindsOf_getD']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `len`
    exact R.copyLen SF S hPD hi' hj' ψ ((pinsS.getD (q₀ + i) default).ψJ ψ)
  · -- `recF`
    intro l hl hrs hmem
    rw [hFssLen] at hl
    rw [hψ, hDs]
    have hkind : (dJ.ksF i' j).getD l .ordinary = .recursive ∨
        (dJ.ksF i' j).getD l .ordinary = .reflexive := by
      rw [IsBlockModel.rss_getD hj,
        rsOf_getD (show l < (dJ.ksF i' j).length from by rw [hCD.ksLen]; exact hl),
        decide_eq_true_eq] at hrs
      exact hrs
    rcases hkind with hk | hk
    · exact ⟨(R.copyRecF SF S hPD hkindsRun hi' hgb hgs CM hj' hl hmem hk).1,
        (R.copyRecF SF S hPD hkindsRun hi' hgb hgs CM hj' hl hmem hk).2,
        (R.copyRecFRead SF S hPD hkindsRun hi' hgb hgs CM hj' hl hmem hk ψ).1,
        (R.copyRecFRead SF S hPD hkindsRun hi' hgb hgs CM hj' hl hmem hk ψ).2⟩
    · exact ⟨(R.copyRecFRefl SF S hPD hkindsRun hi' hgb hgs CM hj' hl hmem hk).1,
        (R.copyRecFRefl SF S hPD hkindsRun hi' hgb hgs CM hj' hl hmem hk).2,
        (R.copyRecFReadRefl SF S hPD hkindsRun hi' hgb hgs CM hj' hl hmem hk ψ).1,
        (R.copyRecFReadRefl SF S hPD hkindsRun hi' hgb hgs CM hj' hl hmem hk ψ).2⟩
  · -- `ordF`
    intro l hl hord
    have hlF : l < cAJ.2 := by rw [hFssLen] at hl; exact hl
    rcases hkA : kindAt (mutKsOf kinds (b.ownOffset (p.k + q₀ + i') + j)) l with
      _ | _ | _ | _ | _
    · -- the copy's field is ordinary too: the LEFT arm, at the READING
      -- (task #315 L-B, DESIGN §U.78): K.42's run carries the λ-pin case,
      -- where the positivity `whnf` dropped the member mention and the two
      -- domains are no longer the same term
      obtain ⟨hrsF, -⟩ := R.copyOrdFLeft SF S hPD hi' hj' hlF hkA ψ
      refine Or.inl ⟨hrsF, ?_⟩
      intro fs₁ hfs hfit
      rw [hψ, hDs] at hfit ⊢
      exact R.copyOrdFLeftRead SF S hPD hres1 hi' hj' hlF hkA ψ ρp hsat fs₁ hfs hfit
    · -- the copy's field is recursive: the RIGHT arm, FINITARY.  At a
      -- MEMBER target the arm is PROVED (task #315 L-B); the PIN target
      -- is the residual
      have hrsT : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false
          = true := by rw [hrsAt l hlF, hkA]; simp
      refine Or.inr ⟨hrsT, R.copyOrdFRight_shape SF S hPD hkindsRun hK32 hi' hgb hgs CM hmn hj'
          hl hord hrsT, R.copyTgtLt SF S hPD hi' hj' l, ?_⟩
      by_cases hmemT : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k
      · rw [hψ, hDs]
        -- the member-target positivity run is K.42's own record, at the
        -- filter the kernel lane WIDENED (integration 3r): the residual
        -- this closure used to take is gone
        exact R.copyOrdFRightReadM SF S hPD hi' hj' hlF
          (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
            R.copyOrdFLeftRun SF S hPD hres1 hi' hj' hlF (Or.inr hmemT) h1 h2 h3 h4 h5 h6 h7)
          hkA hmemT ψ ρp hsat
      · exact hres2 l hl hord hrsT (Or.inl hkA) hmemT
    · -- the copy's field is reflexive: the RIGHT arm, at a telescope the
      -- positivity `whnf` may have MADE (task #315 L-B, DESIGN "the
      -- telescope the positivity `whnf` MAKES").  Against the OLD
      -- `EntryRead` this branch was REFUTED; under lane L-E's repaired
      -- predicate it is PROVED at a MEMBER target, and only the PIN
      -- target is left (DESIGN "does the refutation survive the repair")
      have hrsT : ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false
          = true := by rw [hrsAt l hlF, hkA]; simp
      refine Or.inr ⟨hrsT, R.copyOrdFRight_shape SF S hPD hkindsRun hK32 hi' hgb hgs CM hmn hj'
          hl hord hrsT, R.copyTgtLt SF S hPD hi' hj' l, ?_⟩
      by_cases hmemT : ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k
      · rw [hψ, hDs]
        exact R.copyOrdFRightReadRefl SF S hPD hi' hj' hlF
          (fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
            R.copyOrdFLeftRun SF S hPD hres1 hi' hj' hlF (Or.inr hmemT) h1 h2 h3 h4 h5 h6 h7)
          hkA hmemT ψ ρp hsat
      · exact hres2 l hl hord hrsT (Or.inr hkA) hmemT
    · exact absurd hkA (kindAt_ne_of hkindsRun hGlt l).1
    · exact absurd hkA (kindAt_ne_of hkindsRun hGlt l).2
  · -- `pinF`
    intro l hl hrs hnest
    obtain ⟨h1, h2, h4, h5, h6⟩ := hres3 l hl hrs hnest
    exact ⟨h1, R.copyPinF_shape SF S hPD hkindsRun hK32 hi' hgb hgs CM hmn hj' hl hrs hnest h1,
      h2, R.copyTgtLt SF S hPD hi' hj' l, h4, h5, h6⟩
  · -- `es`
    intro l hl
    have hmapGetD : ∀ (f : AnnotTerm → AnnotTerm) (L : List AnnotTerm) (n : Nat), n < L.length →
        (L.map f).getD n default = f (L.getD n default) := by
      intro f L n hn
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hn,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
      rfl
    have hEs := R.copyEs SF S hPD hi' hj' ψ
    rw [hψ] at hl
    rw [hψ, hDs, hEs, IsBlockModel.Ess_getD hj', hFssLen,
      hmapGetD _ _ l (by rw [hCD.lenE]; rw [hI.IdsM_length] at hl; exact hl)]

end Assembly2

end ConLeche.Model

