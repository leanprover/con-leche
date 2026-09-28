module

import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.TargetNestKit
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.TargetGuardParams
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Verify.Inductives.NestCallRun
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Semantics.EnvFacts
import ConLeche.Verify.InferLeaves
import ConLeche.Model.IndPointKit
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.TargetNodeCover
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.TargetCallAdm
import ConLeche.Model.Inductives.TargetCallData
import ConLeche.Model.Inductives.TargetCallEntry
public import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Model.Inductives.TargetCallEval
import ConLeche.Model.Inductives.TargetCallFrame
import ConLeche.Model.Inductives.TargetCallKid
import ConLeche.Model.Inductives.TargetCallMaj
import ConLeche.Model.Inductives.TargetCallPatch
import ConLeche.Model.Inductives.TargetCallWalk
public import ConLeche.Model.Inductives.TargetCallTie
public import ConLeche.Model.Inductives.TargetNodeDynOf

public section

/-!
# The calls at the admissible frames

`nestedNodeCalls` — every call of a rule at a related (class, node)
pair lands (`NodeLands`) — assembled from the calls' kit:

* the RULE side (`tgtCall_data`): the call's key, telescope and target,
  its typing (`targetCallOk`, K.53′) and the callee's major opened
  (`callMajor_open`);
* the WALK side at the node: the constructor's walked telescope at the
  node's frame (`dyn_ctorFit` at a derived node, `blk_ctorFit` at node
  `0`), its recorded entry (`FrameRec`, `nestMemberNfs`) and K.53′ there
  (`k53_pos`; `k53_entry` at node `0`), the called field's leaf (`callWalkSyn`);
* the SEMANTICS at an admissible visit: the node's valuation (a derived
  node's group holes over its admissible valuation, `admVal_kid`; node
  `0`'s patched frame, `admVal_patch`), the call's target in the leaf's
  reading (`fieldCall_core`), and the landing per leaf: a member hole
  (`admVal_memberLand`), a frame hole (`admVal_frameLand`), a container
  instance at a kid (`former_foldl_mem`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx
  NestHole NestCtorNf NestNodes BinderMeta BlockParts BlockShape TargetMajor fueledOps PosD PosTree
  PosKind PosNodeOk nestHoleConst closeTelescope targetPiDomsWith targetMajorNfs targetFieldNfs
  openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Small kit -/

theorem Expr.ErasedEqL.symm : ∀ {as bs : List Expr}, Expr.ErasedEqL as bs → Expr.ErasedEqL bs as
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨ConLeche.Expr.ErasedEq.symm h1, Expr.ErasedEqL.symm h2⟩

theorem Expr.ErasedEqL.length_eq : ∀ {as bs : List Expr}, Expr.ErasedEqL as bs →
    as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h2⟩ => by simp [Expr.ErasedEqL.length_eq h2]

/-- **The least tuple reads only the index sets below its width.** -/
theorem lfpTuple_congr_Is {w k : Nat} {Is Is' : Nat → V} {Φ : (Nat → V) → Nat → V}
    (h : ∀ m, m < k → Is m = Is' m) {m : Nat} (hm : m < k) :
    lfpTuple w k Is Φ m = lfpTuple w k Is' Φ m := by
  have hP : IsClosedTuple w k Is Φ = IsClosedTuple w k Is' Φ := by
    funext X
    apply propext
    unfold IsClosedTuple InTupleSpace TupleLe
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun c hc => h c hc ▸ h1 c hc, fun c hc => h c hc ▸ h2 c hc⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun c hc => (h c hc).symm ▸ h1 c hc, fun c hc => (h c hc).symm ▸ h2 c hc⟩
  have hch : ∀ {p q : (Nat → V) → Prop} (e : p = q) (hp : ∃ L, p L) (hq : ∃ L, q L),
      Classical.choose hp = Classical.choose hq := by
    intro p q e hp hq; subst e; rfl
  unfold lfpTuple
  rw [h m hm]
  by_cases hc : ∃ L, IsClosedTuple w k Is Φ L
  · have hc' : ∃ L, IsClosedTuple w k Is' Φ L := hP ▸ hc
    rw [dif_pos hc, dif_pos hc', hch hP hc hc', hP]
  · have hc' : ¬ ∃ L, IsClosedTuple w k Is' Φ L := hP ▸ hc
    rw [dif_neg hc, dif_neg hc']

/-- **A carrier at an admissible frame is the clause's** there, the index
sets agreeing below the width. -/
theorem lfpSClause_carrier_of {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V} {Is : Nat → V}
    (hIs : ∀ c, c < D.N → D.idx ψ ρp c = Is c) {m : Nat} (hm : m < D.N) :
    (lfpSClause D ψ Is).carrier ρp m = D.carrier ψ ρp m :=
  (lfpTuple_congr_Is hIs hm).symm

/-! ## K.53′ at the node's own entry -/

/-- **K.53′ at a derived node**: the constructor's walked telescope at the
node's frame is recorded (`FrameRec`); its entry is the node's key read
back, which the class matches (`NodeMajor`), so it is among the class's
recorded normal forms and its called field, opened at the rule's fields,
passed K.53′ (`k53_entry`). -/
theorem k53_pos {F : Nat} {envI : Env} {ctx : NestCtx} {aux : NestNodes}
    {u : PosTree} (hok : PosNodeOk (fueledOps .verified F) envI ctx u)
    (hfrec : ConLeche.FrameRec (fueledOps .verified F) envI ctx aux.ctors u.anc u.key.lvls
      u.key.ds u.grp)
    {envW : Env} {p : BlockShape} {formerTys : List Expr}
    {M : TargetMajor} (hNM : NodeMajor F envW p formerTys ctx M u)
    (hnfs : targetMajorNfs (fueledOps .verified F) envW p formerTys M.pfvs M.lvls M.ds M.ctors
      aux.ctors = .ok M.nfs)
    {ctors : List (ConstantVal × Nat)}
    (hctors : ConLeche.groupCtors ctx u.key.ds.length (u.grp.map (·.1)) = some ctors)
    {x : ConstantVal × Nat} (hx : x ∈ ctors) {crest : Expr} {ks : List PosKind}
    {nds : List (Expr × BinderMeta)} {cur : Expr} {ts' : List PosTree}
    (hcr : ConLeche.instPisWith u.key.ds ((x.1.type.instantiateLevelParams x.1.levelParams
      u.key.lvls).replaceConsts (ConLeche.grpSub u.key.lvls (ctx.hiAt u.anc.length) u.grp))
      = some crest)
    (hd : PosD (fueledOps .verified F) envI ctx (.tele ((ConLeche.grpNews u.key.lvls u.key.ds
      (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc) (ctx.hiAt u.anc.length + u.grp.length) x.2
      0 crest ks nds cur) ts')
    {cn : Name} (hcn : x.1.name = cn) (hcM : M.ctors.any (·.1.name == cn) = true)
    {fam : ConLeche.TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k : Nat} {pw : ConLeche.PropWhen} {ih : ConLeche.TargetIh}
    (hcall : ConLeche.targetCallOk (ConLeche.fueledOps .verified F) envW p formerTys cn fam
      fvsPref fvsF fnorm teles absM base k pw (targetFieldNfs M cn fvsF) ih = .ok ())
    (C : ConLeche.TargetCallRun .verified F envW fam fvsPref fvsF fnorm teles absM base k pw ih) :
    ∃ f, ((targetPiDomsWith fvsF ((closeTelescope nds (ctx.hiAt ((ConLeche.grpNews u.key.lvls
        u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc).length) cur).replaceFVars
        (nestHoleConst ctx ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length)
          u.grp).reverse ++ u.anc)))).getD [])[ih.field]? = some f ∧
      ConLeche.targetK53 (ConLeche.fueledOps .verified F) envW p formerTys
        (fam.majs.getD ih.callee default) (teles.getD ih.field []) C.majDom f = .ok true := by
  have he := hfrec.entry hctors hx hcr hd
  have hhi : ctx.hiAt ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length)
      u.grp).reverse ++ u.anc).length = ctx.hiAt u.anc.length + u.grp.length := by
    simp only [List.length_append, List.length_reverse, ConLeche.grpNews, List.length_map,
      ConLeche.NestCtx.hiAt]
    omega
  rw [hhi]
  refine k53_entry hcall C hnfs he hcn hcM ?_
  show ConLeche.targetClassMatch _ _ _ _ _ _ _ u.key.lvls
    (u.key.ds.map (·.replaceFVars (nestHoleConst ctx
      ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc))))
    = _
  rw [entryDs_readback hok]
  exact hNM.2.2

/-! ## The parameters and the tail of a valuation -/

section ParTail

variable {μ : CheckMode} {envC : Env} (mpC : EnvModelM V μ envC) (ctx : NestCtx) (ψ : Name → Nat)
  (ρ : Nat → V) (xs : List V)

/-- The true valuation's parameters are the prefix's. -/
theorem trueVal_param (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) {v : Nat}
    (hv : v < ctx.nP) : trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - v) = xs.getD v pt := by
  unfold trueVal nodeTrueVal
  have hlv : (nodeHv mpC.base2.acval envC ctx ψ prog).length = ctx.names.length + prog.length := by
    simp [nodeHv, nodeHoleConsts]
  rw [consList_append]
  have hl2 : ((nodeHv mpC.base2.acval envC ctx ψ prog).map (interp V ρ)).length
      = ctx.names.length + prog.length := by rw [List.length_map, hlv]
  have e : ctx.hiAt prog.length - 1 - v
      = (ctx.nP - 1 - v) + ((nodeHv mpC.base2.acval envC ctx ψ prog).map (interp V ρ)).length := by
    rw [hl2]; simp only [ConLeche.NestCtx.hiAt]; omega
  rw [e, consList_apply_add, consList_getD_of_lt _ _ _ (by rw [List.length_take]; omega),
    List.length_take, show min ctx.nP xs.length - 1 - (ctx.nP - 1 - v) = v by omega,
    List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hv, ← List.getD_eq_getElem?_getD]

/-- The true valuation's tail is the context's. -/
theorem trueVal_tail (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) (q : Nat) :
    trueVal mpC ctx ψ ρ xs prog (q + ctx.hiAt prog.length) = ρ q := by
  unfold trueVal nodeTrueVal
  have hlv : (xs.take ctx.nP ++ (nodeHv mpC.base2.acval envC ctx ψ prog).map (interp V ρ)).length
      = ctx.hiAt prog.length := by
    simp [nodeHv, nodeHoleConsts, ConLeche.NestCtx.hiAt]; omega
  rw [← hlv, consList_apply_add]

/-- **Off the holes, the true valuation's**: a valuation agreeing with the
true one off the holes has its parameters and its tail. -/
theorem parTail_of_agree (hxs : ctx.nP ≤ xs.length) {prog : List NestHole} {σ : Nat → V}
    (hag : AgreeOff (holeP (ctx.hiAt prog.length) ctx.nP (ctx.hiAt prog.length)) σ
      (trueVal mpC ctx ψ ρ xs prog)) :
    (∀ v, v < ctx.nP → σ (ctx.hiAt prog.length - 1 - v) = xs.getD v pt) ∧
    (∀ q, σ (q + ctx.hiAt prog.length) = ρ q) := by
  refine ⟨fun v hv => ?_, fun q => ?_⟩
  · rw [hag _ fun h => by have := h.2.1; simp only [ConLeche.NestCtx.hiAt] at this ⊢; omega]
    exact trueVal_param mpC ctx ψ ρ xs hxs prog hv
  · rw [hag _ fun h => by have := h.1; omega]
    exact trueVal_tail mpC ctx ψ ρ xs hxs prog q

end ParTail

/-- **A derived node's constructor stack is read**: its holes — the
members, its frames' and its group's — are stored constants at their
level counts at the constructors' environment. -/
theorem nodeHolesRead_grp {μ : CheckMode} {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI}
    {mpC : EnvModelM V μ envC} {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}
    (H : DynCtx F mk mpC ctx d ns) {u : PosTree} (hu : u ∈ ns)
    (hrd : NodeHolesRead envC ctx u.occ) :
    NodeHolesRead envC ctx
      ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc) := by
  intro a ha
  simp only [nodeHoleConsts, List.mem_append, List.mem_map, List.reverse_append,
    List.reverse_reverse] at ha
  rcases ha with ⟨n, hn, rfl⟩ | ⟨hk, hkm, rfl⟩
  · exact hrd _ (by simp only [nodeHoleConsts, List.mem_append, List.mem_map]; exact Or.inl ⟨n, hn, rfl⟩)
  · rcases hkm with hkm | hkm
    · -- a frame below: the node's own stack
      obtain ⟨-, -, -, -, -, hanc⟩ := H.hok u hu
      rcases hanc with ⟨hao, -⟩ | ⟨han, -⟩
      · refine hrd _ ?_
        simp only [nodeHoleConsts, List.mem_append, List.mem_map, List.mem_reverse]
        exact Or.inr ⟨hk, by rw [← hao]; exact List.mem_reverse.mp hkm, rfl⟩
      · rw [han] at hkm; exact nomatch hkm
    · -- the node's own group
      simp only [ConLeche.grpNews, List.mem_map] at hkm
      obtain ⟨p, hp, rfl⟩ := hkm
      obtain ⟨-, -, -, hinst, -⟩ := posD_frame_inv (H.hok u hu).1
      obtain ⟨nI, hrun⟩ := hinst p hp
      obtain ⟨cvC, capsC, hfC, hlv⟩ := ConLeche.nestInstType_lvls hrun
      obtain ⟨D, hD, -, h2⟩ := posNodeOk_blk H.hcov (H.hok u hu) p.1 (List.mem_map_of_mem hp)
      obtain ⟨nPc, ctorsAs, henvC⟩ := H.henvC
      obtain ⟨lps, hl⟩ := blk_lps_envC H.hcov H.hsub henvC hD
      obtain ⟨i, hi, hpi⟩ := exists_member_of_mem_names (lfp_namesLen mk hD) h2
      obtain ⟨cv, caps, hf, hfI, -⟩ := hl i hi
      rw [hpi] at hf hfI
      rw [H.hcov.find, hfI] at hfC
      obtain ⟨rfl, rfl⟩ : cv = cvC ∧ caps = capsC := by simpa using hfC
      exact ⟨p.1, _, _, rfl, hf, hlv⟩

/-- A class's index set is empty off its guard. -/
theorem tgtClsG_of_mem {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
    {cvc : Nat → ConstantVal} {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env}
    {p : BlockShape} {out : List (ConstantVal × TargetMajor × List Expr)} {ψ : Name → Nat}
    {ρ : Nat → V} {xs : List V} {c : Nat} {t : V}
    (ht : t ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c) :
    tgtClsG d acval envC p out ψ ρ xs c := by
  classical
  by_cases hg : tgtClsG d acval envC p out ψ ρ xs c
  · exact hg
  · unfold tgtClsIs at ht
    rw [if_neg hg] at ht
    exact absurd ht (not_mem_empty t)

/-- **An argument spine opening with variables, read** (`argsA_split` at
parameter variables, whose types need no scoping). -/
theorem argsA_split_fvars {env : Env} (m : EnvModel V env) (ψ : Name → Nat) {D0 D' : Nat}
    {args : List Expr} {argsA : List AnnotTerm}
    (hsp : DenoteMetaSpine m.acval env ψ D' args argsA) {n : Nat} (hn : n ≤ args.length)
    (hpre : ∀ q, q < n → ∃ ty, args[q]? = some (.fvar q ty)) (hnD : n ≤ D0)
    {L : List V} (hL : D' = D0 + L.length) (σ : Nat → V)
    {isR : List V} (hlen : isR.length = args.length - n)
    (htail : ∀ (l : Nat) (xa : AnnotTerm), argsA[n + l]? = some xa →
      isR[l]? = some (interp V (consList L σ) xa)) :
    argsA.map (interp V (consList L σ)) = (List.range n).map (fun q => σ (D0 - 1 - q)) ++ isR := by
  have hl := hsp.length
  apply List.ext_getElem?
  intro q
  by_cases hq : q < n
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_map,
      List.getElem?_range hq]
    obtain ⟨ty, hx⟩ := hpre q hq
    obtain ⟨v, hv, hdv⟩ := denoteMetaSpine_getElem?' hsp q _ hx
    rw [hv, Option.map_some]
    rw [denoteMeta_fvar, Option.some.injEq] at hdv
    subst hdv
    rw [Option.map_some, interp_bvar, show D' - 1 - q = (D0 - 1 - q) + L.length by omega,
      consList_apply_add]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map]
    simp only [List.length_map, List.length_range]
    by_cases hq2 : q < argsA.length
    · rw [List.getElem?_eq_getElem hq2, Option.map_some]
      have hq3 : argsA[n + (q - n)]? = some argsA[q] := by
        rw [show n + (q - n) = q by omega]; exact List.getElem?_eq_getElem hq2
      rw [htail (q - n) (argsA[q]) hq3]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      rfl

/-! ## A key's parameters, read back at a stack's suffix -/

theorem substFvars_congr_s {b D : Nat} {s s' : Nat → Expr} (hs : ∀ v, v < b → s v = s' v) :
    ∀ (X : Expr), Expr.substFvars b D s X = Expr.substFvars b D s' X := by
  intro X
  induction X with
  | bvar _ => rfl
  | fvar i ty ih =>
    simp only [Expr.substFvars]
    by_cases h : i < b
    · rw [if_pos h, if_pos h, hs i h]
    · rw [if_neg h, if_neg h, ih]
  | sort _ => rfl
  | const _ _ => rfl
  | app f a ihf iha => simp only [Expr.substFvars, ihf, iha]
  | lam t b' m iht ihb => simp only [Expr.substFvars, iht, ihb]
  | forallE t b' m iht ihb => simp only [Expr.substFvars, iht, ihb]
  | letE t v b' iht ihv ihb => simp only [Expr.substFvars, iht, ihv, ihb]
  | lit _ => rfl
  | proj _ _ e ih => simp only [Expr.substFvars, ih]

/-- The call's substitution below a suffix of the stack is the suffix's. -/
theorem callSubst_suffix {ctx : NestCtx} (X anc : List NestHole) (fvsF : List Expr) {v : Nat}
    (hv : v < ctx.hiAt anc.length) :
    callSubst ctx (X ++ anc) fvsF v = callSubst ctx anc fvsF v := by
  unfold callSubst
  by_cases h1 : v < ctx.nP
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, if_pos (by simp [ConLeche.NestCtx.hiAt] at hv ⊢; omega), if_pos hv,
      nestHoleConst_suffix X anc hv]

/-- **A key's parameters read back** (`nodeRb` at its occurrence) are, up
to annotations, the call's substitution of them at any stack whose suffix
the key's frames are (its own frames, or none at a cache hit whose
parameters see only the block). -/
theorem nodeRb_erasedEq_prog {ctx : NestCtx} {occ a X : List NestHole} (hocc : a = occ ∨ a = [])
    {x : Expr} (hx : x.fvarsBelow (ctx.hiAt a.length)) {fvsF : List Expr} {b D : Nat}
    (hb : ctx.hiAt (X ++ a).length ≤ b) :
    Expr.ErasedEq (nodeRb ctx occ x) (Expr.substFvars b D (callSubst ctx (X ++ a) fvsF) x) := by
  have hao : ctx.hiAt a.length ≤ ctx.hiAt occ.length := by
    rcases hocc with rfl | rfl
    · exact Nat.le_refl _
    · simp only [ConLeche.NestCtx.hiAt, List.length_nil]; omega
  have hxo : x.fvarsBelow (ctx.hiAt occ.length) := ConLeche.Expr.fvarsBelow_mono hao hx
  have h1 := readback_erasedEq_substFvars (fvsF := fvsF) (D := D) (Nat.le_refl _) hxo
  rw [substFvars_congr_below hao x hx] at h1
  have hXa : ctx.hiAt a.length ≤ b := by
    have : ctx.hiAt a.length ≤ ctx.hiAt (X ++ a).length := by
      simp only [ConLeche.NestCtx.hiAt, List.length_append]; omega
    omega
  rw [substFvars_congr_below hXa x hx]
  have hs : ∀ v, v < ctx.hiAt a.length → callSubst ctx occ fvsF v = callSubst ctx (X ++ a) fvsF v := by
    intro v hv
    rw [callSubst_suffix X a fvsF hv]
    rcases hocc with rfl | rfl
    · rfl
    · have := callSubst_suffix (ctx := ctx) occ [] fvsF hv
      rwa [List.append_nil] at this
  rwa [substFvars_congr_s hs] at h1

theorem erasedEqL_of_getElem : ∀ {as bs : List Expr}, as.length = bs.length →
    (∀ (q : Nat) (a b : Expr), as[q]? = some a → bs[q]? = some b → Expr.ErasedEq a b) →
    Expr.ErasedEqL as bs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, he =>
    ⟨he 0 a b rfl rfl, erasedEqL_of_getElem (by simpa using h)
      fun q a' b' h1 h2 => he (q + 1) a' b' h1 h2⟩

theorem Expr.ErasedEqL.toErasedEqs : ∀ {as bs : List Expr}, Expr.ErasedEqL as bs →
    ConLeche.ErasedEqs as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h1, Expr.ErasedEqL.toErasedEqs h2⟩

/-- **The callee's class at a listed node** (`NodeMajor`): an outside
major naming a member of the node's group, matching the leaf's levels
(the node's) and parameters `P`, which are — up to annotations — the
call's arguments at the node's key, read at a stack of which the node's
frames are a suffix: the match reads its recorded side up to annotations
(`targetClassMatch_congr`). -/
theorem nodeMajor_of_call {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {o : PosTree} (hok : PosNodeOk ops env ctx o) {F : Nat} {envC : Env} {p : BlockShape}
    {formerTys : List Expr} {M : TargetMajor} (hMo : M.member = none)
    (hind : M.ind ∈ o.grp.map (·.1)) {us' : List Level} (hlv : us' = o.key.lvls) {P : List Expr}
    (hCM : ClassMatches F envC p formerTys M us' P) {args : List Expr} {X prog : List NestHole}
    (hprog : prog = X ++ o.anc) {b D : Nat} {fvsF : List Expr} (hb : ctx.hiAt prog.length ≤ b)
    (hPl : P.length = o.key.ds.length) (htake : args.take o.key.ds.length = o.key.ds)
    (hargs : ∀ (q : Nat) (xM xW : Expr), P[q]? = some xM → args[q]? = some xW →
      Expr.ErasedEq xM (Expr.substFvars b D (callSubst ctx prog fvsF) xW)) :
    NodeMajor F envC p formerTys ctx M o := by
  refine ⟨hMo, hind, ?_⟩
  have hocc : o.anc = o.occ ∨ o.anc = [] := by
    rcases hok.2.2.2.2.2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hds := posNodeOk_dsAnc hok
  have hE : Expr.ErasedEqL P (o.key.ds.map (nodeRb ctx o.occ)) := by
    refine erasedEqL_of_getElem (by rw [hPl, List.length_map]) fun q a' b' ha hb' => ?_
    rw [List.getElem?_map] at hb'
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hb'
    have hq : q < o.key.ds.length := (List.getElem?_eq_some_iff.mp hx).1
    have hax : args[q]? = some x := by
      have := congrArg (·[q]?) htake
      simp only [List.getElem?_take, if_pos hq] at this
      rw [this, hx]
    have h1 := hargs q a' x ha hax
    have hxb := (hds x (List.mem_of_getElem? hx)).1.fvarsBelow
    rw [hprog] at hb h1
    have h2 := nodeRb_erasedEq_prog (occ := o.occ) (X := X) (fvsF := fvsF) (D := D) hocc hxb hb
    exact ConLeche.Expr.ErasedEq.trans h1 (ConLeche.Expr.ErasedEq.symm h2)
  unfold ClassMatches
  rw [← hlv, ← ConLeche.targetClassMatch_congr hE.toErasedEqs]
  exact hCM

/-- **A member major's data** (`TargetMajorRun.member`): the block's
levels, and the recursor's first parameter openers. -/
theorem tyEntry_member {mode : CheckMode} {F : Nat} {fe : ConLeche.FEnv} {p : BlockShape}
    {nested : Bool} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rc : ConLeche.RecShape} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member.isSome = true) :
    M.lvls = p.lps.map .param ∧ M.ds = E.fvs.take p.nP ∧
      openPisAtFvars (rc.mI + 1) cvRi.type 0 = some (E.fvs, E.concl) ∧ p.nP ≤ rc.mI := by
  obtain ⟨_, fvs, concl, _, _, maj, _, _, _, hroom, hle, hopen, _, major, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _⟩ := E
  cases major with
  | member => exact ⟨rfl, rfl, hopen, Nat.le_trans hroom hle⟩
  | outside => simp at hM

/-- **A major's parameters number its parameter count.** -/
theorem tyEntry_dsLen {mode : CheckMode} {F : Nat} {fe : ConLeche.FEnv} {p : BlockShape}
    {nested : Bool} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rc : ConLeche.RecShape} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) :
    M.ds.length = M.nPc := by
  obtain ⟨_, fvs, concl, _, _, maj, _, _, _, hroom, hle, hopen, _, major, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _⟩ := E
  cases major with
  | member =>
    have := ConLeche.Verify.openPisAtFvars_length _ hopen
    show (fvs.take p.nP).length = p.nP
    simp only [List.length_take]
    omega
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hl => exact hl

/-- **A member major's parameter count is the block's.** -/
theorem tyEntry_nPc_member {mode : CheckMode} {F : Nat} {fe : ConLeche.FEnv} {p : BlockShape}
    {nested : Bool} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rc : ConLeche.RecShape} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member.isSome = true) : M.nPc = p.nP := by
  obtain ⟨_, fvs, concl, _, _, maj, _, _, _, hroom, hle, hopen, _, major, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _⟩ := E
  cases major with
  | member => rfl
  | outside => simp at hM

/-- **A major's parameters pass the class match's guard**: bvar-closed,
below the recursor's prefix openers. -/
theorem tyEntry_dsGuard {mode : CheckMode} {F : Nat} {fe : ConLeche.FEnv} {p : BlockShape}
    {nested : Bool} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rc : ConLeche.RecShape} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) :
    ∀ a ∈ M.ds, a.bvarB = 0 ∧ a.fvarB ≤ M.pfvs.length := by
  obtain ⟨_, fvs, concl, _, _, maj, _, _, _, hroom, hle, hopen, _, major, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _⟩ := E
  have hl := ConLeche.Verify.openPisAtFvars_length _ hopen
  cases major with
  | member =>
    intro a ha
    dsimp only at ha ⊢
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
    have hil : i < p.nP := by
      have := (List.getElem?_eq_some_iff.mp hi).1; simp only [List.length_take] at this; omega
    rw [List.getElem?_take, if_pos hil] at hi
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hopen i a hi
    refine ⟨by rw [ConLeche.Expr.bvarB_eq]; rfl, ?_⟩
    show (Expr.fvar (0 + i) ty).fvarB ≤ (fvs.take rc.rP).length
    rw [ConLeche.Expr.fvarB_eq, List.length_take]
    simp only [ConLeche.Expr.fvarRange]
    omega
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hl' hsc =>
    intro a ha
    dsimp only at ha ⊢
    obtain ⟨h0, hf⟩ := hsc a ha
    simp only [List.length_take]
    exact ⟨h0, by omega⟩

/-! ## THE CALLS -/

set_option maxHeartbeats 16000000 in
/-- **THE CALLS AT THE ADMISSIBLE FRAMES** (see the module docstring): at a
nested stage's context, the formers' model `mk` (`FormersModelAt`'s
components) and a node list `ns` — the positivity derivation's nodes
(`PosNodeOk`), owned, closed under kids and parents, read in their stack
contexts at `mk` (`NodeSemAt`), with the class tie's node facts
(`NodeListFacts`) — at a related pair and a true decoding, every call
target lands at a node related to its class: its own group, an owner `G`
holds of, or a deeper node at an admissible frame (`nodeAdm`) of the
visit extended by the caller's tuple (`NodeLands`; `TgtNodeDyn.hcall`). -/
theorem nestedNodeCalls {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {nodesR : ConLeche.NestNodes}
    (hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      nodesR)
    {mk : EnvModelM V μ envI} (hmkC : LfpCover mk pp.toBlockShape.memberNames)
    (hmk : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks)
    (hag : ∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n)
    (hsubC : ∀ D ∈ mpC.lfpBlocks, D = dR.toLfp ∨ D ∈ mk.lfpBlocks)
    (htr : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mk.base2.acval envI ψ dd e = some ea →
        denoteMeta mpC.base2.acval envC ψ dd e = some ea)
    (hcoreK : BlockHoleCtxFacts mk.base2 dR pp.lps cvTasR pp.toBlockShape isRecR)
    {fvsP : List Expr} {ns : List PosTree}
    (hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t)
    (hown : ∀ t ∈ ns, NodeOwned (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t)
    (hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns)
    (hpar : ∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids)
    (hsem : ∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ (pp.nestCtx fvsP envI.find? envI.consts)
      (dR.holeCtx ψ).reverse t)
    (hfrec : ∀ t ∈ ns, ConLeche.FrameRec (fueledOps .verified F) envI
      (pp.nestCtx fvsP envI.find? envI.consts) nodesR.ctors t.anc t.key.lvls t.key.ds t.grp)
    (hmemF : MemberForests F envI pp cvTasR ctorsAsR nfsR fvsP ns)
    {par : Nat → Nat} (hPP : ParentPtrs ns par)
    (hF : NodeListFacts mpC (pp.nestCtx fvsP envI.find? envI.consts) ns)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind)
    {ψ : Name → Nat} {ρ : Nat → V} {xs : List V}
    (hgd : ∃ c, c < (tgtRs out).length ∧
      tgtClsG dR mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c)
    (hfrT : NodeFrameTie mpC.base2.acval (pp.nestCtx fvsP envI.find? envI.consts) pp.toBlockShape
      out ns ψ ρ xs envC F (cvTasR.map (·.type))) :
    ∀ c b, c < (tgtRs out).length →
      nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find? envI.consts) dR pp.toBlockShape out ns
        ψ ρ xs envC F (cvTasR.map (·.type)) c b → ∀ t j fs,
      t ∈ˢ (nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
        (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)
        (tgtClsM mc pp.toBlockShape out c) →
      (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b)
        (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)
        ((nlDb mpC dR ns b).carrier (nlψ envC ns ψ b)
          (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) t
        (tgtClsM mc pp.toBlockShape out c) j fs →
      ∀ c' t' y, c' < (tgtRs out).length →
        t' ∈ˢ tgtClsIs dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c' →
        y ∈ˢ app (tgtClsCr dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c') t' →
        tgtCall μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out
          mpC.base2.acval envC ψ (tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs
          (tagged c' t' y) →
        ∃ b', nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find? envI.consts) dR pp.toBlockShape
            out ns ψ ρ xs envC F (cvTasR.map (·.type)) c' b' ∧
          NodeLands (ns.length + 1) (nlDb mpC dR ns) (nlψ envC ns ψ)
            (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs) (nlDp ns)
            (nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par) b
            (tgtClsM mc pp.toBlockShape out c) t j fs b' (tgtClsM mc pp.toBlockShape out c') t' y := by
  intro c b hc hR t j fs ht hHF c' t' y hc' ht' hy hcall
  obtain rfl := CheckMode.eq_verified hμ
  have H := dynCtx_of hctx hmkC hmk hag hsubC htr hcoreK hok hown hkids hpar hsem hF
  have hctx' := hctx
  obtain ⟨hRec, hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov, -, -⟩ := hctx'
  obtain ⟨R, hRaux⟩ := ConLeche.targetRecCheck_run_aux
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have h := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  have hmr : BlockMembersRun mpC.base2 dR pp.toBlockShape cvTasR := by
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; exact blockMembersRun_seam hN hS hcore
  have hM : BlockModelAt mpC.base2 dR.memberNames dR := by
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; exact blockModelAt_seam h hN hS hcore hlfp
  -- the prefix's parameters
  have hparams : SpineFit ρ (dR.params ψ) (xs.take dR.nP) := by
    obtain ⟨c0, hc0, hg0⟩ := hgd
    exact tgtGuard_params hμ hctx hc0 hg0
  have hxs : dR.nP ≤ xs.length := by
    have hl := SpineFit.length_eq hparams
    have hpl : (dR.params ψ).length = dR.nP := by
      have h0 := H.hΔ0 ψ
      rw [List.length_reverse, BlockData.holeCtx, List.length_append, List.length_map,
        List.length_range] at h0
      have hk : dR.k = (pp.nestCtx fvsP envI.find? envI.consts).names.length := by
        rw [H.hnames]; exact (lfp_namesLen mpC H.hd0).symm
      have hnP := H.hnP
      simp only [ConLeche.NestCtx.hiAt] at h0
      omega
    rw [List.length_take, hpl] at hl
    omega
  have hrs : ∀ c (hc : c < (tgtRs out).length),
      (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := fun c hc => List.getElem?_eq_getElem hc
  have hnPc : ∀ c, c < (tgtRs out).length →
      (pp.nestCtx fvsP envI.find? envI.consts).nP ≤ tgtRP pp.toBlockShape c := by
    intro c hc
    obtain ⟨-, hlen, hall⟩ := ConLeche.recStageG_recNames h
    obtain ⟨_, _, _, _, -, -, hle, -⟩ := hall c (by rw [← hlen]; exact hc)
    exact hle
  have hpd : ∀ c, c < (tgtRs out).length →
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        = tgtRP pp.toBlockShape c := fun c hc => blockRulePdomsAV_length hμ mpC h (hrs c hc) ψ
  -- the rule side: the class's decoding, fitting the rule
  obtain ⟨hDeq, hψeq, hFreq⟩ := nlRel_tie (Dc := Dc) (mc := mc) (cvc := cvc) hcov hF hcls hsel
    hnPc hpd hfrT hc hR
  have hti : t ∈ˢ tgtClsIs dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c := by
    unfold tgtClsIs; rw [if_pos hR.1, hDeq, hψeq, hFreq]; exact ht
  have hfitC : tgtClsFit dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c t j fs := by
    unfold tgtClsFit; rw [hDeq, hψeq, hFreq]; exact hHF
  have hjC : j < blockRecNCt (tgtRs out) c := by
    have hj0 := hHF.1
    rw [← hDeq] at hj0
    have hnCt : blockRecNCt (tgtRs out) c
        = (tgtClsD dR Dc out c).nctors (tgtClsM mc pp.toBlockShape out c) := by
      unfold blockRecNCt
      rw [List.getD_eq_getElem?_getD, hrs c hc, Option.getD_some]
      by_cases hm : (tgtMajor out c).member.isSome = true
      · simp only [tgtClsD, tgtClsM, hm, if_true]
        rw [← tgtCls_hctM h hdR c _ (tgtMemAt_of_member hc hm) (hrs c hc)]
        rfl
      · have hMo : (tgtMajor out c).member = none := by
          cases h' : (tgtMajor out c).member with
          | none => rfl
          | some _ => rw [h'] at hm; exact absurd rfl hm
        have hm' : (tgtMajor out c).member.isSome = false := by rw [hMo]; rfl
        simp only [tgtClsD, tgtClsM, hm', Bool.false_eq_true, if_false]
        rw [tgtRs_ctors (hrs c hc)]
        exact (hcls c hc hMo).hlen
    rw [hnCt]; exact hj0
  have hspF := tgtCls_hspF hμ hcov h R hcls hdR hcore hmr hM ψ ρ 0 xs c hc j hjC t fs hti hfitC
  rw [tgtFdomsK, liftDomsK_zero] at hspF
  have hxsP : xs.length = pp.toBlockShape.rulePrefixAt c :=
    (tgtClsIs_pref hti).length_eq.trans (blockRulePdomsAV_length hμ mpC h (hrs c hc) ψ)
  obtain ⟨rc, rhs0, rhs, cA, Q, ih, bs, hcA, hrP, hQF, hQP, hfvF, hfvP, hfvW, hih, hfld, hfsl, hxl,
    hcallOk, hidxLen, hrPc, hcal, hidxB, hbs, hv⟩ :=
    tgtCall_data hμ hcov h R hcls hdR hS hcore hmr ψ ρ hc hjC hspF hxsP _ hcall
  obtain ⟨C⟩ := ConLeche.targetCallOk_run hcallOk
  -- the callee's major, opened at the call's telescope
  generalize htele : (Q.fnorm.map fun t => t.piBinders.1).getD ih.field [] = tele at hidxB hbs hv C
  have hosL := locOpen_locList (rc.rP + cA.2) tele.length
  obtain ⟨I, us, P, hmajO, hment, hshape⟩ := callMajor_open h R C hQP hfvP hcal hidxLen hrPc
    hosL.allFvars (by rw [hosL.1]; exact fun x hx => (hidxB x hx).1)
  have hctxN : (pp.nestCtx fvsP envI.find? envI.consts).names = pp.toBlockShape.memberNames := rfl
  have hfvF' : ∀ l, l < Q.fvsF.length → ∃ ty, Q.fvsF[l]? = some (.fvar (rc.rP + l) ty) :=
    fun l hl => hfvF l (hQF ▸ hl)
  have hmajO' : C.majDom.instantiateList (locOpen (rc.rP + Q.fvsF.length) tele.length) 0
      = Expr.mkAppN (.const I us) (P ++ ih.idx.map (·.instantiateList
        (locOpen (rc.rP + cA.2) tele.length) 0)) := by rw [hQF]; exact hmajO
  have hwb : ∀ d e w, (fueledOps .verified F).whnf envI d e = .ok w →
      e.looseBVarsBounded 0 = true → w.looseBVarsBounded 0 = true :=
    fun d e w hw hb => ConLeche.whnf_looseBVars mk.base2.wf F hw hb
  have hnPr : (pp.nestCtx fvsP envI.find? envI.consts).nP ≤ rc.rP := by
    rw [hrP]
    simpa [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, tgtRP] using hnPc c hc
  have hxsC : (pp.nestCtx fvsP envI.find? envI.consts).nP ≤ xs.length := by rw [H.hnP]; exact hxs
  have hfvWF : ∀ x ∈ Q.fvsF, Expr.WScoped (rc.rP + Q.fvsF.length) x := by rw [hQF]; exact hfvW
  have hflF : fs.length = Q.fvsF.length := by rw [hQF, hfsl]
  -- an outside callee at a listed node naming it: as many parameters as the node's key
  have houtLen : ∀ {o : PosTree}, o ∈ ns → (tgtMajor out ih.callee).member = none →
      (tgtMajor out ih.callee).ind ∈ o.grp.map (·.1) →
      (tgtMajor out ih.callee).ds.length = o.key.ds.length := by
    intro o ho hMo' hind
    obtain ⟨dsa0, -, -, -, hlenP, -⟩ := tgtOutSatW hμ mpC hcov h R (hrs _ hcal) hMo'
      (hcls _ hcal hMo') ψ
    rw [hsel _ hcal hMo'] at hlenP
    obtain ⟨D, hD, h1, h2⟩ := posNodeOk_blk H.hcov (H.hok o ho) _ hind
    rw [lfpSel_eq_of_mem H.hcovC dR.toLfp (H.hsub D hD) h1 h2] at hlenP
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlenPo, -, -⟩ := dyn_nodeBlock H ho
    rw [← hlenP, hlenPo]
  -- a group name is no member
  have hgrpNM : ∀ {o : PosTree}, o ∈ ns → ∀ n ∈ o.grp.map (·.1),
      n ∉ pp.toBlockShape.memberNames := by
    intro o ho n hn hmem
    obtain ⟨D, hD, -, h2⟩ := posNodeOk_blk H.hcov (H.hok o ho) n hn
    obtain ⟨i, hi, rfl⟩ := exists_member_of_mem_names (lfp_namesLen mk hD) h2
    exact hmkC.fresh D hD i hi hmem
  -- a callee naming a group member is outside
  have hcalOut : ∀ {o : PosTree}, o ∈ ns → I ∈ o.grp.map (·.1) →
      (tgtMajor out ih.callee).member = none ∧ I = (tgtMajor out ih.callee).ind := by
    intro o ho hIo
    rcases hshape with ⟨-, ms, hms, hIms, -, -⟩ | h'
    · exfalso
      refine hgrpNM ho I hIo ?_
      rw [hIms]
      simp only [ConLeche.BlockShape.memberNames, List.mem_map]
      exact ⟨ms, List.mem_of_getElem? hms, rfl⟩
    · exact ⟨h'.1, h'.2.1⟩
  -- the callee's class, as the family carries it
  have hmajsEq : (tgtFam pp.toBlockShape out).majs.getD ih.callee default = tgtMajor out ih.callee := by
    simp only [tgtFam, tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases out[ih.callee]? <;> rfl
  -- an outside callee landing at a related node: its component and tuple there
  have htupOut : ∀ {o : Nat}, nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find? envI.consts) dR
      pp.toBlockShape out ns ψ ρ xs envC F (cvTasR.map (·.type)) ih.callee o → (tgtMajor out ih.callee).member = none →
      tgtClsM mc pp.toBlockShape out ih.callee = nlComp mpC dR ns o (tgtMajor out ih.callee).ind ∧
      tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ ih.callee
        = tupW ((nlDb mpC dR ns o).u (nlComp mpC dR ns o (tgtMajor out ih.callee).ind)
          (nlψ envC ns ψ o)) := by
    intro o hRo hMo'
    obtain ⟨hD', hψ', -⟩ := nlRel_tie (Dc := Dc) (mc := mc) (cvc := cvc) hcov hF hcls hsel hnPc
      hpd hfrT hcal hRo
    have hTO' := hcls _ hcal hMo'
    have hcomp : nlComp mpC dR ns o (tgtMajor out ih.callee).ind = mc ih.callee := by
      unfold nlComp
      rw [← hD']
      simp only [tgtClsD, hMo', Option.isSome_none, Bool.false_eq_true, if_false]
      rw [← hTO'.hmem]
      exact idxOf_member hTO'.hnN hTO'.hkN hTO'.hmm
    have hM' : tgtClsM mc pp.toBlockShape out ih.callee = mc ih.callee := by
      simp [tgtClsM, hMo']
    refine ⟨by rw [hM', hcomp], ?_⟩
    funext is
    simp only [tgtClsTup, tgtClsU]
    rw [hD', hψ', hM', hcomp]
  -- an outside callee's index count is the call's
  have hidxOut : (tgtMajor out ih.callee).member = none →
      ih.idx.length = (tgtMajor out ih.callee).nIdx := by
    intro hMo'
    obtain ⟨rcC, uC, hrcC, ⟨EC⟩⟩ := targetEntryAt R (hrs _ hcal)
    have e1 : (tgtFam pp.toBlockShape out).mIs.getD ih.callee 0 = rcC.mI := by
      simp [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hrcC]
    have e2 : (tgtFam pp.toBlockShape out).rPs.getD ih.callee 0 = rcC.rP := by
      simp [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hrcC]
    have := EC.hmI
    omega
  obtain ⟨cvTa0, rest0, holes0, hcv0, hop0, hholes0, hMF⟩ := hmemF
  have hbN : b ≤ ns.length := by
    rcases hR.2 with ⟨-, h'⟩ | ⟨-, h', -⟩
    · omega
    · exact h'
  /- The visited node: node `0` (the member constructors, stack `[]`) or a
  derived node (its group's constructors, over its stack `prog`) — the walked
  constructor, its reading at an admissible visit, the owners of its stack's
  holes, and the listed nodes its container instances land at. -/
  obtain ⟨prog, own, nF, crest, ks, nds, cur, ts, hd, hcrC, hcurC, hndC, hndl, hK, hread, hvisit,
      hstk, hkidN⟩ : ∃ (prog : List NestHole) (own : Nat → Nat) (nF : Nat) (crest : Expr)
      (ks : List PosKind) (nds : List (Expr × ConLeche.BinderMeta)) (cur : Expr)
      (ts : List PosTree),
      PosD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
        (.tele prog ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length) nF 0 crest ks
          nds cur) ts ∧
      crest.looseBVarsBounded 0 = true ∧ cur.looseBVarsBounded 0 = true ∧
      (∀ (l : Nat) (p : Expr × ConLeche.BinderMeta), nds[l]? = some p →
        p.1.looseBVarsBounded 0 = true ∧
          Expr.WScoped ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + l) p.1) ∧
      nds.length = nF ∧
      (∃ f, ((ConLeche.targetPiDomsWith Q.fvsF ((ConLeche.closeTelescope nds
          ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length) cur).replaceFVars
            (ConLeche.nestHoleConst (pp.nestCtx fvsP envI.find? envI.consts) prog))).getD
              [])[ih.field]? = some f ∧
        ConLeche.targetK53 (fueledOps .verified F) envC pp.toBlockShape (cvTasR.map (·.type))
          (tgtMajor out ih.callee) tele C.majDom f = .ok true) ∧
      NodeHolesRead envC (pp.nestCtx fvsP envI.find? envI.consts) prog ∧
      (∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
        nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par b G ρ' →
        ∀ Y, InTupleSpace ((nlDb mpC dR ns b).w (nlψ envC ns ψ b)) (nlDb mpC dR ns b).N
            ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
              (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y →
        (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
        ∃ σN, AdmVal mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs own
            (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
              (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y) prog σN ∧
          fs.length = nF ∧
          ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
            ∃ nda, denoteMeta mpC.base2.acval envC ψ
                ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + i) nd = some nda ∧
              fs.getD i pt ∈ˢ interp V (consList (fs.take i) σN) nda ∧
              AnnotValid V (consList (fs.take i) σN) nda) ∧
      (prog = [] ∨ ∃ u, 0 < b ∧ ns.getD (b - 1) default = u ∧
        (ConLeche.grpNews u.key.lvls u.key.ds
          ((pp.nestCtx fvsP envI.find? envI.consts).hiAt u.anc.length) u.grp).reverse ++ u.anc
            = prog ∧
        own = fun i => if i < u.anc.length then holeOwner ns par b i else b) ∧
      (∀ u'' ∈ ts, u''.occ = prog → u'' ∈ ns ∧ ∃ b'', 0 < b'' ∧ b'' ≤ ns.length ∧
        ns.getD (b'' - 1) default = u'' ∧ nlDp ns b < nlDp ns b'' ∧
        (u''.anc = prog → u''.anc ≠ [] → holeOwner ns par b'' = own)) := by
    by_cases hb0 : b = 0
    · /- ### Node `0` -/
      subst hb0
      have hmem : (tgtMajor out c).member.isSome = true := by
        obtain ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ := hR
        · exact h'
        · exact absurd h' (Nat.lt_irrefl 0)
      have hmR := tgtMemAt_of_member hc hmem
      obtain ⟨ms, hms, hcsR, -⟩ := recStage_ctorsAt (hm := hmR) h (hrs c hc)
      generalize hmdef : pp.toBlockShape.recTgtAt c = m at hms hcsR
      have hmM : tgtClsM mc pp.toBlockShape out c = m := by simp [tgtClsM, hmem, hmdef]
      have hmc : m < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hcsR).1
      have hctM : dR.ctorsM m = ((tgtRs out)[c]'hc).2.2.2 := by
        have := hctorsAs m hmc; rw [hcsR] at this; exact (Option.some.inj this).symm
      have hcj : (dR.ctorsM m)[j]? = some cA := by rw [hctM]; exact hcA
      have hfacts : pp.toBlockShape.memberNames = dR.memberNames ∧ pp.nP = dR.nP ∧
          pp.nIdxs = dR.nIdxs ∧ dR.k = dR.memberNames.length ∧ m < dR.k := by
        obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
        exact ⟨rfl, rfl, rfl, by simp [blockDataOf, blockDataPre, BlockData.withPhi,
          ConLeche.BlockShape.k, ConLeche.BlockShape.memberNames],
          (List.getElem?_eq_some_iff.mp hms).1⟩
      obtain ⟨hnamesD, hnPD, hnIdxsD, hkD, hmk⟩ := hfacts
      obtain ⟨hfC, -⟩ := hcore.2.2.2 m hmk j cA hcj
      have hw := mpC.base2.wf _ (List.mem_of_find?_eq_some hfC)
      -- the member forest
      obtain ⟨crest, ks, ts, hcrest, hd, ⟨ty, hty⟩, hforest⟩ :=
        hMF m _ (by rw [hcsR, ← hctM]) j cA hcj
      obtain ⟨nds, cur, htele0, htyN, hndC, hnl, hcrC, hcurC, -, hsemB⟩ := blk_ctorFit mk ψ hN
        hcoreK hnamesD rfl hnPD hnIdxsD hkD hcv0 hop0 hholes0 hcj hw.1 hw.2.2.2.1 hcrest hty hd
      -- the entry: the member constructor's recorded normal form
      obtain ⟨cvTa0', fvsP', rest', hcv0', hop0', hent⟩ :=
        ConLeche.checkBlockPositivity_memberEntry hPos
      rw [hcv0] at hcv0'
      obtain rfl := Option.some.inj hcv0'
      rw [hop0] at hop0'
      obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest0 = rest' := by simpa using hop0'
      have he := hent m _ (by rw [hcsR, ← hctM]) j cA hcj
      obtain ⟨rcC, uC, -, ⟨EC⟩⟩ := targetEntryAt R (hrs c hc)
      obtain ⟨hMl, hMd, hEop, hEle⟩ := tyEntry_member EC hmem
      have hnfs : targetMajorNfs (fueledOps .verified F) envC pp.toBlockShape
          (cvTasR.map (·.type)) (tgtMajor out c).pfvs (tgtMajor out c).lvls (tgtMajor out c).ds
          (tgtMajor out c).ctors nodesR.ctors = .ok (tgtMajor out c).nfs := by
        have hmemO : out.getD c default ∈ out := by
          have hco : c < out.length := by simpa [tgtRs] using hc
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hco, Option.getD_some]
          exact List.getElem_mem hco
        rw [← hRaux]; exact ConLeche.targetRecRun_nfs R _ hmemO
      have hdsP : Expr.ErasedEqL (pp.nestCtx fvsP envI.find? envI.consts).params
          (tgtMajor out c).ds := by
        rw [hMd]
        have hlP : fvsP.length = pp.nP := ConLeche.Verify.openPisAtFvars_length _ hop0
        have hlE : EC.fvs.length = rcC.mI + 1 := ConLeche.Verify.openPisAtFvars_length _ hEop
        refine erasedEqL_of_fvarIdx _ _ 0 (fun i x hx => ?_) (fun i x hx => ?_)
          (by show fvsP.length = _; rw [List.length_take, hlP, hlE]; omega)
        · obtain ⟨ty', h'⟩ := ConLeche.openPisAtFvars_index _ _ _ hop0 i x hx
          exact ⟨ty', h'⟩
        · rw [List.getElem?_take] at hx
          split at hx
          · obtain ⟨ty', h'⟩ := ConLeche.openPisAtFvars_index _ _ _ hEop i x hx
            exact ⟨ty', h'⟩
          · exact nomatch hx
      have hcM : (tgtMajor out c).ctors.any (·.1.name == cA.1.name) = true := by
        rw [← tgtRs_ctors (hrs c hc)]
        exact List.any_eq_true.mpr ⟨cA, List.mem_of_getElem? hcA, by simp⟩
      have hCM := ConLeche.targetClassMatch_self (ops := fueledOps .verified F) (env := envC)
        (p := pp.toBlockShape) (formerTys := cvTasR.map (·.type)) (us := (tgtMajor out c).lvls)
        (tyEntry_dsGuard EC) (Expr.ErasedEqL.toErasedEqs (Expr.ErasedEqL.symm hdsP))
      have hK := k53_entry hcallOk C hnfs he rfl hcM (by rw [hMl] at hCM ⊢; exact hCM)
      rw [htele, hmajsEq] at hK
      simp only at hK
      rw [htyN] at hK
      -- the members' index counts
      have hids0 : ∀ t, t < (pp.nestCtx fvsP envI.find? envI.consts).names.length →
          (dR.toLfp.ids t ψ).length = (pp.nestCtx fvsP envI.find? envI.consts).nIdxs.getD t 0 := by
        intro t htn
        have htk : t < dR.k := by rw [hkD, ← hnamesD]; exact htn
        have := blockMembers_IdsM_length hmr htk ψ
        rw [BlockData.nIdxAt, ← hnIdxsD] at this
        exact this
      have hnl0 : nlDb mpC dR ns 0 = dR.toLfp := by unfold nlDb; rw [if_pos rfl]
      have hnψ0 : nlψ envC ns ψ 0 = ψ := by unfold nlψ; rw [if_pos rfl]
      have hnF0 : nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs 0
          = consList (xs.take dR.nP) ρ := by unfold nlFr; rw [if_pos rfl]
      have hcl := mpC.lfpClause_of_mem H.hd0
      have hmN : m < dR.toLfp.N := Nat.lt_of_lt_of_le hmk hcl.kN
      -- the constructor at an admissible visit: the patched frame
      have hvisit : ∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
          nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par 0 G ρ' →
          ∀ Y, InTupleSpace ((nlDb mpC dR ns 0).w (nlψ envC ns ψ 0)) (nlDb mpC dR ns 0).N
              ((nlDb mpC dR ns 0).idx (nlψ envC ns ψ 0)
                (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs 0)) Y →
          (nlDb mpC dR ns 0).HFits (nlψ envC ns ψ 0) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
          ∃ σN, (∀ own, AdmVal mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs own
              (addOwn G 0 (nlDb mpC dR ns 0).N ((nlDb mpC dR ns 0).idx (nlψ envC ns ψ 0)
                (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs 0)) Y) [] σN) ∧
            ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
              ∃ nda, denoteMeta mpC.base2.acval envC ψ
                  ((pp.nestCtx fvsP envI.find? envI.consts).hiAt ([] : List NestHole).length + i) nd
                    = some nda ∧
                fs.getD i pt ∈ˢ interp V (consList (fs.take i) σN) nda ∧
                AnnotValid V (consList (fs.take i) σN) nda := by
        intro G ρ' hA Y hY hH
        have hA' := hA
        unfold nodeAdm at hA'
        rw [if_pos rfl] at hA'
        subst hA'
        rw [hnl0, hnψ0, hnF0, hmM] at hH
        have hY' := hY
        rw [hnl0, hnψ0, hnF0] at hY'
        refine ⟨patchFrame dR.toLfp ψ ρ (xs.take dR.nP) Y
            (memberTrue mpC (pp.nestCtx fvsP envI.find? envI.consts) ψ ρ xs),
          fun own => admVal_patch H ψ ρ xs hparams hxs hids0 hY' own G, fun i nd hnd => ?_⟩
        have hfitP := (patchFrame_fit hcl hparams Y
          (memberTrue mpC (pp.nestCtx fvsP envI.find? envI.consts) ψ ρ xs) hmN hH.1 fs).mp hH.2.1
        obtain ⟨-, hmemB⟩ := hsemB _ (patchFrame_sat H ψ ρ xs hxsC hparams hY') fs hfitP
        obtain ⟨nda, hnda, hmemI, hval⟩ := hmemB i nd hnd
        exact ⟨nda, H.htr ψ _ nd hnda, hmemI, hval⟩
      have hread : NodeHolesRead envC (pp.nestCtx fvsP envI.find? envI.consts) [] := by
        intro a ha
        simp only [nodeHoleConsts, List.reverse_nil, List.map_nil, List.append_nil,
          List.mem_map] at ha
        obtain ⟨n, hn, rfl⟩ := ha
        change n ∈ pp.toBlockShape.memberNames at hn
        obtain ⟨c0, hc0, rfl⟩ := List.getElem_of_mem hn
        have hck : c0 < dR.k := by rw [hkD, ← hnamesD]; exact hc0
        obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTasR[c0]? = some cvTb :=
          ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hck)⟩
        have hname := hN.1 c0 cvTb hcvb
        have hlpsT := hS.lpsT c0 cvTb hck hcvb
        obtain ⟨hf, -⟩ := hcore.1 c0 cvTb hcvb
        rw [← hname] at hf
        unfold BlockData.memberName at hf
        rw [← hnamesD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc0,
          Option.getD_some] at hf
        refine ⟨_, _, _, rfl, hf, ?_⟩
        show (pp.lps.map Level.param).length = cvTb.levelParams.length
        rw [List.length_map, hlpsT]
      refine ⟨[], fun _ => 0, cA.2, crest, ks, nds, cur, ts, htele0, hcrC, hcurC, hndC, hnl, hK,
        hread, fun G ρ' hA Y hY hH => ?_, Or.inl rfl, fun u'' hu'' _ => ?_⟩
      · obtain ⟨σN, hAdm, hmemN⟩ := hvisit G ρ' hA Y hY hH
        exact ⟨σN, hAdm _, hfsl, hmemN⟩
      · have hu''ns : u'' ∈ ns := hforest u'' (PosTree.mem_forest_iff.mpr
          ⟨u'', hu'', PosTree.mem_nodes.mpr (Or.inl rfl)⟩)
        obtain ⟨b'', hb''0, hb''l, hb''u⟩ := exists_pos hu''ns
        refine ⟨hu''ns, b'', Nat.pos_of_ne_zero hb''0, hb''l, hb''u, ?_, fun h1 h2 => absurd h1 h2⟩
        unfold nlDp
        rw [if_pos rfl, if_neg hb''0, hb''u]
        have h2 := height_le_nlDd hu''ns
        omega
    · /- ### A derived node -/
      have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      obtain ⟨-, ⟨-, hb0'⟩ | ⟨-, hbl, hNM⟩⟩ := hR
      · exact absurd hb0' hb0
      have hu : ns.getD (b - 1) default ∈ ns := getD_mem_of_lt hbpos hbl
      obtain ⟨u, hub⟩ : ∃ u, ns.getD (b - 1) default = u := ⟨_, rfl⟩
      rw [hub] at hu hNM
      have hMo : (tgtMajor out c).member = none := hNM.1
      have hTO := hcls c hc hMo
      have hnlDb : nlDb mpC dR ns b = lfpSel mpC dR.toLfp u.key.cname := by
        unfold nlDb; rw [if_neg hb0, hub]
      have hnlψ : nlψ envC ns ψ b = nodeψ envC ψ u := by unfold nlψ; rw [if_neg hb0, hub]
      have hDc : Dc c = lfpSel mpC dR.toLfp u.key.cname := by
        have := hDeq; rw [hnlDb] at this; simpa [tgtClsD, hMo] using this
      have hmc : tgtClsM mc pp.toBlockShape out c = mc c := by simp [tgtClsM, hMo]
      have hm : mc c < (lfpSel mpC dR.toLfp u.key.cname).k := hDc ▸ hTO.hmm
      have hjn : j < (lfpSel mpC dR.toLfp u.key.cname).nctors (mc c) := by
        have := hHF.1; rwa [hnlDb, hmc] at this
      obtain ⟨cv, nF, ctors, crest, ks, nds, cur, ts', hcvI, hctors, hxmem, hcr, hd, hts', hndl, hcrC,
        hcurC, hndC, hsemU⟩ := dyn_ctorFit H hu ψ hm hjn
      -- the rule's constructor is the node's
      have hcAM : (tgtMajor out c).ctors[j]? = some cA := by
        rw [← tgtRs_ctors (hrs c hc)]; exact hcA
      have hjM : j < (tgtMajor out c).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
      have hcAj : (tgtMajor out c).ctors[j] = cA := by
        rw [List.getElem?_eq_getElem hjM] at hcAM; exact Option.some.inj hcAM
      have hcn : (cv, nF).1.name = cA.1.name := by
        have e1 := ConLeche.Semantics.Env.find?_name hcvI
        have e2 := ConLeche.Semantics.Env.find?_name (hTO.hctor j hjM)
        rw [hDc] at e2
        simp only [ConLeche.ConstantInfo.name] at e1 e2
        rw [hcAj] at e2
        exact e1.trans e2.symm
      have hnfs : targetMajorNfs (fueledOps .verified F) envC pp.toBlockShape
          (cvTasR.map (·.type)) (tgtMajor out c).pfvs (tgtMajor out c).lvls (tgtMajor out c).ds
          (tgtMajor out c).ctors nodesR.ctors = .ok (tgtMajor out c).nfs := by
        have hmem : out.getD c default ∈ out := by
          have hco : c < out.length := by simpa [tgtRs] using hc
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hco, Option.getD_some]
          exact List.getElem_mem hco
        rw [← hRaux]; exact ConLeche.targetRecRun_nfs R _ hmem
      have hcM : (tgtMajor out c).ctors.any (·.1.name == cA.1.name) = true :=
        List.any_eq_true.mpr ⟨cA, List.mem_of_getElem? hcAM, by simp⟩
      have hK := k53_pos (H.hok u hu) (hfrec u hu) hNM hnfs hctors hxmem hcr hd hcn hcM hcallOk C
      rw [htele, hmajsEq] at hK
      generalize hprog : (ConLeche.grpNews u.key.lvls u.key.ds
        ((pp.nestCtx fvsP envI.find? envI.consts).hiAt u.anc.length) u.grp).reverse ++ u.anc = prog
        at hK
      have hhiP : (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length
          = (pp.nestCtx fvsP envI.find? envI.consts).hiAt u.anc.length + u.grp.length := by
        rw [← hprog]
        simp only [List.length_append, List.length_reverse, ConLeche.grpNews, List.length_map,
          ConLeche.NestCtx.hiAt]
        omega
      rw [hprog, ← hhiP] at hd
      rw [← hhiP] at hndC
      -- the node's constructor at an admissible visit
      have hvisit : ∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
          nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par b G ρ' →
          ∀ Y, InTupleSpace ((nlDb mpC dR ns b).w (nlψ envC ns ψ b)) (nlDb mpC dR ns b).N
              ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
                (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y →
          (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
          ∃ σN, AdmVal mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs
              (fun i => if i < u.anc.length then holeOwner ns par b i else b)
              (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
                (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y) prog σN ∧
            fs.length = nF ∧
            ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
              ∃ nda, denoteMeta mpC.base2.acval envC ψ
                  ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + i) nd = some nda ∧
                fs.getD i pt ∈ˢ interp V (consList (fs.take i) σN) nda ∧
                AnnotValid V (consList (fs.take i) σN) nda := by
        intro G ρ' hA Y hY hH
        have hA' := hA
        unfold nodeAdm at hA'
        rw [if_neg hb0, hub] at hA'
        obtain ⟨σ, hσ, rfl⟩ := hA'
        have hidxEq := (dyn_hAdm H ψ ρ xs hparams par b (by omega) G _ hA).2
        rw [hnlDb, hnlψ, hmc] at hH
        rw [hnlDb, hnlψ] at hidxEq
        have hY' : InTupleSpace ((lfpSel mpC dR.toLfp u.key.cname).w (nodeψ envC ψ u))
            (lfpSel mpC dR.toLfp u.key.cname).N ((lfpSel mpC dR.toLfp u.key.cname).idx (nodeψ envC ψ u)
              (keyFrame (nodeDsaI mk (pp.nestCtx fvsP envI.find? envI.consts) ψ u)
                ((pp.nestCtx fvsP envI.find? envI.consts).hiAt u.anc.length) σ)) Y := by
          intro m' hm'
          rw [hidxEq m' hm']
          have := hY m' (by rw [hnlDb]; exact hm')
          rwa [hnlDb, hnlψ] at this
        obtain ⟨hsatN, hfl, hmem⟩ := hsemU σ hσ.sat Y hY' t fs hH
        refine ⟨_, admVal_kid H hbpos hbl hub hσ hsatN (fun i => rfl)
          (u' := .node [] prog default [] []) hprog.symm, hfl, fun i nd hnd => ?_⟩
        obtain ⟨nda, hnda, hmemI, hval⟩ := hmem i nd hnd
        rw [← hhiP] at hnda
        exact ⟨nda, H.htr ψ _ nd hnda, hmemI, hval⟩
      have hread : NodeHolesRead envC (pp.nestCtx fvsP envI.find? envI.consts) prog := by
        rw [← hprog]; exact nodeHolesRead_grp H hu (hF.read u hu)
      refine ⟨prog, fun i => if i < u.anc.length then holeOwner ns par b i else b, nF, crest, ks, nds,
        cur, ts', hd, hcrC, hcurC, hndC, hndl, hK, hread, hvisit, Or.inr ⟨u, hbpos, hub, hprog, rfl⟩,
        fun u'' hu'' hocc => ?_⟩
      have hkid : u'' ∈ u.kids := hts' u'' hu''
      have hu''ns : u'' ∈ ns := H.hkids u hu u'' hkid
      obtain ⟨b'', hb''0, hb''l, hb''u, hparb''⟩ := hPP.2 b hbpos hbl u'' (by rw [hub]; exact hkid)
      -- the kid is deeper than its parent
      have hprogNE : prog ≠ [] := by
        rw [← hprog]
        obtain ⟨hne, -⟩ := posD_frame_inv (H.hok u hu).1
        intro h0
        have := congrArg List.length h0
        simp [ConLeche.grpNews] at this
        exact hne this.1
      have hbb : b < b'' := by
        obtain ⟨-, hlt', hk'⟩ := hPP.1 b'' hb''0 hb''l (by rw [hb''u, hocc]; exact hprogNE)
        rw [hparb''] at hlt'; exact hlt'
      refine ⟨hu''ns, b'', hb''0, hb''l, hb''u, ?_, fun _ _ => funext (holeOwner_kid hparb'' hbb hub)⟩
      unfold nlDp
      rw [if_neg hb0, if_neg (by omega), hub, hb''u]
      have h1 := PosTree.height_kid hkid
      have h2 := height_le_nlDd hu
      omega
  -- the true visit: the fields' count, and the call's telescope fits
  obtain ⟨σT, hAT, hflT, hmemT⟩ := hvisit (fun _ _ _ _ => True) _
    (dyn_top H ψ ρ xs hparams hxs hPP b (by omega) _ (fun _ _ _ _ _ _ _ _ _ => trivial)) _
    (lfpTuple_mem _ _ _ _) hHF
  have hlenF : Q.fvsF.length = nds.length := by rw [hQF, hndl, ← hflT, hfsl]
  have hiN : ih.field < nds.length := by rw [← hlenF, hQF]; exact hfld
  obtain ⟨e, k, nd, tsi, hnd, hfd, heC, htsi⟩ := tele_field hd hcrC (i := ih.field)
    (by rw [← hndl]; exact hiN)
  -- K.53′, as one erasure equation over the leaf's levels and parameters
  obtain ⟨f, hf, hK53⟩ := hK
  obtain ⟨I0, us0, us', Pw, hmajHd, hErase, hmentW, hcmW⟩ := k53_want hK53
  obtain ⟨rcE, uE, -, ⟨EE⟩⟩ := targetEntryAt R (hrs _ hcal)
  have hcmW' : ClassMatches F envC pp.toBlockShape (cvTasR.map (·.type)) (tgtMajor out ih.callee)
      us' Pw := hcmW
  obtain ⟨hlvW, hPwM⟩ := ConLeche.targetClassMatch_true hcmW
  obtain ⟨hPwLen, hPwAll⟩ := ConLeche.targetParamsDefEq_true hPwM
  have hPwB : ∀ x ∈ Pw, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨a, ha⟩ : ∃ a, (tgtMajor out ih.callee).ds[q]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp hq).1; omega)⟩
    have h0 := (hPwAll q a x ha hq).2.1
    exact ConLeche.Expr.looseBVarsBounded_iff.mpr
      (Nat.le_of_eq (by rw [← ConLeche.Expr.bvarB_eq, h0]))
  have hPlC : P.length = (tgtMajor out ih.callee).nPc := by
    rcases hshape with ⟨hm', ms, -, -, -, hP⟩ | ⟨-, -, -, hPM⟩
    · rw [hP, List.length_take, hQP, Nat.min_eq_left (show pp.nP ≤ rc.rP from hnPr),
        tyEntry_nPc_member EE hm']
    · rw [Expr.ErasedEqL.length_eq hPM, tyEntry_dsLen EE]
  -- the callee's major: its head, and its index arguments opened
  have hmajApp : C.majDom = Expr.mkAppN (.const I0 us0) C.majDom.getAppArgs := by
    rw [← hmajHd, ConLeche.Expr.mkAppN_getApp]
  have hO := hmajO'
  rw [hmajApp, instantiateList_mkAppN] at hO
  have hfnO := congrArg Expr.getAppFn hO
  have hasO := congrArg Expr.getAppArgs hO
  rw [ConLeche.Expr.getAppFn_mkAppN, ConLeche.Expr.getAppFn_mkAppN] at hfnO
  rw [ConLeche.Expr.getAppArgs_mkAppN, ConLeche.Expr.getAppArgs_mkAppN] at hasO
  simp only [Expr.getAppFn, Expr.instantiateList, Expr.getAppArgs, List.nil_append,
    Expr.const.injEq] at hfnO hasO
  obtain ⟨hI0, hus0⟩ := hfnO
  subst I0 us0
  have hidxO : (C.majDom.getAppArgs.drop (tgtMajor out ih.callee).nPc).map
      (·.instantiateList (locOpen (rc.rP + Q.fvsF.length) tele.length) 0)
      = ih.idx.map (·.instantiateList (locOpen (rc.rP + cA.2) tele.length) 0) := by
    rw [List.map_drop, hasO, ← hPlC, List.drop_left]
  have hKX : ((ConLeche.targetPiDomsWith Q.fvsF ((ConLeche.closeTelescope nds
      ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length) cur).replaceFVars
        (ConLeche.nestHoleConst (pp.nestCtx fvsP envI.find? envI.consts) prog))).getD
          [])[ih.field]?.map Expr.eraseFVarTys
      = some (Expr.mkPisOf tele (Expr.mkAppN (.const I us')
          (Pw ++ C.majDom.getAppArgs.drop (tgtMajor out ih.callee).nPc))).eraseFVarTys := by
    rw [hf, Option.map_some, hErase]
  have hmajX : (Expr.mkAppN (.const I us')
      (Pw ++ C.majDom.getAppArgs.drop (tgtMajor out ih.callee).nPc)).instantiateList
        (locOpen (rc.rP + Q.fvsF.length) tele.length) 0
      = Expr.mkAppN (.const I us') (Pw ++ ih.idx.map (·.instantiateList
        (locOpen (rc.rP + cA.2) tele.length) 0)) := by
    rw [instantiateList_mkAppN, List.map_append, hidxO,
      show Pw.map (·.instantiateList (locOpen (rc.rP + Q.fvsF.length) tele.length) 0) = Pw from
        (List.map_congr_left fun x hx => ConLeche.Expr.instantiateList_eq_self (hPwB x hx)).trans
          (List.map_id' _),
      ConLeche.Expr.instantiateList_eq_self (show (Expr.const I us').looseBVarsBounded 0 = true
        from rfl)]
  have hmentX : (Expr.mkAppN (.const I us') Pw).nestOcc
      (pp.nestCtx fvsP envI.find? envI.consts).names 0 0 = true := hmentW
  obtain ⟨teleW, leafC, w, hndEq, htl, htel, hteleHF, hopen, hwF, hargsLen, hargs, hcase⟩ :=
    callWalkSyn hwb hndC hcurC hfvF' hlenF hiN hnd hfd heC hKX (by rw [hQF] at hmajX ⊢; exact hmajX)
      hmentX
  have hiF : ih.field < Q.fvsF.length := by rw [hQF]; exact hfld
  have hbsF : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mpC.base2.acval envC ψ (rc.rP + Q.fvsF.length) [] (tele.map (·.1))).getD []) bs := by
    rw [hQF]; exact hbs
  have hbsl : bs.length = tele.length := by
    obtain ⟨hparT, htailT⟩ := parTail_of_agree mpC _ ψ ρ xs hxsC hAT.agree
    obtain ⟨ndaT, hndaT, hfT, hvalT⟩ := hmemT ih.field nd hnd
    rw [hndEq] at hndaT
    exact (fieldCall_core mpC.base2 ψ htl htel hteleHF hopen hwF hargs hnPr hfvF' hfvWF hread hiF
      hndaT hxl hflF hparT htailT hfT hvalT hbsF).1
  obtain ⟨rfl, rfl, rfl⟩ := tagged_inj (hv hbsl)
  -- the rule's index readings are the opened index arguments', read
  rw [show (ih.idx.map fun x => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + bs.length)
          (x.instantiateList (locOpen (rc.rP + cA.2) bs.length) 0)).getD default))
      = (ih.idx.map (·.instantiateList (locOpen (rc.rP + cA.2) tele.length) 0)).map
        (fun xR => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval envC ψ (rc.rP + Q.fvsF.length + bs.length) xR).getD
            default)) by rw [List.map_map, hQF, hbsl]; rfl]
  generalize hidxR : ih.idx.map (·.instantiateList (locOpen (rc.rP + cA.2) tele.length) 0) = idxR
    at hmajO' hargs hargsLen ⊢
  -- the call, at an admissible visit
  have hcallV : ∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
      nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par b G ρ' →
      ∀ Y, InTupleSpace ((nlDb mpC dR ns b).w (nlψ envC ns ψ b)) (nlDb mpC dR ns b).N
          ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
            (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y →
      (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
      ∃ σN, AdmVal mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs own
          (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
            (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y) prog σN ∧
        (∀ v, v < (pp.nestCtx fvsP envI.find? envI.consts).nP →
          σN ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length - 1 - v) = xs.getD v pt) ∧
        ∃ (ha : AnnotTerm) (argsA : List AnnotTerm),
          denoteMeta mpC.base2.acval envC ψ
            ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + ih.field + bs.length)
            w.getAppFn = some ha ∧
          DenoteMetaSpine mpC.base2.acval envC ψ
            ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + ih.field + bs.length)
            w.getAppArgs argsA ∧
          bs.foldl app (fs.getD ih.field pt) ∈ˢ
            (argsA.map (interp V (consList (fs.take ih.field ++ bs) σN))).foldl app
              (interp V (consList (fs.take ih.field ++ bs) σN) ha) ∧
          ∀ (l : Nat) (xa : AnnotTerm), argsA[Pw.length + l]? = some xa →
            (∀ xW, w.getAppArgs[Pw.length + l]? = some xW →
              xW.nestOcc (pp.nestCtx fvsP envI.find? envI.consts).names
                (pp.nestCtx fvsP envI.find? envI.consts).nP
                ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length) = false) →
            (idxR.map fun xR => interp V (consList bs (consList (xs ++ fs) ρ))
              ((denoteMeta mpC.base2.acval envC ψ (rc.rP + Q.fvsF.length + bs.length) xR).getD
                default))[l]? = some (interp V (consList (fs.take ih.field ++ bs) σN) xa) := by
    intro G ρ' hA Y hY hH
    obtain ⟨σN, hAdmN, -, hmemN⟩ := hvisit G ρ' hA Y hY hH
    obtain ⟨hparN, htailN⟩ := parTail_of_agree mpC _ ψ ρ xs hxsC hAdmN.agree
    obtain ⟨nda, hnda, hfN, hvalN⟩ := hmemN ih.field nd hnd
    rw [hndEq] at hnda
    obtain ⟨-, ha, argsA, hha, hspA, hyA, hidxA⟩ := fieldCall_core mpC.base2 ψ htl htel hteleHF
      hopen hwF hargs hnPr hfvF' hfvWF hread hiF hnda hxl hflF hparN htailN hfN hvalN hbsF
    rw [← consList_append (fs.take ih.field) bs σN] at hyA hidxA
    refine ⟨σN, hAdmN, hparN, ha, argsA, hha, hspA, hyA, fun l xa hxa hhf => ?_⟩
    have hl : Pw.length + l < argsA.length := (List.getElem?_eq_some_iff.mp hxa).1
    have hlA : argsA.length = w.getAppArgs.length := hspA.length.symm
    obtain ⟨xR, hxR⟩ : ∃ xR, idxR[l]? = some xR :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlA, hargsLen] at hl; omega)⟩
    obtain ⟨xW, hxW⟩ : ∃ xW, w.getAppArgs[Pw.length + l]? = some xW :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [List.getElem?_map, hxR, Option.map_some, hidxA l xR xW xa hxR hxW hxa (hhf xW hxW)]
  rcases hcase with ⟨tm, tyv, htm, hfn, hI, hus, hal, hpar0, hhf⟩ |
    ⟨v, tyv, hk, hv0, hvl, hfn, hvk, hI, hus, hdsl, hdst, hhf, har⟩ |
    ⟨u'', nPc, L, hu''m, hocc, hfn, hnc, hnPcL, hkey, hhf⟩
  · -- a member hole: the target lands at node `0`
    have hPlen : Pw.length = pp.nP ∧ (tgtMajor out ih.callee).member.isSome = true ∧
        pp.toBlockShape.recTgtAt ih.callee = tm := by
      rcases hshape with ⟨hmem', ms, hms, hIms, -, hP⟩ | ⟨hMo', hIM, -, -⟩
      · refine ⟨?_, hmem', ?_⟩
        · rw [← hPwLen, tyEntry_dsLen EE, tyEntry_nPc_member EE hmem']
        · have htl' : tm < pp.toBlockShape.memberNames.length := htm
          have e1 : pp.toBlockShape.memberNames[pp.toBlockShape.recTgtAt ih.callee]? = some I := by
            simp only [ConLeche.BlockShape.memberNames, List.getElem?_map, hms, Option.map_some,
              hIms]
          have e2 : pp.toBlockShape.memberNames[tm]? = some I := by
            rw [hI, List.getElem?_eq_getElem htl']
            show some _ = some (pp.toBlockShape.memberNames.getD tm .anonymous)
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl', Option.getD_some]
          have hl1 := (List.getElem?_eq_some_iff.mp e1).1
          exact (List.getElem_inj hndM).mp
            ((List.getElem?_eq_some_iff.mp e1).2.trans (List.getElem?_eq_some_iff.mp e2).2.symm)
      · exfalso
        obtain ⟨rcC, uC, -, ⟨EC⟩⟩ := targetEntryAt R (hrs _ hcal)
        obtain ⟨-, -, hnone, -⟩ := EC.outside_of hMo'
        rw [← hIM, hI] at hnone
        have htl' : tm < pp.toBlockShape.memberNames.length := htm
        have hmemN : (pp.nestCtx fvsP envI.find? envI.consts).names.getD tm .anonymous
            ∈ pp.toBlockShape.memberNames := by
          show pp.toBlockShape.memberNames.getD tm .anonymous ∈ _
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl', Option.getD_some]
          exact List.getElem_mem htl'
        rw [List.findIdx?_eq_none_iff] at hnone
        exact absurd (hnone _ hmemN) (by simp)
    obtain ⟨hPl, hmemC, hrt⟩ := hPlen
    have hkc : (pp.nestCtx fvsP envI.find? envI.consts).names.length = dR.k := by
      rw [H.hnames]; exact lfp_namesLen mpC H.hd0
    have htk : tm < dR.k := by rw [← hkc]; exact htm
    have hnIdxs : dR.nIdxs = pp.toBlockShape.nIdxs := by
      obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; rfl
    have hids : (dR.toLfp.ids tm ψ).length
        = (pp.nestCtx fvsP envI.find? envI.consts).nIdxs.getD tm 0 := by
      have := blockMembers_IdsM_length hmr htk ψ
      rw [BlockData.nIdxAt, hnIdxs] at this
      exact this
    have hisl : idxR.length = (pp.nestCtx fvsP envI.find? envI.consts).nIdxs.getD tm 0 := by
      have e1 := hargsLen; rw [hal, hPl] at e1
      have e2 : (pp.nestCtx fvsP envI.find? envI.consts).nP = pp.nP := rfl
      omega
    have hpre : ∀ q, q < (pp.nestCtx fvsP envI.find? envI.consts).nP →
        ∃ ty, w.getAppArgs[q]? = some (.fvar q ty) := by
      intro q hq
      have hqf : q < fvsP.length := by
        rw [ConLeche.Verify.openPisAtFvars_length _ hop0]; exact hq
      obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ hop0 q _
        (List.getElem?_eq_getElem hqf)
      refine ⟨ty, ?_⟩
      have := congrArg (·[q]?) hpar0
      simp only [List.getElem?_take, if_pos hq] at this
      rw [this]
      show fvsP[q]? = _
      rw [List.getElem?_eq_getElem hqf, hty, Nat.zero_add]
    have hlt : ih.field < fs.length := by rw [hfsl]; exact hfld
    refine ⟨0, ⟨tgtClsG_of_mem ht', Or.inl ⟨hmemC, rfl⟩⟩, fun G ρ' hA Y hY hH => ?_⟩
    obtain ⟨σN, hAdmN, hparN, ha, argsA, hha, hspA, hyA, hidxA⟩ := hcallV G ρ' hA Y hY hH
    rw [hfn] at hha
    have hLl : (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + ih.field + bs.length
        = (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length
          + (fs.take ih.field ++ bs).length := by
      rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega
    have htmh : (pp.nestCtx fvsP envI.find? envI.consts).nP + tm
        < (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length := by
      simp only [ConLeche.NestCtx.hiAt]; omega
    rw [headRead_fvar hha htmh hLl σN] at hyA
    have hnD : (pp.nestCtx fvsP envI.find? envI.consts).nP
        ≤ (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length := by
      simp only [ConLeche.NestCtx.hiAt]; omega
    rw [argsA_split_fvars mpC.base2 ψ hspA (by rw [hal]; omega) hpre hnD hLl σN
      (by rw [List.length_map, hal, hisl]; omega)
      (fun l xa hxa => hidxA l xa (by rwa [hPl]) (fun xW hxW => hhf xW (List.mem_of_getElem? hxW)))]
      at hyA
    have hrange : (List.range (pp.nestCtx fvsP envI.find? envI.consts).nP).map
        (fun q => σN ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length - 1 - q))
        = xs.take (pp.nestCtx fvsP envI.find? envI.consts).nP := by
      apply List.ext_getElem?
      intro q
      rw [List.getElem?_map, List.getElem?_take]
      by_cases hq : q < (pp.nestCtx fvsP envI.find? envI.consts).nP
      · rw [List.getElem?_range hq, if_pos hq, Option.map_some, hparN q hq,
          List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega), Option.getD_some]
      · rw [List.getElem?_eq_none (by simp; omega), if_neg hq]; rfl
    rw [hrange] at hyA
    obtain ⟨-, hG⟩ := admVal_memberLand H hparams hxs hAdmN htm
      (by rw [List.length_map]; exact hisl) hids hyA
    have hM1 : tgtClsM mc pp.toBlockShape out ih.callee = tm := by
      simp [tgtClsM, hmemC, hrt]
    have hT1 : tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ ih.callee
        = tupW (dR.toLfp.u tm ψ) := by
      funext is; simp [tgtClsTup, tgtClsU, tgtClsD, tgtClsM, tgtClsψ, hmemC, hrt]
    rcases hG with hG | ⟨hb', -, -, hyY⟩
    · refine Or.inr (Or.inl ?_)
      rw [hM1, hT1]; exact hG
    · refine Or.inl ⟨hb', ?_⟩
      rw [hM1, hT1]; exact hyY
  · -- a frame hole (none at node `0`): the target lands at the hole's owner
    rcases hstk with rfl | ⟨u, hbpos, hub, hprog, rfl⟩
    · exact absurd hvl (by simp only [List.length_nil]; omega)
    have hlt : ih.field < fs.length := by rw [hfsl]; exact hfld
    have hctx0 : (pp.nestCtx fvsP envI.find? envI.consts).hiAt 0 ≤
        (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length := by
      simp only [ConLeche.NestCtx.hiAt]; omega
    generalize hi : v - (pp.nestCtx fvsP envI.find? envI.consts).hiAt 0 = i at hvk
    have hv' : v = (pp.nestCtx fvsP envI.find? envI.consts).hiAt 0 + i := by omega
    -- the owner, off the true visit
    obtain ⟨ho0, hol, hkm, -⟩ := hAT.frame i hk hvk
    generalize hog : (if i < u.anc.length then holeOwner ns par b i else b) = o
      at ho0 hol hkm
    have hoN : ns.getD (o - 1) default ∈ ns := getD_mem_of_lt ho0 hol
    -- the owner's frames: a suffix of the stack
    have hsuf : ∃ X, prog = X ++ (ns.getD (o - 1) default).anc := by
      by_cases hin : i < u.anc.length
      · rw [if_pos hin] at hog
        have hi' : (ns.getD (b - 1) default).anc.reverse[i]? = some hk := by
          rw [hub]
          rw [← hprog, List.reverse_append, List.reverse_reverse,
            List.getElem?_append_left (by simpa using hin)] at hvk
          exact hvk
        obtain ⟨-, -, -, -, X, hX⟩ := dyn_holeOwner H hPP (b + 1) b (by omega) hbpos hbN i hk hi'
        rw [show holeOwnerF ns par (b + 1) b i = o from hog, hub] at hX
        exact ⟨(ConLeche.grpNews u.key.lvls u.key.ds
          ((pp.nestCtx fvsP envI.find? envI.consts).hiAt u.anc.length) u.grp).reverse ++ X ++
          (ConLeche.grpNews (ns.getD (o - 1) default).key.lvls (ns.getD (o - 1) default).key.ds
            ((pp.nestCtx fvsP envI.find? envI.consts).hiAt (ns.getD (o - 1) default).anc.length)
            (ns.getD (o - 1) default).grp).reverse,
          by rw [← hprog, hX]; simp only [List.append_assoc]⟩
      · rw [if_neg hin] at hog
        subst hog
        rw [hub]
        exact ⟨_, hprog.symm⟩
    obtain ⟨X, hX⟩ := hsuf
    -- the hole is a group member of its owner
    simp only [ConLeche.grpNews, List.mem_map] at hkm
    obtain ⟨p, hp, rfl⟩ := hkm
    simp only at hI hus hdst hdsl hhf har
    have hIo : I ∈ (ns.getD (o - 1) default).grp.map (·.1) := by
      rw [hI]; exact List.mem_map_of_mem hp
    obtain ⟨hMo', hIM⟩ := hcalOut hoN hIo
    have hPl : Pw.length = (ns.getD (o - 1) default).key.ds.length := by
      rw [← hPwLen]
      exact houtLen hoN hMo' (by rw [← hIM]; exact hIo)
    have hRo : nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find? envI.consts) dR pp.toBlockShape
        out ns ψ ρ xs envC F (cvTasR.map (·.type)) ih.callee o := by
      refine ⟨tgtClsG_of_mem ht', Or.inr ⟨ho0, hol, ?_⟩⟩
      refine nodeMajor_of_call (H.hok _ hoN) hMo' (by rw [← hIM]; exact hIo)
        hus hcmW' (args := w.getAppArgs) hX (Nat.le_add_right _ ih.field) hPl
        hdst (fun q xM xW h1 h2 => hargs q xM xW ?_ h2)
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]; exact h1
    obtain ⟨hMc, hTc⟩ := htupOut hRo hMo'
    refine ⟨o, hRo, fun G ρ' hA Y hY hH => ?_⟩
    obtain ⟨σN, hAdmN, -, ha, argsA, hha, hspA, hyA, hidxA⟩ := hcallV G ρ' hA Y hY hH
    rw [hfn] at hha
    have hLl : (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + ih.field + bs.length
        = (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length
          + (fs.take ih.field ++ bs).length := by
      rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega
    rw [headRead_fvar hha hvl hLl σN, hv'] at hyA
    -- the hole's parameters, read
    have hle : (pp.nestCtx fvsP envI.find? envI.consts).hiAt (ns.getD (o - 1) default).anc.length
        ≤ (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length := by
      rw [hX]; simp only [ConLeche.NestCtx.hiAt, List.length_append]; omega
    have hdsW := posNodeOk_dsAnc (H.hok _ hoN)
    have hdsaP := DenoteMetaSpine.lift (m := mk.base2) (φ := ψ) hle (fun x hx => (hdsW x hx).1)
      (dyn_dsaI H hoN ψ)
    have hdsaC := DenoteMetaSpine.transport (fun e _ he => H.htr ψ _ e he) hdsaP
    rw [argsA_split mpC.base2 ψ hspA (n := (ns.getD (o - 1) default).key.ds.length) hdsl
        (by rw [hdst]; exact fun x hx => (hdsW x hx).1.mono hle) hLl σN
        (by rw [List.length_map, hargsLen, hPl]; omega)
        (fun l xa hxa => hidxA l xa (by rwa [hPl])
          (fun xW hxW => hhf xW (by
            rw [← hPl]
            exact List.mem_iff_getElem?.mpr ⟨l, by rw [List.getElem?_drop]; exact hxW⟩))),
      hdst] at hyA
    have hmapE : ((ns.getD (o - 1) default).key.ds.map fun x => interp V σN
        ((denoteMeta mpC.base2.acval envC ψ
          ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length) x).getD default))
        = ((nodeDsaI mk (pp.nestCtx fvsP envI.find? envI.consts) ψ (ns.getD (o - 1) default)).map
          (AnnotTerm.liftN ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length
            - (pp.nestCtx fvsP envI.find? envI.consts).hiAt
              (ns.getD (o - 1) default).anc.length) · 0)).map (interp V σN) := by
      rw [← DenoteMetaSpine.getD_eq hdsaC, List.map_map]; rfl
    rw [hmapE] at hyA
    obtain ⟨-, hG⟩ := admVal_frameLand H hparams hxs hAdmN hvk hdsaP
      (by rw [List.length_map, ← hPl, ← har, hargsLen]; omega) hyA
    simp only at hG
    rw [← hI, hIM, hog] at hG
    rcases hG with hG | ⟨hob, -, -, hyY⟩
    · refine Or.inr (Or.inl ?_)
      rw [hMc, hTc]; exact hG
    · refine Or.inl ⟨hob, ?_⟩
      rw [hMc, hTc]; exact hyY
  · -- a container instance: the target lands at a root's or a kid's node
    have hlt : ih.field < fs.length := by rw [hfsl]; exact hfld
    obtain ⟨hu''ns, b'', hb''0, hb''l, hb''u, hdp, hown⟩ := hkidN u'' (htsi u'' hu''m) hocc
    have hok'' := H.hok u'' hu''ns
    have hcn'' : u''.key.cname = I := by rw [hkey]
    have hIo : I ∈ u''.grp.map (·.1) := hcn'' ▸ hok''.2.1
    obtain ⟨hMo', hIM⟩ := hcalOut hu''ns hIo
    have hdsK : u''.key.ds = w.getAppArgs.take nPc := by rw [hkey]
    have hdsl : u''.key.ds.length = nPc := by rw [hdsK, List.length_take]; omega
    have hPl : Pw.length = u''.key.ds.length := by
      rw [← hPwLen]
      exact houtLen hu''ns hMo' (by rw [← hIM]; exact hIo)
    have hanc'' : u''.anc = prog ∨ u''.anc = [] := by
      rcases hok''.2.2.2.2.2 with ⟨h', -⟩ | ⟨h', -⟩
      · exact Or.inl (h'.trans hocc)
      · exact Or.inr h'
    obtain ⟨X'', hX''⟩ : ∃ X, prog = X ++ u''.anc := by
      rcases hanc'' with h' | h'
      · exact ⟨[], by rw [h', List.nil_append]⟩
      · exact ⟨prog, by rw [h', List.append_nil]⟩
    have hRb : nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find? envI.consts) dR pp.toBlockShape
        out ns ψ ρ xs envC F (cvTasR.map (·.type)) ih.callee b'' := by
      refine ⟨tgtClsG_of_mem ht', Or.inr ⟨hb''0, hb''l, ?_⟩⟩
      rw [hb''u]
      refine nodeMajor_of_call hok'' hMo' (by rw [← hIM]; exact hIo)
        (by rw [hkey]) hcmW' (args := w.getAppArgs) hX'' (Nat.le_add_right _ ih.field) hPl
        (by rw [hdsl, hdsK]) (fun q xM xW h1 h2 => hargs q xM xW ?_ h2)
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]; exact h1
    obtain ⟨hMc, hTc⟩ := htupOut hRb hMo'
    obtain ⟨hDb'', hψb'', -⟩ := nlRel_tie (Dc := Dc) (mc := mc) (cvc := cvc) hcov hF hcls hsel
      hnPc hpd hfrT hcal hRb
    have hTO' := hcls _ hcal hMo'
    have hDcb : nlDb mpC dR ns b'' = Dc ih.callee := by
      rw [← hDb'']; simp [tgtClsD, hMo']
    refine ⟨b'', hRb, fun G ρ' hA Y hY hH => ?_⟩
    obtain ⟨σN, hAdmN, -, ha, argsA, hha, hspA, hyA, hidxA⟩ := hcallV G ρ' hA Y hY hH
    -- the kid's admissible valuation
    obtain ⟨σK, hσK, hσKe⟩ : ∃ σK, AdmVal mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns
        ψ ρ xs (holeOwner ns par b'')
        (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
          (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y) u''.anc σK ∧
        ((u''.anc = prog ∧ σK = σN) ∨ (u''.anc = [] ∧ σK = fun q => σN (q + prog.length))) := by
      by_cases h0 : u''.anc = []
      · exact ⟨_, by rw [h0]; exact hAdmN.drop _, Or.inr ⟨h0, rfl⟩⟩
      · have h' : u''.anc = prog := hanc''.resolve_right h0
        refine ⟨σN, ?_, Or.inl ⟨h', rfl⟩⟩
        rw [h', hown h' h0]
        exact hAdmN
    have hAdm'' : nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par b''
        (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
          (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y)
        (keyFrame (nodeDsaI mk (pp.nestCtx fvsP envI.find? envI.consts) ψ u'')
          ((pp.nestCtx fvsP envI.find? envI.consts).hiAt u''.anc.length) σK) := by
      unfold nodeAdm
      rw [if_neg (by omega), hb''u]
      exact ⟨σK, hσK, rfl⟩
    obtain ⟨hsat'', hidx''⟩ := dyn_hAdm H ψ ρ xs hparams par b'' (by omega) _ _ hAdm''
    refine Or.inr (Or.inr ⟨hdp, by omega, _, hAdm'', ?_⟩)
    have hmN : tgtClsM mc pp.toBlockShape out ih.callee < (nlDb mpC dR ns b'').N := by
      rw [hDcb, show tgtClsM mc pp.toBlockShape out ih.callee = mc ih.callee by simp [tgtClsM, hMo']]
      exact Nat.lt_of_lt_of_le hTO'.hmm (mpC.lfpClause_of_mem hTO'.hD).kN
    rw [lfpSClause_carrier_of hidx'' hmN]
    rw [hDcb, show nlψ envC ns ψ b'' = tgtClsψ cvc out ψ ih.callee from hψb''.symm,
      show tgtClsM mc pp.toBlockShape out ih.callee = mc ih.callee by simp [tgtClsM, hMo'],
      show tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ ih.callee
        = tupW ((Dc ih.callee).u (mc ih.callee) (tgtClsψ cvc out ψ ih.callee)) by
          funext is; simp [tgtClsTup, tgtClsU, tgtClsD, tgtClsM, hMo']]
    rw [hDcb, show nlψ envC ns ψ b'' = tgtClsψ cvc out ψ ih.callee from hψb''.symm] at hsat''
    -- the head: the container's former
    rw [hfn] at hha
    obtain ⟨caps', hfI'⟩ := hTO'.hfind
    obtain ⟨-, rfl⟩ := Rules.denoteMeta_const_arityK hfI' (hIM ▸ hha)
    have hLl : (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + ih.field + bs.length
        = (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length
          + (fs.take ih.field ++ bs).length := by
      rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega
    -- the arguments: the key's parameters, then the call's indices
    have hdsW : ∀ x ∈ u''.key.ds, Expr.WScoped ((pp.nestCtx fvsP envI.find? envI.consts).hiAt
        prog.length) x := fun x hx => by
      have := (hok''.2.2.2.2.1 x hx).1; rwa [hocc] at this
    rw [argsA_split mpC.base2 ψ hspA (n := nPc) hnPcL (by rw [← hdsK]; exact hdsW) hLl σN
        (by rw [List.length_map, hargsLen, hPl, hdsl]; omega)
        (fun l xa hxa => hidxA l xa (by rwa [hPl, hdsl])
          (fun xW hxW => hhf xW (List.mem_iff_getElem?.mpr ⟨l, by
            rw [List.getElem?_drop]; rw [hPl, hdsl] at hxW; exact hxW⟩))),
      ← hdsK] at hyA
    -- the key's parameters, read at the kid's valuation
    have hdsaK := dyn_dsaI H hu''ns ψ
    have hmapK : (u''.key.ds.map fun x => interp V σN ((denoteMeta mpC.base2.acval envC ψ
        ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length) x).getD default))
        = (nodeDsaI mk (pp.nestCtx fvsP envI.find? envI.consts) ψ u'').map (interp V σK) := by
      rcases hσKe with ⟨h', rfl⟩ | ⟨h', rfl⟩
      · rw [h'] at hdsaK
        have hC := DenoteMetaSpine.transport (fun e _ he => H.htr ψ _ e he) hdsaK
        rw [← DenoteMetaSpine.getD_eq hC, List.map_map]; rfl
      · rw [h'] at hdsaK
        have hle0 : (pp.nestCtx fvsP envI.find? envI.consts).hiAt ([] : List NestHole).length
            ≤ (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length := by
          simp only [ConLeche.NestCtx.hiAt, List.length_nil]; omega
        have hL := DenoteMetaSpine.lift (m := mk.base2) (φ := ψ) hle0
          (fun x hx => by
            have := (posNodeOk_dsAnc hok'' x hx).1; rwa [h'] at this) hdsaK
        have hC := DenoteMetaSpine.transport (fun e _ he => H.htr ψ _ e he) hL
        have e0 : (u''.key.ds.map fun x => interp V σN ((denoteMeta mpC.base2.acval envC ψ
            ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length) x).getD default))
            = (u''.key.ds.map fun x => (denoteMeta mpC.base2.acval envC ψ
              ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length) x).getD default).map
                (interp V σN) := by rw [List.map_map]; rfl
        rw [e0, DenoteMetaSpine.getD_eq hC, List.map_map]
        refine List.map_congr_left fun a _ => ?_
        show interp V σN (a.liftN _ 0) = _
        rw [interp_liftN]
        congr 1
        funext q
        simp only [shiftE, Nat.not_lt_zero, if_false, ConLeche.NestCtx.hiAt, List.length_nil]
        congr 1
        omega
    rw [hmapK] at hyA
    -- the container's clause
    obtain ⟨dsa0, -, -, -, hlenP, -⟩ := tgtOutSatW hμ mpC hcov h R (hrs _ hcal) hMo' hTO' ψ
    have hψc : tgtClsψ cvc out ψ ih.callee
        = Level.substFn ψ (cvc ih.callee).levelParams (tgtMajor out ih.callee).lvls := by
      simp [tgtClsψ, hMo']
    have hfI : frameIdx ((Dc ih.callee).params (tgtClsψ cvc out ψ ih.callee)).length
        (keyFrame (nodeDsaI mk (pp.nestCtx fvsP envI.find? envI.consts) ψ u'')
          ((pp.nestCtx fvsP envI.find? envI.consts).hiAt u''.anc.length) σK)
        = (nodeDsaI mk (pp.nestCtx fvsP envI.find? envI.consts) ψ u'').map (interp V σK) := by
      unfold keyFrame
      refine frameIdx_consList ?_ _
      rw [List.length_map, ← DenoteMetaSpine.length_eq hdsaK, hψc, hlenP,
        houtLen hu''ns hMo' (by rw [← hIM]; exact hIo)]
    rw [← hfI] at hyA
    have his : ((idxR.map fun xR => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mpC.base2.acval envC ψ (rc.rP + Q.fvsF.length + bs.length) xR).getD
          default))).length
        = ((Dc ih.callee).ids (mc ih.callee) (tgtClsψ cvc out ψ ih.callee)).length := by
      rw [List.length_map, ← hidxR, List.length_map, hidxOut hMo', hψc,
        tgtOutIdx_len R (hrs _ hcal) hMo' hTO' ψ hlenP]
    have hhead : (mpC.base2.acval (tgtMajor out ih.callee).ind
        (Level.substFn ψ (cvc ih.callee).levelParams us'))
        = mpC.base2.acval ((Dc ih.callee).member (mc ih.callee))
          (tgtClsψ cvc out ψ ih.callee) := by
      rw [hTO'.hmem, hψc, ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlvW ψ)]
    simp only [ConLeche.ConstantInfo.toConstantVal] at hyA
    rw [hhead] at hyA
    exact (former_foldl_mem mpC hTO'.hD hTO'.hmm hsat'' _ his hyA).2

end ConLeche.Model
