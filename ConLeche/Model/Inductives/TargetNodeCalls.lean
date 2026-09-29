module

import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Semantics.EnvFacts
import ConLeche.Verify.InferLeaves
import ConLeche.Model.IndPointKit
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.TargetCallEntry
public import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Model.Inductives.TargetCallMaj
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
  `0`'s hole frame, `admVal_frame0`), the call's target in the leaf's
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
  NestHole NestCtorNf BinderMeta BlockParts BlockShape TargetMajor fueledOps PosD PosTree
  NestFieldKind PosNodeOk closeTelescope targetPiDomsWith targetMajorNfs
  openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Small kit -/

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

/-! ## The parameters and the tail of a valuation -/

section ParTail

variable {μ : CheckMode} {envC : Env} (mpC : EnvModelM V μ envC) (ctx : NestCtx) (ψ : Name → Nat)
  (ρ : Nat → V) (xs : List V)

/-- The true valuation's parameters are the prefix's. -/
theorem trueVal_param (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) {v : Nat}
    (hv : v < ctx.nP) : trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - v) = xs.getD v pt := by
  unfold trueVal nodeTrueVal
  have hlv : (nodeHv mpC.base2.acval envC ctx ψ prog xs.length).length
      = ctx.names.length + prog.length := by
    simp only [nodeHv, List.length_map, List.length_range, ConLeche.NestCtx.hiAt]; omega
  rw [consList_append]
  have hl2 : ((nodeHv mpC.base2.acval envC ctx ψ prog xs.length).map
      (interp V (consList xs ρ))).length = ctx.names.length + prog.length := by
    rw [List.length_map, hlv]
  have e : ctx.hiAt prog.length - 1 - v
      = (ctx.nP - 1 - v) + ((nodeHv mpC.base2.acval envC ctx ψ prog xs.length).map
        (interp V (consList xs ρ))).length := by
    rw [hl2]; simp only [ConLeche.NestCtx.hiAt]; omega
  rw [e, consList_apply_add, consList_getD_of_lt _ _ _ (by rw [List.length_take]; omega),
    List.length_take, show min ctx.nP xs.length - 1 - (ctx.nP - 1 - v) = v by omega,
    List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hv, ← List.getD_eq_getElem?_getD]

/-- The true valuation's tail is the context's. -/
theorem trueVal_tail (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) (q : Nat) :
    trueVal mpC ctx ψ ρ xs prog (q + ctx.hiAt prog.length) = ρ q := by
  unfold trueVal nodeTrueVal
  have hlv : (xs.take ctx.nP ++ (nodeHv mpC.base2.acval envC ctx ψ prog xs.length).map
      (interp V (consList xs ρ))).length = ctx.hiAt prog.length := by
    simp only [nodeHv, List.length_append, List.length_take, List.length_map, List.length_range,
      ConLeche.NestCtx.hiAt]; omega
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
      ConLeche.nestHoleImg_suffix X anc hv]

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

/-- **The callee's class at a listed node, from the leaf's read-back
prefix** (a frame hole's leaf): the class's parameters `P` are, up to
annotations, the node's key parameters read back at a stack of which the
node's frames are a suffix — its own read-back (`nodeRb` at its
occurrence), below its frames. -/
theorem nodeMajor_of_pre {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {o : PosTree} (hok : PosNodeOk ops env ctx o) {F : Nat} {envC : Env} {p : BlockShape}
    {formerTys : List Expr} {M : TargetMajor} (hMo : M.member = none)
    (hind : M.ind ∈ o.grp.map (·.1)) {us' : List Level} (hlv : us' = o.key.lvls) {P : List Expr}
    (hCM : ClassMatches F envC p formerTys M us' P) {S X : List NestHole} (hS : S = X ++ o.anc)
    (hPl : P.length = o.key.ds.length)
    (hE : ∀ (q : Nat) (xM xP : Expr), P[q]? = some xM →
      (o.key.ds.map (·.replaceFVars (ConLeche.nestHoleImg ctx S)))[q]? = some xP →
      Expr.ErasedEq xM xP) :
    NodeMajor F envC p formerTys ctx M o := by
  refine ⟨hMo, hind, ?_⟩
  have hrb : o.key.ds.map (·.replaceFVars (ConLeche.nestHoleImg ctx S))
      = o.key.ds.map (nodeRb ctx o.occ) := by
    rw [hS]; exact entryDs_readback hok X
  have hE' : Expr.ErasedEqL P (o.key.ds.map (nodeRb ctx o.occ)) := by
    refine erasedEqL_of_getElem (by rw [hPl, List.length_map]) fun q a' b' ha hb' => ?_
    rw [← hrb] at hb'
    exact hE q a' b' ha hb'
  unfold ClassMatches
  rw [← hlv, ← ConLeche.targetClassMatch_congr hE'.toErasedEqs]
  exact hCM

/-! ## THE CALLS -/

end ConLeche.Model
