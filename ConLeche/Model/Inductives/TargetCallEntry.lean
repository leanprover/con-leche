module

import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Verify.InferLemmas
public import ConLeche.Model.Inductives.TargetNodeRb
public import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Model.Inductives.TargetRuleData
import ConLeche.Verify.Inductives.NestCallRun

public section

/-!
# A call's recorded entry

K.53′ compares the called field with the walk's recorded normal forms of
the rule's constructors that the class matches (`targetMajorNfs`,
per-component defeq).  At a related pair (class `c`, node `b`) the
node's own entry is among them:

* `k53_entry` — at a recorded entry of one of the class's constructors
  that the class matches, the called field of the entry's telescope
  opened at the rule's fields passed K.53′ (`targetK53`);
* `k53_want` — K.53′'s comparison as one erasure equation: the field is
  the call's telescope over the callee's container at the leaf's levels
  and parameters (matching the callee's class) and the callee's index
  arguments;
* `entryDs_readback` — a derived node's recorded parameters are its key's
  read back (`nodeRb`);
* `tele_field` — a derived constructor telescope's field `i`: its
  derivation, closed.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockShape TargetMajor
  NestCtx NestHole NestCtorNf BinderMeta PosD PosTree PosKind PosNodeOk nestHoleConst
  closeTelescope targetPiDomsWith openPisAtFvars)

/-- **K.53′ at a walked constructor** (see the module docstring): the
rule `(c, j)` of a class whose constructor `cA` the node walked (`e`, the
hook accepting it) and whose class matches the node's instantiation was
typed at `e` too; that run's calls are the stored rule's (`agree`), so a
call `ih` of the rule's record `Q` passed K.53′ against `e`'s field. -/
theorem k53_entry {F : Nat} {envC : Env} {q : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : ConLeche.TargetRecRun .verified F (ConLeche.mkFEnv envC) q nested block cvTas ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) {j : Nat} {cA : ConstantVal × Nat}
    (hcA : (tgtRs out)[c].2.2.2[j]? = some cA) {rP : Nat} (hrP : rP = q.rulePrefixAt c)
    {rhs0 rhs : Expr} (hrhs : (tgtRs out)[c].2.1[j]? = some rhs)
    (Q : ConLeche.TargetRuleRun .verified F
      (ConLeche.consBlockRecsBareF q 0 ((tgtRs out).map fun r => (r.1, r.2.2.1))
        (ConLeche.mkFEnv envC)) (ConLeche.mkFEnv envC) q (cvTas.map (·.type)) (tgtFam q out)
      (tgtRs out)[c].1 rP (tgtRs out)[c].1.type (tgtMajor out c) cA rhs0 rhs)
    {e : NestCtorNf}
    (he : ConLeche.HookOk (ConLeche.targetHook (ConLeche.ShadowOps.fueled .verified F)
      (ConLeche.mkFEnv envC)
      (ConLeche.consBlockRecsBareF q 0 (R.tys.map fun t => (t.1, t.2.1.nIdx)) (ConLeche.mkFEnv envC))
      q (cvTas.map (·.type)) (ConLeche.targetFamilyOf q R.tys) q.recs R.tys) e)
    (hn : cA.1.name = e.ctor)
    (hm : ConLeche.targetClassMatch (ConLeche.fueledOps .verified F) envC q (cvTas.map (·.type))
      (tgtMajor out c).pfvs (tgtMajor out c).lvls (tgtMajor out c).ds e.lvls e.ds = .ok true)
    {ih : ConLeche.TargetIh} (hih : ih ∈ Q.ihs.toList)
    (C : ConLeche.TargetCallRun .verified F envC (tgtFam q out) Q.fvsPref Q.fvsF Q.fnorm
      (Q.fnorm.map fun t => t.piBinders.1)
      (ConLeche.targetAbs q.memberNames (q.lps.map .param)
        (ConLeche.targetHoles (cvTas.map (·.type)) (rP + cA.2)))
      (rP + cA.2) (cvTas.map (·.type)).length
      (Level.zeronessOf (ConLeche.structElimLevel q.elim q.large)) ih) :
    ∃ f, ((targetPiDomsWith Q.fvsF e.ty).getD [])[ih.field]? = some f ∧
      ConLeche.targetK53 (ConLeche.fueledOps .verified F) envC q (cvTas.map (·.type))
        ((tgtFam q out).majs.getD ih.callee default)
        ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []) C.majDom f = .ok true := by
  -- the stored entry at `c` and the check's record there
  obtain ⟨hlenO, hallO⟩ := R.rules
  have hlenT := (ConLeche.targetRecTys_run R.htys R.elims).1
  have hco : c < out.length := by simpa [tgtRs] using hc
  have hcr : c < q.recs.length := by
    have := hlenO; rw [hlenT, Nat.min_self] at this; omega
  obtain ⟨rc, hrc⟩ : ∃ rc, q.recs[c]? = some rc := ⟨_, List.getElem?_eq_getElem hcr⟩
  obtain ⟨t, ht⟩ : ∃ t, R.tys[c]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨rhssA, hout, hlenR, RR⟩ := hallO c rc t hrc ht
  have hoc : out[c] = (t.1, t.2.1, rhssA) := by
    rw [List.getElem?_eq_getElem hco] at hout; exact Option.some.inj hout
  have hr : (tgtRs out)[c] = (t.1, rhssA, t.2.1.nIdx, t.2.1.ctors) := by
    simp only [tgtRs, List.getElem_map, hoc]
  have hM : tgtMajor out c = t.2.1 := by
    simp only [tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hco,
      Option.getD_some, hoc]
  have hr1 : (tgtRs out)[c].1 = t.1 := by rw [hr]
  have hcA' : t.2.1.ctors[j]? = some cA := by rw [hr] at hcA; exact hcA
  have hrhs' : rhssA[j]? = some rhs := by rw [hr] at hrhs; exact hrhs
  have hrP' : rc.rP = rP := by
    rw [hrP]; simp [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc]
  -- the rule's right-hand side, and its stored form
  obtain ⟨rhs1, hrhs1⟩ : ∃ rhs1, rc.rhss[j]? = some rhs1 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenR]; exact (List.getElem?_eq_some_iff.mp hcA').1)⟩
  obtain ⟨o0, ety0, ho0, hrun0⟩ := RR.rule j cA rhs1 hcA' hrhs1
  rw [hrhs'] at ho0
  obtain rfl := Option.some.inj ho0
  -- the rule typed at `e`
  rw [hM] at hm
  obtain ⟨o', hrun'⟩ := ConLeche.targetHook_rule he c rc t hrc ht j cA rhs1 hcA' hrhs1 hn hm
  -- both runs at the stored forms of the family
  rw [targetRecRun_fam_eq R, ConLeche.targetRecRun_bare_eq R, hrP', ← hr1, ← hM] at hrun0 hrun'
  obtain ⟨Q0, -⟩ := ConLeche.targetRule_run hrun0
  obtain ⟨Q', hQ'⟩ := ConLeche.targetRule_run hrun'
  obtain rfl := ConLeche.TargetRuleRun.out_eq Q0 Q'
  obtain ⟨e1, e2, e3, e4⟩ := ConLeche.TargetRuleRun.agree Q Q'
  have hcalls := Q'.hcalls
  rw [hQ', ← e1, ← e2, ← e3, ← e4] at hcalls
  exact ConLeche.targetCallOk_k53 (ConLeche.targetCallsOk_each hcalls ih hih) C

/-! ## K.53′'s comparison, as one erasure equation -/

theorem stripPis_eq_mkPisOf : ∀ {n : Nat} {e r : Expr} {bs : List (Expr × BinderMeta)},
    e.stripPis n = some (bs, r) → e = Expr.mkPisOf bs r
  | 0, e, r, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, e, r, bs, h => by
    cases e with
    | forallE ty b m =>
      simp only [Expr.stripPis] at h
      obtain ⟨⟨bs', r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rw [stripPis_eq_mkPisOf h1]; rfl
    | _ => simp [Expr.stripPis] at h

theorem eraseFVarTys_mkAppN : ∀ (as : List Expr) (f : Expr),
    (Expr.mkAppN f as).eraseFVarTys = Expr.mkAppN f.eraseFVarTys (as.map Expr.eraseFVarTys)
  | [], _ => rfl
  | a :: as, f => by
    show (Expr.mkAppN (.app f a) as).eraseFVarTys = _
    rw [eraseFVarTys_mkAppN as]; rfl

theorem eraseFVarTys_mkPisOf : ∀ (bs : List (Expr × BinderMeta)) (b : Expr),
    (Expr.mkPisOf bs b).eraseFVarTys
      = Expr.mkPisOf (bs.map fun x => (x.1.eraseFVarTys, x.2)) b.eraseFVarTys
  | [], _ => rfl
  | (ty, m) :: bs, b => by
    show Expr.eraseFVarTys (.forallE ty (Expr.mkPisOf bs b) m) = _
    rw [List.map_cons, Expr.mkPisOf, ← eraseFVarTys_mkPisOf bs b]; rfl

/-- **K.53′'s comparison, as one erasure equation**: a passing field is,
up to annotations, the call's telescope over the leaf's container — the
callee's major's head — at the leaf's levels and parameters (which
match the callee's class, `targetClassMatch`) and the callee's index
arguments. -/
theorem k53_want {ops : ConLeche.CheckerOps ConLeche.CheckM} {env : Env} {p : BlockShape}
    {formerTys : List Expr} {Mc : TargetMajor} {tele : List (Expr × BinderMeta)}
    {majDom f : Expr} (h : ConLeche.targetK53 ops env p formerTys Mc tele majDom f = .ok true) :
    ∃ (I : Name) (us us' : List Level) (Pw : List Expr),
      majDom.getAppFn = .const I us ∧
      f.eraseFVarTys = (Expr.mkPisOf tele
        (Expr.mkAppN (.const I us') (Pw ++ majDom.getAppArgs.drop Mc.nPc))).eraseFVarTys ∧
      (Expr.mkAppN (.const I us') Pw).nestOcc p.memberNames 0 0 = true ∧
      ConLeche.targetClassMatch ops env p formerTys Mc.pfvs Mc.lvls Mc.ds us' Pw = .ok true := by
  obtain ⟨teleW, leafW, I, us', us, hstrip, htele, hW, hM, -, hidx, hment, hcm⟩ :=
    ConLeche.targetK53_true h
  refine ⟨I, us, us', leafW.getAppArgs.take Mc.nPc, hM, ?_, hment, hcm⟩
  rw [stripPis_eq_mkPisOf hstrip, eraseFVarTys_mkPisOf, eraseFVarTys_mkPisOf, htele]
  congr 1
  have hleaf : leafW = Expr.mkAppN (.const I us') leafW.getAppArgs := by
    rw [← hW, ConLeche.Expr.mkAppN_getApp]
  generalize hA : leafW.getAppArgs = A at hidx hleaf ⊢
  rw [hleaf, eraseFVarTys_mkAppN, eraseFVarTys_mkAppN, List.map_append, ← hidx,
    ← List.map_append, List.take_append_drop]

/-! ## A derived node's recorded parameters -/

theorem nestHoleConst_suffix {ctx : NestCtx} (X anc : List NestHole) {v : Nat}
    (hv : v < ctx.hiAt anc.length) :
    nestHoleConst ctx (X ++ anc) v = nestHoleConst ctx anc v := by
  unfold nestHoleConst
  by_cases h0 : ctx.nP ≤ v ∧ v < ctx.hiAt 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : ctx.hiAt 0 ≤ v
    · have hl : v - ctx.hiAt 0 < anc.reverse.length := by
        simp [ConLeche.NestCtx.hiAt] at hv h1 ⊢; omega
      rw [if_pos ⟨h1, by simp [ConLeche.NestCtx.hiAt] at hv ⊢; omega⟩, if_pos ⟨h1, hv⟩,
        List.reverse_append, List.getElem?_append_left hl]
    · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]

theorem replaceFVars_congr_below {f g : Nat → Option Expr} {d : Nat}
    (hfg : ∀ v, v < d → f v = g v) :
    ∀ (X : Expr), X.fvarsBelow d → X.replaceFVars f = X.replaceFVars g := by
  intro X
  induction X with
  | bvar i => intro _; rfl
  | fvar i ty _ =>
    intro h
    simp only [Expr.fvarsBelow] at h
    simp only [Expr.replaceFVars, hfg i h]
  | sort u => intro _; rfl
  | const n us => intro _; rfl
  | lit l => intro _; rfl
  | app f a ihf iha => intro h; simp only [Expr.replaceFVars, ihf h.1, iha h.2]
  | lam t body m iht ihb => intro h; simp only [Expr.replaceFVars, iht h.1, ihb h.2]
  | forallE t body m iht ihb => intro h; simp only [Expr.replaceFVars, iht h.1, ihb h.2]
  | letE t v body iht ihv ihb =>
    intro h; simp only [Expr.replaceFVars, iht h.1, ihv h.2.1, ihb h.2.2]
  | proj n i e ih => intro h; simp only [Expr.replaceFVars, ih h]

/-- **A derived node's recorded parameters are its key's read back**: the
kernel reads the key back under the constructor's frames (its group's
holes on top of its own frame stack), which is the key's read-back at
its occurrence. -/
theorem entryDs_readback {ops : ConLeche.CheckerOps ConLeche.CheckM} {env : Env} {ctx : NestCtx}
    {u : PosTree} (hok : PosNodeOk ops env ctx u) (X : List NestHole) :
    u.key.ds.map (·.replaceFVars (nestHoleConst ctx (X ++ u.anc)))
      = u.key.ds.map (nodeRb ctx u.occ) := by
  obtain ⟨-, -, -, -, hws, hanc⟩ := hok
  refine List.map_congr_left fun x hx => ?_
  rcases hanc with ⟨hao, -⟩ | ⟨han, hds⟩
  · have hb : x.fvarsBelow (ctx.hiAt u.anc.length) := by
      rw [hao]; exact Expr.WScoped.fvarsBelow (hws x hx).1
    rw [replaceFVars_congr_below (fun v hv => nestHoleConst_suffix X u.anc hv) x hb,
      concrete_eq_nodeRb ctx u.anc hb, hao]
  · have hb : x.fvarsBelow (ctx.hiAt 0) := Expr.WScoped.fvarsBelow (hds x hx).2
    have hb' : x.fvarsBelow (ctx.hiAt u.occ.length) :=
      Expr.WScoped.fvarsBelow (hws x hx).1
    rw [← concrete_eq_nodeRb ctx u.occ hb', han]
    have e1 : x.replaceFVars (nestHoleConst ctx (X ++ [])) = x.replaceFVars (nestHoleConst ctx []) :=
      replaceFVars_congr_below (fun v hv => nestHoleConst_suffix X [] hv) x hb
    have e2 : x.replaceFVars (nestHoleConst ctx u.occ) = x.replaceFVars (nestHoleConst ctx []) := by
      have := replaceFVars_congr_below (fun v hv => nestHoleConst_suffix (ctx := ctx) u.occ [] hv)
        x hb
      rwa [List.append_nil] at this
    rw [e1, e2]

/-! ## A telescope's field -/

/-- **A derived telescope's field `i`**: its derivation at the field's
depth, its type bvar-closed, its trees the telescope's. -/
theorem tele_field {ops : ConLeche.CheckerOps ConLeche.CheckM} {env : Env} {ctx : NestCtx}
    {prog : List NestHole} {base nF : Nat} {crest : Expr} {ks : List PosKind}
    {nds : List (Expr × BinderMeta)} {cur : Expr} {ts : List PosTree}
    (hd : PosD ops env ctx (.tele prog base nF 0 crest ks nds cur) ts)
    (hcb : crest.looseBVarsBounded 0 = true) {i : Nat} (hi : i < nF) :
    ∃ (e : Expr) (k : PosKind) (nd : Expr) (tsi : List PosTree),
      nds[i]?.map (·.1) = some nd ∧ PosD ops env ctx (.field prog (base + i) 0 e k nd) tsi ∧
      e.looseBVarsBounded 0 = true ∧ ∀ t ∈ tsi, t ∈ ts := by
  obtain ⟨-, -, xs, hop, hall⟩ := ConLeche.posD_tele_open hd
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨x, hx⟩ : ∃ x, xs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨k, nd, ts', -, hnd, hfd, hsub⟩ := hall i x hx
  have hcl := (ConLeche.Verify.openPisAtFvars_bounded nF hop hcb).2 x (List.mem_of_getElem? hx)
  exact ⟨_, k, nd, ts', hnd, by simpa using hfd, hcl, hsub⟩

end ConLeche.Model
