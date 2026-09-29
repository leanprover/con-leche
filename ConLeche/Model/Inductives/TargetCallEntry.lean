module

import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Verify.InferLemmas
public import ConLeche.Model.Inductives.TargetNodeRb
public import ConLeche.Verify.Inductives.RecCheckRun

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
  NestCtx NestHole NestCtorNf BinderMeta PosD PosTree NestFieldKind PosNodeOk nestHoleConst
  closeTelescope targetPiDomsWith targetMajorNfs targetFieldNfs openPisAtFvars)

/-- **K.53′ at a recorded entry** (see the module docstring): an entry of
one of the class's constructors that the class matches is among its
recorded normal forms (`targetMajorNfs`), so its called field passed the
call's K.53′ comparison (`targetK53`). -/
theorem k53_entry {μ : CheckMode} {env : Env} {p : BlockShape} {formerTys : List Expr} {cn : Name}
    {fam : ConLeche.TargetFamily}
    {fvsPref fvsF : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM mvF : Expr → Expr} {base k dA F : Nat} {pw : ConLeche.PropWhen} {M : TargetMajor}
    {ih : ConLeche.TargetIh}
    (hcall : ConLeche.targetCallOk (ConLeche.fueledOps μ F) env p formerTys cn fam fvsPref fvsF
      teles absM mvF base k dA pw (targetFieldNfs M cn fvsF) ih = .ok ())
    (C : ConLeche.TargetCallRun μ F env fam fvsPref fvsF teles absM mvF base k dA pw ih)
    {tbl : List NestCtorNf}
    (hnfs : targetMajorNfs (ConLeche.fueledOps μ F) env p formerTys M.pfvs M.lvls M.ds M.ctors
      tbl = .ok M.nfs)
    {e : NestCtorNf} (he : e ∈ tbl) (hcn : e.ctor = cn)
    (hcM : M.ctors.any (·.1.name == cn) = true)
    (hCM : ConLeche.targetClassMatch (ConLeche.fueledOps μ F) env p formerTys M.pfvs M.lvls M.ds
      e.lvls e.ds = .ok true) :
    ∃ f, ((targetPiDomsWith fvsF e.ty).getD [])[ih.field]? = some f ∧
      ConLeche.targetK53 (ConLeche.fueledOps μ F) env p formerTys (fam.majs.getD ih.callee default)
        (teles.getD ih.field []) C.majDom f = .ok true := by
  have hmem := ConLeche.targetMajorNfs_mem hnfs e he (by rw [hcn]; exact hcM) hCM
  exact (ConLeche.targetCallOk_k53 hcall C).2 _
    (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨hmem, by simp [hcn]⟩, rfl⟩)

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
    {prog : List NestHole} {base nF : Nat} {crest : Expr} {ks : List NestFieldKind}
    {nds : List (Expr × BinderMeta)} {cur : Expr} {ts : List PosTree}
    (hd : PosD ops env ctx (.tele prog base nF 0 crest ks nds cur) ts)
    (hcb : crest.looseBVarsBounded 0 = true) {i : Nat} (hi : i < nF) :
    ∃ (e : Expr) (k : NestFieldKind) (nd : Expr) (tsi : List PosTree),
      nds[i]?.map (·.1) = some nd ∧ PosD ops env ctx (.field prog (base + i) 0 e k nd) tsi ∧
      e.looseBVarsBounded 0 = true ∧ ∀ t ∈ tsi, t ∈ ts := by
  obtain ⟨-, -, xs, hop, hall⟩ := ConLeche.posD_tele_open hd
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨x, hx⟩ : ∃ x, xs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨k, nd, ts', -, hnd, hfd, hsub⟩ := hall i x hx
  have hcl := (ConLeche.Verify.openPisAtFvars_bounded nF hop hcb).2 x (List.mem_of_getElem? hx)
  exact ⟨_, k, nd, ts', hnd, by simpa using hfd, hcl, hsub⟩

end ConLeche.Model
