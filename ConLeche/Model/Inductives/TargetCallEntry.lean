module

import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Verify.Denote.IndFrame
public import ConLeche.Model.Inductives.TargetNodeRb
public import ConLeche.Verify.Inductives.RecCheckRun

public section

/-!
# A call's recorded entry

K.53′ compares the called field with the walk's recorded normal forms of
the rule's constructor at the class (`targetMajorNfs`).  At a related
pair (class `c`, node `b`) the node's own entry is among them:

* `k53_entry` — at a recorded entry of the constructor at the class's
  levels and parameters (up to annotations), the called field of the
  entry's telescope opened at the rule's fields IS the callee's major
  type under the field's telescope, up to annotations;
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
  NestCtx NestHole NestCtorNf NestNodes BinderMeta PosD PosTree PosKind PosNodeOk nestHoleConst
  closeTelescope targetPiDomsWith targetMajorNfs targetFieldNfs openPisAtFvars)

/-- Erasure-equal lists erase alike. -/
theorem erasedEqL_eraseMap : ∀ {as bs : List Expr}, Expr.ErasedEqL as bs →
    as.map Expr.eraseFVarTys = bs.map Expr.eraseFVarTys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, b :: bs, ⟨h1, h2⟩ => by
    simp only [List.map_cons, ConLeche.Expr.eraseFVarTys_eq_iff.mpr h1, erasedEqL_eraseMap h2]

/-- **K.53′ at a recorded entry** (see the module docstring). -/
theorem k53_entry {μ : CheckMode} {env : Env} {cn : Name} {fam : ConLeche.TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : ConLeche.PropWhen} {M : TargetMajor}
    {ih : ConLeche.TargetIh}
    (hcall : ConLeche.targetCallOk (ConLeche.fueledOps μ F) env cn fam fvsPref fvsF fnorm teles
      absM base k pw (targetFieldNfs M cn fvsF) ih = .ok ())
    (C : ConLeche.TargetCallRun μ F env fam fvsPref fvsF fnorm teles absM base k pw ih)
    {aux : NestNodes} (hnfs : M.nfs = some (targetMajorNfs aux M.lvls M.ds))
    {e : NestCtorNf} (he : e ∈ aux.ctors) (hcn : e.ctor = cn) (hlv : e.lvls = M.lvls)
    (hds : Expr.ErasedEqL e.ds M.ds) :
    ((targetPiDomsWith fvsF e.ty).getD [])[ih.field]?.map Expr.eraseFVarTys
      = some (Expr.mkPisOf (teles.getD ih.field []) C.majDom).eraseFVarTys := by
  have hF : targetFieldNfs M cn fvsF = some (((targetMajorNfs aux M.lvls M.ds).filter
      (·.ctor == cn)).map fun e => (targetPiDomsWith fvsF e.ty).getD []) := by
    unfold targetFieldNfs; rw [hnfs]; rfl
  rw [hF] at hcall
  refine (ConLeche.targetCallOk_k53 hcall C).2 _ (List.mem_map.mpr ⟨e, ?_, rfl⟩)
  refine List.mem_filter.mpr ⟨?_, by simp [hcn]⟩
  refine List.mem_filter.mpr ⟨he, ?_⟩
  simp [hlv, erasedEqL_eraseMap hds]

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
