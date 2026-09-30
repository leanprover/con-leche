module

import ConLeche.Verify.Denote.IndFrame
public import ConLeche.Model.Inductives.TargetNodeRb

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
  read back (`nodeRb`, the kernel's `nestHoleImg`);
* `tele_field` — a derived constructor telescope's field `i`: its
  derivation, closed.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockShape TargetMajor
  NestCtx NestHole NestCtorNf BinderMeta PosD PosTree NestFieldKind PosNodeOk nestHoleImg
  closeTelescope targetPiDomsWith targetMajorNfs openPisAtFvars)

/-! ## K.53′'s comparison, as one erasure equation -/

/-! ## A derived node's recorded parameters -/

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
    u.key.ds.map (·.replaceFVars (nestHoleImg ctx (X ++ u.anc)))
      = u.key.ds.map (nodeRb ctx u.occ) := by
  obtain ⟨-, -, -, -, hws, hanc⟩ := hok
  refine List.map_congr_left fun x hx => ?_
  rcases hanc with ⟨hao, -⟩ | ⟨han, hds⟩
  · have hb : x.fvarsBelow (ctx.hiAt u.anc.length) := by
      rw [hao]; exact Expr.WScoped.fvarsBelow (hws x hx).1
    rw [replaceFVars_congr_below (fun v hv => nestHoleImg_append X u.anc hv) x hb, nodeRb, hao]
  · have hb : x.fvarsBelow (ctx.hiAt 0) := Expr.WScoped.fvarsBelow (hds x hx).2
    have e1 : x.replaceFVars (nestHoleImg ctx (X ++ u.anc))
        = x.replaceFVars (nestHoleImg ctx []) := by
      rw [han, List.append_nil]
      have := replaceFVars_congr_below (fun v hv => nestHoleImg_append (ctx := ctx) X [] hv) x hb
      rwa [List.append_nil] at this
    have e2 : x.replaceFVars (nestHoleImg ctx u.occ) = x.replaceFVars (nestHoleImg ctx []) := by
      have := replaceFVars_congr_below (fun v hv => nestHoleImg_append (ctx := ctx) u.occ [] hv)
        x hb
      rwa [List.append_nil] at this
    rw [e1, nodeRb, e2]

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
