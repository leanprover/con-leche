module

public import ConLeche.Model.Inductives.TargetNodeSem
public import ConLeche.Model.Inductives.TargetNodeDyn
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Cached.Erase
import ConLeche.Model.Tiers
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.ContSem

public section

/-!
# The node presentation's admissible frames (lane NESTIND, session 23)

`TgtNodeDyn` (`TargetNodeList.lean`) asks, at every listed node, the
kit's admissible frames `Adm` with `hAdm`, `top`, `trans` and the calls.
A derived node is visited at its key's parameters read at an ADMISSIBLE
valuation of the frames it is derived under (`AdmVal`): the block's
parameters the prefix's, every hole's value inhabiting its type, and every
hole's value — read at full arity (at its own parameters, for a frame's
hole) — either an element the visit's hypotheses `G` hold of (at the
hole's owner node: node `0` for a member hole at the block's parameters,
the frame's owner for a frame hole) or, off the owner's index set, below
the TRUE valuation's constant.  The true valuation (the holes' constants)
is admissible once the shallower nodes' true elements satisfy `G` (`top`),
and an admissible valuation is related to the true one by a hole relation
(`HoleRel`) once `G`'s elements are true (`trans`, through `FrameMono`).

The key's parameters satisfy the container's parameter telescope at every
valuation of the stack context: the kernel TYPES the key at its node's
depth (K.52, `PosD.frame`'s `hkty`), `infer_sound` grades it there, and a
graded instance reads its parameters in the telescope (`keyParamsFit`) —
`nodeKeyFit`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockParts BlockShape fueledOps PosTree PosNodeOk PosD)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-! ## K.52 at a node: the key's parameters fit -/

/-- **K.52, inverted**: a derived frame's key instance is typed at the
frame's depth. -/
theorem posD_frame_kty {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {ts : List PosTree} (h : PosD ops env ctx (.frame prog us ds grp) ts) :
    ∃ ty, ops.inferType env (ctx.hiAt prog.length)
      (Expr.mkAppN (.const (grp.headD default).1 us) ds) = .ok ty := by
  cases h with
  | frame _ _ _ _ _ _ _ _ hkty _ => exact hkty

omit [SetTheory V] in
theorem wScoped_mkAppN_of {d : Nat} :
    ∀ (as : List Expr) {f : Expr}, Expr.WScoped d f → (∀ a ∈ as, Expr.WScoped d a) →
      Expr.WScoped d (Expr.mkAppN f as)
  | [], _, hf, _ => hf
  | a :: as, f, hf, ha => by
    refine wScoped_mkAppN_of as (f := .app f a) ?_ fun x hx => ha x (List.mem_cons_of_mem _ hx)
    simp only [Expr.WScoped]
    exact ⟨hf, ha a List.mem_cons_self⟩

/-- A constant applied to arguments in a context is in it. -/
theorem CtxOkP.mkAppN_const {env : Env} {m : EnvModel V env} {φ : Name → Nat} {d : Nat}
    {Δ : List AnnotTerm} (hΔ : Δ.length = d) {n : Name} {us : List Level} {as : List Expr}
    (h : ∀ x ∈ as, CtxOkP m φ d Δ x) : CtxOkP m φ d Δ (Expr.mkAppN (.const n us) as) := by
  refine ⟨hΔ, fun l hl => ?_⟩
  rcases ConLeche.fvarLeaves_mkAppN hl with h0 | ⟨x, hx, hlx⟩
  · simp [Expr.fvarLeaves] at h0
  · exact (h x hx).2 l hlx

/-- A node's key parameters are scoped, and closed, at the depth of the
frames its frame is derived under. -/
theorem posNodeOk_dsAnc {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {t : PosTree} (hok : PosNodeOk ops env ctx t) :
    ∀ x ∈ t.key.ds, Expr.WScoped (ctx.hiAt t.anc.length) x ∧ x.looseBVarsBounded 0 = true := by
  intro x hx
  obtain ⟨-, -, -, -, hws, hanc⟩ := hok
  refine ⟨?_, ConLeche.Expr.bvarB_le (Nat.le_of_eq (hws x hx).2)⟩
  rcases hanc with ⟨hao, -⟩ | ⟨han, hds⟩
  · rw [hao]; exact (hws x hx).1
  · rw [han]; exact (hds x hx).2

/-- **K.52 at a node** (`hfit` of `FrameMono`): at every valuation of the
node's stack context, its key's parameters read in the container's
parameter telescope — the key instance is typed at the node's depth
(`posD_frame_kty`), graded there (`infer_sound`), and a graded instance
reads its parameters in the telescope (`keyParamsFit`). -/
theorem nodeKeyFit {env : Env} (mk : EnvModelM V μ env) {φ : Name → Nat} {ctx : NestCtx} {F : Nat}
    {Δ0 : List AnnotTerm} (hΔ0 : Δ0.length = ctx.hiAt 0) {t : PosTree}
    (hok : PosNodeOk (fueledOps .verified F) env ctx t) (hsem : NodeSemAt mk.base2 φ ctx Δ0 t)
    {D : LfpDatum V} (hD : D ∈ mk.lfpBlocks) {mm : Nat} (hmm : mm < D.k)
    (hhead : D.member mm = (t.grp.headD default).1)
    {cv : ConstantVal} {caps : IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps))
    (hlenP : t.key.ds.length = (D.params (Level.substFn φ cv.levelParams t.key.lvls)).length)
    {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mk.base2.acval env φ (ctx.hiAt t.anc.length) t.key.ds dsa) :
    ∀ σ : Nat → V, Sat V (stackCtx mk.base2 φ ctx t.anc Δ0) σ →
      Sat V (D.params (Level.substFn φ cv.levelParams t.key.lvls)).reverse
        (keyFrame dsa (ctx.hiAt t.anc.length) σ) := by
  obtain ⟨ty, hty⟩ := posD_frame_kty hok.1
  rw [← hhead] at hty
  have hty' : ConLeche.inferTypeCore .verified env F (ctx.hiAt t.anc.length)
      (Expr.mkAppN (.const (D.member mm) t.key.lvls) t.key.ds) = .ok ty := hty
  have hws := posNodeOk_dsAnc hok
  obtain ⟨-, hC, hL⟩ := hsem
  have hwsE : Expr.WScoped (ctx.hiAt t.anc.length)
      (Expr.mkAppN (.const (D.member mm) t.key.lvls) t.key.ds) :=
    wScoped_mkAppN_of _ (by simp [Expr.WScoped]) fun x hx => (hws x hx).1
  have hbE : (Expr.mkAppN (.const (D.member mm) t.key.lvls) t.key.ds).looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_mkAppN (by simp [Expr.looseBVarsBounded]) fun x hx => (hws x hx).2
  have hLE : Expr.LeavesBounded (Expr.mkAppN (.const (D.member mm) t.key.lvls) t.key.ds) := by
    intro l hl
    rcases ConLeche.fvarLeaves_mkAppN hl with h0 | ⟨x, hx, hlx⟩
    · simp [Expr.fvarLeaves] at h0
    · exact hL x hx l hlx
  obtain ⟨wa, hwa⟩ := acceptedReads_of mk.base2 φ hty' hwsE hbE hLE
  have hCE : CtxOkP mk.base2 φ (ctx.hiAt t.anc.length) (stackCtx mk.base2 φ ctx t.anc Δ0)
      (Expr.mkAppN (.const (D.member mm) t.key.lvls) t.key.ds) :=
    CtxOkP.mkAppN_const (stackCtx_length_hi hΔ0 _) hC
  obtain ⟨-, -, -, -, hgr, -⟩ :=
    Rules.infer_sound (Rules.RulesInputs.ofSem mk φ) (Rules.inferTypeCore_bridge hty')
      ⟨hwsE, hbE, hLE⟩ hCE.toCtxOk hwa
  intro σ hσ
  have hwa' : denoteMeta mk.base2.acval env φ (ctx.hiAt t.anc.length)
      (Expr.mkAppN (.const (D.member mm) t.key.lvls) (t.key.ds ++ [])) = some wa := by
    rw [List.append_nil]; exact hwa
  have := keyParamsFit mk hD hmm hf (Nat.le_refl _) hwa' hlenP (fun x hx => (hws x hx).1) hdsa σ
    (hgr σ hσ)
  rw [Nat.sub_self] at this
  exact this

end ConLeche.Model
