module

public import ConLeche.Model.Inductives.TargetNodeCover
public import ConLeche.Model.Inductives.PosDerivNodes
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Cached.Erase

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

/-! ## Admissible valuations -/

section Adm

variable {envI envC : Env} (mk : EnvModelM V μ envI) (mpC : EnvModelM V μ envC) (ctx : NestCtx)
  (d : BlockData V) (ns : List PosTree) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)

/-- **The true valuation of a frame stack**: the prefix's parameters, then
every hole at its constant's value (`nodeTrueVal`). -/
@[expose] noncomputable def trueVal (prog : List NestHole) : Nat → V :=
  nodeTrueVal ctx.nP (nodeHv mpC.base2.acval envC ctx ψ prog) xs ρ

/-- Node `o`'s component holding the name `n`. -/
@[expose] noncomputable def nlComp (o : Nat) (n : Name) : Nat :=
  (nlDb mpC d ns o).names.idxOf n

/-- **An admissible valuation of a frame stack** at the visit's hypotheses
`G`: the stack context satisfied, the parameters and the tail the true
valuation's, every member hole's value — at full arity — an element `G`
holds of at node `0` where it is applied to the block's parameters and
a fitting index spine, and otherwise below the member's constant; every
frame hole owned by a listed node `o` — whose true frame is the hole's
key read at the true valuation — and its value — at its key's parameters
and full arity — an element `G` holds of at `o` where the index spine fits
`o`'s telescope, and otherwise below the true value. -/
structure AdmVal (G : Nat → Nat → V → V → Prop) (prog : List NestHole) (σ : Nat → V) : Prop where
  sat : Sat V (stackCtx mk.base2 ψ ctx prog (d.holeCtx ψ).reverse) σ
  agree : AgreeOff (holeP (ctx.hiAt prog.length) ctx.nP (ctx.hiAt prog.length)) σ
    (trueVal mpC ctx ψ ρ xs prog)
  member : ∀ t, t < ctx.names.length → ∀ as : List V, as.length = ctx.nP + ctx.nIdxs.getD t 0 →
    ∀ y, y ∈ˢ as.foldl app (σ (ctx.hiAt prog.length - 1 - (ctx.nP + t))) →
      (as.take ctx.nP = xs.take ctx.nP →
        SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) (as.drop ctx.nP) →
        G 0 t (tupW (d.toLfp.u t ψ) (as.drop ctx.nP)) y) ∧
      (¬ (as.take ctx.nP = xs.take ctx.nP ∧
          SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) (as.drop ctx.nP)) →
        y ∈ˢ as.foldl app (trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.nP + t))))
  frame : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk →
    ∃ o, 0 < o ∧ o ≤ ns.length ∧
      hk ∈ ConLeche.grpNews (ns.getD (o - 1) default).key.lvls (ns.getD (o - 1) default).key.ds
        (ctx.hiAt (ns.getD (o - 1) default).anc.length) (ns.getD (o - 1) default).grp ∧
      ∀ dsa, DenoteMetaSpine mk.base2.acval envI ψ (ctx.hiAt prog.length) hk.key.ds dsa →
      -- the owner's true frame is the hole's key read at the true valuation
      keyFrame dsa (ctx.hiAt prog.length) (trueVal mpC ctx ψ ρ xs prog)
        = nlFr mpC ctx d ns ψ ρ xs o ∧
      ∀ is : List V, is.length + hk.key.ds.length = ConLeche.nestArity ctx hk.key.cname →
      ∀ y, y ∈ˢ (dsa.map (interp V σ) ++ is).foldl app
          (σ (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))) →
        (SpineFit (nlFr mpC ctx d ns ψ ρ xs o)
            ((nlDb mpC d ns o).ids (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is →
          G o (nlComp mpC d ns o hk.key.cname)
            (tupW ((nlDb mpC d ns o).u (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is) y) ∧
        (¬ SpineFit (nlFr mpC ctx d ns ψ ρ xs o)
            ((nlDb mpC d ns o).ids (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is →
          y ∈ˢ (dsa.map (interp V (trueVal mpC ctx ψ ρ xs prog)) ++ is).foldl app
            (trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))))

/-- A node's key parameters, read at the formers' model where its frame is
derived. -/
@[expose] noncomputable def nodeDsaI (t : PosTree) : List AnnotTerm :=
  t.key.ds.map fun x => (denoteMeta mk.base2.acval envI ψ (ctx.hiAt t.anc.length) x).getD default

/-- **The admissible frames of node `b`**: node `0` at its true frame
only; a derived node at its key's parameters read at an admissible
valuation of the frames its frame is derived under. -/
@[expose] def nodeAdm (b : Nat) (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V) : Prop :=
  if b = 0 then ρ' = nlFr mpC ctx d ns ψ ρ xs 0
  else ∃ σ, AdmVal mk mpC ctx d ns ψ ρ xs G (ns.getD (b - 1) default).anc σ ∧
    ρ' = keyFrame (nodeDsaI mk ctx ψ (ns.getD (b - 1) default))
      (ctx.hiAt (ns.getD (b - 1) default).anc.length) σ

end Adm

/-! ## OWED — the calls at the admissible frames -/

/-- **OWED — the calls** (`TgtNodeDyn.hcall`) at the admissible frames
`nodeAdm`, under everything `NestedNodeDynOwed` provides: at a related
pair and a true decoding, every call target lands at a node related to its
class — its own group, an owner `G` holds of, or a deeper node at an
admissible frame of the visit extended by the caller's tuple
(`NodeLands`). -/
@[expose] def NestedNodeCallsOwed (V : Type w) [SetTheory V] (μ : ConLeche.CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr))
    (nodesR : ConLeche.NestNodes),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR →
    ∀ (mk : EnvModelM V μ envI), LfpCover mk pp.toBlockShape.memberNames →
    (∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks) →
    (∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n) →
    (∀ D ∈ mpC.lfpBlocks, D = dR.toLfp ∨ D ∈ mk.lfpBlocks) →
    (∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mk.base2.acval envI ψ dd e = some ea →
        denoteMeta mpC.base2.acval envC ψ dd e = some ea) →
    ∀ (fvsP : List Expr) (ns : List PosTree),
      (∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t) →
      (∀ t ∈ ns, NodeOwned (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t) →
      (∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns) →
      (∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids) →
      (∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ (pp.nestCtx fvsP envI.find? envI.consts)
        (dR.holeCtx ψ).reverse t) →
      (∀ t ∈ ns, ConLeche.FrameRec (fueledOps .verified F) envI
        (pp.nestCtx fvsP envI.find? envI.consts) nodesR.ctors t.anc t.key.lvls t.key.ds t.grp) →
      NodeListFacts mpC (pp.nestCtx fvsP envI.find? envI.consts) ns →
      ∀ (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal),
        (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
          TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) →
        (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
          Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind) →
        ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V),
          (∃ c, c < (tgtRs out).length ∧
            tgtClsG dR mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) →
          ∀ c b, c < (tgtRs out).length →
          nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find? envI.consts) dR pp.toBlockShape out ns
            ψ ρ xs envC c b → ∀ t j fs,
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
                out ns ψ ρ xs envC c' b' ∧
              NodeLands (ns.length + 1) (nlDb mpC dR ns) (nlψ envC ns ψ)
                (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs) (nlDp ns)
                (nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs) b
                (tgtClsM mc pp.toBlockShape out c) t j fs b' (tgtClsM mc pp.toBlockShape out c') t' y

end ConLeche.Model
