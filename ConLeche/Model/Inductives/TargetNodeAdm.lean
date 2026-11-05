module

public import ConLeche.Model.Inductives.PosDerivNodes
public import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Cached.Erase

public section

/-!
# The node presentation's admissible frames

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

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockParts BlockShape fueledOps PosTree PosNodeOk PosD)

universe w

variable {V : Type w} [SetTheory V]

/-! ## K.52 at a node: the key's parameters fit -/

/-- **K.52, inverted**: a derived frame's key is typed against its telescope at the frame's
depth. -/
theorem posD_frame_kty {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {ts : List PosTree} (h : PosD ops env ctx (.frame prog us ds grp) ts) :
    ConLeche.familyKeyCheck ops env ctx.find? (ctx.hiAt prog.length) (grp.headD default).1 us ds
      = .ok () := by
  cases h with
  | frame _ _ _ _ _ _ _ _ hkty _ => exact hkty

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
parameter telescope: the key is typed against that telescope at the node's depth
(`posD_frame_kty`), and `keyParamsFit` reads the certificates. -/
theorem nodeKeyFit {env : Env} (mk : EnvModelM V env) {φ : Name → Nat} {ctx : NestCtx} {F : Nat}
    {Δ0 : List Term} (hΔ0 : Δ0.length = ctx.hiAt 0) {t : PosTree}
    (hok : PosNodeOk (fueledOps .verified F) env ctx t) (hsem : NodeSemAt mk.base2 φ ctx Δ0 t)
    (hcov : ContCover mk ctx)
    {D : LfpDatum V} (hD : D ∈ mk.lfpBlocks) {mm : Nat} (hmm : mm < D.k)
    (hhead : D.member mm = (t.grp.headD default).1)
    {cv : ConstantVal} {caps : IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps))
    (hlenP : t.key.ds.length = (D.params (Level.substFn φ cv.levelParams t.key.lvls)).length)
    {dsa : List Term}
    (hdsa : DenoteSpine mk.base2.acval env φ (ctx.hiAt t.anc.length) t.key.ds dsa) :
    ∀ σ : Nat → V, Sat V (stackCtx mk.base2 φ ctx t.anc Δ0) σ →
      Sat V (D.params (Level.substFn φ cv.levelParams t.key.lvls)).reverse
        (keyFrame dsa (ctx.hiAt t.anc.length) σ) := by
  have hk := posD_frame_kty hok.1
  rw [← hhead] at hk
  obtain ⟨-, hcerts⟩ := hcov.keyCerts hD hmm hf hk
  have hws := posNodeOk_dsAnc hok
  obtain ⟨-, hC, hL⟩ := hsem
  have hΔ := stackCtx_length_hi (m := mk.base2) (φ := φ) hΔ0 t.anc
  intro σ hσ
  exact (keyParamsFit mk (Rules.RulesInputs.ofSem mk φ) hD hmm hf hcerts hlenP hΔ
    (fun x hx => ⟨⟨(hws x hx).1, (hws x hx).2, hL x hx⟩, CtxOk.toS (hC x hx).toCtxOk⟩) hdsa σ hσ
    (fun x hx => CtxOk.leavesGr (hC x hx).toCtxOk hσ)).1

/-! ## Admissible valuations -/

section Adm

variable {envI envC : Env} (mk : EnvModelM V envI) (mpC : EnvModelM V envC) (ctx : NestCtx)
  (d : BlockData V) (ns : List PosTree) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)

/-- **The true valuation of a frame stack**: the prefix's parameters, then
every hole at its read-back's value at the prefix (`nodeTrueVal`: a
member hole the member applied to the block's parameters, a frame hole its
container applied to its key's parameters, read back). -/
@[expose] noncomputable def trueVal (prog : List NestHole) : Nat → V :=
  nodeTrueVal ctx.nP (nodeHv mpC.base2.acval envC ctx ψ prog xs.length) xs ρ

/-- Node `o`'s component holding the name `n`. -/
@[expose] noncomputable def nlComp (o : Nat) (n : Name) : Nat :=
  (nlDb mpC d ns o).names.idxOf n

/-- **The owner of hole `i` of node `b`'s frame stack**, along the parent
pointers `par`: the parent if the hole is in the
parent's group, else the parent's owner of it (fuel `f`; each step goes to
an earlier position). -/
@[expose] def holeOwnerF (ns : List PosTree) (par : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, b, i =>
    if i < (ns.getD (par b - 1) default).anc.length ∧ par b < b then holeOwnerF ns par f (par b) i
    else par b

/-- The owner, at enough fuel. -/
@[expose] def holeOwner (ns : List PosTree) (par : Nat → Nat) (b i : Nat) : Nat :=
  holeOwnerF ns par (b + 1) b i

/-- **An admissible valuation of a frame stack** at the visit's hypotheses
`G`: the stack context satisfied, the parameters and the tail the true
valuation's, every member hole's value — a family over the member's
indices, at full arity — an element `G` holds of at node `0` where the
index spine fits (at the block's parameters), and otherwise below the true
value (the member applied to the block's parameters); every frame hole
owned by its listed owner `own i` (the stack's owners: one owner
OCCURRENCE per hole, so that the calls land at a fixed node) — whose true
frame is the hole's key read at the true valuation — and its value — a
family over the container's indices, at full arity — an element `G` holds
of at the owner where the index spine fits the owner's telescope, and
otherwise below the true value. -/
structure AdmVal (own : Nat → Nat) (G : Nat → Nat → V → V → Prop) (prog : List NestHole)
    (σ : Nat → V) : Prop where
  sat : Sat V (stackCtx mk.base2 ψ ctx prog (d.holeCtx ψ).reverse) σ
  agree : AgreeOff (holeP (ctx.hiAt prog.length) ctx.nP (ctx.hiAt prog.length)) σ
    (trueVal mpC ctx ψ ρ xs prog)
  member : ∀ t, t < ctx.names.length → ∀ is : List V, is.length = ctx.nIdxs.getD t 0 →
    ∀ y, y ∈ˢ is.foldl app (σ (ctx.hiAt prog.length - 1 - (ctx.nP + t))) →
      (SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) is →
        G 0 t (tupW (d.toLfp.u t ψ) is) y) ∧
      (¬ SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) is →
        y ∈ˢ is.foldl app (trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.nP + t))))
  frame : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk →
    0 < own i ∧ own i ≤ ns.length ∧
      hk ∈ ConLeche.grpNews (ns.getD (own i - 1) default).key.lvls
        (ns.getD (own i - 1) default).key.ds
        (ctx.hiAt (ns.getD (own i - 1) default).anc.length) (ns.getD (own i - 1) default).grp ∧
      -- the frames below the hole end in the owner's
      (∃ Y, prog.drop (prog.length - i) = Y ++ (ns.getD (own i - 1) default).anc) ∧
      -- the owner's true frame is the hole's key read at the true valuation
      (∀ dsa, DenoteSpine mk.base2.acval envI ψ (ctx.hiAt prog.length) hk.key.ds dsa →
        keyFrame dsa (ctx.hiAt prog.length) (trueVal mpC ctx ψ ρ xs prog)
          = nlFr mpC ctx d ns ψ ρ xs (own i)) ∧
      ∀ is : List V, is.length = hk.nIdx →
      ∀ y, y ∈ˢ is.foldl app (σ (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))) →
        (SpineFit (nlFr mpC ctx d ns ψ ρ xs (own i))
            ((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
              (nlψ envC ns ψ (own i))) is →
          G (own i) (nlComp mpC d ns (own i) hk.key.cname)
            (tupW ((nlDb mpC d ns (own i)).u (nlComp mpC d ns (own i) hk.key.cname)
              (nlψ envC ns ψ (own i))) is) y) ∧
        (¬ SpineFit (nlFr mpC ctx d ns ψ ρ xs (own i))
            ((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
              (nlψ envC ns ψ (own i))) is →
          y ∈ˢ is.foldl app
            (trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))))

/-- A node's key parameters, read at the formers' model where its frame is
derived. -/
@[expose] noncomputable def nodeDsaI (t : PosTree) : List Term :=
  t.key.ds.map fun x => (denote mk.base2.acval envI ψ (ctx.hiAt t.anc.length) x).getD default

/-- **The admissible frames of node `b`**: node `0` at its true frame
only; a derived node at its key's parameters read at an admissible
valuation of the frames its frame is derived under. -/
@[expose] def nodeAdm (par : Nat → Nat) (b : Nat) (G : Nat → Nat → V → V → Prop)
    (ρ' : Nat → V) : Prop :=
  if b = 0 then ρ' = nlFr mpC ctx d ns ψ ρ xs 0
  else ∃ σ, AdmVal mk mpC ctx d ns ψ ρ xs (holeOwner ns par b) G (ns.getD (b - 1) default).anc σ ∧
    ρ' = keyFrame (nodeDsaI mk ctx ψ (ns.getD (b - 1) default))
      (ctx.hiAt (ns.getD (b - 1) default).anc.length) σ

end Adm

end ConLeche.Model
