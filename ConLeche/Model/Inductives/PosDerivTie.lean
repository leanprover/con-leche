module

public import ConLeche.Verify.Inductives.PosDerivInv
public import ConLeche.Kernel.Inductives.BlockTail
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas

public section

/-!
# Every recursor class is a node (lane POSDERIV session 5, ruling (i))

The coordinator's ruling (i) on NESTIND's F14: the positivity walk covers
OFFICIAL's auxiliary set — every container's whole recorded block
(N2-eager frames) and every syntactic nested occurrence (`nestSyn`) — and
the recursor stage admits an outside major only at one of the walk's
recorded classes (`targetMajorOf`'s `aux` check).  So every class of the
recursor family is a node:

* a MEMBER class is the block's own (the member arm);
* an OUTSIDE class `I.{us} Ds` (a reached container, a group mate, a
  syntactic occurrence) is `NodeAtCtor`: some member constructor `(c, j)`
  has a derivation (`MemberCtorD`) whose forest holds a node `t` with
  `I ∈ t.grp` and `ctx.concreteKey t.occ I t.key = ⟨I, us, Ds⟩` — the
  node's instantiation with its holes back to their constants (member
  `m`'s hole to `T_m.{lps}`, the `i`-th frame hole to its frame's group
  member at the frame's levels).

**THE TIE**: `outsideMajor_isNode`.  Its two halves are the run's
(`checkBlockPositivity_nodesM`: every recorded class is a node of a
member constructor's derivation) and the check's (`targetRecCheck_aux`:
every outside major is recorded).  The node is `PosNodeOk`
(`posD_nodes` on the constructor's derivation), its frame derived, its
kids nodes, lower (`PosTree.height_kid`), and reached from the
constructor's roots (`PosTree.forest`).
-/

namespace ConLeche.Model

open ConLeche

/-- **The run half**: every class the positivity run recorded is a node of
a member constructor's derivation (`NodeAtCtor`), at the environment's
scoping (`checkBlockPositivity_derivM`'s premises). -/
theorem checkBlockPositivity_nodesM {env : Env} (hwf : ConLeche.EnvWF env) {F : Nat}
    {p : BlockParts} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nst : Bool}
    {nodes : List NestKey}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps .verified F) env env.find?
      env.consts p cvTas ctorsAs nst = .ok (kinds, nfs, nodes))
    (hT0 : ∀ cvTa0, cvTas.head? = some cvTa0 → cvTa0.type.hasFvar = false)
    (hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes ∧
      ∀ k ∈ nodes, NodeAtCtor (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts)
        holes ctorsAs nfs k := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, h⟩ :=
    ConLeche.checkBlockPositivity_deriv (fun dep e w hw hws => ConLeche.whnf_WScoped hwf F hw hws)
      hrun
  have hpar : ∀ x ∈ fvsP, Expr.WScoped ((p.nestCtx fvsP env.find? env.consts).hiAt 0) x := by
    intro x hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    have hw := (ConLeche.openPisAtFvars_WScoped p.nP cvTa0.type 0 h2
      (Expr.WScoped.of_not_hasFvar (hT0 _ h1))).1 x hx
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ h2 i _ hi
    have hilt : i < p.nP := by
      rw [← ConLeche.Verify.openPisAtFvars_length _ h2]; exact (List.getElem?_eq_some_iff.mp hi).1
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨by simp only [NestCtx.hiAt, BlockParts.nestCtx]; omega, hw.2⟩
  exact ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, (h ⟨fun ci hci => (hwf ci hci).1,
    fun n ci hf => (hwf ci (List.mem_of_find?_eq_some hf)).1⟩ hpar hcl).2⟩

/-- **THE MAJOR → NODE TIE: every class of the recursor family is a node**
(ruling (i); for lane NESTIND).  At the uniform install's recursor stage
(`checkBlockRec`, the target check against the positivity run's recorded
classes `nodes`) and the positivity run that recorded them, every OUTSIDE
major of the checked family — a reached container, a group mate of one,
a syntactic occurrence — is a class of a node of some member
constructor's derivation (`NodeAtCtor`: the node `t` in the derivation's
forest, `I ∈ t.grp`, `ctx.concreteKey t.occ I t.key = ⟨I, us, Ds⟩`).
Member majors are the block's own classes. -/
theorem outsideMajor_isNode {envC envI : Env} (hwf : ConLeche.EnvWF envI) {F : Nat}
    {pp : BlockParts} {cvTas : List ConstantVal} {ctorsAs ctorsN : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : List NestKey}
    {nst nested conf : Bool} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (hrec : ConLeche.checkBlockRec (m := CheckM) (fueledOps .verified F) envC pp nst nested conf
      nodes block cvTas ctorsAs ctorsN = .ok out)
    (hpos : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps .verified F) envI envI.find?
      envI.consts pp cvTas ctorsAs nst = .ok (kinds, nfs, nodes))
    (hT0 : ∀ cvTa0, cvTas.head? = some cvTa0 → cvTa0.type.hasFvar = false)
    (hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars pp.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (pp.nestCtx fvsP envI.find? envI.consts) = some holes ∧
      ∀ o ∈ out, o.2.1.member = none →
        NodeAtCtor (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) holes
          ctorsAs nfs ⟨o.2.1.ind, o.2.1.lvls, o.2.1.ds⟩ := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hn⟩ := checkBlockPositivity_nodesM hwf hpos hT0 hcl
  have haux := ConLeche.targetRecCheck_aux
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hrec))
  exact ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun o ho hM =>
    hn _ (List.contains_iff_mem.mp (haux o ho hM))⟩

end ConLeche.Model
