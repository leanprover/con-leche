module

public import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Kernel.Inductives.BlockTail
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
public import ConLeche.Model.Inductives.TargetNodeRb
public import ConLeche.Model.Inductives.TargetRuleData

public section

/-!
# Every recursor class is a node

The positivity walk is SEEDED with the recursor family's outside majors
(`nestSeeds`: each walked at the root like a container instance), on top
of every container's whole recorded block (N2-eager frames), and the
recursor stage admits an outside major only at one of the walk's
recorded classes (`targetMajorOf`'s `aux` check).  So every class of the
recursor family is a node:

* a MEMBER class is the block's own (the member arm);
* an OUTSIDE class `I.{us} Ds` (a reached container, a group mate, a
  seed) is `NodeAtCtor` or `NodeAtSeed`: some member constructor `(c, j)`
  has a derivation (`MemberCtorD`), or some seed has one (`PosD.seed`),
  whose forest holds a node `t` with
  `I ∈ t.grp` and `ctx.concreteKey t.occ I t.key = ⟨I, us, Ds⟩` — the
  node's instantiation with its holes back to their constants (member
  `m`'s hole to `T_m.{lps}`, the `i`-th frame hole to its frame's group
  member at the frame's levels).

**THE TIE** (inside `outsideClass_reachedNode`).  Its two halves are the run's
(`checkBlockPositivity_nodesM`: every recorded class is a node of a
member constructor's derivation or of a seed's) and the check's (`targetRecCheck_aux`:
every outside major is recorded).  The node is `PosNodeOk`
(`posD_nodes` on the constructor's derivation), its frame derived, its
kids nodes, lower (`PosTree.height_kid`), and reached from the
constructor's roots (`PosTree.forest`).
-/

namespace ConLeche.Model

open ConLeche

/-- **The run half**: every class the positivity run recorded is a node of
a member constructor's derivation (`NodeAtCtor`) or of a seed's
(`NodeAtSeed`), at the environment's scoping
(`checkBlockPositivity_derivM`'s premises). -/
theorem checkBlockPositivity_nodesM {env : Env} (hwf : ConLeche.EnvWF env) {F : Nat}
    {p : BlockParts} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)}
    {nodes : NestNodes}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps .verified F) env env.find?
      env.consts p cvTas ctorsAs = .ok (kinds, nfs, nodes))
    (hT0 : ∀ cvTa0, cvTas.head? = some cvTa0 → cvTa0.type.hasFvar = false)
    (hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes ∧
      ∀ k ∈ nodes.keys, NodeAtCtor (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts)
        holes ctorsAs nfs nodes.ctors k ∨
        NodeAtSeed (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts) nodes.ctors k := by
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
    fun n ci hf => (hwf ci (List.mem_of_find?_eq_some hf)).1⟩ hpar hcl
    ConLeche.fueledOps_annotate_facts).2⟩


/-! ## The coverage theorem's shape: `NodeMajor` at a REACHED node -/

section ReadBack

/-- `replaceFVars` at no mapped variable is the identity. -/
theorem replaceFVars_none : ∀ (e : Expr), e.replaceFVars (fun _ => none) = e
  | .bvar _ | .sort _ | .const .. | .lit _ | .fvar .. => rfl
  | .app f a => by simp [Expr.replaceFVars, replaceFVars_none f, replaceFVars_none a]
  | .lam t b _ => by simp [Expr.replaceFVars, replaceFVars_none t, replaceFVars_none b]
  | .forallE t b _ => by simp [Expr.replaceFVars, replaceFVars_none t, replaceFVars_none b]
  | .letE t v b => by
    simp [Expr.replaceFVars, replaceFVars_none t, replaceFVars_none v, replaceFVars_none b]
  | .proj _ _ x => by simp [Expr.replaceFVars, replaceFVars_none x]

/-- The holes `p ..< p + |hs|` to the terms `hs`, positionally. -/
@[expose] def holeMap (p : Nat) (hs : List Expr) (i : Nat) : Option Expr :=
  if p ≤ i then hs[i - p]? else none

/-- `holeMap` of an empty list maps nothing. -/
theorem holeMap_nil (p : Nat) : holeMap p [] = fun _ => none := by
  funext i; simp [holeMap]

/-- One substitution step of `substAll` at a closed constant list. -/
theorem substFvarAt_replaceFVars {p : Nat} {a : Expr} {as : List Expr}
    (_ha : ∃ n us, a = .const n us) (has : ∀ c ∈ as, ∃ n us, c = .const n us) :
    ∀ (e : Expr), e.fvarsBelow (p + 1 + as.length) →
      Expr.substFvarAt p a (e.replaceFVars (holeMap (p + 1) as))
        = e.replaceFVars (holeMap p (a :: as)) := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp only [Expr.replaceFVars, holeMap]
    by_cases h1 : p + 1 ≤ i
    · have hlt : i - (p + 1) < as.length := by omega
      rw [if_pos h1, List.getElem?_eq_getElem hlt, Option.getD_some, if_pos (by omega)]
      obtain ⟨n, us, hc⟩ := has _ (List.getElem_mem hlt)
      rw [hc]
      have : i - p = (i - (p + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ, List.getElem?_eq_getElem hlt, hc]
      simp [Expr.substFvarAt]
    · rw [if_neg h1]
      simp only [Option.getD_none]
      by_cases h2 : i = p
      · subst h2
        simp [Expr.substFvarAt]
      · have hlt : i < p := by omega
        rw [if_neg (by omega)]
        simp [Expr.substFvarAt, h2, show ¬ i > p by omega]
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | const _ _ => intro _; rfl
  | lit _ => intro _; rfl
  | app f b ihf ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, ihf hb.1, ihb hb.2]
  | lam t b m iht ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, iht hb.1, ihb hb.2]
  | forallE t b m iht ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, iht hb.1, ihb hb.2]
  | letE t v b iht ihv ihb =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, iht hb.1, ihv hb.2.1, ihb hb.2.2]
  | proj s i x ih =>
    intro hb
    simp only [Expr.fvarsBelow] at hb
    simp [Expr.replaceFVars, Expr.substFvarAt, ih hb]

/-- **`substAll` at closed constants is `replaceFVars`** (below the range). -/
theorem substAll_eq_replaceFVars :
    ∀ (hs : List Expr) (p : Nat), (∀ c ∈ hs, ∃ n us, c = .const n us) →
      ∀ (e : Expr), e.fvarsBelow (p + hs.length) →
        substAll p hs e = e.replaceFVars (holeMap p hs)
  | [], p, _, e, _ => by simp [substAll, holeMap_nil, replaceFVars_none]
  | a :: as, p, hc, e, hb => by
    simp only [substAll]
    rw [substAll_eq_replaceFVars as (p + 1) (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) e
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)]
    exact substFvarAt_replaceFVars (hc a List.mem_cons_self)
      (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) e
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)

/-- The kernel's hole constants are `nodeHoleConsts`, positionally. -/
theorem nestHoleConst_eq_holeMap (ctx : NestCtx) (occ : List NestHole) :
    nestHoleConst ctx occ = holeMap ctx.nP (nodeHoleConsts ctx occ) := by
  funext i
  simp only [nestHoleConst, holeMap, nodeHoleConsts, NestCtx.hiAt, Nat.add_zero]
  by_cases h1 : ctx.nP ≤ i
  · simp only [h1, true_and, if_true]
    by_cases h2 : i < ctx.nP + ctx.names.length
    · simp only [h2, if_true]
      have hlt : i - ctx.nP < ctx.names.length := by omega
      rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_map,
        List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    · simp only [h2, if_false, show ctx.nP + ctx.names.length ≤ i by omega, true_and]
      rw [List.getElem?_append_right (by simp; omega), List.length_map]
      by_cases h3 : i < ctx.nP + ctx.names.length + occ.length
      · simp only [h3, if_true, List.getElem?_map]
        congr 2
        omega
      · simp only [h3, if_false]
        rw [List.getElem?_eq_none (by simp; omega)]
  · simp [h1, show ¬ (ctx.nP + ctx.names.length ≤ i) by omega]

/-- **The kernel's concrete key is the node's key read back**, at
parameters below the occurrence's holes. -/
theorem concrete_eq_nodeRb (ctx : NestCtx) (occ : List NestHole) {x : Expr}
    (hx : x.fvarsBelow (ctx.hiAt occ.length)) :
    x.replaceFVars (nestHoleConst ctx occ) = nodeRb ctx occ x := by
  rw [nestHoleConst_eq_holeMap, nodeRb, substAll_eq_replaceFVars _ _
    (nodeHoleConsts_const ctx occ) x (by rw [nodeHoleConsts_length]; simpa [NestCtx.hiAt,
      Nat.add_assoc] using hx)]

end ReadBack

/-! ## Reached nodes -/

theorem PosTree.mem_forest_iff {u : PosTree} :
    ∀ {ts : List PosTree}, u ∈ PosTree.forest ts ↔ ∃ k ∈ ts, u ∈ k.nodes
  | [] => by simp [PosTree.forest]
  | t :: ts => by
    rw [PosTree.mem_forest_cons, PosTree.mem_forest_iff]
    simp

/-- Every node below a reached node is reached. -/
theorem PosTree.Reached.nodes {ts : List PosTree} :
    ∀ (n : Nat) (t : PosTree), t.height ≤ n → PosTree.Reached ts t →
      ∀ u ∈ t.nodes, PosTree.Reached ts u
  | 0, t, hh, _, _, _ => by
    cases t with
    | node occ anc key grp kids => simp [PosTree.height] at hh
  | n + 1, t, hh, hr, u, hu => by
    rcases PosTree.mem_nodes.mp hu with rfl | hu
    · exact hr
    · obtain ⟨k, hk, hku⟩ := PosTree.mem_forest_iff.mp hu
      have := PosTree.height_kid hk
      exact PosTree.Reached.nodes n k (by omega) (.kid hr hk) u hku

/-- **Every node of a forest is reached** from its roots. -/
theorem PosTree.Reached.of_forest {ts : List PosTree} {u : PosTree}
    (hu : u ∈ PosTree.forest ts) : PosTree.Reached ts u := by
  obtain ⟨k, hk, hku⟩ := PosTree.mem_forest_iff.mp hu
  exact PosTree.Reached.nodes k.height k (Nat.le_refl _) (.root hk) u hku

/-- **THE COVERAGE THEOREM**: at the uniform install's recursor stage and
the positivity run whose classes it checked against, every OUTSIDE class `c` of the family has,
in some member constructor's derivation (`MemberCtorD`, forest `ts`) or
some seed's (`PosD.seed`), a REACHED node `t` (`PosTree.Reached ts t`), a node (`PosNodeOk`), with
`NodeMajor ctx (tgtMajor out c) t`: the major names a member of `t`'s
group at the key's levels, its parameters the key read back. -/
theorem outsideClass_reachedNode {envC envI : Env} (hwf : ConLeche.EnvWF envI) {F : Nat}
    {pp : BlockParts} {cvTas : List ConstantVal} {ctorsAs ctorsN : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : NestNodes}
    {nested conf : Bool} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (hrec : ConLeche.checkBlockRec (m := CheckM) (fueledOps .verified F) envC pp nested conf
      nodes block cvTas ctorsAs ctorsN = .ok out)
    (hpos : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps .verified F) envI envI.find?
      envI.consts pp cvTas ctorsAs = .ok (kinds, nfs, nodes))
    (hT0 : ∀ cvTa0, cvTas.head? = some cvTa0 → cvTa0.type.hasFvar = false)
    (hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars pp.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (pp.nestCtx fvsP envI.find? envI.consts) = some holes ∧
      ∀ c, c < out.length → (tgtMajor out c).member = none →
        ∃ ts : List PosTree,
          ((∃ (m : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat)
            (crest : Expr) (ks : List PosKind),
            ctorsAs[m]? = some cs ∧ cs[j]? = some cA ∧
            instPisWith fvsP (nestAbstract (pp.nestCtx fvsP envI.find? envI.consts) holes
              cA.1.type) = some crest ∧
            MemberCtorD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
              cA.2 crest ks ((nfs.getD m []).getD j default) ts) ∨
           ∃ key, PosD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
             (.seed key) ts) ∧
          TreeRec (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
            nodes.ctors ts ∧
          ∃ t, PosTree.Reached ts t ∧
            PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t ∧
            NodeMajor (pp.nestCtx fvsP envI.find? envI.consts) (tgtMajor out c) t := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hn⟩ := checkBlockPositivity_nodesM hwf hpos hT0 hcl
  -- the major → node tie: an outside major is a recorded class
  have haux := ConLeche.targetRecCheck_aux
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hrec))
  refine ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun c hc hM => ?_⟩
  have ho : out.getD c default ∈ out := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]
    exact List.getElem_mem hc
  obtain ⟨ts, hsrc, htr, t, ht, cn, hcn, hkey⟩ : ∃ ts : List PosTree,
      ((∃ (m : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat)
        (crest : Expr) (ks : List PosKind),
        ctorsAs[m]? = some cs ∧ cs[j]? = some cA ∧
        instPisWith fvsP (nestAbstract (pp.nestCtx fvsP envI.find? envI.consts) holes
          cA.1.type) = some crest ∧
        MemberCtorD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
          cA.2 crest ks ((nfs.getD m []).getD j default) ts) ∨
       ∃ key, PosD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
         (.seed key) ts) ∧
      TreeRec (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
        nodes.ctors ts ∧
      NodeOf (pp.nestCtx fvsP envI.find? envI.consts) ts
        ⟨(out.getD c default).2.1.ind, (out.getD c default).2.1.lvls, (out.getD c default).2.1.ds⟩ := by
    rcases hn _ (List.contains_iff_mem.mp (haux _ ho hM)) with
      ⟨m, cs, j, cA, crest, ks, ts, hcs, hj, hcr, hd, htr, hno⟩ | ⟨key, ts, hd, htr, hno⟩
    · exact ⟨ts, Or.inl ⟨m, cs, j, cA, crest, ks, hcs, hj, hcr, hd⟩, htr, hno⟩
    · exact ⟨ts, Or.inr ⟨key, hd⟩, htr, hno⟩
  have hok : PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t := by
    rcases hsrc with ⟨m, cs, j, cA, crest, ks, -, -, -, hd⟩ | ⟨key, hd⟩
    · exact (memberCtorD_nodes hd).2 t ht
    · exact posD_nodes hd t ht
  refine ⟨ts, hsrc, htr, t, PosTree.Reached.of_forest ht, hok, ?_⟩
  simp only [NestCtx.concreteKey, NestKey.mk.injEq] at hkey
  obtain ⟨rfl, hlv, hds⟩ := hkey
  refine ⟨hM, hcn, hlv.symm, ?_⟩
  have htm : tgtMajor out c = (out.getD c default).2.1 := rfl
  rw [htm, ← hds]
  suffices ∀ l : List Expr, (∀ x ∈ l, x.fvarsBelow (ConLeche.NestCtx.hiAt
      (pp.nestCtx fvsP envI.find? envI.consts) t.occ.length)) →
      Expr.ErasedEqL (l.map (·.replaceFVars (nestHoleConst (pp.nestCtx fvsP envI.find? envI.consts)
        t.occ))) (l.map (nodeRb (pp.nestCtx fvsP envI.find? envI.consts) t.occ)) by
    simpa [Function.comp_def] using this t.key.ds (fun x hx => (hok.2.2.2.2.1 x hx).1.fvarsBelow)
  intro l hl
  induction l with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨Expr.ErasedEq.of_eq (concrete_eq_nodeRb _ _ (hl x List.mem_cons_self)),
      ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))⟩

end ConLeche.Model
