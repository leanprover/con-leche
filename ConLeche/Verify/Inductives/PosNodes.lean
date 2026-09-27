module

public import ConLeche.Verify.Inductives.PosDeriv

public section

/-!
# The positivity derivation's nodes

The derivation `PosD` is indexed by the forest of its NODES (`PosTree`):
every container instance it meets, with its instantiation, the frames
at its occurrence (its ancestor chain), the frames its frame is derived
under, its reached group and the nodes of its frame (its children).
The nested recursor's classes are these nodes (one depth per class
cannot order a class visited at two nesting depths; the visits'
NESTING can).

This file states what the index means:

* `PosTree.nodes`/`PosTree.forest`: every node of a tree / a forest,
  the tree first (preorder) — a finite list;
* `PosTree.height`: the tree order is well founded; a child's height is
  below its parent's (`PosTree.height_kid`);
* `posD_top` — the forest's roots OCCUR at the judgment's frames: at a
  field, telescope or constructor list derived under `prog`, every root
  occurs at `prog`; at a frame, at the frame's own stack
  (`grpNews … ++ prog`);
* `posD_nodes` — every node of a derivation's forest is a NODE
  (`PosNodeOk`): its frame is derived with its children as that
  derivation's forest, its container is in its group, its children occur
  at its frame's stack, that stack is well scoped, and either it was
  walked where it occurs (its container the group's head) or it is a
  cache hit (its parameters below every frame hole);
* the semantics of a node is its frame's (`posD_mono`, `FrameMono`,
  `Model/Inductives/PosDerivMono.lean`).

* `posD_tele_open` — a derived telescope, opened: its fields, their
  nodes among its own.

The tie of a recursor major (and a call's callee) to a node is the
node's `key` in the WALK's representation: `C.{lvls} ds`, the
parameters `ds` over the canonical parameter variables `ctx.params`
(`fvar 0 … fvar (nP - 1)`), member `t` as the hole `fvar (nP + t)`, and
the `i`-th hole of the frame stack `occ` (innermost last in
`occ.reverse`) as `fvar (ctx.hiAt 0 + i)`.
-/

namespace ConLeche

/-- The frames at a node's occurrence (its ancestor chain). -/
@[expose] def PosTree.occ : PosTree → List NestHole
  | .node occ _ _ _ _ => occ

/-- The frames the node's own frame is derived under. -/
@[expose] def PosTree.anc : PosTree → List NestHole
  | .node _ anc _ _ _ => anc

/-- The node's instantiation. -/
@[expose] def PosTree.key : PosTree → NestKey
  | .node _ _ key _ _ => key

/-- The node's reached group. -/
@[expose] def PosTree.grp : PosTree → List (Name × Expr)
  | .node _ _ _ grp _ => grp

/-- The nodes of the node's frame. -/
@[expose] def PosTree.kids : PosTree → List PosTree
  | .node _ _ _ _ kids => kids

mutual
/-- Every node of a tree, the root first. -/
@[expose] def PosTree.nodes : PosTree → List PosTree
  | t@(.node _ _ _ _ kids) => t :: PosTree.forest kids
/-- Every node of a forest. -/
@[expose] def PosTree.forest : List PosTree → List PosTree
  | [] => []
  | t :: ts => t.nodes ++ PosTree.forest ts
end

mutual
/-- A tree's height (a leaf node has height 1). -/
@[expose] def PosTree.height : PosTree → Nat
  | .node _ _ _ _ kids => PosTree.forestHeight kids + 1
/-- A forest's height (the empty forest's is 0). -/
@[expose] def PosTree.forestHeight : List PosTree → Nat
  | [] => 0
  | t :: ts => max t.height (PosTree.forestHeight ts)
end

theorem PosTree.height_le_forestHeight : ∀ {ts : List PosTree} {t : PosTree}, t ∈ ts →
    t.height ≤ PosTree.forestHeight ts
  | _ :: _, _, .head _ => by simp only [PosTree.forestHeight]; omega
  | _ :: ts, t, .tail _ h => by
    have := PosTree.height_le_forestHeight (ts := ts) h
    simp only [PosTree.forestHeight]; omega

/-- **The tree order is well founded**: a child is lower than its parent. -/
theorem PosTree.height_kid {t k : PosTree} (hk : k ∈ t.kids) : k.height < t.height := by
  cases t with
  | node occ anc key grp kids =>
    have := PosTree.height_le_forestHeight (ts := kids) hk
    simp only [PosTree.height]; omega

theorem PosTree.mem_forest_append {ts ts' : List PosTree} {t : PosTree} :
    t ∈ PosTree.forest (ts ++ ts') ↔ t ∈ PosTree.forest ts ∨ t ∈ PosTree.forest ts' := by
  induction ts with
  | nil => simp [PosTree.forest]
  | cons x xs ih => simp [PosTree.forest, ih, or_assoc]

theorem PosTree.mem_nodes {t u : PosTree} :
    u ∈ t.nodes ↔ u = t ∨ u ∈ PosTree.forest t.kids := by
  cases t with
  | node occ anc key grp kids => simp [PosTree.nodes, PosTree.kids]

theorem PosTree.mem_forest_cons {t : PosTree} {ts : List PosTree} {u : PosTree} :
    u ∈ PosTree.forest (t :: ts) ↔ u ∈ t.nodes ∨ u ∈ PosTree.forest ts := by
  simp [PosTree.forest]

section Nodes

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-- The frames a judgment's roots occur at. -/
@[expose] def PosJ.rootOcc (ctx : NestCtx) : PosJ → List NestHole
  | .field prog .. => prog
  | .tele prog .. => prog
  | .ctors prog .. => prog
  | .frame prog us ds grp => (grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog
  | .seed _ => []

/-- **The roots occur at the judgment's frames.** -/
theorem posD_top : ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts →
    ∀ t ∈ ts, t.occ = j.rootOcc ctx := by
  intro j ts h
  induction h with
  | const => intro t ht; exact nomatch ht
  | pi _ _ _ _ ih => exact ih
  | hole => intro t ht; exact nomatch ht
  | frameHole => intro t ht; exact nomatch ht
  | contNew =>
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht; rfl
  | contHit =>
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht; rfl
  | frame _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | ctorsNil => intro t ht; exact nomatch ht
  | ctorsCons _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih₁ t ht
    · exact ih₂ t ht
  | teleNil => intro t ht; exact nomatch ht
  | teleCons _ _ ih₁ ih₂ =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih₁ t ht
    · exact ih₂ t ht
  | seed =>
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht; rfl

/-- **What a node is**: its frame derived with its children as that
derivation's forest, its container in its group, its children occurring
at its frame's stack, that stack well scoped, its key's parameters well
scoped at its occurrence (and closed), and either walked where it occurs
(the group's head, `anc = occ`) or — parameters below every frame hole —
derived at the EMPTY stack (`anc = []`; so every node's stack is its
ancestors' groups, every hole has an
owner node above it). -/
@[expose] def PosNodeOk (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (t : PosTree) :
    Prop :=
  PosD ops env ctx (.frame t.anc t.key.lvls t.key.ds t.grp) t.kids ∧
  t.key.cname ∈ t.grp.map (·.1) ∧
  (∀ k ∈ t.kids,
    k.occ = (grpNews t.key.lvls t.key.ds (ctx.hiAt t.anc.length) t.grp).reverse ++ t.anc) ∧
  ProgScoped ctx t.anc ∧
  (∀ x ∈ t.key.ds, Expr.WScoped (ctx.hiAt t.occ.length) x ∧ x.bvarB = 0) ∧
  ((t.anc = t.occ ∧ (t.grp.headD default).1 = t.key.cname) ∨
    (t.anc = [] ∧ ∀ x ∈ t.key.ds, x.fvarB ≤ ctx.hiAt 0 ∧ Expr.WScoped (ctx.hiAt 0) x))

/-- The empty frame stack is well scoped. -/
theorem ProgScoped.nil : ProgScoped ctx [] := fun i hk h => by simp at h

/-- **Every node of a derivation's forest is a node** (`PosNodeOk`). -/
theorem posD_nodes : ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts →
    ∀ t ∈ PosTree.forest ts, PosNodeOk ops env ctx t := by
  intro j ts h
  induction h with
  | const => intro t ht; exact nomatch ht
  | pi _ _ _ _ ih => exact ih
  | hole => intro t ht; exact nomatch ht
  | frameHole => intro t ht; exact nomatch ht
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds hdsw
      hnI hhead hsc hfr ih =>
    intro t ht
    simp only [PosTree.forest, List.append_nil] at ht
    rcases PosTree.mem_nodes.mp ht with rfl | ht
    · refine ⟨hfr, ?_, fun k hk => posD_top hfr k hk, hsc,
        fun x hx => ⟨hdsw x hx, (hds x hx).1⟩, Or.inl ⟨rfl, ?_⟩⟩
      · cases grp with
        | nil => simp at hhead
        | cons p ps =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          simp [PosTree.grp, PosTree.key, hhead]
      · cases grp with
        | nil => simp at hhead
        | cons p ps =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          simp [PosTree.grp, PosTree.key, hhead]
    · exact ih t ht
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds
      hdsw hnI hmem hfr ih =>
    intro t ht
    simp only [PosTree.forest, List.append_nil] at ht
    rcases PosTree.mem_nodes.mp ht with rfl | ht
    · exact ⟨hfr, hmem, fun k hk => posD_top hfr k hk, ProgScoped.nil,
        fun x hx => ⟨Expr.WScoped.mono (by simp [NestCtx.hiAt]) (hdsw x hx), (hds x hx).1⟩,
        Or.inr ⟨rfl, fun x hx => ⟨(hds x hx).2, hdsw x hx⟩⟩⟩
    · exact ih t ht
  | frame _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | ctorsNil => intro t ht; exact nomatch ht
  | ctorsCons _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    intro t ht
    rcases PosTree.mem_forest_append.mp ht with ht | ht
    · exact ih₁ t ht
    · exact ih₂ t ht
  | teleNil => intro t ht; exact nomatch ht
  | teleCons _ _ ih₁ ih₂ =>
    intro t ht
    rcases PosTree.mem_forest_append.mp ht with ht | ht
    · exact ih₁ t ht
    · exact ih₂ t ht
  | @seed n us ds L grp ts hnm hquot hC hds hdsw hleaf hmem hfr ih =>
    intro t ht
    simp only [PosTree.forest, List.append_nil] at ht
    rcases PosTree.mem_nodes.mp ht with rfl | ht
    · exact ⟨hfr, hmem, fun k hk => posD_top hfr k hk, ProgScoped.nil,
        fun x hx => ⟨hdsw x hx, (hds x hx).1⟩,
        Or.inr ⟨rfl, fun x hx => ⟨(hds x hx).2, hdsw x hx⟩⟩⟩
    · exact ih t ht

/-- **A member constructor's nodes**: its roots occur at no frame, and
every node of its forest is a node. -/
theorem memberCtorD_nodes {nF : Nat} {crest : Expr} {ks : List PosKind} {tyN : Expr}
    {ts : List PosTree} (h : MemberCtorD ops env ctx nF crest ks tyN ts) :
    (∀ t ∈ ts, t.occ = []) ∧ ∀ t ∈ PosTree.forest ts, PosNodeOk ops env ctx t := by
  obtain ⟨nds, cur, ht, -⟩ := h
  exact ⟨fun t htt => posD_top ht t htt, posD_nodes ht⟩

/-- **A seed's parameters' leaves are the canonical variables'.** -/
theorem posD_seed_leaves {key : NestKey} {ts : List PosTree}
    (h : PosD ops env ctx (.seed key) ts) : ∀ x ∈ key.ds, SeedLeaves ctx x := by
  cases h with
  | seed _ _ _ _ _ hleaf _ _ => exact hleaf

/-- **A seed's nodes**: its root occurs at no frame, and every node of its
forest is a node. -/
theorem seedD_nodes {key : NestKey} {ts : List PosTree} (h : PosD ops env ctx (.seed key) ts) :
    (∀ t ∈ ts, t.occ = []) ∧ ∀ t ∈ PosTree.forest ts, PosNodeOk ops env ctx t :=
  ⟨fun t htt => posD_top h t htt, posD_nodes h⟩

/-! ## A derived telescope, opened -/

/-- **A derived telescope, opened**: one kind and one output per field,
the telescope opening onto its result at its base depth, and each opened
domain derived as a field at its depth, its nodes among the telescope's. -/
theorem posD_tele_open : ∀ {J : PosJ} {ts : List PosTree}, PosD ops env ctx J ts → match J with
    | .tele prog base nF j cur ks nds res =>
      ks.length = nF ∧ nds.length = nF ∧ ∃ xs, openPisAtFvars nF cur (base + j) = some (xs, res) ∧
        ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd ts', ks[i]? = some k ∧
          nds[i]?.map (·.1) = some nd ∧
          PosD ops env ctx (.field prog (base + j + i) 0 x.fvarTypeD k nd) ts' ∧ ∀ t ∈ ts', t ∈ ts
    | _ => True := by
  intro J ts h
  induction h with
  | teleNil => exact ⟨rfl, rfl, [], by simp [openPisAtFvars], fun _ _ hx => nomatch hx⟩
  | @teleCons prog base nF j a b bm k nd ks nds res ts ts' ha _ _ ihb =>
    obtain ⟨hkl, hnl, xs, hop, hall⟩ := ihb
    refine ⟨by simp [hkl], by simp [hnl], .fvar (base + j) a :: xs, ?_, fun i x hx => ?_⟩
    · simp only [openPisAtFvars]
      rw [show base + j + 1 = base + (j + 1) by omega, hop]
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨k, nd, ts, rfl, rfl, by simpa [Expr.fvarTypeD] using ha,
          fun t ht => List.mem_append_left _ ht⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨k', nd', ts'', h1, h2, h3, h4⟩ := hall i x hx
        refine ⟨k', nd', ts'', by simpa using h1, by simpa using h2, ?_,
          fun t ht => List.mem_append_right _ (h4 t ht)⟩
        rw [show base + j + (i + 1) = base + (j + 1) + i by omega]
        exact h3
  | _ => trivial

/-! ## The reached-major tie

The nested recursor's classes are the block's members and the nodes
REACHED from them by calls (`PosTree.Reached`: a member constructor's
or a seed's roots, and every kid of a reached node); a reached node is a
node in the sense of `PosNodeOk` (`PosTree.Reached.nodeOk`), strictly
lower than its caller (`PosTree.height_kid`).  Outside majors no member
constructor reaches (official's auxiliary types whnf erases, a group mate
nothing calls: `corner_posderiv_major_{delta,group}`) are seeds' roots or
unreached: the recursor stage inducts on them at the true frame after the
reached classes. -/

/-- **The nodes reached from the roots `ts`**: a root, or a kid of a
reached node. -/
inductive PosTree.Reached (ts : List PosTree) : PosTree → Prop where
  | root {t : PosTree} : t ∈ ts → PosTree.Reached ts t
  | kid {t k : PosTree} : PosTree.Reached ts t → k ∈ t.kids → PosTree.Reached ts k

theorem PosTree.mem_forest_of_mem {ts : List PosTree} {t : PosTree} (h : t ∈ ts) :
    t ∈ PosTree.forest ts := by
  induction ts with
  | nil => exact nomatch h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact PosTree.mem_forest_cons.mpr (Or.inl (PosTree.mem_nodes.mpr (Or.inl rfl)))
    · exact PosTree.mem_forest_cons.mpr (Or.inr (ih h))

/-- **Every reached node is a node** (`PosNodeOk`), given the roots are. -/
theorem PosTree.Reached.nodeOk {ts : List PosTree}
    (hroots : ∀ r ∈ ts, PosNodeOk ops env ctx r) {t : PosTree} (h : PosTree.Reached ts t) :
    PosNodeOk ops env ctx t := by
  induction h with
  | root hr => exact hroots _ hr
  | kid _ hk ih => exact posD_nodes ih.1 _ (PosTree.mem_forest_of_mem hk)

/-- **Every hole of a reached node's stack has an OWNER**:
each entry of `t.occ` is a group entry (`grpNews`) of a reached node `u`,
strictly higher than `t` — its ancestor whose frame introduced the hole.
Holds because every node's stack is its ancestors' groups: a walked node
is derived where it occurs, a hole-free one at the empty stack. -/
theorem PosTree.Reached.occ_owners {ts : List PosTree}
    (hroots : ∀ r ∈ ts, PosNodeOk ops env ctx r) (hocc0 : ∀ r ∈ ts, r.occ = [])
    {t : PosTree} (h : PosTree.Reached ts t) :
    ∀ hk ∈ t.occ, ∃ u, PosTree.Reached ts u ∧ PosNodeOk ops env ctx u ∧ t.height < u.height ∧
      hk ∈ grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp := by
  induction h with
  | root hr => intro hk hkm; rw [hocc0 _ hr] at hkm; exact nomatch hkm
  | @kid u k hu hk ih =>
    intro hh hhm
    have hok := PosTree.Reached.nodeOk hroots hu
    rw [hok.2.2.1 k hk, List.mem_append, List.mem_reverse] at hhm
    have hlt := PosTree.height_kid hk
    rcases hhm with hhm | hhm
    · exact ⟨u, hu, hok, hlt, hhm⟩
    · rcases hok.2.2.2.2.2 with ⟨hanc, -⟩ | ⟨hanc, -⟩
      · rw [hanc] at hhm
        obtain ⟨v, hv, hvok, hvlt, hvm⟩ := ih hh hhm
        exact ⟨v, hv, hvok, Nat.lt_trans hlt hvlt, hvm⟩
      · rw [hanc] at hhm; exact nomatch hhm

end Nodes

end ConLeche
