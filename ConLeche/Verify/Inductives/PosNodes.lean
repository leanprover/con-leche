module

public import ConLeche.Verify.Inductives.PosDeriv

public section

/-!
# The positivity derivation's nodes (lane POSDERIV; coordinator's ruling on NESTIND's F13)

The derivation `PosD` is indexed by the forest of its NODES (`PosTree`):
every container instance it meets, with its instantiation, the frames
at its occurrence (its ancestor chain), the frames its frame is derived
under, its reached group and the nodes of its frame (its children).
The nested recursor's classes are these nodes (NESTIND F13: one depth
per class cannot order a class visited at two nesting depths; the
visits' NESTING can).

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
  `Model/Inductives/PosDerivMono.lean`); at a node below every frame
  hole, `keyPos_of_keyD` reads it at the block's own depth.

* the TIE of a field to its node (`posD_field_node`): a field of a
  container kind has exactly one root, keyed by the head application its
  whnf spine (`WhnfSpine`) reaches; with `posD_tele_open` (a telescope's
  fields, their nodes among its own) and `posD_frame_teles` (a frame's
  constructors, their nodes among the frame's), a call's callee on a
  container field of a node's constructor is one of the node's kids, and
  on a member constructor's container field one of the roots.

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
  | frame _ _ _ _ _ _ _ _ ih => exact ih
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

/-- **What a node is**: its frame derived with its children as that
derivation's forest, its container in its group, its children occurring
at its frame's stack, that stack well scoped, and either walked where it
occurs (the group's head, `anc = occ`) or a cache hit (parameters below
every frame hole). -/
@[expose] def PosNodeOk (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (t : PosTree) :
    Prop :=
  PosD ops env ctx (.frame t.anc t.key.lvls t.key.ds t.grp) t.kids ∧
  t.key.cname ∈ t.grp.map (·.1) ∧
  (∀ k ∈ t.kids,
    k.occ = (grpNews t.key.lvls t.key.ds (ctx.hiAt t.anc.length) t.grp).reverse ++ t.anc) ∧
  ProgScoped ctx t.anc ∧
  ((t.anc = t.occ ∧ (t.grp.headD default).1 = t.key.cname) ∨
    (∀ x ∈ t.key.ds, x.fvarB ≤ ctx.hiAt 0))

/-- **Every node of a derivation's forest is a node** (`PosNodeOk`). -/
theorem posD_nodes : ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts →
    ∀ t ∈ PosTree.forest ts, PosNodeOk ops env ctx t := by
  intro j ts h
  induction h with
  | const => intro t ht; exact nomatch ht
  | pi _ _ _ _ ih => exact ih
  | hole => intro t ht; exact nomatch ht
  | frameHole => intro t ht; exact nomatch ht
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds hnI
      hhead hsc hfr ih =>
    intro t ht
    simp only [PosTree.forest, List.append_nil] at ht
    rcases PosTree.mem_nodes.mp ht with rfl | ht
    · refine ⟨hfr, ?_, fun k hk => posD_top hfr k hk, hsc, Or.inl ⟨rfl, ?_⟩⟩
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
  | @contHit prog prog' dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds
      hnI hsc hmem hfr ih =>
    intro t ht
    simp only [PosTree.forest, List.append_nil] at ht
    rcases PosTree.mem_nodes.mp ht with rfl | ht
    · exact ⟨hfr, hmem, fun k hk => posD_top hfr k hk, hsc, Or.inr fun x hx => (hds x hx).2⟩
    · exact ih t ht
  | frame _ _ _ _ _ _ _ _ ih => exact ih
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

/-- **A member constructor's nodes**: its roots occur at no frame, and
every node of its forest is a node. -/
theorem memberCtorD_nodes {nF : Nat} {crest : Expr} {ks : List PosKind} {tyN : Expr}
    {ts : List PosTree} (h : MemberCtorD ops env ctx nF crest ks tyN ts) :
    (∀ t ∈ ts, t.occ = []) ∧ ∀ t ∈ PosTree.forest ts, PosNodeOk ops env ctx t := by
  obtain ⟨nds, cur, ht, -⟩ := h
  exact ⟨fun t htt => posD_top ht t htt, posD_nodes ht⟩

/-! ## The tie of an instantiation to a node

The recursor stage's majors and calls read a field's type; the
derivation's node for that field carries the instantiation the walk
met there.  `WhnfSpine` is the walk's path to it (whnf, then under each
Π-binder), `posD_field_node` the tie: a field of a container kind has
exactly one root, occurring at the field's frames, keyed by the head
application its whnf spine reaches; every other field has none. -/

/-- **The walk's whnf spine**: `e` at depth `dep` reduces (the kernel's
whnf, at each step) through Π-binders, each opened at its depth, to `w`
at depth `dep'`. -/
inductive WhnfSpine (ops : CheckerOps CheckM) (env : Env) : Nat → Expr → Nat → Expr → Prop where
  | here {dep : Nat} {e w : Expr} (hw : ops.whnf env dep e = .ok w) : WhnfSpine ops env dep e dep w
  | pi {dep dep' : Nat} {e a b w : Expr} {bm : BinderMeta}
      (hw : ops.whnf env dep e = .ok (.forallE a b bm))
      (hb : WhnfSpine ops env (dep + 1) (b.instantiate1 (.fvar dep a)) dep' w) :
      WhnfSpine ops env dep e dep' w

/-- **A node keyed at an instantiation** occurs in a forest. -/
@[expose] def PosTree.Keyed (ts : List PosTree) (key : NestKey) : Prop :=
  ∃ t ∈ PosTree.forest ts, t.key = key

/-- **THE TIE (a field to its node)**: a derived field of a flat or
in-progress kind has no node; one of a container kind has exactly one
root, occurring at the field's frames, whose key is the head application
its whnf spine reaches (`C.{lvls}` applied to the key's parameters and
then its indices). -/
theorem posD_field_node : ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts → match j with
    | .field prog dep _ e k _ => ((k.flat = true ∨ k = .inProgress) ∧ ts = []) ∨
        ∃ t, ts = [t] ∧ t.occ = prog ∧ (∃ r, k = .nested r) ∧ ∃ dep' w nPc,
          WhnfSpine ops env dep e dep' w ∧ w.getAppFn = .const t.key.cname t.key.lvls ∧
          t.key.ds = w.getAppArgs.take nPc ∧ ∃ L, nestContainer ctx t.key.cname = some (nPc, L)
    | _ => True := by
  intro j ts h
  induction h with
  | const => exact Or.inl ⟨Or.inl rfl, rfl⟩
  | @pi prog dep kb e a b bm k nb ts hw _ _ _ ih =>
    rcases ih with ⟨hk, rfl⟩ | ⟨t, rfl, hocc, hkn, dep', w, nPc, hsp, hfn, hds, hC⟩
    · exact Or.inl ⟨hk, rfl⟩
    · exact Or.inr ⟨t, rfl, hocc, hkn, dep', w, nPc, .pi hw hsp, hfn, hds, hC⟩
  | hole =>
    refine Or.inl ⟨Or.inl ?_, rfl⟩
    split <;> rfl
  | frameHole => exact Or.inl ⟨Or.inr rfl, rfl⟩
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hC =>
    exact Or.inr ⟨_, rfl, rfl, ⟨_, rfl⟩, dep, w, nPc, .here hw, hfn, rfl, _, hC⟩
  | @contHit prog prog' dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hC =>
    exact Or.inr ⟨_, rfl, rfl, ⟨_, rfl⟩, dep, w, nPc, .here hw, hfn, rfl, _, hC⟩
  | _ => trivial

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

/-- **A frame's constructors, each derived**: the reached group's
constructors (`groupCtors`), each instantiated at the key with the group
abstracted, its telescope derived at the frame's stack, its nodes among
the frame's. -/
theorem posD_frame_teles : ∀ {J : PosJ} {ts : List PosTree}, PosD ops env ctx J ts → match J with
    | .ctors prog hi us ds sub cs => ∀ x ∈ cs, ∃ crest ks nds cur ts',
        instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
          = some crest ∧
        PosD ops env ctx (.tele prog hi x.2 0 crest ks nds cur) ts' ∧ ∀ t ∈ ts', t ∈ ts
    | .frame prog us ds grp => ∃ ctors, groupCtors ctx ds.length (grp.map (·.1)) = some ctors ∧
        ∀ x ∈ ctors, ∃ crest ks nds cur ts',
          instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts
            (grpSub us (ctx.hiAt prog.length) grp)) = some crest ∧
          PosD ops env ctx (.tele ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
            (ctx.hiAt prog.length + grp.length) x.2 0 crest ks nds cur) ts' ∧ ∀ t ∈ ts', t ∈ ts
    | _ => True := by
  intro J ts h
  induction h with
  | frame _ _ _ _ _ _ hctors _ ih => exact ⟨_, hctors, ih⟩
  | ctorsNil => intro x hx; exact nomatch hx
  | @ctorsCons prog hi us ds sub cv nF cs crest ty sv ks nds cur ts ts' _ hcrest _ _ htele _ _ _ _ _
      ihrest =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨crest, ks, nds, cur, ts, hcrest, htele, fun t ht => List.mem_append_left _ ht⟩
    · obtain ⟨c', k', n', cu', ts'', h1, h2, h3⟩ := ihrest x hx
      exact ⟨c', k', n', cu', ts'', h1, h2, fun t ht => List.mem_append_right _ (h3 t ht)⟩
  | _ => trivial

/-! ## The reached-major tie (coordinator's ruling (a), 2026-09-25)

The nested recursor's classes are the block's members and the nodes
REACHED from them by calls (`PosTree.Reached`: a member constructor's
roots, and every kid of a reached node).  A call recurses on a field; the
field's tie (`FieldTie`) says what the callee's class can be: a field of a
flat kind is a member occurrence (or none), one of the in-progress kind
an enclosing frame's hole (the node's own group or an ancestor's), and one
of a container kind has its NODE — at a member constructor a root
(`memberCtorD_field_roots`), at a reached node's constructor one of its
kids (`PosNodeOk.ctor_field_kids`), keyed by the head application its
whnf spine reaches.  So every container a reached class calls on is a
reached node (`PosTree.Reached.ctor_field_kids`), a node in the sense of
`PosNodeOk` (`PosTree.Reached.nodeOk`), strictly lower than its caller
(`PosTree.height_kid`).  Outside majors no class reaches (official's
syntactic auxiliary types the walk never visits, `corner_posderiv_major_
{delta,group}`) are not classes: the recursor lane inducts on them at
the true frame after the reached classes.

The rule side supplies the other half, the callee's major against the
field (the call's typing, `targetCallOk`/(D)); the constructors here are
the frame's group constructors in the representation (D) reads
(`instPisWith ds (… .replaceConsts (grpSub …))`). -/

/-- **A field's tie**: a flat or in-progress kind (no node), or a
container kind with its node among `ts`, occurring at the field's
frames `prog`, keyed by the head application its whnf spine reaches
(`C.{lvls}` applied to the key's parameters, then indices). -/
@[expose] def FieldTie (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (prog : List NestHole) (dep : Nat) (e : Expr) (k : PosKind) (ts : List PosTree) : Prop :=
  (k.flat = true ∨ k = .inProgress) ∨
  ∃ t ∈ ts, t.occ = prog ∧ (∃ r, k = .nested r) ∧ ∃ dep' w nPc,
    WhnfSpine ops env dep e dep' w ∧ w.getAppFn = .const t.key.cname t.key.lvls ∧
    t.key.ds = w.getAppArgs.take nPc ∧ ∃ L, nestContainer ctx t.key.cname = some (nPc, L)

/-- A derived field is tied, to any forest containing its roots. -/
theorem posD_field_tie {prog : List NestHole} {dep kb : Nat} {e : Expr} {k : PosKind}
    {nf : Expr} {ts ts' : List PosTree} (h : PosD ops env ctx (.field prog dep kb e k nf) ts)
    (hsub : ∀ t ∈ ts, t ∈ ts') : FieldTie ops env ctx prog dep e k ts' := by
  rcases posD_field_node h with ⟨hk, -⟩ | ⟨t, rfl, hocc, hkn, rest⟩
  · exact Or.inl hk
  · exact Or.inr ⟨t, hsub t (List.mem_singleton_self t), hocc, hkn, rest⟩

/-- **A derived telescope's fields, tied** (to any forest containing the
telescope's nodes). -/
theorem posD_tele_ties {prog : List NestHole} {base nF j : Nat} {cur : Expr}
    {ks : List PosKind} {nds : List (Expr × BinderMeta)} {res : Expr} {ts ts' : List PosTree}
    (h : PosD ops env ctx (.tele prog base nF j cur ks nds res) ts)
    (hsub : ∀ t ∈ ts, t ∈ ts') :
    ∃ xs, openPisAtFvars nF cur (base + j) = some (xs, res) ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k, ks[i]? = some k ∧
        FieldTie ops env ctx prog (base + j + i) x.fvarTypeD k ts' := by
  obtain ⟨-, -, xs, hop, hall⟩ := posD_tele_open h
  refine ⟨xs, hop, fun i x hx => ?_⟩
  obtain ⟨k, nd, ts'', hk, -, hf, hsub'⟩ := hall i x hx
  exact ⟨k, hk, posD_field_tie hf fun t ht => hsub t (hsub' t ht)⟩

/-- **A member constructor's fields, tied to its ROOTS** (at no frame,
the telescope opened at the block's own depth). -/
theorem memberCtorD_field_roots {nF : Nat} {crest : Expr} {ks : List PosKind} {tyN : Expr}
    {ts : List PosTree} (h : MemberCtorD ops env ctx nF crest ks tyN ts) :
    ∃ xs cur, openPisAtFvars nF crest (ctx.hiAt 0) = some (xs, cur) ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k, ks[i]? = some k ∧
        FieldTie ops env ctx [] (ctx.hiAt 0 + i) x.fvarTypeD k ts := by
  obtain ⟨nds, cur, ht, -⟩ := h
  obtain ⟨xs, hop, hall⟩ := posD_tele_ties ht fun t h => h
  exact ⟨xs, cur, by simpa using hop, fun i x hx => by simpa using hall i x hx⟩

/-- **A node's constructors' fields, tied to its KIDS**: the node's frame
constructors (its group's, `groupCtors`), each instantiated at the key
with the group abstracted to its holes, opened after the group's holes;
every field is tied at the node's frame stack, a container field to one
of the node's kids. -/
theorem PosNodeOk.ctor_field_kids {t : PosTree} (ht : PosNodeOk ops env ctx t) :
    ∃ ctors, groupCtors ctx t.key.ds.length (t.grp.map (·.1)) = some ctors ∧
      ∀ x ∈ ctors, ∃ (crest cur : Expr) (xs : List Expr) (ks : List PosKind),
        instPisWith t.key.ds ((x.1.type.instantiateLevelParams x.1.levelParams t.key.lvls).replaceConsts
          (grpSub t.key.lvls (ctx.hiAt t.anc.length) t.grp)) = some crest ∧
        openPisAtFvars x.2 crest (ctx.hiAt t.anc.length + t.grp.length) = some (xs, cur) ∧
        ∀ (i : Nat) (f : Expr), xs[i]? = some f → ∃ k : PosKind, ks[i]? = some k ∧
          FieldTie ops env ctx
            ((grpNews t.key.lvls t.key.ds (ctx.hiAt t.anc.length) t.grp).reverse ++ t.anc)
            (ctx.hiAt t.anc.length + t.grp.length + i) f.fvarTypeD k t.kids := by
  obtain ⟨ctors, hc, hall⟩ := posD_frame_teles ht.1
  refine ⟨ctors, hc, fun x hx => ?_⟩
  obtain ⟨crest, ks, nds, cur, ts', hcr, htele, hsub⟩ := hall x hx
  obtain ⟨xs, hop, hties⟩ := posD_tele_ties htele hsub
  exact ⟨crest, cur, xs, ks, hcr, by simpa using hop, fun i f hf => by simpa using hties i f hf⟩

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

/-- **THE REACHED-MAJOR TIE**: at a reached node, every field of its
frame's constructors is tied (`FieldTie`) at the node's frame stack; a
container field's node is a kid, itself REACHED, a node, and lower than
its caller.  With `memberCtorD_field_roots` (a member constructor's
container fields: roots, hence reached) this is: every container a
reached class calls on is a reached node. -/
theorem PosTree.Reached.ctor_field_kids {ts : List PosTree}
    (hroots : ∀ r ∈ ts, PosNodeOk ops env ctx r) {t : PosTree} (h : PosTree.Reached ts t) :
    PosNodeOk ops env ctx t ∧
    ∃ ctors, groupCtors ctx t.key.ds.length (t.grp.map (·.1)) = some ctors ∧
      ∀ x ∈ ctors, ∃ (crest cur : Expr) (xs : List Expr) (ks : List PosKind),
        instPisWith t.key.ds ((x.1.type.instantiateLevelParams x.1.levelParams t.key.lvls).replaceConsts
          (grpSub t.key.lvls (ctx.hiAt t.anc.length) t.grp)) = some crest ∧
        openPisAtFvars x.2 crest (ctx.hiAt t.anc.length + t.grp.length) = some (xs, cur) ∧
        ∀ (i : Nat) (f : Expr), xs[i]? = some f → ∃ k : PosKind, ks[i]? = some k ∧
          ((k.flat = true ∨ k = .inProgress) ∨
          ∃ u ∈ t.kids, PosTree.Reached ts u ∧ PosNodeOk ops env ctx u ∧
            u.height < t.height ∧
            u.occ = (grpNews t.key.lvls t.key.ds (ctx.hiAt t.anc.length) t.grp).reverse ++ t.anc ∧
            (∃ r, k = .nested r) ∧ ∃ dep' w nPc,
            WhnfSpine ops env (ctx.hiAt t.anc.length + t.grp.length + i) f.fvarTypeD dep' w ∧
            w.getAppFn = .const u.key.cname u.key.lvls ∧
            u.key.ds = w.getAppArgs.take nPc ∧ ∃ L, nestContainer ctx u.key.cname = some (nPc, L)) := by
  have hok := PosTree.Reached.nodeOk hroots h
  obtain ⟨ctors, hc, hall⟩ := PosNodeOk.ctor_field_kids hok
  refine ⟨hok, ctors, hc, fun x hx => ?_⟩
  obtain ⟨crest, cur, xs, ks, hcr, hop, hties⟩ := hall x hx
  refine ⟨crest, cur, xs, ks, hcr, hop, fun i f hf => ?_⟩
  obtain ⟨k, hk, hti⟩ := hties i f hf
  refine ⟨k, hk, ?_⟩
  rcases hti with hflat | ⟨u, hu, rest⟩
  · exact Or.inl hflat
  · exact Or.inr ⟨u, hu, .kid h hu, PosTree.Reached.nodeOk hroots (.kid h hu),
      PosTree.height_kid hu, rest⟩

end Nodes

end ConLeche
