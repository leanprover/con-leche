module

public import ConLeche.Verify.Inductives.PosNodes

public section

/-!
# The positivity derivation is functional in its outputs

A field judgment's kind and normal form, and a telescope judgment's
kinds, normal forms and result, are determined by the judgment's inputs:
every rule reads the kernel's whnf of its input (a function) and the
rules are told apart by the reduct's shape (`const` by its occurrence
test, `pi` by a Π, `hole`/`frameHole` by a variable head in disjoint
ranges, `contNew`/`contHit` by a constant head — the two agree on their
outputs).  So the walked normal form of a node's constructor — which the
recursor stage reads from the run's record (K.53′, `NestCtorNf`) — is
the one of ANY derivation of that constructor.
-/

namespace ConLeche

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-- The inputs of a judgment determine its outputs (see the module
docstring), as a motive over the judgments. -/
@[expose] def PosJ.Fun (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) : PosJ → Prop
  | .field prog dep kb e k nf => ∀ k' nf' ts',
      PosD ops env ctx (.field prog dep kb e k' nf') ts' → k = k' ∧ nf = nf'
  | .tele prog base nF j cur ks nds res => ∀ ks' nds' res' ts',
      PosD ops env ctx (.tele prog base nF j cur ks' nds' res') ts' →
        ks = ks' ∧ nds = nds' ∧ res = res'
  | _ => True

private theorem ok_inj {α : Type} {a b : α} (h₁ : (Except.ok a : CheckM α) = .ok b) : a = b := by
  cases h₁; rfl

theorem posD_fun : ∀ {j : PosJ} {ts : List PosTree}, PosD ops env ctx j ts → PosJ.Fun ops env ctx j := by
  intro j ts h
  induction h with
  | @const prog dep kb e w hw hocc =>
    intro k' nf' ts' h'
    cases h' with
    | const hw' _ =>
      rw [hw] at hw'; cases ok_inj hw'; exact ⟨rfl, rfl⟩
    | pi hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | hole hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | frameHole hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | contNew hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | contHit hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ih =>
    intro k' nf' ts' h'
    cases h' with
    | const hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' _ _ hb' =>
      rw [hw] at hw'; cases ok_inj hw'
      obtain ⟨rfl, rfl⟩ := ih _ _ _ hb'
      exact ⟨rfl, rfl⟩
    | hole hw' _ hfn =>
      rw [hw] at hw'; cases ok_inj hw'; simp [Expr.getAppFn] at hfn
    | frameHole hw' _ hfn =>
      rw [hw] at hw'; cases ok_inj hw'; simp [Expr.getAppFn] at hfn
    | contNew hw' _ hfn =>
      rw [hw] at hw'; cases ok_inj hw'; simp [Expr.getAppFn] at hfn
    | contHit hw' _ hfn =>
      rw [hw] at hw'; cases ok_inj hw'; simp [Expr.getAppFn] at hfn
  | @hole prog dep kb e w i ty hw hocc hfn hlo hhi =>
    intro k' nf' ts' h'
    cases h' with
    | const hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' =>
      rw [hw] at hw'; cases ok_inj hw'; simp [Expr.getAppFn] at hfn
    | hole hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; cases hfn'; exact ⟨rfl, rfl⟩
    | frameHole hw' _ hfn' hlo' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; cases hfn'; omega
    | contNew hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | contHit hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; exact nomatch hfn'
  | @frameHole prog dep kb e w i ty h hw hocc hfn hlo hhi =>
    intro k' nf' ts' h'
    cases h' with
    | const hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' =>
      rw [hw] at hw'; cases ok_inj hw'; simp [Expr.getAppFn] at hfn
    | hole hw' _ hfn' _ hhi' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; cases hfn'; omega
    | frameHole hw' =>
      rw [hw] at hw'; cases ok_inj hw'; exact ⟨rfl, rfl⟩
    | contNew hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | contHit hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; exact nomatch hfn'
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn =>
    intro k' nf' ts' h'
    cases h' with
    | const hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' =>
      rw [hw] at hw'; cases ok_inj hw'; simp [Expr.getAppFn] at hfn
    | hole hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | frameHole hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | contNew hw' =>
      rw [hw] at hw'; cases ok_inj hw'; exact ⟨rfl, rfl⟩
    | contHit hw' =>
      rw [hw] at hw'; cases ok_inj hw'; exact ⟨rfl, rfl⟩
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn =>
    intro k' nf' ts' h'
    cases h' with
    | const hw' hocc' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hocc] at hocc'; exact nomatch hocc'
    | pi hw' =>
      rw [hw] at hw'; cases ok_inj hw'; simp [Expr.getAppFn] at hfn
    | hole hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | frameHole hw' _ hfn' =>
      rw [hw] at hw'; cases ok_inj hw'; rw [hfn] at hfn'; exact nomatch hfn'
    | contNew hw' =>
      rw [hw] at hw'; cases ok_inj hw'; exact ⟨rfl, rfl⟩
    | contHit hw' =>
      rw [hw] at hw'; cases ok_inj hw'; exact ⟨rfl, rfl⟩
  | frame => trivial
  | ctorsNil => trivial
  | ctorsCons => trivial
  | teleNil =>
    intro ks' nds' res' ts' h'
    cases h'
    exact ⟨rfl, rfl, rfl⟩
  | @teleCons prog base nF j a b bm k nd ks nds res ts ts' ha hb iha ihb =>
    intro ks' nds' res' ts'' h'
    cases h' with
    | teleCons ha' hb' =>
      obtain ⟨rfl, rfl⟩ := iha _ _ _ ha'
      obtain ⟨rfl, rfl, rfl⟩ := ihb _ _ _ _ hb'
      exact ⟨rfl, rfl, rfl⟩
  | seed => trivial

/-- **A telescope's outputs are its inputs'**: two derivations of one
telescope agree on its kinds, normal forms and result. -/
theorem posD_tele_fun {prog : List NestHole} {base nF j : Nat} {cur : Expr}
    {ks ks' : List NestFieldKind} {nds nds' : List (Expr × BinderMeta)} {res res' : Expr}
    {ts ts' : List PosTree}
    (h : PosD ops env ctx (.tele prog base nF j cur ks nds res) ts)
    (h' : PosD ops env ctx (.tele prog base nF j cur ks' nds' res') ts') :
    ks = ks' ∧ nds = nds' ∧ res = res' :=
  posD_fun h _ _ _ _ h'

/-! ## The recorded constructors (K.53′)

The run records, at every node it derives, each frame constructor's
walked normal form (`nestCtorNf`, `NestState.ctorNfs`).  `FrameRec tbl`
says a frame's constructors are recorded in `tbl` — at ANY derivation of
their telescopes, which by `posD_tele_fun` is the run's. -/

/-- **A constructor list recorded** (the frame's walk, `nestCtors`): every
constructor, instantiated as the walk instantiates it, has at every
derivation of its telescope the entry of that derivation's normal form. -/
@[expose] def CtorsRec (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (tbl : List NestCtorNf) (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
    (names : List Name) (holes : List Expr) (cs : List (ConstantVal × Nat)) : Prop :=
  ∀ x ∈ cs, ∀ crest ks nds cur ts',
    nestCrest names us ds holes (x.1.type.instantiateLevelParams x.1.levelParams us) = some crest →
    PosD ops env ctx (.tele prog hi x.2 0 crest ks nds cur) ts' →
    nestCtorNf ctx prog hi us ds x.1 nds cur ∈ tbl

/-- **A frame recorded**: its group's constructors (`groupCtors`), at the
frame's stack, recorded. -/
@[expose] def FrameRec (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (tbl : List NestCtorNf) (prog : List NestHole) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  ∀ ctors, groupCtors ctx ds.length (grp.map (·.1)) = some ctors →
    CtorsRec ops env ctx tbl ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
      (ctx.hiAt prog.length + grp.length) us ds (grp.map (·.1)) (grpHoles (ctx.hiAt prog.length) grp)
      ctors

/-- **Every node of a forest has its frame recorded.** -/
@[expose] def TreeRec (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (tbl : List NestCtorNf) (ts : List PosTree) : Prop :=
  ∀ t ∈ PosTree.forest ts, FrameRec ops env ctx tbl t.anc t.key.lvls t.key.ds t.grp

theorem CtorsRec.mono {tbl tbl' : List NestCtorNf} (hs : ∀ e ∈ tbl, e ∈ tbl')
    {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
    {names : List Name} {holes : List Expr} {cs : List (ConstantVal × Nat)}
    (h : CtorsRec ops env ctx tbl prog hi us ds names holes cs) :
    CtorsRec ops env ctx tbl' prog hi us ds names holes cs :=
  fun x hx crest ks nds cur ts' hc hd => hs _ (h x hx crest ks nds cur ts' hc hd)

theorem FrameRec.mono {tbl tbl' : List NestCtorNf} (hs : ∀ e ∈ tbl, e ∈ tbl')
    {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    (h : FrameRec ops env ctx tbl prog us ds grp) : FrameRec ops env ctx tbl' prog us ds grp :=
  fun ctors hc => (h ctors hc).mono hs

theorem TreeRec.mono {tbl tbl' : List NestCtorNf} (hs : ∀ e ∈ tbl, e ∈ tbl')
    {ts : List PosTree} (h : TreeRec ops env ctx tbl ts) : TreeRec ops env ctx tbl' ts :=
  fun t ht => (h t ht).mono hs

theorem TreeRec.nil (tbl : List NestCtorNf) : TreeRec ops env ctx tbl [] :=
  fun _ h => nomatch h

theorem TreeRec.append {tbl : List NestCtorNf} {ts ts' : List PosTree}
    (h : TreeRec ops env ctx tbl ts) (h' : TreeRec ops env ctx tbl ts') :
    TreeRec ops env ctx tbl (ts ++ ts') := fun t ht => by
  rcases PosTree.mem_forest_append.mp ht with ht | ht
  · exact h t ht
  · exact h' t ht

/-- A node recorded, with its frame's nodes. -/
theorem TreeRec.node {tbl : List NestCtorNf} {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree}
    (hf : FrameRec ops env ctx tbl anc key.lvls key.ds grp) (h : TreeRec ops env ctx tbl ts) :
    TreeRec ops env ctx tbl [.node occ anc key grp ts] := fun t ht => by
  simp only [PosTree.forest, List.append_nil] at ht
  rcases PosTree.mem_nodes.mp ht with rfl | ht
  · exact hf
  · exact h t ht

/-- A recorded frame's derived constructor telescope has its entry. -/
theorem FrameRec.entry {tbl : List NestCtorNf} {prog : List NestHole} {us : List Level}
    {ds : List Expr} {grp : List (Name × Expr)} (h : FrameRec ops env ctx tbl prog us ds grp)
    {ctors : List (ConstantVal × Nat)} (hc : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    {x : ConstantVal × Nat} (hx : x ∈ ctors) {crest : Expr} {ks : List NestFieldKind}
    {nds : List (Expr × BinderMeta)} {cur : Expr} {ts' : List PosTree}
    (hcr : nestCrest (grp.map (·.1)) us ds (grpHoles (ctx.hiAt prog.length) grp)
      (x.1.type.instantiateLevelParams x.1.levelParams us) = some crest)
    (hd : PosD ops env ctx (.tele ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
      (ctx.hiAt prog.length + grp.length) x.2 0 crest ks nds cur) ts') :
    nestCtorNf ctx ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
      (ctx.hiAt prog.length + grp.length) us ds x.1 nds cur ∈ tbl :=
  h ctors hc x hx crest ks nds cur ts' hcr hd

/-- **A cached instantiation, derived and recorded**: its frame, at the
EMPTY frame stack, with the key's container in the frame's group, and
the frame and every node of its derivation recorded in `tbl`. -/
@[expose] def KeyDR (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (tbl : List NestCtorNf)
    (key : NestKey) : Prop :=
  ∃ grp ts, PosD ops env ctx (.frame [] key.lvls key.ds grp) ts ∧ key.cname ∈ grp.map (·.1) ∧
    FrameRec ops env ctx tbl [] key.lvls key.ds grp ∧ TreeRec ops env ctx tbl ts

theorem KeyDR.mono {tbl tbl' : List NestCtorNf} (hs : ∀ e ∈ tbl, e ∈ tbl') {key : NestKey}
    (h : KeyDR ops env ctx tbl key) : KeyDR ops env ctx tbl' key := by
  obtain ⟨grp, ts, hd, hm, hf, ht⟩ := h
  exact ⟨grp, ts, hd, hm, hf.mono hs, ht.mono hs⟩

end ConLeche
