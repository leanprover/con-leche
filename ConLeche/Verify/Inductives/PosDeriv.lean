module

public import ConLeche.Kernel.Inductives.FieldNf
public import ConLeche.Verify.Shift

public section

/-!
# The positivity derivation

`PosD` distills a successful positivity run into an inductive predicate on the positivity
walk's judgments whose rules are `nestPos`'s cases, read declaratively —
no fuel, no cache, no state.  It is SYNTACTIC (the rules
speak of terms, the kernel's whnf and the kernel's structural checks),
and it is keyed by the INSTANTIATION (charter item 4): the container
rule carries the derivation of the container's constructors at the
concrete key `C.{us} ds`, jointly for the container's whole block, never a fact
about `C` in the abstract.

The judgments (`PosJ`):

* `field prog dep kb e k nf` — the term `e` (a field's domain, or a Π
  body `kb` binders in) is positive at depth `dep` under the frames
  `prog`, of kind `k`, with the walk's normal form `nf`;
* `tele prog base nF j cur ks nds res` — the telescope `cur` has `nF`
  positive fields from field `j`, each opened at `base + j`;
* `ctors prog hi us ds sub cs` — every constructor in `cs`, the frame's
  group abstracted by `sub` and instantiated at `ds`, has a positive
  telescope and a result headed by its hole (the frame's walk);
* `frame prog us ds grp` — the container frame at the key `(us, ds)`
  whose group is `grp` (the container's whole recorded block, at the
  holes `hiAt prog.length + i`);
* `syn prog e` — the frames of the field `e`'s SYNTACTIC nested
  occurrences (official's auxiliary types, `nestSyn`), under the frames
  `prog`.

The rules:

* `const` — the whnf mentions no member and no hole;
* `pi` — a Π whose domain is hole-free, its body positive;
* `hole` — a member hole applied at full arity to the block's parameters
  and hole-free indices;
* `frameHole` — a frame's hole, at its own key's parameters, hole-free
  indices and full arity (the instantiation in progress);
* `contNew` — a stored inductive at a concrete instantiation, its frame
  derived HERE (under the current, well-scoped frames), the container at
  the frame's head — only where some parameter mentions a frame hole
  (`hdeep`: the run walks every other instantiation at the empty stack,
  `nestWalkStack`);
* `contHit` — the same, its parameters below every frame hole, its frame
  derived at the EMPTY frame stack (the run walks such an instantiation
  at the root, then caches it; every node's stack is its ancestors'
  groups);
* `frame` — the group (nonempty, headed by a stored inductive
  that is no member and not `Quot`, at the key's parameter count, distinct, each a member of the
  head's recorded block at the key through `nestInstType`), its
  constructors (`groupCtors`), walked (`ctors`); the group is the head
  followed by its recorded block's other members (`nestFrameMates`,
  N2-eager); the instantiation `C.{us} ds` itself is TYPED at the
  frame's depth (K.52, official's check of every replaced nested
  application);
* `ctorsNil`/`ctorsCons`, `teleNil`/`teleCons` — the lists; a telescope's
  field carries its syntactic pass (`syn`);
* `synNil`/`synNew`/`synHit` — a field's syntactic occurrences: each a
  node whose frame is derived here, or a cache hit below every frame
  hole, each with its SOURCE (`SynSrc`: the key is official's reading of
  a raw subterm of the field) (the occurrences the pass skips — the field's own post-whnf
  instance, one in progress — need no rule).

The whnf step is part of every `field` rule (the premise
`ops.whnf env dep e = .ok w`): the rules classify the reduct.  U4 and
the result checks are side conditions of `ctorsCons`, as the run checks
them.

The ONE inversion of the run is `nestPos_deriv` (`PosDerivInv.lean`).
-/

namespace ConLeche

/-- A field's kind, declaratively: the run's `NestFieldKind` without the
cache's table index. -/
inductive PosKind where
  | ordinary
  | recursive (t : Nat)
  | reflexive (t : Nat)
  | inProgress
  | nested (refl : Bool)
  deriving DecidableEq, Inhabited

/-- The run's kind, its table index forgotten. -/
@[expose] def NestFieldKind.erase : NestFieldKind → PosKind
  | .ordinary => .ordinary
  | .recursive t => .recursive t
  | .reflexive t => .reflexive t
  | .inProgress => .inProgress
  | .nested _ r => .nested r

/-- A FLAT kind: hole-free, a member, a member under binders — no
container instantiation. -/
@[expose] def PosKind.flat : PosKind → Bool
  | .ordinary | .recursive _ | .reflexive _ => true
  | _ => false

/-- A kind U4 guards at a member constructor: recursive, reflexive or
nested (official's auxiliary type makes every later read of such a field
ill-typed). -/
@[expose] def PosKind.guarded : PosKind → Bool
  | .recursive _ | .reflexive _ | .nested _ => true
  | _ => false

@[simp] theorem NestFieldKind.erase_eq_ordinary {k : NestFieldKind} :
    k.erase = .ordinary ↔ k = .ordinary := by
  cases k <;> simp [NestFieldKind.erase]

/-- The constructors of every container in `cs` (at one parameter
count), read off the environment — `nestGroupCtors` without its lookup
cache. -/
@[expose] def groupCtors (ctx : NestCtx) (nPc : Nat) : List Name → Option (List (ConstantVal × Nat))
  | [] => some []
  | c :: cs =>
    match nestContainer ctx c with
    | some (nP', L) =>
      if nP' == nPc || L.isEmpty then (groupCtors ctx nPc cs).map (L ++ ·) else none
    | none => none

/-- **The frames are well scoped**: every frame's parameters are well
scoped below the frames' holes. -/
@[expose] def ProgScoped (ctx : NestCtx) (prog : List NestHole) : Prop :=
  ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
    Expr.WScoped (ctx.hiAt prog.length) x

/-- **A raw subterm**: `x` occurs in `e`, binder
bodies read WITHOUT opening (their loose bound variables stay loose) —
the syntactic pass's own reading (`nestSynGo`). -/
inductive Expr.SubOf : Expr → Expr → Prop where
  | refl (e : Expr) : Expr.SubOf e e
  | appF {x f : Expr} (a : Expr) : Expr.SubOf x f → Expr.SubOf x (.app f a)
  | appA {x a : Expr} (f : Expr) : Expr.SubOf x a → Expr.SubOf x (.app f a)
  | lamT {x t : Expr} (b : Expr) (bm : BinderMeta) : Expr.SubOf x t → Expr.SubOf x (.lam t b bm)
  | lamB {x b : Expr} (t : Expr) (bm : BinderMeta) : Expr.SubOf x b → Expr.SubOf x (.lam t b bm)
  | piT {x t : Expr} (b : Expr) (bm : BinderMeta) : Expr.SubOf x t → Expr.SubOf x (.forallE t b bm)
  | piB {x b : Expr} (t : Expr) (bm : BinderMeta) : Expr.SubOf x b → Expr.SubOf x (.forallE t b bm)
  | letT {x t : Expr} (v b : Expr) : Expr.SubOf x t → Expr.SubOf x (.letE t v b)
  | letV {x v : Expr} (t b : Expr) : Expr.SubOf x v → Expr.SubOf x (.letE t v b)
  | letB {x b : Expr} (t v : Expr) : Expr.SubOf x b → Expr.SubOf x (.letE t v b)
  | proj {x y : Expr} (s : Name) (i : Nat) : Expr.SubOf x y → Expr.SubOf x (.proj s i y)

/-- **A syntactic occurrence's SOURCE**: the key is `nestSynApp?` of a raw subterm of the
scanned field `e`, at the frames below `hi` — so its parameters are raw
subterms of `e`. -/
@[expose] def SynSrc (ctx : NestCtx) (hi : Nat) (e : Expr) (key : NestKey) : Prop :=
  ∃ s, Expr.SubOf s e ∧ nestSynApp? ctx hi s = some key

/-- **The derivation's NODES**: every container instance the derivation meets is a node, recorded as
first-class data — its INSTANTIATION `key` (`C.{lvls} ds`, in the walk's
representation: the parameters at the canonical variables `ctx.params`,
member `t` at `nP + t`, the `i`-th enclosing frame's holes from
`hiAt 0 + i`), the frames at its OCCURRENCE `occ` (the enclosing
instantiations, innermost first: its ancestor chain), the frames its
own frame is derived under `anc` (`= occ` when the frame is walked
there; a cache hit's first walk otherwise), the group `grp`, and
the nodes of its frame `kids` (each occurring at this node's frame
stack, `grpNews … ++ anc`).  A derivation's index is the forest of its
nodes; the tree order is the nesting of the visits. -/
inductive PosTree where
  | node (occ anc : List NestHole) (key : NestKey) (grp : List (Name × Expr))
      (kids : List PosTree)
  deriving Inhabited

/-- The walk's judgments (see the module docstring). -/
inductive PosJ where
  | field (prog : List NestHole) (dep kb : Nat) (e : Expr) (k : PosKind) (nf : Expr)
  | tele (prog : List NestHole) (base nF j : Nat) (cur : Expr) (ks : List PosKind)
      (nds : List (Expr × BinderMeta)) (res : Expr)
  | ctors (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
      (sub : Name → List Level → Option Expr) (cs : List (ConstantVal × Nat))
  | frame (prog : List NestHole) (us : List Level) (ds : List Expr) (grp : List (Name × Expr))
  | syn (prog : List NestHole) (e : Expr)

/-- **The positivity derivation** (see the module docstring). -/
inductive PosD (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) :
    PosJ → List PosTree → Prop where
  /-- the reduct mentions no member and no hole -/
  | const {prog : List NestHole} {dep kb : Nat} {e w : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) :
      PosD ops env ctx
        (.field prog dep kb e .ordinary
          (if e.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) then w else e)) []
  /-- a Π with a hole-free domain and a positive body -/
  | pi {prog : List NestHole} {dep kb : Nat} {e a b : Expr} {bm : BinderMeta} {k : PosKind}
      {nb : Expr} {ts : List PosTree}
      (hw : ops.whnf env dep e = .ok (.forallE a b bm))
      (hocc : (Expr.forallE a b bm).nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (hb : PosD ops env ctx (.field prog (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) k nb)
        ts) :
      PosD ops env ctx (.field prog dep kb e k (.forallE a (nb.abstract1 dep) bm)) ts
  /-- a member hole at the block's parameters, hole-free indices, full arity -/
  | hole {prog : List NestHole} {dep kb : Nat} {e w : Expr} {i : Nat} {ty : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.nP ≤ i) (hhi : i < ctx.hiAt 0)
      (hlen : w.getAppArgs.length = ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0)
      (hpar : w.getAppArgs.take ctx.nP = ctx.params)
      (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) :
      PosD ops env ctx
        (.field prog dep kb e (if kb = 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP)) w)
        []
  /-- a frame's hole: its instantiation in progress, at its own parameters,
  hole-free indices, full arity -/
  | frameHole {prog : List NestHole} {dep kb : Nat} {e w : Expr} {i : Nat} {ty : Expr}
      {h : NestHole}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.hiAt 0 ≤ i) (hhi : i < ctx.hiAt prog.length)
      (hk : prog.reverse[i - ctx.hiAt 0]? = some h)
      (hle : h.key.ds.length ≤ w.getAppArgs.length)
      (hpar : w.getAppArgs.take h.key.ds.length = h.key.ds)
      (hfree : ∀ x ∈ w.getAppArgs.drop h.key.ds.length,
        x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (har : w.getAppArgs.length = nestArity ctx h.key.cname) :
      PosD ops env ctx (.field prog dep kb e .inProgress w) []
  /-- a container at a concrete instantiation, its frame derived here -/
  | contNew {prog : List NestHole} {dep kb : Nat} {e w : Expr} {n : Name} {us : List Level}
      {L : List (ConstantVal × Nat)} {nPc nI : Nat} {cty : Expr} {grp : List (Name × Expr)}
      {ts : List PosTree}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .const n us) (hnm : ctx.names.contains n = false)
      (hC : nestContainer ctx n = some (nPc, L)) (hlen : w.getAppArgs.length = nPc + nI)
      (hquot : n ≠ quotName)
      (hidx : ∀ x ∈ w.getAppArgs.drop nPc,
        x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (hds : ∀ x ∈ w.getAppArgs.take nPc,
        x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
      (hdsw : ∀ x ∈ w.getAppArgs.take nPc, Expr.WScoped (ctx.hiAt prog.length) x)
      (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨n, us, w.getAppArgs.take nPc⟩ = .ok (nI, cty))
      (hhead : grp.head? = some (n, cty)) (hsc : ProgScoped ctx prog)
      (hfr : PosD ops env ctx (.frame prog us (w.getAppArgs.take nPc) grp) ts)
      (hdeep : ((w.getAppArgs.take nPc).all fun x => x.fvarB ≤ ctx.hiAt 0) = false) :
      PosD ops env ctx (.field prog dep kb e (.nested (kb != 0)) w)
        [.node prog prog ⟨n, us, w.getAppArgs.take nPc⟩ grp ts]
  /-- a container at a concrete instantiation below every frame hole, its
  frame derived at the EMPTY frame stack (walked there, or a cache hit) -/
  | contHit {prog : List NestHole} {dep kb : Nat} {e w : Expr} {n : Name}
      {us : List Level} {L : List (ConstantVal × Nat)} {nPc nI : Nat} {cty : Expr}
      {grp : List (Name × Expr)} {ts : List PosTree}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .const n us) (hnm : ctx.names.contains n = false)
      (hC : nestContainer ctx n = some (nPc, L)) (hlen : w.getAppArgs.length = nPc + nI)
      (hquot : n ≠ quotName)
      (hidx : ∀ x ∈ w.getAppArgs.drop nPc,
        x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (hds : ∀ x ∈ w.getAppArgs.take nPc,
        x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt 0)
      (hdsw : ∀ x ∈ w.getAppArgs.take nPc, Expr.WScoped (ctx.hiAt 0) x)
      (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨n, us, w.getAppArgs.take nPc⟩ = .ok (nI, cty))
      (hmem : n ∈ grp.map (·.1))
      (hfr : PosD ops env ctx (.frame [] us (w.getAppArgs.take nPc) grp) ts) :
      PosD ops env ctx (.field prog dep kb e (.nested (kb != 0)) w)
        [.node prog [] ⟨n, us, w.getAppArgs.take nPc⟩ grp ts]
  /-- a container frame: the container's whole recorded block and its
  constructors, walked -/
  | frame {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
      {ctors : List (ConstantVal × Nat)} {ts : List PosTree}
      (hne : grp ≠ [])
      (hhd : ctx.names.contains (grp.headD default).1 = false ∧ (grp.headD default).1 ≠ quotName)
      (hhdC : ∃ L, nestContainer ctx (grp.headD default).1 = some (ds.length, L))
      (hnd : (grp.map (·.1)).Nodup)
      (hinst : ∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨p.1, us, ds⟩ = .ok (nI, p.2))
      (hblk : ∀ p ∈ grp.tail, (nestBlockOf ctx (grp.headD default).1).contains p.1 = true)
      (hgrp : grp.map (·.1) = (grp.headD default).1 :: nestFrameMates ctx (grp.headD default).1)
      (hctors : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
      (hkty : ∃ ty, ops.inferType env (ctx.hiAt prog.length)
        (Expr.mkAppN (.const (grp.headD default).1 us) ds) = .ok ty)
      (hwalk : PosD ops env ctx (.ctors ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
        (ctx.hiAt prog.length + grp.length) us ds (grpSub us (ctx.hiAt prog.length) grp) ctors) ts) :
      PosD ops env ctx (.frame prog us ds grp) ts
  | ctorsNil {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
      {sub : Name → List Level → Option Expr} :
      PosD ops env ctx (.ctors prog hi us ds sub []) []
  /-- one frame constructor: its level parameters distinct, instantiated and
  typed, its telescope positive, U4, its result the hole applied with
  hole-free indices -/
  | ctorsCons {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
      {sub : Name → List Level → Option Expr} {cv : ConstantVal} {nF : Nat}
      {cs : List (ConstantVal × Nat)} {crest ty : Expr} {sv : Level} {ks : List PosKind}
      {nds : List (Expr × BinderMeta)} {cur : Expr} {ts ts' : List PosTree}
      (hnd : Name.nodup cv.levelParams = true)
      (hcrest : instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts sub)
        = some crest)
      (hty : ops.inferType env hi crest = .ok ty) (hsort : ops.ensureSort env hi ty = .ok sv)
      (htele : PosD ops env ctx (.tele prog hi nF 0 crest ks nds cur) ts)
      (hu4 : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds hi cur) 0 i) = false)
      (hres : nestResHead cur = true)
      (hidx : (cur.getAppArgs.drop ds.length).all (fun x => !x.nestOcc ctx.names ctx.nP hi) = true)
      (hrest : PosD ops env ctx (.ctors prog hi us ds sub cs) ts') :
      PosD ops env ctx (.ctors prog hi us ds sub ((cv, nF) :: cs)) (ts ++ ts')
  | teleNil {prog : List NestHole} {base j : Nat} {cur : Expr} :
      PosD ops env ctx (.tele prog base 0 j cur [] [] cur) []
  /-- one field of a telescope: positive at its depth, its syntactic
  occurrences' frames (`hs`), then the rest opened at its variable -/
  | teleCons {prog : List NestHole} {base nF j : Nat} {a b : Expr} {bm : BinderMeta}
      {k : PosKind} {nd : Expr} {ks : List PosKind} {nds : List (Expr × BinderMeta)} {res : Expr}
      {ts tss ts' : List PosTree}
      (ha : PosD ops env ctx (.field prog (base + j) 0 a k nd) ts)
      (hs : PosD ops env ctx (.syn prog a) tss)
      (hb : PosD ops env ctx
        (.tele prog base nF (j + 1) (b.instantiate1 (.fvar (base + j) a)) ks nds res) ts') :
      PosD ops env ctx (.tele prog base (nF + 1) j (.forallE a b bm) (k :: ks) ((nd, bm) :: nds) res)
        (ts ++ (tss ++ ts'))
  | synNil {prog : List NestHole} {e : Expr} : PosD ops env ctx (.syn prog e) []
  /-- a syntactic occurrence (official's auxiliary type) whose frame is
  derived here: a stored inductive at a concrete instantiation, the
  container at the frame's head -/
  | synNew {prog : List NestHole} {e : Expr} {n : Name} {us : List Level} {ds : List Expr}
      {L : List (ConstantVal × Nat)} {nI : Nat} {cty : Expr} {grp : List (Name × Expr)}
      {ts ts' : List PosTree}
      (hsrc : SynSrc ctx (ctx.hiAt prog.length) e ⟨n, us, ds⟩)
      (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
      (hC : nestContainer ctx n = some (ds.length, L))
      (hds : ∀ x ∈ ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
      (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x)
      (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty))
      (hhead : grp.head? = some (n, cty)) (hsc : ProgScoped ctx prog)
      (hfr : PosD ops env ctx (.frame prog us ds grp) ts)
      (hrest : PosD ops env ctx (.syn prog e) ts') :
      PosD ops env ctx (.syn prog e) (.node prog prog ⟨n, us, ds⟩ grp ts :: ts')
  /-- a syntactic occurrence below every frame hole whose frame is derived
  at the EMPTY frame stack (walked there, or a cache hit) -/
  | synHit {prog : List NestHole} {e : Expr} {n : Name} {us : List Level} {ds : List Expr}
      {L : List (ConstantVal × Nat)} {grp : List (Name × Expr)} {ts ts' : List PosTree}
      (hsrc : SynSrc ctx (ctx.hiAt prog.length) e ⟨n, us, ds⟩)
      (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
      (hC : nestContainer ctx n = some (ds.length, L))
      (hds : ∀ x ∈ ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt 0)
      (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt 0) x) (hmem : n ∈ grp.map (·.1))
      (hfr : PosD ops env ctx (.frame [] us ds grp) ts)
      (hrest : PosD ops env ctx (.syn prog e) ts') :
      PosD ops env ctx (.syn prog e) (.node prog [] ⟨n, us, ds⟩ grp ts :: ts')

/-- **A member constructor, derived** (its nodes `ts`): its field
telescope positive at the block's own depth (no frames), U4 at the recursive, reflexive and nested
fields, its result's indices hole-free, M3/M2′ on the normal form
`tyN`. -/
@[expose] def MemberCtorD (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (nF : Nat)
    (crest : Expr) (ks : List PosKind) (tyN : Expr) (ts : List PosTree) : Prop :=
  ∃ nds cur, PosD ops env ctx (.tele [] (ctx.hiAt 0) nF 0 crest ks nds cur) ts ∧
    tyN = closeTelescope nds (ctx.hiAt 0) cur ∧
    ((List.range nF).any fun i =>
      (ks.getD i .ordinary).guarded && structUsedLater tyN 0 i) = false ∧
    nestResHead cur = true ∧
    (cur.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true ∧
    tyN.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true

end ConLeche
