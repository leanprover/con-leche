module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Shift

public section

/-!
# The positivity derivation (lane POSDERIV)

The maintainer's ruling (DESIGN, "RULING — use the positivity run, via a
declarative derivation", 2026-09-25): "Of course we can use that things
have passed the positivity check.  Ideally we distill that into something
more abstract/high level/declarative than 'the check returns true', even
if not semantic."

`PosD` is that distillation: an inductive predicate on the positivity
walk's judgments whose rules are `nestPos`'s cases, read declaratively —
no fuel, no cache, no restart, no state.  It is SYNTACTIC (the rules
speak of terms, the kernel's whnf and the kernel's structural checks),
and it is keyed by the INSTANTIATION (charter item 4): the container
rule carries the derivation of the container's constructors at the
concrete key `C.{us} ds`, jointly for the reached group, never a fact
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
  whose reached group is `grp` (at the holes `hiAt prog.length + i`).

The rules:

* `const` — the whnf mentions no member and no hole;
* `pi` — a Π whose domain is hole-free, its body positive;
* `hole` — a member hole applied at full arity to the block's parameters
  and hole-free indices;
* `frameHole` — a frame's hole, at its own key's parameters, hole-free
  indices and full arity (the instantiation in progress);
* `contNew` — a stored inductive at a concrete instantiation, its frame
  derived HERE (under the current, well-scoped frames), the container at
  the frame's head;
* `contHit` — the same, its parameters below every frame hole, its frame
  derived under some other, well-scoped, frame stack (a cache hit: the
  frame the run accepted earlier);
* `frame` — the reached group (nonempty, headed by a stored inductive
  that is no member and not `Quot`, at the key's parameter count, distinct, each a member of the
  head's recorded block at the key through `nestInstType`), its
  constructors (`groupCtors`), walked (`ctors`);
* `ctorsNil`/`ctorsCons`, `teleNil`/`teleCons` — the lists.

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

/-- A kind of a field the flat (switch-off) route installs: hole-free, a
member, a member under binders — no container instantiation. -/
@[expose] def PosKind.flat : PosKind → Bool
  | .ordinary | .recursive _ | .reflexive _ => true
  | _ => false

@[simp] theorem NestFieldKind.erase_flat (k : NestFieldKind) : k.erase.flat = k.flat := by
  cases k <;> rfl

/-- A kind U4 guards at a member constructor: recursive, reflexive or
nested (official's auxiliary type makes every later read of such a field
ill-typed). -/
@[expose] def PosKind.guarded : PosKind → Bool
  | .recursive _ | .reflexive _ | .nested _ => true
  | _ => false

@[simp] theorem NestFieldKind.erase_eq_ordinary {k : NestFieldKind} :
    k.erase = .ordinary ↔ k = .ordinary := by
  cases k <;> simp [NestFieldKind.erase]

/-- The frame's new walk entries (one per group member, at the key). -/
@[expose] def grpNews (us : List Level) (ds : List Expr) (hi : Nat) (grp : List (Name × Expr)) :
    List NestHole :=
  grp.map fun p => { key := ⟨p.1, us, ds⟩, base := hi }

/-- The frame's member substitution (`nestFrame`'s `sub`): the group's
members at the key's levels to their holes. -/
@[expose] def grpSub (us : List Level) (hi : Nat) (grp : List (Name × Expr)) :
    Name → List Level → Option Expr :=
  fun c us' => if us' == us then
    (grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)).lookup c else none

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

/-- **The derivation's NODES** (coordinator's ruling on NESTIND's F13):
every container instance the derivation meets is a node, recorded as
first-class data — its INSTANTIATION `key` (`C.{lvls} ds`, in the walk's
representation: the parameters at the canonical variables `ctx.params`,
member `t` at `nP + t`, the `i`-th enclosing frame's holes from
`hiAt 0 + i`), the frames at its OCCURRENCE `occ` (the enclosing
instantiations, innermost first: its ancestor chain), the frames its
own frame is derived under `anc` (`= occ` when the frame is walked
there; a cache hit's first walk otherwise), the reached group `grp`, and
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
      (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨n, us, w.getAppArgs.take nPc⟩ = .ok (nI, cty))
      (hhead : grp.head? = some (n, cty)) (hsc : ProgScoped ctx prog)
      (hfr : PosD ops env ctx (.frame prog us (w.getAppArgs.take nPc) grp) ts) :
      PosD ops env ctx (.field prog dep kb e (.nested (kb != 0)) w)
        [.node prog prog ⟨n, us, w.getAppArgs.take nPc⟩ grp ts]
  /-- a container at a concrete instantiation below every frame hole, its
  frame derived under another well-scoped frame stack (a cache hit) -/
  | contHit {prog prog' : List NestHole} {dep kb : Nat} {e w : Expr} {n : Name}
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
      (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨n, us, w.getAppArgs.take nPc⟩ = .ok (nI, cty))
      (hsc : ProgScoped ctx prog')
      (hmem : n ∈ grp.map (·.1))
      (hfr : PosD ops env ctx (.frame prog' us (w.getAppArgs.take nPc) grp) ts) :
      PosD ops env ctx (.field prog dep kb e (.nested (kb != 0)) w)
        [.node prog prog' ⟨n, us, w.getAppArgs.take nPc⟩ grp ts]
  /-- a container frame: the reached group and its constructors, walked -/
  | frame {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
      {ctors : List (ConstantVal × Nat)} {ts : List PosTree}
      (hne : grp ≠ [])
      (hhd : ctx.names.contains (grp.headD default).1 = false ∧ (grp.headD default).1 ≠ quotName)
      (hhdC : ∃ L, nestContainer ctx (grp.headD default).1 = some (ds.length, L))
      (hnd : (grp.map (·.1)).Nodup)
      (hinst : ∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
        ⟨p.1, us, ds⟩ = .ok (nI, p.2))
      (hblk : ∀ p ∈ grp.tail, (nestBlockOf ctx (grp.headD default).1).contains p.1 = true)
      (hctors : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
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
  /-- one field of a telescope: positive at its depth, then the rest opened
  at its variable -/
  | teleCons {prog : List NestHole} {base nF j : Nat} {a b : Expr} {bm : BinderMeta}
      {k : PosKind} {nd : Expr} {ks : List PosKind} {nds : List (Expr × BinderMeta)} {res : Expr}
      {ts ts' : List PosTree}
      (ha : PosD ops env ctx (.field prog (base + j) 0 a k nd) ts)
      (hb : PosD ops env ctx
        (.tele prog base nF (j + 1) (b.instantiate1 (.fvar (base + j) a)) ks nds res) ts') :
      PosD ops env ctx (.tele prog base (nF + 1) j (.forallE a b bm) (k :: ks) ((nd, bm) :: nds) res)
        (ts ++ ts')

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
