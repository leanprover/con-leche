module

public import ConLeche.Kernel.Inductives.PositivityK
public import ConLeche.Verify.Inductives.PosDeriv

public section

/-!
# The key-named positivity derivation (PRIMREC / NESTKN-M1)

`PosDK` distills a successful run of the key-named positivity check
(`Kernel/Inductives/PositivityK.lean`, variant E) into an inductive
predicate whose rules are `posK`'s, `useK`'s, `nodeK`'s and `metK`'s cases read
declaratively — no fuel, no cache, no state.  It replaces `PosD`'s path
frames (`prog`, `contNew`/`contHit`, the `PosTree` forest) by two
judgments: a NODE, derived once at its own layout (the ONE layout function
`nestLayoutK`, K-f), and a USE, which carries the node's derivation, the
match of the user's parameters against the node's `DsF` (its bindings, and
the K-d check per parameter) and — for every flexible family the node
MET — the binding's own judgment (a family of the user met there, the
user's own hole, or a PENDING use of a concrete key at the user's layout).

The judgments (`PosJK`), each at a layout `L` (`LayoutK`: the flexible
families `hiAt0 ..< hiAt0 + L.nF`, then the own group's holes, `L.hi` the
first variable above) and a met set `met` (the flexible families of `L`'s
node that the node MET; the ROOT has none):

* `field L met dep kb e k nf` — the term `e` is positive at depth `dep`,
  of kind `k`, with the walk's normal form `nf`;
* `tele L met nF j cur ks nds res` — `nF` positive fields of `cur` from
  field `j`, field `j` opened at `L.hi + j`;
* `ctors L met cs` — every (constructor, crest) of `cs` walked;
* `node kc lo met` — the node of the canonical key `kc`: its layout `lo`
  (`nestLayoutK` at `nestContainer`, the one function), its crests walked
  at `lo.L` with the met set `met`;
* `use L met kc ps` — the canonical key `kc`, spelled `ps` at `L`, used;
* `bind L met b` — a binding `b` of a family the used node met;
* `syn L met e` — the syntactic pass of the field `e`.

A cache hit is a `use` whose `node` premise is COPIED from the run's cache
invariant (a `Prop` derivation duplicates for free); a first visit is the
same rule with the node derived by the recursive walk.  The derivation is
therefore a finite TREE (DESIGN "PRIMREC / NESTKN-M1": tree, not
completion order).  It has no freshness premise (PROOFPLAN R2) and no
scoping premise: well-scopedness is a consequence, provable by induction
over the derivation from the layout's own facts (M2).

The one inversion of the run is `posK_deriv` (`PosDerivKInv.lean`).
-/

namespace ConLeche

/-! ## The match, declaratively -/

/-- The node record a layout's matches read (`bindInnerK` reads only its
flexible families' count, keys and inner-abstracted parameters). -/
@[expose] def nodeOfK (lo : LayoutOutK) : NodeK :=
  { key := default, q := 0, dsF := lo.L.dsF, nF := lo.L.nF, met := [], merged := lo.merged,
    famKeys := lo.L.fams.map (·.1), famPs := lo.famPs }

/-- **One parameter checked (K-d, `checkParamsK`)**: the pattern at the
bindings IS the user's parameter, or — only where the pattern holds a
KN5-merged family — both sides type at the user's depth and are defeq
there. -/
@[expose] def ParamOkK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (L : LayoutK)
    (merged : List Nat) (θ : Nat → Option Expr) (p t : Expr) : Prop :=
  p.replaceFVars θ = t ∨
    (merged.any (fun j => p.nestOcc [] (ctx.hiAt 0 + j) (ctx.hiAt 0 + j + 1)) = true ∧
      (∃ ty, ops.inferType env L.hi (p.replaceFVars θ) = .ok ty) ∧
      (∃ ty, ops.inferType env L.hi t = .ok ty) ∧
      ops.isDefEq env L.hi (p.replaceFVars θ) t = .ok true)

/-! ## The judgments and the derivation -/

/-- **A hook on the `use` rule** (PRIMREC / NESTKN-M3): a condition on the user's
layout `L`, the used key `kc`, the node's key `kn`, the user's parameters `ps`, the
node's layout `lo` and met set `metc`, and the match's bindings.  The kernel checks
today are the rule's premises; the hook carries what the model side needs beyond
them (`UseOkK`, `Model/Inductives/PosDerivMonoK.lean`), until a kernel round checks
it.  `PosDK` is the derivation at the TRIVIAL hook (what the run inverts to today). -/
abbrev UseHookK : Type :=
  LayoutK → NestKey → NestKey → List Expr → LayoutOutK → List Nat → List (Nat × Expr) → Prop

/-- The trivial hook. -/
@[expose] def trivHookK : UseHookK := fun _ _ _ _ _ _ _ => True

/-- The walk's judgments (see the module docstring). -/
inductive PosJK where
  | field (L : LayoutK) (met : List Nat) (dep kb : Nat) (e : Expr) (k : PosKind) (nf : Expr)
  | tele (L : LayoutK) (met : List Nat) (nF j : Nat) (cur : Expr) (ks : List PosKind)
      (nds : List (Expr × BinderMeta)) (res : Expr)
  | ctors (L : LayoutK) (met : List Nat) (cs : List ((ConstantVal × Nat) × Expr))
  | node (kc : NestKey) (lo : LayoutOutK) (met : List Nat)
  | use (L : LayoutK) (met : List Nat) (kc : NestKey) (ps : List Expr)
  | bind (L : LayoutK) (met : List Nat) (b : Expr)
  | syn (L : LayoutK) (met : List Nat) (e : Expr)

/-- **The key-named positivity derivation** (see the module docstring). -/
inductive PosDKH (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK) :
    PosJK → Prop where
  /-- the reduct mentions no member and no family -/
  | const {L : LayoutK} {met : List Nat} {dep kb : Nat} {e w : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP L.hi = false) :
      PosDKH ops env ctx hk
        (.field L met dep kb e .ordinary (if e.nestOcc ctx.names ctx.nP L.hi then w else e))
  /-- a Π with a hole-free domain and a positive body -/
  | pi {L : LayoutK} {met : List Nat} {dep kb : Nat} {e a b : Expr} {bm : BinderMeta}
      {k : PosKind} {nb : Expr}
      (hw : ops.whnf env dep e = .ok (.forallE a b bm))
      (hocc : (Expr.forallE a b bm).nestOcc ctx.names ctx.nP L.hi = true)
      (ha : a.nestOcc ctx.names ctx.nP L.hi = false)
      (hb : PosDKH ops env ctx hk (.field L met (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) k nb)) :
      PosDKH ops env ctx hk (.field L met dep kb e k (.forallE a (nb.abstract1 dep) bm))
  /-- a member hole at the block's parameters, hole-free indices, full arity -/
  | hole {L : LayoutK} {met : List Nat} {dep kb : Nat} {e w : Expr} {i : Nat} {ty : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP L.hi = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.nP ≤ i) (hhi : i < ctx.hiAt 0)
      (hlen : w.getAppArgs.length = ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0)
      (hpar : w.getAppArgs.take ctx.nP = ctx.params)
      (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP L.hi = false) :
      PosDKH ops env ctx hk
        (.field L met dep kb e (if kb = 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP)) w)
  /-- a FLEXIBLE family of the layout, applied to exactly its indices
  (hole-free), MET by this node -/
  | famHole {L : LayoutK} {met : List Nat} {dep kb : Nat} {e w : Expr} {i : Nat} {ty : Expr}
      {key : NestKey} {nI : Nat}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP L.hi = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.hiAt 0 ≤ i) (hhi : i < L.hi)
      (hj : i - ctx.hiAt 0 < L.nF)
      (hfam : L.fams[i - ctx.hiAt 0]? = some (key, nI))
      (hlen : w.getAppArgs.length = nI)
      (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP L.hi = false)
      (hmet : i - ctx.hiAt 0 ∈ met) :
      PosDKH ops env ctx hk (.field L met dep kb e .inProgress w)
  /-- an OWN hole (variant E: today's frame hole) at `DsF`, hole-free
  indices, full arity: the node in progress -/
  | ownHole {L : LayoutK} {met : List Nat} {dep kb : Nat} {e w : Expr} {i : Nat} {ty : Expr}
      {g : Name}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP L.hi = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.hiAt 0 ≤ i) (hhi : i < L.hi)
      (hj : L.nF ≤ i - ctx.hiAt 0)
      (hg : L.grp[i - ctx.hiAt 0 - L.nF]? = some g)
      (hle : L.dsF.length ≤ w.getAppArgs.length)
      (hpar : w.getAppArgs.take L.dsF.length = L.dsF)
      (hfree : ∀ x ∈ w.getAppArgs.drop L.dsF.length, x.nestOcc ctx.names ctx.nP L.hi = false)
      (har : w.getAppArgs.length = nestArity ctx g) :
      PosDKH ops env ctx hk (.field L met dep kb e .inProgress w)
  /-- a container at an instantiation: the canonical key (read back) USED -/
  | cont {L : LayoutK} {met : List Nat} {dep kb : Nat} {e w : Expr} {n : Name}
      {us : List Level} {Lc : List (ConstantVal × Nat)} {nPc nI : Nat} {cty : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP L.hi = true)
      (hfn : w.getAppFn = .const n us) (hnm : ctx.names.contains n = false)
      (hC : nestContainer ctx n = some (nPc, Lc)) (hquot : n ≠ quotName)
      (hlen : w.getAppArgs.length = nPc + nI)
      (hidx : ∀ x ∈ w.getAppArgs.drop nPc, x.nestOcc ctx.names ctx.nP L.hi = false)
      (hds : ∀ x ∈ w.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ L.hi)
      (hnI : nestInstType (m := CheckM) ctx L.hi ⟨n, us, w.getAppArgs.take nPc⟩ = .ok (nI, cty))
      (huse : PosDKH ops env ctx hk (.use L met ⟨n, us, (w.getAppArgs.take nPc).map (rbK ctx L)⟩
        (w.getAppArgs.take nPc))) :
      PosDKH ops env ctx hk (.field L met dep kb e (.nested (kb != 0)) w)
  | teleNil {L : LayoutK} {met : List Nat} {j : Nat} {cur : Expr} :
      PosDKH ops env ctx hk (.tele L met 0 j cur [] [] cur)
  /-- one field of a telescope: positive at its depth, its syntactic pass,
  then the rest opened at its variable -/
  | teleCons {L : LayoutK} {met : List Nat} {nF j : Nat} {a b : Expr} {bm : BinderMeta}
      {k : PosKind} {nd : Expr} {ks : List PosKind} {nds : List (Expr × BinderMeta)} {res : Expr}
      (ha : PosDKH ops env ctx hk (.field L met (L.hi + j) 0 a k nd))
      (hs : PosDKH ops env ctx hk (.syn L met a))
      (hb : PosDKH ops env ctx hk
        (.tele L met nF (j + 1) (b.instantiate1 (.fvar (L.hi + j) a)) ks nds res)) :
      PosDKH ops env ctx hk (.tele L met (nF + 1) j (.forallE a b bm) (k :: ks) ((nd, bm) :: nds) res)
  | ctorsNil {L : LayoutK} {met : List Nat} : PosDKH ops env ctx hk (.ctors L met [])
  /-- one crest walked: its telescope positive, U4, its result headed by a
  family with hole-free indices -/
  | ctorsCons {L : LayoutK} {met : List Nat} {cv : ConstantVal} {nF : Nat} {crest : Expr}
      {cs : List ((ConstantVal × Nat) × Expr)} {ks : List PosKind}
      {nds : List (Expr × BinderMeta)} {cur : Expr}
      (htele : PosDKH ops env ctx hk (.tele L met nF 0 crest ks nds cur))
      (hu4 : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds L.hi cur) 0 i) = false)
      (hres : nestResHead cur = true)
      (hidx : (cur.getAppArgs.drop L.dsF.length).all
        (fun x => !x.nestOcc ctx.names ctx.nP L.hi) = true)
      (hrest : PosDKH ops env ctx hk (.ctors L met cs)) :
      PosDKH ops env ctx hk (.ctors L met (((cv, nF), crest) :: cs))
  /-- **a node**: its layout the ONE function of its key (K-f), its crests
  walked at it -/
  | node {kc : NestKey} {lo : LayoutOutK} {met : List Nat}
      (hlay : nestLayoutK ops env ctx (nestContainer ctx) kc = .ok lo)
      (hwalk : PosDKH ops env ctx hk (.ctors lo.L met (lo.ctors.zip lo.crests))) :
      PosDKH ops env ctx hk (.node kc lo met)
  /-- **a use**: the key's former at the user (K-c), K.52 at the user's
  layout, the node of the key's group (`kn`, the group member walked first),
  the user's parameters matched against its `DsF` and checked (K-d), and
  every binding of a family the node MET, judged at the user; the bindings are
  the match's with every inner family bound from its outer one (`bindInnerK`),
  every family bound -/
  | use {L : LayoutK} {met : List Nat} {kc kn : NestKey} {ps : List Expr} {lo : LayoutOutK}
      {metc : List Nat} {rs : List (List (Nat × Expr))} {bs : List (Nat × Expr)}
      (hinst : ∃ r, nestInstType (m := CheckM) ctx L.hi ⟨kc.cname, kc.lvls, ps⟩ = .ok r)
      (hk52 : ∃ ty, ops.inferType env L.hi (Expr.mkAppN (.const kc.cname kc.lvls) ps) = .ok ty)
      (hnode : PosDKH ops env ctx hk (.node kn lo metc))
      (hgrp : kc.cname ∈ lo.ginfo.map (·.1)) (hlv : kc.lvls = kn.lvls) (hkds : kc.ds = kn.ds)
      (hlen : lo.L.dsF.length = ps.length)
      (hbs : (lo.L.dsF.zip ps).mapM (matchStepK ctx L lo.L.nF) = .ok rs)
      (hinner : bindInnerK ctx L (nodeOfK lo) (List.range lo.L.nF).reverse rs.flatten = .ok bs)
      (hall : ∀ j, j < lo.L.nF → bs.any (·.1 == j) = true)
      (hpar : ∀ x ∈ lo.L.dsF.zip ps,
        ParamOkK ops env ctx L lo.merged (thetaK ctx lo.L.nF bs) x.1 x.2)
      (hbind : ∀ b ∈ bs, b.1 ∈ metc → PosDKH ops env ctx hk (.bind L met b.2))
      (hhook : hk L kc kn ps lo metc bs) :
      PosDKH ops env ctx hk (.use L met kc ps)
  /-- a met family bound to a flexible family of the user: met there too -/
  | bindFam {L : LayoutK} {met : List Nat} {i : Nat} {ty : Expr}
      (hlo : ctx.hiAt 0 ≤ i) (hhi : i < ctx.hiAt 0 + L.nF) (hmet : i - ctx.hiAt 0 ∈ met) :
      PosDKH ops env ctx hk (.bind L met (.fvar i ty))
  /-- a met family bound to the user's own hole (applied): in progress there -/
  | bindOwn {L : LayoutK} {met : List Nat} {b : Expr} {i : Nat} {ty : Expr}
      (hfn : b.getAppFn = .fvar i ty) (hlo : ctx.hiAt 0 + L.nF ≤ i) (hhi : i < L.hi) :
      PosDKH ops env ctx hk (.bind L met b)
  /-- a met family bound to a key occurrence: that key USED at the user (the
  pending use) -/
  | bindKey {L : LayoutK} {met : List Nat} {b : Expr} {n : Name} {us : List Level}
      (hfn : b.getAppFn = .const n us)
      (huse : PosDKH ops env ctx hk
        (.use L met ⟨n, us, b.getAppArgs.map (rbK ctx L)⟩ b.getAppArgs)) :
      PosDKH ops env ctx hk (.bind L met b)
  | synNil {L : LayoutK} {met : List Nat} {e : Expr} : PosDKH ops env ctx hk (.syn L met e)
  /-- a syntactic occurrence (official's auxiliary type) used -/
  | synUse {L : LayoutK} {met : List Nat} {e : Expr} {key : NestKey}
      (hsrc : SynSrc ctx L.hi e key)
      (huse : PosDKH ops env ctx hk
        (.use L met ⟨key.cname, key.lvls, key.ds.map (rbK ctx L)⟩ key.ds))
      (hrest : PosDKH ops env ctx hk (.syn L met e)) :
      PosDKH ops env ctx hk (.syn L met e)

/-- **The derivation the run inverts to today**: at the trivial hook. -/
abbrev PosDK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) : PosJK → Prop :=
  PosDKH ops env ctx trivHookK

/-- **A member constructor, derived** at the ROOT layout: its field
telescope positive, U4 at the recursive, reflexive and nested fields, its
result's indices hole-free, M3/M2′ on the normal form `tyN` (at a hook). -/
@[expose] def MemberCtorDKH (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (hk : UseHookK)
    (nF : Nat) (crest : Expr) (ks : List PosKind) (tyN : Expr) : Prop :=
  ∃ met nds cur, PosDKH ops env ctx hk (.tele (rootLayoutK ctx) met nF 0 crest ks nds cur) ∧
    tyN = closeTelescope nds (ctx.hiAt 0) cur ∧
    ((List.range nF).any fun i =>
      (ks.getD i .ordinary).guarded && structUsedLater tyN 0 i) = false ∧
    nestResHead cur = true ∧
    (cur.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true ∧
    tyN.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true

/-- A member constructor, derived at the trivial hook (what the run gives today). -/
abbrev MemberCtorDK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (nF : Nat)
    (crest : Expr) (ks : List PosKind) (tyN : Expr) : Prop :=
  MemberCtorDKH ops env ctx trivHookK nF crest ks tyN

end ConLeche
