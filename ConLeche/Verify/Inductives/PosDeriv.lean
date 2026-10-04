module

public import ConLeche.Kernel.Inductives.Positivity
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
* `ctors prog hi us ds names holes cs` — every constructor in `cs`, the
  frame's group `names` abstracted (to `holes`) and instantiated at `ds`
  (`nestCrest`), has a positive
  telescope and a result headed by its hole (the frame's walk);
* `frame prog us ds grp` — the container frame at the key `(us, ds)`
  whose group is `grp` (the container's whole recorded block, at the
  holes `hiAt prog.length + i`);
* `seed key` — the frame of a SEED (`nestSeeds`: an outside class the
  recursor check resolved, `checkBlockSeeds`, walked at the root).

The rules:

* `const` — the whnf mentions no member and no hole;
* `pi` — a Π whose domain is hole-free, its body positive;
* `hole` — a member hole (standing for the member applied to the block's
  parameters) applied to hole-free indices, at full arity;
* `frameHole` — a frame's hole (the instantiation in progress, standing
  for its container applied to the key's parameters), applied to
  hole-free indices, at full arity;
* `contNew` — a stored inductive at a concrete instantiation, its frame
  derived HERE (under the current, well-scoped frames), the container at
  the frame's head;
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
* `ctorsNil`/`ctorsCons`, `teleNil`/`teleCons` — the lists;
* `seed` — a seed: a stored inductive (no member, not `Quot`) at a
  concrete instantiation below every frame hole whose parameters' leaves
  are the canonical variables' (`SeedLeaves`), its frame derived at the
  EMPTY frame stack (walked there, or a cache hit).

The whnf step is part of every `field` rule (the premise
`ops.whnf env dep e = .ok w`): the rules classify the reduct.  U4 and
the result checks are side conditions of `ctorsCons`, as the run checks
them.

The ONE inversion of the run is `nestPos_deriv` (`PosDerivInv.lean`).
-/

namespace ConLeche

/-- The frame's new walk entries (one per group member, at the key). -/
@[expose] def grpNews (us : List Level) (ds : List Expr) (hi : Nat) (grp : List (Name × Expr)) :
    List NestHole :=
  grp.map fun p => { key := ⟨p.1, us, ds⟩, base := hi }

/-- The frame's holes (`nestFrame`'s): the group's members' variables
`hi + i`, typed by their instantiated formers. -/
@[expose] def grpHoles (hi : Nat) (grp : List (Name × Expr)) : List Expr :=
  grp.mapIdx fun i (_, ty) => Expr.fvar (hi + i) ty

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

/-! ### The holes' entries (`nestHoleAt`) -/

theorem nestHoleAt_some {ctx : NestCtx} {prog : List NestHole} {i : Nat} {h : NestHole}
    (hh : nestHoleAt ctx prog i = some h) : ctx.nP ≤ i ∧ i < ctx.hiAt prog.length := by
  unfold nestHoleAt at hh
  split at hh
  · rename_i h1
    have := (List.getElem?_eq_some_iff.mp hh).1
    simp only [List.length_append, NestCtx.rootHoles, List.length_map,
      List.length_reverse] at this
    exact ⟨h1, by simp only [NestCtx.hiAt]; omega⟩
  · exact nomatch hh

/-- A member hole's entry is the root frame's. -/
theorem nestHoleAt_root {ctx : NestCtx} {prog : List NestHole} {i : Nat} {h : NestHole}
    (hh : nestHoleAt ctx prog i = some h) (hlt : i < ctx.hiAt 0) :
    h = ⟨⟨ctx.names.getD (i - ctx.nP) .anonymous, ctx.lps.map .param, ctx.params⟩, ctx.nP⟩ := by
  obtain ⟨h1, -⟩ := nestHoleAt_some hh
  unfold nestHoleAt at hh
  rw [ite_eq_left h1, List.getElem?_append_left (by simp [NestCtx.rootHoles, NestCtx.hiAt] at hlt ⊢; omega)]
    at hh
  simp only [NestCtx.rootHoles, List.getElem?_map] at hh
  have hl : i - ctx.nP < ctx.names.length := by simp [NestCtx.hiAt] at hlt; omega
  rw [List.getElem?_eq_getElem hl] at hh
  simp only [Option.map_some, Option.some.injEq] at hh
  rw [← hh, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]

/-- A frame hole's entry is its frame's. -/
theorem nestHoleAt_frame {ctx : NestCtx} {prog : List NestHole} {i : Nat} {h : NestHole}
    (hh : nestHoleAt ctx prog i = some h) (hge : ctx.hiAt 0 ≤ i) :
    prog.reverse[i - ctx.hiAt 0]? = some h := by
  obtain ⟨h1, -⟩ := nestHoleAt_some hh
  unfold nestHoleAt at hh
  rw [ite_eq_left h1, List.getElem?_append_right (by simp [NestCtx.rootHoles, NestCtx.hiAt] at hge ⊢; omega)]
    at hh
  simp only [NestCtx.rootHoles, List.length_map] at hh
  rwa [show i - ctx.nP - ctx.names.length = i - ctx.hiAt 0 by simp [NestCtx.hiAt]; omega] at hh

theorem nestHoleAt_of_root {ctx : NestCtx} (prog : List NestHole) {i : Nat} (h1 : ctx.nP ≤ i)
    (hlt : i < ctx.hiAt 0) :
    nestHoleAt ctx prog i
      = some ⟨⟨ctx.names.getD (i - ctx.nP) .anonymous, ctx.lps.map .param, ctx.params⟩, ctx.nP⟩ := by
  have hl : i - ctx.nP < ctx.names.length := by simp [NestCtx.hiAt] at hlt; omega
  unfold nestHoleAt
  rw [ite_eq_left h1, List.getElem?_append_left (by simpa [NestCtx.rootHoles] using hl)]
  simp only [NestCtx.rootHoles, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
    List.getD_eq_getElem?_getD, Option.getD_some]

theorem nestHoleAt_of_frame {ctx : NestCtx} {prog : List NestHole} {i : Nat} {h : NestHole}
    (hge : ctx.hiAt 0 ≤ i) (hk : prog.reverse[i - ctx.hiAt 0]? = some h) :
    nestHoleAt ctx prog i = some h := by
  have h1 : ctx.nP ≤ i := by simp [NestCtx.hiAt] at hge; omega
  unfold nestHoleAt
  rw [ite_eq_left h1, List.getElem?_append_right (by simp [NestCtx.rootHoles, NestCtx.hiAt] at hge ⊢; omega)]
  simp only [NestCtx.rootHoles, List.length_map]
  rwa [show i - ctx.nP - ctx.names.length = i - ctx.hiAt 0 by simp [NestCtx.hiAt]; omega]

/-- A syntactic telescope of `n` binders ending in a sort has `n` binders. -/
theorem stripPis_sort_piBinders_length :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {s : Level},
      e.stripPis n = some (bs, .sort s) → e.piBinders.1.length = n
  | 0, e, bs, s, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | n + 1, e, bs, s, h => by
    cases e with
    | forallE ty b m =>
      simp only [Expr.stripPis] at h
      obtain ⟨⟨bs', e'⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      simp only [Expr.piBinders, List.length_cons]
      rw [stripPis_sort_piBinders_length n hb]
    | _ => simp [Expr.stripPis] at h

/-- **Every member's stored former has the arity `nP + nIdx`**
(`nestArity`, the frames' arity: its type is a syntactic telescope of
the block's parameters and its indices). -/
@[expose] def NestArityOk (ctx : NestCtx) : Prop :=
  ∀ t, t < ctx.names.length →
    nestArity ctx (ctx.names.getD t .anonymous) = ctx.nP + ctx.nIdxs.getD t 0

/-- **The root frame reads as the members' own rule** (the premise the
inversion reads a member hole's occurrence under): the canonical
parameters are `nP` variables below `nP`, and every member's stored
former has the arity `nP + nIdx` (`nestArity`, the frames' arity). -/
@[expose] def NestRootOk (ctx : NestCtx) : Prop :=
  ctx.params.length = ctx.nP ∧ (∀ x ∈ ctx.params, ∃ i ty, x = .fvar i ty ∧ i < ctx.nP) ∧
  NestArityOk ctx

/-- **The frames are well scoped**: every frame's parameters are well
scoped below the frames' holes. -/
@[expose] def ProgScoped (ctx : NestCtx) (prog : List NestHole) : Prop :=
  ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
    Expr.WScoped (ctx.hiAt prog.length) x

/-- **A seed's leaves are the canonical variables'**: every free-variable
leaf of `x` is a leaf of a canonical parameter variable or of a member
hole (`nestHoles`) — the term was moved to the walk's representation
(`nestSeedOf`). -/
@[expose] def SeedLeaves (ctx : NestCtx) (x : Expr) : Prop :=
  ∀ hs, nestHoles ctx = some hs → ∀ l ∈ x.fvarLeaves, ∃ a ∈ ctx.params ++ hs, l ∈ a.fvarLeaves

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
  | field (prog : List NestHole) (dep kb : Nat) (e : Expr) (k : NestFieldKind) (nf : Expr)
  | tele (prog : List NestHole) (base nF j : Nat) (cur : Expr) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr)
  | ctors (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
      (names : List Name) (holes : List Expr) (cs : List (ConstantVal × Nat))
  | frame (prog : List NestHole) (us : List Level) (ds : List Expr) (grp : List (Name × Expr))
  | seed (key : NestKey)

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
  | pi {prog : List NestHole} {dep kb : Nat} {e a b : Expr} {bm : BinderMeta} {k : NestFieldKind}
      {nb : Expr} {ts : List PosTree}
      (hw : ops.whnf env dep e = .ok (.forallE a b bm))
      (hocc : (Expr.forallE a b bm).nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (hb : PosD ops env ctx (.field prog (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) k nb)
        ts) :
      PosD ops env ctx (.field prog dep kb e k (.forallE a (nb.abstract1 dep) bm)) ts
  /-- a member hole at hole-free indices, full arity -/
  | hole {prog : List NestHole} {dep kb : Nat} {e w : Expr} {i : Nat} {ty : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.nP ≤ i) (hhi : i < ctx.hiAt 0)
      (hlen : w.getAppArgs.length = ctx.nIdxs.getD (i - ctx.nP) 0)
      (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) :
      PosD ops env ctx
        (.field prog dep kb e (if kb = 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP)) w)
        []
  /-- a frame's hole: its instantiation in progress, at hole-free indices,
  full arity -/
  | frameHole {prog : List NestHole} {dep kb : Nat} {e w : Expr} {i : Nat} {ty : Expr}
      {h : NestHole}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.hiAt 0 ≤ i) (hhi : i < ctx.hiAt prog.length)
      (hk : prog.reverse[i - ctx.hiAt 0]? = some h)
      (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false)
      (har : w.getAppArgs.length + h.key.ds.length = nestArity ctx h.key.cname) :
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
      (hfr : PosD ops env ctx (.frame prog us (w.getAppArgs.take nPc) grp) ts) :
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
        (ctx.hiAt prog.length + grp.length) us ds (grp.map (·.1))
        (grpHoles (ctx.hiAt prog.length) grp) ctors) ts) :
      PosD ops env ctx (.frame prog us ds grp) ts
  | ctorsNil {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
      {names : List Name} {holes : List Expr} :
      PosD ops env ctx (.ctors prog hi us ds names holes []) []
  /-- one frame constructor: its level parameters distinct, instantiated and
  typed, its telescope positive, U4, its result the hole applied with
  hole-free indices -/
  | ctorsCons {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
      {names : List Name} {holes : List Expr} {cv : ConstantVal} {nF : Nat}
      {cs : List (ConstantVal × Nat)} {crest ty : Expr} {sv : Level} {ks : List NestFieldKind}
      {nds : List (Expr × BinderMeta)} {cur : Expr} {ts ts' : List PosTree}
      (hnd : Name.nodup cv.levelParams = true)
      (hcrest : nestCrest names us ds holes (cv.type.instantiateLevelParams cv.levelParams us)
        = some crest)
      (hty : ops.inferType env hi crest = .ok ty) (hsort : ops.ensureSort env hi ty = .ok sv)
      (htele : PosD ops env ctx (.tele prog hi nF 0 crest ks nds cur) ts)
      (hu4 : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
        structUsedLater (closeTelescope nds hi cur) 0 i) = false)
      (hres : nestResHead cur = true)
      (hidx : cur.getAppArgs.all (fun x => !x.nestOcc ctx.names ctx.nP hi) = true)
      (hrest : PosD ops env ctx (.ctors prog hi us ds names holes cs) ts') :
      PosD ops env ctx (.ctors prog hi us ds names holes ((cv, nF) :: cs)) (ts ++ ts')
  | teleNil {prog : List NestHole} {base j : Nat} {cur : Expr} :
      PosD ops env ctx (.tele prog base 0 j cur [] [] cur) []
  /-- one field of a telescope: positive at its depth, then the rest
  opened at its variable -/
  | teleCons {prog : List NestHole} {base nF j : Nat} {a b : Expr} {bm : BinderMeta}
      {k : NestFieldKind} {nd : Expr} {ks : List NestFieldKind} {nds : List (Expr × BinderMeta)} {res : Expr}
      {ts ts' : List PosTree}
      (ha : PosD ops env ctx (.field prog (base + j) 0 a k nd) ts)
      (hb : PosD ops env ctx
        (.tele prog base nF (j + 1) (b.instantiate1 (.fvar (base + j) a)) ks nds res) ts') :
      PosD ops env ctx (.tele prog base (nF + 1) j (.forallE a b bm) (k :: ks) ((nd, bm) :: nds) res)
        (ts ++ ts')
  /-- a seed (`nestSeeds`): a stored inductive at a concrete instantiation
  below every frame hole, its parameters' leaves the canonical variables',
  its frame derived at the EMPTY frame stack (walked there, or a cache hit) -/
  | seed {n : Name} {us : List Level} {ds : List Expr} {L : List (ConstantVal × Nat)}
      {grp : List (Name × Expr)} {ts : List PosTree}
      (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
      (hC : nestContainer ctx n = some (ds.length, L))
      (hds : ∀ x ∈ ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt 0)
      (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt 0) x) (hleaf : ∀ x ∈ ds, SeedLeaves ctx x)
      (hmem : n ∈ grp.map (·.1))
      (hfr : PosD ops env ctx (.frame [] us ds grp) ts) :
      PosD ops env ctx (.seed ⟨n, us, ds⟩) [.node [] [] ⟨n, us, ds⟩ grp ts]

/-- **A member constructor, derived** (its nodes `ts`): the root frame's
constructor judgment read at one constructor — its field telescope
positive at the block's own depth (no frames), U4 at the non-ordinary
fields, its result (the member's hole) applied to hole-free indices. -/
@[expose] def MemberCtorD (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (nF : Nat)
    (crest : Expr) (ks : List NestFieldKind) (tyN : Expr) (ts : List PosTree) : Prop :=
  ∃ nds cur, PosD ops env ctx (.tele [] (ctx.hiAt 0) nF 0 crest ks nds cur) ts ∧
    tyN = closeTelescope nds (ctx.hiAt 0) cur ∧
    ((List.range nF).any fun i =>
      ks.getD i .ordinary != .ordinary && structUsedLater tyN 0 i) = false ∧
    nestResHead cur = true ∧
    cur.getAppArgs.all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true

end ConLeche
