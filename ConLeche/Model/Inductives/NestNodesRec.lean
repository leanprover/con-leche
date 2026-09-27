module

public import ConLeche.Model.Inductives.UseBridgeK
public import ConLeche.Model.Inductives.PosAccK
public import ConLeche.Verify.Inductives.PosDerivKInv
import ConLeche.Verify.Inductives.PosNfK
public import ConLeche.Verify.Inductives.HomeTie
public import ConLeche.Verify.EnvBound
public import ConLeche.Kernel.Basis.Names
import ConLeche.Model.Install

public section

/-!
# The key-named positivity table, persisted per block (PRIMREC / NESTKN-M6)

A LATER recursor check (an older nested home's hot classes, or the block's
own family read at a later environment) reads the key-named positivity facts
of a block installed EARLIER.  This module records them, proof-only, beside
the carrier (never in the checker's `Env`), and moves them along the fold.

* `NodeTableK ops env ctx hk cache` — every entry of a run's node cache
  carries its node's derivation at the hook `hk`, keyed by the entry's
  canonical key (`NodeK.key`), with the entry's fields tied to the node's
  layout (`NodeTieK`).  `DerivCacheK`'s second half is this table at the
  trivial hook (`DerivCacheK.table`); PRIMREC / NESTKN-M3B concludes it at
  the hook `UseOkK`.
* `NestNodesAt env names E ctx F holes css st` — the block `names` ran its
  key-named positivity check at the environment `E` (its formers consed,
  the walk's environment) and context `ctx`, the run's final state is `st`,
  its table holds at `UseOkK`, and the CURRENT environment `env` extends `E`
  as a suffix (so `env.prefixTo |E|` IS `E`) preserving every lookup.
  `NestNodesRec env names` hides `E ctx F holes css st`.
* `NodesCover mp` — every recorded block of the carrier has its record, or
  is a basis block (its names reserved; basis blocks are flat).  A proof-only
  invariant beside `LfpCover` (not a field of it: the live install runs the
  path-framed positivity check, so no live `addLfp` site could supply it —
  it joins `LfpCover` at the switch).  Transport: `NodesCover.ext` (the
  recorded list kept, a suffix extension preserving lookups — the cons
  funnel and `BlockCover`'s append), `NodesCover.addLfp`.

The consumers (`NestNodesAt.layout_prefix`, `NestNodesAt.frameMono`):
the recorded layout of a cached node is `nestLayoutK` at the LATER
environment's prefix view `env.prefixTo |E|` (the same function at the same
arguments: no env tie), and at every model OF `E` the node's frame facts
hold (`FrameMonoK`, `FrameAccJK`).  Moving the frame facts to a model of
the later environment is the open half (DESIGN "PRIMREC / NESTKN-M6").
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo CheckM NestCtx NestKey LayoutK
  LayoutOutK NodeK NestStK UseHookK PosDKH fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The node table at a hook -/

/-- A cache entry's fields are its node's layout's (`DerivCacheK`'s ties). -/
@[expose] def NodeTieK (nd : NodeK) (kn : NestKey) (lo : LayoutOutK) : Prop :=
  nd.key.cname ∈ lo.ginfo.map (·.1) ∧ nd.key.lvls = kn.lvls ∧ nd.key.ds = kn.ds ∧
    nd.dsF = lo.L.dsF ∧ nd.nF = lo.L.nF ∧ nd.merged = lo.merged ∧
    nd.famKeys = lo.L.fams.map (·.1) ∧ nd.famPs = lo.famPs ∧
    nd.famTys = lo.L.famTys ∧ nd.famNIs = lo.L.fams.map (·.2)

/-- **The node table of a run's cache at a hook**: every entry carries its
node's derivation (`.node kn lo nd.met`) and is tied to that node's layout. -/
@[expose] def NodeTableK (ops : ConLeche.CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (hk : UseHookK) (cache : List NodeK) : Prop :=
  ∀ nd ∈ cache, ∃ kn lo, PosDKH ops env ctx hk (.node kn lo nd.met) ∧ NodeTieK nd kn lo

/-- `DerivCacheK`'s table is the node table at the trivial hook. -/
theorem DerivCacheK.table {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {st : NestStK} (h : ConLeche.DerivCacheK ops env ctx st) :
    NodeTableK ops env ctx ConLeche.trivHookK st.cache.toList :=
  fun nd hnd => h.2 nd hnd

/-- A cached node, looked up by its key, is a table entry. -/
theorem NodeTableK.find {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {hk : UseHookK} {st : NestStK} (h : NodeTableK ops env ctx hk st.cache.toList)
    {k : NestKey} {nd : NodeK} (hf : st.node? k = some nd) :
    nd.key = k ∧ ∃ kn lo, PosDKH ops env ctx hk (.node kn lo nd.met) ∧ NodeTieK nd kn lo := by
  unfold NestStK.node? at hf
  rw [← Array.find?_toList] at hf
  refine ⟨?_, h nd (List.mem_of_find?_eq_some hf)⟩
  have := List.find?_some hf
  simpa using this

/-! ## The record -/

/-- **A block's key-named positivity record** (see the module docstring). -/
structure NestNodesAt (env : Env) (names : List Name) (E : Env) (ctx : NestCtx) (F : Nat)
    (holes : List Expr) (css : List (List (ConstantVal × Nat))) (st : NestStK) : Prop where
  /-- the current environment extends the walk's as a suffix -/
  suffix : ∃ new, env.consts = new ++ E.consts
  /-- every lookup of the walk's environment survives -/
  fwd : FindPreserved E env
  /-- the walk's context reads the walk's environment -/
  find : ctx.find? = E.find?
  consts : ctx.consts = E.consts
  /-- the walk's context is the block's -/
  names : ctx.names = names
  /-- the key-named check ran at the walk's environment, ending at `st` -/
  run : ∃ ksss nsss, ConLeche.nestBlockCtorsGoK (fueledOps .verified F) E ctx holes css {} =
    .ok (ksss, nsss, st)
  /-- every cached node's derivation, at the hook the model reads -/
  table : NodeTableK (fueledOps .verified F) E ctx
    (ConLeche.UseOkK (fueledOps .verified F) E ctx) st.cache.toList

/-- **A block's record**, its walk hidden. -/
@[expose] def NestNodesRec (env : Env) (names : List Name) : Prop :=
  ∃ (E : Env) (ctx : NestCtx) (F : Nat) (holes : List Expr)
    (css : List (List (ConstantVal × Nat))) (st : NestStK),
    NestNodesAt env names E ctx F holes css st

/-- **(b) The record at the install** — the key-named check's run at the walk's
environment `E` (formers consed) and the table of its final state at the hook
`UseOkK` (the inversion at the hook, PRIMREC / NESTKN-M3B, supplies `htab`
from `hrun`), read at `E` itself. -/
theorem nestNodesAt_install {E : Env} {ctx : NestCtx} {F : Nat} {names : List Name}
    {holes : List Expr} {css : List (List (ConstantVal × Nat))}
    {ksss : List (List (List ConLeche.NestFieldKind))} {nsss : List (List Expr)} {st : NestStK}
    (hrun : ConLeche.nestBlockCtorsGoK (fueledOps .verified F) E ctx holes css {} =
      .ok (ksss, nsss, st))
    (htab : NodeTableK (fueledOps .verified F) E ctx
      (ConLeche.UseOkK (fueledOps .verified F) E ctx) st.cache.toList)
    (hfind : ctx.find? = E.find?) (hcs : ctx.consts = E.consts) (hnames : ctx.names = names) :
    NestNodesAt E names E ctx F holes css st where
  suffix := ⟨[], rfl⟩
  fwd := fun h => h
  find := hfind
  consts := hcs
  names := hnames
  run := ⟨ksss, nsss, hrun⟩
  table := htab

/-- `nestBlockCtorsK`'s run, as the record's (`nestBlockCtorsK` returns only the
final state's `base`; its `GoK` run is inside). -/
theorem nestBlockCtorsK_runGo {ops : ConLeche.CheckerOps CheckM} {E : Env} {ctx : NestCtx}
    {holes : List Expr} {css : List (List (ConstantVal × Nat))}
    {ksss : List (List (List ConLeche.NestFieldKind))} {nsss : List (List Expr)}
    {base : ConLeche.NestState}
    (h : ConLeche.nestBlockCtorsK (m := CheckM) ops E ctx holes css = .ok (ksss, nsss, base)) :
    ∃ st : NestStK, st.base = base ∧
      ConLeche.nestBlockCtorsGoK ops E ctx holes css {} = .ok (ksss, nsss, st) := by
  simp only [ConLeche.nestBlockCtorsK, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨ksss₁, nsss₁, st⟩ := r
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨st, rfl, hr⟩

/-- **Transport** of one record to an extension that keeps the walk's
environment a suffix and every lookup. -/
theorem NestNodesAt.ext {env env' : Env} {names : List Name} {E : Env} {ctx : NestCtx} {F : Nat}
    {holes : List Expr} {css : List (List (ConstantVal × Nat))} {st : NestStK}
    (h : NestNodesAt env names E ctx F holes css st)
    (hsuf : ∃ new, env'.consts = new ++ env.consts) (hfwd : FindPreserved env env') :
    NestNodesAt env' names E ctx F holes css st where
  suffix := by
    obtain ⟨n₁, h₁⟩ := h.suffix
    obtain ⟨n₂, h₂⟩ := hsuf
    exact ⟨n₂ ++ n₁, by rw [h₂, h₁, List.append_assoc]⟩
  fwd := fun hf => hfwd (h.fwd hf)
  find := h.find
  consts := h.consts
  names := h.names
  run := h.run
  table := h.table

theorem NestNodesRec.ext {env env' : Env} {names : List Name} (h : NestNodesRec env names)
    (hsuf : ∃ new, env'.consts = new ++ env.consts) (hfwd : FindPreserved env env') :
    NestNodesRec env' names := by
  obtain ⟨E, ctx, F, holes, css, st, h⟩ := h
  exact ⟨E, ctx, F, holes, css, st, h.ext hsuf hfwd⟩

/-! ## The invariant beside the carrier -/

section Cover

variable {μ : ConLeche.CheckMode}

/-- **Every recorded block has its key-named positivity record**, or is a
basis block (every name reserved: the basis installs pin flat blocks and run
no walk). -/
@[expose] def NodesCover {env : Env} (mp : EnvModelM V μ env) : Prop :=
  ∀ D ∈ mp.lfpBlocks, NestNodesRec env D.names ∨ ∀ n ∈ D.names, n ∈ ConLeche.reservedBasisNames

theorem nodesCover_empty : NodesCover (EnvModelM.empty V μ) :=
  fun _ hD => nomatch hD

/-- **Transport** across an extension keeping the recorded list: the
environment grows by a suffix, every lookup kept (the cons funnel: a fresh
cons; `BlockCover`: an append). -/
theorem NodesCover.ext {env env' : Env} {mp : EnvModelM V μ env} {mp' : EnvModelM V μ env'}
    (h : NodesCover mp) (hL : mp'.lfpBlocks = mp.lfpBlocks)
    (hsuf : ∃ new, env'.consts = new ++ env.consts) (hfwd : FindPreserved env env') :
    NodesCover mp' := by
  intro D hD
  rw [hL] at hD
  exact (h D hD).imp (fun hr => hr.ext hsuf hfwd) id

/-- A fresh cons keeping the recorded list. -/
theorem NodesCover.cons {env : Env} {mp : EnvModelM V μ env} {c₀ : ConstantInfo}
    {mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩} (h : NodesCover mp)
    (hfresh : env.find? c₀.name = none) (hL : mp'.lfpBlocks = mp.lfpBlocks) :
    NodesCover mp' :=
  h.ext hL ⟨[c₀], rfl⟩ (fun hf => findPreserved_cons hfresh hf)

/-- **The block's record** (`EnvModelM.addLfp`): the new block brings its
record (a uniform install) or is a basis block. -/
theorem NodesCover.addLfp {env : Env} {mp : EnvModelM V μ env} (h : NodesCover mp)
    (D : LfpDatum V) (hL) (hst) (hrd) (hrdC) (hlic)
    (hD : NestNodesRec env D.names ∨ ∀ n ∈ D.names, n ∈ ConLeche.reservedBasisNames) :
    NodesCover (mp.addLfp D hL hst hrd hrdC hlic) := by
  intro D' hD'
  rcases List.mem_cons.mp hD' with rfl | h'
  · exact hD
  · exact h D' h'

/-- The record of a recorded block that is not a basis block. -/
theorem NodesCover.rec {env : Env} {mp : EnvModelM V μ env} (h : NodesCover mp)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {n : Name} (hn : n ∈ D.names)
    (hnb : n ∉ ConLeche.reservedBasisNames) : NestNodesRec env D.names :=
  (h D hD).resolve_right fun hall => hnb (hall n hn)

end Cover

/-! ## (c) The consumers -/

/-- The walk's context at the walk's environment is the recorded one. -/
theorem NestNodesAt.ctx_atEnv {env : Env} {names : List Name} {E : Env} {ctx : NestCtx}
    {F : Nat} {holes : List Expr} {css : List (List (ConstantVal × Nat))} {st : NestStK}
    (h : NestNodesAt env names E ctx F holes css st) : ctx.atEnv E.find? E.consts = ctx := by
  cases ctx
  simp only [ConLeche.NestCtx.atEnv, ConLeche.NestCtx.mk.injEq]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, h.find.symm, h.consts.symm⟩

/-- The later environment's prefix view at the walk's length is the walk's
environment. -/
theorem NestNodesAt.prefix_eq {env : Env} {names : List Name} {E : Env} {ctx : NestCtx}
    {F : Nat} {holes : List Expr} {css : List (List (ConstantVal × Nat))} {st : NestStK}
    (h : NestNodesAt env names E ctx F holes css st) : env.prefixTo E.consts.length = E := by
  obtain ⟨new, hn⟩ := h.suffix
  exact Env.prefixTo_of_extends hn

/-- **(c) The layout, recomputed at the later environment's prefix view**: for
every cached node (looked up by its key), `nestLayoutK` at the later
environment's prefix of the walk's length, with the walk's context read
there, is the recorded node's layout — the same function at the same
arguments — and the node carries its derivation. -/
theorem NestNodesAt.layout_prefix {env : Env} {names : List Name} {E : Env} {ctx : NestCtx}
    {F : Nat} {holes : List Expr} {css : List (List (ConstantVal × Nat))} {st : NestStK}
    (h : NestNodesAt env names E ctx F holes css st) {k : NestKey} {nd : NodeK}
    (hf : st.node? k = some nd) :
    nd.key = k ∧ ∃ kn lo, NodeTieK nd kn lo ∧
      (let Ev := env.prefixTo E.consts.length
       let ctxv := ctx.atEnv Ev.find? Ev.consts
       ConLeche.nestLayoutK (fueledOps .verified F) Ev ctxv (ConLeche.nestContainer ctxv) kn =
         .ok lo) ∧
      PosDKH (fueledOps .verified F) E ctx (ConLeche.UseOkK (fueledOps .verified F) E ctx)
        (.node kn lo nd.met) := by
  obtain ⟨hk, kn, lo, hd, htie⟩ := h.table.find hf
  refine ⟨hk, kn, lo, htie, ?_, hd⟩
  simp only
  rw [h.prefix_eq, h.ctx_atEnv]
  exact (ConLeche.posDK_node_nf hd).1

/-- **(c) The frame facts at a model of the walk's environment**: every
cached node's frame is monotone (`FrameMonoK`, the carriers grow and the hole
fits transfer) and, at a positive level, accessible (`FrameAccJK`). -/
theorem NestNodesAt.frameMono {env : Env} {names : List Name} {E : Env} {ctx : NestCtx}
    {F : Nat} {holes : List Expr} {css : List (List (ConstantVal × Nat))} {st : NestStK}
    (h : NestNodesAt env names E ctx F holes css st) {μ : ConLeche.CheckMode}
    (mp : EnvModelM V μ E) {φ : Name → Nat} (hin : RulesInputs V mp.base2 φ)
    {nd : NodeK} (hnd : nd ∈ st.cache.toList) :
    ∃ kn lo, NodeTieK nd kn lo ∧ FrameMonoK mp φ ctx kn lo nd.met ∧
      ∀ w, w ≠ 0 → FrameAccJK mp φ w ctx kn lo nd.met := by
  obtain ⟨kn, lo, hd, htie⟩ := h.table nd hnd
  exact ⟨kn, lo, htie, posDK_monoOk mp hin hd, fun w hw => posDK_accOk mp hin hw hd⟩

end ConLeche.Model
