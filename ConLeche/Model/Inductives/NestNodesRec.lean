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

/-- **The frame facts of a node table** at a model of the table's
environment: every cached node's frame is monotone (`FrameMonoK`, the carriers
grow and the hole fits transfer) and, at a positive level, accessible
(`FrameAccJK`).  At a RE-RUN of the key-named check at the later environment
(DESIGN "PRIMREC / NESTKN-M6", route R) this is the whole consumer. -/
theorem NodeTableK.frameMono {env : Env} {ctx : NestCtx} {F : Nat} {cache : List NodeK}
    (h : NodeTableK (fueledOps .verified F) env ctx
      (ConLeche.UseOkK (fueledOps .verified F) env ctx) cache)
    {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {φ : Name → Nat}
    (hin : RulesInputs V mp.base2 φ) {nd : NodeK} (hnd : nd ∈ cache) :
    ∃ kn lo, NodeTieK nd kn lo ∧ FrameMonoK mp φ ctx kn lo nd.met ∧
      ∀ w, w ≠ 0 → FrameAccJK mp φ w ctx kn lo nd.met := by
  obtain ⟨kn, lo, hd, htie⟩ := h nd hnd
  exact ⟨kn, lo, htie, posDK_monoOk mp hin hd, fun w hw => posDK_accOk mp hin hw hd⟩

/-- **(c) The frame facts at a model of the walk's environment** (the record's
table, `NodeTableK.frameMono`). -/
theorem NestNodesAt.frameMono {env : Env} {names : List Name} {E : Env} {ctx : NestCtx}
    {F : Nat} {holes : List Expr} {css : List (List (ConstantVal × Nat))} {st : NestStK}
    (h : NestNodesAt env names E ctx F holes css st) {μ : ConLeche.CheckMode}
    (mp : EnvModelM V μ E) {φ : Name → Nat} (hin : RulesInputs V mp.base2 φ)
    {nd : NodeK} (hnd : nd ∈ st.cache.toList) :
    ∃ kn lo, NodeTieK nd kn lo ∧ FrameMonoK mp φ ctx kn lo nd.met ∧
      ∀ w, w ≠ 0 → FrameAccJK mp φ w ctx kn lo nd.met :=
  h.table.frameMono mp hin hnd

/-! ## (c) Moving a node's frame fact to a later model -/

section Move

variable {μ μ' : ConLeche.CheckMode}

/-- **The terms a node's frame fact reads** (`FrameMonoK`'s hypotheses): its
`DsF`, its families' keys' parameters, and the annotations of their leaves. -/
@[expose] def FrameMatK (lo : LayoutOutK) (y : Expr) : Prop :=
  y ∈ lo.L.dsF ∨ (∃ p ∈ lo.L.fams, y ∈ p.1.ds) ∨
    ∃ x, (x ∈ lo.L.dsF ∨ ∃ p ∈ lo.L.fams, x ∈ p.1.ds) ∧ ∃ l ∈ x.fvarLeaves, y = l.2

/-- `nestInstType` reads the context's lookup at the key's container only. -/
theorem nestInstType_atEnv {ctx : NestCtx} {f : Name → Option ConstantInfo}
    {cs : List ConstantInfo} {hi : Nat} {key : NestKey} (h : f key.cname = ctx.find? key.cname) :
    ConLeche.nestInstType (m := CheckM) (ctx.atEnv f cs) hi key =
      ConLeche.nestInstType ctx hi key := by
  simp only [ConLeche.nestInstType, ConLeche.NestCtx.atEnv, h]

/-- A successful `nestInstType` found its container stored. -/
theorem nestInstType_find {ctx : NestCtx} {hi : Nat} {key : NestKey} {r : Nat × Expr}
    (h : ConLeche.nestInstType (m := CheckM) ctx hi key = .ok r) :
    ∃ ci, ctx.find? key.cname = some ci := by
  cases hf : ctx.find? key.cname with
  | some ci => exact ⟨ci, rfl⟩
  | none =>
    simp [ConLeche.nestInstType, hf, ConLeche.unwrapOr, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h

/-- A context's reading moves backwards along a reading tie. -/
theorem CtxOkP.move {env env' : Env} {m : EnvModel V env} {m' : EnvModel V env'}
    {φ : Name → Nat} {d : Nat} {Δa : List AnnotTerm} {e : Expr}
    (h : CtxOkP m' φ d Δa e)
    (hr : ∀ l ∈ e.fvarLeaves, ∀ ea, denoteMeta m'.acval env' φ l.1 l.2 = some ea →
      denoteMeta m.acval env φ l.1 l.2 = some ea) :
    CtxOkP m φ d Δa e := by
  refine ⟨h.1, fun l hl => ?_⟩
  obtain ⟨h1, h2, tl, Aa, htl, rest⟩ := h.2 l hl
  exact ⟨h1, h2, tl, Aa, hr l hl tl htl, rest⟩

theorem DenoteMetaSpine.move {env env' : Env} {acval acval' : Name → (Name → Nat) → AnnotTerm}
    {φ : Name → Nat} {d : Nat} :
    ∀ {xs : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval' env' φ d xs vs →
      (∀ x ∈ xs, ∀ ea, denoteMeta acval' env' φ d x = some ea →
        denoteMeta acval env φ d x = some ea) →
      DenoteMetaSpine acval env φ d xs vs
  | _, _, .nil, _ => .nil
  | _, _, .cons hx hs, hr =>
    .cons (hr _ List.mem_cons_self _ hx) (DenoteMetaSpine.move hs fun y hy => hr y (List.mem_cons_of_mem _ hy))

/-- A hole relation at a node's BASE does not read the model (its own
group is empty) nor the context's environment. -/
theorem HoleRelK.baseMove {env env' : Env} {m : EnvModel V env} {m' : EnvModel V env'}
    {φ : Name → Nat} {ctx : NestCtx} {f : Name → Option ConstantInfo} {cs : List ConstantInfo}
    {L : LayoutK} {met : List Nat} {d : Nat} {Δa : List AnnotTerm} {R : FrameRel V}
    (h : HoleRelK m' φ (ctx.atEnv f cs) (layoutBaseK (ctx.atEnv f cs) L) met d Δa R) :
    HoleRelK m φ ctx (layoutBaseK ctx L) met d Δa R where
  hiEq := h.hiEq
  dom := h.dom
  agree := h.agree
  member := h.member
  fam := h.fam
  own := fun g n hg => by simp at hg
  dsScoped := h.dsScoped

/-- **(c) A node's frame fact at a LATER model**, from the fact at a model of
the walk's environment `E`: given coverage at `E`, lookups kept, every
later-recorded block holding the node's head recorded at `E`, the
containers of `E`'s names unchanged, and the node's material read alike
(later reading ⇒ the same reading at `E`).  The context is the walk's, read at
the later environment (`NestCtx.atEnv`). -/
theorem FrameMonoK.move {E env' : Env} {mpE : EnvModelM V μ E} {mp' : EnvModelM V μ' env'}
    {φ : Name → Nat} {ctx : NestCtx} {kn : NestKey} {lo : LayoutOutK} {met : List Nat}
    (h : FrameMonoK mpE φ ctx kn lo met) (hcov : ContCover mpE ctx)
    (hfwd : FindPreserved E env')
    (hblk : ∀ D ∈ mp'.lfpBlocks, ∀ mm, mm < D.k → D.member mm = ((grpOfK lo).headD default).1 →
      D ∈ mpE.lfpBlocks)
    (hcont : ConLeche.nestContainer (ctx.atEnv env'.find? env'.consts)
      ((grpOfK lo).headD default).1 = ConLeche.nestContainer ctx ((grpOfK lo).headD default).1)
    (hread : ∀ y, FrameMatK lo y → ∀ d ea, denoteMeta mp'.base2.acval env' φ d y = some ea →
      denoteMeta mpE.base2.acval E φ d y = some ea) :
    FrameMonoK mp' φ (ctx.atEnv env'.find? env'.consts) kn lo met := by
  intro _ hkC hkq D hD mm hmm hhead lps hlps hul hds dsa hdsa hlenP hnL Δh R₀ hR₀ hlay hΔ hCds
    hLds hfit
  have hDE := hblk D hD mm hmm hhead
  have hlpsE : ∀ mm', mm' < D.k → ∃ cv caps,
      E.find? (D.member mm') = some (.indInfo cv caps) ∧ cv.levelParams = lps := by
    intro mm' hmm'
    obtain ⟨cv, caps, hf⟩ := (mpE.lfp_ok D hDE).2.1.1 mm' hmm'
    obtain ⟨cv', caps', hf', hl⟩ := hlps mm' hmm'
    rw [hfwd hf] at hf'
    injection hf' with hf'
    injection hf' with h1 _
    exact ⟨cv, caps, hf, h1 ▸ hl⟩
  have hdsaE : DenoteMetaSpine mpE.base2.acval E φ (ctx.hiAt 0 + lo.L.nF) lo.L.dsF dsa :=
    hdsa.move fun x hx ea hr => hread x (.inl hx) _ ea hr
  have hnLE : (∃ nP' L, ConLeche.nestContainer ctx (D.member mm) = some (nP', L) ∧ L ≠ []) ∨
      lps.Nodup := by
    rw [hhead, ← hcont, ← hhead]
    exact hnL
  have hleaf : ∀ x, (x ∈ lo.L.dsF ∨ ∃ p ∈ lo.L.fams, x ∈ p.1.ds) →
      ∀ l ∈ x.fvarLeaves, ∀ ea, denoteMeta mp'.base2.acval env' φ l.1 l.2 = some ea →
        denoteMeta mpE.base2.acval E φ l.1 l.2 = some ea :=
    fun x hx l hl ea hr => hread l.2 (.inr (.inr ⟨x, hx, l, hl, rfl⟩)) _ ea hr
  have hlayE : LaySiteK mpE.base2 φ ctx (layoutBaseK ctx lo.L) (ctx.hiAt 0 + lo.L.nF) Δh :=
    { keys := fun p hp x hx => by
        obtain ⟨h1, h2, h3, h4, xa, h5⟩ := hlay.keys p hp x hx
        exact ⟨h1, h2, h3, h4.move (hleaf x (.inr ⟨p, hp, hx⟩)), xa,
          hread x (.inr (.inl ⟨p, hp, hx⟩)) _ xa h5⟩
      dsF := fun x hx => (hlay.dsF x hx).move (hleaf x (.inl hx)) }
  obtain ⟨hnd, hg, hle, hfitT⟩ := h hcov hkC hkq hDE hmm hhead hlpsE hul hds hdsaE hlenP hnLE
    hR₀.baseMove hlayE hΔ (fun x hx => (hCds x hx).move (hleaf x (.inl hx))) hLds hfit
  refine ⟨hnd, ⟨hg.1, hg.2.1, fun p hp => ⟨(hg.2.2 p hp).1, ?_⟩⟩, hle, hfitT⟩
  obtain ⟨nI, hI⟩ := (hg.2.2 p hp).2
  obtain ⟨ci, hci⟩ := nestInstType_find hI
  refine ⟨nI, ?_⟩
  rw [nestInstType_atEnv (by rw [hci]; exact hfwd (by rw [← hcov.find]; exact hci))]
  exact hI

/-- The admissible items at a node's base do not read the context's
environment (the own-group disjunct is empty there). -/
theorem holeQK_base_atEnv {ctx : NestCtx} {f : Name → Option ConstantInfo}
    {cs : List ConstantInfo} {L : LayoutK} {met : List Nat} {d : Nat} :
    HoleQK (ctx.atEnv f cs) (layoutBaseK (ctx.atEnv f cs) L) met d =
      HoleQK ctx (layoutBaseK ctx L) met d := by
  funext i n
  simp [HoleQK, layoutBaseK, ConLeche.NestCtx.atEnv, ConLeche.NestCtx.hiAt]

/-- An accessibility hole relation at a node's BASE does not read the model
nor the context's environment. -/
theorem HoleRelAK.baseMove {env env' : Env} {m : EnvModel V env} {m' : EnvModel V env'}
    {φ : Name → Nat} {ctx : NestCtx} {f : Name → Option ConstantInfo} {cs : List ConstantInfo}
    {L : LayoutK} {met : List Nat} {d : Nat} {Δa : List AnnotTerm} {R : FrameRel V}
    (h : HoleRelAK m' φ (ctx.atEnv f cs) (layoutBaseK (ctx.atEnv f cs) L) met d Δa R) :
    HoleRelAK m φ ctx (layoutBaseK ctx L) met d Δa R where
  hiEq := h.hiEq
  dom := h.dom
  agree := h.agree
  own := fun g n hg => by simp at hg
  dsScoped := h.dsScoped
  symm := h.symm
  rich := by rw [← holeQK_base_atEnv (f := f) (cs := cs)]; exact h.rich
  lrefl := h.lrefl

/-- **(c) A node's accessibility frame fact at a LATER model** (the twin of
`FrameMonoK.move`, same premises). -/
theorem FrameAccJK.move {E env' : Env} {mpE : EnvModelM V μ E} {mp' : EnvModelM V μ' env'}
    {φ : Name → Nat} {w : Nat} {ctx : NestCtx} {kn : NestKey} {lo : LayoutOutK}
    {met : List Nat}
    (h : FrameAccJK mpE φ w ctx kn lo met) (hcov : ContCover mpE ctx)
    (hfwd : FindPreserved E env')
    (hblk : ∀ D ∈ mp'.lfpBlocks, ∀ mm, mm < D.k → D.member mm = ((grpOfK lo).headD default).1 →
      D ∈ mpE.lfpBlocks)
    (hcont : ConLeche.nestContainer (ctx.atEnv env'.find? env'.consts)
      ((grpOfK lo).headD default).1 = ConLeche.nestContainer ctx ((grpOfK lo).headD default).1)
    (hread : ∀ y, FrameMatK lo y → ∀ d ea, denoteMeta mp'.base2.acval env' φ d y = some ea →
      denoteMeta mpE.base2.acval E φ d y = some ea) :
    FrameAccJK mp' φ w (ctx.atEnv env'.find? env'.consts) kn lo met := by
  intro hok hkC hkq D hD mm hmm hhead lps hlps hul hds dsa hdsa hlenP hnL Δh R₀ hR₀ hlay hΔ hCds
    hLds hfit
  have hDE := hblk D hD mm hmm hhead
  have hlpsE : ∀ mm', mm' < D.k → ∃ cv caps,
      E.find? (D.member mm') = some (.indInfo cv caps) ∧ cv.levelParams = lps := by
    intro mm' hmm'
    obtain ⟨cv, caps, hf⟩ := (mpE.lfp_ok D hDE).2.1.1 mm' hmm'
    obtain ⟨cv', caps', hf', hl⟩ := hlps mm' hmm'
    rw [hfwd hf] at hf'
    injection hf' with hf'
    injection hf' with h1 _
    exact ⟨cv, caps, hf, h1 ▸ hl⟩
  have hdsaE : DenoteMetaSpine mpE.base2.acval E φ (ctx.hiAt 0 + lo.L.nF) lo.L.dsF dsa :=
    hdsa.move fun x hx ea hr => hread x (.inl hx) _ ea hr
  have hnLE : (∃ nP' L, ConLeche.nestContainer ctx (D.member mm) = some (nP', L) ∧ L ≠ []) ∨
      lps.Nodup := by
    rw [hhead, ← hcont, ← hhead]
    exact hnL
  have hleaf : ∀ x, (x ∈ lo.L.dsF ∨ ∃ p ∈ lo.L.fams, x ∈ p.1.ds) →
      ∀ l ∈ x.fvarLeaves, ∀ ea, denoteMeta mp'.base2.acval env' φ l.1 l.2 = some ea →
        denoteMeta mpE.base2.acval E φ l.1 l.2 = some ea :=
    fun x hx l hl ea hr => hread l.2 (.inr (.inr ⟨x, hx, l, hl, rfl⟩)) _ ea hr
  have hlayE : LaySiteK mpE.base2 φ ctx (layoutBaseK ctx lo.L) (ctx.hiAt 0 + lo.L.nF) Δh :=
    { keys := fun p hp x hx => by
        obtain ⟨h1, h2, h3, h4, xa, h5⟩ := hlay.keys p hp x hx
        exact ⟨h1, h2, h3, h4.move (hleaf x (.inr ⟨p, hp, hx⟩)), xa,
          hread x (.inr (.inl ⟨p, hp, hx⟩)) _ xa h5⟩
      dsF := fun x hx => (hlay.dsF x hx).move (hleaf x (.inl hx)) }
  obtain ⟨hnd, hg, hw, hout⟩ := h ⟨hcov, hok.2⟩ hkC hkq hDE hmm hhead hlpsE hul hds hdsaE hlenP
    hnLE hR₀.baseMove hlayE hΔ (fun x hx => (hCds x hx).move (hleaf x (.inl hx))) hLds hfit
  refine ⟨hnd, ⟨hg.1, hg.2.1, fun p hp => ⟨(hg.2.2 p hp).1, ?_⟩⟩, hw, ?_⟩
  · obtain ⟨nI, hI⟩ := (hg.2.2 p hp).2
    obtain ⟨ci, hci⟩ := nestInstType_find hI
    refine ⟨nI, ?_⟩
    rw [nestInstType_atEnv (by rw [hci]; exact hfwd (by rw [← hcov.find]; exact hci))]
    exact hI
  · rw [holeQK_base_atEnv]; exact hout

/-- **What moves a node's frame fact from the walk's model to a later one**
(`FrameMonoK.move`'s ties, at one node): the later-recorded blocks holding the
node's head are recorded at the walk's model, the head's container is
unchanged, and the node's material reads alike. -/
@[expose] def NodeMoveK {E env : Env} (mpE : EnvModelM V μ E) (mp : EnvModelM V μ' env)
    (φ : Name → Nat) (ctx : NestCtx) (lo : LayoutOutK) : Prop :=
  (∀ D ∈ mp.lfpBlocks, ∀ mm, mm < D.k → D.member mm = ((grpOfK lo).headD default).1 →
    D ∈ mpE.lfpBlocks) ∧
  ConLeche.nestContainer (ctx.atEnv env.find? env.consts) ((grpOfK lo).headD default).1 =
    ConLeche.nestContainer ctx ((grpOfK lo).headD default).1 ∧
  ∀ y, FrameMatK lo y → ∀ d ea, denoteMeta mp.base2.acval env φ d y = some ea →
    denoteMeta mpE.base2.acval E φ d y = some ea

/-- **(c) The record's frame facts at the LATER model** (route P): the walk's
facts at a model `mpE` of the walk's environment (coverage and the rules'
inputs there), moved along the record's lookup preservation and each cached
node's ties (`NodeMoveK`). -/
theorem NestNodesAt.frameMono_later {env : Env} {names : List Name} {E : Env} {ctx : NestCtx}
    {F : Nat} {holes : List Expr} {css : List (List (ConstantVal × Nat))} {st : NestStK}
    (h : NestNodesAt env names E ctx F holes css st)
    (mpE : EnvModelM V μ E) (mp : EnvModelM V μ' env) {φ : Name → Nat}
    (hin : RulesInputs V mpE.base2 φ) (hcov : ContCover mpE ctx)
    (hmove : ∀ nd ∈ st.cache.toList, ∀ kn lo, NodeTieK nd kn lo →
      PosDKH (fueledOps .verified F) E ctx (ConLeche.UseOkK (fueledOps .verified F) E ctx)
        (.node kn lo nd.met) → NodeMoveK mpE mp φ ctx lo)
    {nd : NodeK} (hnd : nd ∈ st.cache.toList) :
    ∃ kn lo, NodeTieK nd kn lo ∧
      FrameMonoK mp φ (ctx.atEnv env.find? env.consts) kn lo nd.met ∧
      ∀ w, w ≠ 0 → FrameAccJK mp φ w (ctx.atEnv env.find? env.consts) kn lo nd.met := by
  obtain ⟨kn, lo, hd, htie⟩ := h.table nd hnd
  obtain ⟨hb, hc, hr⟩ := hmove nd hnd kn lo htie hd
  exact ⟨kn, lo, htie, (posDK_monoOk mpE hin hd).move hcov (fun hf => h.fwd hf) hb hc hr,
    fun w hw => (posDK_accOk mpE hin hw hd).move hcov (fun hf => h.fwd hf) hb hc hr⟩

end Move

end ConLeche.Model
