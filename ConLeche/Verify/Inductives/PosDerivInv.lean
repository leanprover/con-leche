module

public import ConLeche.Verify.Inductives.PosDerivFun
public import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.NestContInv
public import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Inductives.StructWF

public section

/-!
# The positivity run, inverted ONCE into the derivation (lane POSDERIV)

`nestPos_deriv`: a successful run of the positivity function (any fuel,
any `ops` whose whnf keeps terms well scoped) yields the derivation
`PosD` of its input, and a successful syntactic pass (`nestSyn`) the
derivation of its frames.  This file is the only place that reads the
run: its cache and its fuel stay here.

The run's state carries the invariant `DerivCache`: every container
lookup is the environment's (`nestContainer`), and every cached
instantiation below the frame holes has a frame derivation under some
well-scoped frame stack (`KeyD`) — the premise of the derivation's
`contHit` rule.  The run's well-scopedness (`ProgScoped`, `WScoped` of
each walked term) is threaded alongside, because a cache hit's frame was
derived under the frames of its first walk.
-/

-- the throw-branch closers are tried at every split; some are unused
set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-! ## The run's invariant -/

/-- **A cached instantiation, derived**: its frame, at the EMPTY frame
stack (a key below every frame hole is walked there), with the key's
container in the frame's group. -/
@[expose] def KeyD (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (key : NestKey) : Prop :=
  ∃ grp ts, PosD ops env ctx (.frame [] key.lvls key.ds grp) ts ∧ key.cname ∈ grp.map (·.1)

/-- **The run's state invariant**: the container lookups are the
environment's, and every cached instantiation whose parameters lie below
the frame holes is derived. -/
@[expose] def DerivCache (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (st : NestState) :
    Prop :=
  (∀ c r, st.ctorsOf.lookup c = some r → r = nestContainer ctx c) ∧
  ∀ ki ∈ st.keys.toList, (∀ x ∈ ki.key.ds, x.fvarB ≤ ctx.hiAt 0) →
    KeyDR ops env ctx st.ctorNfs.toList ki.key

theorem derivCache_empty : DerivCache ops env ctx {} :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

/-- The invariant survives a state that only records more constructors. -/
theorem DerivCache.grow {st st' : NestState} (h : DerivCache ops env ctx st)
    (hco : st'.ctorsOf = st.ctorsOf) (hk : st'.keys = st.keys)
    (hc : ∀ e ∈ st.ctorNfs.toList, e ∈ st'.ctorNfs.toList) : DerivCache ops env ctx st' :=
  ⟨fun c r hl => h.1 c r (hco ▸ hl), fun ki hki hfv => (h.2 ki (hk ▸ hki) hfv).mono hc⟩

theorem DerivCache.lookup {st : NestState} (h : DerivCache ops env ctx st) (c : Name) :
    (nestContainerC ctx st c).1 = nestContainer ctx c := by
  unfold nestContainerC
  split
  · rename_i r hr; exact h.1 c r hr
  · rfl

theorem DerivCache.insert {st : NestState} (h : DerivCache ops env ctx st) (c : Name) :
    DerivCache ops env ctx (nestContainerC ctx st c).2 := by
  unfold nestContainerC
  split
  · exact h
  · refine ⟨fun c' r hl => ?_, h.2⟩
    simp only [List.lookup] at hl
    split at hl
    · rename_i heq
      simp only [Option.some.injEq] at hl
      rw [← hl]
      congr 1
      exact (beq_iff_eq.mp heq).symm
    · exact h.1 c' r hl

/-! ## The recorded classes (the major → node tie's run half)

The run records the CLASSES of every node it meets (`NestState.nodes`,
`NestCtx.concreteKey`).  `NodesIn st st' ts`: the run from `st` to `st'`
appended classes of nodes of the forest `ts` only. -/

/-- A class of a node of the forest `ts`: a member of its group at its
instantiation, the holes of its occurrence back to their constants. -/
@[expose] def NodeOf (ctx : NestCtx) (ts : List PosTree) (k : NestKey) : Prop :=
  ∃ t ∈ PosTree.forest ts, ∃ c ∈ t.grp.map (·.1), ctx.concreteKey t.occ c t.key = k

/-- The run from `st` to `st'` recorded classes of the forest `ts` only,
and constructors only on top (K.53′), and every node of `ts` has its frame
recorded at `st'`. -/
@[expose] def NodesIn (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (st st' : NestState)
    (ts : List PosTree) : Prop :=
  (∃ new : List NestKey, st'.nodes.toList = st.nodes.toList ++ new ∧ ∀ k ∈ new, NodeOf ctx ts k) ∧
  (∃ newC : List NestCtorNf, st'.ctorNfs.toList = st.ctorNfs.toList ++ newC) ∧
  TreeRec ops env ctx st'.ctorNfs.toList ts

theorem NodesIn.nil {st st' : NestState} (h : st'.nodes = st.nodes)
    (hc : st'.ctorNfs = st.ctorNfs) : NodesIn ops env ctx st st' [] :=
  ⟨⟨[], by simp [h], fun _ hk => nomatch hk⟩, ⟨[], by simp [hc]⟩, TreeRec.nil _⟩

theorem NodesIn.of_eq_left {st st₁ st' : NestState} {ts : List PosTree}
    (h : st₁.nodes = st.nodes) (hc : st₁.ctorNfs = st.ctorNfs)
    (h' : NodesIn ops env ctx st₁ st' ts) : NodesIn ops env ctx st st' ts := by
  obtain ⟨⟨n, e, a⟩, ⟨nc, ec⟩, hr⟩ := h'
  exact ⟨⟨n, by rw [e, h], a⟩, ⟨nc, by rw [ec, hc]⟩, hr⟩

/-- A later state that records more constructors (and no class). -/
theorem NodesIn.grow {st st₁ st' : NestState} {ts : List PosTree}
    (h' : NodesIn ops env ctx st st₁ ts) (h : st'.nodes = st₁.nodes)
    (hc : ∃ l, st'.ctorNfs.toList = st₁.ctorNfs.toList ++ l) : NodesIn ops env ctx st st' ts := by
  obtain ⟨⟨n, e, a⟩, ⟨nc, ec⟩, hr⟩ := h'
  obtain ⟨l, hl⟩ := hc
  exact ⟨⟨n, by rw [h, e], a⟩, ⟨nc ++ l, by rw [hl, ec, List.append_assoc]⟩,
    hr.mono fun x hx => by rw [hl]; exact List.mem_append_left _ hx⟩

theorem NodesIn.of_eq_right {st st₁ st' : NestState} {ts : List PosTree}
    (h' : NodesIn ops env ctx st st₁ ts) (h : st'.nodes = st₁.nodes)
    (hc : st'.ctorNfs = st₁.ctorNfs) : NodesIn ops env ctx st st' ts :=
  h'.grow h ⟨[], by simp [hc]⟩

theorem NodesIn.trans {st st₁ st₂ : NestState} {ts₁ ts₂ : List PosTree}
    (h₁ : NodesIn ops env ctx st st₁ ts₁) (h₂ : NodesIn ops env ctx st₁ st₂ ts₂) :
    NodesIn ops env ctx st st₂ (ts₁ ++ ts₂) := by
  obtain ⟨⟨n₁, e₁, a₁⟩, ⟨c₁, f₁⟩, r₁⟩ := h₁
  obtain ⟨⟨n₂, e₂, a₂⟩, ⟨c₂, f₂⟩, r₂⟩ := h₂
  refine ⟨⟨n₁ ++ n₂, by rw [e₂, e₁, List.append_assoc], fun k hk => ?_⟩,
    ⟨c₁ ++ c₂, by rw [f₂, f₁, List.append_assoc]⟩,
    (r₁.mono fun x hx => by rw [f₂]; exact List.mem_append_left _ hx).append r₂⟩
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨t, ht, rest⟩ := a₁ k hk
    exact ⟨t, PosTree.mem_forest_append.mpr (Or.inl ht), rest⟩
  · obtain ⟨t, ht, rest⟩ := a₂ k hk
    exact ⟨t, PosTree.mem_forest_append.mpr (Or.inr ht), rest⟩

/-- A node's own forest holds its frame's nodes. -/
theorem PosTree.forest_kids_sub {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree} :
    ∀ t ∈ PosTree.forest ts, t ∈ PosTree.forest [.node occ anc key grp ts] := by
  intro t ht
  simp only [PosTree.forest, List.append_nil]
  exact PosTree.mem_nodes.mpr (Or.inr ht)

theorem PosTree.self_mem_forest {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree} :
    PosTree.node occ anc key grp ts ∈ PosTree.forest [.node occ anc key grp ts] := by
  simp only [PosTree.forest, List.append_nil]
  exact PosTree.mem_nodes.mpr (Or.inl rfl)

/-- **A walked node's classes recorded**: its whole group at its key; its
frame's constructors recorded. -/
theorem NodesIn.walked {st st₁ : NestState} {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree} (h : NodesIn ops env ctx st st₁ ts)
    (hf : FrameRec ops env ctx st₁.ctorNfs.toList anc key.lvls key.ds grp) :
    NodesIn ops env ctx st { st₁ with nodes := st₁.nodes ++
      (grp.map fun p => ctx.concreteKey occ p.1 key).toArray } [.node occ anc key grp ts] := by
  obtain ⟨⟨n, e, a⟩, hc, hr⟩ := h
  refine ⟨⟨n ++ grp.map fun p => ctx.concreteKey occ p.1 key, ?_, fun k hk => ?_⟩, hc,
    TreeRec.node hf hr⟩
  · simp [e]
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨t, ht, rest⟩ := a k hk
    exact ⟨t, PosTree.forest_kids_sub t ht, rest⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    exact ⟨_, PosTree.self_mem_forest, p.1, List.mem_map_of_mem hp, rfl⟩

/-- **A hit's class recorded**: its own container; its (cached) frame and
nodes recorded already. -/
theorem NodesIn.hit {st : NestState} {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree} (hmem : key.cname ∈ grp.map (·.1))
    (hf : FrameRec ops env ctx st.ctorNfs.toList anc key.lvls key.ds grp)
    (hts : TreeRec ops env ctx st.ctorNfs.toList ts) :
    NodesIn ops env ctx st { st with nodes := st.nodes.push (ctx.concreteKey occ key.cname key) }
      [.node occ anc key grp ts] := by
  refine ⟨⟨[ctx.concreteKey occ key.cname key], by simp, fun k hk => ?_⟩, ⟨[], by simp⟩,
    TreeRec.node hf hts⟩
  simp only [List.mem_singleton] at hk
  subst hk
  exact ⟨_, PosTree.self_mem_forest, key.cname, hmem, rfl⟩

/-- **The inversion's claim about a walk function** (the positivity
function, or its recursive call one fuel lower). -/
@[expose] def RunDeriv (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState) (k : NestFieldKind)
    (nf : Expr) (st' : NestState),
    rec prog dep kb e st = .ok (k, nf, st') →
    ctx.hiAt prog.length ≤ dep → WScoped dep e → ProgScoped ctx prog →
    DerivCache ops env ctx st →
    DerivCache ops env ctx st' ∧
      ∃ ts, PosD ops env ctx (.field prog dep kb e k.erase nf) ts ∧ NodesIn ops env ctx st st' ts

/-- **The inversion's claim about a syntactic pass** (`nestSyn`, or its
recursive call one fuel lower). -/
@[expose] def SynDeriv (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState) : Prop :=
  ∀ (prog : List NestHole) (skip : List NestKey) (e : Expr) (st st' : NestState) (d : Nat),
    syn prog skip e st = .ok st' → WScoped d e → ProgScoped ctx prog → DerivCache ops env ctx st →
    DerivCache ops env ctx st' ∧ ∃ ts, PosD ops env ctx (.syn prog e) ts ∧ NodesIn ops env ctx st st' ts

/-! ## Scoping -/

theorem ProgScoped.nil : ProgScoped ctx [] := fun i hk h => by simp at h

/-- The frames grown by a frame's new entries stay well scoped. -/
theorem ProgScoped.push {prog : List NestHole} (hsc : ProgScoped ctx prog) {us : List Level}
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x)
    (grp : List (Name × Expr)) :
    ProgScoped ctx ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog) := by
  intro i hk h x hx
  have hle : ctx.hiAt prog.length ≤
      ctx.hiAt ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog).length := by
    simp only [NestCtx.hiAt, List.length_append]; omega
  rw [List.reverse_append, List.reverse_reverse] at h
  rcases Nat.lt_or_ge i prog.reverse.length with hi | hi
  · rw [List.getElem?_append_left hi] at h
    exact WScoped.mono hle (hsc i hk h x hx)
  · rw [List.getElem?_append_right hi] at h
    obtain ⟨p, -, rfl⟩ : ∃ p ∈ grp, hk = { key := ⟨p.1, us, ds⟩, base := ctx.hiAt prog.length } := by
      have := List.mem_of_getElem? h
      simp only [grpNews, List.mem_map] at this
      obtain ⟨p, hp, rfl⟩ := this
      exact ⟨p, hp, rfl⟩
    exact WScoped.mono hle (hds x hx)

theorem grpNews_mapIdx (us : List Level) (ds : List Expr) (hi : Nat) (grp : List (Name × Expr)) :
    (grp.mapIdx fun _ (c, _) => ({ key := ⟨c, us, ds⟩, base := hi } : NestHole))
      = grpNews us ds hi grp := by
  apply List.ext_getElem (by simp [grpNews])
  intro i h₁ h₂
  simp [grpNews]

/-- The frame's substitution replaces a constant by one of the group's
holes. -/
theorem grpSub_hole {us us' : List Level} {hi : Nat} {grp : List (Name × Expr)} {c : Name}
    {r : Expr} (h : grpSub us hi grp c us' = some r) :
    ∃ i, ∃ hi' : i < grp.length, r = .fvar (hi + i) grp[i].2 := by
  unfold grpSub at h
  split at h
  · have hmem : ∀ (L : List (Name × Expr)), L.lookup c = some r → ∃ q ∈ L, q.2 = r := by
      intro L
      induction L with
      | nil => intro h; simp [List.lookup] at h
      | cons x xs ih =>
        intro h
        simp only [List.lookup] at h
        split at h
        · exact ⟨x, List.mem_cons_self, Option.some.inj h⟩
        · obtain ⟨q, hq, hqr⟩ := ih h
          exact ⟨q, List.mem_cons_of_mem _ hq, hqr⟩
    obtain ⟨q, hq, hqr⟩ := hmem _ h
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hq
    simp only [List.getElem_mapIdx] at hqr ⊢
    exact ⟨i, by simpa using hi', hqr.symm⟩
  · exact nomatch h

/-- The container's type former at the key is closed. -/
theorem nestInstType_closed (hc : NestCtxOk ctx) {hi : Nat} {key : NestKey} {nI : Nat}
    {cty : Expr} (h : nestInstType (m := CheckM) ctx hi key = .ok (nI, cty)) :
    cty.hasFvar = false := by
  obtain ⟨cvC, caps, hf, -, rfl, -⟩ := nestInstType_inv h
  rw [ConLeche.Expr.hasFvar_instantiateLevelParams]
  exact hc.2 _ _ hf

/-- A container's constructors come from the context's constants. -/
theorem nestContainer_mem {C : Name} {nP : Nat} {L : List (ConstantVal × Nat)}
    (h : nestContainer ctx C = some (nP, L)) :
    ∀ x ∈ L, ∃ nPc, ConstantInfo.ctorInfo x.1 nPc x.2 ∈ ctx.consts := by
  intro x hx
  unfold nestContainer at h
  split at h
  · rename_i cv caps hf
    dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact nomatch hx
    · rename_i c cs hcs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨ci, hci, hfm⟩ := List.mem_filterMap.mp hy
      split at hfm
      · rename_i cv' nPc nF
        split at hfm
        · split at hfm
          · split at hfm
            · simp only [Option.some.injEq] at hfm
              subst hfm
              exact ⟨nPc, hci⟩
            · exact nomatch hfm
          · exact nomatch hfm
        · exact nomatch hfm
      · exact nomatch hfm
  · exact nomatch h

/-- The pure group listing's constructors come from its containers. -/
theorem groupCtors_mem {nPc : Nat} :
    ∀ {cs : List Name} {ctors : List (ConstantVal × Nat)}, groupCtors ctx nPc cs = some ctors →
      ∀ x ∈ ctors, ∃ c ∈ cs, ∃ nP' L, nestContainer ctx c = some (nP', L) ∧ x ∈ L
  | [], ctors, h, x, hx => by
    simp only [groupCtors, Option.some.injEq] at h; subst h; exact nomatch hx
  | c :: cs, ctors, h, x, hx => by
    simp only [groupCtors] at h
    split at h
    · rename_i nP' L hq
      split at h
      · obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨c, List.mem_cons_self, nP', L, hq, hx⟩
        · obtain ⟨c', hc', rest'⟩ := groupCtors_mem hr x hx
          exact ⟨c', List.mem_cons_of_mem _ hc', rest'⟩
      · exact nomatch h
    · exact nomatch h

/-- **The pure group listing**: its constructors are its containers',
and every container's constructors are listed (at the frame's parameter
count, or none). -/
theorem groupCtors_spec {nPc : Nat} :
    ∀ {cs : List Name} {ctors : List (ConstantVal × Nat)}, groupCtors ctx nPc cs = some ctors →
      (∀ x ∈ ctors, ∃ c ∈ cs, ∃ nP' L, nestContainer ctx c = some (nP', L) ∧
          (nP' = nPc ∨ L = []) ∧ x ∈ L) ∧
        ∀ c ∈ cs, ∃ nP' L, nestContainer ctx c = some (nP', L) ∧
          (nP' = nPc ∨ L = []) ∧ ∀ x ∈ L, x ∈ ctors
  | [], ctors, h => by
    simp only [groupCtors, Option.some.injEq] at h; subst h
    exact ⟨fun _ hx => (nomatch hx), fun _ hc => (nomatch hc)⟩
  | c :: cs, ctors, h => by
    simp only [groupCtors] at h
    split at h
    · rename_i nP' L hq
      split at h
      · rename_i hok
        have hok' : nP' = nPc ∨ L = [] := by
          simp only [Bool.or_eq_true, beq_iff_eq, List.isEmpty_iff] at hok; exact hok
        obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hin, hall⟩ := groupCtors_spec hr
        refine ⟨fun x hx => ?_, fun c' hc' => ?_⟩
        · rcases List.mem_append.mp hx with hx | hx
          · exact ⟨c, List.mem_cons_self, nP', L, hq, hok', hx⟩
          · obtain ⟨c', hc', rest'⟩ := hin x hx
            exact ⟨c', List.mem_cons_of_mem _ hc', rest'⟩
        · rcases List.mem_cons.mp hc' with rfl | hc'
          · exact ⟨nP', L, hq, hok', fun x hx => List.mem_append_left _ hx⟩
          · obtain ⟨nP'', L', h1, h2, h3⟩ := hall c' hc'
            exact ⟨nP'', L', h1, h2, fun x hx => List.mem_append_right _ (h3 x hx)⟩
      · exact nomatch h
    · exact nomatch h

/-! ## The telescope -/

section Tele

variable {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
  {syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState}

/-- **The telescope walk, derived.** -/
theorem nestFields_deriv (hrec : RunDeriv ops env ctx rec) (hsyn : SynDeriv ops env ctx syn)
    {prog : List NestHole} {base : Nat}
    {err : CheckError} (hhi : ctx.hiAt prog.length ≤ base) (hsc : ProgScoped ctx prog) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields rec syn prog base err nF j cur st = .ok (ks, nds, res, st') →
      WScoped (base + j) cur → DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧
        ∃ ts, PosD ops env ctx (.tele prog base nF j cur (ks.map (·.erase)) nds res) ts ∧
          NodesIn ops env ctx st st' ts := by
  intro nF
  induction nF with
  | zero =>
    intro j cur st ks nds res st' h _ hI
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hI, [], .teleNil, NodesIn.nil rfl rfl⟩
  | succ nF ih =>
    intro j cur st ks nds res st' h hws hI
    unfold nestFields at h
    split at h
    · rename_i a b bm
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i r₁ hr₁
      obtain ⟨k₁, nd₁, st₁⟩ := r₁
      simp only at h
      simp only [WScoped] at hws
      obtain ⟨hI₁, ts₁, h₁, hn₁⟩ :=
        hrec prog (base + j) 0 a st k₁ nd₁ st₁ hr₁ (by omega) hws.1 hsc hI
      split at h
      · simp at h
      rename_i stS hS
      obtain ⟨hIS, tsS, hS', hnS⟩ := hsyn prog _ a st₁ stS _ hS hws.1 hsc hI₁
      split at h
      · simp at h
      rename_i r₂ hr₂
      obtain ⟨ks₂, nds₂, res₂, st₂⟩ := r₂
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hws' : WScoped (base + (j + 1)) (b.instantiate1 (.fvar (base + j) a)) := by
        rw [show base + (j + 1) = base + j + 1 by omega]
        exact WScoped.instantiate1 hws.1 0 hws.2
      obtain ⟨hI₂, ts₂, h₂, hn₂⟩ := ih (j + 1) _ stS ks₂ nds₂ res₂ st₂ hr₂ hws' hIS
      exact ⟨hI₂, ts₁ ++ (tsS ++ ts₂), .teleCons h₁ hS' h₂, hn₁.trans (hnS.trans hn₂)⟩
    · simp at h

end Tele

/-! ## Small facts -/

theorem posD_nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] : ∀ (l : List α), l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun h => ?_, posD_nodup_eraseDups _⟩
    rw [List.mem_eraseDups, List.mem_filter] at h
    simp at h
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  have := List.length_filter_le (fun b => !b == a) as
  omega

/-- A frame's group grown by named containers, inverted. -/
theorem nestGrowGroup_inv' {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (cs : List Name) (grp grp' : List (Name × Expr)),
      nestGrowGroup (m := CheckM) ctx hi us ds cs grp = .ok grp' →
      ∃ ext, grp' = grp ++ ext ∧ ext.map (·.1) = cs ∧
        ∀ p ∈ ext, ∃ nI, nestInstType (m := CheckM) ctx hi ⟨p.1, us, ds⟩ = .ok (nI, p.2)
  | [], grp, grp', h => by
    simp only [nestGrowGroup, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, rfl, fun _ hp => nomatch hp⟩
  | c :: cs, grp, grp', h => by
    simp only [nestGrowGroup, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i q hq
    obtain ⟨nI, cty⟩ := q
    obtain ⟨ext, rfl, hmap, hall⟩ := nestGrowGroup_inv' cs _ grp' h
    refine ⟨(c, cty) :: ext, by simp, by simp [hmap], fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨nI, hq⟩
    · exact hall p hp

theorem erase_getD (ks : List NestFieldKind) (i : Nat) :
    (ks.map (·.erase)).getD i .ordinary = (ks.getD i .ordinary).erase := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? <;> rfl

theorem erase_getD_bne (ks : List NestFieldKind) (i : Nat) :
    ((ks.map (·.erase)).getD i .ordinary != .ordinary) = (ks.getD i .ordinary != .ordinary) := by
  rw [erase_getD]
  cases ks.getD i .ordinary <;> rw [Bool.eq_iff_iff] <;> simp [NestFieldKind.erase, bne_iff_ne]

/-! ## The frame -/

section Frame

variable {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
  {syn : List NestHole → List NestKey → Expr → NestState → CheckM NestState}

/-- **A frame's constructors, derived.** -/
theorem nestCtors_deriv (hrec : RunDeriv ops env ctx rec) (hsyn : SynDeriv ops env ctx syn)
    {prog : List NestHole} {hi : Nat}
    {us : List Level} {ds : List Expr} {sub : Name → List Level → Option Expr}
    (hhi : ctx.hiAt prog.length = hi) (hsc : ProgScoped ctx prog)
    (hds : ∀ x ∈ ds, WScoped hi x) (hsub : ∀ c us' r, sub c us' = some r → WScoped hi r) :
    ∀ (cs : List (ConstantVal × Nat)) (st st' : NestState), (∀ x ∈ cs, x.1.type.hasFvar = false) →
      nestCtors ctx ops env rec syn prog hi us ds ds.length sub cs st = .ok st' →
      DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧ ∃ ts, PosD ops env ctx (.ctors prog hi us ds sub cs) ts ∧
        NodesIn ops env ctx st st' ts ∧
        CtorsRec ops env ctx st'.ctorNfs.toList prog hi us ds sub cs := by
  intro cs
  induction cs with
  | nil =>
    intro st st' _ h hI
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, [], .ctorsNil, NodesIn.nil rfl rfl, fun _ hx => nomatch hx⟩
  | cons x cs ih =>
    intro st st' hcl h hI
    obtain ⟨cv, nF⟩ := x
    simp only [nestCtors, bind, Except.bind] at h
    have hnd : Name.nodup cv.levelParams = true := by
      rcases hb : Name.nodup cv.levelParams
      · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      · rfl
    rw [if_pos hnd] at h
    split at h
    · simp at h
    rename_i crest hcrest
    have hcrest' := unwrapOr_ok hcrest
    split at h
    · simp at h
    rename_i ty hty
    split at h
    · simp at h
    rename_i sv hsv
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨ks, nds, cur, st₁⟩ := r
    have hws : WScoped (hi + 0) crest := by
      refine wscoped_instPisWith hds (WScoped.replaceConsts_closed hsub _ ?_) hcrest'
      rw [ConLeche.Expr.hasFvar_instantiateLevelParams]
      exact hcl _ List.mem_cons_self
    obtain ⟨hI₁, ts₁, h₁, hn₁⟩ :=
      nestFields_deriv hrec hsyn (by omega) hsc nF 0 crest st ks nds cur st₁ hr hws hI
    dsimp only at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hu4
    split at h
    · rename_i hok
      have hI₁' : DerivCache ops env ctx
          { st₁ with ctorNfs := (st₁.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur)) } :=
        hI₁.grow rfl rfl fun e he => by
          show e ∈ (st₁.ctorNfs.push _).toList
          rw [Array.toList_push]; exact List.mem_append_left _ he
      obtain ⟨hI', ts₂, h₂, hn₂, hr₂⟩ :=
        ih _ st' (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) h hI₁'
      have hn₁' : NodesIn ops env ctx st
          { st₁ with ctorNfs := (st₁.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur)) } ts₁ :=
        hn₁.grow rfl ⟨[nestCtorNf ctx prog hi us ds cv nds cur], Array.toList_push⟩
      refine ⟨hI', ts₁ ++ ts₂, ?_, hn₁'.trans hn₂, fun x hx => ?_⟩
      · simp only [Bool.and_eq_true] at hok
        refine .ctorsCons hnd hcrest' hty hsv h₁ ?_ hok.1 hok.2 h₂
        simp only [erase_getD_bne]
        simpa using hu4
      · rcases List.mem_cons.mp hx with rfl | hx
        · intro crest'' ks'' nds'' cur'' ts'' hcr'' hd''
          rw [hcrest'] at hcr''
          obtain rfl := Option.some.inj hcr''
          obtain ⟨-, rfl, rfl⟩ := posD_tele_fun (by simpa using h₁) hd''
          obtain ⟨-, ⟨nc, hnc⟩, -⟩ := hn₂
          rw [hnc]
          exact List.mem_append_left _ (by simp)
        · exact hr₂ x hx
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A frame's constructor listing, without its cache.** -/
theorem nestGroupCtors_deriv {nPc : Nat} :
    ∀ (cs : List Name) (st : NestState) (ctors : List (ConstantVal × Nat)) (st' : NestState),
      nestGroupCtors (m := CheckM) ctx nPc cs st = .ok (ctors, st') → DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧ groupCtors ctx nPc cs = some ctors ∧ st'.nodes = st.nodes ∧
        st'.ctorNfs = st.ctorNfs
  | [], st, ctors, st', h, hst => by
    simp only [nestGroupCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hst, rfl, rfl, rfl⟩
  | c :: cs, st, ctors, st', h, hst => by
    simp only [nestGroupCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i q hq
    have hq' := unwrapOr_ok hq
    rw [hst.lookup c] at hq'
    obtain ⟨nP', L⟩ := q
    dsimp only at h
    split at h
    · rename_i hok
      split at h
      · simp at h
      rename_i r hr
      obtain ⟨rest, st₁⟩ := r
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hI₁, hg, hnd₁, hnc₁⟩ := nestGroupCtors_deriv cs _ rest st₁ hr (hst.insert c)
      refine ⟨hI₁, ?_, by rw [hnd₁]; unfold nestContainerC; split <;> rfl,
        by rw [hnc₁]; unfold nestContainerC; split <;> rfl⟩
      simp only [groupCtors, hq']
      rw [if_pos (by simpa using hok), hg]
      rfl
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The frame's group-mates are distinct from each other and from the
container. -/
theorem nestFrameMates_nodup (C : Name) : (C :: nestFrameMates ctx C).Nodup := by
  refine List.nodup_cons.mpr ⟨fun h => ?_, ((posD_nodup_eraseDups _).filter _)⟩
  simp [nestFrameMates, List.mem_filter] at h

/-- A frame's group-mate is a member of the container's recorded block. -/
theorem mem_nestFrameMates {C c : Name} (h : c ∈ nestFrameMates ctx C) :
    c ∈ nestBlockOf ctx C ∧ c ≠ C := by
  simp only [nestFrameMates, List.mem_filter, List.mem_eraseDups, bne_iff_ne, ne_eq] at h
  exact h

/-- **A container frame, derived**: the state invariant is kept and the
frame is derived (the group's facts are the `frame` rule's). -/
theorem nestFrame_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    (hsyn : SynDeriv ops env ctx syn)
    {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
    (hhi : ctx.hiAt prog.length = hi) (hsc : ProgScoped ctx prog)
    (hds : ∀ x ∈ ds, WScoped hi x) {grp : List (Name × Expr)} {st st' : NestState}
    (hne : grp ≠ [])
    (hhd : ctx.names.contains (grp.headD default).1 = false ∧ (grp.headD default).1 ≠ quotName)
    (hhdC : ∃ L, nestContainer ctx (grp.headD default).1 = some (ds.length, L))
    (hnd : (grp.map (·.1)).Nodup)
    (hinst : ∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx hi ⟨p.1, us, ds⟩ = .ok (nI, p.2))
    (hblk : ∀ p ∈ grp.tail, (nestBlockOf ctx (grp.headD default).1).contains p.1 = true)
    (hgrp : grp.map (·.1) = (grp.headD default).1 :: nestFrameMates ctx (grp.headD default).1)
    (h : nestFrame ctx ops env rec syn prog hi us ds ds.length grp st = .ok st')
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ ∃ ts, PosD ops env ctx (.frame prog us ds grp) ts ∧
      NodesIn ops env ctx st st' ts ∧ FrameRec ops env ctx st'.ctorNfs.toList prog us ds grp := by
  simp only [nestFrame, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i kty hkty
  split at h
  · simp at h
  rename_i v hgc
  obtain ⟨ctors, st₁⟩ := v
  obtain ⟨hI₁, hgc', hnd₁, hnc₁⟩ := nestGroupCtors_deriv _ st ctors st₁ hgc hI
  have hwc' : nestCtors ctx ops env rec syn
      ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length) us ds ds.length
      (grpSub us hi grp) ctors st₁ = .ok st' := by
    rw [← grpNews_mapIdx]; exact h
  have hlenN : ((grpNews us ds hi grp).reverse ++ prog).length = grp.length + prog.length := by
    simp [grpNews]
  have hhi' : ctx.hiAt ((grpNews us ds hi grp).reverse ++ prog).length = hi + grp.length := by
    rw [hlenN, ← hhi]; simp only [NestCtx.hiAt]; omega
  have hsc' : ProgScoped ctx ((grpNews us ds hi grp).reverse ++ prog) := by
    subst hhi; exact hsc.push hds grp
  have hsub : ∀ c us' r, grpSub us hi grp c us' = some r → WScoped (hi + grp.length) r := by
    intro c us' r hr
    obtain ⟨i, hi', rfl⟩ := grpSub_hole hr
    obtain ⟨nI, hnI⟩ := hinst _ (List.getElem_mem hi')
    simp only [WScoped]
    exact ⟨by omega, WScoped.of_not_hasFvar (nestInstType_closed hctx hnI)⟩
  have hcl : ∀ x ∈ ctors, x.1.type.hasFvar = false := by
    intro x hx
    obtain ⟨c, -, nP', L, hL, hxL⟩ := groupCtors_mem hgc' x hx
    obtain ⟨nPc, hmem⟩ := nestContainer_mem hL x hxL
    exact hctx.1 _ hmem
  obtain ⟨hI₂, ts, hw', hn₂, hcr₂⟩ := nestCtors_deriv hrec hsyn hhi' hsc'
    (fun x hx => WScoped.mono (by omega) (hds x hx)) hsub ctors st₁ st' hcl hwc' hI₁
  subst hhi
  refine ⟨hI₂, ts, .frame hne hhd hhdC hnd hinst hblk hgrp hgc' ⟨kty, hkty⟩ hw',
    hn₂.of_eq_left hnd₁ hnc₁, fun ctors' hc' => ?_⟩
  rw [hgc'] at hc'
  obtain rfl := Option.some.inj hc'
  exact hcr₂

/-- **Accepting the group-mates keeps the invariant.** -/
theorem nestAcceptGroup_deriv {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st st' : NestState),
      nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' →
      DerivCache ops env ctx st →
      (∀ p ∈ grp, (∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) →
        KeyDR ops env ctx st.ctorNfs.toList ⟨p.1, us, ds⟩) →
      DerivCache ops env ctx st'
  | [], st, st', h, hI, _ => by
    simp only [nestAcceptGroup, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hI
  | (c, ty) :: rest, st, st', h, hI, hk => by
    simp only [nestAcceptGroup, bind, Except.bind] at h
    split at h
    · split at h
      · simp at h
      refine nestAcceptGroup_deriv rest _ st' h ⟨hI.1, fun ki hki hfv => ?_⟩
        (fun p hp => hk p (List.mem_cons_of_mem _ hp))
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
      rcases hki with hki | rfl
      · exact hI.2 ki hki hfv
      · exact hk (c, ty) List.mem_cons_self hfv
    · exact nestAcceptGroup_deriv rest st st' h hI (fun p hp => hk p (List.mem_cons_of_mem _ hp))

/-- Accepting the group-mates records no class and no constructor. -/
theorem nestAcceptGroup_nodes {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st st' : NestState),
      nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' →
        st'.nodes = st.nodes ∧ st'.ctorNfs = st.ctorNfs
  | [], st, st', h => by
    simp only [nestAcceptGroup, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, rfl⟩
  | (c, ty) :: rest, st, st', h => by
    simp only [nestAcceptGroup, bind, Except.bind] at h
    split at h
    · split at h
      · simp at h
      have := nestAcceptGroup_nodes rest _ st' h
      exact this
    · have := nestAcceptGroup_nodes rest _ st' h
      exact this

/-- **A new (or re-walked) instantiation, derived**: its frame, under the
current frames, the container at the frame's head, the container's
whole recorded block its group. -/
theorem nestContNew_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    (hsyn : SynDeriv ops env ctx syn)
    {prog : List NestHole} (hsc : ProgScoped ctx prog) {kb : Nat} {n : Name} {us : List Level}
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) {nPc : Nat}
    (hnPc : ds.length = nPc) (hq : ∃ L, nestContainer ctx n = some (nPc, L)) {old : Option Nat}
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContNew ctx ops env rec syn prog kb n us ds nPc old st = .ok (k, st'))
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ k.erase = .nested (kb != 0) ∧ ∃ nI cty grp,
      nestInstType (m := CheckM) ctx (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨n, us, ds⟩
        = .ok (nI, cty) ∧
      grp.head? = some (n, cty) ∧
      ∃ ts, PosD ops env ctx (.frame (nestWalkStack ctx prog ds) us ds grp) ts ∧
        NodesIn ops env ctx st st' [.node prog (nestWalkStack ctx prog ds) ⟨n, us, ds⟩ grp ts] := by
  subst hnPc
  have hscw : ProgScoped ctx (nestWalkStack ctx prog ds) := by
    unfold nestWalkStack; split
    · exact ProgScoped.nil
    · exact hsc
  have hdsw : ∀ x ∈ ds, WScoped (ctx.hiAt (nestWalkStack ctx prog ds).length) x := by
    unfold nestWalkStack; split
    · rename_i hfree
      intro x hx
      exact WScoped.of_fvarsBelow (hds x hx)
        (Expr.fvarB_le (by simpa using List.all_eq_true.mp hfree x hx))
    · exact hds
  have hroot : (∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) → nestWalkStack ctx prog ds = [] := by
    intro hfree
    unfold nestWalkStack
    rw [if_pos (List.all_eq_true.mpr fun x hx => by simpa using hfree x hx)]
  simp only [nestContNew, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i ni hni
  obtain ⟨nI, cty⟩ := ni
  split at h
  · simp at h
  rename_i grp' hgrow
  obtain ⟨ext, rfl, hmap, hext⟩ := nestGrowGroup_inv' _ _ _ hgrow
  split at h
  · simp at h
  rename_i st₁ hfr
  have hmap' : (((n, cty) :: ext).map (·.1)) = n :: nestFrameMates ctx n := by
    simp [hmap]
  obtain ⟨hI₁, tsF, hframe, hnF, hfrec⟩ := nestFrame_deriv (grp := [(n, cty)] ++ ext) hctx hrec hsyn rfl hscw hdsw
    (by simp) ⟨hnm, hquot⟩ hq (by simpa [hmap'] using nestFrameMates_nodup (ctx := ctx) n)
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨nI, hni⟩
      · exact hext p hp)
    (fun p hp => by
      have hp' : p.1 ∈ nestFrameMates ctx n := by
        rw [← hmap]; exact List.mem_map_of_mem (by simpa using hp)
      simpa using (mem_nestFrameMates hp').1)
    (by simpa using hmap') hfr ⟨hI.1, hI.2⟩
  have hkey : ∀ p ∈ (n, cty) :: ext, (∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) →
      KeyDR ops env ctx st₁.ctorNfs.toList ⟨p.1, us, ds⟩ :=
    fun p hp hfree => ⟨_, tsF, by rw [← hroot hfree]; exact hframe, List.mem_map_of_mem hp,
      by rw [← hroot hfree]; exact hfrec, hnF.2.2⟩
  split at h
  · simp at h
  rename_i st₂ hacc
  have hI₂ : DerivCache ops env ctx st₂ :=
    nestAcceptGroup_deriv _ _ _ hacc ⟨hI₁.1, hI₁.2⟩ fun p hp => hkey p (List.mem_of_mem_drop hp)
  obtain ⟨hacn, hacc'⟩ := nestAcceptGroup_nodes (ctx := ctx) _ _ st₂ hacc
  have hn₂ : NodesIn ops env ctx st st₂ tsF := (hnF.of_eq_left rfl rfl).of_eq_right hacn hacc'
  have hn₃ := hn₂.walked (occ := prog) (anc := nestWalkStack ctx prog ds) (key := ⟨n, us, ds⟩)
    (grp := (n, cty) :: ext) (by rw [hacc']; exact hfrec)
  have hout : k.erase = .nested (kb != 0) := by
    split at h <;>
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]; rfl
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨⟨hI₂.1, hI₂.2⟩, hout, nI, cty, _, hni, rfl, tsF, hframe, hn₃⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨⟨hI₂.1, fun ki hki hfv => ?_⟩, hout, nI, cty, _, hni, rfl, tsF, hframe,
      hn₃.of_eq_right rfl rfl⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
    rcases hki with hki | rfl
    · exact hI₂.2 ki hki hfv
    · have := hkey _ List.mem_cons_self hfv
      rw [← hacc'] at this
      exact this

/-- A walked instantiation: at its occurrence's frames, or — below every
frame hole — at the empty stack. -/
theorem contNew_split {prog : List NestHole} {n : Name} {us : List Level} {ds : List Expr}
    {st st' : NestState}
    (hr : ∃ nI cty grp,
      nestInstType (m := CheckM) ctx (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨n, us, ds⟩
        = .ok (nI, cty) ∧
      grp.head? = some (n, cty) ∧
      ∃ ts, PosD ops env ctx (.frame (nestWalkStack ctx prog ds) us ds grp) ts ∧
        NodesIn ops env ctx st st' [.node prog (nestWalkStack ctx prog ds) ⟨n, us, ds⟩ grp ts]) :
    (∃ nI cty grp,
      nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty) ∧
      grp.head? = some (n, cty) ∧ ∃ ts, PosD ops env ctx (.frame prog us ds grp) ts ∧
        NodesIn ops env ctx st st' [.node prog prog ⟨n, us, ds⟩ grp ts]) ∨
    ((∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) ∧ ∃ grp ts,
      PosD ops env ctx (.frame [] us ds grp) ts ∧ n ∈ grp.map (·.1) ∧
      NodesIn ops env ctx st st' [.node prog [] ⟨n, us, ds⟩ grp ts]) := by
  obtain ⟨nI, cty, grp, hnI, hhead, ts, hfr, hn⟩ := hr
  unfold nestWalkStack at hnI hfr hn
  split at hnI
  · rename_i hfree
    rw [if_pos hfree] at hfr hn
    refine Or.inr ⟨fun x hx => by simpa using List.all_eq_true.mp hfree x hx, grp, ts, hfr, ?_, hn⟩
    cases grp with
    | nil => simp at hhead
    | cons p ps =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact List.mem_cons_self
  · rename_i hfree
    rw [if_neg hfree] at hfr hn
    exact Or.inl ⟨nI, cty, grp, hnI, hhead, ts, hfr, hn⟩

/-- **The instantiation met, derived**: in progress it rejects;
otherwise the frame is derived here, or the key is a hit below every
frame hole with a derived frame elsewhere. -/
theorem nestContKey_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    (hsyn : SynDeriv ops env ctx syn)
    {prog : List NestHole} (hsc : ProgScoped ctx prog) {kb : Nat} {n : Name} {us : List Level}
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) {nPc : Nat}
    (hnPc : ds.length = nPc) (hq : ∃ L, nestContainer ctx n = some (nPc, L))
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContKey ctx ops env rec syn prog kb n us ds nPc st = .ok (k, st'))
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ k.erase = .nested (kb != 0) ∧
      ((∃ nI cty grp,
        nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty) ∧
        grp.head? = some (n, cty) ∧ ∃ ts, PosD ops env ctx (.frame prog us ds grp) ts ∧
          NodesIn ops env ctx st st' [.node prog prog ⟨n, us, ds⟩ grp ts]) ∨
       ((∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) ∧ ∃ grp ts,
          PosD ops env ctx (.frame [] us ds grp) ts ∧ n ∈ grp.map (·.1) ∧
          NodesIn ops env ctx st st' [.node prog [] ⟨n, us, ds⟩ grp ts])) := by
  subst hnPc
  unfold nestContKey at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · split at h
    · rename_i q hfq
      split at h
      · -- a hit
        rename_i hfree
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hqs, hqk, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfq
        have hkeq : st.keys[q].key = ⟨n, us, ds⟩ := by simpa using hqk
        have hfree' : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0 := by simpa using hfree
        have := hI.2 _ (Array.getElem_mem_toList hqs) (by rw [hkeq]; exact hfree')
        rw [hkeq] at this
        obtain ⟨grp, ts, hfr, hmem, hfrec, htrec⟩ := this
        exact ⟨⟨hI.1, hI.2⟩, rfl, Or.inr ⟨hfree', grp, ts, hfr, hmem,
          NodesIn.hit (key := ⟨n, us, ds⟩) hmem hfrec htrec⟩⟩
      · obtain ⟨hI', hk, hr⟩ := nestContNew_deriv hctx hrec hsyn hsc hnm hquot hds rfl hq h hI
        exact ⟨hI', hk, contNew_split hr⟩
    · obtain ⟨hI', hk, hr⟩ := nestContNew_deriv hctx hrec hsyn hsc hnm hquot hds rfl hq h hI
      exact ⟨hI', hk, contNew_split hr⟩

/-! ### The syntactic pass -/

/-- The scan's keys have their sources: official's reading of a raw
subterm (F15). -/
theorem nestSynGo_src {hi : Nat} :
    ∀ (e : Expr) (acc : NestSynAcc) (k : NestKey), k ∈ (nestSynGo ctx hi e acc).keys.toList →
      k ∈ acc.keys.toList ∨ SynSrc ctx hi e k := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro acc k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · dsimp only at hk
      split at hk
      · rename_i k' hk'
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | rfl
        · exact .inl hk
        · exact .inr ⟨_, .refl _, hk'⟩
      · have lift : ∀ acc', (k ∈ acc'.keys.toList → k ∈ acc.keys.toList ∨ SynSrc ctx hi (.app f a) k) →
            k ∈ (nestSynGo ctx hi a (nestSynGo ctx hi f acc')).keys.toList →
            k ∈ acc.keys.toList ∨ SynSrc ctx hi (.app f a) k := by
          intro acc' h0 hk
          rcases iha _ k hk with hk | ⟨s, hs, hsk⟩
          · rcases ihf _ k hk with hk | ⟨s, hs, hsk⟩
            · exact h0 hk
            · exact .inr ⟨s, .appF _ hs, hsk⟩
          · exact .inr ⟨s, .appA _ hs, hsk⟩
        split at hk
        · split at hk
          · exact .inl hk
          · exact lift { acc with seen := acc.seen.insert (.app f a) } (fun h => .inl h) hk
        · exact lift { acc with seen := acc.seen.insert (.app f a) } (fun h => .inl h) hk
  | lam t b bm iht ihb =>
    intro acc k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · rcases ihb _ k hk with hk | ⟨s, hs, hsk⟩
      · rcases iht _ k hk with hk | ⟨s, hs, hsk⟩
        · exact .inl hk
        · exact .inr ⟨s, .lamT _ _ hs, hsk⟩
      · exact .inr ⟨s, .lamB _ _ hs, hsk⟩
  | forallE t b bm iht ihb =>
    intro acc k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · rcases ihb _ k hk with hk | ⟨s, hs, hsk⟩
      · rcases iht _ k hk with hk | ⟨s, hs, hsk⟩
        · exact .inl hk
        · exact .inr ⟨s, .piT _ _ hs, hsk⟩
      · exact .inr ⟨s, .piB _ _ hs, hsk⟩
  | letE t v b iht ihv ihb =>
    intro acc k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · rcases ihb _ k hk with hk | ⟨s, hs, hsk⟩
      · rcases ihv _ k hk with hk | ⟨s, hs, hsk⟩
        · rcases iht _ k hk with hk | ⟨s, hs, hsk⟩
          · exact .inl hk
          · exact .inr ⟨s, .letT _ _ hs, hsk⟩
        · exact .inr ⟨s, .letV _ _ hs, hsk⟩
      · exact .inr ⟨s, .letB _ _ hs, hsk⟩
  | proj sn i x ih =>
    intro acc k hk
    rw [nestSynGo] at hk
    split at hk
    · exact .inl hk
    · rcases ih _ k hk with hk | ⟨s, hs, hsk⟩
      · exact .inl hk
      · exact .inr ⟨s, .proj _ _ hs, hsk⟩
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro acc k hk
    rw [nestSynGo] at hk
    split at hk <;> exact .inl hk

/-- **Every syntactic occurrence has its source** (F15). -/
theorem nestSynOccs_src {hi : Nat} {e : Expr} {k : NestKey} (hk : k ∈ nestSynOccs ctx hi e) :
    SynSrc ctx hi e k := by
  rw [nestSynOccs, List.mem_eraseDups] at hk
  rcases nestSynGo_src e {} k hk with hk | h
  · simp at hk
  · exact h

/-- A walked syntactic occurrence, as a `syn` node (walked here, or at
the empty stack). -/
theorem synOf_contNew {prog : List NestHole} {e : Expr} {n : Name} {us : List Level}
    {ds : List Expr} {L : List (ConstantVal × Nat)} {st st₀ st' : NestState}
    (hsrc : SynSrc ctx (ctx.hiAt prog.length) e ⟨n, us, ds⟩)
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    (hC : nestContainer ctx n = some (ds.length, L))
    (hdsok : ∀ x ∈ ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length)
    (hdsw : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) (hsc : ProgScoped ctx prog)
    (hcase : (∃ nI cty grp,
      nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty) ∧
      grp.head? = some (n, cty) ∧ ∃ ts, PosD ops env ctx (.frame prog us ds grp) ts ∧
        NodesIn ops env ctx st₀ st' [.node prog prog ⟨n, us, ds⟩ grp ts]) ∨
    ((∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) ∧ ∃ grp ts,
      PosD ops env ctx (.frame [] us ds grp) ts ∧ n ∈ grp.map (·.1) ∧
      NodesIn ops env ctx st₀ st' [.node prog [] ⟨n, us, ds⟩ grp ts]))
    (hst : st₀.nodes = st.nodes) (hstc : st₀.ctorNfs = st.ctorNfs) :
    ∃ ts, (∀ ts', PosD ops env ctx (.syn prog e) ts' → PosD ops env ctx (.syn prog e) (ts ++ ts')) ∧
      NodesIn ops env ctx st st' ts := by
  rcases hcase with ⟨nI, cty, grp, hnI, hhead, tsF, hfr, hnF⟩ | ⟨hfree, grp, tsF, hfr, hmem, hnF⟩
  · exact ⟨[_], fun ts' hr => .synNew hsrc hnm hquot hC hdsok hdsw hnI hhead hsc hfr hr,
      hnF.of_eq_left hst hstc⟩
  · exact ⟨[_], fun ts' hr => .synHit hsrc hnm hquot hC
      (fun x hx => ⟨(hdsok x hx).1, hfree x hx⟩)
      (fun x hx => WScoped.of_fvarsBelow (hdsw x hx) (Expr.fvarB_le (hfree x hx))) hmem hfr hr,
      hnF.of_eq_left hst hstc⟩

/-- **One syntactic occurrence, derived**: walked here or a hit, a `syn`
node; skipped, nothing. -/
theorem nestSynKey_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    (hsyn : SynDeriv ops env ctx syn) {prog : List NestHole} (hsc : ProgScoped ctx prog)
    {skip : List NestKey} {d : Nat} {e : Expr} {key : NestKey} {st st' : NestState}
    (hwk : ∀ x ∈ key.ds, WScoped d x) (hsrc : SynSrc ctx (ctx.hiAt prog.length) e key)
    (h : nestSynKey ctx ops env rec syn prog skip key st = .ok st')
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ ∃ ts, (∀ ts', PosD ops env ctx (.syn prog e) ts' →
      PosD ops env ctx (.syn prog e) (ts ++ ts')) ∧ NodesIn ops env ctx st st' ts := by
  obtain ⟨n, us, ds⟩ := key
  unfold nestSynKey at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hdsok
  have hdsok' : ∀ x ∈ ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length := by
    simpa using hdsok
  have hdsw : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x := fun x hx =>
    WScoped.of_fvarsBelow (hwk x hx) (Expr.fvarB_le (hdsok' x hx).2)
  split at h
  · -- skipped
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, [], fun ts' h => h, NodesIn.nil rfl rfl⟩
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hmq
  have hnm : ctx.names.contains n = false := by
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hmq; simpa using hmq.1
  have hquot : n ≠ quotName := by
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hmq; exact hmq.2
  have hI₀ := hI.insert n
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i q hq
  rw [hI.lookup n] at hq
  obtain ⟨nPc, L⟩ := q
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hlen
  have hlen' : ds.length = nPc := by simpa using hlen
  have hC : nestContainer ctx n = some (ds.length, L) := by rw [hlen']; exact hq
  split at h
  · -- cached
    rename_i q' hfq
    split at h
    · -- a hit below every frame hole
      rename_i hfree
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hqs, hqk, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfq
      have hkeq : (nestContainerC ctx st n).2.keys[q'].key = ⟨n, us, ds⟩ := by simpa using hqk
      have hfree' : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0 := by simpa using hfree
      have hkd := hI₀.2 _ (Array.getElem_mem_toList hqs) (by rw [hkeq]; exact hfree')
      rw [hkeq] at hkd
      obtain ⟨grp, tsF, hfr, hmem, hfrec, htrec⟩ := hkd
      exact ⟨⟨hI₀.1, hI₀.2⟩, [_], fun ts' hr => .synHit hsrc hnm hquot hC (fun x hx =>
        ⟨(hdsok' x hx).1, hfree' x hx⟩) (fun x hx => WScoped.of_fvarsBelow (hdsw x hx)
          (Expr.fvarB_le (hfree' x hx))) hmem hfr hr,
        (NodesIn.hit (key := ⟨n, us, ds⟩) hmem hfrec htrec).of_eq_left
          (by unfold nestContainerC; split <;> rfl) (by unfold nestContainerC; split <;> rfl)⟩
    · -- re-walked
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i r hr₁
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hI₁, -, hr₂⟩ :=
        nestContNew_deriv hctx hrec hsyn hsc hnm hquot hdsw hlen' ⟨L, hq⟩ hr₁ hI₀
      exact ⟨hI₁, synOf_contNew hsrc hnm hquot hC hdsok' hdsw hsc (contNew_split hr₂)
        (by unfold nestContainerC; split <;> rfl) (by unfold nestContainerC; split <;> rfl)⟩
  · simp only [bind, Except.bind] at h
    split at h
    · simp at h
    rename_i r hr₁
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hI₁, -, hr₂⟩ :=
      nestContNew_deriv hctx hrec hsyn hsc hnm hquot hdsw hlen' ⟨L, hq⟩ hr₁ hI₀
    exact ⟨hI₁, synOf_contNew hsrc hnm hquot hC hdsok' hdsw hsc (contNew_split hr₂)
      (by unfold nestContainerC; split <;> rfl) (by unfold nestContainerC; split <;> rfl)⟩

/-- **A syntactic pass's keys, derived.** -/
theorem nestSynKeys_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    (hsyn : SynDeriv ops env ctx syn) {prog : List NestHole} (hsc : ProgScoped ctx prog)
    {skip : List NestKey} {d : Nat} {e : Expr} :
    ∀ (keys : List NestKey) (st st' : NestState), (∀ k ∈ keys, ∀ x ∈ k.ds, WScoped d x) →
      (∀ k ∈ keys, SynSrc ctx (ctx.hiAt prog.length) e k) →
      nestSynKeys ctx ops env rec syn prog skip keys st = .ok st' →
      DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧ ∃ ts, PosD ops env ctx (.syn prog e) ts ∧ NodesIn ops env ctx st st' ts
  | [], st, st', _, _, h, hI => by
    simp only [nestSynKeys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, [], .synNil, NodesIn.nil rfl rfl⟩
  | key :: keys, st, st', hwk, hks, h, hI => by
    simp only [nestSynKeys, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i st₁ h₁
    obtain ⟨hI₁, ts₁, hk, hn₁⟩ :=
      nestSynKey_deriv hctx hrec hsyn hsc (hwk key List.mem_cons_self)
        (hks key List.mem_cons_self) h₁ hI
    obtain ⟨hI₂, ts₂, hr, hn₂⟩ := nestSynKeys_deriv hctx hrec hsyn hsc keys st₁ st'
      (fun k hk => hwk k (List.mem_cons_of_mem _ hk))
      (fun k hk => hks k (List.mem_cons_of_mem _ hk)) h hI₁
    exact ⟨hI₂, _, hk ts₂ hr, hn₁.trans hn₂⟩

end Frame

/-! ## THE INVERSION -/

/-- **THE ONE INVERSION OF THE POSITIVITY RUN.**  A successful run of
`nestPos` — at any fuel, under any `ops` whose whnf keeps terms well
scoped, at a context whose stored constants are closed — keeps the
cache invariant, and when it leaves no restart pending, its input is
derived (`PosD`), with the run's kind (its table index forgotten) and
normal form. -/
theorem nestPos_deriv (hctx : NestCtxOk ctx)
    (hwsc : ∀ dep e w, ops.whnf env dep e = .ok w → WScoped dep e → WScoped dep w) :
    ∀ fuel, RunDeriv ops env ctx (nestPos ops env ctx fuel) ∧
      SynDeriv ops env ctx (nestSyn ops env ctx fuel)
  | 0 => by
    refine ⟨fun prog dep kb e st k nf st' hrun => ?_, fun prog skip e st st' d h => ?_⟩
    · simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
    · simp [nestSyn, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1 => by
    obtain ⟨ih, ihs⟩ := nestPos_deriv hctx hwsc fuel
    refine ⟨?_, fun prog skip e st st' d h hw hsc hI => ?_⟩
    rotate_left
    · rw [nestSyn] at h
      exact nestSynKeys_deriv hctx ih ihs hsc _ st st' (nestSynOccs_wscoped hw)
        (fun _ hk => nestSynOccs_src hk) h hI
    intro prog dep kb e st k nf st' hrun hhi hws hsc hI
    rw [nestPos] at hrun
    cases hw : ops.whnf env dep e with
    | error err => simp [hw, bind, Except.bind] at hrun
    | ok w =>
      simp only [hw, bind, Except.bind] at hrun
      have hwsw := hwsc dep e w hw hws
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false
      · rw [if_pos (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        exact ⟨hI, _, .const hw hocc, NodesIn.nil rfl rfl⟩
      have hocc' : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true := by simpa using hocc
      rw [if_neg (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        rename_i a b bm
        by_cases ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true
        · rw [if_pos ha] at hrun
          simp [throw, throwThe, MonadExceptOf.throw] at hrun
        rw [if_neg ha] at hrun
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        simp only [WScoped] at hwsw
        obtain ⟨hI', ts, hb, hn⟩ := ih prog (dep + 1) (kb + 1) _ st k₁ nb _ hv (by omega)
          (WScoped.instantiate1 hwsw.1 0 hwsw.2) hsc hI
        exact ⟨hI', ts, .pi hw hocc' (by simpa using ha) hb, hn⟩
      · -- a head applied to arguments
        split at hrun
        · -- a variable head
          rename_i i ty hfn
          by_cases hmem : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
          · rw [if_pos hmem] at hrun
            by_cases hc : (w.getAppArgs.length == ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0 &&
                List.take ctx.nP w.getAppArgs == ctx.params &&
                w.getAppArgs.all fun x => !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x)
                = true
            · rw [if_pos hc] at hrun
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl, rfl⟩ := hrun
              refine ⟨hI, ?_⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true] at hc
              have hd := PosD.hole (kb := kb) hw hocc' hfn hmem.1 hmem.2 hc.1.1 hc.1.2 hc.2
              refine ⟨[], ?_, NodesIn.nil rfl rfl⟩
              by_cases hkb : kb = 0
              · subst hkb; exact hd
              · have : (kb == 0) = false := by simpa using hkb
                simp only [this, hkb, if_false, Bool.false_eq_true] at hd ⊢
                exact hd
            · rw [if_neg hc] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · rw [if_neg hmem] at hrun
            by_cases hfr' : (decide (ctx.hiAt 0 ≤ i) && decide (i < ctx.hiAt prog.length)) = true
            · rw [if_pos hfr'] at hrun
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr'
              split at hrun
              · simp [throw, throwThe, MonadExceptOf.throw] at hrun
              · rename_i key hk
                by_cases hpar : (decide (key.key.ds.length ≤ w.getAppArgs.length) &&
                    (List.take key.key.ds.length w.getAppArgs == key.key.ds)) = true
                · rw [if_pos hpar] at hrun
                  by_cases hidx : ((w.getAppArgs.drop key.key.ds.length).all fun x =>
                      !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x) = true
                  · rw [if_pos hidx] at hrun
                    by_cases har : (w.getAppArgs.length == nestArity ctx key.key.cname) = true
                    · rw [if_pos har] at hrun
                      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                      obtain ⟨rfl, rfl, rfl⟩ := hrun
                      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpar
                      simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hidx
                      exact ⟨hI, _, .frameHole hw hocc' hfn hfr'.1 hfr'.2 hk hpar.1 hpar.2 hidx
                        (by simpa using har), NodesIn.nil rfl rfl⟩
                    · rw [if_neg har] at hrun
                      simp [throw, throwThe, MonadExceptOf.throw] at hrun
                  · rw [if_neg hidx] at hrun
                    simp [throw, throwThe, MonadExceptOf.throw] at hrun
                · rw [if_neg hpar] at hrun
                  simp [throw, throwThe, MonadExceptOf.throw] at hrun
            · rw [if_neg hfr'] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
        · -- `contApp`
          rename_i n us hfn
          by_cases hnm : ctx.names.contains n = true
          · rw [if_pos hnm] at hrun
            simp [throw, throwThe, MonadExceptOf.throw] at hrun
          rw [if_neg hnm] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl, rfl⟩ := hrun
          obtain ⟨nPc, L, hq, hle, hidxfree, hnq, hdsok, nI, cty, hnI, hlen, hkey⟩ := nestCont_inv hv
          rw [hI.lookup n] at hq
          have hdsok' : ∀ x ∈ w.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length := by
            simpa using hdsok
          have hdsw : ∀ x ∈ w.getAppArgs.take nPc, WScoped (ctx.hiAt prog.length) x := fun x hx =>
            WScoped.of_fvarsBelow (wScoped_getAppArgs hwsw x (List.mem_of_mem_take hx))
              (Expr.fvarB_le (hdsok' x hx).2)
          have hdl : (w.getAppArgs.take nPc).length = nPc := by rw [List.length_take]; omega
          obtain ⟨hI', hk, hcase⟩ := nestContKey_deriv hctx ih ihs hsc (by simpa using hnm) hnq
            hdsw hdl ⟨L, hq⟩ hkey (hI.insert n)
          refine ⟨hI', ?_⟩
          rw [hk]
          have hidx' : ∀ x ∈ w.getAppArgs.drop nPc,
              x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by simpa using hidxfree
          have hnC : (nestContainerC ctx st n).2.nodes = st.nodes := by
            unfold nestContainerC; split <;> rfl
          have hnCc : (nestContainerC ctx st n).2.ctorNfs = st.ctorNfs := by
            unfold nestContainerC; split <;> rfl
          rcases hcase with ⟨nI', cty', grp, hnI', hhead, ts, hfr, hn⟩ |
            ⟨hfree, grp, ts, hfr, hmem, hn⟩
          · rw [hnI] at hnI'
            obtain ⟨rfl, rfl⟩ : nI = nI' ∧ cty = cty' := by simpa using hnI'
            exact ⟨_, .contNew hw hocc' hfn (by simpa using hnm) hq hlen hnq hidx' hdsok' hdsw hnI
              hhead hsc hfr, hn.of_eq_left hnC hnCc⟩
          · exact ⟨_, .contHit hw hocc' hfn (by simpa using hnm) hq hlen hnq hidx'
              (fun x hx => ⟨(hdsok' x hx).1, hfree x hx⟩)
              (fun x hx => WScoped.of_fvarsBelow (hdsw x hx) (Expr.fvarB_le (hfree x hx))) hnI
              hmem hfr, hn.of_eq_left hnC hnCc⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-- **A member constructor's run, derived**: the cache invariant kept,
and the constructor derived (`MemberCtorD`). -/
theorem nestMemberCtor_deriv (hctx : NestCtxOk ctx)
    (hwsc : ∀ dep e w, ops.whnf env dep e = .ok w → WScoped dep e → WScoped dep w)
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : nestMemberCtor ops env ctx nF crest st = .ok (ks, tyN, st'))
    (hws : WScoped (ctx.hiAt 0) crest) (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ ∃ ts, MemberCtorD ops env ctx nF crest (ks.map (·.erase)) tyN ts ∧
      NodesIn ops env ctx st st' ts := by
  unfold nestMemberCtor at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨ks₁, nds₁, res, st₁⟩ := r
  simp only at h
  obtain ⟨hI₁, ts, ht, hn⟩ := nestFields_deriv (nestPos_deriv hctx hwsc (whnfWalkFuel crest)).1
    (nestPos_deriv hctx hwsc (whnfWalkFuel crest)).2
    (prog := []) (by simp) ProgScoped.nil nF 0 crest st ks₁ nds₁ res st₁ hr (by simpa using hws) hI
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hu4
  split at h
  · rename_i hok
    split at h
    · rename_i hha
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hok
      refine ⟨hI₁, ts, ⟨nds₁, res, ht, rfl, ?_, hok.1, hok.2, hha⟩, hn⟩
      refine Bool.eq_false_iff.mpr fun hany => hu4 ?_
      rw [List.any_eq_true] at hany ⊢
      obtain ⟨i, hi, hx⟩ := hany
      refine ⟨i, hi, ?_⟩
      revert hx
      rw [erase_getD]
      cases ks₁.getD i .ordinary <;> simp [PosKind.guarded, NestFieldKind.erase]
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A recorded class, at a member constructor's derivation**: some
member constructor `(c, j)` of the block, its member-abstracted crest
derived (`MemberCtorD`, at its output normal form), and `k` a class of a
node of that derivation's forest (`NodeOf`). -/
@[expose] def NodeAtCtor (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (nfs : List (List Expr)) (tbl : List NestCtorNf)
    (k : NestKey) : Prop :=
  ∃ (c : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat) (crest : Expr)
    (ks : List PosKind) (ts : List PosTree),
    ctorsAs[c]? = some cs ∧ cs[j]? = some cA ∧
    instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
    MemberCtorD ops env ctx cA.2 crest ks ((nfs.getD c []).getD j default) ts ∧
    TreeRec ops env ctx tbl ts ∧ NodeOf ctx ts k

theorem NodeAtCtor.mono {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {holes : List Expr}
    {ctorsAs : List (List (ConstantVal × Nat))} {nfs : List (List Expr)}
    {tbl tbl' : List NestCtorNf} (hs : ∀ e ∈ tbl, e ∈ tbl') {k : NestKey}
    (h : NodeAtCtor ops env ctx holes ctorsAs nfs tbl k) :
    NodeAtCtor ops env ctx holes ctorsAs nfs tbl' k := by
  obtain ⟨c, cs, j, cA, crest, ks, ts, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨c, cs, j, cA, crest, ks, ts, h1, h2, h3, h4, h5.mono hs, h6⟩

/-- **The install's positivity stage, derived** (at either position of the
route switch): the context `checkBlockPositivity` builds, and — at a
context whose stored constants are closed, canonical parameters well
scoped at the walk's depth and closed constructors — every stored
constructor's member-abstracted crest derived (`MemberCtorD`) with the
run's kinds and its output normal form. -/
theorem checkBlockPositivity_deriv {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : NestNodes}
    {nst : Bool}
    (hwsc : ∀ dep e w, ops.whnf env₁ dep e = .ok w → WScoped dep e → WScoped dep w)
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs nst = .ok (kinds, nfs, nodes)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find? consts) = some holes ∧
      (NestCtxOk (p.nestCtx fvsP find? consts) →
        (∀ x ∈ fvsP, WScoped ((p.nestCtx fvsP find? consts).hiAt 0) x) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ks ts,
            instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
              = some crest ∧
            MemberCtorD ops env₁ (p.nestCtx fvsP find? consts) cA.2 crest (ks.map (·.erase))
              ((nfs.getD c []).getD j default) ts ∧
            (kinds.getD c []).getD j [] = ks ∧ (nst = false → ∀ k ∈ ks, k.flat = true) ∧
            TreeRec ops env₁ (p.nestCtx fvsP find? consts) nodes.ctors ts) ∧
        ∀ k ∈ nodes.keys, NodeAtCtor ops env₁ (p.nestCtx fvsP find? consts) holes ctorsAs nfs
          nodes.ctors k) := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hthr⟩ := checkBlockPositivity_inv_I h
  refine ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun hctx hpar hcl => ?_⟩
  have hws : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∀ crest,
      instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type) = some crest →
      WScoped ((p.nestCtx fvsP find? consts).hiAt 0) crest :=
    fun c cs hc j cA hj crest hcr =>
      memberCrest_wscoped (nestHoles_ok hctx h3) hpar (hcl c cs hc j cA hj) hcr
  have := hthr (fun st => DerivCache ops env₁ (p.nestCtx fvsP find? consts) st ∧
      ∀ k ∈ st.nodes.toList, NodeAtCtor ops env₁ (p.nestCtx fvsP find? consts) holes ctorsAs nfs
        st.ctorNfs.toList k)
    (fun st st' => ∃ l, st'.ctorNfs.toList = st.ctorNfs.toList ++ l)
    ⟨derivCache_empty, fun k hk => by simp at hk⟩ (fun _ => ⟨[], by simp⟩)
    (fun a b c ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by rw [h₂, h₁, List.append_assoc]⟩)
    (fun c cs hc j cA hj crest hcr st₀ ks tyN st₁ htyN hI hm => by
      obtain ⟨hI₁, ts, hd, ⟨new, hnodes, hnew⟩, ⟨gl, hgl⟩, htr⟩ :=
        nestMemberCtor_deriv hctx hwsc hm (hws c cs hc j cA hj crest hcr) hI.1
      refine ⟨⟨hI₁, fun k hk => ?_⟩, ⟨gl, hgl⟩⟩
      rw [hnodes] at hk
      rcases List.mem_append.mp hk with hk | hk
      · exact (hI.2 k hk).mono fun e he => by rw [hgl]; exact List.mem_append_left _ he
      · exact ⟨c, cs, j, cA, crest, ks.map (·.erase), ts, hc, hj, hcr, htyN ▸ hd, htr,
          hnew k hk⟩)
  obtain ⟨stF, ⟨-, hF⟩, hkeys, hctors, hall⟩ := this
  refine ⟨fun c cs hc j cA hj => ?_, fun k hk => (hF k (hkeys ▸ hk)).mono fun e he => by
    rw [hctors]; exact List.mem_append_right _ he⟩
  obtain ⟨crest, st₀, ks, tyN, st₁, hcr, hI₀, hm, rfl, hks, hfl, ⟨l, hl⟩⟩ := hall c cs hc j cA hj
  obtain ⟨ts, hd, hn⟩ :=
    (nestMemberCtor_deriv hctx hwsc hm (hws c cs hc j cA hj crest hcr) hI₀.1).2
  refine ⟨crest, ks, ts, hcr, hd, hks, hfl, hn.2.2.mono fun e he => ?_⟩
  rw [hctors]
  exact List.mem_append_right _ (by rw [hl]; exact List.mem_append_left _ he)

end ConLeche
