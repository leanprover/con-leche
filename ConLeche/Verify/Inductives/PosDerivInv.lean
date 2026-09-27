module

public import ConLeche.Verify.Inductives.PosDerivFun
public import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.NestContInv
public import ConLeche.Verify.Inductives.PositivityInv
public import ConLeche.Verify.Inductives.HookOuts
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Abstract
import ConLeche.Verify.Leaves

public section

/-!
# The positivity run, inverted ONCE into the derivation

`nestPos_deriv`: a successful run of the positivity function (any fuel,
any `ops` whose whnf keeps terms well scoped) yields the derivation
`PosD` of its input, and a successful seed pass (`nestSeeds`) the
derivation of every seed's frame.  This file is the only place that reads the
run: its cache and its fuel stay here.

The run's state carries the invariant `DerivCache`: every container
lookup is the environment's (`nestContainer`), and every cached
instantiation below the frame holes has a frame derivation under some
well-scoped frame stack — the premise of the derivation's
`contHit` rule.  The run's well-scopedness (`ProgScoped`, `WScoped` of
each walked term) is threaded alongside, because a cache hit's frame was
derived under the frames of its first walk.
-/

-- the throw-branch closers are tried at every split; some are unused
set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {hook : NestHook CheckM}

/-! ## The run's invariant -/

/-- **The run's state invariant**: the container lookups are the
environment's, and every cached instantiation whose parameters lie below
the frame holes is derived (and walked, the hook accepting its
constructors). -/
@[expose] def DerivCache (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (hook : NestHook CheckM) (st : NestState) : Prop :=
  (∀ c r, st.ctorsOf.lookup c = some r → r = nestContainer ctx c) ∧
  ∀ ki ∈ st.keys.toList, (∀ x ∈ ki.key.ds, x.fvarB ≤ ctx.hiAt 0) →
    KeyDR ops env ctx (HookOk hook) ki.key

theorem derivCache_empty : DerivCache ops env ctx hook {} :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

/-- The invariant survives a state that only records more (the hook's
outputs, the nodes' classes, the in-progress list). -/
theorem DerivCache.grow {st st' : NestState} (h : DerivCache ops env ctx hook st)
    (hco : st'.ctorsOf = st.ctorsOf) (hk : st'.keys = st.keys) : DerivCache ops env ctx hook st' :=
  ⟨fun c r hl => h.1 c r (hco ▸ hl), fun ki hki hfv => h.2 ki (hk ▸ hki) hfv⟩

theorem DerivCache.lookup {st : NestState} (h : DerivCache ops env ctx hook st) (c : Name) :
    (nestContainerC ctx st c).1 = nestContainer ctx c := by
  unfold nestContainerC
  split
  · rename_i r hr; exact h.1 c r hr
  · rfl

theorem DerivCache.insert {st : NestState} (h : DerivCache ops env ctx hook st) (c : Name) :
    DerivCache ops env ctx hook (nestContainerC ctx st c).2 := by
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
`NestCtx.concreteKey`).  `NodesIn Q st st' ts`: the run from `st` to `st'`
appended classes of nodes of the forest `ts` only, and every node of `ts`
has its frame walked (`TreeRec Q`). -/

/-- A class of a node of the forest `ts`: a member of its group at its
instantiation, the holes of its occurrence back to their constants. -/
@[expose] def NodeOf (ctx : NestCtx) (ts : List PosTree) (k : NestKey) : Prop :=
  ∃ t ∈ PosTree.forest ts, ∃ c ∈ t.grp.map (·.1), ctx.concreteKey t.occ c t.key = k

/-- The run from `st` to `st'` recorded classes of the forest `ts` only,
and every node of `ts` has its frame walked (`Q`). -/
@[expose] def NodesIn (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (Q : NestCtorNf → Prop) (st st' : NestState) (ts : List PosTree) : Prop :=
  (∃ new : List NestKey, st'.nodes.toList = st.nodes.toList ++ new ∧ ∀ k ∈ new, NodeOf ctx ts k) ∧
  TreeRec ops env ctx Q ts

variable {Q : NestCtorNf → Prop}

theorem NodesIn.nil {st st' : NestState} (h : st'.nodes = st.nodes) :
    NodesIn ops env ctx Q st st' [] :=
  ⟨⟨[], by simp [h], fun _ hk => nomatch hk⟩, TreeRec.nil _⟩

theorem NodesIn.of_eq_left {st st₁ st' : NestState} {ts : List PosTree}
    (h : st₁.nodes = st.nodes) (h' : NodesIn ops env ctx Q st₁ st' ts) :
    NodesIn ops env ctx Q st st' ts := by
  obtain ⟨⟨n, e, a⟩, hr⟩ := h'
  exact ⟨⟨n, by rw [e, h], a⟩, hr⟩

theorem NodesIn.of_eq_right {st st₁ st' : NestState} {ts : List PosTree}
    (h' : NodesIn ops env ctx Q st st₁ ts) (h : st'.nodes = st₁.nodes) :
    NodesIn ops env ctx Q st st' ts := by
  obtain ⟨⟨n, e, a⟩, hr⟩ := h'
  exact ⟨⟨n, by rw [h, e], a⟩, hr⟩

theorem NodesIn.trans {st st₁ st₂ : NestState} {ts₁ ts₂ : List PosTree}
    (h₁ : NodesIn ops env ctx Q st st₁ ts₁) (h₂ : NodesIn ops env ctx Q st₁ st₂ ts₂) :
    NodesIn ops env ctx Q st st₂ (ts₁ ++ ts₂) := by
  obtain ⟨⟨n₁, e₁, a₁⟩, r₁⟩ := h₁
  obtain ⟨⟨n₂, e₂, a₂⟩, r₂⟩ := h₂
  refine ⟨⟨n₁ ++ n₂, by rw [e₂, e₁, List.append_assoc], fun k hk => ?_⟩, r₁.append r₂⟩
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
frame walked. -/
theorem NodesIn.walked {st st₁ : NestState} {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree} (h : NodesIn ops env ctx Q st st₁ ts)
    (hf : FrameRec ops env ctx Q anc key.lvls key.ds grp) :
    NodesIn ops env ctx Q st { st₁ with nodes := st₁.nodes ++
      (grp.map fun p => ctx.concreteKey occ p.1 key).toArray } [.node occ anc key grp ts] := by
  obtain ⟨⟨n, e, a⟩, hr⟩ := h
  refine ⟨⟨n ++ grp.map fun p => ctx.concreteKey occ p.1 key, ?_, fun k hk => ?_⟩,
    TreeRec.node hf hr⟩
  · simp [e]
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨t, ht, rest⟩ := a k hk
    exact ⟨t, PosTree.forest_kids_sub t ht, rest⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    exact ⟨_, PosTree.self_mem_forest, p.1, List.mem_map_of_mem hp, rfl⟩

/-- **A hit's class recorded**: its own container; its (cached) frame and
nodes walked already. -/
theorem NodesIn.hit {st : NestState} {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree} (hmem : key.cname ∈ grp.map (·.1))
    (hf : FrameRec ops env ctx Q anc key.lvls key.ds grp)
    (hts : TreeRec ops env ctx Q ts) :
    NodesIn ops env ctx Q st { st with nodes := st.nodes.push (ctx.concreteKey occ key.cname key) }
      [.node occ anc key grp ts] := by
  refine ⟨⟨[ctx.concreteKey occ key.cname key], by simp, fun k hk => ?_⟩, TreeRec.node hf hts⟩
  simp only [List.mem_singleton] at hk
  subst hk
  exact ⟨_, PosTree.self_mem_forest, key.cname, hmem, rfl⟩

/-- **The inversion's claim about a walk function** (the positivity
function, or its recursive call one fuel lower). -/
@[expose] def RunDeriv (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (hook : NestHook CheckM)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState) (k : NestFieldKind)
    (nf : Expr) (st' : NestState),
    rec prog dep kb e st = .ok (k, nf, st') →
    ctx.hiAt prog.length ≤ dep → WScoped dep e → ProgScoped ctx prog →
    DerivCache ops env ctx hook st →
    DerivCache ops env ctx hook st' ∧
      ∃ ts, PosD ops env ctx (.field prog dep kb e k.erase nf) ts ∧
        NodesIn ops env ctx (HookOk hook) st st' ts

/-! ## Scoping -/

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
  · obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp h
    have hmem : (c, r) ∈ (grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)) := by
      rw [hl]; simp
    obtain ⟨i, hi', he⟩ := List.getElem_of_mem hmem
    have hi'' : i < grp.length := by simpa using hi'
    refine ⟨i, hi'', ?_⟩
    rw [List.getElem_mapIdx] at he
    exact (congrArg Prod.snd he).symm
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

/-- **The telescope walk, derived.** -/
theorem nestFields_deriv (hrec : RunDeriv ops env ctx hook rec)
    {prog : List NestHole} {base : Nat}
    {err : CheckError} (hhi : ctx.hiAt prog.length ≤ base) (hsc : ProgScoped ctx prog) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields rec prog base err nF j cur st = .ok (ks, nds, res, st') →
      WScoped (base + j) cur → DerivCache ops env ctx hook st →
      DerivCache ops env ctx hook st' ∧
        ∃ ts, PosD ops env ctx (.tele prog base nF j cur (ks.map (·.erase)) nds res) ts ∧
          NodesIn ops env ctx (HookOk hook) st st' ts := by
  intro nF
  induction nF with
  | zero =>
    intro j cur st ks nds res st' h _ hI
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hI, [], .teleNil, NodesIn.nil rfl⟩
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
      rename_i r₂ hr₂
      obtain ⟨ks₂, nds₂, res₂, st₂⟩ := r₂
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hws' : WScoped (base + (j + 1)) (b.instantiate1 (.fvar (base + j) a)) := by
        rw [show base + (j + 1) = base + j + 1 by omega]
        exact WScoped.instantiate1 hws.1 0 hws.2
      obtain ⟨hI₂, ts₂, h₂, hn₂⟩ := ih (j + 1) _ st₁ ks₂ nds₂ res₂ st₂ hr₂ hws' hI₁
      exact ⟨hI₂, ts₁ ++ ts₂, .teleCons h₁ h₂, hn₁.trans hn₂⟩
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

/-- **A frame's constructors, derived.** -/
theorem nestCtors_deriv (hrec : RunDeriv ops env ctx hook rec)
    {prog : List NestHole} {hi : Nat}
    {us : List Level} {ds : List Expr} {sub : Name → List Level → Option Expr}
    (hhi : ctx.hiAt prog.length = hi) (hsc : ProgScoped ctx prog)
    (hds : ∀ x ∈ ds, WScoped hi x) (hsub : ∀ c us' r, sub c us' = some r → WScoped hi r) :
    ∀ (cs : List (ConstantVal × Nat)) (st st' : NestState), (∀ x ∈ cs, x.1.type.hasFvar = false) →
      nestCtors ctx ops env hook rec prog hi us ds ds.length sub cs st = .ok st' →
      DerivCache ops env ctx hook st →
      DerivCache ops env ctx hook st' ∧ ∃ ts, PosD ops env ctx (.ctors prog hi us ds sub cs) ts ∧
        NodesIn ops env ctx (HookOk hook) st st' ts ∧
        CtorsRec ops env ctx (HookOk hook) prog hi us ds sub cs := by
  intro cs
  induction cs with
  | nil =>
    intro st st' _ h hI
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, [], .ctorsNil, NodesIn.nil rfl, fun _ hx => nomatch hx⟩
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
      nestFields_deriv hrec (by omega) hsc nF 0 crest st ks nds cur st₁ hr hws hI
    dsimp only at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hu4
    split at h
    · rename_i hok
      split at h
      · simp at h
      rename_i xs hxs
      have hI₁' : DerivCache ops env ctx hook { st₁ with done := st₁.done ++ xs.toArray } :=
        hI₁.grow rfl rfl
      obtain ⟨hI', ts₂, h₂, hn₂, hr₂⟩ :=
        ih _ st' (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) h hI₁'
      have hn₁' : NodesIn ops env ctx (HookOk hook) st
          { st₁ with done := st₁.done ++ xs.toArray } ts₁ :=
        hn₁.of_eq_right rfl
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
          exact ⟨xs, hxs⟩
        · exact hr₂ x hx
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A frame's constructor listing, without its cache.** -/
theorem nestGroupCtors_deriv {nPc : Nat} :
    ∀ (cs : List Name) (st : NestState) (ctors : List (ConstantVal × Nat)) (st' : NestState),
      nestGroupCtors (m := CheckM) ctx nPc cs st = .ok (ctors, st') → DerivCache ops env ctx hook st →
      DerivCache ops env ctx hook st' ∧ groupCtors ctx nPc cs = some ctors ∧ st'.nodes = st.nodes
  | [], st, ctors, st', h, hst => by
    simp only [nestGroupCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hst, rfl, rfl⟩
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
      obtain ⟨hI₁, hg, hnd₁⟩ := nestGroupCtors_deriv cs _ rest st₁ hr (hst.insert c)
      refine ⟨hI₁, ?_, by rw [hnd₁]; unfold nestContainerC; split <;> rfl⟩
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
theorem nestFrame_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx hook rec)
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
    (h : nestFrame ctx ops env hook rec prog hi us ds ds.length grp st = .ok st')
    (hI : DerivCache ops env ctx hook st) :
    DerivCache ops env ctx hook st' ∧ ∃ ts, PosD ops env ctx (.frame prog us ds grp) ts ∧
      NodesIn ops env ctx (HookOk hook) st st' ts ∧ FrameRec ops env ctx (HookOk hook) prog us ds grp := by
  simp only [nestFrame, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i kty hkty
  split at h
  · simp at h
  rename_i v hgc
  obtain ⟨ctors, st₁⟩ := v
  obtain ⟨hI₁, hgc', hnd₁⟩ := nestGroupCtors_deriv _ st ctors st₁ hgc hI
  have hwc' : nestCtors ctx ops env hook rec
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
  obtain ⟨hI₂, ts, hw', hn₂, hcr₂⟩ := nestCtors_deriv hrec hhi' hsc'
    (fun x hx => WScoped.mono (by omega) (hds x hx)) hsub ctors st₁ st' hcl hwc' hI₁
  subst hhi
  refine ⟨hI₂, ts, .frame hne hhd hhdC hnd hinst hblk hgrp hgc' ⟨kty, hkty⟩ hw',
    hn₂.of_eq_left hnd₁, fun ctors' hc' => ?_⟩
  rw [hgc'] at hc'
  obtain rfl := Option.some.inj hc'
  exact hcr₂

/-- **Accepting the group-mates keeps the invariant.** -/
theorem nestAcceptGroup_deriv {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st st' : NestState),
      nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' →
      DerivCache ops env ctx hook st →
      (∀ p ∈ grp, (∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) →
        KeyDR ops env ctx (HookOk hook) ⟨p.1, us, ds⟩) →
      DerivCache ops env ctx hook st'
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

/-- Accepting the group-mates records no class. -/
theorem nestAcceptGroup_nodes {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st st' : NestState),
      nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' →
        st'.nodes = st.nodes
  | [], st, st', h => by
    simp only [nestAcceptGroup, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
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
theorem nestContNew_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx hook rec)
    {prog : List NestHole} (hsc : ProgScoped ctx prog) {kb : Nat} {n : Name} {us : List Level}
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) {nPc : Nat}
    (hnPc : ds.length = nPc) (hq : ∃ L, nestContainer ctx n = some (nPc, L)) {old : Option Nat}
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContNew ctx ops env hook rec prog kb n us ds nPc old st = .ok (k, st'))
    (hI : DerivCache ops env ctx hook st) :
    DerivCache ops env ctx hook st' ∧ k.erase = .nested (kb != 0) ∧ ∃ nI cty grp,
      nestInstType (m := CheckM) ctx (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨n, us, ds⟩
        = .ok (nI, cty) ∧
      grp.head? = some (n, cty) ∧
      ∃ ts, PosD ops env ctx (.frame (nestWalkStack ctx prog ds) us ds grp) ts ∧
        NodesIn ops env ctx (HookOk hook) st st' [.node prog (nestWalkStack ctx prog ds) ⟨n, us, ds⟩ grp ts] := by
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
  obtain ⟨hI₁, tsF, hframe, hnF, hfrec⟩ := nestFrame_deriv (grp := [(n, cty)] ++ ext) hctx hrec rfl hscw hdsw
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
      KeyDR ops env ctx (HookOk hook) ⟨p.1, us, ds⟩ :=
    fun p hp hfree => ⟨_, tsF, by rw [← hroot hfree]; exact hframe, List.mem_map_of_mem hp,
      by rw [← hroot hfree]; exact hfrec, hnF.2⟩
  split at h
  · simp at h
  rename_i st₂ hacc
  have hI₂ : DerivCache ops env ctx hook st₂ :=
    nestAcceptGroup_deriv _ _ _ hacc ⟨hI₁.1, hI₁.2⟩
      fun p hp => hkey p (List.mem_of_mem_drop hp)
  have hacn := nestAcceptGroup_nodes (ctx := ctx) _ _ st₂ hacc
  have hn₂ : NodesIn ops env ctx (HookOk hook) st st₂ tsF := (hnF.of_eq_left rfl).of_eq_right hacn
  have hn₃ := hn₂.walked (occ := prog) (anc := nestWalkStack ctx prog ds) (key := ⟨n, us, ds⟩)
    (grp := (n, cty) :: ext) hfrec
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
      hn₃.of_eq_right rfl⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
    rcases hki with hki | rfl
    · exact hI₂.2 ki hki hfv
    · exact hkey _ List.mem_cons_self hfv

/-- A walked instantiation: at its occurrence's frames, or — below every
frame hole — at the empty stack. -/
theorem contNew_split {prog : List NestHole} {n : Name} {us : List Level} {ds : List Expr}
    {st st' : NestState}
    (hr : ∃ nI cty grp,
      nestInstType (m := CheckM) ctx (ctx.hiAt (nestWalkStack ctx prog ds).length) ⟨n, us, ds⟩
        = .ok (nI, cty) ∧
      grp.head? = some (n, cty) ∧
      ∃ ts, PosD ops env ctx (.frame (nestWalkStack ctx prog ds) us ds grp) ts ∧
        NodesIn ops env ctx (HookOk hook) st st' [.node prog (nestWalkStack ctx prog ds) ⟨n, us, ds⟩ grp ts]) :
    (∃ nI cty grp,
      nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty) ∧
      grp.head? = some (n, cty) ∧ ∃ ts, PosD ops env ctx (.frame prog us ds grp) ts ∧
        NodesIn ops env ctx (HookOk hook) st st' [.node prog prog ⟨n, us, ds⟩ grp ts]) ∨
    ((∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) ∧ ∃ grp ts,
      PosD ops env ctx (.frame [] us ds grp) ts ∧ n ∈ grp.map (·.1) ∧
      NodesIn ops env ctx (HookOk hook) st st' [.node prog [] ⟨n, us, ds⟩ grp ts]) := by
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
theorem nestContKey_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx hook rec)
    {prog : List NestHole} (hsc : ProgScoped ctx prog) {kb : Nat} {n : Name} {us : List Level}
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) {nPc : Nat}
    (hnPc : ds.length = nPc) (hq : ∃ L, nestContainer ctx n = some (nPc, L))
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContKey ctx ops env hook rec prog kb n us ds nPc st = .ok (k, st'))
    (hI : DerivCache ops env ctx hook st) :
    DerivCache ops env ctx hook st' ∧ k.erase = .nested (kb != 0) ∧
      ((∃ nI cty grp,
        nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty) ∧
        grp.head? = some (n, cty) ∧ ∃ ts, PosD ops env ctx (.frame prog us ds grp) ts ∧
          NodesIn ops env ctx (HookOk hook) st st' [.node prog prog ⟨n, us, ds⟩ grp ts]) ∨
       ((∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) ∧ ∃ grp ts,
          PosD ops env ctx (.frame [] us ds grp) ts ∧ n ∈ grp.map (·.1) ∧
          NodesIn ops env ctx (HookOk hook) st st' [.node prog [] ⟨n, us, ds⟩ grp ts])) := by
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
      · obtain ⟨hI', hk, hr⟩ := nestContNew_deriv hctx hrec hsc hnm hquot hds rfl hq h hI
        exact ⟨hI', hk, contNew_split hr⟩
    · obtain ⟨hI', hk, hr⟩ := nestContNew_deriv hctx hrec hsc hnm hquot hds rfl hq h hI
      exact ⟨hI', hk, contNew_split hr⟩

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
    ∀ fuel, RunDeriv ops env ctx hook (nestPos ops env ctx hook fuel)
  | 0 => by
    intro prog dep kb e st k nf st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | fuel + 1 => by
    have ih := nestPos_deriv hctx hwsc fuel
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
        exact ⟨hI, _, .const hw hocc, NodesIn.nil rfl⟩
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
              refine ⟨[], ?_, NodesIn.nil rfl⟩
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
                        (by simpa using har), NodesIn.nil rfl⟩
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
            WScoped.of_fvarsBelow (Expr.WScoped.getAppArgs hwsw x (List.mem_of_mem_take hx))
              (Expr.fvarB_le (hdsok' x hx).2)
          have hdl : (w.getAppArgs.take nPc).length = nPc := by rw [List.length_take]; omega
          obtain ⟨hI', hk, hcase⟩ := nestContKey_deriv hctx ih hsc (by simpa using hnm) hnq
            hdsw hdl ⟨L, hq⟩ hkey (hI.insert n)
          refine ⟨hI', ?_⟩
          rw [hk]
          have hidx' : ∀ x ∈ w.getAppArgs.drop nPc,
              x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by simpa using hidxfree
          have hnC : (nestContainerC ctx st n).2.nodes = st.nodes := by
            unfold nestContainerC; split <;> rfl
          rcases hcase with ⟨nI', cty', grp, hnI', hhead, ts, hfr, hn⟩ |
            ⟨hfree, grp, ts, hfr, hmem, hn⟩
          · rw [hnI] at hnI'
            obtain ⟨rfl, rfl⟩ : nI = nI' ∧ cty = cty' := by simpa using hnI'
            exact ⟨_, .contNew hw hocc' hfn (by simpa using hnm) hq hlen hnq hidx' hdsok' hdsw hnI
              hhead hsc hfr, hn.of_eq_left hnC⟩
          · exact ⟨_, .contHit hw hocc' hfn (by simpa using hnm) hq hlen hnq hidx'
              (fun x hx => ⟨(hdsok' x hx).1, hfree x hx⟩)
              (fun x hx => WScoped.of_fvarsBelow (hdsw x hx) (Expr.fvarB_le (hfree x hx))) hnI
              hmem hfr, hn.of_eq_left hnC⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-- **A member constructor's run, derived**: the cache invariant kept,
and the constructor derived (`MemberCtorD`). -/
theorem nestMemberCtor_deriv (hctx : NestCtxOk ctx)
    (hwsc : ∀ dep e w, ops.whnf env dep e = .ok w → WScoped dep e → WScoped dep w)
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : nestMemberCtor ops env ctx hook nF crest st = .ok (ks, tyN, st'))
    (hws : WScoped (ctx.hiAt 0) crest) (hI : DerivCache ops env ctx hook st) :
    DerivCache ops env ctx hook st' ∧ ∃ ts, MemberCtorD ops env ctx nF crest (ks.map (·.erase)) tyN ts ∧
      NodesIn ops env ctx (HookOk hook) st st' ts := by
  unfold nestMemberCtor at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨ks₁, nds₁, res, st₁⟩ := r
  simp only at h
  obtain ⟨hI₁, ts, ht, hn⟩ := nestFields_deriv (nestPos_deriv hctx hwsc (whnfWalkFuel crest))
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
    (ctorsAs : List (List (ConstantVal × Nat))) (nfs : List (List Expr)) (Q : NestCtorNf → Prop)
    (k : NestKey) : Prop :=
  ∃ (c : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat) (crest : Expr)
    (ks : List PosKind) (ts : List PosTree),
    ctorsAs[c]? = some cs ∧ cs[j]? = some cA ∧
    instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
    MemberCtorD ops env ctx cA.2 crest ks ((nfs.getD c []).getD j default) ts ∧
    TreeRec ops env ctx Q ts ∧ NodeOf ctx ts k

/-! ## The seeds -/

/-- The pure annotation keeps scoping and only shrinks the leaves (the
seeds' premise, `checkBlockPositivity_deriv`). -/
theorem fueledOps_annotate_facts {mode : CheckMode} {F d : Nat} {env : Env} :
    ∀ e e', (fueledOps mode F).annotate env d e = .ok e' → WScoped d e →
      e.looseBVarsBounded 0 = true → WScoped d e' ∧ ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves :=
  fun e _ h hw hb => ⟨annotateCore_WScoped F e h hw, annotateCore_leaves_sub F e h hw hb⟩

/-- **A seed's facts** (`nestSeedKey?` and its annotation): no member and
not `Quot`, a stored container at the seed's parameter count, its
parameters' leaves the canonical variables' (`SeedLeaves`) and well scoped
at the walk's depth. -/
@[expose] def SeedOk (ctx : NestCtx) (s : NestKey × Nat) : Prop :=
  ctx.names.contains s.1.cname = false ∧ s.1.cname ≠ quotName ∧
    (∃ L, nestContainer ctx s.1.cname = some (s.2, L)) ∧ s.1.ds.length = s.2 ∧
    ∀ x ∈ s.1.ds, SeedLeaves ctx x ∧ WScoped (ctx.hiAt 0) x

/-- Annotation, pointwise: well scoped, and its leaves the input's. -/
theorem nestAnnotAll_inv {d : Nat}
    (hann : ∀ e e', ops.annotate env d e = .ok e' → WScoped d e → e.looseBVarsBounded 0 = true →
      WScoped d e' ∧ ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    ∀ {xs ys : List Expr}, nestAnnotAll ops env d xs = .ok ys →
      (∀ x ∈ xs, WScoped d x ∧ x.looseBVarsBounded 0 = true) →
      ys.length = xs.length ∧ ∀ y ∈ ys, ∃ x ∈ xs, WScoped d y ∧ ∀ l ∈ y.fvarLeaves, l ∈ x.fvarLeaves
  | [], ys, h, _ => by
    simp only [nestAnnotAll, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun _ hy => nomatch hy⟩
  | x :: xs, ys, h, hxs => by
    simp only [nestAnnotAll, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i x' hx'
    split at h
    · simp at h
    rename_i xs' hxs'
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hw, hb⟩ := hxs x List.mem_cons_self
    obtain ⟨hw', hl'⟩ := hann x x' hx' hw hb
    obtain ⟨hlen, hall⟩ := nestAnnotAll_inv hann hxs' fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    refine ⟨by simp [hlen], fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, hw', hl'⟩
    · obtain ⟨z, hz, h1, h2⟩ := hall y hy
      exact ⟨z, List.mem_cons_of_mem _ hz, h1, h2⟩

/-- **The seed keys' facts**: every seed the stage reads is `SeedOk`. -/
theorem nestSeedKeys_ok {holes : List Expr} (hh : nestHoles ctx = some holes)
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x)
    (hann : ∀ e e', ops.annotate env (ctx.hiAt 0) e = .ok e' → WScoped (ctx.hiAt 0) e →
      e.looseBVarsBounded 0 = true →
      WScoped (ctx.hiAt 0) e' ∧ ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) :
    ∀ {rs : List (Nat × Expr)} {seeds : List (NestKey × Nat)},
      nestSeedKeys ops env ctx holes rs = .ok seeds → ∀ s ∈ seeds, SeedOk ctx s
  | [], seeds, h, s, hs => by
    simp only [nestSeedKeys, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact nomatch hs
  | (nB, ty) :: rs, seeds, h, s, hs => by
    simp only [nestSeedKeys, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i rest hrest
    have ih := nestSeedKeys_ok hh hholes hpar hann hrest
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ih s hs
    rename_i k nPc hk
    split at h
    · simp at h
    rename_i ds hds
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hs with rfl | hs
    · obtain ⟨hnm, hq, hC, hlen, hleaf, hw⟩ := nestSeedKey?_spec hk
      have hwk := hw hholes hpar
      obtain ⟨hlen', hall⟩ := nestAnnotAll_inv hann hds fun x hx =>
        ⟨hwk x hx, Expr.bvarB_le (Nat.le_of_eq (hleaf x hx).1)⟩
      refine ⟨hnm, hq, hC, by rw [hlen', hlen], fun y hy => ?_⟩
      obtain ⟨x, hx, hwy, hly⟩ := hall y hy
      refine ⟨fun hs' hh' l hl => ?_, hwy⟩
      rw [hh] at hh'
      obtain rfl := Option.some.inj hh'
      exact (hleaf x hx).2 l (hly l hl)
    · exact ih s hs

/-- **A recorded class, at a seed's derivation**: some seed's frame
derived (`PosD.seed`), and `k` a class of a node of its forest. -/
@[expose] def NodeAtSeed (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (Q : NestCtorNf → Prop) (k : NestKey) : Prop :=
  ∃ (key : NestKey) (ts : List PosTree), PosD ops env ctx (.seed key) ts ∧
    TreeRec ops env ctx Q ts ∧ NodeOf ctx ts k

/-- **The seeds, derived**: the cache invariant kept, every class the
pass records a node of a seed's derivation. -/
theorem nestSeeds_deriv (hctx : NestCtxOk ctx)
    (hwsc : ∀ dep e w, ops.whnf env dep e = .ok w → WScoped dep e → WScoped dep w) :
    ∀ (ks : List (NestKey × Nat)) (st st' : NestState), nestSeeds ops env ctx hook ks st = .ok st' →
      (∀ s ∈ ks, SeedOk ctx s) → DerivCache ops env ctx hook st →
      DerivCache ops env ctx hook st' ∧
        ∃ new : List NestKey, st'.nodes.toList = st.nodes.toList ++ new ∧
          ∀ k ∈ new, NodeAtSeed ops env ctx (HookOk hook) k
  | [], st, st', h, _, hI => by
    simp only [nestSeeds, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, [], by simp, fun _ hk => nomatch hk⟩
  | (key, nPc) :: ks, st, st', h, hok, hI => by
    obtain ⟨n, us, ds⟩ := key
    simp only [nestSeeds, bind, Except.bind] at h
    split at h
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hchk
    have hchk' : ∀ x ∈ ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt 0 := by simpa using hchk
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨k₁, st₁⟩ := r
    obtain ⟨hnm, hquot, ⟨L, hC⟩, hlen, hds⟩ := hok (⟨n, us, ds⟩, nPc) List.mem_cons_self
    obtain ⟨hI₁, -, hcase⟩ := nestContKey_deriv hctx (nestPos_deriv hctx hwsc _) ProgScoped.nil
      hnm hquot (fun x hx => (hds x hx).2) hlen ⟨L, hC⟩ hr hI
    have hC' : nestContainer ctx n = some (ds.length, L) := by rw [hlen]; exact hC
    have hseed : ∃ ts, PosD ops env ctx (.seed ⟨n, us, ds⟩) ts ∧
        NodesIn ops env ctx (HookOk hook) st st₁ ts := by
      rcases hcase with ⟨nI, cty, grp, -, hhead, ts, hfr, hn⟩ | ⟨-, grp, ts, hfr, hmem, hn⟩
      · refine ⟨_, .seed hnm hquot hC' hchk' (fun x hx => (hds x hx).2) (fun x hx => (hds x hx).1)
          ?_ hfr, hn⟩
        cases grp with
        | nil => simp at hhead
        | cons p ps =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          exact List.mem_cons_self
      · exact ⟨_, .seed hnm hquot hC' hchk' (fun x hx => (hds x hx).2) (fun x hx => (hds x hx).1)
          hmem hfr, hn⟩
    obtain ⟨ts, hD, ⟨new₁, hn₁, hnew₁⟩, htr₁⟩ := hseed
    obtain ⟨hI₂, new₂, hn₂, hnew₂⟩ :=
      nestSeeds_deriv hctx hwsc ks st₁ st' h (fun s hs => hok s (List.mem_cons_of_mem _ hs)) hI₁
    refine ⟨hI₂, new₁ ++ new₂, by rw [hn₂, hn₁, List.append_assoc], fun k hk => ?_⟩
    rcases List.mem_append.mp hk with hk | hk
    · exact ⟨_, ts, hD, htr₁, hnew₁ k hk⟩
    · exact hnew₂ k hk

/-- **The install's positivity stage, derived**: the context `checkBlockPositivity` builds, and — at a
context whose stored constants are closed, canonical parameters well
scoped at the walk's depth, closed constructors and an annotation that
keeps scoping and leaves — every stored constructor's member-abstracted
crest derived (`MemberCtorD`) with the run's kinds and its output normal
form, every node of it walked (the hook accepting every walked
constructor, `HookOk`) and the hook accepting the constructor itself
(`nestMemberNf`, node `0`); and every recorded class a node of a member
constructor's derivation or of a seed's. -/
theorem checkBlockPositivity_deriv {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {keys : List NestKey}
    {done : List (Nat × Nat × Expr)}
    (hwsc : ∀ dep e w, ops.whnf env₁ dep e = .ok w → WScoped dep e → WScoped dep w)
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs hook
      = .ok (kinds, nfs, keys, done)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find? consts) = some holes ∧
      (NestCtxOk (p.nestCtx fvsP find? consts) →
        (∀ x ∈ fvsP, WScoped ((p.nestCtx fvsP find? consts).hiAt 0) x) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) →
        (∀ e e', ops.annotate env₁ ((p.nestCtx fvsP find? consts).hiAt 0) e = .ok e' →
          WScoped ((p.nestCtx fvsP find? consts).hiAt 0) e → e.looseBVarsBounded 0 = true →
          WScoped ((p.nestCtx fvsP find? consts).hiAt 0) e' ∧
            ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ks ts,
            instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
              = some crest ∧
            MemberCtorD ops env₁ (p.nestCtx fvsP find? consts) cA.2 crest (ks.map (·.erase))
              ((nfs.getD c []).getD j default) ts ∧
            (kinds.getD c []).getD j [] = ks ∧
            TreeRec ops env₁ (p.nestCtx fvsP find? consts) (HookOk hook) ts ∧
            HookOk hook (nestMemberNf (p.nestCtx fvsP find? consts) cA.1
              ((nfs.getD c []).getD j default))) ∧
        (∀ k ∈ keys, NodeAtCtor ops env₁ (p.nestCtx fvsP find? consts) holes ctorsAs nfs
          (HookOk hook) k ∨ NodeAtSeed ops env₁ (p.nestCtx fvsP find? consts) (HookOk hook) k)) := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hthr⟩ := checkBlockPositivity_inv_I h
  refine ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun hctx hpar hcl hann => ?_⟩
  have hws : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∀ crest,
      instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type) = some crest →
      WScoped ((p.nestCtx fvsP find? consts).hiAt 0) crest :=
    fun c cs hc j cA hj crest hcr =>
      memberCrest_wscoped (nestHoles_ok hctx h3) hpar (hcl c cs hc j cA hj) hcr
  have := hthr (fun st => DerivCache ops env₁ (p.nestCtx fvsP find? consts) hook st ∧
      ∀ k ∈ st.nodes.toList, NodeAtCtor ops env₁ (p.nestCtx fvsP find? consts) holes ctorsAs nfs
        (HookOk hook) k)
    (fun _ _ => True)
    ⟨derivCache_empty, fun k hk => by simp at hk⟩ (fun _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun c cs hc j cA hj crest hcr st₀ ks tyN st₁ xs htyN hI hm hx => by
      obtain ⟨hI₁, ts, hd, ⟨new, hnodes, hnew⟩, htr⟩ :=
        nestMemberCtor_deriv hctx hwsc hm (hws c cs hc j cA hj crest hcr) hI.1
      refine ⟨⟨hI₁.grow rfl rfl, fun k hk => ?_⟩, trivial⟩
      have hk' : k ∈ st₁.nodes.toList := hk
      rw [hnodes] at hk'
      rcases List.mem_append.mp hk' with hk' | hk'
      · exact hI.2 k hk'
      · exact ⟨c, cs, j, cA, crest, ks.map (·.erase), ts, hc, hj, hcr, htyN ▸ hd, htr,
          hnew k hk'⟩)
  obtain ⟨stM, seeds, stF, ⟨hIM, hM⟩, hseeds, hstF, hkeys, -, hall⟩ := this
  have hsok := nestSeedKeys_ok h3 (nestHoles_ok hctx h3) hpar hann hseeds
  obtain ⟨-, new, hnew, hnewS⟩ := nestSeeds_deriv hctx hwsc seeds stM stF hstF hsok hIM
  refine ⟨fun c cs hc j cA hj => ?_, fun k hk => ?_⟩
  · obtain ⟨crest, st₀, ks, tyN, st₁, xs, hcr, hI₀, hm, hx, rfl, hks, -⟩ := hall c cs hc j cA hj
    obtain ⟨ts, hd, hn⟩ :=
      (nestMemberCtor_deriv hctx hwsc hm (hws c cs hc j cA hj crest hcr) hI₀.1).2
    exact ⟨crest, ks, ts, hcr, hd, hks, hn.2, ⟨xs, hx⟩⟩
  · rw [hkeys, hnew] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl (hM k hk)
    · exact Or.inr (hnewS k hk)

end ConLeche
