module

public import ConLeche.Verify.Inductives.PosDerivFun
public import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.NestContInv
public import ConLeche.Verify.Inductives.PositivityInv
public import ConLeche.Verify.Inductives.HoleImg
import ConLeche.Kernel.Inductives.RecCheck
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The positivity run, inverted ONCE into the derivation

`nestPos_deriv`: a successful run of the positivity function (any fuel,
any `ops` whose whnf keeps terms well scoped) yields the derivation
`PosD` of its input, and a successful seed pass (`nestSeeds`) the
derivation of every seed's frame.  This file is the only place that reads the
run: its cache and its fuel stay here.

The run's state carries the invariant `DerivCache`: every cached
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

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-! ## The run's invariant -/

/-- **The run's state invariant**: every cached instantiation whose
parameters lie below the frame holes is derived. -/
@[expose] def DerivCache (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (st : NestState) :
    Prop :=
  ∀ ki ∈ st.keys.toList, (∀ x ∈ ki.ds, x.fvarB ≤ ctx.hiAt 0) →
    KeyDR ops env ctx st.ctorNfs.toList ki

theorem derivCache_empty : DerivCache ops env ctx {} :=
  fun _ h => by simp at h

/-- The invariant survives a state that only records more constructors. -/
theorem DerivCache.grow {st st' : NestState} (h : DerivCache ops env ctx st)
    (hk : st'.keys = st.keys)
    (hc : ∀ e ∈ st.ctorNfs.toList, e ∈ st'.ctorNfs.toList) : DerivCache ops env ctx st' :=
  fun ki hki hfv => (h ki (hk ▸ hki) hfv).mono hc

/-- The run from `st` to `st'` recorded constructors only on top (K.53′),
and every node of `ts` has its frame recorded at `st'`. -/
@[expose] def NodesIn (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (st st' : NestState)
    (ts : List PosTree) : Prop :=
  (∃ newC : List NestCtorNf, st'.ctorNfs.toList = st.ctorNfs.toList ++ newC) ∧
  TreeRec ops env ctx st'.ctorNfs.toList ts

theorem NodesIn.nil {st st' : NestState} (hc : st'.ctorNfs = st.ctorNfs) :
    NodesIn ops env ctx st st' [] :=
  ⟨⟨[], by simp [hc]⟩, TreeRec.nil _⟩

theorem NodesIn.of_eq_left {st st₁ st' : NestState} {ts : List PosTree}
    (hc : st₁.ctorNfs = st.ctorNfs)
    (h' : NodesIn ops env ctx st₁ st' ts) : NodesIn ops env ctx st st' ts := by
  obtain ⟨⟨nc, ec⟩, hr⟩ := h'
  exact ⟨⟨nc, by rw [ec, hc]⟩, hr⟩

/-- A later state that records more constructors. -/
theorem NodesIn.grow {st st₁ st' : NestState} {ts : List PosTree}
    (h' : NodesIn ops env ctx st st₁ ts)
    (hc : ∃ l, st'.ctorNfs.toList = st₁.ctorNfs.toList ++ l) : NodesIn ops env ctx st st' ts := by
  obtain ⟨⟨nc, ec⟩, hr⟩ := h'
  obtain ⟨l, hl⟩ := hc
  exact ⟨⟨nc ++ l, by rw [hl, ec, List.append_assoc]⟩,
    hr.mono fun x hx => by rw [hl]; exact List.mem_append_left _ hx⟩

theorem NodesIn.of_eq_right {st st₁ st' : NestState} {ts : List PosTree}
    (h' : NodesIn ops env ctx st st₁ ts)
    (hc : st'.ctorNfs = st₁.ctorNfs) : NodesIn ops env ctx st st' ts :=
  h'.grow ⟨[], by simp [hc]⟩

theorem NodesIn.trans {st st₁ st₂ : NestState} {ts₁ ts₂ : List PosTree}
    (h₁ : NodesIn ops env ctx st st₁ ts₁) (h₂ : NodesIn ops env ctx st₁ st₂ ts₂) :
    NodesIn ops env ctx st st₂ (ts₁ ++ ts₂) := by
  obtain ⟨⟨c₁, f₁⟩, r₁⟩ := h₁
  obtain ⟨⟨c₂, f₂⟩, r₂⟩ := h₂
  exact ⟨⟨c₁ ++ c₂, by rw [f₂, f₁, List.append_assoc]⟩,
    (r₁.mono fun x hx => by rw [f₂]; exact List.mem_append_left _ hx).append r₂⟩

/-- **A walked node**: its frame's constructors recorded. -/
theorem NodesIn.walked {st st₁ : NestState} {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree} (h : NodesIn ops env ctx st st₁ ts)
    (hf : FrameRec ops env ctx st₁.ctorNfs.toList anc key.lvls key.ds grp) :
    NodesIn ops env ctx st st₁ [.node occ anc key grp ts] := by
  obtain ⟨hc, hr⟩ := h
  exact ⟨hc, TreeRec.node hf hr⟩

/-- **A hit**: its (cached) frame and nodes recorded already. -/
theorem NodesIn.hit {st : NestState} {occ anc : List NestHole} {key : NestKey}
    {grp : List (Name × Expr)} {ts : List PosTree}
    (hf : FrameRec ops env ctx st.ctorNfs.toList anc key.lvls key.ds grp)
    (hts : TreeRec ops env ctx st.ctorNfs.toList ts) :
    NodesIn ops env ctx st st [.node occ anc key grp ts] :=
  ⟨⟨[], by simp⟩, TreeRec.node hf hts⟩

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
      ∃ ts, PosD ops env ctx (.field prog dep kb e k nf) ts ∧ NodesIn ops env ctx st st' ts

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

/-- A frame's hole is one of the group's variables. -/
theorem grpHoles_hole {hi : Nat} {grp : List (Name × Expr)} {x : Expr}
    (h : x ∈ grpHoles hi grp) :
    ∃ i, ∃ hi' : i < grp.length, x = .fvar (hi + i) grp[i].2 := by
  obtain ⟨i, hi', he⟩ := List.getElem_of_mem h
  have hi'' : i < grp.length := by simpa [grpHoles] using hi'
  refine ⟨i, hi'', ?_⟩
  rw [← he]
  simp [grpHoles, List.getElem_mapIdx]

/-- The container's type former at the key (its hole's type) is well
scoped where the key's parameters are. -/
theorem nestInstType_wscoped (hc : NestCtxOk ctx) {hi d : Nat} {key : NestKey} {nI : Nat}
    {cty : Expr} (h : nestInstType (m := CheckM) ctx hi key = .ok (nI, cty))
    (hds : ∀ x ∈ key.ds, WScoped d x) : WScoped d cty := by
  obtain ⟨cvC, caps, hf, -, hcty, -⟩ := nestInstType_inv h
  refine wscoped_instPisWith hds (WScoped.of_not_hasFvar ?_) hcty
  rw [ConLeche.Expr.hasFvar_instantiateLevelParams]
  exact hc _ _ hf

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
theorem nestFields_deriv (hrec : RunDeriv ops env ctx rec)
    {prog : List NestHole} {base : Nat}
    {err : CheckError} (hhi : ctx.hiAt prog.length ≤ base) (hsc : ProgScoped ctx prog) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields rec prog base err nF j cur st = .ok (ks, nds, res, st') →
      WScoped (base + j) cur → DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧
        ∃ ts, PosD ops env ctx (.tele prog base nF j cur ks nds res) ts ∧
          NodesIn ops env ctx st st' ts := by
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

/-! ## The frame -/

section Frame

variable {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}

/-- **A constructor's walk, as the run output it**: the constructor
`cA`, instantiated as the frame instantiates it (`crest`), has a derived
telescope whose kinds and normal form (closed over the fields) are the
run's output `o`, U4 and the result's checks, and its nodes recorded in
`tbl`. -/
@[expose] def CtorOut (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (tbl : List NestCtorNf) (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
    (names : List Name) (holes : List Expr) (cA : ConstantVal × Nat)
    (o : List NestFieldKind × Expr) : Prop :=
  ∃ crest nds cur ts, nestCrest names us ds holes
      (cA.1.type.instantiateLevelParams cA.1.levelParams us) = some crest ∧
    (∃ ty, ops.inferType env hi crest = .ok ty) ∧
    PosD ops env ctx (.tele prog hi cA.2 0 crest o.1 nds cur) ts ∧
    o.2 = closeTelescope nds hi cur ∧
    ((List.range cA.2).any fun i => o.1.getD i .ordinary != .ordinary &&
      structUsedLater (closeTelescope nds hi cur) 0 i) = false ∧
    nestResHead cur = true ∧
    cur.getAppArgs.all (fun x => !x.nestOcc ctx.names ctx.nP hi) = true ∧
    TreeRec ops env ctx tbl ts

theorem CtorOut.mono {tbl tbl' : List NestCtorNf} (hs : ∀ e ∈ tbl, e ∈ tbl')
    {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
    {names : List Name} {holes : List Expr} {cA : ConstantVal × Nat}
    {o : List NestFieldKind × Expr} (h : CtorOut ops env ctx tbl prog hi us ds names holes cA o) :
    CtorOut ops env ctx tbl' prog hi us ds names holes cA o := by
  obtain ⟨crest, nds, cur, ts, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨crest, nds, cur, ts, h1, h2, h3, h4, h5, h6, h7, h8.mono hs⟩

/-- **A frame's constructors, derived** — the root frame's and every
container frame's: the constructor list derived, recorded, and every
constructor's output (`CtorOut`). -/
theorem nestCtors_deriv
    {recC : Expr → List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)}
    (hrec : ∀ x, RunDeriv ops env ctx (recC x))
    {prog : List NestHole} {hi : Nat}
    {us : List Level} {ds : List Expr} {names : List Name} {holes : List Expr}
    (hhi : ctx.hiAt prog.length = hi) (hsc : ProgScoped ctx prog)
    (hds : ∀ x ∈ ds, WScoped hi x) (hholes : ∀ x ∈ holes, WScoped hi x)
    (hlen : names.length ≤ holes.length) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState) (os : List (List NestFieldKind × Expr))
      (st' : NestState), (∀ x ∈ cs, x.1.type.hasFvar = false) →
      nestCtors ctx ops env recC prog hi us ds names holes cs st = .ok (os, st') →
      DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧ ∃ ts, PosD ops env ctx (.ctors prog hi us ds names holes cs) ts ∧
        NodesIn ops env ctx st st' ts ∧
        CtorsRec ops env ctx st'.ctorNfs.toList prog hi us ds names holes cs ∧
        os.length = cs.length ∧
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ o, os[j]? = some o ∧
          CtorOut ops env ctx st'.ctorNfs.toList prog hi us ds names holes cA o := by
  intro cs
  induction cs with
  | nil =>
    intro st os st' _ h hI
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, [], .ctorsNil, NodesIn.nil rfl, (fun _ hx => nomatch hx), rfl,
      fun _ _ hj => by simp at hj⟩
  | cons x cs ih =>
    intro st os st' hcl h hI
    obtain ⟨cv, nF⟩ := x
    simp only [nestCtors, bind, Except.bind] at h
    have hnd : Name.nodup cv.levelParams = true := by
      rcases hb : Name.nodup cv.levelParams
      · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      · rfl
    rw [ite_eq_left hnd] at h
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
      refine WScoped_nestCrest ?_ hlen
        (fun x hx => (List.mem_append.mp hx).elim (hds x) (hholes x)) hcrest'
      rw [ConLeche.Expr.hasFvar_instantiateLevelParams]
      exact hcl _ List.mem_cons_self
    obtain ⟨hI₁, ts₁, h₁, hn₁⟩ :=
      nestFields_deriv (hrec crest) (by omega) hsc nF 0 crest st ks nds cur st₁ hr hws hI
    dsimp only at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hu4
    split at h
    · rename_i hok
      split at h
      · simp at h
      rename_i r₂ hr₂
      obtain ⟨os₂, st₂⟩ := r₂
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hI₁' : DerivCache ops env ctx
          { st₁ with ctorNfs := (st₁.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur)) } :=
        hI₁.grow rfl fun e he => by
          show e ∈ (st₁.ctorNfs.push _).toList
          rw [Array.toList_push]; exact List.mem_append_left _ he
      obtain ⟨hI', ts₂, h₂, hn₂, hr₂', hlen₂, hout₂⟩ :=
        ih _ os₂ st₂ (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) hr₂ hI₁'
      have hn₁' : NodesIn ops env ctx st
          { st₁ with ctorNfs := (st₁.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur)) } ts₁ :=
        hn₁.grow ⟨[nestCtorNf ctx prog hi us ds cv nds cur], Array.toList_push⟩
      have hu4' : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
          structUsedLater (closeTelescope nds hi cur) 0 i) = false := by simpa using hu4
      simp only [Bool.and_eq_true] at hok
      have hsub₂ : ∀ e ∈ ({ st₁ with ctorNfs := (st₁.ctorNfs.push
          (nestCtorNf ctx prog hi us ds cv nds cur)) } : NestState).ctorNfs.toList,
          e ∈ st₂.ctorNfs.toList := by
        obtain ⟨⟨nc, hnc⟩, -⟩ := hn₂
        intro e he; rw [hnc]; exact List.mem_append_left _ he
      refine ⟨hI', ts₁ ++ ts₂, .ctorsCons hnd hcrest' hty hsv h₁ hu4' hok.1 hok.2 h₂,
        hn₁'.trans hn₂, fun x hx => ?_, by simp [hlen₂], fun j cA hj => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · intro crest'' ks'' nds'' cur'' ts'' hcr'' hd''
          rw [hcrest'] at hcr''
          obtain rfl := Option.some.inj hcr''
          obtain ⟨-, rfl, rfl⟩ := posD_tele_fun (by simpa using h₁) hd''
          exact hsub₂ _ (by simp)
        · exact hr₂' x hx
      · cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          refine ⟨_, rfl, crest, nds, cur, ts₁, hcrest', ⟨ty, hty⟩, h₁, rfl, hu4', hok.1, hok.2,
            ?_⟩
          exact hn₁'.2.mono hsub₂
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj ⊢
          exact hout₂ j cA hj
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A frame's constructor listing.** -/
theorem nestGroupCtors_deriv {nPc : Nat} :
    ∀ (cs : List Name) (ctors : List (ConstantVal × Nat)),
      nestGroupCtors (m := CheckM) ctx nPc cs = .ok ctors → groupCtors ctx nPc cs = some ctors
  | [], ctors, h => by
    simp only [nestGroupCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | c :: cs, ctors, h => by
    simp only [nestGroupCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i q hq
    have hq' := unwrapOr_ok hq
    obtain ⟨nP', L⟩ := q
    dsimp only at h
    split at h
    · rename_i hok
      split at h
      · simp at h
      rename_i rest hr
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hg := nestGroupCtors_deriv cs rest hr
      simp only [groupCtors, hq']
      rw [ite_eq_left (by simpa using hok), hg]
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
    (h : nestFrame ctx ops env rec prog hi us ds ds.length grp st = .ok st')
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ ∃ ts, PosD ops env ctx (.frame prog us ds grp) ts ∧
      NodesIn ops env ctx st st' ts ∧ FrameRec ops env ctx st'.ctorNfs.toList prog us ds grp := by
  simp only [nestFrame, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i kty hkty
  split at h
  · simp at h
  rename_i ctors hgc
  have hgc' := nestGroupCtors_deriv _ ctors hgc
  split at h
  · simp at h
  rename_i v' hv'
  obtain ⟨os, st₂⟩ := v'
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hwc' : nestCtors ctx ops env (fun _ => rec)
      ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length) us ds (grp.map (·.1))
      (grpHoles hi grp) ctors st = .ok (os, st₂) := by
    rw [← grpNews_mapIdx]; exact hv'
  have hlenN : ((grpNews us ds hi grp).reverse ++ prog).length = grp.length + prog.length := by
    simp [grpNews]
  have hhi' : ctx.hiAt ((grpNews us ds hi grp).reverse ++ prog).length = hi + grp.length := by
    rw [hlenN, ← hhi]; simp only [NestCtx.hiAt]; omega
  have hsc' : ProgScoped ctx ((grpNews us ds hi grp).reverse ++ prog) := by
    subst hhi; exact hsc.push hds grp
  have hsub : ∀ x ∈ grpHoles hi grp, WScoped (hi + grp.length) x := by
    intro x hx
    obtain ⟨i, hi', rfl⟩ := grpHoles_hole hx
    obtain ⟨nI, hnI⟩ := hinst _ (List.getElem_mem hi')
    simp only [WScoped]
    exact ⟨by omega, WScoped.mono (by omega) (nestInstType_wscoped hctx hnI hds)⟩
  have hcl : ∀ x ∈ ctors, x.1.type.hasFvar = false := by
    intro x hx
    obtain ⟨c, -, nP', L, hL, hxL⟩ := groupCtors_mem hgc' x hx
    obtain ⟨n, nPc, hmem⟩ := nestContainer_mem hL x hxL
    exact hctx _ _ hmem
  obtain ⟨hI₂, ts, hw', hn₂, hcr₂, -⟩ := nestCtors_deriv (fun _ => hrec) hhi' hsc'
    (fun x hx => WScoped.mono (by omega) (hds x hx)) hsub (by simp [grpHoles]) ctors st os st₂
    hcl hwc' hI
  subst hhi
  refine ⟨hI₂, ts, .frame hne hhd hhdC hnd hinst hblk hgrp hgc' ⟨kty, hkty⟩ hw',
    hn₂, fun ctors' hc' => ?_⟩
  rw [hgc'] at hc'
  obtain rfl := Option.some.inj hc'
  exact hcr₂

/-- **Accepting the group keeps the invariant**: every key it adds is
one of the group's. -/
theorem nestAcceptGroup_mem {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (keys : Array NestKey) (k : NestKey),
      k ∈ (nestAcceptGroup us ds grp keys).toList → k ∈ keys.toList ∨ ∃ p ∈ grp, k = ⟨p.1, us, ds⟩
  | [], keys, k, h => .inl h
  | (c, ty) :: rest, keys, k, h => by
    unfold nestAcceptGroup at h
    rcases nestAcceptGroup_mem rest _ k h with h | ⟨p, hp, rfl⟩
    · split at h
      · exact .inl (by assumption)
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact .inl h
        · exact .inr ⟨(c, ty), List.mem_cons_self, rfl⟩
    · exact .inr ⟨p, List.mem_cons_of_mem _ hp, rfl⟩

/-- **A new (or re-walked) instantiation, derived**: its frame, under the
current frames, the container at the frame's head, the container's
whole recorded block its group. -/
theorem nestContNew_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    {prog : List NestHole} (hsc : ProgScoped ctx prog) {kb : Nat} {n : Name} {us : List Level}
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) {nPc : Nat}
    (hnPc : ds.length = nPc) (hq : ∃ L, nestContainer ctx n = some (nPc, L)) {nI : Nat}
    {cty : Expr}
    (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty))
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContNew ctx ops env rec prog kb n us ds nPc cty st = .ok (k, st'))
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ k = .nested (kb != 0) ∧ ∃ nI cty grp,
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
    rw [ite_eq_left (List.all_eq_true.mpr fun x hx => by simpa using hfree x hx)]
  -- the type former's checks, at the walk's (smaller) hole range
  have hni : nestInstType (m := CheckM) ctx (ctx.hiAt (nestWalkStack ctx prog ds).length)
      ⟨n, us, ds⟩ = .ok (nI, cty) := by
    refine nestInstType_mono_hi ?_ hnI
    unfold nestWalkStack; split <;> simp [NestCtx.hiAt]
  simp only [nestContNew, bind, Except.bind] at h
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
    (by simpa using hmap') hfr hI
  have hkey : ∀ p ∈ (n, cty) :: ext, (∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) →
      KeyDR ops env ctx st₁.ctorNfs.toList ⟨p.1, us, ds⟩ :=
    fun p hp hfree => ⟨_, tsF, by rw [← hroot hfree]; exact hframe, List.mem_map_of_mem hp,
      by rw [← hroot hfree]; exact hfrec, hnF.2⟩
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hn₂ : NodesIn ops env ctx st st₁ tsF := hnF.of_eq_left rfl
  have hn₃ := hn₂.walked (occ := prog) (anc := nestWalkStack ctx prog ds) (key := ⟨n, us, ds⟩)
    (grp := (n, cty) :: ext) hfrec
  refine ⟨fun ki hki hfv => ?_, rfl, nI, cty, _, hni, rfl, tsF, hframe,
    hn₃.of_eq_right rfl⟩
  dsimp only at hki
  split at hki
  · rcases nestAcceptGroup_mem _ _ ki hki with hki | ⟨p, hp, rfl⟩
    · exact hI₁ ki hki hfv
    · exact hkey p hp hfv
  · exact hI₁ ki hki hfv

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
    rw [ite_eq_left hfree] at hfr hn
    refine Or.inr ⟨fun x hx => by simpa using List.all_eq_true.mp hfree x hx, grp, ts, hfr, ?_, hn⟩
    cases grp with
    | nil => simp at hhead
    | cons p ps =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact List.mem_cons_self
  · rename_i hfree
    rw [ite_eq_right hfree] at hfr hn
    exact Or.inl ⟨nI, cty, grp, hnI, hhead, ts, hfr, hn⟩

/-- **The instantiation met, derived**: in progress it rejects;
otherwise the frame is derived here, or the key is a hit below every
frame hole with a derived frame elsewhere. -/
theorem nestContKey_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    {prog : List NestHole} (hsc : ProgScoped ctx prog) {kb : Nat} {n : Name} {us : List Level}
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) {nPc : Nat}
    (hnPc : ds.length = nPc) (hq : ∃ L, nestContainer ctx n = some (nPc, L)) {nI : Nat}
    {cty : Expr}
    (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty))
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContKey ctx ops env rec prog kb n us ds nPc cty st = .ok (k, st'))
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ k = .nested (kb != 0) ∧
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
    · -- a hit
      rename_i hhit
      simp only [Bool.and_eq_true, Array.contains_iff_mem] at hhit
      obtain ⟨hfree, hmemK⟩ := hhit
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfree' : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0 := by simpa using hfree
      obtain ⟨grp, ts, hfr, hmem, hfrec, htrec⟩ := hI _ (Array.mem_toList_iff.mpr hmemK) hfree'
      exact ⟨hI, rfl, Or.inr ⟨hfree', grp, ts, hfr, hmem,
        NodesIn.hit (key := ⟨n, us, ds⟩) hfrec htrec⟩⟩
    · obtain ⟨hI', hk, hr⟩ := nestContNew_deriv hctx hrec hsc hnm hquot hds rfl hq hnI h hI
      exact ⟨hI', hk, contNew_split hr⟩

end Frame

/-! ## THE INVERSION -/

/-- **THE ONE INVERSION OF THE POSITIVITY RUN.**  A successful run of
`nestPos` — at any fuel, under any `ops` whose whnf keeps terms well
scoped, at a context whose stored constants are closed — keeps the
cache invariant, and when it leaves no restart pending, its input is
derived (`PosD`), with the run's kind and
normal form. -/
theorem nestPos_deriv (hctx : NestCtxOk ctx) (hroot : NestRootOk ctx)
    (hwsc : ∀ dep e w, ops.whnf env dep e = .ok w → WScoped dep e → WScoped dep w) :
    ∀ fuel, RunDeriv ops env ctx (nestPos ops env ctx fuel)
  | 0 => by
    intro prog dep kb e st k nf st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | fuel + 1 => by
    have ih := nestPos_deriv hctx hroot hwsc fuel
    intro prog dep kb e st k nf st' hrun hhi hws hsc hI
    rw [nestPos] at hrun
    cases hw : ops.whnf env dep e with
    | error err => simp [hw, bind, Except.bind] at hrun
    | ok w =>
      simp only [hw, bind, Except.bind] at hrun
      have hwsw := hwsc dep e w hw hws
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false
      · rw [ite_eq_left (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        exact ⟨hI, _, .const hw hocc, NodesIn.nil rfl⟩
      have hocc' : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true := by simpa using hocc
      rw [ite_eq_right (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        rename_i a b bm
        by_cases ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true
        · rw [ite_eq_left ha] at hrun
          simp [throw, throwThe, MonadExceptOf.throw] at hrun
        rw [ite_eq_right ha] at hrun
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
          split at hrun
          · rename_i hk hhk
            obtain ⟨hlo, hhi'⟩ := nestHoleAt_some hhk
            by_cases hc : ((w.getAppArgs.all fun x =>
                  !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x) &&
                (w.getAppArgs.length + hk.key.ds.length == nestArity ctx hk.key.cname)) = true
            · rw [ite_eq_left hc] at hrun
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl, rfl⟩ := hrun
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true] at hc
              obtain ⟨hfree, har⟩ := hc
              refine ⟨hI, [], ?_, NodesIn.nil rfl⟩
              by_cases hlt : i < ctx.hiAt 0
              · -- a member hole: the root frame's entry
                rw [ite_eq_left hlt]
                obtain rfl := nestHoleAt_root hhk hlt
                obtain ⟨hPl, -, hAr⟩ := hroot
                dsimp only at har
                have ht : i - ctx.nP < ctx.names.length := by
                  simp only [NestCtx.hiAt] at hlt; omega
                rw [hAr _ ht, hPl] at har
                have hd := PosD.hole (kb := kb) hw hocc' hfn hlo hlt (by omega) hfree
                by_cases hkb : kb = 0
                · subst hkb; exact hd
                · have : (kb == 0) = false := by simpa using hkb
                  simp only [this, hkb, ite_false, Bool.false_eq_true] at hd ⊢
                  exact hd
              · -- a frame hole: its frame's entry
                rw [ite_eq_right hlt]
                have hge : ctx.hiAt 0 ≤ i := by omega
                exact .frameHole hw hocc' hfn hge hhi' (nestHoleAt_frame hhk hge) hfree har
            · rw [ite_eq_right hc] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · simp [throw, throwThe, MonadExceptOf.throw] at hrun
        · -- `contApp`
          rename_i n us hfn
          by_cases hnm : ctx.names.contains n = true
          · rw [ite_eq_left hnm] at hrun
            simp [throw, throwThe, MonadExceptOf.throw] at hrun
          rw [ite_eq_right hnm] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl, rfl⟩ := hrun
          obtain ⟨nPc, L, hq, hle, hidxfree, hnq, hdsok, nI, cty, hnI, hlen, hkey⟩ :=
            nestCont_inv hv
          have hdsok' : ∀ x ∈ w.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length := by
            simpa using hdsok
          have hdsw : ∀ x ∈ w.getAppArgs.take nPc, WScoped (ctx.hiAt prog.length) x := fun x hx =>
            WScoped.of_fvarsBelow (Expr.WScoped.getAppArgs hwsw x (List.mem_of_mem_take hx))
              (Expr.fvarB_le (hdsok' x hx).2)
          have hdl : (w.getAppArgs.take nPc).length = nPc := by rw [List.length_take]; omega
          obtain ⟨hI', hk, hcase⟩ := nestContKey_deriv hctx ih hsc (by simpa using hnm) hnq
            hdsw hdl ⟨L, hq⟩ hnI hkey hI
          refine ⟨hI', ?_⟩
          rw [hk]
          have hidx' : ∀ x ∈ w.getAppArgs.drop nPc,
              x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by simpa using hidxfree
          rcases hcase with ⟨nI', cty', grp, hnI', hhead, ts, hfr, hn⟩ |
            ⟨hfree, grp, ts, hfr, hmem, hn⟩
          · rw [hnI] at hnI'
            obtain ⟨rfl, rfl⟩ : nI = nI' ∧ cty = cty' := by simpa using hnI'
            exact ⟨_, .contNew hw hocc' hfn (by simpa using hnm) hq hlen hnq hidx' hdsok' hdsw
              hnI hhead hsc hfr, hn⟩
          · exact ⟨_, .contHit hw hocc' hfn (by simpa using hnm) hq hlen hnq hidx'
              (fun x hx => ⟨(hdsok' x hx).1, hfree x hx⟩)
              (fun x hx => WScoped.of_fvarsBelow (hdsw x hx) (Expr.fvarB_le (hfree x hx)))
              hnI hmem hfr, hn⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-! ## The root frame -/

/-- **The root frame, derived**: the cache invariant kept, constructors
recorded only on top, and per member its constructor list derived at the
root key (`.ctors []`), its nodes and constructors recorded, and every
constructor's output (`CtorOut`). -/
theorem nestRoot_deriv (hctx : NestCtxOk ctx) (hroot : NestRootOk ctx)
    (hwsc : ∀ dep e w, ops.whnf env dep e = .ok w → WScoped dep e → WScoped dep w)
    {holes : List Expr} (hh : nestHoles ctx = some holes)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestState)
      (outs : List (List (List NestFieldKind × Expr))) (st' : NestState),
      nestRoot ops env ctx holes css st = .ok (outs, st') →
      (∀ cs ∈ css, ∀ x ∈ cs, x.1.type.hasFvar = false) → DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧ (∃ l, st'.ctorNfs.toList = st.ctorNfs.toList ++ l) ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs → ∃ os ts,
        outs[c]? = some os ∧
        PosD ops env ctx (.ctors [] (ctx.hiAt 0) (ctx.lps.map .param) ctx.params
          ctx.names holes cs) ts ∧
        TreeRec ops env ctx st'.ctorNfs.toList ts ∧
        CtorsRec ops env ctx st'.ctorNfs.toList [] (ctx.hiAt 0) (ctx.lps.map .param) ctx.params
          ctx.names holes cs ∧
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ o, os[j]? = some o ∧
          CtorOut ops env ctx st'.ctorNfs.toList [] (ctx.hiAt 0) (ctx.lps.map .param) ctx.params
            ctx.names holes cA o
  | [], st, outs, st', h, _, hI => by
    simp only [nestRoot, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, ⟨[], by simp⟩, fun _ _ hc => by simp at hc⟩
  | cs₀ :: css, st, outs, st', h, hcl, hI => by
    simp only [nestRoot, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨o, st₁⟩ := r₁
    simp only at h
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨os₂, st₂⟩ := r₂
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    subst h₁ h₂
    have hparN : ∀ x ∈ ctx.params, WScoped ctx.nP x := by
      intro x hx
      obtain ⟨i, ty, rfl, hi⟩ := hroot.2.1 x hx
      have := hpar _ hx
      simp only [WScoped] at this ⊢
      exact ⟨hi, this.2⟩
    have hsub : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x := fun x hx =>
      (nestHoles_ok hctx hparN hh x hx).1
    have hlenH : ctx.names.length ≤ holes.length := by
      rw [nestHoles_length hh]; exact Nat.le_refl _
    obtain ⟨hI₁, ts₁, hd₁, hn₁, hcr₁, -, hout₁⟩ :=
      nestCtors_deriv (fun x => nestPos_deriv hctx hroot hwsc (whnfWalkFuel x)) (prog := []) rfl
        ProgScoped.nil hpar hsub hlenH
        cs₀ st o st₁ (hcl cs₀ List.mem_cons_self) hr₁ hI
    obtain ⟨hI₂, ⟨l₂, hl₂⟩, hall₂⟩ :=
      nestRoot_deriv hctx hroot hwsc hh hpar css st₁ os₂ st₂ hr₂
        (fun cs hcs => hcl cs (List.mem_cons_of_mem _ hcs)) hI₁
    have hsub₂ : ∀ e ∈ st₁.ctorNfs.toList, e ∈ st₂.ctorNfs.toList := fun e he => by
      rw [hl₂]; exact List.mem_append_left _ he
    obtain ⟨⟨l₁, hl₁⟩, htr₁⟩ := hn₁
    refine ⟨hI₂, ⟨l₁ ++ l₂, by rw [hl₂, hl₁, List.append_assoc]⟩, fun c cs hc => ?_⟩
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨o, ts₁, rfl, hd₁, htr₁.mono hsub₂, hcr₁.mono hsub₂,
        fun j cA hj => by
          obtain ⟨o', ho', hco⟩ := hout₁ j cA hj
          exact ⟨o', ho', hco.mono hsub₂⟩⟩
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact hall₂ c cs hc

/-! ## The seeds -/

/-- **A seed's facts** (`nestSeedOf` at a class stage (b) resolved): no
member and not `Quot`, a stored container at the seed's parameter count,
its parameters' leaves the canonical variables' (`SeedLeaves`) and well
scoped at the walk's depth. -/
@[expose] def SeedOk (ctx : NestCtx) (s : NestKey × Nat) : Prop :=
  ctx.names.contains s.1.cname = false ∧ s.1.cname ≠ quotName ∧
    (∃ L, nestContainer ctx s.1.cname = some (s.2, L)) ∧ s.1.ds.length = s.2 ∧
    (∀ x ∈ s.1.ds, SeedLeaves ctx x ∧ WScoped (ctx.hiAt 0) x) ∧
    ∀ x ∈ s.1.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt 0

/-- **The seeds, derived**: the cache invariant kept, every seed's frame
derived at the root (`PosD.seed`, its one node the seed's own key, whose
group holds it, recorded), and constructors recorded only on top. -/
theorem nestSeeds_deriv (hctx : NestCtxOk ctx) (hroot : NestRootOk ctx)
    (hwsc : ∀ dep e w, ops.whnf env dep e = .ok w → WScoped dep e → WScoped dep w) :
    ∀ (ks : List (NestKey × Nat)) (st st' : NestState), nestSeeds ops env ctx ks st = .ok st' →
      (∀ s ∈ ks, SeedOk ctx s) → DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧
        (∀ s ∈ ks, ∃ grp ts, PosD ops env ctx (.seed s.1) [.node [] [] s.1 grp ts] ∧
          s.1.cname ∈ grp.map (·.1) ∧
          TreeRec ops env ctx st'.ctorNfs.toList [.node [] [] s.1 grp ts]) ∧
        ∃ l, st'.ctorNfs.toList = st.ctorNfs.toList ++ l
  | [], st, st', h, _, hI => by
    simp only [nestSeeds, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, fun _ hs => by simp at hs, [], by simp⟩
  | (key, nPc) :: ks, st, st', h, hok, hI => by
    obtain ⟨n, us, ds⟩ := key
    simp only [nestSeeds, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i ni hni
    obtain ⟨nI, cty⟩ := ni
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨k₁, st₁⟩ := r
    obtain ⟨hnm, hquot, ⟨L, hC⟩, hlen, hds, hchk'⟩ := hok (⟨n, us, ds⟩, nPc) List.mem_cons_self
    obtain ⟨hI₁, -, hcase⟩ := nestContKey_deriv hctx (nestPos_deriv hctx hroot hwsc _) ProgScoped.nil
      hnm hquot (fun x hx => (hds x hx).2) hlen ⟨L, hC⟩ hni hr hI
    have hC' : nestContainer ctx n = some (ds.length, L) := by rw [hlen]; exact hC
    have hseed : ∃ grp ts, PosD ops env ctx (.seed ⟨n, us, ds⟩) [.node [] [] ⟨n, us, ds⟩ grp ts] ∧
        n ∈ grp.map (·.1) ∧ NodesIn ops env ctx st st₁ [.node [] [] ⟨n, us, ds⟩ grp ts] := by
      rcases hcase with ⟨nI, cty, grp, -, hhead, ts, hfr, hn⟩ | ⟨-, grp, ts, hfr, hmem, hn⟩
      · have hmem : n ∈ grp.map (·.1) := by
          cases grp with
          | nil => simp at hhead
          | cons p ps =>
            simp only [List.head?_cons, Option.some.injEq] at hhead
            subst hhead
            exact List.mem_cons_self
        exact ⟨grp, ts, .seed hnm hquot hC' hchk' (fun x hx => (hds x hx).2)
          (fun x hx => (hds x hx).1) hmem hfr, hmem, hn⟩
      · exact ⟨grp, ts, .seed hnm hquot hC' hchk' (fun x hx => (hds x hx).2)
          (fun x hx => (hds x hx).1) hmem hfr, hmem, hn⟩
    obtain ⟨grp, ts, hD, hmem, ⟨l₁, hl₁⟩, htr₁⟩ := hseed
    obtain ⟨hI₂, hall₂, ⟨l₂, hl₂⟩⟩ :=
      nestSeeds_deriv hctx hroot hwsc ks st₁ st' h (fun s hs => hok s (List.mem_cons_of_mem _ hs)) hI₁
    have hsub : ∀ e ∈ st₁.ctorNfs.toList, e ∈ st'.ctorNfs.toList := fun e he => by
      rw [hl₂]; exact List.mem_append_left _ he
    refine ⟨hI₂, fun s hs => ?_, ⟨l₁ ++ l₂, by rw [hl₂, hl₁, List.append_assoc]⟩⟩
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨grp, ts, hD, hmem, htr₁.mono hsub⟩
    · exact hall₂ s hs

/-- The canonical parameters opened off a former read as the root
frame's key (`NestRootOk`), at stored formers of the members' arity. -/
theorem nestRootOk_of_open {ctx : NestCtx} {T rest : Expr}
    (hop : openPisAtFvars ctx.nP T 0 = some (ctx.params, rest)) (hAr : NestArityOk ctx) :
    NestRootOk ctx := by
  refine ⟨ConLeche.Verify.openPisAtFvars_length _ hop, fun x hx => ?_, hAr⟩
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index _ _ _ hop i x hi
  have := (List.getElem?_eq_some_iff.mp hi).1
  rw [ConLeche.Verify.openPisAtFvars_length _ hop] at this
  exact ⟨0 + i, ty, rfl, by omega⟩

/-- **The root frame's constructors recorded**, member by member. -/
@[expose] def CtorsRecRoot (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (holes : List Expr) (tbl : List NestCtorNf) (css : List (List (ConstantVal × Nat))) : Prop :=
  ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs →
    CtorsRec ops env ctx tbl [] (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.names holes cs

theorem CtorsRecRoot.mono {holes : List Expr} {tbl tbl' : List NestCtorNf}
    (hs : ∀ e ∈ tbl, e ∈ tbl') {css : List (List (ConstantVal × Nat))}
    (h : CtorsRecRoot ops env ctx holes tbl css) : CtorsRecRoot ops env ctx holes tbl' css :=
  fun c cs hc => (h c cs hc).mono hs

/-- The canonical parameters are hole-free readers of themselves: read
back, they are unchanged. -/
theorem params_readback {ctx : NestCtx} (hroot : NestRootOk ctx) (prog : List NestHole) :
    ctx.params.map (·.replaceFVars (nestHoleImg ctx prog)) = ctx.params := by
  refine (List.map_congr_left fun x hx => ?_).trans (List.map_id _)
  obtain ⟨i, ty, rfl, hi⟩ := hroot.2.1 x hx
  simp only [Expr.replaceFVars, id]
  rw [nestHoleImg_lt_nP (prog := prog) hi]
  rfl

/-- **A member constructor's entry, recorded at the root key** (K.53′'s
root-frame entries): at a recorded root frame, a member constructor of
the block's own levels whose member-abstracted crest is derived
(`MemberCtorD`) has its normal form's entry — at the block's own levels
and parameters, read back — in the table. -/
theorem rootEntry_mem {holes : List Expr} {tbl : List NestCtorNf}
    {css : List (List (ConstantVal × Nat))} (hroot : NestRootOk ctx)
    (hrec : CtorsRecRoot ops env ctx holes tbl css) {c : Nat} {cs : List (ConstantVal × Nat)}
    (hc : css[c]? = some cs) {cA : ConstantVal × Nat} (hcA : cA ∈ cs)
    (hlps : cA.1.levelParams = ctx.lps) {crest : Expr}
    (hcr : nestCrest ctx.names (ctx.lps.map .param) ctx.params holes cA.1.type = some crest)
    {ks : List NestFieldKind} {tyN : Expr} {ts : List PosTree}
    (hd : MemberCtorD ops env ctx cA.2 crest ks tyN ts) :
    (⟨cA.1.name, ctx.lps.map .param, ctx.params, tyN.replaceFVars (nestHoleImg ctx [])⟩ :
      NestCtorNf) ∈ tbl := by
  obtain ⟨nds, cur, htele, rfl, -⟩ := hd
  have hcr' : nestCrest ctx.names (ctx.lps.map .param) ctx.params holes
      (cA.1.type.instantiateLevelParams cA.1.levelParams (ctx.lps.map .param)) = some crest := by
    rw [rootCrest_eq _ _ hlps]; exact hcr
  have h := hrec c cs hc cA hcA crest ks nds cur ts hcr' htele
  unfold nestCtorNf at h
  rwa [params_readback hroot []] at h

/-- **The install's positivity stage, derived**: the context
`checkBlockPositivity` builds, and — at a context whose stored constants
are closed, canonical parameters well scoped at the walk's depth, closed
constructors of the block's own levels and member formers of the
members' arity — every stored constructor's member-abstracted crest
derived (`MemberCtorD`, the root frame's constructor judgment with every
member applied in its normal form, from official's uniform check) with
the run's kinds and its output normal form, its
nodes recorded in the walk's final state `pos`, which keeps the cache
invariant (the seeds continue from it, `checkBlockSeeds_deriv`), and
every constructor's entry recorded (`CtorsRec` at the root key). -/
theorem checkBlockPositivity_deriv {env₁ : Env}
    {find? : Name → Option ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos : NestState}
    (hwsc : ∀ dep e w, ops.whnf env₁ dep e = .ok w → WScoped dep e → WScoped dep w)
    (h : checkBlockPositivity ops env₁ find? p cvTas ctorsAs = .ok (kinds, nfs, pos)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find?) = some holes ∧
      (NestCtxOk (p.nestCtx fvsP find?) →
        NestArityOk (p.nestCtx fvsP find?) →
        (∀ x ∈ fvsP, WScoped ((p.nestCtx fvsP find?).hiAt 0) x) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ cA ∈ cs, cA.1.levelParams = p.lps) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ks ts,
            nestCrest (p.nestCtx fvsP find?).names (p.lps.map .param) fvsP holes cA.1.type
              = some crest ∧
            MemberCtorD ops env₁ (p.nestCtx fvsP find?) cA.2 crest ks
              ((nfs.getD c []).getD j default) ts ∧
            (kinds.getD c []).getD j [] = ks ∧
            TreeRec ops env₁ (p.nestCtx fvsP find?) pos.ctorNfs.toList ts) ∧
        CtorsRecRoot ops env₁ (p.nestCtx fvsP find?) holes pos.ctorNfs.toList ctorsAs ∧
        DerivCache ops env₁ (p.nestCtx fvsP find?) pos) := by
  obtain ⟨cvTa0, fvsP, rest, holes, outs, h1, h2, h3, hU, hr, -, rfl, rfl⟩ :=
    checkBlockPositivity_inv h
  refine ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun hctx hAr hpar hcl hlps => ?_⟩
  have hroot := nestRootOk_of_open (ctx := p.nestCtx fvsP find?) h2 hAr
  obtain ⟨hIM, -, hall⟩ := nestRoot_deriv hctx hroot hwsc h3 hpar ctorsAs {} outs pos hr
    (fun cs hcs x hx => by
      obtain ⟨c, hc⟩ := List.getElem?_of_mem hcs
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      exact hcl c cs hc j x hj) derivCache_empty
  have hRR : CtorsRecRoot ops env₁ (p.nestCtx fvsP find?) holes pos.ctorNfs.toList
      ctorsAs := fun c cs hc => by
    obtain ⟨os, ts, -, -, -, hcr, -⟩ := hall c cs hc
    exact hcr
  refine ⟨fun c cs hc j cA hj => ?_, hRR, hIM⟩
  obtain ⟨os, ts, hoc, -, -, -, hout⟩ := hall c cs hc
  obtain ⟨o, hoj, crest, nds, cur, ts', hcr, -, hd, ho2, hu4, hres, hidx, htr⟩ := hout j cA hj
  rw [rootCrest_eq _ _ (hlps c cs hc cA (List.mem_of_getElem? hj))] at hcr
  refine ⟨crest, o.1, ts', hcr, ⟨nds, cur, hd, ?_, ?_, hres, hidx⟩, ?_, htr⟩
  · rw [outs_getD hoc hoj default]; exact ho2
  · rw [outs_getD hoc hoj default, ho2]; exact hu4
  · exact outs_getD hoc hoj []

end ConLeche
