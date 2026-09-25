module

public import ConLeche.Verify.Inductives.PosDeriv
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
any `ops` whose whnf keeps terms well scoped), leaving no restart
pending, yields the derivation `PosD` of its input.  This file is the
only place that reads the run: its cache, its restarts and its fuel stay
here.

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

/-- **A cached instantiation, derived**: its frame, under some well-scoped
frame stack, with the key's container in the frame's final group. -/
@[expose] def KeyD (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (key : NestKey) : Prop :=
  ∃ prog grp, ProgScoped ctx prog ∧ PosD ops env ctx (.frame prog key.lvls key.ds grp) ∧
    key.cname ∈ grp.map (·.1)

/-- **The run's state invariant**: the container lookups are the
environment's, and every cached instantiation whose parameters lie below
the frame holes is derived. -/
@[expose] def DerivCache (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (st : NestState) :
    Prop :=
  (∀ c r, st.ctorsOf.lookup c = some r → r = nestContainer ctx c) ∧
  ∀ ki ∈ st.keys.toList, (∀ x ∈ ki.key.ds, x.fvarB ≤ ctx.hiAt 0) → KeyD ops env ctx ki.key

theorem derivCache_empty : DerivCache ops env ctx {} :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

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

/-- A restart: the entry state's cache with the restarted walk's lookups. -/
theorem DerivCache.mix {st₀ st : NestState} (h₀ : DerivCache ops env ctx st₀)
    (h : DerivCache ops env ctx st) : DerivCache ops env ctx { st₀ with ctorsOf := st.ctorsOf } :=
  ⟨h.1, h₀.2⟩

/-- A restart request changes no cache. -/
theorem DerivCache.restart {st : NestState} (h : DerivCache ops env ctx st)
    (r : Option (Nat × List Name)) : DerivCache ops env ctx { st with restart := r } :=
  ⟨h.1, h.2⟩

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
    DerivCache ops env ctx st' ∧ (st'.restart = none → PosD ops env ctx (.field prog dep kb e k.erase nf))

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

/-- **The telescope walk, derived.** -/
theorem nestFields_deriv (hrec : RunDeriv ops env ctx rec) {prog : List NestHole} {base : Nat}
    {err : CheckError} (hhi : ctx.hiAt prog.length ≤ base) (hsc : ProgScoped ctx prog) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields rec prog base err nF j cur st = .ok (ks, nds, res, st') →
      WScoped (base + j) cur → DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧
        (st'.restart = none → PosD ops env ctx (.tele prog base nF j cur (ks.map (·.erase)) nds res)) := by
  intro nF
  induction nF with
  | zero =>
    intro j cur st ks nds res st' h _ hI
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hI, fun _ => .teleNil⟩
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
      obtain ⟨hI₁, hA⟩ := hrec prog (base + j) 0 a st k₁ nd₁ st₁ hr₁ (by omega) hws.1 hsc hI
      by_cases hrs : st₁.restart.isSome = true
      · rw [if_pos hrs] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl⟩ := h
        refine ⟨hI₁, fun hc => ?_⟩
        rw [hc] at hrs; exact nomatch hrs
      rw [if_neg hrs] at h
      have hc₁ : st₁.restart = none := by simpa using hrs
      split at h
      · simp at h
      rename_i r₂ hr₂
      obtain ⟨ks₂, nds₂, res₂, st₂⟩ := r₂
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hws' : WScoped (base + (j + 1)) (b.instantiate1 (.fvar (base + j) a)) := by
        rw [show base + (j + 1) = base + j + 1 by omega]
        exact WScoped.instantiate1 hws.1 0 hws.2
      obtain ⟨hI₂, hrest⟩ := ih (j + 1) _ st₁ ks₂ nds₂ res₂ st₂ hr₂ hws' hI₁
      exact ⟨hI₂, fun hc => .teleCons (hA hc₁) (hrest hc)⟩
    · simp at h

end Tele

/-! ## Small facts -/

/-- The arguments of a well-scoped spine are well scoped. -/
theorem wScoped_getAppArgs {d : Nat} : ∀ {e : Expr}, WScoped d e → ∀ x ∈ e.getAppArgs, WScoped d x
  | .app f a, h, x, hx => by
    simp only [WScoped] at h
    simp only [getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact wScoped_getAppArgs h.1 x hx
    · exact h.2
  | .bvar _, _, x, hx | .fvar .., _, x, hx | .sort _, _, x, hx | .const .., _, x, hx
  | .lit _, _, x, hx | .lam .., _, x, hx | .forallE .., _, x, hx | .letE .., _, x, hx
  | .proj .., _, x, hx => by simp [getAppArgs] at hx

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
theorem nestCtors_deriv (hrec : RunDeriv ops env ctx rec) {prog : List NestHole} {hi : Nat}
    {us : List Level} {ds : List Expr} {sub : Name → List Level → Option Expr}
    (hhi : ctx.hiAt prog.length = hi) (hsc : ProgScoped ctx prog)
    (hds : ∀ x ∈ ds, WScoped hi x) (hsub : ∀ c us' r, sub c us' = some r → WScoped hi r) :
    ∀ (cs : List (ConstantVal × Nat)) (st st' : NestState), (∀ x ∈ cs, x.1.type.hasFvar = false) →
      nestCtors ctx ops env rec prog hi us ds ds.length sub cs st = .ok st' →
      DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧ (st'.restart = none → PosD ops env ctx (.ctors prog hi us ds sub cs)) := by
  intro cs
  induction cs with
  | nil =>
    intro st st' _ h hI
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, fun _ => .ctorsNil⟩
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
    obtain ⟨hI₁, htele⟩ := nestFields_deriv hrec (by omega) hsc nF 0 crest st ks nds cur st₁ hr hws hI
    dsimp only at h
    by_cases hrs : st₁.restart.isSome = true
    · rw [if_pos hrs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨hI₁, fun hc => ?_⟩
      rw [hc] at hrs; exact nomatch hrs
    rw [if_neg hrs] at h
    have hc₁ : st₁.restart = none := by simpa using hrs
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hu4
    split at h
    · rename_i hok
      obtain ⟨hI', hrest⟩ := ih st₁ st' (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) h hI₁
      refine ⟨hI', fun hc => ?_⟩
      simp only [Bool.and_eq_true] at hok
      refine .ctorsCons hnd hcrest' hty hsv (htele hc₁) ?_ hok.1 hok.2 (hrest hc)
      simp only [erase_getD_bne]
      simpa using hu4
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **A frame's constructor listing, without its cache.** -/
theorem nestGroupCtors_deriv {nPc : Nat} :
    ∀ (cs : List Name) (st : NestState) (ctors : List (ConstantVal × Nat)) (st' : NestState),
      nestGroupCtors (m := CheckM) ctx nPc cs st = .ok (ctors, st') → DerivCache ops env ctx st →
      DerivCache ops env ctx st' ∧ groupCtors ctx nPc cs = some ctors
  | [], st, ctors, st', h, hst => by
    simp only [nestGroupCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hst, rfl⟩
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
      obtain ⟨hI₁, hg⟩ := nestGroupCtors_deriv cs _ rest st₁ hr (hst.insert c)
      refine ⟨hI₁, ?_⟩
      simp only [groupCtors, hq']
      rw [if_pos (by simpa using hok), hg]
      rfl
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The frame's group, as the derivation's `frame` rule asks. -/
@[expose] def GrpD (ctx : NestCtx) (hi : Nat) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  grp ≠ [] ∧ (grp.map (·.1)).Nodup ∧
  (∀ p ∈ grp, ∃ nI, nestInstType (m := CheckM) ctx hi ⟨p.1, us, ds⟩ = .ok (nI, p.2)) ∧
  ∀ p ∈ grp.tail, (nestBlockOf ctx (grp.headD default).1).contains p.1 = true

/-- **A container frame, restarts included, derived**: the state
invariant is kept, and when no restart is pending the final group
extends the entry group and its frame is derived. -/
theorem nestFrame_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr}
    (hhi : ctx.hiAt prog.length = hi) (hsc : ProgScoped ctx prog)
    (hds : ∀ x ∈ ds, WScoped hi x) :
    ∀ (r : Nat) (grp : List (Name × Expr)) (st₀ : NestState) (grp' : List (Name × Expr))
      (st' : NestState), GrpD ctx hi us ds grp →
      (ctx.names.contains (grp.headD default).1 = false ∧ (grp.headD default).1 ≠ quotName) →
      nestFrame ctx ops env rec prog hi us ds ds.length r grp st₀ = .ok (grp', st') →
      DerivCache ops env ctx st₀ →
      DerivCache ops env ctx st' ∧ (st'.restart = none →
        (∃ ext, grp' = grp ++ ext) ∧ PosD ops env ctx (.frame prog us ds grp')) := by
  intro r
  induction r with
  | zero =>
    intro grp st₀ grp' st' _ _ h _
    simp [nestFrame, throw, throwThe, MonadExceptOf.throw] at h
  | succ r ih =>
    intro grp st₀ grp' st' hg hhd h hI₀
    simp only [nestFrame, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i v hgc
    obtain ⟨ctors, st₁⟩ := v
    obtain ⟨hI₁, hgc'⟩ := nestGroupCtors_deriv _ st₀ ctors st₁ hgc hI₀
    split at h
    · simp at h
    rename_i st₂ hwc
    have hwc' : nestCtors ctx ops env rec
        ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length) us ds ds.length
        (grpSub us hi grp) ctors st₁ = .ok st₂ := by
      rw [← grpNews_mapIdx]; exact hwc
    obtain ⟨hne, hnd, hinst, hblk⟩ := hg
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
    obtain ⟨hI₂, hwalk⟩ := nestCtors_deriv hrec hhi' hsc'
      (fun x hx => WScoped.mono (by omega) (hds x hx)) hsub ctors st₁ st₂ hcl hwc' hI₁
    split at h
    · -- a restart request
      rename_i b adds hrs
      split at h
      · -- at this frame: restart with the grown group
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        rename_i hnew
        split at h
        · rename_i hblk'
          split at h
          · simp at h
          rename_i grp'' hgrow
          obtain ⟨ext, rfl, hmap, hext⟩ := nestGrowGroup_inv' _ _ _ hgrow
          have hg' : GrpD ctx hi us ds (grp ++ ext) := by
            refine ⟨by simp [hne], ?_, fun p hp => ?_, fun p hp => ?_⟩
            · rw [List.map_append, hmap, List.nodup_append]
              refine ⟨hnd, (posD_nodup_eraseDups _).filter _, fun a ha b hb hab => ?_⟩
              subst hab
              rw [List.mem_filter] at hb
              have hc : (grp.map (·.1)).contains a = true := List.contains_iff_mem.mpr ha
              rw [hc] at hb
              exact absurd hb.2 (by decide)
            · rcases List.mem_append.mp hp with hp | hp
              · exact hinst p hp
              · exact hext p hp
            · obtain ⟨p₀, ps₀, hp₀⟩ := List.exists_cons_of_ne_nil hne
              subst hp₀
              simp only [List.cons_append, List.tail_cons, List.headD_cons] at hp ⊢
              rcases List.mem_append.mp hp with hp | hp
              · exact hblk p (by simpa using hp)
              · have hpn : p.1 ∈ List.filter (fun c => !((p₀ :: ps₀).map (·.1)).contains c)
                    adds.eraseDups := by
                  rw [← hmap]; exact List.mem_map_of_mem hp
                have := List.all_eq_true.mp hblk' _ hpn
                simpa using this
          have hhd' : ctx.names.contains ((grp ++ ext).headD default).1 = false ∧
              ((grp ++ ext).headD default).1 ≠ quotName := by
            obtain ⟨p₀, ps₀, hp₀⟩ := List.exists_cons_of_ne_nil hne
            subst hp₀; simpa using hhd
          obtain ⟨hI', hres⟩ := ih (grp ++ ext) _ grp' st' hg' hhd' h (hI₀.mix hI₂)
          refine ⟨hI', fun hc => ?_⟩
          obtain ⟨⟨ext', rfl⟩, hfr⟩ := hres hc
          exact ⟨⟨ext ++ ext', by simp⟩, hfr⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · -- another frame's restart: unwind
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hI₂, fun hc => ?_⟩
        rw [hc] at hrs; exact nomatch hrs
    · -- no restart: the frame's own result
      rename_i hrs
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hI₂, fun hc => ⟨⟨[], by simp⟩, ?_⟩⟩
      subst hhi
      exact .frame hne hhd hnd hinst hblk hgc' (hwalk hc)

/-- **Accepting the reached group-mates keeps the invariant.** -/
theorem nestAcceptGroup_deriv {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st st' : NestState),
      nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' →
      DerivCache ops env ctx st →
      (∀ p ∈ grp, KeyD ops env ctx ⟨p.1, us, ds⟩) →
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
      · exact hk (c, ty) List.mem_cons_self
    · exact nestAcceptGroup_deriv rest st st' h hI (fun p hp => hk p (List.mem_cons_of_mem _ hp))

/-- **A new (or re-walked) instantiation, derived**: its frame, under the
current frames, the container at the frame's head. -/
theorem nestContNew_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    {prog : List NestHole} (hsc : ProgScoped ctx prog) {kb : Nat} {n : Name} {us : List Level}
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) {nPc : Nat}
    (hnPc : ds.length = nPc) {old : Option Nat}
    {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContNew ctx ops env rec prog kb n us ds nPc old st = .ok (k, st'))
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ (st'.restart = none →
      k.erase = .nested (kb != 0) ∧ ∃ nI cty grp,
        nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty) ∧
        grp.head? = some (n, cty) ∧ PosD ops env ctx (.frame prog us ds grp)) := by
  subst hnPc
  simp only [nestContNew, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i ni hni
  obtain ⟨nI, cty⟩ := ni
  split at h
  · simp at h
  rename_i gs hfr
  obtain ⟨grp', st₁⟩ := gs
  have hg : GrpD ctx (ctx.hiAt prog.length) us ds [(n, cty)] :=
    ⟨by simp, by simp, fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨nI, hni⟩, fun p hp => by simp at hp⟩
  obtain ⟨hI₁, hres⟩ := nestFrame_deriv hctx hrec rfl hsc hds _ [(n, cty)] st grp' st₁ hg
    ⟨hnm, hquot⟩ hfr hI
  by_cases hrs : st₁.restart.isSome = true
  · rw [if_pos hrs] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hI₁, fun hc => by rw [hc] at hrs; exact nomatch hrs⟩
  rw [if_neg hrs] at h
  have hc₁ : st₁.restart = none := by simpa using hrs
  obtain ⟨⟨ext, rfl⟩, hframe⟩ := hres hc₁
  have hkey : ∀ p ∈ (n, cty) :: ext, KeyD ops env ctx ⟨p.1, us, ds⟩ :=
    fun p hp => ⟨prog, _, hsc, hframe, List.mem_map_of_mem hp⟩
  split at h
  · simp at h
  rename_i st₂ hacc
  have hI₂ : DerivCache ops env ctx st₂ :=
    nestAcceptGroup_deriv _ _ _ hacc hI₁ fun p hp => hkey p (List.mem_of_mem_drop hp)
  have hout : k.erase = .nested (kb != 0) ∧ ∃ nI cty grp,
      nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty) ∧
      grp.head? = some (n, cty) ∧ PosD ops env ctx (.frame prog us ds grp) := by
    refine ⟨?_, nI, cty, _, hni, rfl, hframe⟩
    split at h <;>
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]; rfl
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hI₂, fun _ => hout⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨⟨hI₂.1, fun ki hki hfv => ?_⟩, fun _ => hout⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
    rcases hki with hki | rfl
    · exact hI₂.2 ki hki hfv
    · exact hkey _ List.mem_cons_self

/-- **The instantiation met, derived**: a cycle leaves a restart pending;
otherwise the frame is derived here, or the key is a hit below every
frame hole with a derived frame elsewhere. -/
theorem nestContKey_deriv (hctx : NestCtxOk ctx) (hrec : RunDeriv ops env ctx rec)
    {prog : List NestHole} (hsc : ProgScoped ctx prog) {kb : Nat} {n : Name} {us : List Level}
    (hnm : ctx.names.contains n = false) (hquot : n ≠ quotName)
    {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt prog.length) x) {nPc : Nat}
    (hnPc : ds.length = nPc) {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestContKey ctx ops env rec prog kb n us ds nPc st = .ok (k, st'))
    (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ (st'.restart = none →
      k.erase = .nested (kb != 0) ∧
      ((∃ nI cty grp,
        nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty) ∧
        grp.head? = some (n, cty) ∧ PosD ops env ctx (.frame prog us ds grp)) ∨
       ((∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) ∧ KeyD ops env ctx ⟨n, us, ds⟩))) := by
  subst hnPc
  unfold nestContKey at h
  split at h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨hI.restart _, fun hc => by simp at hc⟩
  · split at h
    · rename_i q hfq
      split at h
      · -- a hit
        rename_i hfree
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hI, fun _ => ⟨rfl, Or.inr ⟨by simpa using hfree, ?_⟩⟩⟩
        obtain ⟨hqs, hqk, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfq
        have hkeq : st.keys[q].key = ⟨n, us, ds⟩ := by simpa using hqk
        have hfree' : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0 := by simpa using hfree
        have := hI.2 _ (Array.getElem_mem_toList hqs) (by rw [hkeq]; exact hfree')
        rwa [hkeq] at this
      · obtain ⟨hI', hr⟩ := nestContNew_deriv hctx hrec hsc hnm hquot hds rfl h hI
        exact ⟨hI', fun hc => ⟨(hr hc).1, Or.inl (hr hc).2⟩⟩
    · obtain ⟨hI', hr⟩ := nestContNew_deriv hctx hrec hsc hnm hquot hds rfl h hI
      exact ⟨hI', fun hc => ⟨(hr hc).1, Or.inl (hr hc).2⟩⟩

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
    ∀ fuel, RunDeriv ops env ctx (nestPos ops env ctx fuel)
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
        exact ⟨hI, fun _ => .const hw hocc⟩
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
        obtain ⟨hI', hB⟩ := ih prog (dep + 1) (kb + 1) _ st k₁ nb _ hv (by omega)
          (WScoped.instantiate1 hwsw.1 0 hwsw.2) hsc hI
        exact ⟨hI', fun hc => .pi hw hocc' (by simpa using ha) (hB hc)⟩
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
              refine ⟨hI, fun _ => ?_⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true] at hc
              have hd := PosD.hole (kb := kb) hw hocc' hfn hmem.1 hmem.2 hc.1.1 hc.1.2 hc.2
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
                      exact ⟨hI, fun _ => .frameHole hw hocc' hfn hfr'.1 hfr'.2 hk hpar.1 hpar.2 hidx
                        (by simpa using har)⟩
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
          obtain ⟨hI', hres⟩ := nestContKey_deriv hctx ih hsc (by simpa using hnm) hnq hdsw hdl hkey
            (hI.insert n)
          refine ⟨hI', fun hc => ?_⟩
          obtain ⟨hk, hcase⟩ := hres hc
          rw [hk]
          have hidx' : ∀ x ∈ w.getAppArgs.drop nPc,
              x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by simpa using hidxfree
          rcases hcase with ⟨nI', cty', grp, hnI', hhead, hfr⟩ | ⟨hfree, prog', grp, hsc', hfr, hmem⟩
          · rw [hnI] at hnI'
            obtain ⟨rfl, rfl⟩ : nI = nI' ∧ cty = cty' := by simpa using hnI'
            exact .contNew hw hocc' hfn (by simpa using hnm) hq hlen hnq hidx' hdsok' hnI hhead hfr
          · exact .contHit hw hocc' hfn (by simpa using hnm) hq hlen hnq hidx'
              (fun x hx => ⟨(hdsok' x hx).1, hfree x hx⟩) hnI hsc' hmem hfr
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-- **A member constructor's run, derived**: the cache invariant kept,
and the constructor derived (`MemberCtorD`). -/
theorem nestMemberCtor_deriv (hctx : NestCtxOk ctx)
    (hwsc : ∀ dep e w, ops.whnf env dep e = .ok w → WScoped dep e → WScoped dep w)
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : nestMemberCtor ops env ctx nF crest st = .ok (ks, tyN, st'))
    (hws : WScoped (ctx.hiAt 0) crest) (hI : DerivCache ops env ctx st) :
    DerivCache ops env ctx st' ∧ MemberCtorD ops env ctx nF crest (ks.map (·.erase)) tyN := by
  unfold nestMemberCtor at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨ks₁, nds₁, res, st₁⟩ := r
  simp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hnr
  have hc : st₁.restart = none := by simpa using hnr
  obtain ⟨hI₁, htele⟩ := nestFields_deriv (nestPos_deriv hctx hwsc (whnfWalkFuel crest))
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
      refine ⟨hI₁, nds₁, res, htele hc, rfl, ?_, hok.1, hok.2, hha⟩
      refine Bool.eq_false_iff.mpr fun hany => hu4 ?_
      rw [List.any_eq_true] at hany ⊢
      obtain ⟨i, hi, hx⟩ := hany
      refine ⟨i, hi, ?_⟩
      revert hx
      rw [erase_getD]
      cases ks₁.getD i .ordinary <;> simp [PosKind.guarded, NestFieldKind.erase]
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The install's positivity stage, derived** (at either position of the
route switch): the context `checkBlockPositivity` builds, and — at a
context whose stored constants are closed, canonical parameters well
scoped at the walk's depth and closed constructors — every stored
constructor's member-abstracted crest derived (`MemberCtorD`) with the
run's kinds and its output normal form. -/
theorem checkBlockPositivity_deriv {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nst : Bool}
    (hwsc : ∀ dep e w, ops.whnf env₁ dep e = .ok w → WScoped dep e → WScoped dep w)
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs nst = .ok (kinds, nfs)) :
    ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP find? consts) = some holes ∧
      (NestCtxOk (p.nestCtx fvsP find? consts) →
        (∀ x ∈ fvsP, WScoped ((p.nestCtx fvsP find? consts).hiAt 0) x) →
        (∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) →
        ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
          ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ks,
            instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type)
              = some crest ∧
            MemberCtorD ops env₁ (p.nestCtx fvsP find? consts) cA.2 crest (ks.map (·.erase))
              ((nfs.getD c []).getD j default) ∧
            (kinds.getD c []).getD j [] = ks ∧ (nst = false → ∀ k ∈ ks, k.flat = true)) := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hthr⟩ := checkBlockPositivity_inv_I h
  refine ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun hctx hpar hcl => ?_⟩
  have hws : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∀ crest,
      instPisWith fvsP (nestAbstract (p.nestCtx fvsP find? consts) holes cA.1.type) = some crest →
      WScoped ((p.nestCtx fvsP find? consts).hiAt 0) crest :=
    fun c cs hc j cA hj crest hcr =>
      memberCrest_wscoped (nestHoles_ok hctx h3) hpar (hcl c cs hc j cA hj) hcr
  have := hthr (DerivCache ops env₁ (p.nestCtx fvsP find? consts)) derivCache_empty
    (fun c cs hc j cA hj crest hcr st₀ ks tyN st₁ _ hI hm =>
      (nestMemberCtor_deriv hctx hwsc hm (hws c cs hc j cA hj crest hcr) hI).1)
  intro c cs hc j cA hj
  obtain ⟨crest, st₀, ks, tyN, st₁, hcr, hI₀, hm, rfl, hks, hfl⟩ := this c cs hc j cA hj
  exact ⟨crest, ks, hcr, (nestMemberCtor_deriv hctx hwsc hm (hws c cs hc j cA hj crest hcr) hI₀).2,
    hks, hfl⟩

end ConLeche
