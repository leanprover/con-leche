module

public import ConLeche.Verify.Inductives.PosComplete
import ConLeche.Verify.Inductives.PosCompleteFrame
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstList
import ConLeche.Verify.Shift

public section

/-!
# Uniformity: a frame's constructor has the walk's shape (lane COMPLETE-4, (A))

The frame-constructor relation (`srel_rb`) reads a frame's constructor —
the container's constructor with the container's group abstracted to the
frame's holes, instantiated at the key's parameters — in the walk's shape
(`WShape`): every frame hole applied to its key's parameters.  That holds
because the container's own-block occurrences are UNIFORM: official's
`check_uniform_ind_occs` (`Official.uniformOcc`), which the container
passed when official added it.  `wshape_frameCtor` derives the shape from
that check, the key's parameters' own shape, and the container's
constructor type mentioning no member and no auxiliary name.
-/

namespace ConLeche

open Expr

section Unif

variable {ctx : NestCtx} {isAux : Name → Bool}

/-! ## The walk's shape is closed under application -/

theorem WShape.app' {P : List NestHole} {f a : Expr} (hf : WShape ctx isAux P f)
    (ha : WShape ctx isAux P a) : WShape ctx isAux P (.app f a) := by
  cases hf with
  | frm hk his =>
    rw [← Expr.mkAppN_append_one]
    refine .frm hk (fun x hx => ?_)
    rcases List.mem_append.mp hx with hx | hx
    · exact his x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ha
  | app hnf hf₁ ha₁ =>
    exact .app (fun i ty h => hnf i ty (by simpa [Expr.getAppFn] using h)) (.app hnf hf₁ ha₁) ha
  | const hn hax => exact .app (fun i ty h => by simp [Expr.getAppFn] at h) (.const hn hax) ha
  | par hi hg hty =>
    refine .app (fun i ty h => ?_) (.par hi hg hty) ha
    simp only [Expr.getAppFn, Expr.fvar.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [NestCtx.hiAt]; omega
  | mem ht =>
    refine .app (fun i ty h => ?_) (.mem ht) ha
    simp only [Expr.getAppFn, Expr.fvar.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [NestCtx.hiAt]; omega
  | lam h₁ h₂ => exact .app (fun i ty h => by simp [Expr.getAppFn] at h) (.lam h₁ h₂) ha
  | forallE h₁ h₂ => exact .app (fun i ty h => by simp [Expr.getAppFn] at h) (.forallE h₁ h₂) ha
  | letE h₁ h₂ h₃ => exact .app (fun i ty h => by simp [Expr.getAppFn] at h) (.letE h₁ h₂ h₃) ha
  | proj h₁ => exact .app (fun i ty h => by simp [Expr.getAppFn] at h) (.proj h₁) ha
  | bvar j => exact .app (fun i ty h => by simp [Expr.getAppFn] at h) (.bvar j) ha
  | sort u => exact .app (fun i ty h => by simp [Expr.getAppFn] at h) (.sort u) ha
  | lit l => exact .app (fun i ty h => by simp [Expr.getAppFn] at h) (.lit l) ha

theorem WShape.mkAppN' {P : List NestHole} : ∀ (ys : List Expr) {x : Expr},
    WShape ctx isAux P x → (∀ y ∈ ys, WShape ctx isAux P y) → WShape ctx isAux P (Expr.mkAppN x ys)
  | [], _, hx, _ => hx
  | y :: ys, _, hx, hys =>
    WShape.mkAppN' ys (hx.app' (hys y List.mem_cons_self))
      (fun z hz => hys z (List.mem_cons_of_mem _ hz))

/-- **The walk's shape under another stack** agreeing on the frames a
well-scoped term can name. -/
theorem WShape.restack {P P' Q : List NestHole}
    (hP : ∀ i, i < Q.length → P.reverse[i]? = Q.reverse[i]?)
    (hP' : ∀ i, i < Q.length → P'.reverse[i]? = Q.reverse[i]?) :
    ∀ {x : Expr}, WShape ctx isAux P x → Expr.WScoped (ctx.hiAt Q.length) x →
      WShape ctx isAux P' x := by
  intro x hx
  induction hx with
  | const hn ha => intro _; exact .const hn ha
  | par hi hg hty => intro _; exact .par hi hg hty
  | mem ht => intro _; exact .mem ht
  | @frm i ty h is hk _ ih =>
    intro hsc
    obtain ⟨hsc1, hsc2⟩ := wscoped_mkAppN hsc
    obtain ⟨hsc3, -⟩ := wscoped_mkAppN hsc1
    simp only [Expr.WScoped] at hsc3
    have hi : i < Q.length := by simp only [NestCtx.hiAt] at hsc3; omega
    exact .frm (by rw [hP' i hi, ← hP i hi]; exact hk) (fun y hy => ih y hy (hsc2 y hy))
  | app hnf _ _ ihf iha =>
    intro hsc; simp only [Expr.WScoped] at hsc; exact .app hnf (ihf hsc.1) (iha hsc.2)
  | lam _ _ iht ihb =>
    intro hsc; simp only [Expr.WScoped] at hsc; exact .lam (iht hsc.1) (ihb hsc.2)
  | forallE _ _ iht ihb =>
    intro hsc; simp only [Expr.WScoped] at hsc; exact .forallE (iht hsc.1) (ihb hsc.2)
  | letE _ _ _ iht ihv ihb =>
    intro hsc; simp only [Expr.WScoped] at hsc
    exact .letE (iht hsc.1) (ihv hsc.2.1) (ihb hsc.2.2)
  | proj _ ih => intro hsc; simp only [Expr.WScoped] at hsc; exact .proj (ih hsc)
  | bvar j => intro _; exact .bvar j
  | sort u => intro _; exact .sort u
  | lit l => intro _; exact .lit l

/-! ## Telescopes -/

theorem stripPis_of_le_piArity : ∀ (n : Nat) (t : Expr), n ≤ t.piArity →
    ∃ bs r, t.stripPis n = some (bs, r)
  | 0, t, _ => ⟨[], t, rfl⟩
  | n + 1, .forallE a b m, h => by
    simp only [Expr.piArity] at h
    obtain ⟨bs, r, hr⟩ := stripPis_of_le_piArity n b (by omega)
    exact ⟨(a, m) :: bs, r, by simp [Expr.stripPis, hr]⟩
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h | _ + 1, .const _ _, h
  | _ + 1, .app _ _, h | _ + 1, .lam _ _ _, h | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h
  | _ + 1, .proj _ _ _, h => by simp [Expr.piArity] at h

theorem stripPis_forallE_inv {n : Nat} {t : Expr} {bs : List (Expr × BinderMeta)} {r : Expr}
    (h : t.stripPis (n + 1) = some (bs, r)) :
    ∃ a b m bs', t = .forallE a b m ∧ b.stripPis n = some (bs', r) := by
  cases t with
  | forallE a b m =>
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', r'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    exact ⟨a, b, m, bs', rfl, by rw [h1, h2.2]⟩
  | _ => simp [Expr.stripPis] at h

theorem stripPis_instantiate1 {v : Expr} : ∀ (n : Nat) (t : Expr) (k : Nat)
    {bs : List (Expr × BinderMeta)} {r : Expr}, t.stripPis n = some (bs, r) →
    ∃ bs', (t.instantiate1 v k).stripPis n = some (bs', r.instantiate1 v (k + n))
  | 0, t, k, bs, r, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis]⟩
  | n + 1, t, k, bs, r, h => by
    obtain ⟨a, b, m, bs', rfl, hb⟩ := stripPis_forallE_inv h
    obtain ⟨bs'', hb'⟩ := stripPis_instantiate1 (v := v) n b (k + 1) hb
    rw [show k + 1 + n = k + (n + 1) by omega] at hb'
    refine ⟨(a.instantiate1 v k, m) :: bs'', ?_⟩
    simp only [Expr.instantiate1, Expr.stripPis, hb', Option.map_some]

theorem stripPis_instLP {ks : List Name} {us : List Level} : ∀ (n : Nat) (t : Expr)
    {bs : List (Expr × BinderMeta)} {r : Expr}, t.stripPis n = some (bs, r) →
    ∃ bs', (t.instantiateLevelParams ks us).stripPis n = some (bs', r.instantiateLevelParams ks us)
  | 0, t, bs, r, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis]⟩
  | n + 1, t, bs, r, h => by
    obtain ⟨a, b, m, bs', rfl, hb⟩ := stripPis_forallE_inv h
    obtain ⟨bs'', hb'⟩ := stripPis_instLP (ks := ks) (us := us) n b hb
    exact ⟨(a.instantiateLevelParams ks us, ⟨Level.substPW ks us m.pw⟩) :: bs'', by
      simp only [Expr.instantiateLevelParams, Expr.stripPis, hb', Option.map_some]⟩

theorem stripPis_replaceConsts {f : Name → List Level → Option Expr} : ∀ (n : Nat) (t : Expr)
    {bs : List (Expr × BinderMeta)} {r : Expr}, t.stripPis n = some (bs, r) →
    ∃ bs', (t.replaceConsts f).stripPis n = some (bs', r.replaceConsts f)
  | 0, t, bs, r, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis]⟩
  | n + 1, t, bs, r, h => by
    obtain ⟨a, b, m, bs', rfl, hb⟩ := stripPis_forallE_inv h
    obtain ⟨bs'', hb'⟩ := stripPis_replaceConsts (f := f) n b hb
    exact ⟨(a.replaceConsts f, m) :: bs'', by
      simp only [Expr.replaceConsts, Expr.stripPis, hb', Option.map_some]⟩

/-- **A telescope instantiation is one bulk instantiation of the body.** -/
theorem instPisWith_of_stripPis : ∀ (ds : List Expr) (t : Expr)
    {bs : List (Expr × BinderMeta)} {r : Expr}, t.stripPis ds.length = some (bs, r) →
    instPisWith ds t = some (r.instantiateList ds.reverse 0)
  | [], t, bs, r, h => by
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [instPisWith, Expr.instantiateList_nil]
  | d :: ds, t, bs, r, h => by
    obtain ⟨a, b, m, bs', rfl, hb⟩ := stripPis_forallE_inv (n := ds.length) h
    obtain ⟨bs'', hb'⟩ := stripPis_instantiate1 (v := d) ds.length b 0 hb
    rw [Nat.zero_add] at hb'
    simp only [instPisWith]
    rw [instPisWith_of_stripPis ds _ hb', List.reverse_cons,
      Expr.instantiateList_append_one ds.reverse r d 0, List.length_reverse, Nat.zero_add]

theorem hasFvar_stripPis : ∀ (n : Nat) (t : Expr) {bs : List (Expr × BinderMeta)} {r : Expr},
    t.stripPis n = some (bs, r) → t.hasFvar = false → r.hasFvar = false
  | 0, t, bs, r, h, ht => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact ht
  | n + 1, t, bs, r, h, ht => by
    obtain ⟨a, b, m, bs', rfl, hb⟩ := stripPis_forallE_inv h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at ht
    exact hasFvar_stripPis n b hb ht.2

theorem deepOcc_stripPis {p : Name → Bool} : ∀ (n : Nat) (t : Expr)
    {bs : List (Expr × BinderMeta)} {r : Expr},
    t.stripPis n = some (bs, r) → t.deepOcc p = false → r.deepOcc p = false
  | 0, t, bs, r, h, ht => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact ht
  | n + 1, t, bs, r, h, ht => by
    obtain ⟨a, b, m, bs', rfl, hb⟩ := stripPis_forallE_inv h
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at ht
    exact deepOcc_stripPis n b hb ht.2

theorem uniformOcc_stripPis {names : List Name} {lvls : List Level} {np : Nat} :
    ∀ (n : Nat) (t : Expr) (off : Nat) {bs : List (Expr × BinderMeta)} {r : Expr},
      t.stripPis n = some (bs, r) → Official.uniformOcc names lvls np off t = true →
      Official.uniformOcc names lvls np (off + n) r = true
  | 0, t, off, bs, r, h, ht => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact ht
  | n + 1, t, off, bs, r, h, ht => by
    obtain ⟨a, b, m, bs', rfl, hb⟩ := stripPis_forallE_inv h
    simp only [Official.uniformOcc, Bool.and_eq_true] at ht
    have := uniformOcc_stripPis n b (off + 1) hb ht.2
    rwa [show off + 1 + n = off + (n + 1) by omega] at this

/-! ## The spine through the three maps -/

theorem instLP_mkAppN {ks : List Name} {us : List Level} : ∀ (args : List Expr) (f : Expr),
    (Expr.mkAppN f args).instantiateLevelParams ks us =
      Expr.mkAppN (f.instantiateLevelParams ks us) (args.map (·.instantiateLevelParams ks us))
  | [], _ => rfl
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl, instLP_mkAppN as]
    rfl

theorem replaceConsts_mkAppN {g : Name → List Level → Option Expr} : ∀ (args : List Expr) (f : Expr),
    (Expr.mkAppN f args).replaceConsts g =
      Expr.mkAppN (f.replaceConsts g) (args.map (·.replaceConsts g))
  | [], _ => rfl
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl, replaceConsts_mkAppN as]
    rfl

theorem instantiateList_mkAppN {vs : List Expr} {k : Nat} : ∀ (args : List Expr) (f : Expr),
    (Expr.mkAppN f args).instantiateList vs k =
      Expr.mkAppN (f.instantiateList vs k) (args.map (·.instantiateList vs k))
  | [], _ => rfl
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl, instantiateList_mkAppN as]
    simp only [Expr.instantiateList, List.map_cons, Expr.mkAppN]

theorem deepOcc_getAppFn {p : Name → Bool} : ∀ (e : Expr), e.deepOcc p = false →
    e.getAppFn.deepOcc p = false := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h; simp only [Expr.deepOcc, Bool.or_eq_false_iff] at h
    simpa [Expr.getAppFn] using ihf h.1
  | _ => intro h; simpa [Expr.getAppFn] using h

/-- A closed replacement at an index the bulk instantiation substitutes. -/
theorem instantiateList_bvar_closed {vs : List Expr} {k j : Nat} (hkj : k ≤ j)
    (hj : j - k < vs.length) (hcl : ∀ v ∈ vs, v.looseBVarsBounded 0 = true) :
    (Expr.bvar j).instantiateList vs k = vs[j - k] := by
  simp only [Expr.instantiateList]
  rw [if_neg (by omega), dif_pos hj]
  exact Expr.instantiateList_eq_self
    (Expr.looseBVarsBounded_mono (Nat.zero_le _) (hcl _ (List.getElem_mem hj)))

/-! ## The frame constructor's shape -/

variable {wp : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
  {names : List Name} {lvls : List Level} {ks : List Name}

/-- A group hole of the frame at its entry. -/
theorem frame_getElem? {j : Nat} (hj : j < grp.length) :
    ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp).reverse[wp.length + j]? =
      some { key := ⟨grp[j].1, us, ds⟩, base := ctx.hiAt wp.length } := by
  rw [List.reverse_append, List.reverse_reverse, List.getElem?_append_right (by simp)]
  simp [grpNews, hj]

/-- **The uniformity induction**: a sub-term of the container's
constructor body at depth `k` below its parameters, official's uniformity
check passing, closed, mentioning no member and no auxiliary name, becomes
— the group abstracted, the parameters instantiated at the key's (well
shaped, closed) parameters — a term of the walk's shape under the frame. -/
theorem wshape_uniform
    (hsub : ∀ n ∈ grp.map (·.1), names.contains n = true)
    (hds : ∀ x ∈ ds, WShape ctx isAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) x ∧
      x.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), Official.uniformOcc names lvls ds.length (ds.length + k) e = true →
      e.hasFvar = false → e.deepOcc (fun n => ctx.names.contains n || isAux n) = false →
      WShape ctx isAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
        (((e.instantiateLevelParams ks us).replaceConsts
          (grpSub us (ctx.hiAt wp.length) grp)).instantiateList ds.reverse k) := by
  have hcl : ∀ v ∈ ds.reverse, v.looseBVarsBounded 0 = true :=
    fun v hv => (hds v (List.mem_reverse.mp hv)).2
  -- a constant: its hole, or itself
  have hconst : ∀ (n : Nat → Nat) (c : Name) (us' : List Level) (k : Nat),
      (ctx.names.contains c || isAux c) = false →
      (names.contains c = true → ds = []) →
      WShape ctx isAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
        ((((Expr.const c us').instantiateLevelParams ks us).replaceConsts
          (grpSub us (ctx.hiAt wp.length) grp)).instantiateList ds.reverse k) := by
    intro _ c us' k hc hnp
    simp only [Bool.or_eq_false_iff] at hc
    simp only [Expr.instantiateLevelParams, Expr.replaceConsts, grpSub]
    split
    · rename_i hus
      cases hl : (grp.mapIdx fun i (c, ty) => (c, Expr.fvar (ctx.hiAt wp.length + i) ty)).lookup c with
      | none => simp only [Option.getD_none, Expr.instantiateList]; exact .const hc.1 hc.2
      | some e =>
        obtain ⟨j, hj, h1, h2⟩ := lookup_mem_name hl
        simp only [List.length_mapIdx] at hj
        simp only [List.getElem_mapIdx] at h1 h2
        subst h2
        have hmem : c ∈ grp.map (·.1) := by rw [← h1]; exact List.mem_map_of_mem (List.getElem_mem hj)
        have hds0 := hnp (hsub c hmem)
        simp only [Option.getD_some, Expr.instantiateList]
        have hk := frame_getElem? (ctx := ctx) (wp := wp) (us := us) (ds := ds) hj
        have := WShape.frm (ctx := ctx) (isAux := isAux) (is := []) (ty := grp[j].2) hk
          (fun x hx => nomatch hx)
        simp only [hds0, Expr.mkAppN] at this
        rw [show ctx.hiAt wp.length + j = ctx.hiAt 0 + (wp.length + j) by
          simp only [NestCtx.hiAt]; omega]
        rw [hds0] at hk ⊢
        exact this
    · simp only [Option.getD_none, Expr.instantiateList]; exact .const hc.1 hc.2
  intro e
  induction e with
  | bvar j =>
    intro k _ _ _
    by_cases hjk : j < k
    · simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList, if_pos hjk]
      exact .bvar j
    · by_cases hj : j - k < ds.reverse.length
      · simp only [Expr.instantiateLevelParams, Expr.replaceConsts]
        rw [instantiateList_bvar_closed (by omega) hj hcl]
        exact (hds _ (List.mem_reverse.mp (List.getElem_mem hj))).1
      · simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList,
          if_neg hjk, dif_neg hj]
        exact .bvar _
  | fvar i ty _ => intro k _ h; simp [Expr.hasFvar] at h
  | sort u =>
    intro k _ _ _
    simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList]
    exact .sort _
  | lit l =>
    intro k _ _ _
    simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList]
    exact .lit l
  | const c us' =>
    intro k hu _ hd
    simp only [Official.uniformOcc, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      beq_iff_eq] at hu
    refine hconst id c us' k (by simpa [Expr.deepOcc] using hd) (fun hc => ?_)
    rcases hu with hu | hu
    · rw [hu] at hc; exact nomatch hc
    · exact List.eq_nil_of_length_eq_zero hu.1
  | app f a ihf iha =>
    intro k hu hfv hd
    have hfv' := hfv
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv'
    have hd' := hd
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hd'
    -- the congruence case
    have hcong : Official.uniformOcc names lvls ds.length (ds.length + k) f = true →
        Official.uniformOcc names lvls ds.length (ds.length + k) a = true →
        WShape ctx isAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp)
          ((((Expr.app f a).instantiateLevelParams ks us).replaceConsts
            (grpSub us (ctx.hiAt wp.length) grp)).instantiateList ds.reverse k) := by
      intro h1 h2
      simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList]
      exact (ihf k h1 hfv'.1 hd'.1).app' (iha k h2 hfv'.2 hd'.2)
    simp only [Official.uniformOcc] at hu
    split at hu
    · rename_i c us' hfn
      split at hu
      · split at hu
        · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
        · -- the exact occurrence: the group member at the key's parameters
          rename_i hcn _
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hu
          obtain ⟨⟨⟨hlen, -⟩, -⟩, hargs⟩ := hu
          have hE : Expr.app f a = Expr.mkAppN (.const c us') (Expr.app f a).getAppArgs := by
            conv => lhs; rw [← Expr.mkAppN_getApp (.app f a)]
            rw [hfn]
          have hdc : (ctx.names.contains c || isAux c) = false := by
            have := deepOcc_getAppFn _ hd
            rw [hfn] at this; simpa [Expr.deepOcc] using this
          rw [hE, instLP_mkAppN, replaceConsts_mkAppN, instantiateList_mkAppN]
          have hmap : (((Expr.app f a).getAppArgs.map (·.instantiateLevelParams ks us)).map
              (·.replaceConsts (grpSub us (ctx.hiAt wp.length) grp))).map
                (·.instantiateList ds.reverse k) = ds := by
            rw [hargs]
            apply List.ext_getElem (by simp)
            intro i hi₁ hi₂
            simp only [List.getElem_map, List.getElem_range, Expr.instantiateLevelParams,
              Expr.replaceConsts]
            have hi : i < ds.length := hi₂
            rw [instantiateList_bvar_closed (by omega) (by simp; omega) hcl]
            rw [List.getElem_reverse]
            congr 1
            omega
          rw [hmap]
          -- the head: the group hole (then `frm`), or the constant
          simp only [Expr.instantiateLevelParams, Expr.replaceConsts, grpSub]
          split
          · cases hl : (grp.mapIdx fun i (c, ty) =>
                (c, Expr.fvar (ctx.hiAt wp.length + i) ty)).lookup c with
            | none =>
              simp only [Option.getD_none, Expr.instantiateList]
              simp only [Bool.or_eq_false_iff] at hdc
              exact WShape.mkAppN' ds (.const hdc.1 hdc.2) (fun x hx => (hds x hx).1)
            | some e =>
              obtain ⟨j, hj, h1, h2⟩ := lookup_mem_name hl
              simp only [List.length_mapIdx] at hj
              simp only [List.getElem_mapIdx] at h1 h2
              subst h2
              simp only [Option.getD_some, Expr.instantiateList]
              have hk := frame_getElem? (ctx := ctx) (wp := wp) (us := us) (ds := ds) hj
              have := WShape.frm (ctx := ctx) (isAux := isAux) (is := []) (ty := grp[j].2) hk
                (fun x hx => nomatch hx)
              rw [show ctx.hiAt wp.length + j = ctx.hiAt 0 + (wp.length + j) by
                simp only [NestCtx.hiAt]; omega]
              simpa [Expr.mkAppN] using this
          · simp only [Option.getD_none, Expr.instantiateList]
            simp only [Bool.or_eq_false_iff] at hdc
            exact WShape.mkAppN' ds (.const hdc.1 hdc.2) (fun x hx => (hds x hx).1)
      · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
    · simp only [Bool.and_eq_true] at hu; exact hcong hu.1 hu.2
  | lam t b m iht ihb =>
    intro k hu hfv hd
    simp only [Official.uniformOcc, Bool.and_eq_true] at hu
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hd
    simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList]
    exact .lam (iht k hu.1 hfv.1 hd.1) (ihb (k + 1) (by rw [← Nat.add_assoc]; exact hu.2) hfv.2 hd.2)
  | forallE t b m iht ihb =>
    intro k hu hfv hd
    simp only [Official.uniformOcc, Bool.and_eq_true] at hu
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hd
    simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList]
    exact .forallE (iht k hu.1 hfv.1 hd.1)
      (ihb (k + 1) (by rw [← Nat.add_assoc]; exact hu.2) hfv.2 hd.2)
  | letE t v b iht ihv ihb =>
    intro k hu hfv hd
    simp only [Official.uniformOcc, Bool.and_eq_true] at hu
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.deepOcc, Bool.or_eq_false_iff] at hd
    simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList]
    exact .letE (iht k hu.1.1 hfv.1.1 hd.1.1) (ihv k hu.1.2 hfv.1.2 hd.1.2)
      (ihb (k + 1) (by rw [← Nat.add_assoc]; exact hu.2) hfv.2 hd.2)
  | proj s i x ih =>
    intro k hu hfv hd
    simp only [Official.uniformOcc] at hu
    simp only [Expr.hasFvar] at hfv
    simp only [Expr.deepOcc] at hd
    simp only [Expr.instantiateLevelParams, Expr.replaceConsts, Expr.instantiateList]
    exact .proj (ih k hu hfv hd)

/-- **UNIFORMITY ⇒ THE WALK'S SHAPE.**  A frame's constructor (the
container's constructor, its group abstracted, instantiated at the key's
parameters) has the walk's shape under the frame, when the container
passed official's uniformity check, its constructor type is closed and
mentions no member and no auxiliary name, and the key's parameters are
well shaped and closed. -/
theorem wshape_frameCtor {cv : ConstantVal} {crest : Expr}
    (hsub : ∀ n ∈ grp.map (·.1), names.contains n = true)
    (hds : ∀ x ∈ ds, WShape ctx isAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) x ∧
      x.looseBVarsBounded 0 = true)
    (hpi : ds.length ≤ cv.type.piArity)
    (hu : Official.uniformOcc names lvls ds.length 0 cv.type = true)
    (hcl : cv.type.hasFvar = false)
    (hdo : cv.type.deepOcc (fun n => ctx.names.contains n || isAux n) = false)
    (hcr : instPisWith ds ((cv.type.instantiateLevelParams ks us).replaceConsts
      (grpSub us (ctx.hiAt wp.length) grp)) = some crest) :
    WShape ctx isAux ((grpNews us ds (ctx.hiAt wp.length) grp).reverse ++ wp) crest := by
  obtain ⟨bs, r, hr⟩ := stripPis_of_le_piArity ds.length cv.type hpi
  obtain ⟨bs₁, hr₁⟩ := stripPis_instLP (ks := ks) (us := us) ds.length cv.type hr
  obtain ⟨bs₂, hr₂⟩ := stripPis_replaceConsts (f := grpSub us (ctx.hiAt wp.length) grp) _ _ hr₁
  rw [instPisWith_of_stripPis ds _ hr₂, Option.some.injEq] at hcr
  subst hcr
  have hur := uniformOcc_stripPis ds.length cv.type 0 hr hu
  rw [Nat.zero_add, show ds.length = ds.length + 0 from rfl] at hur
  exact wshape_uniform hsub hds r 0 hur (hasFvar_stripPis _ _ hr hcl) (deepOcc_stripPis _ _ hr hdo)

end Unif

end ConLeche
