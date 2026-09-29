module

public import ConLeche.Kernel.Inductives.GenRec
public import ConLeche.Verify.Shift
public import ConLeche.Verify.Inductives.ClassGenScope
public import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.NestScope

public section

/-!
# The generator's pieces do not depend on the depth they are built at
(lane GENREC-CLS)

A minor premise's type `ClassGen.minorTy c x d` is built by opening the
constructor's declared telescope at `d`, reading the walked field types
there, opening each inductive hypothesis's telescope further up, and
closing everything again at the depth it was opened at.  As soon as
everything it reads from OUTSIDE the telescope sits below `d` (the
parameters, the constructor's types, the class's parameters, the motive
variables it names), the result does not depend on `d` at all — the same
term at every such depth.  The proof is the checker's depth-invariance
bisimulation in miniature: every step commutes with `shiftFrom p`
(`openPisAtFvars`, `targetPiDomsWith`, `getAppArgs`, `mkAppN`,
`closeTelescope`), and a term scoped below the cut is unmoved.

What it buys: the generated recursor type's prefix holds a minor premise
built at its SLOT `nP + s`, while the generated rules (and the rule
frame the family premise is stated at) build the same pieces at the rule
prefix `rP`.  By `ClassGen.minorTy_depth` the two are one term.
-/

namespace ConLeche

open Expr

/-! ## Shifting commutes with the generator's steps -/

theorem shiftFrom_getD {p : Nat} (l : List Expr) (i : Nat) :
    (l.map (shiftFrom p)).getD i default = shiftFrom p (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> rfl

/-- **Opening commutes with a shift below the opening depth.** -/
theorem openPisAtFvars_shiftFrom {p : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr}, p ≤ d →
      openPisAtFvars n e d = some (fvs, o) →
      openPisAtFvars n (shiftFrom p e) (d + 1) = some (fvs.map (shiftFrom p), shiftFrom p o)
  | 0, e, d, fvs, o, _, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | n + 1, .forallE dom body mb, d, fvs, o, hpd, h => by
    simp only [openPisAtFvars] at h
    split at h
    · next fvs' o' hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := openPisAtFvars_shiftFrom n (by omega : p ≤ d + 1) hrec
      rw [shiftFrom_instantiate1 hpd] at ih
      simp only [shiftFrom, openPisAtFvars]
      rw [ih]
      simp only [List.map_cons, shiftFrom, if_pos hpd]
    · exact nomatch h
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h
  | _ + 1, .sort _, _, _, _, _, h | _ + 1, .const _ _, _, _, _, _, h
  | _ + 1, .app _ _, _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, _, h
  | _ + 1, .letE _ _ _, _, _, _, _, h | _ + 1, .lit _, _, _, _, _, h
  | _ + 1, .proj _ _ _, _, _, _, _, h => by simp [openPisAtFvars] at h

/-- **Instantiating a telescope's domains commutes with a shift.** -/
theorem targetPiDomsWith_shiftFrom {p : Nat} :
    ∀ (fvs : List Expr) {T : Expr} {ws : List Expr}, targetPiDomsWith fvs T = some ws →
      targetPiDomsWith (fvs.map (shiftFrom p)) (shiftFrom p T) = some (ws.map (shiftFrom p))
  | [], T, ws, h => by
    simp only [targetPiDomsWith, Option.some.injEq] at h
    subst h; rfl
  | x :: xs, .forallE d b mb, ws, h => by
    simp only [targetPiDomsWith, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨rest, hr, rfl⟩ := h
    have ih := targetPiDomsWith_shiftFrom (p := p) xs hr
    rw [shiftFrom_instantiate1_gen] at ih
    simp only [List.map_cons, shiftFrom, targetPiDomsWith, ih]
    rfl
  | _ :: _, .bvar _, _, h | _ :: _, .fvar _ _, _, h | _ :: _, .sort _, _, h
  | _ :: _, .const _ _, _, h | _ :: _, .app _ _, _, h | _ :: _, .lam _ _ _, _, h
  | _ :: _, .letE _ _ _, _, h | _ :: _, .lit _, _, h | _ :: _, .proj _ _ _, _, h => by
    simp [targetPiDomsWith] at h

/-- **Closing a telescope commutes with a shift below its depth.** -/
theorem closeTelescope_shiftFrom {p : Nat} :
    ∀ (bs : List (Expr × BinderMeta)) (d : Nat) (body : Expr), p ≤ d →
      shiftFrom p (closeTelescope bs d body)
        = closeTelescope (bs.map fun b => (shiftFrom p b.1, b.2)) (d + 1) (shiftFrom p body)
  | [], _, _, _ => rfl
  | (dom, bm) :: bs, d, body, hpd => by
    simp only [closeTelescope, shiftFrom, List.map_cons]
    rw [shiftFrom_abstract1 hpd, closeTelescope_shiftFrom bs (d + 1) body (by omega)]

/-- A shift from `p` moves a variable at or above `p` up by one, its
annotation shifted. -/
theorem shiftFrom_fvar_ge {p i : Nat} (h : p ≤ i) (ty : Expr) :
    shiftFrom p (.fvar i ty) = .fvar (i + 1) (shiftFrom p ty) := by
  simp [shiftFrom, h]

/-- A shift from `p` fixes a variable below `p`. -/
theorem shiftFrom_fvar_lt {p i : Nat} (h : i < p) (ty : Expr) :
    shiftFrom p (.fvar i ty) = .fvar i ty := by
  simp [shiftFrom, show ¬ p ≤ i by omega]

/-! ## The generator's steps, shifted -/

/-- **An inductive hypothesis's pieces, shifted.** -/
theorem ClassGen.ihParts_shiftFrom {g : ClassGen} {p t tele d : Nat} {w : Expr}
    {xs idx : List Expr} (hpd : p ≤ d) (h : g.ihParts t tele w d = some (xs, idx)) :
    g.ihParts t tele (shiftFrom p w) (d + 1) = some (xs.map (shiftFrom p), idx.map (shiftFrom p)) := by
  unfold ClassGen.ihParts at h ⊢
  obtain ⟨⟨xs', leaf⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [openPisAtFvars_shiftFrom tele hpd hop]
  show some _ = _
  rw [getAppArgs_shiftFrom, List.map_drop]

/-- The binder datum of a shifted variable is the shifted datum. -/
theorem ClassGen.binder_shiftFrom (g : ClassGen) {p : Nat} (x : Expr) (hx : ∀ i ty, x = .fvar i ty →
    p ≤ i) : g.binder (shiftFrom p x) = ((shiftFrom p (g.binder x).1), (g.binder x).2) := by
  cases x with
  | fvar i ty =>
    rw [shiftFrom_fvar_ge (hx i ty rfl)]
    simp [ClassGen.binder, Expr.fvarTypeD]
  | _ => simp [ClassGen.binder, shiftFrom, Expr.fvarTypeD]

end ConLeche

namespace ConLeche

open Expr

/-- `Option.mapM` over pointwise-related results. -/
theorem option_mapM_rel {α β γ : Type} :
    ∀ (l : List α) {f : α → Option β} {f' : α → Option γ} {τ : β → γ} {r : List β},
      l.mapM f = some r → (∀ a ∈ l, ∀ b, f a = some b → f' a = some (τ b)) →
      l.mapM f' = some (r.map τ)
  | [], _, _, _, r, h, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | a :: l, f, f', τ, r, h, hp => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure, Option.some.injEq] at h
    subst h
    rw [hp a List.mem_cons_self b hb,
      option_mapM_rel l hbs (fun a' ha' b' hb' => hp a' (List.mem_cons_of_mem _ ha') b' hb')]
    rfl

set_option maxHeartbeats 1600000 in
/-- **A minor premise's type, one level deeper**: built at `d + 1` it is
the one built at `d` shifted from any cut `p ≤ d` below which the
generator's outside inputs sit. -/
theorem ClassGen.minorTy_shiftFrom {g : ClassGen} {c : Nat} {x : ClassCtor} {p d : Nat}
    (hpd : p ≤ d) (hD : fvarsBelow p x.tyD) (hN : fvarsBelow p x.tyN)
    (hds : ∀ e ∈ (g.cls.getD c default).ds, fvarsBelow p e)
    (hmot : ∀ t, (t = c ∨ ∃ i tele, (i, t, tele) ∈ x.recs) →
      g.nP + (ClassRead.motiveSlot ⟨g.slots, []⟩ t).getD 0 < p)
    {T : Expr} (h : g.minorTy c x d = some T) :
    g.minorTy c x (d + 1) = some (shiftFrom p T) := by
  have hmv : ∀ t, (t = c ∨ ∃ i tele, (i, t, tele) ∈ x.recs) →
      shiftFrom p (g.motVar t) = g.motVar t := fun t ht => by
    simp only [ClassGen.motVar, ClassGen.slotVar]
    exact shiftFrom_fvar_lt (hmot t ht) _
  unfold ClassGen.minorTy at h ⊢
  obtain ⟨⟨fvs, res⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ihs, hihs, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  have hop' := openPisAtFvars_shiftFrom x.nF hpd hop
  rw [shiftFrom_eq_self hD] at hop'
  have hws' := targetPiDomsWith_shiftFrom (p := p) fvs hws
  rw [shiftFrom_eq_self hN] at hws'
  have hfvs := ConLeche.openPisAtFvars_index x.nF _ _ hop
  refine Option.bind_eq_some_iff.mpr ⟨(fvs.map (shiftFrom p), shiftFrom p res), hop', ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨ws.map (shiftFrom p), hws', ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨ihs.map fun b => (shiftFrom p b.1, b.2),
    option_mapM_rel _ hihs fun l hl b hb => ?_, ?_⟩
  · have hl' : l < x.recs.length := by
      have := List.mem_range.mp hl; exact this

    split at hb
    next i t tele hq =>
    dsimp only
    have hmem : (i, t, tele) ∈ x.recs := by
      rw [← hq]
      exact getD_mem_of_lt hl' _
    try simp only at hb ⊢
    obtain ⟨⟨xs, idx⟩, hip, hb⟩ := Option.bind_eq_some_iff.mp hb
    simp only [Option.pure_def, Option.some.injEq] at hb
    subst hb
    have hip' := ClassGen.ihParts_shiftFrom (p := p) (by omega) hip
    rw [← shiftFrom_getD] at hip'
    rw [show d + 1 + x.nF + l = d + x.nF + l + 1 by omega]
    refine Option.bind_eq_some_iff.mpr ⟨(xs.map (shiftFrom p), idx.map (shiftFrom p)), hip', ?_⟩
    have hop2 : ∃ leaf, openPisAtFvars tele (ws.getD i default) (d + x.nF + l)
        = some (xs, leaf) := by
      unfold ClassGen.ihParts at hip
      obtain ⟨⟨xs', leaf⟩, hop2, hip⟩ := Option.bind_eq_some_iff.mp hip
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hip
      obtain ⟨rfl, -⟩ := hip
      exact ⟨leaf, hop2⟩
    obtain ⟨leaf, hop2⟩ := hop2
    have hxsF := ConLeche.openPisAtFvars_index _ _ _ hop2
    have hX : List.map g.binder (xs.map (shiftFrom p))
        = (xs.map g.binder).map fun b => (shiftFrom p b.1, b.2) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun y hy => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      obtain ⟨ty, hxe⟩ := hxsF k _ (List.getElem?_eq_getElem hk)
      simp only [Function.comp]
      rw [ClassGen.binder_shiftFrom g _ (fun i' ty' h' => by
        rw [hxe] at h'; injection h' with h1; omega)]
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, and_true]
    rw [hX, closeTelescope_shiftFrom _ _ _ (by omega), shiftFrom_mkAppN,
      hmv t (.inr ⟨i, tele, hmem⟩), List.map_append, List.map_cons, List.map_nil,
      shiftFrom_mkAppN, shiftFrom_getD]
  · -- the whole telescope
    show some _ = some _
    congr 1
    have hF : List.map g.binder (fvs.map (shiftFrom p))
        = (fvs.map g.binder).map fun b => (shiftFrom p b.1, b.2) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun y hy => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      obtain ⟨ty, hxe⟩ := hfvs k _ (List.getElem?_eq_getElem hk)
      simp only [Function.comp]
      rw [ClassGen.binder_shiftFrom g _ (fun i' ty' h' => by
        rw [hxe] at h'; injection h' with h1; omega)]
    have hdsE : (g.cls.getD c default).ds.map (shiftFrom p) = (g.cls.getD c default).ds :=
      (List.map_congr_left fun e he => shiftFrom_eq_self (hds e he)).trans (List.map_id _)
    rw [closeTelescope_shiftFrom _ _ _ hpd, List.map_append, ← hF, shiftFrom_mkAppN,
      hmv c (.inl rfl), List.map_append, List.map_cons, List.map_nil, shiftFrom_mkAppN,
      getAppArgs_shiftFrom, List.map_drop, List.map_append, hdsE]
    rfl


/-- **A minor premise's type is the same at every depth** above its
slot: at `d₀` its outside inputs sit below `d₀` (the constructor's types,
the class's parameters, the motives it names), and the type itself is
scoped below `d₀`. -/
theorem ClassGen.minorTy_depth {g : ClassGen} {c : Nat} {x : ClassCtor} {d₀ : Nat}
    (hD : fvarsBelow d₀ x.tyD) (hN : fvarsBelow d₀ x.tyN)
    (hds : ∀ e ∈ (g.cls.getD c default).ds, fvarsBelow d₀ e)
    (hmot : ∀ t, (t = c ∨ ∃ i tele, (i, t, tele) ∈ x.recs) →
      g.nP + (ClassRead.motiveSlot ⟨g.slots, []⟩ t).getD 0 < d₀)
    {T : Expr} (hT : fvarsBelow d₀ T) (h : g.minorTy c x d₀ = some T) :
    ∀ k, g.minorTy c x (d₀ + k) = some T
  | 0 => h
  | k + 1 => by
    have ih := ClassGen.minorTy_depth hD hN hds hmot hT h k
    have := ClassGen.minorTy_shiftFrom (p := d₀ + k) (Nat.le_refl _)
      (fvarsBelow_mono (by omega) hD) (fvarsBelow_mono (by omega) hN)
      (fun e he => fvarsBelow_mono (by omega) (hds e he))
      (fun t ht => Nat.lt_of_lt_of_le (hmot t ht) (by omega)) ih
    rw [shiftFrom_eq_self (fvarsBelow_mono (by omega) hT)] at this
    exact this

/-- **An inductive hypothesis's type** (the generator's, inside a minor
premise): the walked field's telescope `w`, opened at `e`, closed over
the motive of class `t` at the leaf's indices and the applied field `f`. -/
@[expose] def ClassGen.ihTy (g : ClassGen) (t tele : Nat) (w f : Expr) (e : Nat) :
    Option Expr := do
  let (xs, idx) ← g.ihParts t tele w e
  pure (closeTelescope (xs.map g.binder) e
    (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN f xs])))

/-- **An inductive hypothesis's type is the same at every depth** above
its outside inputs. -/
theorem ClassGen.ihTy_depth {g : ClassGen} {t tele : Nat} {w f : Expr} {e₀ : Nat}
    (hw : fvarsBelow e₀ w) (hf : fvarsBelow e₀ f)
    (hmot : g.nP + (ClassRead.motiveSlot ⟨g.slots, []⟩ t).getD 0 < e₀)
    {T : Expr} (hT : fvarsBelow e₀ T) (h : g.ihTy t tele w f e₀ = some T) :
    ∀ k, g.ihTy t tele w f (e₀ + k) = some T
  | 0 => h
  | k + 1 => by
    have ih := ClassGen.ihTy_depth hw hf hmot hT h k
    unfold ClassGen.ihTy at ih ⊢
    obtain ⟨⟨xs, idx⟩, hip, ih⟩ := Option.bind_eq_some_iff.mp ih
    simp only [Option.pure_def, Option.some.injEq] at ih
    have hp : e₀ + k ≤ e₀ + k := Nat.le_refl _
    have hip' := ClassGen.ihParts_shiftFrom (p := e₀ + k) hp hip
    rw [shiftFrom_eq_self (fvarsBelow_mono (by omega) hw)] at hip'
    rw [show e₀ + (k + 1) = e₀ + k + 1 by omega]
    refine Option.bind_eq_some_iff.mpr ⟨(xs.map (shiftFrom (e₀ + k)),
      idx.map (shiftFrom (e₀ + k))), hip', ?_⟩
    have hop2 : ∃ leaf, openPisAtFvars tele w (e₀ + k) = some (xs, leaf) := by
      unfold ClassGen.ihParts at hip
      obtain ⟨⟨xs', leaf⟩, hop2, hip⟩ := Option.bind_eq_some_iff.mp hip
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hip
      obtain ⟨rfl, -⟩ := hip
      exact ⟨leaf, hop2⟩
    obtain ⟨leaf, hop2⟩ := hop2
    have hxsF := ConLeche.openPisAtFvars_index _ _ _ hop2
    have hX : List.map g.binder (xs.map (shiftFrom (e₀ + k)))
        = (xs.map g.binder).map fun b => (shiftFrom (e₀ + k) b.1, b.2) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun y hy => ?_
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      obtain ⟨ty, hxe⟩ := hxsF j _ (List.getElem?_eq_getElem hj)
      simp only [Function.comp]
      rw [ClassGen.binder_shiftFrom g _ (fun i' ty' h' => by
        rw [hxe] at h'; injection h' with h1; omega)]
    have hmv : shiftFrom (e₀ + k) (g.motVar t) = g.motVar t := by
      simp only [ClassGen.motVar, ClassGen.slotVar]
      exact shiftFrom_fvar_lt (by omega) _
    simp only [Option.pure_def, Option.some.injEq]
    rw [hX]
    calc _ = shiftFrom (e₀ + k) (closeTelescope (xs.map g.binder) (e₀ + k)
          (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN f xs]))) := by
          rw [closeTelescope_shiftFrom _ _ _ (Nat.le_refl _), shiftFrom_mkAppN, hmv,
            List.map_append, List.map_cons, List.map_nil, shiftFrom_mkAppN,
            shiftFrom_eq_self (fvarsBelow_mono (by omega) hf)]
      _ = T := by rw [ih]; exact shiftFrom_eq_self (fvarsBelow_mono (by omega) hT)


set_option maxHeartbeats 800000 in
/-- **A minor premise's type, spelled out** at any depth `d`: the
constructor's declared telescope opened at `d`, the walked field types
there, one inductive hypothesis type (`ClassGen.ihTy`) per recursive
field, the conclusion the class's motive at the declared result's
indices and the constructor applied. -/
theorem ClassGen.minorTy_unfold {g : ClassGen} {c : Nat} {x : ClassCtor} {d : Nat} {T : Expr}
    (h : g.minorTy c x d = some T) :
    ∃ (fvs : List Expr) (res : Expr) (ws : List Expr) (ihs : List (Expr × BinderMeta)),
      openPisAtFvars x.nF x.tyD d = some (fvs, res) ∧
      targetPiDomsWith fvs x.tyN = some ws ∧
      ihs.length = x.recs.length ∧
      (∀ (l i t tele : Nat), x.recs[l]? = some (i, t, tele) → ∃ ty,
        g.ihTy t tele (ws.getD i default) (fvs.getD i default) (d + x.nF + l) = some ty ∧
        ihs[l]? = some (ty, g.bm)) ∧
      T = closeTelescope (fvs.map g.binder ++ ihs) d
        (Expr.mkAppN (g.motVar c) (res.getAppArgs.drop (g.cls.getD c default).nPc ++
          [Expr.mkAppN (.const x.cv.name (g.cls.getD c default).lvls)
            ((g.cls.getD c default).ds ++ fvs)])) := by
  unfold ClassGen.minorTy at h
  obtain ⟨⟨fvs, res⟩, hop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ihs, hihs, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  have hihl := option_mapM_length hihs
  simp only [List.length_range] at hihl
  refine ⟨fvs, res, ws, ihs, hop, hws, hihl, fun l i t tele hrl => ?_, rfl⟩
  have hl : l < x.recs.length := (List.getElem?_eq_some_iff.mp hrl).1
  obtain ⟨y, hy, hyb⟩ := option_mapM_getElem? hihs l l (List.getElem?_range (by
    exact lt_of_lt_of_eq hl rfl))
  have hq : x.recs.getD l default = (i, t, tele) := by
    rw [List.getD_eq_getElem?_getD, hrl]; rfl
  split at hy
  next i' t' tele' hq' =>
  obtain ⟨rfl, rfl, rfl⟩ : i = i' ∧ t = t' ∧ tele = tele' := by
    have : x.recs.getD l default = (i', t', tele') := hq'
    rw [hq] at this
    injection this with h1 h2; injection h2 with h2 h3; exact ⟨h1, h2, h3⟩
  obtain ⟨⟨xs, idx⟩, hip, hy⟩ := Option.bind_eq_some_iff.mp hy
  simp only [Option.pure_def, Option.some.injEq] at hy
  subst hy
  refine ⟨_, ?_, hyb⟩
  unfold ClassGen.ihTy
  rw [hip]
  rfl

end ConLeche
