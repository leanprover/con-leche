module

public import InLeanProof.Sim
public import InLeanProof.FVar
public import InLeanProof.Range

/-!
# The translation as `grind` vocabulary (task #451, lane P2-0)

The body walks of InLean (`InLeanProof/Walks*.lean`) are the cached twins'
`sym … => vcgen … <;> finish` scripts (`Verify/Cached/DiscC*.lean`), with
InLean's program on the left and con-leche's *pure* fueled checker, at the
translation, on the right.  A post states InLean's value through the
translation, never as `∃ c, TransS s v = some c ∧ …` (the rule of
`Verify/Cached/Grind.lean` §2): the translation is a **total** function
`TrS s` with unconditional equations, one per constructor, and the side
condition that the partial reading `TransS` is defined is the Boolean
`OkS s`, again one equation per constructor.  On a term with `OkS` the two
agree (`TransS_of_ok`), so every operation lemma of lane P1 (stated over
`toExpr`) carries over.

Families (all `@[conleche_grind]`, the walks' shared set):

1. **The total translation** `trL`, `trE`, `TrS` and its constructor
   equations; `mdata` and `EO.stripTop` are invisible (`TrS_stripTop`).
2. **The side condition** `okL`, `okE`, `OkS` and its constructor
   equations.
3. **Agreement with the partial reading** (`TransS_of_ok`,
   `trE_of_toExpr`).
4. **Stability along the run**: the free-variable table only grows
   (`TabLe`), and a term's translation read at a later state is the same
   (`TrS_of_tabLe`).
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## 1. The total translation -/

/-- Levels, total: a level metavariable reads as `zero` (never reached on a
term with `okL`). -/
@[expose] def trL : Level → ConLeche.Level
  | .zero => .zero
  | .succ u => .succ (trL u)
  | .max u v => .max (trL u) (trL v)
  | .imax u v => .imax (trL u) (trL v)
  | .param n => .param (toName n)
  | .mvar _ => .zero

/-- Expressions, total, given the id translation: what has no reading
(a metavariable, an untranslatable free variable) reads as `bvar 0`. -/
@[expose] def trE (fv : FVarId → Option ConLeche.Expr) : Expr → ConLeche.Expr
  | .bvar i => .bvar i
  | .fvar id => (fv id).getD (.bvar 0)
  | .mvar _ => .bvar 0
  | .sort u => .sort (trL u)
  | .const n us => .const (toName n) (us.map trL)
  | .app f a => .app (trE fv f) (trE fv a)
  | .lam _ t b _ => .lam (trE fv t) (trE fv b)
  | .forallE _ t b _ => .forallE (trE fv t) (trE fv b)
  | .letE _ t v b _ => .letE (trE fv t) (trE fv v) (trE fv b)
  | .lit l => .lit (toLit l)
  | .mdata _ e => trE fv e
  | .proj s i e => .proj (toName s) i (trE fv e)

/-- **The translation at state `s`**: free variables through the state's
table. -/
@[expose] def TrS (s : InLean.CState) : Expr → ConLeche.Expr :=
  trE (FVarTable.trans (tableOf s))

section Eqns
variable (s : InLean.CState)

@[conleche_grind =] theorem TrS_bvar (i : Nat) : TrS s (.bvar i) = .bvar i := rfl
@[conleche_grind =] theorem TrS_sort (u : Level) : TrS s (.sort u) = .sort (trL u) := rfl
@[conleche_grind =] theorem TrS_const (n : Name) (us : List Level) :
    TrS s (.const n us) = .const (toName n) (us.map trL) := rfl
@[conleche_grind =] theorem TrS_app (f a : Expr) : TrS s (.app f a) = .app (TrS s f) (TrS s a) := rfl
@[conleche_grind =] theorem TrS_lam (n : Name) (t b : Expr) (bi : BinderInfo) :
    TrS s (.lam n t b bi) = .lam (TrS s t) (TrS s b) := rfl
@[conleche_grind =] theorem TrS_forallE (n : Name) (t b : Expr) (bi : BinderInfo) :
    TrS s (.forallE n t b bi) = .forallE (TrS s t) (TrS s b) := rfl
@[conleche_grind =] theorem TrS_letE (n : Name) (t v b : Expr) (nd : Bool) :
    TrS s (.letE n t v b nd) = .letE (TrS s t) (TrS s v) (TrS s b) := rfl
@[conleche_grind =] theorem TrS_lit (l : Literal) : TrS s (.lit l) = .lit (toLit l) := rfl
@[conleche_grind =] theorem TrS_mdata (m : MData) (e : Expr) : TrS s (.mdata m e) = TrS s e := rfl
@[conleche_grind =] theorem TrS_proj (n : Name) (i : Nat) (e : Expr) :
    TrS s (.proj n i e) = .proj (toName n) i (TrS s e) := rfl

/-- `EO.stripTop` is invisible to the translation (the stuttering step). -/
theorem TrS_stripTop (e : Expr) : TrS s (EO.stripTop e) = TrS s e := by
  induction e <;> simp_all [EO.stripTop, TrS, trE]
grind_pattern [conleche_grind] TrS_stripTop => EO.stripTop e, TrS s e

end Eqns

/-! ## 2. The side condition -/

/-- A level has a reading: no metavariable. -/
@[expose] def okL : Level → Bool
  | .zero | .param _ => true
  | .succ u => okL u
  | .max u v | .imax u v => okL u && okL v
  | .mvar _ => false

/-- A level has a reading and is within C's depth bound. -/
@[expose] def okLv (u : Level) : Bool := okL u && decide (depthS u ≤ maxLevelDepth)

/-- A term has a reading under `fv`, and is in range (`Expr.RangeOk`: the
cached fields mean what the walks compute). -/
@[expose] def okE (fv : FVarId → Option ConLeche.Expr) : Expr → Bool
  | .bvar i => decide (i + 1 ≤ maxRange)
  | .lit _ => true
  | .fvar id => (fv id).isSome
  | .mvar _ => false
  | .sort u => okLv u
  | .const _ us => us.all okLv
  | .app f a | .lam _ f a _ | .forallE _ f a _ => okE fv f && okE fv a
  | .letE _ t v b _ => okE fv t && okE fv v && okE fv b
  | .mdata _ e | .proj _ _ e => okE fv e

/-- **The term has a reading at state `s`.** -/
@[expose] def OkS (s : InLean.CState) (e : Expr) : Bool :=
  okE (FVarTable.trans (tableOf s)) e

section OkEqns
variable (s : InLean.CState)

@[conleche_grind =] theorem OkS_bvar (i : Nat) : OkS s (.bvar i) = decide (i + 1 ≤ maxRange) := rfl
@[conleche_grind =] theorem OkS_sort (u : Level) : OkS s (.sort u) = okLv u := rfl
@[conleche_grind =] theorem OkS_const (n : Name) (us : List Level) :
    OkS s (.const n us) = us.all okLv := rfl
@[conleche_grind =] theorem OkS_app (f a : Expr) : OkS s (.app f a) = (OkS s f && OkS s a) := rfl
@[conleche_grind =] theorem OkS_lam (n : Name) (t b : Expr) (bi : BinderInfo) :
    OkS s (.lam n t b bi) = (OkS s t && OkS s b) := rfl
@[conleche_grind =] theorem OkS_forallE (n : Name) (t b : Expr) (bi : BinderInfo) :
    OkS s (.forallE n t b bi) = (OkS s t && OkS s b) := rfl
@[conleche_grind =] theorem OkS_letE (n : Name) (t v b : Expr) (nd : Bool) :
    OkS s (.letE n t v b nd) = (OkS s t && OkS s v && OkS s b) := rfl
@[conleche_grind =] theorem OkS_lit (l : Literal) : OkS s (.lit l) = true := rfl
@[conleche_grind =] theorem OkS_mdata (m : MData) (e : Expr) : OkS s (.mdata m e) = OkS s e := rfl
@[conleche_grind =] theorem OkS_proj (n : Name) (i : Nat) (e : Expr) :
    OkS s (.proj n i e) = OkS s e := rfl

theorem OkS_stripTop (e : Expr) : OkS s (EO.stripTop e) = OkS s e := by
  induction e <;> simp_all [EO.stripTop, OkS, okE]
grind_pattern [conleche_grind] OkS_stripTop => EO.stripTop e, OkS s e

end OkEqns

/-! ## 3. Agreement with the partial reading -/

theorem toLevel_of_okL : ∀ {u : Level}, okL u = true → toLevel u = some (trL u)
  | .zero, _ => rfl
  | .param _, _ => rfl
  | .mvar _, h => by simp [okL] at h
  | .succ u, h => by simp [okL] at h; simp [toLevel, trL, toLevel_of_okL h]
  | .max u v, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp [toLevel, trL, toLevel_of_okL h.1, toLevel_of_okL h.2]
  | .imax u v, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp [toLevel, trL, toLevel_of_okL h.1, toLevel_of_okL h.2]

theorem toLevels_of_all : ∀ {us : List Level}, us.all okL = true → toLevels us = some (us.map trL)
  | [], _ => rfl
  | u :: us, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [toLevels, toLevel_of_okL h.1, toLevels_of_all h.2]

theorem okL_of_toLevel : ∀ {u : Level} {c : ConLeche.Level}, toLevel u = some c →
    okL u = true ∧ trL u = c
  | .zero, c, h => by simp [toLevel] at h; exact ⟨rfl, h⟩
  | .param _, c, h => by simp [toLevel] at h; exact ⟨rfl, h⟩
  | .mvar _, c, h => by simp [toLevel] at h
  | .succ u, c, h => by
    simp only [toLevel, Option.map_eq_some_iff] at h
    obtain ⟨cu, hu, rfl⟩ := h
    obtain ⟨h1, h2⟩ := okL_of_toLevel hu
    exact ⟨h1, by simp [trL, h2]⟩
  | .max u v, c, h => by
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu, hu, cv, hv, rfl⟩ := h
    obtain ⟨h1, h2⟩ := okL_of_toLevel hu; obtain ⟨h3, h4⟩ := okL_of_toLevel hv
    exact ⟨by simp [okL, h1, h3], by simp [trL, h2, h4]⟩
  | .imax u v, c, h => by
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu, hu, cv, hv, rfl⟩ := h
    obtain ⟨h1, h2⟩ := okL_of_toLevel hu; obtain ⟨h3, h4⟩ := okL_of_toLevel hv
    exact ⟨by simp [okL, h1, h3], by simp [trL, h2, h4]⟩

theorem okLs_of_toLevels : ∀ {us : List Level} {cs : List ConLeche.Level}, toLevels us = some cs →
    us.all okL = true ∧ us.map trL = cs
  | [], cs, h => by simp [toLevels] at h; exact ⟨rfl, by simp [h]⟩
  | u :: us, cs, h => by
    simp only [toLevels, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu, hu, cus, hus, rfl⟩ := h
    obtain ⟨h1, h2⟩ := okL_of_toLevel hu; obtain ⟨h3, h4⟩ := okLs_of_toLevels hus
    exact ⟨by simp [h1, h3], by simp [h2, h4]⟩

/-- On a term with a reading, the partial translation is the total one. -/
theorem toExpr_of_okE (fv : FVarId → Option ConLeche.Expr) :
    ∀ {e : Expr}, okE fv e = true → toExpr fv e = some (trE fv e) := by
  intro e
  induction e with
  | fvar id =>
    intro h; simp only [okE, Option.isSome_iff_exists] at h
    obtain ⟨c, hc⟩ := h; simp [toExpr, trE, hc]
  | mvar _ => intro h; simp [okE] at h
  | sort u =>
    intro h; simp only [okE, okLv, Bool.and_eq_true] at h
    simp [toExpr, trE, toLevel_of_okL h.1]
  | const n us =>
    intro h; simp only [okE] at h
    have h' : us.all okL = true := by
      simp only [List.all_eq_true, okLv, Bool.and_eq_true] at h ⊢; exact fun u hu => (h u hu).1
    simp [toExpr, trE, toLevels_of_all h']
  | app f a ihf iha =>
    intro h; simp only [okE, Bool.and_eq_true] at h; simp [toExpr, trE, ihf h.1, iha h.2]
  | lam _ t b _ iht ihb =>
    intro h; simp only [okE, Bool.and_eq_true] at h; simp [toExpr, trE, iht h.1, ihb h.2]
  | forallE _ t b _ iht ihb =>
    intro h; simp only [okE, Bool.and_eq_true] at h; simp [toExpr, trE, iht h.1, ihb h.2]
  | letE _ t v b _ iht ihv ihb =>
    intro h; simp only [okE, Bool.and_eq_true] at h
    simp [toExpr, trE, iht h.1.1, ihv h.1.2, ihb h.2]
  | mdata _ x ih => intro h; simp only [okE] at h; simp [toExpr, trE, ih h]
  | proj _ _ x ih => intro h; simp only [okE] at h; simp [toExpr, trE, ih h]
  | bvar _ => intro _; rfl
  | lit _ => intro _; rfl

/-- And a defined partial translation means a reading. -/
theorem okE_of_toExpr (fv : FVarId → Option ConLeche.Expr) :
    ∀ {e : Expr} {c : ConLeche.Expr}, Expr.RangeOk e → toExpr fv e = some c →
      okE fv e = true ∧ trE fv e = c := by
  intro e
  induction e with
  | fvar id => intro c _ h; simp [toExpr] at h; simp [okE, trE, h]
  | mvar _ => intro c _ h; simp [toExpr] at h
  | sort u =>
    intro c hr h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cu, hu, rfl⟩ := h
    obtain ⟨h1, h2⟩ := okL_of_toLevel hu
    exact ⟨by simp only [okE, okLv, h1, Bool.true_and, decide_eq_true_eq]; exact hr,
      by simp [trE, h2]⟩
  | const n us =>
    intro c hr h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cus, hus, rfl⟩ := h
    obtain ⟨h1, h2⟩ := okLs_of_toLevels hus
    refine ⟨?_, by simp [trE, h2]⟩
    simp only [okE, List.all_eq_true, okLv, Bool.and_eq_true, decide_eq_true_eq]
    simp only [List.all_eq_true] at h1
    exact fun u hu => ⟨h1 u hu, hr u hu⟩
  | app f a ihf iha =>
    intro c hr h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cf, hf, ca, ha, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ihf hr.1 hf; obtain ⟨h3, h4⟩ := iha hr.2 ha
    exact ⟨by simp [okE, h1, h3], by simp [trE, h2, h4]⟩
  | lam _ t b _ iht ihb =>
    intro c hr h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    obtain ⟨h1, h2⟩ := iht hr.1 ht; obtain ⟨h3, h4⟩ := ihb hr.2 hb
    exact ⟨by simp [okE, h1, h3], by simp [trE, h2, h4]⟩
  | forallE _ t b _ iht ihb =>
    intro c hr h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    obtain ⟨h1, h2⟩ := iht hr.1 ht; obtain ⟨h3, h4⟩ := ihb hr.2 hb
    exact ⟨by simp [okE, h1, h3], by simp [trE, h2, h4]⟩
  | letE _ t v b _ iht ihv ihb =>
    intro c hr h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    obtain ⟨h1, h2⟩ := iht hr.1 ht; obtain ⟨h3, h4⟩ := ihv hr.2.1 hv
    obtain ⟨h5, h6⟩ := ihb hr.2.2 hb
    exact ⟨by simp [okE, h1, h3, h5], by simp [trE, h2, h4, h6]⟩
  | mdata _ x ih => intro c hr h; simp only [toExpr] at h; exact ih hr h
  | proj _ _ x ih =>
    intro c hr h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hr hx
    exact ⟨h1, by simp [trE, h2]⟩
  | bvar i =>
    intro c hr h; simp [toExpr] at h
    exact ⟨by simp only [okE, decide_eq_true_eq]; exact hr, h⟩
  | lit _ => intro c _ h; simp [toExpr] at h; exact ⟨rfl, h⟩

/-- A term with a reading is in range. -/
theorem RangeOk_of_okE {fv : FVarId → Option ConLeche.Expr} :
    ∀ {e : Expr}, okE fv e = true → Expr.RangeOk e := by
  intro e
  induction e with
  | bvar i => intro h; simpa [okE, Expr.RangeOk] using h
  | sort u => intro h; simp only [okE, okLv, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  | const n us =>
    intro h u hu
    simp only [okE, List.all_eq_true, okLv, Bool.and_eq_true, decide_eq_true_eq] at h
    exact (h u hu).2
  | app f a ihf iha => intro h; simp only [okE, Bool.and_eq_true] at h; exact ⟨ihf h.1, iha h.2⟩
  | lam _ t b _ iht ihb => intro h; simp only [okE, Bool.and_eq_true] at h; exact ⟨iht h.1, ihb h.2⟩
  | forallE _ t b _ iht ihb =>
    intro h; simp only [okE, Bool.and_eq_true] at h; exact ⟨iht h.1, ihb h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro h; simp only [okE, Bool.and_eq_true] at h; exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | mdata _ x ih => intro h; exact ih h
  | proj _ _ x ih => intro h; exact ih h
  | fvar _ | mvar _ | lit _ => intro _; trivial

theorem RangeOk_of_OkS {s : InLean.CState} {e : Expr} (h : OkS s e = true) : Expr.RangeOk e :=
  RangeOk_of_okE h

/-- **The bridge**: on a term with a reading at `s`, `TransS` is `TrS`. -/
theorem TransS_of_ok {s : InLean.CState} {e : Expr} (h : OkS s e = true) :
    TransS s e = some (TrS s e) :=
  toExpr_of_okE _ h

theorem ok_of_TransS {s : InLean.CState} {e : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e)
    (h : TransS s e = some c) : OkS s e = true ∧ TrS s e = c :=
  okE_of_toExpr _ hr h

/-! ## 4. Stability along the run -/

/-- **The table only grows**: every id the earlier state reads, the later
state reads the same. -/
@[expose] def TabLe (s₀ s₁ : InLean.CState) : Prop :=
  FvLe (FVarTable.trans (tableOf s₀)) (FVarTable.trans (tableOf s₁))

@[conleche_grind .] theorem TabLe.refl (s : InLean.CState) : TabLe s s := fun _ _ h => h

theorem TabLe.trans {s₀ s₁ s₂ : InLean.CState} (h₁ : TabLe s₀ s₁) (h₂ : TabLe s₁ s₂) :
    TabLe s₀ s₂ := fun id c h => h₂ id c (h₁ id c h)
grind_pattern [conleche_grind] TabLe.trans => TabLe s₀ s₁, TabLe s₁ s₂

/-- A term with a reading keeps it, and its translation, at a later state. -/
theorem okS_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {e : Expr}
    (he : OkS s₀ e = true) : OkS s₁ e = true := by
  have h₁ := TransS_of_ok he
  have h₂ := toExpr_mono h e _ h₁
  exact (ok_of_TransS (RangeOk_of_OkS he) h₂).1
grind_pattern [conleche_grind] okS_of_tabLe => TabLe s₀ s₁, OkS s₁ e

theorem TrS_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {e : Expr}
    (he : OkS s₀ e = true) : TrS s₁ e = TrS s₀ e := by
  have h₁ := TransS_of_ok he
  have h₂ := toExpr_mono h e _ h₁
  exact (ok_of_TransS (RangeOk_of_OkS he) h₂).2
grind_pattern [conleche_grind] TrS_of_tabLe => TabLe s₀ s₁, TrS s₁ e

/-! ## 5. The spine, lists, options and steps through the translation -/

/-- What the table answers for an id reads as a free variable (or the
`bvar 0` of an untranslatable id): no spine of its own. -/
theorem trans_getD_spine (s : InLean.CState) (id : FVarId) :
    ((FVarTable.trans (tableOf s) id).getD (.bvar 0)).getAppFn =
        (FVarTable.trans (tableOf s) id).getD (.bvar 0) ∧
      ((FVarTable.trans (tableOf s) id).getD (.bvar 0)).getAppArgs = [] := by
  cases h : FVarTable.trans (tableOf s) id with
  | none => exact ⟨rfl, rfl⟩
  | some c =>
    obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c h
    exact ⟨rfl, rfl⟩

section Spine
variable (s : InLean.CState)

/-- The spine's head, read through `mdata` (`getAppFnT`), translates to the
translation's head. -/
@[conleche_grind =] theorem TrS_getAppFnT (e : Expr) :
    TrS s (Expr.getAppFnT e) = (TrS s e).getAppFn := by
  induction e with
  | fvar id => exact (trans_getD_spine s id).1.symm
  | _ => simp_all [Expr.getAppFnT, TrS, trE, ConLeche.Expr.getAppFn]

theorem OkS_getAppFnT {e : Expr} (h : OkS s e = true) : OkS s (Expr.getAppFnT e) = true := by
  induction e <;> simp_all [Expr.getAppFnT, OkS, okE]
grind_pattern [conleche_grind] OkS_getAppFnT => OkS s e, Expr.getAppFnT e

/-- A list of terms, translated. -/
@[expose] def TrSL (l : List Expr) : List ConLeche.Expr := l.map (TrS s)

/-- Every term of a list has a reading. -/
@[expose] def OkSL (l : List Expr) : Bool := l.all (OkS s)

@[conleche_grind =] theorem TrSL_nil : TrSL s [] = [] := rfl
@[conleche_grind =] theorem TrSL_cons (a : Expr) (l : List Expr) :
    TrSL s (a :: l) = TrS s a :: TrSL s l := rfl
@[conleche_grind =] theorem OkSL_nil : OkSL s [] = true := rfl
@[conleche_grind =] theorem OkSL_cons (a : Expr) (l : List Expr) :
    OkSL s (a :: l) = (OkS s a && OkSL s l) := rfl

theorem TrSL_appArgs_go : ∀ (e : Expr) (acc : List Expr),
    TrSL s (appArgs.go e acc) = (TrS s e).getAppArgs ++ TrSL s acc := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro acc
    rw [appArgs.go, ihf (a :: acc)]
    simp [TrSL, TrS, trE, ConLeche.Expr.getAppArgs]
  | mdata _ x ih => intro acc; simp only [appArgs.go, ih]; rfl
  | fvar id => intro acc; simp [appArgs.go, TrS, trE, (trans_getD_spine s id).2]
  | _ => intro acc; simp [appArgs.go, TrS, trE, ConLeche.Expr.getAppArgs]

/-- The spine's arguments, read through `mdata` (`appArgs`), translate to the
translation's arguments. -/
@[conleche_grind =] theorem TrSL_appArgs (e : Expr) :
    TrSL s (appArgs e) = (TrS s e).getAppArgs := by
  have := TrSL_appArgs_go s e []
  simpa [appArgs, TrSL] using this

theorem OkSL_appArgs_go : ∀ {e : Expr} {acc : List Expr}, OkS s e = true → OkSL s acc = true →
    OkSL s (appArgs.go e acc) = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro acc h hacc
    simp only [OkS, okE, Bool.and_eq_true] at h
    exact ihf h.1 (by simp [OkSL_cons, hacc]; exact h.2)
  | mdata _ x ih => intro acc h hacc; exact ih h hacc
  | _ => intro acc _ hacc; simpa [appArgs.go] using hacc

theorem OkSL_appArgs {e : Expr} (h : OkS s e = true) : OkSL s (appArgs e) = true :=
  OkSL_appArgs_go s h rfl
grind_pattern [conleche_grind] OkSL_appArgs => OkS s e, appArgs e

/-- An optional term, translated. -/
@[expose] def TrO : Option Expr → Option ConLeche.Expr
  | none => none
  | some e => some (TrS s e)

/-- An optional term has a reading. -/
@[expose] def OkO : Option Expr → Bool
  | none => true
  | some e => OkS s e

@[conleche_grind =] theorem TrO_none : TrO s none = none := rfl
@[conleche_grind =] theorem TrO_some (e : Expr) : TrO s (some e) = some (TrS s e) := rfl
@[conleche_grind =] theorem OkO_none : OkO s none = true := rfl
@[conleche_grind =] theorem OkO_some (e : Expr) : OkO s (some e) = OkS s e := rfl

/-- A head-normalization step, translated. -/
@[expose] def TrStep : InLean.WhnfStep → ConLeche.WhnfStep
  | .done e => .done (TrS s e)
  | .cont e => .cont (TrS s e)

/-- A step's term has a reading. -/
@[expose] def OkStep : InLean.WhnfStep → Bool
  | .done e | .cont e => OkS s e

@[conleche_grind =] theorem TrStep_done (e : Expr) : TrStep s (.done e) = .done (TrS s e) := rfl
@[conleche_grind =] theorem TrStep_cont (e : Expr) : TrStep s (.cont e) = .cont (TrS s e) := rfl
@[conleche_grind =] theorem OkStep_done (e : Expr) : OkStep s (.done e) = OkS s e := rfl
@[conleche_grind =] theorem OkStep_cont (e : Expr) : OkStep s (.cont e) = OkS s e := rfl

/-- A step's term is closed (`StepWS`'s twin for closedness). -/
@[expose] def StepClosed : ConLeche.WhnfStep → Bool
  | .done e | .cont e => e.looseBVarsBounded 0

@[conleche_grind =] theorem StepClosed_done (e : ConLeche.Expr) :
    StepClosed (.done e) = e.looseBVarsBounded 0 := rfl
@[conleche_grind =] theorem StepClosed_cont (e : ConLeche.Expr) :
    StepClosed (.cont e) = e.looseBVarsBounded 0 := rfl

end Spine

/-! ## 6. Instantiation through the translation (P1's `toExpr_instantiate1`) -/

/-- **One-value instantiation** reads as con-leche's, at a closed value. -/
theorem TrS_inst1 {s : InLean.CState} {b v : Expr} (hb : OkS s b = true) (hv : OkS s v = true)
    (hcl : (TrS s v).looseBVarsBounded 0 = true) :
    OkS s (EO.instantiate1 b v) = true ∧
      TrS s (EO.instantiate1 b v) = (TrS s b).instantiate1 (TrS s v) 0 := by
  have h := toExpr_instantiate1 (FVarTable.trans_fvarsOnly _) (RangeOk_of_OkS hb)
    (RangeOk_of_OkS hv) (TransS_of_ok hb) (TransS_of_ok hv) hcl
  have hv0 : v.looseBVarRange = 0 := by
    rw [looseBVarRange_toExpr (FVarTable.trans_fvarsOnly _) (RangeOk_of_OkS hv) (TransS_of_ok hv)]
    have := ConLeche.Expr.looseBVarsBounded_iff.1 hcl
    omega
  have hr : Expr.RangeOk (EO.instantiate1 b v) := instantiate1_eq b v ▸
    RangeOk_instantiate (RangeOk_of_OkS hb)
      (fun j hj => by simp at hj; subst hj; exact RangeOk_of_OkS hv)
      (fun j hj => by simp at hj; subst hj; exact hv0)
  exact ok_of_TransS hr h

theorem OkS_inst1 {s : InLean.CState} {b v : Expr} (hb : OkS s b = true) (hv : OkS s v = true)
    (hcl : (TrS s v).looseBVarsBounded 0 = true) : OkS s (EO.instantiate1 b v) = true :=
  (TrS_inst1 hb hv hcl).1
grind_pattern [conleche_grind] OkS_inst1 => OkS s b, OkS s v, EO.instantiate1 b v

theorem TrS_inst1_eq {s : InLean.CState} {b v : Expr} (hb : OkS s b = true) (hv : OkS s v = true)
    (hcl : (TrS s v).looseBVarsBounded 0 = true) :
    TrS s (EO.instantiate1 b v) = (TrS s b).instantiate1 (TrS s v) 0 :=
  (TrS_inst1 hb hv hcl).2
grind_pattern [conleche_grind] TrS_inst1_eq => OkS s b, OkS s v, TrS s (EO.instantiate1 b v)

/-! ## 7. Closedness (con-leche's `looseBVarsBounded`, one equation per constructor) -/

section Closed
open ConLeche.Expr

@[conleche_grind =] theorem lbb_app (k : Nat) (f a : ConLeche.Expr) :
    (ConLeche.Expr.app f a).looseBVarsBounded k = (f.looseBVarsBounded k && a.looseBVarsBounded k) := rfl
@[conleche_grind =] theorem lbb_letE (k : Nat) (t v b : ConLeche.Expr) :
    (ConLeche.Expr.letE t v b).looseBVarsBounded k =
      (t.looseBVarsBounded k && v.looseBVarsBounded k && b.looseBVarsBounded (k + 1)) := rfl
@[conleche_grind =] theorem lbb_proj (k : Nat) (n : ConLeche.Name) (i : Nat) (e : ConLeche.Expr) :
    (ConLeche.Expr.proj n i e).looseBVarsBounded k = e.looseBVarsBounded k := rfl

theorem lbb_instantiate1 {a e : ConLeche.Expr} (ha : a.looseBVarsBounded 0 = true)
    (he : e.looseBVarsBounded 1 = true) : (e.instantiate1 a 0).looseBVarsBounded 0 = true :=
  ConLeche.Expr.looseBVarsBounded_instantiate1_gen ha he
grind_pattern [conleche_grind] lbb_instantiate1 => a.looseBVarsBounded 0, e.instantiate1 a 0

theorem lbb_getAppFn {e : ConLeche.Expr} (h : e.looseBVarsBounded 0 = true) :
    e.getAppFn.looseBVarsBounded 0 = true := by
  induction e <;> simp_all [ConLeche.Expr.getAppFn, ConLeche.Expr.looseBVarsBounded]
grind_pattern [conleche_grind] lbb_getAppFn => e.looseBVarsBounded 0, e.getAppFn

/-- An optional term is closed. -/
@[expose] def OptClosed : Option ConLeche.Expr → Bool
  | none => true
  | some e => e.looseBVarsBounded 0

@[conleche_grind =] theorem OptClosed_none : OptClosed none = true := rfl
@[conleche_grind =] theorem OptClosed_some (e : ConLeche.Expr) :
    OptClosed (some e) = e.looseBVarsBounded 0 := rfl

/-- Every term of a list is closed. -/
@[expose] def AllClosed (l : List ConLeche.Expr) : Bool := l.all (·.looseBVarsBounded 0)

theorem allClosed_getAppArgs {e : ConLeche.Expr} (h : e.looseBVarsBounded 0 = true) :
    AllClosed e.getAppArgs = true := by
  induction e <;> simp_all [ConLeche.Expr.getAppArgs, ConLeche.Expr.looseBVarsBounded, AllClosed]
grind_pattern [conleche_grind] allClosed_getAppArgs => e.looseBVarsBounded 0, e.getAppArgs

end Closed

/-! ## 8. The core's own spellings and shapes -/

@[conleche_grind =] theorem inst1I_eq (e v : Expr) : e.inst1I v = EO.instantiate1 e v := rfl

/-- `EO.stripTop` never answers an `mdata` node (the step's `mdata` arm is
unreachable). -/
theorem stripTop_ne_mdata : ∀ {e : Expr} {m : MData} {b : Expr}, EO.stripTop e = .mdata m b → False
  | .mdata _ x, m, b, h => by rw [EO.stripTop] at h; exact stripTop_ne_mdata h
  | .bvar _, _, _, h | .fvar _, _, _, h | .mvar _, _, _, h | .sort _, _, _, h
  | .const .., _, _, h | .app .., _, _, h | .lam .., _, _, h | .forallE .., _, _, h
  | .letE .., _, _, h | .lit _, _, _, h | .proj .., _, _, h => by simp [EO.stripTop] at h
grind_pattern [conleche_grind] stripTop_ne_mdata => EO.stripTop e, Expr.mdata m b

/-- The depth of a free variable's translation (total; meaningful on an id
with a reading). -/
@[expose] def fvIdxS (s : InLean.CState) (id : FVarId) : Nat :=
  match TrS s (.fvar id) with
  | .fvar i _ => i
  | _ => 0

/-- The type annotation of a free variable's translation (total). -/
@[expose] def fvTyS (s : InLean.CState) (id : FVarId) : ConLeche.Expr :=
  match TrS s (.fvar id) with
  | .fvar _ ty => ty
  | _ => .bvar 0

/-- **A free variable with a reading translates to con-leche's free
variable** (the table answers only `.fvar`s, `FVarTable.trans_fvarsOnly`). -/
theorem TrS_fvar {s : InLean.CState} {id : FVarId} (h : OkS s (.fvar id) = true) :
    TrS s (.fvar id) = .fvar (fvIdxS s id) (fvTyS s id) := by
  simp only [OkS, okE, Option.isSome_iff_exists] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨i, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id _ hc
  simp [fvIdxS, fvTyS, TrS, trE, hc]
grind_pattern [conleche_grind] TrS_fvar => OkS s (.fvar id)

end InLeanProof
