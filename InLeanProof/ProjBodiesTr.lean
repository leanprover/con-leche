module

public import InLeanProof.EnvPresI
public import InLeanProof.Range
/- `Expr.hasLooseBVars`/`looseBVarRange` are read through the data field (as in `Ops.lean`). -/
import all Lean.Expr

/-!
# A structure's projection bodies through the translation (task #451, lane P3r)

InLean builds field `i`'s projection body at use (`projBodyAt`): the
constructor type's parameters instantiated by `bvar (nP - k)`, the fields
before `i` by the subject's projections `.proj T j (bvar 0)`, field `i`'s
domain read off.  con-leche's install computes every body once
(`structProjBodies`: `instPisAtLift` at `structProjPs nP`, then
`structProjBodiesGo`).  Both substitute *open* values, lifted under binders;
`toExpr_instantiate` reads instantiation at closed values only.

**Main results.**
* `toExpr_instantiate1L`: InLean's `instantiate1` at an open value in range
  reads as con-leche's `instantiate1Lift`.
* `projBodyAt_tr`: field `i`'s body as InLean builds it reads as con-leche's
  `structProjBodies`' entry `i`, given that every intermediate term of
  `projBodyAt` is in range (`projStepsOk`).
* `hasPis_iff_structProjBodies`: InLean's table test (`hasPis (nP + nF)`) is
  con-leche's `structProjBodies` succeeding.

**`projStepsOk` is checked by InLean (`InLean.projStepsAllOk`).**  The test
`FEnv.projBodiesInRange` (P3c) reads the *final* bodies; an intermediate
term can be out of range while the final body is not: a parameter reference
at depth `d` in a later field's domain becomes `bvar (nP - k + d)` after the
parameter's step and is lowered again by each field step, so with `i ≥ 1`
fields before it, a reference with `d + 1 = maxRange` past the parameter
binder is at `maxRange` after the step and at `maxRange - i` at the end.
Lean's `Expr.mkData` panics there (C aborts), and the proof cannot say what
the cached range of such a node is, so an instantiation step after it is not
read.  `checkInductiveC` runs `projStepsOk` at each structure's last field
(`projStepsOk_mono` gives the earlier ones) beside `projBodiesInRange`.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Instantiation at an open value -/

variable {fv : FVarId → Option ConLeche.Expr}

theorem inst1L_cut (hfv : FVarsOnly fv) (v : Expr) (cv : ConLeche.Expr)
    {x : Expr} {k : Nat} {c : ConLeche.Expr} (hr : Expr.RangeOk x)
    (hc : x.looseBVarRange ≤ k) (h : toExpr fv x = some c) :
    toExpr fv (mapSpec (instF #[v]) x k) = some (c.instantiate1Lift cv k) := by
  have hf : instF #[v] x k = some x := by simp [instF, hc]
  rw [mapSpec_eq_of_some hf, h, ConLeche.Expr.instantiate1Lift_eq_self
    (ConLeche.Expr.looseBVarsBounded_mono (by rw [Expr.looseBVarRange_eq hr] at hc; exact hc)
      (toExpr_bounded hfv x c h))]

/-- InLean's instantiation walk at one open value reads as con-leche's
capture-avoiding substitution (`instantiate1Lift`), on a term in range. -/
theorem toExpr_mapSpec_inst1L (hfv : FVarsOnly fv) {v : Expr} {cv : ConLeche.Expr}
    (hv : toExpr fv v = some cv) (hvr : Expr.RangeOk v) :
    ∀ (e : Expr), Expr.RangeOk e → ∀ (k : Nat) (c : ConLeche.Expr), toExpr fv e = some c →
      toExpr fv (mapSpec (instF #[v]) e k) = some (c.instantiate1Lift cv k) := by
  intro e
  induction e with
  | bvar i =>
    intro hr k c h
    by_cases hcut : (Expr.bvar i).looseBVarRange ≤ k
    · exact inst1L_cut hfv v cv hr hcut h
    · simp only [toExpr, Option.some.injEq] at h
      subst h
      have hcut' := hcut
      rw [Expr.looseBVarRange_eq hr] at hcut'
      have hik : ¬ i < k := by simp only [rangeS] at hcut'; omega
      by_cases hin : i - k < 1
      · have hieq : i = k := by omega
        have hf : instF #[v] (.bvar i) k = some (EO.liftLooseBVars v 0 k) := by
          simp [instF, hcut, hik, hin]
        rw [mapSpec_eq_of_some hf, toExpr_liftLooseBVars hfv hvr hv]
        simp [ConLeche.Expr.instantiate1Lift, hieq]
      · have hf : instF #[v] (.bvar i) k = some (.bvar (i - 1)) := by
          simp [instF, hcut, hik, hin]
        rw [mapSpec_eq_of_some hf]
        simp only [toExpr, ConLeche.Expr.instantiate1Lift]
        rw [ite_eq_right_iff.2 (by omega), ite_eq_left_iff.2 (by omega)]
  | fvar id =>
    intro hr k c h
    exact inst1L_cut hfv v cv hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | mvar m => intro _ k c h; simp [toExpr] at h
  | sort u =>
    intro hr k c h
    exact inst1L_cut hfv v cv hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | const n us =>
    intro hr k c h
    exact inst1L_cut hfv v cv hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | lit l =>
    intro hr k c h
    exact inst1L_cut hfv v cv hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | app g a ihg iha =>
    intro hr k c h
    by_cases hcut : (Expr.app g a).looseBVarRange ≤ k
    · exact inst1L_cut hfv v cv hr hcut h
    · have hf : instF #[v] (.app g a) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cg, hg, ca, ha, rfl⟩ := h
      simp [mapSpec, hf, toExpr, ihg hr.1 k cg hg, iha hr.2 k ca ha,
        ConLeche.Expr.instantiate1Lift]
  | lam n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.lam n t b bi).looseBVarRange ≤ k
    · exact inst1L_cut hfv v cv hr hcut h
    · have hf : instF #[v] (.lam n t b bi) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb,
        ConLeche.Expr.instantiate1Lift]
  | forallE n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.forallE n t b bi).looseBVarRange ≤ k
    · exact inst1L_cut hfv v cv hr hcut h
    · have hf : instF #[v] (.forallE n t b bi) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb,
        ConLeche.Expr.instantiate1Lift]
  | letE n t w b nd iht ihw ihb =>
    intro hr k c h
    by_cases hcut : (Expr.letE n t w b nd).looseBVarRange ≤ k
    · exact inst1L_cut hfv v cv hr hcut h
    · have hf : instF #[v] (.letE n t w b nd) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cw, hw, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihw hr.2.1 k cw hw, ihb hr.2.2 (k + 1) cb hb,
        ConLeche.Expr.instantiate1Lift]
  | mdata m x ih =>
    intro hr k c h
    by_cases hcut : (Expr.mdata m x).looseBVarRange ≤ k
    · exact inst1L_cut hfv v cv hr hcut h
    · have hf : instF #[v] (.mdata m x) k = none := by simp [instF, hcut]
      simp only [toExpr] at h
      simp [mapSpec, hf, toExpr, ih hr k c h]
  | proj sn i x ih =>
    intro hr k c h
    by_cases hcut : (Expr.proj sn i x).looseBVarRange ≤ k
    · exact inst1L_cut hfv v cv hr hcut h
    · have hf : instF #[v] (.proj sn i x) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.map_eq_some_iff] at h
      obtain ⟨cx, hx, rfl⟩ := h
      simp [mapSpec, hf, toExpr, ih hr k cx hx, ConLeche.Expr.instantiate1Lift]

/-- **InLean's `instantiate1` at an open value** (in range) reads as
con-leche's `instantiate1Lift`, on a term in range. -/
theorem toExpr_instantiate1L (hfv : FVarsOnly fv) {e v : Expr} {c cv : ConLeche.Expr}
    (hr : Expr.RangeOk e) (hvr : Expr.RangeOk v) (h : toExpr fv e = some c)
    (hv : toExpr fv v = some cv) :
    toExpr fv (EO.instantiate1 e v) = some (c.instantiate1Lift cv 0) := by
  rw [instantiate1_eq, instantiate_eq]
  split
  · rename_i hn
    have hl : e.looseBVarRange = 0 := by
      have : (!e.hasLooseBVars) = true := by simpa using hn
      simpa [Expr.hasLooseBVars] using this
    rw [Expr.looseBVarRange_eq hr] at hl
    have hb := toExpr_bounded hfv e c h
    rw [hl] at hb
    rw [ConLeche.Expr.instantiate1Lift_eq_self hb]; exact h
  · exact toExpr_mapSpec_inst1L hfv hv hvr e hr 0 c h

/-! ## The top of a term through `mdata` -/

theorem RangeOk_stripTop : ∀ {e : Expr}, Expr.RangeOk e → Expr.RangeOk (EO.stripTop e)
  | .mdata _ x, h => RangeOk_stripTop (e := x) h
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .const _ _, h | .app _ _, h
  | .lam _ _ _ _, h | .forallE _ _ _ _, h | .letE _ _ _ _ _, h | .lit _, h | .proj _ _ _, h => h

/-- A term reading as a `∀` is one below its `mdata`. -/
theorem stripTop_forallE (hfv : FVarsOnly fv) : ∀ {e : Expr} {a b : ConLeche.Expr},
    toExpr fv e = some (.forallE a b) →
    ∃ n t body bi, EO.stripTop e = .forallE n t body bi ∧ toExpr fv t = some a ∧
      toExpr fv body = some b
  | .mdata _ x, _, _, h => stripTop_forallE hfv (e := x) h
  | .forallE n t body bi, _, _, h => by
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, ConLeche.Expr.forallE.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl, rfl⟩ := h
    exact ⟨n, t, body, bi, rfl, ht, hb⟩
  | .fvar id, _, _, h => by
    obtain ⟨i, ty, he⟩ := hfv id _ h
    cases he
  | .bvar _, _, _, h | .mvar _, _, _, h | .sort _, _, _, h | .const _ _, _, _, h
  | .app _ _, _, _, h | .lam _ _ _ _, _, _, h | .letE _ _ _ _ _, _, _, h | .lit _, _, _, h
  | .proj _ _ _, _, _, h => by
    simp [toExpr, Option.bind_eq_some_iff] at h

/-! ## The intermediate terms' range -/

/-- The field steps towards field `i` are a prefix of those towards a later
field. -/
theorem fieldsOkB_mono (T : Name) (i : Nat) : ∀ (m j : Nat) (e : Expr) (i' : Nat),
    i - j = m → i' ≤ i → fieldsOkB T i j e = true → fieldsOkB T i' j e = true := by
  intro m
  induction m with
  | zero =>
    intro j e i' hm hi h
    rw [fieldsOkB] at h ⊢
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    split
    · simp only [show ¬ j < i' by omega, ↓reduceIte]
    · rfl
  | succ m ih =>
    intro j e i' hm hi h
    rw [fieldsOkB] at h ⊢
    simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    split
    · next b _ hst =>
      rw [hst] at h2
      simp only [show j < i by omega, ↓reduceIte] at h2
      split
      · exact ih (j + 1) _ i' (by omega) hi h2
      · rfl
    · rfl

/-- **`projStepsOk` at a later field gives it at an earlier one.** -/
theorem projStepsOk_mono {T : Name} {nP i i' : Nat} {cty : Expr} (hi : i' ≤ i)
    (h : projStepsOk T nP i cty = true) : projStepsOk T nP i' cty = true := by
  unfold projStepsOk at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨-, h2⟩ := h
  split
  · next r hr =>
    rw [hr] at h2
    exact fieldsOkB_mono T i _ 0 r i' rfl hi h2
  · rfl

theorem structProjPs_drop {nP k : Nat} (hk : k < nP) :
    (ConLeche.structProjPs nP).drop k =
      .bvar (nP - k) :: (ConLeche.structProjPs nP).drop (k + 1) := by
  unfold ConLeche.structProjPs
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  simp

theorem structProjPs_drop_self (nP : Nat) : (ConLeche.structProjPs nP).drop nP = [] := by
  simp [ConLeche.structProjPs]

/-- **The parameter loop** reads as con-leche's `instPisAtLift` at the remaining
parameter variables. -/
theorem params_tr (nP : Nat) (hnP : nP < maxRange) : ∀ (m k : Nat) (e : Expr) (ce : ConLeche.Expr),
    nP - k = m → k ≤ nP → paramsOkB nP k e = true → toExprC e = some ce →
    ∀ r, ConLeche.Expr.instPisAtLift ((ConLeche.structProjPs nP).drop k) ce = some r →
      ∃ r', projBodyAt.params nP k e = some r' ∧ toExprC r' = some r ∧ Expr.RangeOk r' := by
  intro m
  induction m with
  | zero =>
    intro k e ce hm hk hok hc r hr
    have hkn : k = nP := by omega
    subst hkn
    rw [structProjPs_drop_self] at hr
    simp only [ConLeche.Expr.instPisAtLift, Option.some.injEq] at hr
    subst hr
    rw [paramsOkB] at hok
    refine ⟨e, ?_, hc, (RangeOk_of_inRange (Bool.and_eq_true_iff.1 hok).1).1⟩
    rw [projBodyAt.params]; simp
  | succ m ih =>
    intro k e ce hm hk hok hc r hr
    have hkn : k < nP := by omega
    rw [structProjPs_drop hkn] at hr
    rw [paramsOkB] at hok
    simp only [hkn, ↓reduceIte, Bool.and_eq_true] at hok
    obtain ⟨hin, hrest⟩ := hok
    have her := (RangeOk_of_inRange hin).1
    cases ce with
    | forallE dom body =>
      simp only [ConLeche.Expr.instPisAtLift] at hr
      obtain ⟨n, t, b, bi, hst, ht, hb⟩ := stripTop_forallE fvarsOnly_none hc
      have hbr : Expr.RangeOk b := by
        have := RangeOk_stripTop her; rw [hst] at this; exact this.2
      rw [hst] at hrest
      simp only at hrest
      have hvr : Expr.RangeOk (Expr.bvar (nP - k)) := by
        simp only [Expr.RangeOk]; omega
      have hi := toExpr_instantiate1L fvarsOnly_none hbr hvr hb (cv := .bvar (nP - k)) rfl
      rw [← mkBvar_eq] at hi
      obtain ⟨r', h1, h2, h3⟩ := ih (k + 1) _ _ (by omega) (by omega) hrest hi r hr
      refine ⟨r', ?_, h2, h3⟩
      rw [projBodyAt.params]; simp only [hkn, ↓reduceIte, hst]; exact h1
    | _ => simp [ConLeche.Expr.instPisAtLift] at hr

/-- **The field loop** reads as `structProjBodiesGo`: field `i`'s domain is the
list's entry `i - j`. -/
theorem fields_tr (T : Name) (i : Nat) : ∀ (m j : Nat) (e : Expr) (ce : ConLeche.Expr)
    (n : Nat) (l : List ConLeche.Expr),
    i - j = m → j ≤ i → fieldsOkB T i j e = true → toExprC e = some ce →
    ConLeche.structProjBodiesGo (toName T) n j ce = some l → i - j < n →
      ∃ b, projBodyAt.fields T i j e = some b ∧ toExprC b = some (l.getD (i - j) default) := by
  intro m
  induction m with
  | zero =>
    intro j e ce n l hm hj hok hc hl hn
    have hji : j = i := by omega
    subst hji
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    cases ce with
    | forallE dom body =>
      simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at hl
      obtain ⟨l', -, rfl⟩ := hl
      obtain ⟨nm, t, b, bi, hst, ht, -⟩ := stripTop_forallE fvarsOnly_none hc
      refine ⟨t, ?_, by simpa [toExprC] using ht⟩
      rw [projBodyAt.fields]; simp [hst]
    | _ => simp [ConLeche.structProjBodiesGo] at hl
  | succ m ih =>
    intro j e ce n l hm hj hok hc hl hn
    have hji : j < i := by omega
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [fieldsOkB] at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hin, hrest⟩ := hok
    have her := (RangeOk_of_inRange hin).1
    cases ce with
    | forallE dom body =>
      simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at hl
      obtain ⟨l', hl', rfl⟩ := hl
      obtain ⟨nm, t, b, bi, hst, -, hb⟩ := stripTop_forallE fvarsOnly_none hc
      have hbr : Expr.RangeOk b := by
        have := RangeOk_stripTop her; rw [hst] at this; exact this.2
      rw [hst] at hrest
      simp only [hji, ↓reduceIte] at hrest
      have hvr : Expr.RangeOk (Expr.proj T j (.bvar 0)) := by
        simp only [Expr.RangeOk]; decide
      have hi := toExpr_instantiate1L fvarsOnly_none hbr hvr hb
        (cv := ConLeche.structProjArgP (toName T) j) rfl
      obtain ⟨b', h1, h2⟩ := ih (j + 1) _ _ n' l' (by omega) (by omega) hrest hi hl' (by omega)
      refine ⟨b', ?_, ?_⟩
      · rw [projBodyAt.fields]; simp only [hst, hji, ↓reduceIte]; exact h1
      · rw [h2]
        have : i - j = (i - (j + 1)) + 1 := by omega
        rw [this]; rfl
    | _ => simp [ConLeche.structProjBodiesGo] at hl

/-- **Field `i`'s body, as InLean builds it, is con-leche's**, given every
intermediate term in range (`projStepsOk`). -/
theorem projBodyAt_tr {T : Name} {nP nF i : Nat} {cty : Expr} {ccty : ConLeche.Expr}
    {bodies : Array ConLeche.Expr} (hok : projStepsOk T nP i cty = true)
    (hc : toExprC cty = some ccty)
    (hs : ConLeche.structProjBodies (toName T) nP nF ccty = some bodies) (hi : i < nF) :
    ∃ b, projBodyAt T nP i cty = some b ∧ fvarS b = false ∧
      toExprC b = some (bodies.getD i default) := by
  unfold projStepsOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hnP, hpar⟩, hfld⟩ := hok
  replace hnP : nP < maxRange := by
    have : EO.maxBVarIdx = 1048574 := rfl
    have : maxRange = 1048575 := rfl
    omega
  unfold ConLeche.structProjBodies at hs
  cases hr : ConLeche.Expr.instPisAtLift (ConLeche.structProjPs nP) ccty with
  | none => rw [hr] at hs; cases hs
  | some r =>
    rw [hr] at hs
    simp only [Option.map_eq_some_iff] at hs
    obtain ⟨l, hl, rfl⟩ := hs
    obtain ⟨r', h1, h2, -⟩ := params_tr nP hnP _ 0 cty ccty rfl (Nat.zero_le _) hpar hc r
      (by simpa using hr)
    rw [h1] at hfld
    simp only at hfld
    obtain ⟨b, hb1, hb2⟩ := fields_tr T i _ 0 r' r nF l rfl (Nat.zero_le _) hfld h2 hl (by omega)
    refine ⟨b, ?_, fvarS_of_toExprC hb2, ?_⟩
    · show (projBodyAt.params nP 0 cty).bind (projBodyAt.fields T i 0) = some b
      rw [h1]; exact hb1
    · rw [hb2]; simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## The table test: enough binders -/

/-- con-leche's term binds at least `n` syntactic `∀`s (`hasPis`' twin). -/
@[expose] def cPis : Nat → ConLeche.Expr → Bool
  | 0, _ => true
  | n + 1, .forallE _ b => cPis n b
  | _ + 1, _ => false

theorem hasPis_tr : ∀ (n : Nat) {e : Expr} {ce : ConLeche.Expr}, toExprC e = some ce →
    hasPis n e = cPis n ce
  | 0, _, _, _ => by simp [hasPis, cPis]
  | n + 1, e, ce, h => by
    cases e with
    | mdata m x => exact hasPis_tr (n + 1) (e := x) h
    | forallE nm t b bi =>
      simp only [toExprC, toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, -, cb, hb, rfl⟩ := h
      simp only [hasPis, cPis]
      exact hasPis_tr n hb
    | fvar _ => simp [toExprC, toExpr] at h
    | bvar _ | mvar _ | sort _ | const _ _ | app _ _ | lam _ _ _ _ | letE _ _ _ _ _ | lit _
    | proj _ _ _ =>
      simp only [toExprC, toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Option.map_eq_some_iff] at h
      first
        | (obtain ⟨_, _, rfl⟩ := h; rfl)
        | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl)
        | (obtain ⟨_, _, _, _, _, _, rfl⟩ := h; rfl)
        | (subst h; rfl)
        | (cases h)

/-- A value whose lifts are no `∀` (a variable, a projection). -/
@[expose] def NoPiLift (v : ConLeche.Expr) : Prop :=
  ∀ k c a b, ConLeche.Expr.liftLooseBVars k c v ≠ .forallE a b

theorem noPiLift_bvar (m : Nat) : NoPiLift (.bvar m) := by
  intro k c a b h; simp only [ConLeche.Expr.liftLooseBVars] at h; split at h <;> cases h

theorem noPiLift_proj (S : ConLeche.Name) (j : Nat) (x : ConLeche.Expr) : NoPiLift (.proj S j x) := by
  intro k c a b h; simp [ConLeche.Expr.liftLooseBVars] at h

theorem cPis_instantiate1Lift {v : ConLeche.Expr} (hv : NoPiLift v) :
    ∀ (n : Nat) (e : ConLeche.Expr) (d : Nat), cPis n (e.instantiate1Lift v d) = cPis n e
  | 0, _, _ => by simp [cPis]
  | n + 1, e, d => by
    cases e with
    | forallE a b =>
      simp only [ConLeche.Expr.instantiate1Lift, cPis]
      exact cPis_instantiate1Lift hv n b (d + 1)
    | bvar i =>
      simp only [ConLeche.Expr.instantiate1Lift]
      split
      · cases h : ConLeche.Expr.liftLooseBVars d 0 v with
        | forallE a b => exact absurd h (hv d 0 a b)
        | _ => rfl
      · split <;> rfl
    | _ => simp [ConLeche.Expr.instantiate1Lift, cPis]

theorem instPisAtLift_cPis : ∀ (as : List ConLeche.Expr), (∀ a ∈ as, NoPiLift a) →
    ∀ (ce : ConLeche.Expr) (n : Nat),
      match ConLeche.Expr.instPisAtLift as ce with
      | some r => cPis n r = cPis (as.length + n) ce
      | none => cPis (as.length + n) ce = false
  | [], _, ce, n => by simp [ConLeche.Expr.instPisAtLift]
  | a :: as, ha, ce, n => by
    cases ce with
    | forallE x body =>
      simp only [ConLeche.Expr.instPisAtLift, List.length_cons]
      have ih := instPisAtLift_cPis as (fun a h => ha a (List.mem_cons_of_mem _ h))
        (body.instantiate1Lift a) n
      rw [show as.length + 1 + n = (as.length + n) + 1 by omega]
      simp only [cPis]
      rw [cPis_instantiate1Lift (ha a List.mem_cons_self)] at ih
      exact ih
    | _ =>
      simp only [ConLeche.Expr.instPisAtLift, List.length_cons]
      rw [show as.length + 1 + n = (as.length + n) + 1 by omega]
      rfl

theorem go_isSome (S : ConLeche.Name) : ∀ (m j : Nat) (r : ConLeche.Expr),
    (ConLeche.structProjBodiesGo S m j r).isSome = cPis m r
  | 0, _, _ => by simp [ConLeche.structProjBodiesGo, cPis]
  | m + 1, j, r => by
    cases r with
    | forallE x body =>
      simp only [ConLeche.structProjBodiesGo, Option.isSome_map, cPis]
      rw [go_isSome S m (j + 1)]
      exact cPis_instantiate1Lift (noPiLift_proj _ _ _) m body 0
    | _ => simp [ConLeche.structProjBodiesGo, cPis]

theorem structProjPs_noPi (nP : Nat) : ∀ a ∈ ConLeche.structProjPs nP, NoPiLift a := by
  intro a ha
  simp only [ConLeche.structProjPs, List.mem_map] at ha
  obtain ⟨_, _, rfl⟩ := ha
  exact noPiLift_bvar _

/-- **InLean's table test is con-leche's bodies succeeding**: the constructor
type binds the parameters and the fields. -/
theorem hasPis_iff_structProjBodies {S : ConLeche.Name} {nP nF : Nat} {cty : Expr}
    {ccty : ConLeche.Expr} (hc : toExprC cty = some ccty) :
    hasPis (nP + nF) cty = (ConLeche.structProjBodies S nP nF ccty).isSome := by
  rw [hasPis_tr _ hc]
  have h := instPisAtLift_cPis (ConLeche.structProjPs nP) (structProjPs_noPi nP) ccty nF
  unfold ConLeche.structProjBodies
  have hlen : (ConLeche.structProjPs nP).length = nP := by simp [ConLeche.structProjPs]
  rw [hlen] at h
  cases hr : ConLeche.Expr.instPisAtLift (ConLeche.structProjPs nP) ccty with
  | none => rw [hr] at h; simp only at h; rw [h]; rfl
  | some r =>
    rw [hr] at h; simp only at h
    simp only [Option.isSome_map]
    rw [go_isSome, h]

end InLeanProof
