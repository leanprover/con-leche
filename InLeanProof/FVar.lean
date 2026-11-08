module

public import InLeanProof.Sim

/-!
# Free variables and the checker's equality (task #451, lane P1: O2, O3)

* **O2**: InLean's checker equality `Expr.clEq` is, on terms in range,
  equality after `erase` (`clEq_iff_erase`); `toExpr` reads through `erase` (`toExpr_erase`), and conversely two terms
  that translate equal under an injective id translation are equal after
  `erase` (`erase_eq_of_toExpr`, through the left inverse `fromExpr`).  So,
  at a state whose table is in order, `clEq a b` holds on terms in range
  exactly when `a` and `b` translate equal (`clEq_iff_TransS`).
* **O3**: the table's invariant `FVTableOK` makes the id translation
  injective (`trans_inj`), and `mkFVarM` keeps the invariant, answers the free
  variable con-leche's `.fvar d ty` is, and only extends the translation
  (`mkFVarM_ok`).

Numbers are global, the classes per depth (`InLean/StateC.lean`): a number
translates only at the depth it was interned at (`FVarTable.live`).
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Left inverses of the translations -/

/-- Levels back. -/
def fromLevel : ConLeche.Level → Level
  | .zero => .zero
  | .succ u => .succ (fromLevel u)
  | .max u v => .max (fromLevel u) (fromLevel v)
  | .imax u v => .imax (fromLevel u) (fromLevel v)
  | .param n => .param (fromName n)

theorem fromLevel_of_toLevel : ∀ {a : Level} {c : ConLeche.Level},
    toLevel a = some c → fromLevel c = a := by
  intro a
  induction a with
  | zero => intro c h; simp only [toLevel, Option.some.injEq] at h; subst h; rfl
  | param n => intro c h; simp only [toLevel, Option.some.injEq] at h; subst h
               simp [fromLevel, fromName_toName]
  | mvar m => intro c h; simp [toLevel] at h
  | succ u ih =>
    intro c h
    simp only [toLevel, Option.map_eq_some_iff] at h
    obtain ⟨cu, hu, rfl⟩ := h
    simp [fromLevel, ih hu]
  | max u v ihu ihv =>
    intro c h
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu, hu, cv, hv, rfl⟩ := h
    simp [fromLevel, ihu hu, ihv hv]
  | imax u v ihu ihv =>
    intro c h
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu, hu, cv, hv, rfl⟩ := h
    simp [fromLevel, ihu hu, ihv hv]

theorem fromLevels_of_toLevels : ∀ {a : List Level} {c : List ConLeche.Level},
    toLevels a = some c → c.map fromLevel = a
  | [], c, h => by simp only [toLevels, Option.some.injEq] at h; subst h; rfl
  | u :: us, c, h => by
    simp only [toLevels, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu, hu, cus, hus, rfl⟩ := h
    simp [fromLevel_of_toLevel hu, fromLevels_of_toLevels hus]

/-- Literals back. -/
def fromLit : ConLeche.Literal → Literal
  | .natVal n => .natVal n
  | .strVal s => .strVal s

theorem fromLit_toLit : ∀ l : Literal, fromLit (toLit l) = l
  | .natVal _ => rfl
  | .strVal _ => rfl

/-- Terms back, after `erase` (anonymous binders, default infos, `nonDep`
false, no `mdata`), free variables through `inv`. -/
def fromExpr (inv : ConLeche.Expr → FVarId) : ConLeche.Expr → Expr
  | .bvar i => .bvar i
  | e@(.fvar ..) => .fvar (inv e)
  | .sort u => .sort (fromLevel u)
  | .const n us => .const (fromName n) (us.map fromLevel)
  | .app f a => .app (fromExpr inv f) (fromExpr inv a)
  | .lam t b => .lam .anonymous (fromExpr inv t) (fromExpr inv b) .default
  | .forallE t b => .forallE .anonymous (fromExpr inv t) (fromExpr inv b) .default
  | .letE t v b => .letE .anonymous (fromExpr inv t) (fromExpr inv v) (fromExpr inv b) false
  | .lit l => .lit (fromLit l)
  | .proj s i e => .proj (fromName s) i (fromExpr inv e)

/-! ## O2: translating equal is being equal after `erase` -/

/-- An id translation that tells ids apart. -/
@[expose] def FvInj (fv : FVarId → Option ConLeche.Expr) : Prop :=
  ∀ i j c, fv i = some c → fv j = some c → i = j

open Classical in
/-- The inverse of an id translation on its image. -/
noncomputable def fvInv (fv : FVarId → Option ConLeche.Expr) (c : ConLeche.Expr) : FVarId :=
  if h : ∃ id, fv id = some c then Classical.choose h else ⟨.anonymous⟩

theorem fvInv_eq {fv : FVarId → Option ConLeche.Expr} (hinj : FvInj fv) {id : FVarId}
    {c : ConLeche.Expr} (h : fv id = some c) : fvInv fv c = id := by
  have hex : ∃ id, fv id = some c := ⟨id, h⟩
  unfold fvInv
  simp only [hex, ↓reduceDIte]
  exact hinj _ _ _ (Classical.choose_spec hex) h

/-- **A translatable term is, after `erase`, read back from its translation.** -/
theorem erase_eq_fromExpr {fv : FVarId → Option ConLeche.Expr} (hfo : FVarsOnly fv)
    (hinj : FvInj fv) :
    ∀ (a : Expr) (c : ConLeche.Expr), toExpr fv a = some c → erase a = fromExpr (fvInv fv) c := by
  intro a
  induction a with
  | bvar i => intro c h; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | fvar id =>
    intro c h
    obtain ⟨i, ty, rfl⟩ := hfo id _ h
    simp only [toExpr] at h
    simp [erase, fromExpr, fvInv_eq hinj h]
  | mvar m => intro c h; simp [toExpr] at h
  | sort u =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cu, hu, rfl⟩ := h
    simp [erase, fromExpr, fromLevel_of_toLevel hu]
  | const n us =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cus, hus, rfl⟩ := h
    simp [erase, fromExpr, fromLevels_of_toLevels hus, fromName_toName]
  | lit l => intro c h; simp only [toExpr, Option.some.injEq] at h; subst h
             simp [erase, fromExpr, fromLit_toLit]
  | app g x ihg ihx =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, cx, hx, rfl⟩ := h
    simp [erase, fromExpr, ihg cg hg, ihx cx hx]
  | lam n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp [erase, fromExpr, iht ct ht, ihb cb hb]
  | forallE n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp [erase, fromExpr, iht ct ht, ihb cb hb]
  | letE n t v b nd iht ihv ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    simp [erase, fromExpr, iht ct ht, ihv cv hv, ihb cb hb]
  | mdata m x ih => intro c h; simp only [toExpr] at h; rw [erase_mdata]; exact ih c h
  | proj s i x ih =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    simp [erase, fromExpr, ih cx hx, fromName_toName]

/-- **O2**: two terms translating equal are equal after `erase`. -/
theorem erase_eq_of_toExpr {fv : FVarId → Option ConLeche.Expr} (hfo : FVarsOnly fv)
    (hinj : FvInj fv) {a b : Expr} {c : ConLeche.Expr}
    (ha : toExpr fv a = some c) (hb : toExpr fv b = some c) : erase a = erase b := by
  rw [erase_eq_fromExpr hfo hinj a c ha, erase_eq_fromExpr hfo hinj b c hb]

/-- `Expr.clEq` is equality of translations (under an injective id
translation, on translatable terms in range). -/
theorem clEq_of_toExpr {fv : FVarId → Option ConLeche.Expr} (hfo : FVarsOnly fv)
    (hinj : FvInj fv) {a b : Expr} {c : ConLeche.Expr} (hra : Expr.RangeOk a)
    (hrb : Expr.RangeOk b) (ha : toExpr fv a = some c) (hb : toExpr fv b = some c) :
    Expr.clEq a b = true :=
  (clEq_iff_erase hra hrb).2 (erase_eq_of_toExpr hfo hinj ha hb)

/-! ## Translations along a larger id translation -/

/-- `fv₁` answers less than `fv₂`. -/
@[expose] def FvLe (fv₁ fv₂ : FVarId → Option ConLeche.Expr) : Prop :=
  ∀ id c, fv₁ id = some c → fv₂ id = some c

theorem toExpr_mono {fv₁ fv₂ : FVarId → Option ConLeche.Expr} (hle : FvLe fv₁ fv₂) :
    ∀ (e : Expr) (c : ConLeche.Expr), toExpr fv₁ e = some c → toExpr fv₂ e = some c := by
  intro e
  induction e with
  | fvar id => intro c h; exact hle id c h
  | app g x ihg ihx =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨cg, hg, cx, hx, rfl⟩ := h
    exact ⟨cg, ihg cg hg, cx, ihx cx hx, rfl⟩
  | lam n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    exact ⟨ct, iht ct ht, cb, ihb cb hb, rfl⟩
  | forallE n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    exact ⟨ct, iht ct ht, cb, ihb cb hb, rfl⟩
  | letE n t v b nd iht ihv ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    exact ⟨ct, iht ct ht, cv, ihv cv hv, cb, ihb cb hb, rfl⟩
  | mdata m x ih => intro c h; simp only [toExpr] at h ⊢; exact ih c h
  | proj s i x ih =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h ⊢
    obtain ⟨cx, hx, rfl⟩ := h
    exact ⟨cx, ih cx hx, rfl⟩
  | bvar | mvar | sort | const | lit => intro c h; exact h

/-! ## `EO.clHash` is a function of the term after `erase` -/

/-- The plain structural hash `EO.clHashGo` computes. -/
def clHashS : Expr → UInt64
  | .mdata _ x => clHashS x
  | .app f a => mixHash 5 (mixHash (clHashS f) (clHashS a))
  | .lam _ t b _ => mixHash 6 (mixHash (clHashS t) (clHashS b))
  | .forallE _ t b _ => mixHash 7 (mixHash (clHashS t) (clHashS b))
  | .letE _ t v b _ => mixHash 8 (mixHash (clHashS t) (mixHash (clHashS v) (clHashS b)))
  | .proj s i x => mixHash 11 (mixHash (hash s) (mixHash (hash i) (clHashS x)))
  | e => hash e

theorem clHashS_erase : ∀ e : Expr, clHashS (erase e) = clHashS e := by
  intro e
  induction e <;> simp_all [erase, clHashS]

section clHash
/- The hash walk's memo compares nodes exactly, as `InLean/ExprOps.lean`
elaborates it. -/
attribute [local instance 2000] instBEqExprExact
local instance : LawfulBEq Expr := instBEqExprExact_lawful
local instance : LawfulHashable Expr := ⟨fun _ _ h => by rw [eq_of_beq h]⟩

/-- The hash memo's invariant: every entry is `clHashS`'s. -/
def HashMemoInv (memo : Std.HashMap Expr UInt64) : Prop :=
  ∀ e h, memo[e]? = some h → h = clHashS e

theorem HashMemoInv.insert {memo : Std.HashMap Expr UInt64} (hm : HashMemoInv memo) {e : Expr}
    {h : UInt64} (he : h = clHashS e) : HashMemoInv (memo.insert e h) := by
  intro e' h' hl
  rw [Std.HashMap.getElem?_insert] at hl
  split at hl
  · rename_i heq
    have : e = e' := eq_of_beq heq
    subst this
    simp only [Option.some.injEq] at hl
    exact hl ▸ he
  · exact hm e' h' hl

theorem clHashGo_spec : ∀ (e : Expr) (memo : Std.HashMap Expr UInt64), HashMemoInv memo →
    (EO.clHashGo e memo).1 = clHashS e ∧ HashMemoInv (EO.clHashGo e memo).2 := by
  intro e
  induction e with
  | mdata m x ih => intro memo hm; rw [EO.clHashGo]; exact ih memo hm
  | app f a ihf iha =>
    intro memo hm
    rw [EO.clHashGo, EO.withMemoH]
    cases hl : memo[Expr.app f a]? with
    | some h => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := ihf memo hm
      obtain ⟨h3, h4⟩ := iha _ h2
      have hv : mixHash 5 (mixHash (EO.clHashGo f memo).1
          (EO.clHashGo a (EO.clHashGo f memo).2).1) = clHashS (.app f a) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | lam n t b bi iht ihb =>
    intro memo hm
    rw [EO.clHashGo, EO.withMemoH]
    cases hl : memo[Expr.lam n t b bi]? with
    | some h => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : mixHash 6 (mixHash (EO.clHashGo t memo).1
          (EO.clHashGo b (EO.clHashGo t memo).2).1) = clHashS (.lam n t b bi) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | forallE n t b bi iht ihb =>
    intro memo hm
    rw [EO.clHashGo, EO.withMemoH]
    cases hl : memo[Expr.forallE n t b bi]? with
    | some h => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : mixHash 7 (mixHash (EO.clHashGo t memo).1
          (EO.clHashGo b (EO.clHashGo t memo).2).1) = clHashS (.forallE n t b bi) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | letE n t v b nd iht ihv ihb =>
    intro memo hm
    rw [EO.clHashGo, EO.withMemoH]
    cases hl : memo[Expr.letE n t v b nd]? with
    | some h => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      have hv : mixHash 8 (mixHash (EO.clHashGo t memo).1
          (mixHash (EO.clHashGo v (EO.clHashGo t memo).2).1
            (EO.clHashGo b (EO.clHashGo v (EO.clHashGo t memo).2).2).1)) =
          clHashS (.letE n t v b nd) := by
        rw [h1, h3, h5]; rfl
      exact ⟨hv, h6.insert hv⟩
  | proj s i x ih =>
    intro memo hm
    rw [EO.clHashGo, EO.withMemoH]
    cases hl : memo[Expr.proj s i x]? with
    | some h => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := ih memo hm
      have hv : mixHash 11 (mixHash (hash s) (mixHash (hash i) (EO.clHashGo x memo).1)) =
          clHashS (.proj s i x) := by
        rw [h1]; rfl
      exact ⟨hv, h2.insert hv⟩
  | bvar | fvar | mvar | sort | const | lit => intro memo hm; exact ⟨rfl, hm⟩

theorem clHash_eq (e : Expr) : EO.clHash e = clHashS e :=
  (clHashGo_spec e _ (fun _ _ h => by simp [EO.freshFor] at h)).1

end clHash

/-- **`EO.clHash` agrees on `erase`-equal terms** (so on `clEq`-equal ones). -/
theorem clHash_of_erase {a b : Expr} (h : erase a = erase b) : EO.clHash a = EO.clHash b := by
  rw [clHash_eq, clHash_eq, ← clHashS_erase a, h, clHashS_erase]

/-! ## The table's translation -/

theorem fvParts_fvId (d n : Nat) : fvParts? (fvId d n) = some (d, n) := by
  unfold fvParts? fvId; simp

theorem eq_fvId_of_fvParts {id : FVarId} {d n : Nat} (h : fvParts? id = some (d, n)) :
    id = fvId d n := by
  obtain ⟨nm⟩ := id
  simp only [fvParts?] at h
  split at h
  · rename_i p d' n'
    split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : p = EO.fvRoot := by simpa using hp
      subst this
      rfl
    · simp at h
  · simp at h

theorem FVarTable.live_lt {t : FVarTable} {d n : Nat} (h : t.live d n = true) :
    n < t.tys.size := by
  unfold FVarTable.live at h
  split at h
  · rename_i ty hty
    exact (Array.getElem?_eq_some_iff.1 hty).1
  · simp at h

/-- The table translates an id to a free variable at the id's depth. -/
theorem FVarTable.transNum_some {t : FVarTable} {d n : Nat} {c : ConLeche.Expr}
    (h : t.transNum d n = some c) :
    t.live d n = true ∧ ∃ ty cty, t.tys[n]? = some ty ∧ toExpr (t.inner n) ty = some cty ∧
      c = .fvar d cty := by
  rw [FVarTable.transNum_eq] at h
  split at h
  · rename_i hl
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ty, hty, cty, hcty, rfl⟩ := h
    exact ⟨hl, ty, cty, hty, hcty, rfl⟩
  · simp at h

theorem FVarTable.trans_some {t : FVarTable} {id : FVarId} {c : ConLeche.Expr}
    (h : t.trans id = some c) :
    ∃ d n, id = fvId d n ∧ t.transNum d n = some c := by
  unfold FVarTable.trans at h
  split at h
  · rename_i d n hp
    exact ⟨d, n, eq_fvId_of_fvParts hp, h⟩
  · simp at h

theorem FVarTable.trans_fvarsOnly (t : FVarTable) : FVarsOnly t.trans := by
  intro id c h
  obtain ⟨d, n, -, hn⟩ := FVarTable.trans_some h
  obtain ⟨-, ty, cty, -, -, rfl⟩ := FVarTable.transNum_some hn
  exact ⟨d, cty, rfl⟩

theorem fvDepth_fvId (d n : Nat) : EO.fvDepth? (fvId d n) = some d := by
  unfold EO.fvDepth? fvId; simp

/-- The table translates an id at the depth the id carries (what
`EO.abstractDepths` reads). -/
theorem FVarTable.trans_depthOK (t : FVarTable) : FvDepthOK t.trans := by
  intro id c h
  obtain ⟨d, n, rfl, hn⟩ := FVarTable.trans_some h
  obtain ⟨-, ty, cty, -, -, rfl⟩ := FVarTable.transNum_some hn
  exact ⟨d, cty, rfl, fvDepth_fvId d n⟩

theorem FVarTable.inner_some {t : FVarTable} {n : Nat} {id : FVarId} {c : ConLeche.Expr}
    (h : t.inner n id = some c) :
    ∃ d m, id = fvId d m ∧ m < n ∧ t.transNum d m = some c := by
  unfold FVarTable.inner at h
  split at h
  · rename_i d m hp
    split at h
    · rename_i hm; exact ⟨d, m, eq_fvId_of_fvParts hp, hm, h⟩
    · simp at h
  · simp at h

theorem FVarTable.inner_fvarsOnly (t : FVarTable) (n : Nat) : FVarsOnly (t.inner n) := by
  intro id c h
  obtain ⟨d, m, -, -, hm⟩ := FVarTable.inner_some h
  obtain ⟨-, ty, cty, -, -, rfl⟩ := FVarTable.transNum_some hm
  exact ⟨d, cty, rfl⟩

theorem FVarTable.inner_mono (t : FVarTable) {n N : Nat} (h : n ≤ N) : FvLe (t.inner n) (t.inner N) := by
  intro id c hc
  obtain ⟨d, m, rfl, hm, ht⟩ := FVarTable.inner_some hc
  have hmN : m < N := by omega
  simp only [FVarTable.inner, fvParts_fvId, hmN, ↓reduceIte]; exact ht

theorem FVarTable.inner_le_trans (t : FVarTable) (n : Nat) : FvLe (t.inner n) t.trans := by
  intro id c hc
  obtain ⟨d, m, rfl, -, ht⟩ := FVarTable.inner_some hc
  simp only [FVarTable.trans, fvParts_fvId]; exact ht

/-- Above the table's size, the inner translation is the whole one. -/
theorem FVarTable.trans_le_inner (t : FVarTable) {n : Nat} (h : t.tys.size ≤ n) :
    FvLe t.trans (t.inner n) := by
  intro id c hc
  obtain ⟨d, m, rfl, ht⟩ := FVarTable.trans_some hc
  have := FVarTable.live_lt (FVarTable.transNum_some ht).1
  have hmn : m < n := by omega
  simp only [FVarTable.inner, fvParts_fvId, hmn, ↓reduceIte]; exact ht

/-! ## O3: the table's translation tells ids apart -/

theorem FVTableOK.transNum_inj {s : InLean.CState} (hs : FVTableOK s) :
    ∀ N d₁ n₁ d₂ n₂ c, n₁ < N → n₂ < N → (tableOf s).transNum d₁ n₁ = some c →
      (tableOf s).transNum d₂ n₂ = some c → d₁ = d₂ ∧ n₁ = n₂ := by
  intro N
  induction N with
  | zero => intro _ _ _ _ _ h; omega
  | succ N ih =>
    intro d₁ n₁ d₂ n₂ c h₁ h₂ e₁ e₂
    obtain ⟨l₁, ty₁, ct₁, hty₁, hct₁, rfl⟩ := FVarTable.transNum_some e₁
    obtain ⟨l₂, ty₂, ct₂, hty₂, hct₂, hc⟩ := FVarTable.transNum_some e₂
    simp only [ConLeche.Expr.fvar.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨rfl, ?_⟩
    -- the types translate equal along the numbers below `N`, which the
    -- induction tells apart
    have hinj : FvInj ((tableOf s).inner N) := by
      intro i j x hi hj
      obtain ⟨di, mi, rfl, hmi, hti⟩ := FVarTable.inner_some hi
      obtain ⟨dj, mj, rfl, hmj, htj⟩ := FVarTable.inner_some hj
      obtain ⟨rfl, rfl⟩ := ih di mi dj mj x hmi hmj hti htj
      rfl
    have he : erase ty₁ = erase ty₂ :=
      erase_eq_of_toExpr (FVarTable.inner_fvarsOnly _ N) hinj
        (toExpr_mono (FVarTable.inner_mono _ (by omega)) ty₁ ct₁ hct₁)
        (toExpr_mono (FVarTable.inner_mono _ (by omega)) ty₂ ct₁ hct₂)
    -- so they hash alike, and the two numbers share one class
    unfold FVarTable.live at l₁ l₂
    simp only [tableOf] at hty₁ hty₂ l₁ l₂
    rw [hty₁] at l₁
    rw [hty₂] at l₂
    simp only at l₁ l₂
    rw [clHash_of_erase he] at l₁
    exact hs.distinct d₁ _ n₁ n₂ ty₁ ty₂ (List.contains_iff_mem.1 l₁)
      (List.contains_iff_mem.1 l₂) hty₁ hty₂ he

/-- **O3: under the table's invariant, the id translation is injective.** -/
theorem FVTableOK.trans_inj {s : InLean.CState} (hs : FVTableOK s) :
    FvInj (tableOf s).trans := by
  intro i j c hi hj
  obtain ⟨di, ni, rfl, hti⟩ := FVarTable.trans_some hi
  obtain ⟨dj, nj, rfl, htj⟩ := FVarTable.trans_some hj
  have hni := FVarTable.live_lt (FVarTable.transNum_some hti).1
  have hnj := FVarTable.live_lt (FVarTable.transNum_some htj).1
  obtain ⟨rfl, rfl⟩ := hs.transNum_inj _ di ni dj nj c hni hnj hti htj
  rfl

/-! ## O3: interning keeps the table in order -/

theorem erase_eraseK : ∀ e : Expr, erase (eraseK e) = erase e := by
  intro e
  induction e <;> simp_all [erase, eraseK]

theorem erase_of_keyEq {a b : Expr} (h : Expr.keyEq a b = true) : erase a = erase b := by
  simp only [Expr.keyEq, decide_eq_true_eq] at h
  rw [← erase_eraseK a, h, erase_eraseK]

theorem getElem?_push_of_lt {α : Type} {a : Array α} {x : α} {m : Nat} (h : m < a.size) :
    (a.push x)[m]? = a[m]? := by
  rw [Array.getElem?_push]; simp [Nat.ne_of_lt h]

theorem key_beq {a b : Nat} {x y : Expr} (h : ((a, EKey.mk x) == (b, EKey.mk y)) = true) :
    a = b ∧ Expr.keyEq x y = true := by
  simp only [BEq.beq, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, h.2⟩

/-- The table after interning a fresh number `t.tys.size` of type `ty` in class
`(d, h)` (`cands` that class's numbers before). -/
@[expose] def FVarTable.push (t : FVarTable) (d : Nat) (h : UInt64) (cands : List Nat) (ty : Expr) :
    FVarTable :=
  ⟨t.tys.push ty, t.cls.insert (d, h) (t.tys.size :: cands)⟩

theorem FVarTable.push_live {t : FVarTable} {d : Nat} {h : UInt64} {ty : Expr}
    {d' m : Nat} (hm : m < t.tys.size) :
    (t.push d h (t.cls.getD (d, h) []) ty).live d' m = t.live d' m := by
  unfold FVarTable.live FVarTable.push
  simp only [Array.getElem?_push, show m ≠ t.tys.size by omega, ↓reduceIte]
  split
  · rename_i tm _
    rw [Std.HashMap.getD_insert]
    split
    · rename_i heq
      have : (d, h) = (d', InLean.EO.clHash tm) := eq_of_beq heq
      rw [this]
      simp only [List.contains_cons]
      have : (m == t.tys.size) = false := by simp; omega
      rw [this, Bool.false_or]
    · rfl
  · rfl

theorem FVarTable.push_transNum {t : FVarTable} {d : Nat} {h : UInt64} {ty : Expr} :
    ∀ m, m < t.tys.size → ∀ d',
      (t.push d h (t.cls.getD (d, h) []) ty).transNum d' m = t.transNum d' m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm d'
    rw [FVarTable.transNum_eq, FVarTable.transNum_eq, FVarTable.push_live hm]
    have hin : (t.push d h (t.cls.getD (d, h) []) ty).inner m = t.inner m := by
      funext id
      unfold FVarTable.inner
      split
      · rename_i d'' m'' _
        split
        · rename_i hlt; exact ih m'' hlt (by omega) d''
        · rfl
      · rfl
    have hty : (t.push d h (t.cls.getD (d, h) []) ty).tys[m]? = t.tys[m]? := by
      simp only [FVarTable.push, Array.getElem?_push, show m ≠ t.tys.size by omega, ↓reduceIte]
    rw [hin, hty]

theorem FVarTable.push_trans {t : FVarTable} {d : Nat} {h : UInt64} {ty : Expr} :
    FvLe t.trans (t.push d h (t.cls.getD (d, h) []) ty).trans := by
  intro id c hc
  obtain ⟨d', m, rfl, ht⟩ := FVarTable.trans_some hc
  have hm := FVarTable.live_lt (FVarTable.transNum_some ht).1
  simp only [FVarTable.trans, fvParts_fvId]
  rw [FVarTable.push_transNum m hm d']; exact ht

theorem FVarTable.push_inner {t : FVarTable} {d : Nat} {h : UInt64} {ty : Expr} {m : Nat}
    (hm : m ≤ t.tys.size) :
    (t.push d h (t.cls.getD (d, h) []) ty).inner m = t.inner m := by
  funext id
  unfold FVarTable.inner
  split
  · rename_i d'' m'' _
    split
    · rename_i hlt; exact FVarTable.push_transNum m'' (by omega) d''
    · rfl
  · rfl

/-- **O3: `mkFVarM` interns the free variable con-leche's `.fvar d cty` is**,
keeps the table's invariant, only extends the translation, and touches no
field but the table's. -/
theorem mkFVarM_ok {s : InLean.CState} (hs : FVTableOK s) {d : Nat} {ty : Expr}
    {cty : ConLeche.Expr} (hty : TransS s ty = some cty) (hrty : Expr.RangeOk ty) {r : Expr}
    {s' : InLean.CState}
    (hrun : mkFVarM d ty s = .ok (r, s')) :
    FVTableOK s' ∧ TransS s' r = some (.fvar d cty) ∧
      FvLe (tableOf s).trans (tableOf s').trans ∧
      ∃ seen cls tys, s' = { s with fvSeen := seen, fvCls := cls, fvTys := tys } := by
  -- the type, read through the whole table, and an `erase`-equal interned type
  have hread : ∀ n tn, s.fvTys[n]? = some tn → erase tn = erase ty →
      toExpr ((tableOf s).inner n) tn = some cty := by
    intro n tn htn he
    obtain ⟨ctn, hctn⟩ := hs.ty n tn htn
    have h1 := toExpr_mono ((tableOf s).inner_le_trans n) tn ctn hctn
    rw [← toExpr_erase, he, toExpr_erase] at h1
    unfold TransS at hty
    rw [hty] at h1
    cases h1; exact hctn
  simp only [mkFVarM, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    Except.pure] at hrun
  split at hrun
  · -- the `keyEq` fast path
    rename_i n hseen
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨hl, tn, htn, he⟩ := hs.seen d ty n hseen
    refine ⟨hs, ?_, fun _ _ h => h, s.fvSeen, s.fvCls, s.fvTys, rfl⟩
    have hr := hread n tn htn he.symm
    simp only [TransS, toExpr, FVarTable.trans, fvParts_fvId, FVarTable.transNum_eq, hl,
      ↓reduceIte]
    simp only [tableOf] at htn hr ⊢
    simp [htn, hr]
  · rename_i hmiss
    split at hrun
    · -- a class of the depth holds an `erase`-equal type
      rename_i c hfind
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have hmem := List.mem_of_find?_eq_some hfind
      have hp := List.find?_some hfind
      obtain ⟨tc, htc, hhash⟩ := hs.cls d _ c hmem
      rw [htc, Option.getD_some] at hp
      replace hp := Expr.clEq_sound hp
      have hl : (tableOf s).live d c = true := by
        simp only [FVarTable.live, tableOf, htc, hhash]
        exact List.contains_iff_mem.2 hmem
      refine ⟨?_, ?_, fun _ _ h => h, _, s.fvCls, s.fvTys, rfl⟩
      · refine { cls := hs.cls, distinct := hs.distinct, ty := hs.ty, range := hs.range, seen := ?_ }
        intro d' k n hk
        rw [Std.HashMap.getElem?_insert] at hk
        split at hk
        · rename_i heq
          simp only [Option.some.injEq] at hk
          subst hk
          obtain ⟨rfl, hk'⟩ := key_beq heq
          refine ⟨hl, tc, htc, ?_⟩
          rw [← erase_of_keyEq hk', hp]
        · exact hs.seen d' k n hk
      · have hr := hread c tc htc hp
        simp only [TransS, toExpr, FVarTable.trans, fvParts_fvId, FVarTable.transNum_eq]
        simp only [tableOf] at hl htc hr ⊢
        simp [hl, htc, hr]
    · -- a fresh number
      rename_i hnone
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have hnot : ∀ x ∈ s.fvCls.getD (d, EO.clHash ty) [], ∀ tx, s.fvTys[x]? = some tx →
          erase tx ≠ erase ty := by
        intro x hx tx htx he
        have := (List.find?_eq_none.1 hnone) x hx
        rw [htx, Option.getD_some, clEq_iff_erase (hs.range x tx htx) hrty] at this
        exact this he
      have hlt : ∀ d' h' m, m ∈ s.fvCls.getD (d', h') [] → m < s.fvTys.size := by
        intro d' h' m hm
        obtain ⟨tm, htm, -⟩ := hs.cls d' h' m hm
        exact (Array.getElem?_eq_some_iff.1 htm).1
      have htab :
          tableOf
            { s with
              fvSeen := s.fvSeen.insert (d, EKey.mk ty) s.fvTys.size
              fvCls := s.fvCls.insert (d, EO.clHash ty)
                (s.fvTys.size :: s.fvCls.getD (d, EO.clHash ty) [])
              fvTys := s.fvTys.push ty } =
          (tableOf s).push d (EO.clHash ty) ((tableOf s).cls.getD (d, EO.clHash ty) []) ty := rfl
      have hsize : (tableOf s).tys.size = s.fvTys.size := rfl
      -- the new number is live at `d`
      have hlnew : ((tableOf s).push d (EO.clHash ty) ((tableOf s).cls.getD (d, EO.clHash ty) []) ty).live
          d s.fvTys.size = true := by
        simp [FVarTable.live, FVarTable.push, tableOf]
      have hinnew : toExpr (((tableOf s).push d (EO.clHash ty)
          ((tableOf s).cls.getD (d, EO.clHash ty) []) ty).inner s.fvTys.size) ty = some cty := by
        rw [FVarTable.push_inner (Nat.le_of_eq hsize.symm)]
        exact toExpr_mono ((tableOf s).trans_le_inner (Nat.le_of_eq hsize)) ty cty hty
      refine ⟨?_, ?_, ?_, _, _, _, rfl⟩
      · refine { cls := ?_, distinct := ?_, ty := ?_, seen := ?_, range := ?_ }
        · intro d' h' m hm
          simp only [Std.HashMap.getD_insert] at hm
          split at hm
          · rename_i heq
            have hk : (d, EO.clHash ty) = (d', h') := eq_of_beq heq
            simp only [Prod.mk.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            rcases List.mem_cons.1 hm with rfl | hm
            · exact ⟨ty, Array.getElem?_push_size, rfl⟩
            · obtain ⟨tm, htm, hh⟩ := hs.cls d _ m hm
              exact ⟨tm, (getElem?_push_of_lt (hlt _ _ _ hm)).trans htm, hh⟩
          · obtain ⟨tm, htm, hh⟩ := hs.cls d' h' m hm
            exact ⟨tm, (getElem?_push_of_lt (hlt _ _ _ hm)).trans htm, hh⟩
        · intro d' h' n m tn tm hn hm htn htm he
          simp only [Std.HashMap.getD_insert] at hn hm
          split at hn
          · rename_i heq
            have hk : (d, EO.clHash ty) = (d', h') := eq_of_beq heq
            simp only [Prod.mk.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            simp only [heq, ↓reduceIte] at hm
            rcases List.mem_cons.1 hn with rfl | hn <;> rcases List.mem_cons.1 hm with rfl | hm
            · rfl
            · rw [Array.getElem?_push_size, Option.some.injEq] at htn
              subst htn
              rw [getElem?_push_of_lt (hlt _ _ _ hm)] at htm
              exact absurd he.symm (hnot m hm tm htm)
            · rw [Array.getElem?_push_size, Option.some.injEq] at htm
              subst htm
              rw [getElem?_push_of_lt (hlt _ _ _ hn)] at htn
              exact absurd he (hnot n hn tn htn)
            · rw [getElem?_push_of_lt (hlt _ _ _ hn)] at htn
              rw [getElem?_push_of_lt (hlt _ _ _ hm)] at htm
              exact hs.distinct d _ n m tn tm hn hm htn htm he
          · rename_i hne
            simp only [hne, Bool.false_eq_true, ↓reduceIte] at hm
            rw [getElem?_push_of_lt (hlt _ _ _ hn)] at htn
            rw [getElem?_push_of_lt (hlt _ _ _ hm)] at htm
            exact hs.distinct d' h' n m tn tm hn hm htn htm he
        · intro n tn htn
          rw [htab]
          by_cases hn : n < s.fvTys.size
          · rw [getElem?_push_of_lt hn] at htn
            rw [FVarTable.push_inner (by rw [hsize]; omega)]
            exact hs.ty n tn htn
          · have : n = s.fvTys.size := by
              have := (Array.getElem?_eq_some_iff.1 htn).1
              simp at this; omega
            subst this
            rw [Array.getElem?_push_size, Option.some.injEq] at htn
            subst htn
            exact ⟨cty, hinnew⟩
        · intro d' k n hk
          rw [htab]
          rw [Std.HashMap.getElem?_insert] at hk
          split at hk
          · rename_i heq
            simp only [Option.some.injEq] at hk
            subst hk
            obtain ⟨rfl, hk'⟩ := key_beq heq
            exact ⟨hlnew, ty, Array.getElem?_push_size, (erase_of_keyEq hk').symm⟩
          · obtain ⟨hl, tn, htn, he⟩ := hs.seen d' k n hk
            have hn := FVarTable.live_lt hl
            refine ⟨?_, tn, ?_, he⟩
            · rw [FVarTable.push_live hn]; exact hl
            · exact (getElem?_push_of_lt hn).trans htn
        · intro n tn htn
          by_cases hn : n < s.fvTys.size
          · rw [getElem?_push_of_lt hn] at htn
            exact hs.range n tn htn
          · have : n = s.fvTys.size := by
              have := (Array.getElem?_eq_some_iff.1 htn).1
              simp at this; omega
            subst this
            rw [Array.getElem?_push_size, Option.some.injEq] at htn
            subst htn
            exact hrty
      · unfold TransS
        rw [htab]
        simp only [toExpr, FVarTable.trans, fvParts_fvId, FVarTable.transNum_eq, hlnew, ↓reduceIte]
        simp [FVarTable.push, tableOf] at hinnew ⊢
        simp [hinnew]
      · rw [htab]; exact FVarTable.push_trans

/-- **A translated free variable's type is the table's**: what
`InLean.fvarTypeM?` reads (`CState.fvTys[n]`) translates to the type
con-leche's node `.fvar d cty` carries. -/
theorem TransS_fvar {s : InLean.CState} {id : FVarId} {d : Nat} {cty : ConLeche.Expr}
    (h : TransS s (.fvar id) = some (.fvar d cty)) :
    ∃ n ty, fvParts? id = some (d, n) ∧ s.fvTys[n]? = some ty ∧ TransS s ty = some cty := by
  simp only [TransS, toExpr] at h
  obtain ⟨d', n, rfl, hn⟩ := FVarTable.trans_some h
  obtain ⟨-, ty, cty', hty, hcty, hc⟩ := FVarTable.transNum_some hn
  simp only [ConLeche.Expr.fvar.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨n, ty, fvParts_fvId d n, hty,
    toExpr_mono ((tableOf s).inner_le_trans n) ty cty hcty⟩

/-- **O2 at a state**: the checker's equality is equality of translations. -/
theorem clEq_iff_TransS {s : InLean.CState} (hs : FVTableOK s) {a b : Expr} {c : ConLeche.Expr}
    (hra : Expr.RangeOk a) (hrb : Expr.RangeOk b)
    (ha : TransS s a = some c) : Expr.clEq a b = true ↔ TransS s b = some c := by
  constructor
  · intro h
    rw [← ha]; exact (toExpr_of_clEq _ h).symm
  · intro hb
    exact clEq_of_toExpr (FVarTable.trans_fvarsOnly _) hs.trans_inj hra hrb ha hb

end InLeanProof
