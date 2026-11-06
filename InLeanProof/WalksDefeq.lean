module

public import InLeanProof.StateOpsI
public import ConLeche.Verify.Cached.DiscC5
/- `Literal`'s derived `BEq` is not exposed by `Lean.Expr`; `lit_beq_toLit`
reads it. -/
import all Lean.Expr

/-!
# The definitional-equality walks (task #451, lane P2-defeq)

The twins of `Verify/Cached/DiscC2.lean` (the stuck-term certificates) and
`Verify/Cached/DiscC5.lean` (definitional equality: the easy cases, the
λ-telescope, offsets, lazy delta, the proj/proj check, the stuck
comparison and `defeqBody`), each InLean body's triple proved by its
master twin's `sym only [conleche_grind, …] => vcgen […] <;> finish`
script, with the translation vocabulary of `GrindI.lean`/`StateOpsI.lean`
and the vocabulary below.

The post of every walk is `KnotSpecI`'s: `CSOKI`, the table grown
(`TabLe`), and the pure entry at the inputs' translations answering the
answer's translation; a walk that answers a term also states its reading,
its scope and its closedness.

**What this file assumes** (named hypotheses, other lanes' to discharge):
* the walks of `DiscC1` that P2-whnf owns (`defEqList`, `defeqSpine`,
  `unfoldDefinition`, `reduceNat`, `reduceProjCore`): `*SpecI` predicates;
* the readers of the environment at use (O4, P3's): `DefeqEnvI fe env`,
  each reader of `InLean/FEnv.lean` and `InLean/CoreDefs.lean` the
  definitional-equality family runs, against con-leche's at the translation.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Vocabulary: the term readers through the translation -/

section Readers

variable (s : InLean.CState)

/-- A free variable's total translation is a free variable or `bvar 0`:
no constant, no application. -/
theorem trans_getD_cases (s : InLean.CState) (id : FVarId) :
    (∃ i ty, (FVarTable.trans (tableOf s) id).getD (.bvar 0) = .fvar i ty) ∨
      (FVarTable.trans (tableOf s) id).getD (.bvar 0) = .bvar 0 := by
  cases h : FVarTable.trans (tableOf s) id with
  | none => exact Or.inr rfl
  | some c =>
    obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c h
    exact Or.inl ⟨d, ty, rfl⟩

theorem toName_boolTrueName : toName InLean.boolTrueName = ConLeche.boolTrueName := rfl
theorem toName_natZeroName : toName InLean.natZeroName = ConLeche.natZeroName := rfl
theorem toName_natSuccName : toName InLean.natSuccName = ConLeche.natSuccName := rfl

theorem cname_beq_eq_decide (a b : ConLeche.Name) : (a == b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp [h]

theorem isBoolTrue_TrS (e : Expr) :
    InLean.Expr.isBoolTrue e = (TrS s e).isBoolTrue := by
  induction e with
  | mdata _ x ih => exact ih
  | const c us =>
    cases us with
    | nil =>
      simp only [InLean.Expr.isBoolTrue, TrS_const, List.map_nil, ConLeche.Expr.isBoolTrue,
        name_beq_eq_decide, cname_beq_eq_decide, toName_boolTrueName]
      exact decide_eq_decide.2 Iff.rfl
    | cons _ _ => rfl
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h⟩ | h <;>
      simp [InLean.Expr.isBoolTrue, TrS, trE, h, ConLeche.Expr.isBoolTrue]
  | _ => rfl
grind_pattern [conleche_grind] isBoolTrue_TrS => InLean.Expr.isBoolTrue e, TrS s e

theorem okL_of_okLv {u : Level} (h : okLv u = true) : okL u = true := by
  simp only [okLv, Bool.and_eq_true] at h; exact h.1
grind_pattern [conleche_grind] okL_of_okLv => okLv u

theorem all_okL_of_okLv {us : List Level} (h : us.all okLv = true) : us.all okL = true := by
  simp only [List.all_eq_true] at h ⊢; exact fun u hu => okL_of_okLv (h u hu)
grind_pattern [conleche_grind] all_okL_of_okLv => us.all okLv

@[conleche_grind =] theorem verifiedChecks_verifiedI :
    InLean.CheckMode.verifiedChecks .verified = true := rfl

@[conleche_grind =] theorem verifiedChecks_verifiedC :
    ConLeche.CheckMode.verifiedChecks .verified = true := rfl

@[conleche_grind =] theorem okL_zero : okL Level.zero = true := rfl
@[conleche_grind =] theorem trL_zero : trL Level.zero = ConLeche.Level.zero := rfl

/-- **Inversion**: a term translating to a sort is a sort under its `mdata`. -/
theorem stripTop_of_TrS_sort {e : Expr} {v : ConLeche.Level} (h : TrS s e = .sort v) :
    ∃ u, EO.stripTop e = .sort u := by
  induction e with
  | sort u => exact ⟨u, rfl⟩
  | mdata _ x ih => exact ih h
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h'] at h
  | _ => simp [TrS, trE] at h

theorem stripTop_of_TrS_forallE {e : Expr} {t b : ConLeche.Expr} (h : TrS s e = .forallE t b) :
    ∃ n t' b' bi, EO.stripTop e = .forallE n t' b' bi := by
  induction e with
  | forallE n t' b' bi => exact ⟨n, t', b', bi, rfl⟩
  | mdata _ x ih => exact ih h
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h'] at h
  | _ => simp [TrS, trE] at h

theorem stripTop_of_TrS_lam {e : Expr} {t b : ConLeche.Expr} (h : TrS s e = .lam t b) :
    ∃ n t' b' bi, EO.stripTop e = .lam n t' b' bi := by
  induction e with
  | lam n t' b' bi => exact ⟨n, t', b', bi, rfl⟩
  | mdata _ x ih => exact ih h
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h'] at h
  | _ => simp [TrS, trE] at h

theorem stripTop_of_TrS_lit {e : Expr} {l : ConLeche.Literal} (h : TrS s e = .lit l) :
    ∃ l', EO.stripTop e = .lit l' := by
  induction e with
  | lit l' => exact ⟨l', rfl⟩
  | mdata _ x ih => exact ih h
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h'] at h
  | _ => simp [TrS, trE] at h

theorem stripTop_of_TrS_const {e : Expr} {n : ConLeche.Name} {us : List ConLeche.Level}
    (h : TrS s e = .const n us) : ∃ n' us', EO.stripTop e = .const n' us' := by
  induction e with
  | const n' us' => exact ⟨n', us', rfl⟩
  | mdata _ x ih => exact ih h
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h'] at h
  | _ => simp [TrS, trE] at h

theorem stripTop_of_TrS_app {e : Expr} {f a : ConLeche.Expr} (h : TrS s e = .app f a) :
    ∃ f' a', EO.stripTop e = .app f' a' := by
  induction e with
  | app f' a' => exact ⟨f', a', rfl⟩
  | mdata _ x ih => exact ih h
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h'] at h
  | _ => simp [TrS, trE] at h

theorem stripTop_of_TrS_proj {e : Expr} {n : ConLeche.Name} {i : Nat} {x : ConLeche.Expr}
    (h : TrS s e = .proj n i x) : ∃ n' x', EO.stripTop e = .proj n' i x' := by
  induction e with
  | proj n' i' x' => simp [TrS, trE] at h; exact ⟨n', x', by rw [h.2.1]; rfl⟩
  | mdata _ x ih => exact ih h
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h'] at h
  | _ => simp [TrS, trE] at h

/-- On a term with a reading, a free variable reads as a free variable. -/
theorem stripTop_of_TrS_fvar {e : Expr} {i : Nat} {ty : ConLeche.Expr}
    (h : TrS s e = .fvar i ty) : ∃ id, EO.stripTop e = .fvar id := by
  induction e with
  | fvar id => exact ⟨id, rfl⟩
  | mdata _ x ih => exact ih h
  | _ => simp [TrS, trE] at h

theorem getAppFnT_shape : ∀ (e : Expr),
    (∀ m x, Expr.getAppFnT e ≠ .mdata m x) ∧ (∀ f a, Expr.getAppFnT e ≠ .app f a)
  | .app f _ => by simp only [Expr.getAppFnT]; exact getAppFnT_shape f
  | .mdata _ x => by simp only [Expr.getAppFnT]; exact getAppFnT_shape x
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => by simp [Expr.getAppFnT]

/-! The inversions keyed on a scrutinee (`EO.stripTop e`), so that grind
pairs a constructor only with the translations of the terms a walk
matches on. -/

theorem invS_sort {e : Expr} {v : ConLeche.Level} (h : TrS s (EO.stripTop e) = (.sort v)) :
    ∃ u, EO.stripTop e = .sort u :=
  stripTop_of_TrS_sort s (by rwa [TrS_stripTop] at h)
grind_pattern [conleche_grind] invS_sort => TrS s (EO.stripTop e), ConLeche.Expr.sort v

theorem invS_forallE {e : Expr} {t b : ConLeche.Expr} (h : TrS s (EO.stripTop e) = (.forallE t b)) :
    ∃ n t' b' bi, EO.stripTop e = .forallE n t' b' bi :=
  stripTop_of_TrS_forallE s (by rwa [TrS_stripTop] at h)
grind_pattern [conleche_grind] invS_forallE => TrS s (EO.stripTop e), ConLeche.Expr.forallE t b

theorem invS_lam {e : Expr} {t b : ConLeche.Expr} (h : TrS s (EO.stripTop e) = (.lam t b)) :
    ∃ n t' b' bi, EO.stripTop e = .lam n t' b' bi :=
  stripTop_of_TrS_lam s (by rwa [TrS_stripTop] at h)
grind_pattern [conleche_grind] invS_lam => TrS s (EO.stripTop e), ConLeche.Expr.lam t b

theorem invS_lit {e : Expr} {l : ConLeche.Literal} (h : TrS s (EO.stripTop e) = (.lit l)) :
    ∃ l', EO.stripTop e = .lit l' :=
  stripTop_of_TrS_lit s (by rwa [TrS_stripTop] at h)
grind_pattern [conleche_grind] invS_lit => TrS s (EO.stripTop e), ConLeche.Expr.lit l

theorem invS_const {e : Expr} {n : ConLeche.Name} {us : List ConLeche.Level} (h : TrS s (EO.stripTop e) = (.const n us)) :
    ∃ n' us', EO.stripTop e = .const n' us' :=
  stripTop_of_TrS_const s (by rwa [TrS_stripTop] at h)
grind_pattern [conleche_grind] invS_const => TrS s (EO.stripTop e), ConLeche.Expr.const n us

theorem invS_app {e : Expr} {f a : ConLeche.Expr} (h : TrS s (EO.stripTop e) = (.app f a)) :
    ∃ f' a', EO.stripTop e = .app f' a' :=
  stripTop_of_TrS_app s (by rwa [TrS_stripTop] at h)
grind_pattern [conleche_grind] invS_app => TrS s (EO.stripTop e), ConLeche.Expr.app f a

theorem invS_proj {e : Expr} {n : ConLeche.Name} {i : Nat} {x : ConLeche.Expr} (h : TrS s (EO.stripTop e) = (.proj n i x)) :
    ∃ n' x', EO.stripTop e = .proj n' i x' :=
  stripTop_of_TrS_proj s (by rwa [TrS_stripTop] at h)
grind_pattern [conleche_grind] invS_proj => TrS s (EO.stripTop e), ConLeche.Expr.proj n i x

theorem invS_fvar {e : Expr} {i : Nat} {ty : ConLeche.Expr} (h : TrS s (EO.stripTop e) = (.fvar i ty)) :
    ∃ id, EO.stripTop e = .fvar id :=
  stripTop_of_TrS_fvar s (by rwa [TrS_stripTop] at h)
grind_pattern [conleche_grind] invS_fvar => TrS s (EO.stripTop e), ConLeche.Expr.fvar i ty

/-- The head reader of `etaCert` (`ioNeutral`), on a term with a reading. -/
theorem ioNeutral_TrS {e : Expr} (h : OkS s e = true) :
    InLean.Expr.ioNeutral e = (TrS s e).ioNeutral := by
  have hh := OkS_getAppFnT s h
  simp only [InLean.Expr.ioNeutral, ConLeche.Expr.ioNeutral, ← TrS_getAppFnT]
  have hsh := getAppFnT_shape e
  generalize Expr.getAppFnT e = x at hh hsh
  cases x with
  | fvar id => rw [TrS_fvar hh]
  | mvar _ => simp [OkS, okE] at hh
  | mdata m y => exact absurd rfl (hsh.1 m y)
  | app f a => exact absurd rfl (hsh.2 f a)
  | _ => rfl
grind_pattern [conleche_grind] ioNeutral_TrS => OkS s e, InLean.Expr.ioNeutral e

theorem headIsProj_TrS (e : Expr) :
    InLean.Expr.headIsProj e = (TrS s e).headIsProj := by
  simp only [InLean.Expr.headIsProj, ConLeche.Expr.headIsProj, ← TrS_getAppFnT]
  have hsh := getAppFnT_shape e
  generalize Expr.getAppFnT e = x at hsh
  cases x with
  | fvar id => rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h']
  | mdata m y => exact absurd rfl (hsh.1 m y)
  | app f a => exact absurd rfl (hsh.2 f a)
  | _ => rfl
grind_pattern [conleche_grind] headIsProj_TrS => InLean.Expr.headIsProj e, TrS s e

theorem isForall_stripTop_TrS (e : Expr) :
    (EO.stripTop e).isForall = (TrS s e).isForallE := by
  induction e with
  | mdata _ x ih => exact ih
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;>
      simp [TrS, trE, h', EO.stripTop, ConLeche.Expr.isForallE, Expr.isForall]
  | _ => simp [TrS, trE, EO.stripTop, ConLeche.Expr.isForallE, Expr.isForall]
grind_pattern [conleche_grind] isForall_stripTop_TrS => (EO.stripTop e).isForall, TrS s e

theorem hasFVar_TrS {e : Expr} (h : OkS s e = true) : e.hasFVar = (TrS s e).hasFvar :=
  hasFVar_toExpr (FVarTable.trans_fvarsOnly _) (RangeOk_of_OkS h) (TransS_of_ok h)
grind_pattern [conleche_grind] hasFVar_TrS => OkS s e, e.hasFVar

theorem stripTop_getAppFnT (e : Expr) : EO.stripTop (Expr.getAppFnT e) = Expr.getAppFnT e := by
  have h := (getAppFnT_shape e).1
  generalize Expr.getAppFnT e = x at h
  cases x with
  | mdata m y => exact absurd rfl (h m y)
  | _ => rfl

/-! The inversions keyed on a spine's head (`Expr.getAppFnT e`). -/

theorem invH_sort {e : Expr} {v : ConLeche.Level} (h : TrS s (Expr.getAppFnT e) = (.sort v)) :
    ∃ u, Expr.getAppFnT e = .sort u := by
  have := stripTop_of_TrS_sort s h
  rwa [stripTop_getAppFnT] at this
grind_pattern [conleche_grind] invH_sort => TrS s (Expr.getAppFnT e), ConLeche.Expr.sort v

theorem invH_forallE {e : Expr} {t b : ConLeche.Expr} (h : TrS s (Expr.getAppFnT e) = (.forallE t b)) :
    ∃ n t' b' bi, Expr.getAppFnT e = .forallE n t' b' bi := by
  have := stripTop_of_TrS_forallE s h
  rwa [stripTop_getAppFnT] at this
grind_pattern [conleche_grind] invH_forallE => TrS s (Expr.getAppFnT e), ConLeche.Expr.forallE t b

theorem invH_lam {e : Expr} {t b : ConLeche.Expr} (h : TrS s (Expr.getAppFnT e) = (.lam t b)) :
    ∃ n t' b' bi, Expr.getAppFnT e = .lam n t' b' bi := by
  have := stripTop_of_TrS_lam s h
  rwa [stripTop_getAppFnT] at this
grind_pattern [conleche_grind] invH_lam => TrS s (Expr.getAppFnT e), ConLeche.Expr.lam t b

theorem invH_lit {e : Expr} {l : ConLeche.Literal} (h : TrS s (Expr.getAppFnT e) = (.lit l)) :
    ∃ l', Expr.getAppFnT e = .lit l' := by
  have := stripTop_of_TrS_lit s h
  rwa [stripTop_getAppFnT] at this
grind_pattern [conleche_grind] invH_lit => TrS s (Expr.getAppFnT e), ConLeche.Expr.lit l

theorem invH_const {e : Expr} {n : ConLeche.Name} {us : List ConLeche.Level} (h : TrS s (Expr.getAppFnT e) = (.const n us)) :
    ∃ n' us', Expr.getAppFnT e = .const n' us' := by
  have := stripTop_of_TrS_const s h
  rwa [stripTop_getAppFnT] at this
grind_pattern [conleche_grind] invH_const => TrS s (Expr.getAppFnT e), ConLeche.Expr.const n us

theorem invH_proj {e : Expr} {n : ConLeche.Name} {i : Nat} {x : ConLeche.Expr} (h : TrS s (Expr.getAppFnT e) = (.proj n i x)) :
    ∃ n' x', Expr.getAppFnT e = .proj n' i x' := by
  have := stripTop_of_TrS_proj s h
  rwa [stripTop_getAppFnT] at this
grind_pattern [conleche_grind] invH_proj => TrS s (Expr.getAppFnT e), ConLeche.Expr.proj n i x

theorem invH_fvar {e : Expr} {i : Nat} {ty : ConLeche.Expr} (h : TrS s (Expr.getAppFnT e) = (.fvar i ty)) :
    ∃ id, Expr.getAppFnT e = .fvar id := by
  have := stripTop_of_TrS_fvar s h
  rwa [stripTop_getAppFnT] at this
grind_pattern [conleche_grind] invH_fvar => TrS s (Expr.getAppFnT e), ConLeche.Expr.fvar i ty

end Readers

section Closed
open ConLeche.Expr

@[conleche_grind =] theorem lbb_lam (k : Nat) (t b : ConLeche.Expr) :
    (ConLeche.Expr.lam t b).looseBVarsBounded k =
      (t.looseBVarsBounded k && b.looseBVarsBounded (k + 1)) := rfl
@[conleche_grind =] theorem lbb_forallE (k : Nat) (t b : ConLeche.Expr) :
    (ConLeche.Expr.forallE t b).looseBVarsBounded k =
      (t.looseBVarsBounded k && b.looseBVarsBounded (k + 1)) := rfl
@[conleche_grind =] theorem lbb_fvar (k i : Nat) (ty : ConLeche.Expr) :
    (ConLeche.Expr.fvar i ty).looseBVarsBounded k = true := rfl

end Closed

/- One-value instantiation, keyed on the translated instance alone: the
readings of the pieces at the reading state are then grind's to derive
(`okS_of_tabLe`), where `GrindI`'s multi-pattern waits for them. -/
grind_pattern [conleche_grind] TrS_inst1_eq => TrS s (EO.instantiate1 b v)
grind_pattern [conleche_grind] OkS_inst1 => OkS s (EO.instantiate1 b v)

/- The spine's head, keyed on the translation's head too: the pure side reads
`(TrS s e).getAppFn`, InLean `e.getAppFnT`. -/
grind_pattern [conleche_grind] TrS_getAppFnT => (TrS s e).getAppFn
grind_pattern [conleche_grind] TrSL_appArgs => (TrS s e).getAppArgs

/-! ## Vocabulary: equality, literals, λ pairs, the loop budgets -/

section Eq

theorem fv_of_CSOKI {s : InLean.CState} (hs : CSOKI mode eager env s) : FVTableOK s := hs.fv
grind_pattern [conleche_grind] fv_of_CSOKI => CSOKI mode eager env s

/-- **The checker's equality** (`clEq`, the scoped `==`) on terms with a
reading is equality of translations (P1's `clEq_iff_TransS`). -/
theorem clBeq_TrS {s : InLean.CState} (hs : FVTableOK s) {a b : Expr} (ha : OkS s a = true)
    (hb : OkS s b = true) :
    (@BEq.beq Expr InLean.instBEqExprI a b) = decide (TrS s a = TrS s b) := by
  have h := clEq_iff_TransS hs (TransS_of_ok ha) (b := b)
  rw [TransS_of_ok hb, Option.some.injEq] at h
  show Expr.clEq a b = _
  by_cases he : TrS s a = TrS s b
  · simp only [he, decide_true]; exact h.2 he.symm
  · simp only [he, decide_false]
    cases hc : Expr.clEq a b
    · rfl
    · exact absurd (h.1 hc).symm he
grind_pattern [conleche_grind] clBeq_TrS => OkS s a, @BEq.beq Expr InLean.instBEqExprI a b
grind_pattern [conleche_grind] clBeq_TrS => OkS s b, @BEq.beq Expr InLean.instBEqExprI a b

@[conleche_grind =] theorem lit_beq_toLit : ∀ (a b : Literal), (a == b) = (toLit a == toLit b)
  | .natVal n, .natVal m => by
    show (n == m) = _; rw [Bool.eq_iff_iff]; simp [toLit]
  | .strVal n, .strVal m => by
    show (n == m) = _; rw [Bool.eq_iff_iff]; simp [toLit]
  | .natVal n, .strVal m => by
    show false = _; rw [Bool.eq_iff_iff]; simp [toLit]
  | .strVal n, .natVal m => by
    show false = _; rw [Bool.eq_iff_iff]; simp [toLit]

theorem lamsFuel_eq : InLean.lamsFuel = ConLeche.lamsFuel := by
  unfold InLean.lamsFuel ConLeche.lamsFuel; rfl
theorem defeqLoopFuel_eq : InLean.defeqLoopFuel = ConLeche.defeqLoopFuel := by
  unfold InLean.defeqLoopFuel ConLeche.defeqLoopFuel; rfl

end Eq

section LamPair
variable (s : InLean.CState)

theorem stripTop_of_ne_mdata {x : Expr} (h : ∀ (m : MData) (y : Expr), x = .mdata m y → False) :
    EO.stripTop x = x := by
  cases x with
  | mdata m y => exact absurd rfl (h m y)
  | _ => rfl

/-- A pair of λs, read through `mdata`, translates to the translations' pair. -/
theorem lamPairI_some (a b : Expr) : ∀ {q : Expr × Expr × Expr × Expr},
    InLean.Expr.lamPair? a b = some q →
    TrS s a = .lam (TrS s q.1) (TrS s q.2.1) ∧ TrS s b = .lam (TrS s q.2.2.1) (TrS s q.2.2.2) ∧
      OkS s a = (OkS s q.1 && OkS s q.2.1) ∧ OkS s b = (OkS s q.2.2.1 && OkS s q.2.2.2) ∧
      (TrS s a).lamPair? (TrS s b) = some (TrS s q.1, TrS s q.2.1, TrS s q.2.2.1, TrS s q.2.2.2) := by
  induction a, b using InLean.Expr.lamPair?.induct with
  | case1 _ a b ih => intro q h; rw [InLean.Expr.lamPair?] at h; exact ih h
  | case2 a _ b hna ih =>
    intro q h; rw [InLean.Expr.lamPair?.eq_2 _ _ _ hna] at h; exact ih h
  | case3 =>
    intro q h; simp only [InLean.Expr.lamPair?, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | case4 x y h1 h2 h3 =>
    intro q h; rw [InLean.Expr.lamPair?.eq_4 _ _ h1 h2 h3] at h; simp at h
grind_pattern [conleche_grind] lamPairI_some => InLean.Expr.lamPair? a b, TrS s a, some q

theorem lamPairI_none (a b : Expr) : InLean.Expr.lamPair? a b = none →
    (TrS s a).lamPair? (TrS s b) = none := by
  induction a, b using InLean.Expr.lamPair?.induct with
  | case1 _ a b ih => intro h; rw [InLean.Expr.lamPair?] at h; exact ih h
  | case2 a _ b hna ih =>
    intro h; rw [InLean.Expr.lamPair?.eq_2 _ _ _ hna] at h; exact ih h
  | case3 => intro h; simp [InLean.Expr.lamPair?] at h
  | case4 x y h1 h2 h3 =>
    intro _
    cases hx : TrS s x with
    | lam t b =>
      obtain ⟨n, t', b', bi, hx'⟩ := stripTop_of_TrS_lam s hx
      rw [stripTop_of_ne_mdata h1] at hx'
      cases hy : TrS s y with
      | lam t₂ b₂ =>
        obtain ⟨n₂, t₂', b₂', bi₂, hy'⟩ := stripTop_of_TrS_lam s hy
        rw [stripTop_of_ne_mdata h2] at hy'
        exact (h3 _ _ _ _ _ _ _ _ hx' hy').elim
      | _ => rfl
    | _ => rfl
grind_pattern [conleche_grind] lamPairI_none => InLean.Expr.lamPair? a b, TrS s a, TrS s b

end LamPair

/-! ## The `Nat` offset readers through the translation -/

section Offsets
variable (s : InLean.CState)

theorem isNatZero_TrS (e : Expr) : InLean.Expr.isNatZero e = (TrS s e).isNatZero := by
  induction e with
  | mdata _ x ih => exact ih
  | lit l =>
    cases l with
    | natVal n => cases n <;> rfl
    | strVal _ => rfl
  | const c us =>
    cases us with
    | nil =>
      simp only [InLean.Expr.isNatZero, TrS_const, List.map_nil, ConLeche.Expr.isNatZero,
        name_beq_eq_decide, cname_beq_eq_decide, toName_natZeroName]
      exact decide_eq_decide.2 Iff.rfl
    | cons _ _ => rfl
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h⟩ | h <;>
      simp [InLean.Expr.isNatZero, TrS, trE, h, ConLeche.Expr.isNatZero]
  | _ => rfl
grind_pattern [conleche_grind] isNatZero_TrS => InLean.Expr.isNatZero e, TrS s e

theorem isLitI_TrS (e : Expr) : InLean.Expr.isLitI e = (TrS s e).isLit := by
  induction e with
  | mdata _ x ih => exact ih
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h⟩ | h <;>
      simp [InLean.Expr.isLitI, TrS, trE, h, ConLeche.Expr.isLit]
  | _ => rfl
grind_pattern [conleche_grind] isLitI_TrS => InLean.Expr.isLitI e, TrS s e

theorem natPredI_TrS (e : Expr) : TrO s (InLean.Expr.natPred? e) = (TrS s e).natPred? := by
  induction e with
  | mdata _ x ih => exact ih
  | lit l =>
    cases l with
    | natVal n => cases n <;> rfl
    | strVal _ => rfl
  | app f x _ _ =>
    simp only [InLean.Expr.natPred?, TrS_app]
    rw [← TrS_stripTop s f]
    have hne : ∀ m y, EO.stripTop f ≠ .mdata m y := fun m y h => stripTop_ne_mdata h
    generalize EO.stripTop f = g at hne
    cases g with
    | const c us =>
      cases us with
      | nil =>
        simp only [TrS_const, List.map_nil, ConLeche.Expr.natPred?, name_beq_eq_decide,
          toName_natSuccName]
        by_cases h : toName c = ConLeche.natSuccName <;> simp [h, TrO]
      | cons _ _ => rfl
    | fvar id =>
      rcases trans_getD_cases s id with ⟨i, ty, h⟩ | h <;>
        simp [TrS, trE, h, ConLeche.Expr.natPred?, TrO]
    | mdata m y => exact absurd rfl (hne m y)
    | app f' x' => cases (TrS s f') <;> rfl
    | _ => rfl
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h⟩ | h <;>
      simp [InLean.Expr.natPred?, TrS, trE, h, ConLeche.Expr.natPred?, TrO]
  | _ => rfl
grind_pattern [conleche_grind] natPredI_TrS => InLean.Expr.natPred? e, TrS s e

theorem okO_natPredI {e : Expr} (h : OkS s e = true) : OkO s (InLean.Expr.natPred? e) = true := by
  induction e with
  | mdata _ x ih => exact ih h
  | lit l =>
    cases l with
    | natVal n => cases n <;> rfl
    | strVal _ => rfl
  | app f x _ _ =>
    simp only [OkS_app, Bool.and_eq_true] at h
    simp only [InLean.Expr.natPred?]
    split
    · split
      · exact h.2
      · rfl
    · rfl
  | _ => rfl
grind_pattern [conleche_grind] okO_natPredI => OkS s e, InLean.Expr.natPred? e

theorem closed_natPred {e : ConLeche.Expr} (h : e.looseBVarsBounded 0 = true) :
    OptClosed e.natPred? = true := by
  unfold ConLeche.Expr.natPred?
  split
  · rfl
  · split
    · simp only [lbb_app] at h; simp only [OptClosed_some]; exact (Bool.and_eq_true _ _ ▸ h).2
    · rfl
  · rfl
grind_pattern [conleche_grind] closed_natPred => e.looseBVarsBounded 0, e.natPred?

theorem TrO_eq_some {o : Option Expr} {c : ConLeche.Expr} (h : TrO s o = some c) :
    ∃ x, o = some x := by
  cases o with
  | none => simp [TrO] at h
  | some x => exact ⟨x, rfl⟩
grind_pattern [conleche_grind] TrO_eq_some => TrO s o, some c

end Offsets

/-! ## Delta steps and the loop's outcome through the translation -/

section Steps
variable (s : InLean.CState)

/-- A lazy-delta step, translated. -/
@[expose] def TrDS : InLean.DeltaStep → ConLeche.DeltaStep
  | .cont a b => .cont (TrS s a) (TrS s b)
  | .eq => .eq
  | .diff => .diff
  | .unknown => .unknown

/-- A step's pair has a reading. -/
@[expose] def OkDS : InLean.DeltaStep → Bool
  | .cont a b => OkS s a && OkS s b
  | _ => true

@[conleche_grind =] theorem TrDS_cont (a b : Expr) :
    TrDS s (.cont a b) = .cont (TrS s a) (TrS s b) := rfl
@[conleche_grind =] theorem TrDS_eq : TrDS s .eq = .eq := rfl
@[conleche_grind =] theorem TrDS_diff : TrDS s .diff = .diff := rfl
@[conleche_grind =] theorem TrDS_unknown : TrDS s .unknown = .unknown := rfl
@[conleche_grind =] theorem OkDS_cont (a b : Expr) : OkDS s (.cont a b) = (OkS s a && OkS s b) :=
  rfl
@[conleche_grind =] theorem OkDS_eq : OkDS s .eq = true := rfl
@[conleche_grind =] theorem OkDS_diff : OkDS s .diff = true := rfl
@[conleche_grind =] theorem OkDS_unknown : OkDS s .unknown = true := rfl

/-- The loop's outcome, translated. -/
@[expose] def TrLR : InLean.LazyRes → ConLeche.LazyRes
  | .verdict v => .verdict v
  | .unknown a b => .unknown (TrS s a) (TrS s b)

/-- The outcome's pair has a reading. -/
@[expose] def OkLR : InLean.LazyRes → Bool
  | .verdict _ => true
  | .unknown a b => OkS s a && OkS s b

@[conleche_grind =] theorem TrLR_verdict (v : Bool) : TrLR s (.verdict v) = .verdict v := rfl
@[conleche_grind =] theorem TrLR_unknown (a b : Expr) :
    TrLR s (.unknown a b) = .unknown (TrS s a) (TrS s b) := rfl
@[conleche_grind =] theorem OkLR_verdict (v : Bool) : OkLR s (.verdict v) = true := rfl
@[conleche_grind =] theorem OkLR_unknown (a b : Expr) :
    OkLR s (.unknown a b) = (OkS s a && OkS s b) := rfl

end Steps

/-- A step's pair is closed. -/
@[expose] def StepClosedD : ConLeche.DeltaStep → Bool
  | .cont a b => a.looseBVarsBounded 0 && b.looseBVarsBounded 0
  | _ => true

@[conleche_grind =] theorem StepClosedD_cont (a b : ConLeche.Expr) :
    StepClosedD (.cont a b) = (a.looseBVarsBounded 0 && b.looseBVarsBounded 0) := rfl
@[conleche_grind =] theorem StepClosedD_eq : StepClosedD .eq = true := rfl
@[conleche_grind =] theorem StepClosedD_diff : StepClosedD .diff = true := rfl
@[conleche_grind =] theorem StepClosedD_unknown : StepClosedD .unknown = true := rfl

/-- The loop's stuck pair is closed. -/
@[expose] def LazyClosed : ConLeche.LazyRes → Bool
  | .unknown a b => a.looseBVarsBounded 0 && b.looseBVarsBounded 0
  | .verdict _ => true

@[conleche_grind =] theorem LazyClosed_unknown (a b : ConLeche.Expr) :
    LazyClosed (.unknown a b) = (a.looseBVarsBounded 0 && b.looseBVarsBounded 0) := rfl
@[conleche_grind =] theorem LazyClosed_verdict (v : Bool) : LazyClosed (.verdict v) = true := rfl

/-! ## The readers of the environment at use (O4's statements, P3's to prove)

What con-leche's lookups answer, as a function of the name (`ctorRd`,
`indRd`: the fields the certificates read), so that the pure side's
`match` on a lookup is a `match` on an `Option` InLean's reader maps to. -/

/-- What a certificate reads of a constructor's entry: its level
parameters and counts. -/
@[expose] def ctorRd (env : ConLeche.Env) (c : ConLeche.Name) :
    Option (List ConLeche.Name × Nat × Nat) :=
  match env.find? c with
  | some (.ctorInfo cv nP nF) => some (cv.levelParams, nP, nF)
  | _ => none

/-- What a certificate reads of an inductive former's entry. -/
structure IndGate where
  lps : List ConLeche.Name
  eta : Bool
  etaCtor : ConLeche.Name
  etaParams : Nat
  etaFields : Nat
  unitlike : Bool
  unitParams : Nat

/-- What a certificate reads of an inductive former's entry. -/
@[expose] def indRd (env : ConLeche.Env) (T : ConLeche.Name) : Option IndGate :=
  match env.find? T with
  | some (.indInfo cv caps) =>
    some ⟨cv.levelParams, caps.eta, caps.etaCtor, caps.etaParams, caps.etaFields, caps.unitlike,
      caps.unitParams⟩
  | _ => none

/-- InLean's constructor view, read as `ctorRd`. -/
@[expose] def ctorGateI (x : ConstantVal × Nat × Nat) : List ConLeche.Name × Nat × Nat :=
  (x.1.levelParams.map toName, x.2.1, x.2.2)

/-- InLean's former view, read as `indRd`. -/
@[expose] def indGateI (x : ConstantVal × InLean.IndCaps) : IndGate :=
  ⟨x.1.levelParams.map toName, x.2.eta, toName x.2.etaCtor, x.2.etaParams, x.2.etaFields,
    x.2.unitlike, x.2.unitParams⟩

/-- Lean's reducibility hints, read as con-leche's. -/
@[expose] def trHint : ReducibilityHints → ConLeche.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- The value `notProofFastM` answers at a state. -/
@[expose] def notProofFastV (fe : InLean.FEnv) (s : InLean.CState) (a : Expr) : Bool :=
  match proofPW fe (fvTyOf s.fvTys) a with
  | some pw => !pw.isProp
  | none => false

/-- The value `isProofFastM` answers at a state. -/
@[expose] def isProofFastV (fe : InLean.FEnv) (s : InLean.CState) (a : Expr) : Bool :=
  match proofPW fe (fvTyOf s.fvTys) a with
  | some pw => pw.isProp
  | none => false

/-- **The readers at use agree with con-leche's install** (O4, P3's): each
reader the definitional-equality family runs, at a term with a reading,
answers con-leche's reader at the translation. -/
structure DefeqEnvI (fe : InLean.FEnv) (env : ConLeche.Env) : Prop where
  notProof : ∀ s a, FVTableOK s → OkS s a = true →
    notProofFastV fe s a = ConLeche.notProofFast env.find? env.findTable? (TrS s a)
  isProof : ∀ s a, FVTableOK s → OkS s a = true →
    isProofFastV fe s a = ConLeche.isProofFast env.find? env.findTable? (TrS s a)
  etaShape : ∀ s a, OkS s a = true → etaCtorShapeC fe a = ConLeche.etaCtorShape env (TrS s a)
  unfoldable : ∀ s e, OkS s e = true →
    unfoldableHeadC fe e = ConLeche.unfoldableHead env (TrS s e)
  headHint : ∀ s e, OkS s e = true → trHint (headHintC fe e) = ConLeche.headHint env (TrS s e)
  strLit : strLitStoredF fe = ConLeche.strLitStored env
  towerSlots : ∀ T n, fe.towerSlotsAllF T n = ConLeche.towerSlotsAll env (toName T) n
  ctor : ∀ c, ctorRd env (toName c) = (fe.ctorView? c).map ctorGateI
  ind : ∀ T, indRd env (toName T) = (fe.indView? T).map indGateI

section EnvReaders

variable {fe : InLean.FEnv} {s : InLean.CState}

theorem notProofFastM_specI (hfe : DefeqEnvI fe env) (hs : CSOKI mode eager env s) {a : Expr}
    (ha : OkS s a = true) :
    ⦃fun s' => s' = s⦄ notProofFastM fe a
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s s' ∧
      v = ConLeche.notProofFast env.find? env.findTable? (TrS s a); ⊤⦄ := by
  refine tripleI_iff_run.2 fun v s' hr => ?_
  simp only [notProofFastM, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨hs, TabLe.refl _, hfe.notProof s a hs.fv ha⟩

theorem isProofFastM_specI (hfe : DefeqEnvI fe env) (hs : CSOKI mode eager env s) {a : Expr}
    (ha : OkS s a = true) :
    ⦃fun s' => s' = s⦄ isProofFastM fe a
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s s' ∧
      v = ConLeche.isProofFast env.find? env.findTable? (TrS s a); ⊤⦄ := by
  refine tripleI_iff_run.2 fun v s' hr => ?_
  simp only [isProofFastM, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨hs, TabLe.refl _, hfe.isProof s a hs.fv ha⟩

end EnvReaders

/-- `propIrrel` is its fast arms in front of `proofIrrel` (InLean's body
calls `proofIrrelI` where the pure one inlines it). -/
theorem propIrrel_eq {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (env : ConLeche.Env) (d : Nat) (a b : ConLeche.Expr) :
    ConLeche.propIrrel r env d a b =
      (if ConLeche.notProofFast env.find? env.findTable? a ||
          ConLeche.notProofFast env.find? env.findTable? b then pure false
        else if ConLeche.isProofFast env.find? env.findTable? a &&
          ConLeche.isProofFast env.find? env.findTable? b then pure true
        else ConLeche.proofIrrel r d a b) := rfl

section EnvReaders2

variable {fe : InLean.FEnv}

@[conleche_grind =] theorem optionMap_none {α β : Type} (f : α → β) : (none : Option α).map f = none :=
  rfl
@[conleche_grind =] theorem optionMap_some {α β : Type} (f : α → β) (x : α) :
    (some x).map f = some (f x) := rfl

theorem indRd_toName (hfe : DefeqEnvI fe env) (T : Name) :
    indRd env (toName T) = (fe.indView? T).map indGateI := hfe.ind T
grind_pattern [conleche_grind] indRd_toName => DefeqEnvI fe env, fe.indView? T

theorem ctorRd_toName (hfe : DefeqEnvI fe env) (c : Name) :
    ctorRd env (toName c) = (fe.ctorView? c).map ctorGateI := hfe.ctor c
grind_pattern [conleche_grind] ctorRd_toName => DefeqEnvI fe env, fe.ctorView? c

theorem towerSlots_toName (hfe : DefeqEnvI fe env) (T : Name) (n : Nat) :
    fe.towerSlotsAllF T n = ConLeche.towerSlotsAll env (toName T) n := hfe.towerSlots T n
grind_pattern [conleche_grind] towerSlots_toName => DefeqEnvI fe env, fe.towerSlotsAllF T n

theorem etaShape_TrS (hfe : DefeqEnvI fe env) {s : InLean.CState} {a : Expr}
    (h : OkS s a = true) : etaCtorShapeC fe a = ConLeche.etaCtorShape env (TrS s a) :=
  hfe.etaShape s a h
grind_pattern [conleche_grind] etaShape_TrS => DefeqEnvI fe env, OkS s a, etaCtorShapeC fe a

theorem strLit_eq (hfe : DefeqEnvI fe env) : strLitStoredF fe = ConLeche.strLitStored env :=
  hfe.strLit
grind_pattern [conleche_grind] strLit_eq => DefeqEnvI fe env, strLitStoredF fe

theorem unfoldable_TrS (hfe : DefeqEnvI fe env) {s : InLean.CState} {e : Expr}
    (h : OkS s e = true) : unfoldableHeadC fe e = ConLeche.unfoldableHead env (TrS s e) :=
  hfe.unfoldable s e h
grind_pattern [conleche_grind] unfoldable_TrS => DefeqEnvI fe env, OkS s e, unfoldableHeadC fe e

theorem headHint_TrS (hfe : DefeqEnvI fe env) {s : InLean.CState} {e : Expr}
    (h : OkS s e = true) : trHint (headHintC fe e) = ConLeche.headHint env (TrS s e) :=
  hfe.headHint s e h
grind_pattern [conleche_grind] headHint_TrS => DefeqEnvI fe env, OkS s e, headHintC fe e

@[conleche_grind =] theorem indGateI_mk (cv : ConstantVal) (caps : InLean.IndCaps) :
    indGateI (cv, caps) = ⟨cv.levelParams.map toName, caps.eta, toName caps.etaCtor,
      caps.etaParams, caps.etaFields, caps.unitlike, caps.unitParams⟩ := rfl

@[conleche_grind =] theorem ctorGateI_mk (cv : ConstantVal) (nP nF : Nat) :
    ctorGateI (cv, nP, nF) = (cv.levelParams.map toName, nP, nF) := rfl

end EnvReaders2

/-! ## Names and lists through the translation -/

section Lists

theorem contains_map_toName : ∀ (l : List Name) (n : Name),
    (l.map toName).contains (toName n) = l.contains n
  | [], _ => rfl
  | x :: l, n => by
    simp only [List.map_cons, List.contains_cons, contains_map_toName l n, cname_beq_eq_decide,
      name_beq_eq_decide]

theorem reservedBasisNames_eq :
    ConLeche.reservedBasisNames = InLean.reservedBasisNames.map toName := rfl

@[conleche_grind =] theorem reserved_contains (n : Name) :
    InLean.reservedBasisNames.contains n = ConLeche.reservedBasisNames.contains (toName n) := by
  rw [reservedBasisNames_eq, contains_map_toName]

theorem toName_map_inj : ∀ {a b : List Name}, a.map toName = b.map toName → a = b
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [toName_inj h.1, toName_map_inj h.2]

grind_pattern [conleche_grind] toName_map_inj => a.map toName, b.map toName
grind_pattern [conleche_grind] toName_inj => toName a, toName b

@[conleche_grind =] theorem length_map_trL (us : List Level) : (us.map trL).length = us.length :=
  List.length_map _
@[conleche_grind =] theorem length_map_toName (l : List Name) : (l.map toName).length = l.length :=
  List.length_map _

variable (s : InLean.CState)

theorem length_appArgs (e : Expr) : (appArgs e).length = (TrS s e).getAppArgs.length := by
  rw [← TrSL_appArgs, TrSL, List.length_map]
grind_pattern [conleche_grind] length_appArgs => (appArgs e).length, TrS s e

@[conleche_grind =] theorem TrSL_take (l : List Expr) (n : Nat) :
    TrSL s (l.take n) = (TrSL s l).take n := by simp [TrSL, List.map_take]
@[conleche_grind =] theorem TrSL_drop (l : List Expr) (n : Nat) :
    TrSL s (l.drop n) = (TrSL s l).drop n := by simp [TrSL, List.map_drop]
@[conleche_grind =] theorem TrSL_reverse (l : List Expr) :
    TrSL s l.reverse = (TrSL s l).reverse := by simp [TrSL, List.map_reverse]

theorem OkSL_take {l : List Expr} (h : OkSL s l = true) (n : Nat) : OkSL s (l.take n) = true := by
  simp only [OkSL, List.all_eq_true] at h ⊢; exact fun x hx => h x (List.mem_of_mem_take hx)
grind_pattern [conleche_grind] OkSL_take => OkSL s l, l.take n

theorem OkSL_drop {l : List Expr} (h : OkSL s l = true) (n : Nat) : OkSL s (l.drop n) = true := by
  simp only [OkSL, List.all_eq_true] at h ⊢; exact fun x hx => h x (List.mem_of_mem_drop hx)
grind_pattern [conleche_grind] OkSL_drop => OkSL s l, l.drop n

theorem OkSL_reverse {l : List Expr} (h : OkSL s l = true) : OkSL s l.reverse = true := by
  simp only [OkSL, List.all_eq_true, List.mem_reverse] at h ⊢; exact h
grind_pattern [conleche_grind] OkSL_reverse => OkSL s l, l.reverse

theorem AllClosed_take {l : List ConLeche.Expr} (h : AllClosed l = true) (n : Nat) :
    AllClosed (l.take n) = true := by
  simp only [AllClosed, List.all_eq_true] at h ⊢; exact fun x hx => h x (List.mem_of_mem_take hx)
grind_pattern [conleche_grind] AllClosed_take => AllClosed l, l.take n

theorem AllClosed_drop {l : List ConLeche.Expr} (h : AllClosed l = true) (n : Nat) :
    AllClosed (l.drop n) = true := by
  simp only [AllClosed, List.all_eq_true] at h ⊢; exact fun x hx => h x (List.mem_of_mem_drop hx)
grind_pattern [conleche_grind] AllClosed_drop => AllClosed l, l.drop n

theorem AllClosed_reverse {l : List ConLeche.Expr} (h : AllClosed l = true) :
    AllClosed l.reverse = true := by
  simp only [AllClosed, List.all_eq_true, List.mem_reverse] at h ⊢; exact h
grind_pattern [conleche_grind] AllClosed_reverse => AllClosed l, l.reverse

theorem TrSL_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {l : List Expr}
    (hl : OkSL s₀ l = true) : TrSL s₁ l = TrSL s₀ l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [OkSL_cons, Bool.and_eq_true] at hl
    simp only [TrSL_cons, TrS_of_tabLe h hl.1, ih hl.2]
grind_pattern [conleche_grind] TrSL_of_tabLe => TabLe s₀ s₁, TrSL s₁ l

theorem OkSL_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {l : List Expr}
    (hl : OkSL s₀ l = true) : OkSL s₁ l = true := by
  simp only [OkSL, List.all_eq_true] at hl ⊢; exact fun x hx => okS_of_tabLe h (hl x hx)
grind_pattern [conleche_grind] OkSL_of_tabLe => TabLe s₀ s₁, OkSL s₁ l

/-- The `.proj` spine (`projNodesC_spec`'s twin: InLean's is pure). -/
@[conleche_grind =] theorem TrSL_projNodes (T : Name) (b : Expr) (l : List Nat) :
    TrSL s (InLean.projNodesI T b l) = projsOf (toName T) (TrS s b) l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [InLean.projNodesI, TrSL_cons, ih, TrS_proj, projsOf_cons]

theorem OkSL_projNodes {b : Expr} (h : OkS s b = true) (T : Name) (l : List Nat) :
    OkSL s (InLean.projNodesI T b l) = true := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [InLean.projNodesI, OkSL_cons, OkS_proj, h, ih, Bool.and_self]
grind_pattern [conleche_grind] OkSL_projNodes => OkS s b, InLean.projNodesI T b l

theorem AllClosed_projsOf {b : ConLeche.Expr} (h : b.looseBVarsBounded 0 = true)
    (T : ConLeche.Name) (l : List Nat) : AllClosed (projsOf T b l) = true := by
  simp only [AllClosed, projsOf, List.all_map, List.all_eq_true, Function.comp_apply]
  exact fun _ _ => h
grind_pattern [conleche_grind] AllClosed_projsOf => b.looseBVarsBounded 0, projsOf T b l

end Lists

/-- `structUnitCert` with the former's lookup read through `indRd`. -/
theorem structUnitCert_eq {m : Type → Type} [Monad m] (r : ConLeche.CoreFns m)
    (env : ConLeche.Env) (d : Nat) (a b : ConLeche.Expr) :
    ConLeche.structUnitCert r env d a b = (do
      let ta ← r.inferIO d a
      let wta ← r.whnf d ta
      match wta.getAppFn with
      | .const T us' =>
        match indRd env T with
        | some g =>
          if g.unitlike = true ∧ ConLeche.reservedBasisNames.contains T = false ∧
              wta.getAppArgs.length = g.unitParams ∧ us'.length = g.lps.length then do
            let tb ← r.inferIO d b
            let wtb ← r.whnf d tb
            if wtb.isForallE then pure false else r.defeq d wta wtb
          else pure false
        | none => pure false
      | _ => pure false) := by
  unfold ConLeche.structUnitCert indRd
  refine congrArg (_ >>= ·) (funext fun ta => ?_)
  refine congrArg (_ >>= ·) (funext fun wta => ?_)
  cases wta.getAppFn with
  | const T us' =>
    dsimp only
    cases env.find? T with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

/-- `structEtaCertWith` with the lookups read through `ctorRd`/`indRd`. -/
theorem structEtaCertWith_eq {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (env : ConLeche.Env) (d : Nat) (a b wtb : ConLeche.Expr) :
    ConLeche.structEtaCertWith r env d a b wtb = (do
      match a.getAppFn with
      | .const c us =>
        match ctorRd env c with
        | some (clps, cnP, cnF) =>
          if a.getAppArgs.length = cnP + cnF then
            match wtb.getAppFn with
            | .const T us' =>
              match indRd env T with
              | some g =>
                if g.eta = true ∧ g.etaCtor = c ∧
                    ConLeche.reservedBasisNames.contains T = false ∧
                    ConLeche.reservedBasisNames.contains c = false ∧
                    wtb.getAppArgs.length = g.etaParams ∧
                    us'.length = g.lps.length ∧
                    clps = g.lps ∧
                    ConLeche.towerSlotsAll env T g.etaFields = true then
                  if ← ConLeche.liftFueled "level comparison"
                      (ConLeche.Level.isEquivList us us') then
                    if ← ConLeche.defEqList r env d
                        (a.getAppArgs.take g.etaParams) wtb.getAppArgs then
                      ConLeche.defEqList r env d
                        (a.getAppArgs.drop g.etaParams)
                        (ConLeche.etaProjs T b g.etaFields)
                    else pure false
                  else pure false
                else pure false
              | none => pure false
            | _ => pure false
          else pure false
        | none => pure false
      | _ => pure false : m Bool) := by
  unfold ConLeche.structEtaCertWith indRd ctorRd
  cases a.getAppFn with
  | const c us =>
    dsimp only
    cases env.find? c with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo cvc cnP cnF =>
        dsimp only
        split
        · cases wtb.getAppFn with
          | const T us' =>
            dsimp only
            cases env.find? T with
            | none => rfl
            | some ci' => cases ci' <;> rfl
          | _ => rfl
        · rfl
      | _ => rfl
  | _ => rfl

/-! ## Hints and same heads through the translation -/

theorem hintLt_trHint : ∀ (a b : ReducibilityHints),
    hintLt a b = ConLeche.ReducibilityHint.lt (trHint a) (trHint b)
  | .opaque, .opaque | .opaque, .abbrev | .opaque, .regular _ | .abbrev, .opaque
  | .abbrev, .abbrev | .abbrev, .regular _ | .regular _, .opaque | .regular _, .abbrev => rfl
  | .regular h₁, .regular h₂ => by
    simp only [hintLt, trHint, ConLeche.ReducibilityHint.lt, decide_eq_decide]
    exact UInt32.lt_iff_toNat_lt
grind_pattern [conleche_grind] hintLt_trHint => hintLt a b

theorem hintSameRegular_trHint : ∀ (a b : ReducibilityHints),
    hintSameRegular a b = ConLeche.ReducibilityHint.sameRegular (trHint a) (trHint b)
  | .opaque, _ | .abbrev, _ | .regular _, .opaque | .regular _, .abbrev => rfl
  | .regular h₁, .regular h₂ => by
    simp only [hintSameRegular, trHint, ConLeche.ReducibilityHint.sameRegular]
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact UInt32.toNat_inj.symm
grind_pattern [conleche_grind] hintSameRegular_trHint => hintSameRegular a b

theorem sameConstHeads_TrS (s : InLean.CState) (a b : Expr) :
    InLean.sameConstHeadsC a b = ConLeche.sameConstHeads (TrS s a) (TrS s b) := by
  unfold InLean.sameConstHeadsC
  rw [← TrS_stripTop s a, ← TrS_stripTop s b]
  have ha : ∀ m y, EO.stripTop a ≠ .mdata m y := fun m y h => stripTop_ne_mdata h
  have hb : ∀ m y, EO.stripTop b ≠ .mdata m y := fun m y h => stripTop_ne_mdata h
  generalize EO.stripTop a = x at ha
  generalize EO.stripTop b = y at hb
  cases x with
  | app f₁ a₁ =>
    cases y with
    | app f₂ a₂ =>
      simp only [TrS_app, ConLeche.sameConstHeads, ← TrS_getAppFnT]
      have h1 := (getAppFnT_shape f₁).1
      have h2 := (getAppFnT_shape f₂).1
      generalize Expr.getAppFnT f₁ = g₁ at h1
      generalize Expr.getAppFnT f₂ = g₂ at h2
      cases g₁ with
      | const n₁ _ =>
        cases g₂ with
        | const n₂ _ => simp only [TrS_const, name_beq_eq_decide, cname_beq_eq_decide]
        | fvar id =>
          rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h']
        | mdata m z => exact absurd rfl (h2 m z)
        | _ => rfl
      | fvar id =>
        rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;> simp [TrS, trE, h']
      | mdata m z => exact absurd rfl (h1 m z)
      | _ => rfl
    | fvar id =>
      rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;>
        simp [TrS, trE, h', ConLeche.sameConstHeads]
    | mdata m z => exact absurd rfl (hb m z)
    | _ => rfl
  | fvar id =>
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;>
      simp [TrS, trE, h', ConLeche.sameConstHeads]
  | mdata m z => exact absurd rfl (ha m z)
  | _ => rfl
grind_pattern [conleche_grind] sameConstHeads_TrS => InLean.sameConstHeadsC a b, TrS s a

/-! ## The callees P2-whnf owns, as named specs (`DiscC1`'s twins) -/

/-- `unfoldDefinitionI`'s spec (`unfoldDefinitionC_spec`'s twin), P2-whnf's to
prove. -/
abbrev UnfoldDefSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (fe : InLean.FEnv) : Prop :=
  ∀ {e : Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ → OkS s₀ e = true →
    (TrS s₀ e).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ unfoldDefinitionI fe e
    ⦃fun o s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      TrO s' o = ConLeche.unfoldDefinition env (TrS s₀ e) ∧ OptClosed (TrO s' o) = true; ⊤⦄

/-- `defeqSpineI`'s spec (`defeqSpineC_spec`'s twin), P2-whnf's to prove. -/
abbrev DefeqSpineSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (r : InLean.CoreFnsI) : Prop :=
  ∀ {d : Nat} {a b : Expr} {s₀ : InLean.CState},
    CSOKI mode eager env s₀ → OkS s₀ a = true → OkS s₀ b = true →
    ConLeche.Expr.WScoped d (TrS s₀ a) → ConLeche.Expr.WScoped d (TrS s₀ b) →
    (TrS s₀ a).looseBVarsBounded 0 = true → (TrS s₀ b).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ defeqSpineI r d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqSpine (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄

/-- `reduceNatI`'s spec (`reduceNatC_spec`'s twin), P2-whnf's to prove. -/
abbrev ReduceNatSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (r : InLean.CoreFnsI) (fe : InLean.FEnv) : Prop :=
  ∀ {d : Nat} {i : Expr} {s₀ : InLean.CState},
    CSOKI mode eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ reduceNatI r fe d i
    ⦃fun o s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (ConLeche.reduceNat (ConLeche.fueledFns mode eager env) env d (TrS s₀ i)) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true; ⊤⦄

/-- `defEqListI`'s spec (`defEqListC_spec`'s twin), P2-whnf's to prove. -/
abbrev DefEqListSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (r : InLean.CoreFnsI) : Prop :=
  ∀ {d : Nat} {args brgs : List Expr} {s₀ : InLean.CState},
    CSOKI mode eager env s₀ → OkSL s₀ args = true → OkSL s₀ brgs = true →
    AllWS d (TrSL s₀ args) → AllWS d (TrSL s₀ brgs) →
    AllClosed (TrSL s₀ args) = true → AllClosed (TrSL s₀ brgs) = true →
    ⦃fun s => s = s₀⦄ defEqListI r d args brgs
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defEqList (ConLeche.fueledFns mode eager env) env d (TrSL s₀ args)
        (TrSL s₀ brgs)) v; ⊤⦄

/-! ## DiscC2's twins: the stuck-term certificates -/

section Walks

variable {r : InLean.CoreFnsI}

/-- The eq-true shortcut (`boolTrueShortcutC_spec`'s twin). -/
theorem boolTrueShortcutI_spec (ih : KnotSpecI mode eager env r) {d : Nat} {a : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ a = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ a)) (hc : (TrS s₀ a).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ boolTrueShortcutI r d a
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.boolTrueShortcut (ConLeche.fueledFns mode eager env) d (TrS s₀ a)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.boolTrueShortcut] =>
    vcgen [InLean.boolTrueShortcutI, ih.whnf hs hok hw hc] <;> finish

/-- `proofIrrelI` (`proofIrrelC_spec`'s twin). -/
theorem proofIrrelI_spec (ih : KnotSpecI mode eager env r) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.proofIrrelI r d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.proofIrrel (ConLeche.fueledFns mode eager env) d (TrS s₀ a) (TrS s₀ b)) v;
        ⊤⦄ := by
  sym only [conleche_grind, ConLeche.proofIrrel] =>
    vcgen [InLean.proofIrrelI, ih.inferIO, ih.whnf, isEquivLM_specI (mode := mode) (eager := eager)
        (env := env), liftFueled_specI (mode := mode) (eager := eager) (env := env)] <;>
      -- the pure side is nine binds deep, one `Runs.bind_eq` generation each
      finish (gen := 12)

/-- The hoisted `Prop`-branch test (`propIrrelC_spec`'s twin). -/
theorem propIrrelI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode eager env r)
    (hfe : DefeqEnvI fe env) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.propIrrelI r fe d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.propIrrel (ConLeche.fueledFns mode eager env) env d (TrS s₀ a) (TrS s₀ b)) v;
        ⊤⦄ := by
  sym only [conleche_grind, propIrrel_eq] =>
    vcgen [InLean.propIrrelI, notProofFastM_specI (mode := mode) (eager := eager) hfe,
      isProofFastM_specI (mode := mode) (eager := eager) hfe,
      proofIrrelI_spec ih] <;> finish

/-- `etaCertI` (`etaCertC_spec`'s twin). -/
theorem etaCertI_spec (ih : KnotSpecI .verified eager env r) {d : Nat} {ty₁ body₁ b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hokt : OkS s₀ ty₁ = true)
    (hokbody : OkS s₀ body₁ = true) (hokb : OkS s₀ b = true)
    (hwty : ConLeche.Expr.WScoped d (TrS s₀ ty₁)) (hwbody : ConLeche.Expr.WScoped d (TrS s₀ body₁))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hct : (TrS s₀ ty₁).looseBVarsBounded 0 = true)
    (hcbody : (TrS s₀ body₁).looseBVarsBounded 1 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.etaCertI .verified r d ty₁ body₁ b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.etaCert .verified (ConLeche.fueledFns .verified eager env) env d (TrS s₀ ty₁)
        (TrS s₀ body₁) (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.etaCert] =>
    vcgen [InLean.etaCertI, ih.inferIO, ih.whnf, ih.defeq, ih.infer,
      mkFVarM_specI (mode := .verified) (eager := eager) (env := env)] <;>
      -- the verified arm is seven binds deep, one `Runs.bind_eq` generation each
      finish (gen := 10)

/-- `structUnitCertI` (`structUnitCertC_spec`'s twin). -/
theorem structUnitCertI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode eager env r)
    (hfe : DefeqEnvI fe env) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.structUnitCertI r fe d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.structUnitCert (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, structUnitCert_eq] =>
    vcgen [InLean.structUnitCertI, ih.inferIO, ih.whnf, ih.defeq] <;>
      -- the pure side is eight binds and matches deep, one generation each, and
      -- the translation's head (`getAppFnT`) adds two more
      finish (gen := 12)

/-- `structEtaCertWithI` (`structEtaCertWithC_spec`'s twin). -/
theorem structEtaCertWithI_spec {fe : InLean.FEnv} (hfe : DefeqEnvI fe env)
    (hlist : DefEqListSpecI mode eager env r) {d : Nat} {a b wtb : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hokw : OkS s₀ wtb = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hww : ConLeche.Expr.WScoped d (TrS s₀ wtb))
    (hca : (TrS s₀ a).looseBVarsBounded 0 = true) (hcb : (TrS s₀ b).looseBVarsBounded 0 = true)
    (hcw : (TrS s₀ wtb).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.structEtaCertWithI r fe d a b wtb
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.structEtaCertWith (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b) (TrS s₀ wtb)) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaCertWith_eq] =>
    vcgen [InLean.structEtaCertWithI, isEquivListLM_specI (mode := mode) (eager := eager)
        (env := env), liftFueled_specI (mode := mode) (eager := eager) (env := env), hlist] <;>
      -- two lookups and two spine heads deep before the first bind, one generation each
      finish (gen := 12)

/-- `structEtaCertI` (`structEtaCertC_spec`'s twin). -/
theorem structEtaCertI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode eager env r)
    (hfe : DefeqEnvI fe env) (hlist : DefEqListSpecI mode eager env r) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.structEtaCertI r fe d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.structEtaCert (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.structEtaCert] =>
    vcgen [InLean.structEtaCertI, ih.inferIO, ih.whnf, structEtaCertWithI_spec hfe hlist] <;>
      finish

/-- `stuckIrrelI` (`stuckIrrelC_spec`'s twin). -/
theorem stuckIrrelI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode eager env r)
    (hfe : DefeqEnvI fe env) (hlist : DefEqListSpecI mode eager env r) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.stuckIrrelI r fe d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.stuckIrrel (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.stuckIrrel] =>
    vcgen [InLean.stuckIrrelI, structEtaCertI_spec ih hfe hlist, structUnitCertI_spec ih hfe,
      proofIrrelI_spec ih] <;> finish

end Walks

/-! ## DiscC5's twins: definitional equality -/

section Walks5

variable {r : InLean.CoreFnsI}

/-- The innermost level of the λ-telescope comparison
(`defeqLamsInnerC_spec`'s twin). -/
theorem defeqLamsInnerI_spec (ih : KnotSpecI .verified eager env r) {d : Nat} {b₁ b₂ : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hok1 : OkS s₀ b₁ = true)
    (hok2 : OkS s₀ b₂ = true) (h1 : ConLeche.Expr.WScoped (d + 1) (TrS s₀ b₁))
    (h2 : ConLeche.Expr.WScoped (d + 1) (TrS s₀ b₂)) (hc1 : (TrS s₀ b₁).looseBVarsBounded 0 = true)
    (hc2 : (TrS s₀ b₂).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqLamsInnerI .verified r d b₁ b₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqLamsInner .verified (ConLeche.fueledFns .verified eager env) d
        (TrS s₀ b₁) (TrS s₀ b₂)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqLamsInner] =>
    vcgen [InLean.defeqLamsInnerI, ih.defeq, ih.infer] <;> finish

/-- InLean's λ-telescope comparison past the opened bodies (`lamsStepI`'s
twin). -/
@[expose] def lamsStepL (r : InLean.CoreFnsI) (n d : Nat) (b₁ b₂ : Expr) : InLean.CheckCM Bool :=
  match InLean.Expr.lamPair? b₁ b₂ with
  | some q =>
    if b₁ == b₂ then pure true
    else InLean.defeqLamsI .verified r n (d + 1) q.1 q.2.1 q.2.2.1 q.2.2.2
  | none => InLean.defeqLamsInnerI .verified r d b₁ b₂

theorem defeqLamsL_zero (r : InLean.CoreFnsI) (d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) :
    InLean.defeqLamsI .verified r 0 d ty₁ body₁ ty₂ body₂ = (do
      unless ← r.defeq d ty₁ ty₂ do return false
      let fv ← mkFVarM d ty₂
      InLean.defeqLamsInnerI .verified r d (body₁.inst1I fv) (body₂.inst1I fv) :
        InLean.CheckCM Bool) := rfl

set_option smartUnfolding false in
/-- `defeqLamsI`'s step (as `defeqLamsI_succ`: the structural recursion sits
under the binds, where no equation is generated). -/
theorem defeqLamsL_succ (r : InLean.CoreFnsI) (n d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) :
    InLean.defeqLamsI .verified r (n + 1) d ty₁ body₁ ty₂ body₂ = (do
      unless ← r.defeq d ty₁ ty₂ do return false
      let fv ← mkFVarM d ty₂
      lamsStepL r n d (body₁.inst1I fv) (body₂.inst1I fv) : InLean.CheckCM Bool) := by
  refine congrArg (r.defeq d ty₁ ty₂ >>= ·) (funext fun x => ?_)
  cases x
  · rfl
  · refine congrArg (mkFVarM d ty₂ >>= ·) (funext fun fv => ?_)
    unfold lamsStepL
    dsimp only
    cases InLean.Expr.lamPair? (body₁.inst1I fv) (body₂.inst1I fv) <;> rfl

/-- The λ-telescope comparison at fuel `n` (`LamsSpec`'s twin, a named
predicate: an atom in `grind`'s context). -/
@[expose] def LamsSpecI (eager : Bool) (env : ConLeche.Env) (r : InLean.CoreFnsI) (n : Nat) :
    Prop :=
  ∀ {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : InLean.CState}, CSOKI .verified eager env s₀ →
    OkS s₀ ty₁ = true → OkS s₀ body₁ = true → OkS s₀ ty₂ = true → OkS s₀ body₂ = true →
    ConLeche.Expr.WScoped d (TrS s₀ ty₁) → ConLeche.Expr.WScoped d (TrS s₀ body₁) →
    ConLeche.Expr.WScoped d (TrS s₀ ty₂) → ConLeche.Expr.WScoped d (TrS s₀ body₂) →
    (TrS s₀ ty₁).looseBVarsBounded 0 = true → (TrS s₀ body₁).looseBVarsBounded 1 = true →
    (TrS s₀ ty₂).looseBVarsBounded 0 = true → (TrS s₀ body₂).looseBVarsBounded 1 = true →
    ⦃fun s => s = s₀⦄ InLean.defeqLamsI .verified r n d ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqLams .verified (ConLeche.fueledFns .verified eager env) n d (TrS s₀ ty₁)
        (TrS s₀ body₁) (TrS s₀ ty₂) (TrS s₀ body₂)) v; ⊤⦄

theorem LamsSpecI.triple {n : Nat} (h : LamsSpecI eager env r n) {d : Nat}
    {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (o1 : OkS s₀ ty₁ = true) (o2 : OkS s₀ body₁ = true) (o3 : OkS s₀ ty₂ = true)
    (o4 : OkS s₀ body₂ = true)
    (w1 : ConLeche.Expr.WScoped d (TrS s₀ ty₁)) (w2 : ConLeche.Expr.WScoped d (TrS s₀ body₁))
    (w3 : ConLeche.Expr.WScoped d (TrS s₀ ty₂)) (w4 : ConLeche.Expr.WScoped d (TrS s₀ body₂))
    (c1 : (TrS s₀ ty₁).looseBVarsBounded 0 = true) (c2 : (TrS s₀ body₁).looseBVarsBounded 1 = true)
    (c3 : (TrS s₀ ty₂).looseBVarsBounded 0 = true) (c4 : (TrS s₀ body₂).looseBVarsBounded 1 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqLamsI .verified r n d ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqLams .verified (ConLeche.fueledFns .verified eager env) n d (TrS s₀ ty₁)
        (TrS s₀ body₁) (TrS s₀ ty₂) (TrS s₀ body₂)) v; ⊤⦄ :=
  h hs o1 o2 o3 o4 w1 w2 w3 w4 c1 c2 c3 c4

theorem lamsStepL_spec (ih : KnotSpecI .verified eager env r) {n : Nat} (hn : LamsSpecI eager env r n)
    {d : Nat} {b₁ b₂ : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hok1 : OkS s₀ b₁ = true) (hok2 : OkS s₀ b₂ = true)
    (h1 : ConLeche.Expr.WScoped (d + 1) (TrS s₀ b₁)) (h2 : ConLeche.Expr.WScoped (d + 1) (TrS s₀ b₂))
    (hc1 : (TrS s₀ b₁).looseBVarsBounded 0 = true) (hc2 : (TrS s₀ b₂).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ lamsStepL r n d b₁ b₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (lamsStepP (ConLeche.fueledFns .verified eager env) .verified n d (TrS s₀ b₁)
        (TrS s₀ b₂)) v; ⊤⦄ := by
  sym only [conleche_grind, lamsStepP] =>
    vcgen [lamsStepL, defeqLamsInnerI_spec ih, hn.triple] <;> finish

/-- By induction on the descent budget (`lamsSpec_all`'s twin). -/
theorem lamsSpecI_all (ih : KnotSpecI .verified eager env r) (fuel : Nat) :
    LamsSpecI eager env r fuel := by
  induction fuel with
  | zero =>
    intro d ty₁ body₁ ty₂ body₂ s₀ hs _ _ _ _ _ _ _ _ _ _ _ _
    sym only [conleche_grind, defeqLams_zero] =>
      vcgen [defeqLamsL_zero, ih.defeq, mkFVarM_specI (mode := .verified) (eager := eager)
          (env := env), defeqLamsInnerI_spec ih] <;> finish
  | succ n ihn =>
    intro d ty₁ body₁ ty₂ body₂ s₀ hs _ _ _ _ _ _ _ _ _ _ _ _
    sym only [conleche_grind, defeqLams_succ] =>
      vcgen [defeqLamsL_succ, ih.defeq, mkFVarM_specI (mode := .verified) (eager := eager)
          (env := env), lamsStepL_spec ih ihn] <;> finish

/-- The easy cases (`quickDefEqC_spec`'s twin). -/
theorem quickDefEqI_spec (ih : KnotSpecI .verified eager env r) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.quickDefEqI .verified r d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.quickDefEq .verified (ConLeche.fueledFns .verified eager env) d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.quickDefEq.eq_def, lamsFuel_eq] =>
    vcgen [InLean.quickDefEqI, ih.defeq, mkFVarM_specI (mode := .verified) (eager := eager)
        (env := env), isEquivLM_specI (mode := .verified) (eager := eager) (env := env),
      liftFueled_specI (mode := .verified) (eager := eager) (env := env),
      LamsSpecI.triple (lamsSpecI_all ih InLean.lamsFuel)] <;> finish

/-- Offsets (`defeqOffsetC_spec`'s twin). -/
theorem defeqOffsetI_spec (ih : KnotSpecI mode eager env r) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqOffsetI r d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqOffset (ConLeche.fueledFns mode eager env) d (TrS s₀ a) (TrS s₀ b)) v;
        ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqOffset] =>
    vcgen [InLean.defeqOffsetI, ih.defeq] <;> finish

/-- `try_unfold_proj_app` (`tryUnfoldProjAppC_spec`'s twin). -/
theorem tryUnfoldProjAppI_spec (ih : KnotSpecI mode eager env r) {d : Nat} {e : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ e)) (hc : (TrS s₀ e).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.tryUnfoldProjAppI r d e
    ⦃fun o s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (ConLeche.tryUnfoldProjApp (ConLeche.fueledFns mode eager env) d (TrS s₀ e)) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.tryUnfoldProjApp] =>
    vcgen [InLean.tryUnfoldProjAppI, ih.whnfCore] <;> finish

/-- The end of a step (`deltaQuickC_spec`'s twin). -/
theorem deltaQuickI_spec (ih : KnotSpecI .verified eager env r) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.deltaQuickI .verified r d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkDS s' v = true ∧
      Runs (ConLeche.deltaQuick .verified (ConLeche.fueledFns .verified eager env) d (TrS s₀ a)
        (TrS s₀ b)) (TrDS s' v) ∧
      StepPairWS d (TrDS s' v) ∧ StepClosedD (TrDS s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.deltaQuick] =>
    vcgen [InLean.deltaQuickI, quickDefEqI_spec ih] <;> finish

/-- One lazy-delta step (`lazyDeltaStepC_spec`'s twin). -/
theorem lazyDeltaStepI_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified eager env r)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified eager env r)
    {d : Nat} {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.lazyDeltaStepI .verified r fe d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkDS s' v = true ∧
      Runs (ConLeche.lazyDeltaStep .verified (ConLeche.fueledFns .verified eager env) env d
        (TrS s₀ a) (TrS s₀ b)) (TrDS s' v) ∧
      StepPairWS d (TrDS s' v) ∧ StepClosedD (TrDS s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.lazyDeltaStep, ConLeche.unfoldDefinition_WScoped henv] =>
    vcgen [InLean.lazyDeltaStepI, tryUnfoldProjAppI_spec ih, deltaQuickI_spec ih, ih.whnfCore,
      hunf, hspine] <;> finish

/-! The lazy-delta loop's continuations, named as the pure ones are
(`ldr…P`, `DiscC5.lean`), each block its own triple. -/

/-- Past the step. -/
@[expose] def ldrStepL (eager : Bool) (r : InLean.CoreFnsI) (fe : InLean.FEnv) (d n : Nat)
    (a b : Expr) : InLean.DeltaStep → InLean.CheckCM InLean.LazyRes
  | .cont a' b' => InLean.lazyDeltaReductionI .verified eager r fe d n a' b'
  | .eq => pure (.verdict true)
  | .diff => pure (.verdict false)
  | .unknown => pure (.unknown a b)

/-- Past the right literal acceleration. -/
@[expose] def ldrNatBL (eager : Bool) (r : InLean.CoreFnsI) (fe : InLean.FEnv) (d n : Nat)
    (a b : Expr) : Option Expr → InLean.CheckCM InLean.LazyRes
  | some b₂ => do
    let v ← r.defeq d a b₂
    pure (.verdict v)
  | none => InLean.lazyDeltaStepI .verified r fe d a b >>= ldrStepL eager r fe d n a b

/-- Past the left literal acceleration. -/
@[expose] def ldrNatAL (eager : Bool) (r : InLean.CoreFnsI) (fe : InLean.FEnv) (d n : Nat)
    (a b : Expr) (fold : Bool) : Option Expr → InLean.CheckCM InLean.LazyRes
  | some a₂ => do
    let v ← r.defeq d a₂ b
    pure (.verdict v)
  | none =>
    (if fold then InLean.reduceNatI r fe d b else pure none) >>= ldrNatBL eager r fe d n a b

/-- Past the offset check. -/
@[expose] def ldrOffL (eager : Bool) (r : InLean.CoreFnsI) (fe : InLean.FEnv) (d n : Nat)
    (a b : Expr) : Option Bool → InLean.CheckCM InLean.LazyRes
  | some v => pure (.verdict v)
  | none =>
    (if eager || (!a.hasFVar && !b.hasFVar) then InLean.reduceNatI r fe d a else pure none) >>=
      ldrNatAL eager r fe d n a b (eager || (!a.hasFVar && !b.hasFVar))

/-- The loop's step with its continuations named. -/
theorem lazyDeltaReductionL_succ (r : InLean.CoreFnsI) (fe : InLean.FEnv) (d n : Nat)
    (a b : Expr) :
    InLean.lazyDeltaReductionI .verified eager r fe d (n + 1) a b =
      InLean.defeqOffsetI r d a b >>= ldrOffL eager r fe d n a b := by
  rw [InLean.lazyDeltaReductionI.eq_2]; rfl

/-- The lazy-delta loop at budget `n` (`LazySpec`'s twin, a named predicate). -/
@[expose] def LazySpecI (eager : Bool) (env : ConLeche.Env) (r : InLean.CoreFnsI)
    (fe : InLean.FEnv) (d n : Nat) : Prop :=
  ∀ {a b : Expr} {s₀ : InLean.CState}, CSOKI .verified eager env s₀ →
    OkS s₀ a = true → OkS s₀ b = true →
    ConLeche.Expr.WScoped d (TrS s₀ a) → ConLeche.Expr.WScoped d (TrS s₀ b) →
    (TrS s₀ a).looseBVarsBounded 0 = true → (TrS s₀ b).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.lazyDeltaReductionI .verified eager r fe d n a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ConLeche.lazyDeltaReduction .verified eager (ConLeche.fueledFns .verified eager env)
        env d n (TrS s₀ a) (TrS s₀ b)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄

theorem LazySpecI.triple {fe : InLean.FEnv} {d n : Nat} (h : LazySpecI eager env r fe d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.lazyDeltaReductionI .verified eager r fe d n a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ConLeche.lazyDeltaReduction .verified eager (ConLeche.fueledFns .verified eager env)
        env d n (TrS s₀ a) (TrS s₀ b)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ :=
  h hs hoka hokb hwa hwb hca hcb

theorem ldrStepL_spec {fe : InLean.FEnv} {d n : Nat} (hn : LazySpecI eager env r fe d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (st : InLean.DeltaStep)
    (hok : OkDS s₀ st = true) (hst : StepPairWS d (TrDS s₀ st))
    (hcst : StepClosedD (TrDS s₀ st) = true) :
    ⦃fun s => s = s₀⦄ ldrStepL eager r fe d n a b st
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ldrStepP (ConLeche.fueledFns .verified eager env) env d .verified eager n (TrS s₀ a)
        (TrS s₀ b) (TrDS s₀ st)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ldrStepP] =>
    vcgen [ldrStepL, LazySpecI.triple hn] <;> finish

theorem ldrNatBL_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified eager env r)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified eager env r)
    {d n : Nat} (hn : LazySpecI eager env r fe d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (o : Option Expr) (hok : OkO s₀ o = true)
    (ho : OptWS d (TrO s₀ o)) (hco : OptClosed (TrO s₀ o) = true) :
    ⦃fun s => s = s₀⦄ ldrNatBL eager r fe d n a b o
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ldrNatBP (ConLeche.fueledFns .verified eager env) env d .verified eager n (TrS s₀ a)
        (TrS s₀ b) (TrO s₀ o)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ldrNatBP] =>
    vcgen [ldrNatBL, ih.defeq, lazyDeltaStepI_spec ih hfe henv hunf hspine, ldrStepL_spec hn] <;>
      finish

theorem ldrNatAL_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified eager env r)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified eager env r)
    (hnat : ReduceNatSpecI .verified eager env r fe)
    {d n : Nat} (hn : LazySpecI eager env r fe d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (o : Option Expr) (hok : OkO s₀ o = true)
    (ho : OptWS d (TrO s₀ o)) (hco : OptClosed (TrO s₀ o) = true) :
    ⦃fun s => s = s₀⦄ ldrNatAL eager r fe d n a b (eager || (!a.hasFVar && !b.hasFVar)) o
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ldrNatAP (ConLeche.fueledFns .verified eager env) env d .verified eager n (TrS s₀ a)
        (TrS s₀ b) (TrO s₀ o)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ldrNatAP] =>
    vcgen [ldrNatAL, ih.defeq, hnat, ldrNatBL_spec ih hfe henv hunf hspine hn] <;> finish

theorem ldrOffL_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified eager env r)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified eager env r)
    (hnat : ReduceNatSpecI .verified eager env r fe)
    {d n : Nat} (hn : LazySpecI eager env r fe d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (o : Option Bool) :
    ⦃fun s => s = s₀⦄ ldrOffL eager r fe d n a b o
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ldrOffP (ConLeche.fueledFns .verified eager env) env d .verified eager n (TrS s₀ a)
        (TrS s₀ b) o) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ldrOffP] =>
    vcgen [ldrOffL, hnat, ldrNatAL_spec ih hfe henv hunf hspine hnat hn] <;> finish

/-- By induction on the step budget (`lazySpec_all`'s twin). -/
theorem lazySpecI_all {fe : InLean.FEnv} (ih : KnotSpecI .verified eager env r)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified eager env r)
    (hnat : ReduceNatSpecI .verified eager env r fe) {d : Nat} (n : Nat) :
    LazySpecI eager env r fe d n := by
  induction n with
  | zero =>
    intro a b s₀ hs _ _ _ _ _ _
    sym only [conleche_grind] => vcgen [InLean.lazyDeltaReductionI] <;> finish
  | succ n ihn =>
    intro a b s₀ hs _ _ _ _ _ _
    sym only [conleche_grind, lazyDeltaReduction_succ] =>
      vcgen [lazyDeltaReductionL_succ, defeqOffsetI_spec ih,
        ldrOffL_spec ih hfe henv hunf hspine hnat ihn] <;> finish

end Walks5

end InLeanProof
