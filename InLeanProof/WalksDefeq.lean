module

public import InLeanProof.StateOpsI
public import ConLeche.Verify.Cached.DiscC5
public import InLeanProof.WalksIota
import InLeanProof.WalksIotaRec

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

variable {mode : ConLeche.CheckMode} {mi : InLean.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Vocabulary: the term readers through the translation -/

section Readers

variable (s : InLean.CState)

@[conleche_grind =] theorem toName_boolTrueName :
    toName InLean.boolTrueName = ConLeche.boolTrueName := rfl
@[conleche_grind =] theorem toName_natZeroName :
    toName InLean.natZeroName = ConLeche.natZeroName := rfl
@[conleche_grind =] theorem toName_natSuccName :
    toName InLean.natSuccName = ConLeche.natSuccName := rfl

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

theorem okL_of_okLv_level {u : Level} (h : okLv u = true) : okL u = true := by
  simp only [okLv, Bool.and_eq_true] at h; exact h.1
grind_pattern [conleche_grind] okL_of_okLv_level => okLv u

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

/-- The head of a spine: a constant on both sides, or a constant on neither. -/
theorem head_cases (s : InLean.CState) (e : Expr) :
    (∃ n us, Expr.getAppFnT e = .const n us ∧ (TrS s e).getAppFn = .const (toName n) (us.map trL)) ∨
    ((∀ n us, Expr.getAppFnT e ≠ .const n us) ∧ ∀ cn cus, (TrS s e).getAppFn ≠ .const cn cus) := by
  rw [← TrS_getAppFnT]
  generalize hx : Expr.getAppFnT e = x
  cases x with
  | const n us => exact .inl ⟨n, us, rfl, rfl⟩
  | mdata m y => exact (getAppFnT_ne_mdata hx).elim
  | _ =>
    right
    refine ⟨fun _ _ h => Expr.noConfusion h, fun cn cus h => ?_⟩
    obtain ⟨n', us', h'⟩ := stripTop_of_TrS_const s h
    simp [EO.stripTop] at h'

/-- The spine's argument count through the translation. -/
theorem numArgs_TrS {s : InLean.CState} {e : Expr} (h : OkS s e = true) :
    Expr.getAppNumArgsT e = (TrS s e).getAppArgs.length :=
  getAppNumArgsT_eq (FVarTable.trans_fvarsOnly _) e _ (TransS_of_ok h)

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
  have h := clEq_iff_TransS hs (RangeOk_of_OkS ha) (RangeOk_of_OkS hb) (TransS_of_ok ha) (b := b)
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

@[conleche_grind =] theorem lit_beq_toLit (a b : Literal) :
    Literal.beqI a b = (toLit a == toLit b) := by
  cases a <;> cases b <;> simp only [Literal.beqI, toLit] <;> rw [Bool.eq_iff_iff] <;> simp

theorem bindersFuel_eq : InLean.bindersFuel = ConLeche.bindersFuel := by
  unfold InLean.bindersFuel ConLeche.bindersFuel; rfl
theorem defeqLoopFuel_eq : InLean.defeqLoopFuel = ConLeche.defeqLoopFuel := by
  unfold InLean.defeqLoopFuel ConLeche.defeqLoopFuel; rfl

end Eq

section BinderPair
variable (s : InLean.CState)

theorem stripTop_of_ne_mdata {x : Expr} (h : ∀ (m : MData) (y : Expr), x = .mdata m y → False) :
    EO.stripTop x = x := by
  cases x with
  | mdata m y => exact absurd rfl (h m y)
  | _ => rfl

/-- A pair of binders, read through `mdata`, translates to the translations'
pair. -/
theorem binderPairI_some (lam : Bool) (a b : Expr) : ∀ {q : Expr × Expr × Expr × Expr},
    InLean.Expr.binderPair? lam a b = some q →
    OkS s a = (OkS s q.1 && OkS s q.2.1) ∧ OkS s b = (OkS s q.2.2.1 && OkS s q.2.2.2) ∧
      ConLeche.Expr.binderPair? lam (TrS s a) (TrS s b) =
        some (TrS s q.1, TrS s q.2.1, TrS s q.2.2.1, TrS s q.2.2.2) := by
  induction a, b using InLean.Expr.binderPair?.induct lam with
  | case1 _ a b ih => intro q h; rw [InLean.Expr.binderPair?] at h; exact ih h
  | case2 a _ b hna ih =>
    intro q h; rw [InLean.Expr.binderPair?.eq_2 _ _ _ _ hna] at h; exact ih h
  | case3 _ _ _ _ _ _ _ _ hl =>
    intro q h; simp only [InLean.Expr.binderPair?, hl, ↓reduceIte, Option.some.injEq] at h; subst h
    subst hl
    exact ⟨rfl, rfl, rfl⟩
  | case4 _ _ _ _ _ _ _ _ hl =>
    intro q h; simp [InLean.Expr.binderPair?, hl] at h
  | case5 _ _ _ _ _ _ _ _ hl =>
    intro q h; simp [InLean.Expr.binderPair?, hl] at h
  | case6 _ _ _ _ _ _ _ _ hl =>
    intro q h; simp only [InLean.Expr.binderPair?, hl, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq] at h; subst h
    simp only [Bool.not_eq_true] at hl; subst hl
    exact ⟨rfl, rfl, rfl⟩
  | case7 x y h1 h2 h3 h4 =>
    intro q h; rw [InLean.Expr.binderPair?.eq_5 _ _ _ h1 h2 h3 h4] at h; simp at h

theorem binderPairI_none (lam : Bool) (a b : Expr) : InLean.Expr.binderPair? lam a b = none →
    ConLeche.Expr.binderPair? lam (TrS s a) (TrS s b) = none := by
  induction a, b using InLean.Expr.binderPair?.induct lam with
  | case1 _ a b ih => intro h; rw [InLean.Expr.binderPair?] at h; exact ih h
  | case2 a _ b hna ih =>
    intro h; rw [InLean.Expr.binderPair?.eq_2 _ _ _ _ hna] at h; exact ih h
  | case3 _ _ _ _ _ _ _ _ hl => intro h; simp [InLean.Expr.binderPair?, hl] at h
  | case4 _ _ _ _ _ _ _ _ hl =>
    intro _; simp only [Bool.not_eq_true] at hl; subst hl; rfl
  | case5 _ _ _ _ _ _ _ _ hl => intro _; subst hl; rfl
  | case6 _ _ _ _ _ _ _ _ hl => intro h; simp [InLean.Expr.binderPair?, hl] at h
  | case7 x y h1 h2 h3 h4 =>
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
      | _ => cases lam <;> rfl
    | forallE t b =>
      obtain ⟨n, t', b', bi, hx'⟩ := stripTop_of_TrS_forallE s hx
      rw [stripTop_of_ne_mdata h1] at hx'
      cases hy : TrS s y with
      | forallE t₂ b₂ =>
        obtain ⟨n₂, t₂', b₂', bi₂, hy'⟩ := stripTop_of_TrS_forallE s hy
        rw [stripTop_of_ne_mdata h2] at hy'
        exact (h4 _ _ _ _ _ _ _ _ hx' hy').elim
      | _ => cases lam <;> rfl
    | _ => cases lam <;> rfl

end BinderPair

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

/-! ## String literals and free variables in the stuck comparison -/

section Stuck
variable (s : InLean.CState)

theorem strLitList_TrS : ∀ cs : List Char,
    TrS s (cs.foldr (init := .app (.const listNilName [.zero]) (.const charName []))
      fun c e => .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e) =
      cs.foldr (init := .app (.const ConLeche.listNilName [.zero]) (.const ConLeche.charName []))
        (fun c e => .app (.app (.app (.const ConLeche.listConsName [.zero])
          (.const ConLeche.charName []))
          (.app (.const ConLeche.charOfNatName []) (.lit (.natVal c.toNat)))) e) ∧
    OkS s (cs.foldr (init := .app (.const listNilName [.zero]) (.const charName []))
      fun c e => .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e) = true
  | [] => ⟨rfl, rfl⟩
  | c :: cs => by
    obtain ⟨h1, h2⟩ := strLitList_TrS cs
    simp only [List.foldr_cons, TrS_app, OkS_app, h1, h2]
    exact ⟨rfl, rfl⟩
theorem strLit_TrS (st : String) :
    TrS s (InLean.strLitToConstructor st) = ConLeche.strLitToConstructor st ∧
      OkS s (InLean.strLitToConstructor st) = true := by
  unfold InLean.strLitToConstructor ConLeche.strLitToConstructor
  obtain ⟨h1, h2⟩ := strLitList_TrS s st.toList
  simp only [TrS_app, OkS_app, h1, h2]
  exact ⟨rfl, rfl⟩
theorem lbb_strLit (st : String) : (ConLeche.strLitToConstructor st).looseBVarsBounded 0 = true := by
  unfold ConLeche.strLitToConstructor
  induction st.toList with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldr_cons, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at ih ⊢
    simp [ih.2]

@[conleche_grind =] theorem TrS_strLit (st : String) :
    TrS s (InLean.strLitToConstructor st) = ConLeche.strLitToConstructor st := (strLit_TrS s st).1
@[conleche_grind =] theorem OkS_strLit (st : String) :
    OkS s (InLean.strLitToConstructor st) = true := (strLit_TrS s st).2
attribute [conleche_grind =] lbb_strLit

@[conleche_grind =] theorem map_trL_eq_nil (us : List Level) : (us.map trL = []) = (us = []) := by
  simp

@[conleche_grind =] theorem toName_stringOfListName :
    toName InLean.stringOfListName = ConLeche.stringOfListName := rfl

theorem toLit_eq_strVal {l : Literal} {st : String} (h : toLit l = .strVal st) :
    l = .strVal st := by
  cases l with
  | natVal _ => simp [toLit] at h
  | strVal _ => simp only [toLit, ConLeche.Literal.strVal.injEq] at h; rw [h]
grind_pattern [conleche_grind] toLit_eq_strVal => toLit l, ConLeche.Literal.strVal st


/-- An interned free variable's depth is its translation's (`trans_depthOK`). -/
theorem fvarDepth_TrS {id : FVarId} (h : OkS s (.fvar id) = true) :
    InLean.fvarDepth? id = some (fvIdxS s id) := by
  simp only [OkS, okE, Option.isSome_iff_exists] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, ty, rfl, hd⟩ := FVarTable.trans_depthOK _ id c hc
  simp only [InLean.fvarDepth?, hd, fvIdxS, TrS, trE, hc, Option.getD_some]
grind_pattern [conleche_grind] fvarDepth_TrS => OkS s (.fvar id), InLean.fvarDepth? id

end Stuck

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
  | some (.ctorInfo cv nP nF _) => some (cv.levelParams, nP, nF)
  | _ => none

/-- What a certificate reads of an inductive former's entry. -/
structure IndGate where
  lps : List ConLeche.Name
  eta : Bool

/-- What a certificate reads of an inductive former's entry. -/
@[expose] def indRd (env : ConLeche.Env) (T : ConLeche.Name) : Option IndGate :=
  match env.find? T with
  | some (.indInfo cv caps) => some ⟨cv.levelParams, caps.eta⟩
  | _ => none

/-- What a certificate reads of a structure's projection table: its
constructor and counts. -/
structure TblGate where
  ctor : ConLeche.Name
  numParams : Nat
  numFields : Nat

/-- What a certificate reads of a projection table. -/
@[expose] def tblRd (env : ConLeche.Env) (T : ConLeche.Name) : Option TblGate :=
  match env.findTable? T with
  | some tbl => some ⟨tbl.ctor, tbl.numParams, tbl.numFields⟩
  | none => none

/-- InLean's constructor view, read as `ctorRd`. -/
@[expose] def ctorGateI (x : ConstantVal × Nat × Nat × Name) : List ConLeche.Name × Nat × Nat :=
  (x.1.levelParams.map toName, x.2.1, x.2.2.1)

/-- InLean's former view, read as `indRd`. -/
@[expose] def indGateI (x : ConstantVal × InLean.IndCaps) : IndGate :=
  ⟨x.1.levelParams.map toName, x.2.eta⟩

/-- InLean's table, read as `tblRd`. -/
@[expose] def tblGateI (t : InLean.TableView) : TblGate :=
  ⟨toName t.ctor, t.numParams, t.numFields⟩

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
  strLit : fe.strLit = ConLeche.strLitStored env
  ctor : ∀ c, ctorRd env (toName c) = (fe.ctorView? c).map ctorGateI
  ind : ∀ T, indRd env (toName T) = (fe.indView? T).map indGateI
  /-- the views (the tables, the unit-like shape and the partial-constructor
  gate read them) -/
  view : EnvViewI fe env

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

/-- A projection table through the views, read as `tblRd`. -/
theorem tblRd_V (hv : EnvViewI fe env) (T : Name) :
    tblRd env (toName T) = (fe.findTable? T).map tblGateI := by
  unfold tblRd
  cases ht : fe.findTable? T with
  | none => rw [hv.tableNone T ht]; rfl
  | some t =>
    obtain ⟨ct, hct, h1, h2, h3, -⟩ := hv.table T t ht
    rw [hct]
    simp [tblGateI, h1, h2, h3]

theorem tblRd_toName (hfe : DefeqEnvI fe env) (T : Name) :
    tblRd env (toName T) = (fe.findTable? T).map tblGateI := tblRd_V hfe.view T
grind_pattern [conleche_grind] tblRd_toName => DefeqEnvI fe env, fe.findTable? T

theorem etaShape_TrS (hfe : DefeqEnvI fe env) {s : InLean.CState} {a : Expr}
    (h : OkS s a = true) : etaCtorShapeC fe a = ConLeche.etaCtorShape env (TrS s a) :=
  hfe.etaShape s a h
grind_pattern [conleche_grind] etaShape_TrS => DefeqEnvI fe env, OkS s a, etaCtorShapeC fe a

theorem strLit_eq (hfe : DefeqEnvI fe env) : fe.strLit = ConLeche.strLitStored env :=
  hfe.strLit
grind_pattern [conleche_grind] strLit_eq => DefeqEnvI fe env, fe.strLit

theorem unfoldable_TrS (hfe : DefeqEnvI fe env) {s : InLean.CState} {e : Expr}
    (h : OkS s e = true) : unfoldableHeadC fe e = ConLeche.unfoldableHead env (TrS s e) :=
  hfe.unfoldable s e h
grind_pattern [conleche_grind] unfoldable_TrS => DefeqEnvI fe env, OkS s e, unfoldableHeadC fe e

theorem headHint_TrS (hfe : DefeqEnvI fe env) {s : InLean.CState} {e : Expr}
    (h : OkS s e = true) : trHint (headHintC fe e) = ConLeche.headHint env (TrS s e) :=
  hfe.headHint s e h
grind_pattern [conleche_grind] headHint_TrS => DefeqEnvI fe env, OkS s e, headHintC fe e

@[conleche_grind =] theorem indGateI_mk (cv : ConstantVal) (caps : InLean.IndCaps) :
    indGateI (cv, caps) = ⟨cv.levelParams.map toName, caps.eta⟩ := rfl

@[conleche_grind =] theorem tblGateI_ctor (t : InLean.TableView) :
    (tblGateI t).ctor = toName t.ctor := rfl
@[conleche_grind =] theorem tblGateI_numParams (t : InLean.TableView) :
    (tblGateI t).numParams = t.numParams := rfl
@[conleche_grind =] theorem tblGateI_numFields (t : InLean.TableView) :
    (tblGateI t).numFields = t.numFields := rfl

@[conleche_grind =] theorem ctorGateI_mk (cv : ConstantVal) (nP nF : Nat) (T : Name) :
    ctorGateI (cv, nP, nF, T) = (cv.levelParams.map toName, nP, nF) := rfl

end EnvReaders2

/-! ## Names and lists through the translation -/

section Lists

/-! The list lemmas of `WalksIotaRec` (take/drop of translated, checked and
closed lists), registered for this lane's `grind` calls. -/

attribute [conleche_grind =] TrSL_take TrSL_drop
grind_pattern [conleche_grind] OkSL_take => OkSL s l, l.take k
grind_pattern [conleche_grind] OkSL_drop => OkSL s l, l.drop k
grind_pattern [conleche_grind] AllClosed_take => AllClosed l, l.take k
grind_pattern [conleche_grind] AllClosed_drop => AllClosed l, l.drop k

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


theorem OkSL_reverse {l : List Expr} (h : OkSL s l = true) : OkSL s l.reverse = true := by
  simp only [OkSL, List.all_eq_true, List.mem_reverse] at h ⊢; exact h
grind_pattern [conleche_grind] OkSL_reverse => OkSL s l, l.reverse

theorem AllClosed_reverse {l : List ConLeche.Expr} (h : AllClosed l = true) :
    AllClosed l.reverse = true := by
  simp only [AllClosed, List.all_eq_true, List.mem_reverse] at h ⊢; exact h
grind_pattern [conleche_grind] AllClosed_reverse => AllClosed l, l.reverse

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

/-! ## The partial-constructor gate and the unit-like shape (task #515's readers)

Both read the views (`EnvViewI`, `DefeqEnvI.view`): the gate a constructor,
the family its type ends in and that family's capabilities; the shape a
family's capabilities, its table's first entry and that entry's constructor,
whose type InLean instantiates at the instance's levels (`instLevelParamsM`)
and arguments (`instI`). -/

section Shape

variable {fe : InLean.FEnv}

/-- **The partial-constructor gate through the views** (`etaCtorPartialC_eq`'s
twin). -/
theorem etaCtorPartial_TrS (hv : EnvViewI fe env) (s : InLean.CState) {a : Expr}
    (ha : OkS s a = true) :
    InLean.etaCtorPartialC fe a = ConLeche.etaCtorPartial env (TrS s a) := by
  unfold InLean.etaCtorPartialC ConLeche.etaCtorPartial
  rw [← numArgs_TrS ha]
  rcases head_cases s a with ⟨n, us, hx, hc⟩ | ⟨hx, hc⟩
  · rw [hx, hc]
    simp only
    cases hcv : fe.ctorView? n with
    | none =>
      have hn := hv.ctorNone n hcv
      simp only
      all_goals
        cases hf : env.find? (toName n) with
        | none => rfl
        | some ci =>
          cases ci with
          | ctorInfo ccv nP nF T => exact absurd hf (hn ccv nP nF T)
          | _ => rfl
    | some x =>
      obtain ⟨cv, nP, nF, T⟩ := x
      obtain ⟨ccv, hcvr, hL⟩ := hv.ctor n cv nP nF T hcv
      rw [hL]
      simp only
      by_cases hlt : Expr.getAppNumArgsT a < nP + nF
      · simp only [hlt, ↓reduceIte]
        cases hiv : fe.indView? T with
        | none =>
          have hn := hv.indNone T hiv
          simp only
          all_goals
            cases hf : env.find? (toName T) with
            | none => rfl
            | some ci =>
              cases ci with
              | indInfo ccvT caps => exact absurd hf (hn ccvT caps)
              | _ => rfl
        | some y =>
          obtain ⟨cvT, caps⟩ := y
          obtain ⟨ccvT, -, hLT⟩ := hv.ind T cvT caps hiv
          rw [hLT]
          simp only [toCaps]
          cases ht : fe.findTable? T with
          | none => rw [hv.tableNone T ht]
          | some t =>
            obtain ⟨ct, hct, h1, -⟩ := hv.table T t ht
            rw [hct]
            simp only [h1, name_beq_eq_decide, decide_eq_true_eq]
      · simp only [hlt, ↓reduceIte]
  · split
    · rename_i h; exact absurd h (hx _ _)
    · split
      · rename_i h; exact absurd h (hc _ _)
      · rfl

theorem etaPartial_TrS (hfe : DefeqEnvI fe env) {s : InLean.CState} {a : Expr}
    (h : OkS s a = true) : InLean.etaCtorPartialC fe a = ConLeche.etaCtorPartial env (TrS s a) :=
  etaCtorPartial_TrS hfe.view s h
grind_pattern [conleche_grind] etaPartial_TrS =>
  DefeqEnvI fe env, OkS s a, InLean.etaCtorPartialC fe a

/-- InLean's `peelPis` through the translation, with the rest's reading. -/
theorem peelPis_map_TrS (s : InLean.CState) : ∀ (n : Nat) (t : Expr), OkS s t = true →
    (∀ r, InLean.peelPis n t = some r → OkS s r = true) ∧
      ConLeche.Expr.peelPis n (TrS s t) = (InLean.peelPis n t).map (TrS s)
  | 0, t, h => by
    refine ⟨fun r hr => ?_, by simp [ConLeche.Expr.peelPis, InLean.peelPis]⟩
    simp only [InLean.peelPis, Option.some.injEq] at hr
    exact hr ▸ h
  | n + 1, .forallE _ _ b _, h => by
    simp only [OkS_forallE, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := peelPis_map_TrS s n b h.2
    exact ⟨fun r hr => h1 r hr, by rw [TrS_forallE, ConLeche.Expr.peelPis, InLean.peelPis, h2]⟩
  | n + 1, .mdata _ e, h => by
    rw [OkS_mdata] at h
    rw [TrS_mdata, InLean.peelPis]
    exact peelPis_map_TrS s (n + 1) e h
  | n + 1, .fvar id, _ => by
    refine ⟨fun r hr => by simp [InLean.peelPis] at hr, ?_⟩
    simp only [InLean.peelPis, TrS, trE]
    cases hf : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | n + 1, .bvar _, _ | n + 1, .mvar _, _ | n + 1, .sort _, _ | n + 1, .const .., _
  | n + 1, .app .., _ | n + 1, .lam .., _ | n + 1, .letE .., _ | n + 1, .lit _, _
  | n + 1, .proj .., _ => ⟨fun r hr => by simp [InLean.peelPis] at hr, rfl⟩

/-- A peel of a closed telescope is bounded by the binders it peels. -/
theorem lbb_peelPis : ∀ {n k : Nat} {e r : ConLeche.Expr}, e.looseBVarsBounded k = true →
    ConLeche.Expr.peelPis n e = some r → r.looseBVarsBounded (k + n) = true
  | 0, k, e, r, he, h => by
    simp only [ConLeche.Expr.peelPis, Option.some.injEq] at h; exact h ▸ he
  | n + 1, k, .forallE _ b, r, he, h => by
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at he
    have := lbb_peelPis (n := n) he.2 h
    rwa [Nat.add_assoc, Nat.add_comm 1 n] at this
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _ _, _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const _ _, _, _, h | _ + 1, _, .app _ _, _, _, h | _ + 1, _, .lam _ _, _, _, h
  | _ + 1, _, .letE _ _ _, _, _, h | _ + 1, _, .lit _, _, _, h
  | _ + 1, _, .proj _ _ _, _, _, h => nomatch h

/-- **The field telescope of a closed instance is closed** (`unitLikeShape_WScoped`'s
companion): the stored constructor type is closed, the peel leaves the
parameters' binders, and the instance's closed arguments fill them. -/
theorem unitLikeShape_closed (henv : ConLeche.EnvWF env) {w tele : ConLeche.Expr} {n : Nat}
    (hw : w.looseBVarsBounded 0 = true) (h : ConLeche.unitLikeShape env w = some (tele, n)) :
    tele.looseBVarsBounded 0 = true := by
  obtain ⟨S, us, _, _, tbl, cvC, _, _, _, -, -, -, -, -, hlen, hfC, -, ht⟩ :=
    ConLeche.unitLikeShape_some h
  rw [ConLeche.unitFieldTele_eq] at ht
  cases hb : ConLeche.Expr.peelPis tbl.numParams
      (cvC.type.instantiateLevelParams cvC.levelParams us) with
  | none => rw [hb] at ht; exact nomatch ht
  | some body =>
    rw [hb] at ht
    obtain rfl := Option.some.inj ht
    have hc0 : (cvC.type.instantiateLevelParams cvC.levelParams us).looseBVarsBounded
        0 = true := by
      rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
      exact (henv.consts _ (ConLeche.Env.find?_mem hfC)).2.2.2.1
    have hbb := lbb_peelPis hc0 hb
    rw [Nat.zero_add, ← hlen] at hbb
    have hargs := allClosed_getAppArgs hw
    simp only [AllClosed, List.all_eq_true] at hargs
    exact ConLeche.instSpine_closed hargs hbb

/-- The shape's answer, its telescope translated. -/
@[expose] def trUnitShape (s : InLean.CState) :
    Option (Expr × Nat) → Option (ConLeche.Expr × Nat)
  | some (t, n) => some (TrS s t, n)
  | none => none

/-- The shape's telescope has a reading. -/
@[expose] def okUnitShape (s : InLean.CState) : Option (Expr × Nat) → Bool
  | some (t, _) => OkS s t
  | none => true

end Shape

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
                match tblRd env T with
                | some tb =>
                  if g.eta = true ∧ tb.ctor = c ∧
                      wtb.getAppArgs.length = tb.numParams ∧
                      us'.length = g.lps.length ∧
                      clps = g.lps then
                    if ← ConLeche.liftFueled "level comparison"
                        (ConLeche.Level.isEquivList us us') then
                      if ← ConLeche.defEqList r env d
                          (a.getAppArgs.take tb.numParams) wtb.getAppArgs then
                        ConLeche.defEqList r env d
                          (a.getAppArgs.drop tb.numParams)
                          (ConLeche.etaProjs T b tb.numFields)
                      else pure false
                    else pure false
                  else pure false
                | none => pure false
              | none => pure false
            | _ => pure false
          else pure false
        | none => pure false
      | _ => pure false : m Bool) := by
  unfold ConLeche.structEtaCertWith indRd ctorRd tblRd
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
            | some ci' =>
              cases ci' with
              | indInfo cvT caps =>
                dsimp only
                cases env.findTable? T <;> rfl
              | _ => rfl
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
abbrev DefeqSpineSpecI (mode : ConLeche.CheckMode) (mi : InLean.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (fe : InLean.FEnv) (lv : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {s₀ : InLean.CState},
    CSOKI mode eager env s₀ → OkS s₀ a = true → OkS s₀ b = true →
    ConLeche.Expr.WScoped d (TrS s₀ a) → ConLeche.Expr.WScoped d (TrS s₀ b) →
    (TrS s₀ a).looseBVarsBounded 0 = true → (TrS s₀ b).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ defeqSpineI mi fe eager lv d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqSpine (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄

/-- `reduceNatI`'s spec (`reduceNatC_spec`'s twin), P2-whnf's to prove. -/
abbrev ReduceNatSpecI (mode : ConLeche.CheckMode) (mi : InLean.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (fe : InLean.FEnv) (lv : Nat) : Prop :=
  ∀ {d : Nat} {i : Expr} {s₀ : InLean.CState},
    CSOKI mode eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ reduceNatI mi fe eager lv d i
    ⦃fun o s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (ConLeche.reduceNat (ConLeche.fueledFns mode eager env) env d (TrS s₀ i)) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true; ⊤⦄

/-- `defEqListI`'s spec (`defEqListC_spec`'s twin), P2-whnf's to prove. -/
abbrev DefEqListSpecI (mode : ConLeche.CheckMode) (mi : InLean.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (fe : InLean.FEnv) (lv : Nat) : Prop :=
  ∀ {d : Nat} {args brgs : List Expr} {s₀ : InLean.CState},
    CSOKI mode eager env s₀ → OkSL s₀ args = true → OkSL s₀ brgs = true →
    AllWS d (TrSL s₀ args) → AllWS d (TrSL s₀ brgs) →
    AllClosed (TrSL s₀ args) = true → AllClosed (TrSL s₀ brgs) = true →
    ⦃fun s => s = s₀⦄ defEqListI mi fe eager lv d args brgs
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defEqList (ConLeche.fueledFns mode eager env) env d (TrSL s₀ args)
        (TrSL s₀ brgs)) v; ⊤⦄

/-! ## DiscC2's twins: the stuck-term certificates -/

section Walks

variable {fe : InLean.FEnv} {lv : Nat}

/-- The eq-true shortcut (`boolTrueShortcutC_spec`'s twin). -/
theorem boolTrueShortcutI_spec (ih : KnotSpecI mode mi eager env fe lv) {d : Nat} {a : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ a = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ a)) (hc : (TrS s₀ a).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ boolTrueShortcutI mi fe eager lv d a
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.boolTrueShortcut (ConLeche.fueledFns mode eager env) d (TrS s₀ a)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.boolTrueShortcut] =>
    vcgen [InLean.boolTrueShortcutI.eq_def, ih.whnf hs hok hw hc] <;> finish

/-- `proofIrrelI` (`proofIrrelC_spec`'s twin). -/
theorem proofIrrelI_spec (ih : KnotSpecI mode mi eager env fe lv) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.proofIrrelI mi fe eager lv d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.proofIrrel (ConLeche.fueledFns mode eager env) d (TrS s₀ a) (TrS s₀ b)) v;
        ⊤⦄ := by
  sym only [conleche_grind, ConLeche.proofIrrel] =>
    vcgen [InLean.proofIrrelI.eq_def, ih.inferIO, ih.whnf, isEquivLM_specI (mode := mode) (eager := eager)
        (env := env), liftFueled_specI (mode := mode) (eager := eager) (env := env)] <;>
      -- the pure side is nine binds deep, one `Runs.bind_eq` generation each
      finish (gen := 12)

/-- The hoisted `Prop`-branch test (`propIrrelC_spec`'s twin). -/
theorem propIrrelI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode mi eager env fe lv)
    (hfe : DefeqEnvI fe env) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.propIrrelI mi fe eager lv d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.propIrrel (ConLeche.fueledFns mode eager env) env d (TrS s₀ a) (TrS s₀ b)) v;
        ⊤⦄ := by
  sym only [conleche_grind, propIrrel_eq] =>
    vcgen [InLean.propIrrelI.eq_def, notProofFastM_specI (mode := mode) (eager := eager) hfe,
      isProofFastM_specI (mode := mode) (eager := eager) hfe,
      proofIrrelI_spec ih] <;> finish

/-- `etaCertI` (`etaCertC_spec`'s twin). -/
theorem etaCertI_spec (ih : KnotSpecI .verified .verified eager env fe lv) {d : Nat} {ty₁ body₁ b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hokt : OkS s₀ ty₁ = true)
    (hokbody : OkS s₀ body₁ = true) (hokb : OkS s₀ b = true)
    (hwty : ConLeche.Expr.WScoped d (TrS s₀ ty₁)) (hwbody : ConLeche.Expr.WScoped d (TrS s₀ body₁))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hct : (TrS s₀ ty₁).looseBVarsBounded 0 = true)
    (hcbody : (TrS s₀ body₁).looseBVarsBounded 1 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.etaCertI .verified fe eager lv d ty₁ body₁ b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.etaCert .verified (ConLeche.fueledFns .verified eager env) env d (TrS s₀ ty₁)
        (TrS s₀ body₁) (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.etaCert] =>
    vcgen [InLean.etaCertI.eq_def, ih.inferIO, ih.whnf, ih.defeq, ih.infer,
      mkFVarM_specI (mode := .verified) (eager := eager) (env := env)] <;>
      -- the verified arm is seven binds deep, one `Runs.bind_eq` generation each
      finish (gen := 10)

/-- `structEtaCertWithI` (`structEtaCertWithC_spec`'s twin). -/
theorem structEtaCertWithI_spec {fe : InLean.FEnv} (hfe : DefeqEnvI fe env)
    (hlist : DefEqListSpecI mode mi eager env fe lv) {d : Nat} {a b wtb : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hokw : OkS s₀ wtb = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hww : ConLeche.Expr.WScoped d (TrS s₀ wtb))
    (hca : (TrS s₀ a).looseBVarsBounded 0 = true) (hcb : (TrS s₀ b).looseBVarsBounded 0 = true)
    (hcw : (TrS s₀ wtb).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.structEtaCertWithI mi fe eager lv d a b wtb
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.structEtaCertWith (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b) (TrS s₀ wtb)) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaCertWith_eq] =>
    vcgen [InLean.structEtaCertWithI.eq_def, isEquivListLM_specI (mode := mode) (eager := eager)
        (env := env), liftFueled_specI (mode := mode) (eager := eager) (env := env), hlist] <;>
      -- three lookups (the constructor, the former, its table) and two spine heads deep
      -- before the first bind, one generation each
      finish (gen := 13)

/-- **A binder opened at a fresh variable**, InLean's way (`mkFVarM`, then
`inst1I`): the variable reads as con-leche's `.fvar d dom`, the opened body
as the body instantiated at it, scoped one deeper and closed. -/
theorem open_runI {s₀ s₁ : InLean.CState} {d : Nat} {dom body fv : Expr}
    (hs : CSOKI mode eager env s₀) (hokd : OkS s₀ dom = true) (hokb : OkS s₀ body = true)
    (hwd : ConLeche.Expr.WScoped d (TrS s₀ dom)) (hwb : ConLeche.Expr.WScoped d (TrS s₀ body))
    (hcd : (TrS s₀ dom).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ body).looseBVarsBounded 1 = true)
    (h : mkFVarM d dom s₀ = .ok (fv, s₁)) :
    CSOKI mode eager env s₁ ∧ TabLe s₀ s₁ ∧ OkS s₁ fv = true ∧
      TrS s₁ fv = .fvar d (TrS s₀ dom) ∧ OkS s₁ (body.inst1I fv) = true ∧
      TrS s₁ (body.inst1I fv) = (TrS s₀ body).instantiate1 (.fvar d (TrS s₀ dom)) 0 ∧
      ConLeche.Expr.WScoped (d + 1) (TrS s₁ (body.inst1I fv)) ∧
      (TrS s₁ (body.inst1I fv)).looseBVarsBounded 0 = true := by
  obtain ⟨hs1, hle1, hokfv, htrfv⟩ :=
    tripleI_iff_run.1 (mkFVarM_specI (mode := mode) (eager := eager) (env := env) hs d hokd hcd)
      fv s₁ h
  have hokb1 := okS_of_tabLe hle1 hokb
  have hfvcl : (TrS s₁ fv).looseBVarsBounded 0 = true := by rw [htrfv]; rfl
  have hTI : TrS s₁ (body.inst1I fv) = (TrS s₀ body).instantiate1 (.fvar d (TrS s₀ dom)) 0 := by
    rw [inst1I_eq, TrS_inst1_eq hokb1 hokfv hfvcl, TrS_of_tabLe hle1 hokb, htrfv]
  refine ⟨hs1, hle1, hokfv, htrfv, by rw [inst1I_eq]; exact OkS_inst1 hokb1 hokfv hfvcl, hTI, ?_, ?_⟩
  · rw [hTI]; exact wscoped_open 0 hwd hwb
  · rw [hTI]; exact lbb_instantiate1 rfl hcb

/-- A walk answering `false` at once, against a pure `false`. -/
theorem pureFalse_specI {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) :
    ⦃fun s => s = s₀⦄ (pure false : InLean.CheckCM Bool)
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (pure false : ConLeche.FueledM Bool) v; ⊤⦄ :=
  tripleI_iff_run.2 fun v s' hr => by
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩

theorem structEtaExpandI_noForall {fe : InLean.FEnv} {k d : Nat} {a b t : Expr}
    (hn : ∀ n dom body bi, EO.stripTop t ≠ .forallE n dom body bi) :
    InLean.structEtaExpandI mi fe eager lv (k + 1) d a b t = pure false := by
  rw [InLean.structEtaExpandI.eq_def]
  dsimp only
  split
  · rename_i h; exact absurd h (hn _ _ _ _)
  · rfl

/-- `structEtaFullI` (`structEtaFullC_spec`'s twin). -/
theorem structEtaFullI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode mi eager env fe lv)
    (hfe : DefeqEnvI fe env) (hlist : DefEqListSpecI mode mi eager env fe lv) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.structEtaFullI mi fe eager lv d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.structEtaFull (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.structEtaFull] =>
    vcgen [InLean.structEtaFullI.eq_def, ih.inferIO, ih.whnf, structEtaCertWithI_spec hfe hlist] <;>
      finish

/-- `structEtaExpand` at a successor, its `∀` match spelled out. -/
theorem structEtaExpand_succ_eq {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (env : ConLeche.Env) (k d : Nat) (a b t : ConLeche.Expr) :
    ConLeche.structEtaExpand r env (k + 1) d a b t =
      (match t with
        | .forallE dom body =>
          ConLeche.structEtaExpand r env k (d + 1) (.app a (.fvar d dom)) (.app b (.fvar d dom))
            (body.instantiate1 (.fvar d dom))
        | _ => pure false) := by
  cases t <;> rfl

/-- The η-expansion (`structEtaExpandC_spec`'s twin). -/
theorem structEtaExpandI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode mi eager env fe lv)
    (hfe : DefeqEnvI fe env) (hlist : DefEqListSpecI mode mi eager env fe lv) :
    ∀ {k d : Nat} {a b t : Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ →
      OkS s₀ a = true → OkS s₀ b = true → OkS s₀ t = true →
      ConLeche.Expr.WScoped d (TrS s₀ a) → ConLeche.Expr.WScoped d (TrS s₀ b) →
      ConLeche.Expr.WScoped d (TrS s₀ t) →
      (TrS s₀ a).looseBVarsBounded 0 = true → (TrS s₀ b).looseBVarsBounded 0 = true →
      (TrS s₀ t).looseBVarsBounded 0 = true →
      ⦃fun s => s = s₀⦄ InLean.structEtaExpandI mi fe eager lv k d a b t
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.structEtaExpand (ConLeche.fueledFns mode eager env) env k d (TrS s₀ a)
          (TrS s₀ b) (TrS s₀ t)) v; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro d a b t s₀ hs hoka hokb hokt hwa hwb hwt hca hcb hct
    sym only [conleche_grind, ConLeche.structEtaExpand] =>
      vcgen [InLean.structEtaExpandI.eq_def, structEtaFullI_spec ih hfe hlist] <;> finish
  | succ k ihk =>
    intro d a b t s₀ hs hoka hokb hokt hwa hwb hwt hca hcb hct
    rw [structEtaExpand_succ_eq]
    by_cases hf : ∃ n dom body bi, EO.stripTop t = .forallE n dom body bi
    · obtain ⟨n, dom, body, bi, h⟩ := hf
      have htr : TrS s₀ t = .forallE (TrS s₀ dom) (TrS s₀ body) := by
        rw [← TrS_stripTop, h, TrS_forallE]
      have hok' : OkS s₀ (.forallE n dom body bi) = true := by rw [← h, OkS_stripTop]; exact hokt
      rw [htr] at hwt hct ⊢
      rw [InLean.structEtaExpandI.eq_def]
      simp only [h]
      rw [OkS_forallE, Bool.and_eq_true] at hok'
      rw [ConLeche.Cached.wscoped_forallE_eq] at hwt
      rw [lbb_forallE, Bool.and_eq_true] at hct
      refine tripleI_iff_run.2 fun v s' hr => ?_
      obtain ⟨fv, s₁, h1, hr⟩ := bind_run hr
      obtain ⟨hs1, hle1, hokfv, htrfv, hokI, hTI, hwI, hcI⟩ :=
        open_runI hs hok'.1 hok'.2 hwt.1 hwt.2 hct.1 hct.2 h1
      have hoka1 := okS_of_tabLe hle1 hoka
      have hokb1 := okS_of_tabLe hle1 hokb
      have hta : TrS s₁ a = TrS s₀ a := TrS_of_tabLe hle1 hoka
      have htb : TrS s₁ b = TrS s₀ b := TrS_of_tabLe hle1 hokb
      obtain ⟨hs', hle', hrun⟩ := tripleI_iff_run.1 (ihk hs1
        (by rw [OkS_app, hoka1, hokfv]; rfl) (by rw [OkS_app, hokb1, hokfv]; rfl) hokI
        (by rw [TrS_app, hta, htrfv, ConLeche.Cached.wscoped_app_eq, ConLeche.Cached.wscoped_fvar_eq]
            exact ⟨wscoped_succ hwa, Nat.lt_succ_self d, hwt.1⟩)
        (by rw [TrS_app, htb, htrfv, ConLeche.Cached.wscoped_app_eq, ConLeche.Cached.wscoped_fvar_eq]
            exact ⟨wscoped_succ hwb, Nat.lt_succ_self d, hwt.1⟩)
        hwI
        (by rw [TrS_app, hta, htrfv, lbb_app, hca]; rfl)
        (by rw [TrS_app, htb, htrfv, lbb_app, hcb]; rfl)
        hcI) v s' hr
      rw [TrS_app, TrS_app, hta, htb, htrfv, hTI] at hrun
      exact ⟨hs', hle1.trans hle', hrun⟩
    · have hn : ∀ n dom body bi, EO.stripTop t ≠ .forallE n dom body bi :=
        fun n dom body bi h => hf ⟨n, dom, body, bi, h⟩
      rw [structEtaExpandI_noForall hn]
      cases htr : TrS s₀ t with
      | forallE dom body => exact absurd htr (TrS_ne_forallE s₀ hn dom body)
      | _ => exact pureFalse_specI hs

/-- `structEtaCertI` (`structEtaCertC_spec`'s twin). -/
theorem structEtaCertI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode mi eager env fe lv)
    (hfe : DefeqEnvI fe env) (hlist : DefEqListSpecI mode mi eager env fe lv) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.structEtaCertI mi fe eager lv d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.structEtaCert (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.structEtaCert] =>
    vcgen [InLean.structEtaCertI.eq_def, structEtaFullI_spec ih hfe hlist, ih.inferIO, ih.defeq,
      structEtaExpandI_spec ih hfe hlist] <;> finish

/-- `isPropType` with its binds named. -/
theorem isPropType_eq {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (d : Nat) (T : ConLeche.Expr) :
    ConLeche.isPropType r d T = (do
      let tt ← r.inferIO d T
      let w ← r.whnf d tt
      match w with
      | .sort u => ConLeche.liftFueled "level comparison" (u.isEquiv .zero)
      | _ => pure false) := rfl

/-- A `liftFueled` of a present answer, last in a block, is that answer. -/
@[conleche_grind =] theorem liftFueled_some_eq {α : Type} (w : String) (a : α) :
    (ConLeche.liftFueled w (some a) : ConLeche.FueledM α) = pure a := rfl

/-- `isPropTypeI` (`isPropTypeC_spec`'s twin). -/
theorem isPropTypeI_spec (ih : KnotSpecI mode mi eager env fe lv) {d : Nat} {T : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ T = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ T)) (hc : (TrS s₀ T).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.isPropTypeI mi fe eager lv d T
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.isPropType (ConLeche.fueledFns mode eager env) d (TrS s₀ T)) v; ⊤⦄ := by
  sym only [conleche_grind, isPropType_eq] =>
    vcgen [InLean.isPropTypeI.eq_def, ih.inferIO, ih.whnf, isEquivLM_specI (mode := mode) (eager := eager)
        (env := env), liftFueled_specI (mode := mode) (eager := eager) (env := env)] <;> finish

/-- **A field test's spec**: the recursive unit-like test's at a fuel, as the
field loop calls it. -/
abbrev UnitLikeSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (ul : Nat → Expr → InLean.CheckCM Bool) (ul' : Nat → ConLeche.Expr → ConLeche.FueledM Bool) :
    Prop :=
  ∀ {d : Nat} {e : Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ → OkS s₀ e = true →
    ConLeche.Expr.WScoped d (TrS s₀ e) → (TrS s₀ e).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ ul d e
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ Runs (ul' d (TrS s₀ e)) v; ⊤⦄

/-- `unitLikeFields` at a successor, its `∀` match spelled out. -/
theorem unitLikeFields_succ_eq {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (ul : Nat → ConLeche.Expr → m Bool) (n d : Nat) (t : ConLeche.Expr) :
    ConLeche.unitLikeFields r ul (n + 1) d t =
      (match t with
        | .forallE dom body => do
          if ← ConLeche.isPropType r d dom then
            ConLeche.unitLikeFields r ul n (d + 1) (body.instantiate1 (.fvar d dom))
          else if ← ul d dom then
            ConLeche.unitLikeFields r ul n (d + 1) (body.instantiate1 (.fvar d dom))
          else pure false
        | _ => pure false) := by
  cases t <;> rfl

/-- The field loop (`unitLikeFieldsC_spec`'s twin), given the field test's spec. -/
theorem unitLikeFieldsI_spec (ih : KnotSpecI mode mi eager env fe lv)
    {ulf : Nat} {ul' : Nat → ConLeche.Expr → ConLeche.FueledM Bool}
    (hul : UnitLikeSpecI mode eager env (InLean.unitLikeLoopI mi fe eager lv ulf) ul') :
    ∀ {n d : Nat} {t : Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ → OkS s₀ t = true →
      ConLeche.Expr.WScoped d (TrS s₀ t) → (TrS s₀ t).looseBVarsBounded 0 = true →
      ⦃fun s => s = s₀⦄ InLean.unitLikeFieldsI mi fe eager lv ulf n d t
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.unitLikeFields (ConLeche.fueledFns mode eager env) ul' n d (TrS s₀ t)) v;
          ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro d t s₀ hs hok hw hc
    sym only [conleche_grind, ConLeche.unitLikeFields] =>
      vcgen [InLean.unitLikeFieldsI.eq_def] <;> finish
  | succ n ihn =>
    intro d t s₀ hs hok hw hc
    rw [unitLikeFields_succ_eq]
    by_cases hf : ∃ nm dom body bi, EO.stripTop t = .forallE nm dom body bi
    · obtain ⟨nm, dom, body, bi, h⟩ := hf
      have htr : TrS s₀ t = .forallE (TrS s₀ dom) (TrS s₀ body) := by
        rw [← TrS_stripTop, h, TrS_forallE]
      have hok' : OkS s₀ (.forallE nm dom body bi) = true := by rw [← h, OkS_stripTop]; exact hok
      rw [htr] at hw hc ⊢
      rw [InLean.unitLikeFieldsI.eq_def]
      simp only [h]
      rw [OkS_forallE, Bool.and_eq_true] at hok'
      rw [ConLeche.Cached.wscoped_forallE_eq] at hw
      rw [lbb_forallE, Bool.and_eq_true] at hc
      refine tripleI_iff_run.2 fun v s' hr => ?_
      obtain ⟨p, s₁, h1, hr⟩ := bind_run hr
      obtain ⟨hs1, hle1, hrun1⟩ := tripleI_iff_run.1 (isPropTypeI_spec ih hs hok'.1 hw.1 hc.1) p s₁ h1
      have hokd1 := okS_of_tabLe hle1 hok'.1
      have hokb1 := okS_of_tabLe hle1 hok'.2
      have htd : TrS s₁ dom = TrS s₀ dom := TrS_of_tabLe hle1 hok'.1
      have htbo : TrS s₁ body = TrS s₀ body := TrS_of_tabLe hle1 hok'.2
      -- the continuation after a passed field: open the binder, the rest of the loop
      have hcont : ∀ {s₂ : InLean.CState}, CSOKI mode eager env s₂ → TabLe s₀ s₂ →
          (InLean.mkFVarM d dom >>= fun fv => InLean.unitLikeFieldsI mi fe eager lv ulf n (d + 1)
            (body.inst1I fv)) s₂ = .ok (v, s') →
          CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
            Runs (ConLeche.unitLikeFields (ConLeche.fueledFns mode eager env) ul' n (d + 1)
              ((TrS s₀ body).instantiate1 (.fvar d (TrS s₀ dom)) 0)) v := by
        intro s₂ hs2 hle2 hr2
        obtain ⟨fv, s₃, h3, hr3⟩ := bind_run hr2
        have htd2 : TrS s₂ dom = TrS s₀ dom := TrS_of_tabLe hle2 hok'.1
        have htb2 : TrS s₂ body = TrS s₀ body := TrS_of_tabLe hle2 hok'.2
        obtain ⟨hs3, hle3, -, -, hokI, hTI, hwI, hcI⟩ :=
          open_runI hs2 (okS_of_tabLe hle2 hok'.1) (okS_of_tabLe hle2 hok'.2)
            (by rw [htd2]; exact hw.1) (by rw [htb2]; exact hw.2)
            (by rw [htd2]; exact hc.1) (by rw [htb2]; exact hc.2) h3
        obtain ⟨hs', hle', hrun⟩ := tripleI_iff_run.1 (ihn hs3 hokI hwI hcI) v s' hr3
        rw [hTI, htd2, htb2] at hrun
        exact ⟨hs', hle2.trans (hle3.trans hle'), hrun⟩
      cases p with
      | true =>
        simp only [↓reduceIte] at hr
        obtain ⟨hs', hle', hrun⟩ := hcont hs1 hle1 hr
        exact ⟨hs', hle', Runs.bind hrun1 (by simp only [↓reduceIte]; exact hrun)⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hr
        obtain ⟨q, s₂, h2, hr⟩ := bind_run hr
        obtain ⟨hs2, hle2, hrun2⟩ := tripleI_iff_run.1 (hul hs1 hokd1 (by rw [htd]; exact hw.1)
          (by rw [htd]; exact hc.1)) q s₂ h2
        rw [htd] at hrun2
        cases q with
        | true =>
          simp only [↓reduceIte] at hr
          obtain ⟨hs', hle', hrun⟩ := hcont hs2 (hle1.trans hle2) hr
          exact ⟨hs', hle', Runs.bind hrun1 (by
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact Runs.bind hrun2 (by simp only [↓reduceIte]; exact hrun))⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hr
          obtain ⟨rfl, rfl⟩ := pure_run hr
          exact ⟨hs2, hle1.trans hle2, Runs.bind hrun1 (by
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact Runs.bind hrun2 (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Runs.pure _))⟩
    · have hn : ∀ nm dom body bi, EO.stripTop t ≠ .forallE nm dom body bi :=
        fun nm dom body bi h => hf ⟨nm, dom, body, bi, h⟩
      have hI : InLean.unitLikeFieldsI mi fe eager lv ulf (n + 1) d t = pure false := by
        rw [InLean.unitLikeFieldsI.eq_def]
        dsimp only
        split
        · rename_i h; exact absurd h (hn _ _ _ _)
        · rfl
      rw [hI]
      cases htr : TrS s₀ t with
      | forallE dom body => exact absurd htr (TrS_ne_forallE s₀ hn dom body)
      | _ => exact pureFalse_specI hs

/-- **The unit-like shape through the views** (`unitLikeShapeF_mkFEnv`'s twin):
InLean's answer reads as con-leche's, its telescope with a reading. -/
theorem unitLikeShapeM_specI {fe : InLean.FEnv} (hfe : DefeqEnvI fe env) {w : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ w = true)
    (hc : (TrS s₀ w).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.unitLikeShapeM fe w
    ⦃fun o s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ okUnitShape s' o = true ∧
      trUnitShape s' o = ConLeche.unitLikeShape env (TrS s₀ w); ⊤⦄ := by
  have hv := hfe.view
  refine tripleI_iff_run.2 fun o s' hr => ?_
  unfold InLean.unitLikeShapeM at hr
  unfold ConLeche.unitLikeShape
  rcases head_cases s₀ w with ⟨S, us, hx, hhd⟩ | ⟨hx, hhd⟩
  · rw [hhd]
    rw [hx] at hr
    simp only at hr ⊢
    have hus : us.all okLv = true := by
      have := OkS_getAppFnT (s := s₀) hok; rw [hx] at this; exact this
    cases hiv : fe.indView? S with
    | none =>
      simp only [hiv] at hr
      obtain ⟨rfl, rfl⟩ := pure_run hr
      refine ⟨hs, TabLe.refl _, rfl, ?_⟩
      have hn := hv.indNone S hiv
      cases hf : env.find? (toName S) with
      | none => rfl
      | some ci =>
        cases ci with
        | indInfo ccv caps => exact absurd hf (hn ccv caps)
        | _ => rfl
    | some y =>
      obtain ⟨cvS, caps⟩ := y
      simp only [hiv] at hr
      obtain ⟨ccvS, hcvS, hLS⟩ := hv.ind S cvS caps hiv
      rw [hLS]
      simp only [toCaps] at hr ⊢
      have hlen : (appArgs w).length = (TrS s₀ w).getAppArgs.length := length_appArgs s₀ w
      have hlps : ccvS.levelParams = cvS.levelParams.map toName := hcvS.2.1
      rw [hlps, ← hlen, length_map_trL, length_map_toName]
      by_cases h1 : caps.eta = true ∧ us.length = cvS.levelParams.length
      · simp only [h1, and_self, ↓reduceIte] at hr ⊢
        cases ht : fe.findTable? S with
        | none =>
          simp only [ht] at hr
          obtain ⟨rfl, rfl⟩ := pure_run hr
          rw [hv.tableNone S ht]
          exact ⟨hs, TabLe.refl _, rfl, rfl⟩
        | some tbl =>
          simp only [ht] at hr
          obtain ⟨ct, hct, hcctor, hnF, hnP, -⟩ := hv.table S tbl ht
          rw [hct]
          simp only
          rw [hcctor, hnF, hnP]
          by_cases h2 : (appArgs w).length = tbl.numParams
          · simp only [h2, ↓reduceIte] at hr ⊢
            cases hcv : fe.ctorView? tbl.ctor with
            | none =>
              simp only [hcv] at hr
              obtain ⟨rfl, rfl⟩ := pure_run hr
              refine ⟨hs, TabLe.refl _, rfl, ?_⟩
              have hn := hv.ctorNone tbl.ctor hcv
              cases hf : env.find? (toName tbl.ctor) with
              | none => rfl
              | some ci =>
                cases ci with
                | ctorInfo ccv nP nF T => exact absurd hf (hn ccv nP nF T)
                | _ => rfl
            | some x =>
              obtain ⟨cvC, nPc, nFc, TC⟩ := x
              simp only [hcv] at hr
              obtain ⟨ccvC, hcvC, hLC⟩ := hv.ctor tbl.ctor cvC nPc nFc TC hcv
              rw [hLC]
              simp only
              rw [hcvC.2.1]
              obtain ⟨cty, s₁, h1, hr⟩ := bind_run hr
              obtain ⟨hs1, hle1, hok1, htr1⟩ := tripleI_iff_run.1
                (instLevelParamsM_specI (mode := mode) (eager := eager) (env := env) hs
                  (hcvC.2.2.okS s₀) hcvC.2.2.1 hus) cty s₁ h1
              obtain ⟨rfl, rfl⟩ := pure_run hr
              have hty : TrS s₀ cvC.type = ccvC.type := hcvC.2.2.trS s₀
              rw [hty] at htr1
              obtain ⟨hpok, hpeq⟩ := peelPis_map_TrS s₁ tbl.numParams cty hok1
              have hargs : OkSL s₁ (appArgs w) = true :=
                OkSL_of_tabLe hle1 (OkSL_appArgs (s := s₀) hok)
              have htargs : TrSL s₁ (appArgs w) = (TrS s₀ w).getAppArgs := by
                rw [TrSL_of_tabLe hle1 (OkSL_appArgs (s := s₀) hok), TrSL_appArgs]
              have hcl : AllClosed (TrSL s₁ (appArgs w).reverse) = true := by
                have := allClosed_getAppArgs hc
                rw [← htargs] at this
                simpa [TrSL, AllClosed, List.map_reverse] using this
              unfold ConLeche.unitFieldTele
              rw [← htr1, hpeq]
              refine ⟨hs1, hle1, ?_, ?_⟩
              · cases hp : InLean.peelPis tbl.numParams cty with
                | none => rfl
                | some body =>
                  exact (TrS_instI (hpok body hp) (OkSL_reverse s₁ hargs) hcl).1
              · cases hp : InLean.peelPis tbl.numParams cty with
                | none => rfl
                | some body =>
                  simp only [Option.map_some, trUnitShape]
                  rw [(TrS_instI (hpok body hp) (OkSL_reverse s₁ hargs) hcl).2]
                  rw [← htargs]
                  simp only [TrSL, List.map_reverse]
          · simp only [h2, ↓reduceIte] at hr ⊢
            obtain ⟨rfl, rfl⟩ := pure_run hr
            exact ⟨hs, TabLe.refl _, rfl, rfl⟩
      · simp only [h1, ↓reduceIte] at hr ⊢
        obtain ⟨rfl, rfl⟩ := pure_run hr
        exact ⟨hs, TabLe.refl _, rfl, rfl⟩
  · have hnone : InLean.unitLikeShapeM fe w = pure none := by
      unfold InLean.unitLikeShapeM
      split
      · rename_i h; exact absurd h (hx _ _)
      · rfl
    rw [← InLean.unitLikeShapeM.eq_def] at hr
    rw [hnone] at hr
    obtain ⟨rfl, rfl⟩ := pure_run hr
    refine ⟨hs, TabLe.refl _, rfl, ?_⟩
    split
    · rename_i h; exact absurd h (hhd _ _)
    · rfl

/-- The structure arm (`unitLikeStructC_spec`'s twin), given the field test's spec. -/
theorem unitLikeStructI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode mi eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    {ulf : Nat} {ul' : Nat → ConLeche.Expr → ConLeche.FueledM Bool}
    (hul : UnitLikeSpecI mode eager env (InLean.unitLikeLoopI mi fe eager lv ulf) ul') {d : Nat}
    {w : Expr} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (hok : OkS s₀ w = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ w)) (hc : (TrS s₀ w).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.unitLikeStructI mi fe eager lv ulf d w
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.unitLikeStruct (ConLeche.fueledFns mode eager env) ul' env d (TrS s₀ w)) v;
        ⊤⦄ := by
  refine tripleI_iff_run.2 fun v s' hr => ?_
  rw [InLean.unitLikeStructI.eq_def] at hr
  obtain ⟨o, s₁, h1, hr⟩ := bind_run hr
  obtain ⟨hs1, hle1, hok1, htr1⟩ := tripleI_iff_run.1 (unitLikeShapeM_specI hfe hs hok hc) o s₁ h1
  unfold ConLeche.unitLikeStruct
  rw [← htr1]
  match o, hok1, htr1 with
  | none, _, _ =>
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact ⟨hs1, hle1, Runs.pure _⟩
  | some (tele, n), hokt, htr =>
    simp only [okUnitShape] at hokt
    simp only [trUnitShape] at htr ⊢
    obtain ⟨hs', hle', hrun⟩ := tripleI_iff_run.1 (unitLikeFieldsI_spec ih hul hs1 hokt
      (ConLeche.unitLikeShape_WScoped henv hw htr.symm)
      (unitLikeShape_closed henv hc htr.symm)) v s' hr
    exact ⟨hs', hle1.trans hle', hrun⟩

theorem unitLikeFuel_eq : InLean.unitLikeFuel = ConLeche.unitLikeFuel := by
  unfold InLean.unitLikeFuel ConLeche.unitLikeFuel; rfl

/-- `unitLikeLoop` at a successor, its `∀` match spelled out. -/
theorem unitLikeLoop_succ_eq {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (env : ConLeche.Env) (fuel d : Nat) (T : ConLeche.Expr) :
    ConLeche.unitLikeLoop r env (fuel + 1) d T = (do
      let w ← r.whnf d T
      match w with
      | .forallE dom body =>
        ConLeche.unitLikeLoop r env fuel (d + 1) (body.instantiate1 (.fvar d dom))
      | _ => ConLeche.unitLikeStruct r (ConLeche.unitLikeLoop r env fuel) env d w) := by
  rw [ConLeche.unitLikeLoop]
  rfl

/-- The unit-like test (`unitLikeLoopC_spec`'s twin). -/
theorem unitLikeLoopI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode mi eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env) :
    ∀ {fuel : Nat}, UnitLikeSpecI mode eager env (InLean.unitLikeLoopI mi fe eager lv fuel)
      (ConLeche.unitLikeLoop (ConLeche.fueledFns mode eager env) env fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d T s₀ hs hok hw hc
    sym only [conleche_grind, ConLeche.unitLikeLoop] =>
      vcgen [InLean.unitLikeLoopI.eq_def] <;> finish
  | succ fuel ihf =>
    intro d T s₀ hs hok hw hc
    sym only [conleche_grind, unitLikeLoop_succ_eq] =>
      vcgen [InLean.unitLikeLoopI.eq_def, ih.whnf,
        mkFVarM_specI (mode := mode) (eager := eager) (env := env), ihf,
        unitLikeStructI_spec ih hfe henv ihf] <;> finish

/-- `structUnitCertI` (`structUnitCertC_spec`'s twin). -/
theorem structUnitCertI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode mi eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.structUnitCertI mi fe eager lv d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.structUnitCert (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.structUnitCert, unitLikeFuel_eq] =>
    vcgen [InLean.structUnitCertI.eq_def, ih.inferIO, ih.whnf, ih.defeq,
      unitLikeLoopI_spec ih hfe henv] <;> finish

/-- `stuckIrrelI` (`stuckIrrelC_spec`'s twin). -/
theorem stuckIrrelI_spec {fe : InLean.FEnv} (ih : KnotSpecI mode mi eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env) (hlist : DefEqListSpecI mode mi eager env fe lv)
    {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.stuckIrrelI mi fe eager lv d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.stuckIrrel (ConLeche.fueledFns mode eager env) env d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.stuckIrrel] =>
    vcgen [InLean.stuckIrrelI.eq_def, structEtaCertI_spec ih hfe hlist,
      structUnitCertI_spec ih hfe henv, proofIrrelI_spec ih] <;> finish

end Walks

/-! ## The accumulator arrays through the translation -/

section Arrays
variable (s : InLean.CState)

@[conleche_grind =] theorem TrSL_push_rev (fvs : Array Expr) (a : Expr) :
    (TrSL s (fvs.push a).toList).reverse = TrS s a :: (TrSL s fvs.toList).reverse := by
  simp [TrSL]

@[conleche_grind =] theorem OkSL_push (fvs : Array Expr) (a : Expr) :
    OkSL s (fvs.push a).toList = (OkSL s fvs.toList && OkS s a) := by
  simp [OkSL, List.all_append, Bool.and_comm]

@[conleche_grind =] theorem AllClosed_push (fvs : Array Expr) (a : Expr) :
    AllClosed (TrSL s (fvs.push a).toList) =
      (AllClosed (TrSL s fvs.toList) && (TrS s a).looseBVarsBounded 0) := by
  simp [AllClosed, TrSL, List.all_append]

@[conleche_grind =] theorem TrSL_singleton_rev (a : Expr) :
    (TrSL s (#[a] : Array Expr).toList).reverse = [TrS s a] := by
  simp [TrSL]

@[conleche_grind =] theorem TrSL_empty_rev :
    (TrSL s (#[] : Array Expr).toList).reverse = [] := by
  simp [TrSL]

@[conleche_grind =] theorem OkSL_singleton (a : Expr) :
    OkSL s (#[a] : Array Expr).toList = OkS s a := by
  simp [OkSL]

@[conleche_grind =] theorem OkSL_empty : OkSL s (#[] : Array Expr).toList = true := by
  simp [OkSL]

@[conleche_grind =] theorem AllClosed_singleton (a : Expr) :
    AllClosed (TrSL s (#[a] : Array Expr).toList) = (TrS s a).looseBVarsBounded 0 := by
  simp [AllClosed, TrSL]

@[conleche_grind =] theorem AllClosed_empty : AllClosed (TrSL s (#[] : Array Expr).toList) = true := by
  simp [AllClosed, TrSL]

end Arrays

section ClosedBinders
open ConLeche.Expr

/-- One binder opened at a closed value: the body, instantiated with it in
front of the accumulator, is closed (`wscoped_open_binder`'s twin). -/
theorem lbb_open_binder {a body : ConLeche.Expr} {ws : List ConLeche.Expr}
    (ha : a.looseBVarsBounded 0 = true) (hb : (body.instantiateList ws 1).looseBVarsBounded 1 = true) :
    (body.instantiateList (a :: ws)).looseBVarsBounded 0 = true := by
  rw [ConLeche.Expr.instantiateList_cons]
  exact looseBVarsBounded_instantiate1_gen ha hb
grind_pattern [conleche_grind] lbb_open_binder => body.instantiateList (a :: ws)

/-- Both sides of a pair of binders, opened over the accumulator `vs`, are
closed where present (`OptBinderPairWS`'s companion: InLean's knot takes
closed terms). -/
@[expose] def OptBinderPairCl (vs : List ConLeche.Expr) :
    Option (ConLeche.Expr × ConLeche.Expr × ConLeche.Expr × ConLeche.Expr) → Prop
  | none => True
  | some q =>
    (q.1.instantiateList vs).looseBVarsBounded 0 = true ∧
      (q.2.1.instantiateList vs 1).looseBVarsBounded 1 = true ∧
      (q.2.2.1.instantiateList vs).looseBVarsBounded 0 = true ∧
      (q.2.2.2.instantiateList vs 1).looseBVarsBounded 1 = true

@[conleche_grind =] theorem OptBinderPairCl.some_eq (vs : List ConLeche.Expr)
    (q : ConLeche.Expr × ConLeche.Expr × ConLeche.Expr × ConLeche.Expr) :
    OptBinderPairCl vs (some q) = ((q.1.instantiateList vs).looseBVarsBounded 0 = true ∧
      (q.2.1.instantiateList vs 1).looseBVarsBounded 1 = true ∧
      (q.2.2.1.instantiateList vs).looseBVarsBounded 0 = true ∧
      (q.2.2.2.instantiateList vs 1).looseBVarsBounded 1 = true) := rfl

theorem lbb_binderPair? {lam : Bool} {b₁ b₂ : ConLeche.Expr} {vs : List ConLeche.Expr}
    (h₁ : (b₁.instantiateList vs).looseBVarsBounded 0 = true)
    (h₂ : (b₂.instantiateList vs).looseBVarsBounded 0 = true) :
    OptBinderPairCl vs (ConLeche.Expr.binderPair? lam b₁ b₂) := by
  cases h : ConLeche.Expr.binderPair? lam b₁ b₂ with
  | none => trivial
  | some q =>
    obtain ⟨t₁, c₁, t₂, c₂⟩ := q
    obtain ⟨rfl, rfl⟩ := ConLeche.Expr.binderPair?_some h
    cases lam <;>
      simp only [ConLeche.Expr.binderOf, instList_lam_eq, instList_forallE_eq,
        ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h₁ h₂ <;>
      exact ⟨h₁.1, h₁.2, h₂.1, h₂.2⟩
grind_pattern [conleche_grind] lbb_binderPair? =>
  (b₁.instantiateList vs).looseBVarsBounded 0, (b₂.instantiateList vs).looseBVarsBounded 0,
    ConLeche.Expr.binderPair? lam b₁ b₂

end ClosedBinders

grind_pattern [conleche_grind] binderPairI_some =>
  InLean.Expr.binderPair? lam a b, TrS s a, some q
grind_pattern [conleche_grind] binderPairI_none =>
  InLean.Expr.binderPair? lam a b, TrS s a, TrS s b

/-! ## DiscC5's twins: definitional equality -/

section Walks5

variable {fe : InLean.FEnv} {lv : Nat}

/-- The innermost level of the binder-telescope comparison
(`defeqBindersInnerC_spec`'s twin). -/
theorem defeqBindersInnerI_spec (ih : KnotSpecI .verified .verified eager env fe lv) {lam : Bool} {d : Nat}
    {b₁ b₂ : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hok1 : OkS s₀ b₁ = true) (hok2 : OkS s₀ b₂ = true)
    (h1 : ConLeche.Expr.WScoped (d + 1) (TrS s₀ b₁)) (h2 : ConLeche.Expr.WScoped (d + 1) (TrS s₀ b₂))
    (hc1 : (TrS s₀ b₁).looseBVarsBounded 0 = true) (hc2 : (TrS s₀ b₂).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqBindersInnerI .verified fe eager lv lam d b₁ b₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqBindersInner .verified (ConLeche.fueledFns .verified eager env) lam d
        (TrS s₀ b₁) (TrS s₀ b₂)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqBindersInner] =>
    vcgen [InLean.defeqBindersInnerI.eq_def, ih.defeq, ih.infer] <;> finish

/-- One level's domain comparison (`defeqDomainC_spec`'s twin). -/
theorem defeqDomainI_spec (ih : KnotSpecI .verified .verified eager env fe lv) {d : Nat} {fvs : Array Expr}
    {ty₁ ty₂ dom₂ : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hok1 : OkS s₀ ty₁ = true) (hok2 : OkS s₀ ty₂ = true) (hokd : OkS s₀ dom₂ = true)
    (hfv : OkSL s₀ fvs.toList = true) (hfc : AllClosed (TrSL s₀ fvs.toList) = true)
    (h1 : ConLeche.Expr.WScoped d ((TrS s₀ ty₁).instantiateList (TrSL s₀ fvs.toList).reverse))
    (h2 : ConLeche.Expr.WScoped d (TrS s₀ dom₂))
    (hc1 : ((TrS s₀ ty₁).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true)
    (hc2 : (TrS s₀ dom₂).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqDomainI .verified fe eager lv d fvs ty₁ ty₂ dom₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqDomain (ConLeche.fueledFns .verified eager env) d
        (TrSL s₀ fvs.toList).reverse (TrS s₀ ty₁) (TrS s₀ ty₂) (TrS s₀ dom₂)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqDomain] =>
    vcgen [InLean.defeqDomainI.eq_def, instListRevM_specI (mode := .verified) (eager := eager) (env := env), ih.defeq] <;> finish

/-- InLean's innermost level on the bulk-opened bodies (`bindersLeafI`'s
twin). -/
@[expose] def bindersLeafL (fe : InLean.FEnv) (eager : Bool) (lv : Nat) (lam : Bool) (d : Nat) (fvs : Array Expr)
    (b₁ b₂ : Expr) : InLean.CheckCM Bool := do
  let o₁ ← instListRevM b₁ fvs
  let o₂ ← instListRevM b₂ fvs
  InLean.defeqBindersInnerI .verified fe eager lv lam d o₁ o₂

/-- InLean's binder-telescope comparison past the domains (`bindersStepI`'s
twin). -/
@[expose] def bindersStepL (fe : InLean.FEnv) (eager : Bool) (lv : Nat) (lam : Bool) (n d : Nat) (fvs : Array Expr)
    (b₁ b₂ : Expr) : InLean.CheckCM Bool :=
  match InLean.Expr.binderPair? lam b₁ b₂ with
  | some q => InLean.defeqBindersI .verified fe eager lv lam n (d + 1) fvs q.1 q.2.1 q.2.2.1 q.2.2.2
  | none => bindersLeafL fe eager lv lam d fvs b₁ b₂

theorem defeqBindersL_zero {fe : InLean.FEnv} (lv : Nat) (lam : Bool) (d : Nat) (fvs : Array Expr)
    (ty₁ body₁ ty₂ body₂ : Expr) :
    InLean.defeqBindersI .verified fe eager lv lam 0 d fvs ty₁ body₁ ty₂ body₂ = (do
      let dom₂ ← instListRevM ty₂ fvs
      unless ← InLean.defeqDomainI .verified fe eager lv d fvs ty₁ ty₂ dom₂ do return false
      let fv ← mkFVarM d dom₂
      let fvs' ← pure (fvs.push fv)
      bindersLeafL fe eager lv lam d fvs' body₁ body₂ : InLean.CheckCM Bool) := by
  rw [InLean.defeqBindersI.eq_def]; rfl

set_option smartUnfolding false in
/-- `defeqBindersI`'s step (as `defeqBindersI_succ`: the structural recursion
sits under the binds, where no equation is generated). -/
theorem defeqBindersL_succ {fe : InLean.FEnv} (lv : Nat) (lam : Bool) (n d : Nat) (fvs : Array Expr)
    (ty₁ body₁ ty₂ body₂ : Expr) :
    InLean.defeqBindersI .verified fe eager lv lam (n + 1) d fvs ty₁ body₁ ty₂ body₂ = (do
      let dom₂ ← instListRevM ty₂ fvs
      unless ← InLean.defeqDomainI .verified fe eager lv d fvs ty₁ ty₂ dom₂ do return false
      let fv ← mkFVarM d dom₂
      let fvs' ← pure (fvs.push fv)
      bindersStepL fe eager lv lam n d fvs' body₁ body₂ : InLean.CheckCM Bool) := by
  rw [InLean.defeqBindersI.eq_def]
  refine congrArg (instListRevM ty₂ fvs >>= ·) (funext fun dom₂ => ?_)
  refine congrArg (InLean.defeqDomainI .verified fe eager lv d fvs ty₁ ty₂ dom₂ >>= ·) (funext fun x => ?_)
  cases x
  · rfl
  · refine congrArg (mkFVarM d dom₂ >>= ·) (funext fun fv => ?_)
    refine congrArg (pure (fvs.push fv) >>= ·) (funext fun fvs' => ?_)
    unfold bindersStepL
    cases InLean.Expr.binderPair? lam body₁ body₂ with
    | none => rfl
    | some q => rfl

/-- The binder-telescope comparison at fuel `n` (`BindersSpec`'s twin, a
named predicate: an atom in `grind`'s context).  The scope and closedness
facts are the level's parts opened over the accumulator. -/
@[expose] def BindersSpecI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat) (n : Nat) :
    Prop :=
  ∀ {lam : Bool} {d : Nat} {fvs : Array Expr} {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : InLean.CState},
    CSOKI .verified eager env s₀ →
    OkS s₀ ty₁ = true → OkS s₀ body₁ = true → OkS s₀ ty₂ = true → OkS s₀ body₂ = true →
    OkSL s₀ fvs.toList = true → AllClosed (TrSL s₀ fvs.toList) = true →
    ConLeche.Expr.WScoped d ((TrS s₀ ty₁).instantiateList (TrSL s₀ fvs.toList).reverse) →
    ConLeche.Expr.WScoped d ((TrS s₀ body₁).instantiateList (TrSL s₀ fvs.toList).reverse 1) →
    ConLeche.Expr.WScoped d ((TrS s₀ ty₂).instantiateList (TrSL s₀ fvs.toList).reverse) →
    ConLeche.Expr.WScoped d ((TrS s₀ body₂).instantiateList (TrSL s₀ fvs.toList).reverse 1) →
    ((TrS s₀ ty₁).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true →
    ((TrS s₀ body₁).instantiateList (TrSL s₀ fvs.toList).reverse 1).looseBVarsBounded 1 = true →
    ((TrS s₀ ty₂).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true →
    ((TrS s₀ body₂).instantiateList (TrSL s₀ fvs.toList).reverse 1).looseBVarsBounded 1 = true →
    ⦃fun s => s = s₀⦄ InLean.defeqBindersI .verified fe eager lv lam n d fvs ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqBinders .verified (ConLeche.fueledFns .verified eager env) lam n d
        (TrSL s₀ fvs.toList).reverse (TrS s₀ ty₁) (TrS s₀ body₁) (TrS s₀ ty₂) (TrS s₀ body₂)) v; ⊤⦄

theorem BindersSpecI.triple {n : Nat} (h : BindersSpecI eager env fe lv n) {lam : Bool} {d : Nat}
    {fvs : Array Expr} {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : InLean.CState}
    (hs : CSOKI .verified eager env s₀)
    (o1 : OkS s₀ ty₁ = true) (o2 : OkS s₀ body₁ = true) (o3 : OkS s₀ ty₂ = true)
    (o4 : OkS s₀ body₂ = true) (ofv : OkSL s₀ fvs.toList = true)
    (ofc : AllClosed (TrSL s₀ fvs.toList) = true)
    (w1 : ConLeche.Expr.WScoped d ((TrS s₀ ty₁).instantiateList (TrSL s₀ fvs.toList).reverse))
    (w2 : ConLeche.Expr.WScoped d ((TrS s₀ body₁).instantiateList (TrSL s₀ fvs.toList).reverse 1))
    (w3 : ConLeche.Expr.WScoped d ((TrS s₀ ty₂).instantiateList (TrSL s₀ fvs.toList).reverse))
    (w4 : ConLeche.Expr.WScoped d ((TrS s₀ body₂).instantiateList (TrSL s₀ fvs.toList).reverse 1))
    (c1 : ((TrS s₀ ty₁).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true)
    (c2 : ((TrS s₀ body₁).instantiateList (TrSL s₀ fvs.toList).reverse 1).looseBVarsBounded 1 = true)
    (c3 : ((TrS s₀ ty₂).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true)
    (c4 : ((TrS s₀ body₂).instantiateList (TrSL s₀ fvs.toList).reverse 1).looseBVarsBounded 1 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqBindersI .verified fe eager lv lam n d fvs ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqBinders .verified (ConLeche.fueledFns .verified eager env) lam n d
        (TrSL s₀ fvs.toList).reverse (TrS s₀ ty₁) (TrS s₀ body₁) (TrS s₀ ty₂) (TrS s₀ body₂)) v; ⊤⦄ :=
  h hs o1 o2 o3 o4 ofv ofc w1 w2 w3 w4 c1 c2 c3 c4

theorem bindersLeafL_spec (ih : KnotSpecI .verified .verified eager env fe lv) {lam : Bool} {d : Nat}
    {fvs : Array Expr} {b₁ b₂ : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hok1 : OkS s₀ b₁ = true) (hok2 : OkS s₀ b₂ = true) (hfv : OkSL s₀ fvs.toList = true)
    (hfc : AllClosed (TrSL s₀ fvs.toList) = true)
    (h1 : ConLeche.Expr.WScoped (d + 1) ((TrS s₀ b₁).instantiateList (TrSL s₀ fvs.toList).reverse))
    (h2 : ConLeche.Expr.WScoped (d + 1) ((TrS s₀ b₂).instantiateList (TrSL s₀ fvs.toList).reverse))
    (hc1 : ((TrS s₀ b₁).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true)
    (hc2 : ((TrS s₀ b₂).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ bindersLeafL fe eager lv lam d fvs b₁ b₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (bindersLeafP (ConLeche.fueledFns .verified eager env) .verified lam d
        (TrSL s₀ fvs.toList).reverse (TrS s₀ b₁) (TrS s₀ b₂)) v; ⊤⦄ := by
  sym only [conleche_grind, bindersLeafP] =>
    vcgen [bindersLeafL, instListRevM_specI (mode := .verified) (eager := eager) (env := env), defeqBindersInnerI_spec ih] <;> finish

theorem bindersStepL_spec (ih : KnotSpecI .verified .verified eager env fe lv) {n : Nat}
    (hn : BindersSpecI eager env fe lv n) {lam : Bool} {d : Nat} {fvs : Array Expr} {b₁ b₂ : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hok1 : OkS s₀ b₁ = true) (hok2 : OkS s₀ b₂ = true) (hfv : OkSL s₀ fvs.toList = true)
    (hfc : AllClosed (TrSL s₀ fvs.toList) = true)
    (h1 : ConLeche.Expr.WScoped (d + 1) ((TrS s₀ b₁).instantiateList (TrSL s₀ fvs.toList).reverse))
    (h2 : ConLeche.Expr.WScoped (d + 1) ((TrS s₀ b₂).instantiateList (TrSL s₀ fvs.toList).reverse))
    (hc1 : ((TrS s₀ b₁).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true)
    (hc2 : ((TrS s₀ b₂).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ bindersStepL fe eager lv lam n d fvs b₁ b₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (bindersStepP (ConLeche.fueledFns .verified eager env) .verified lam n d
        (TrSL s₀ fvs.toList).reverse (TrS s₀ b₁) (TrS s₀ b₂)) v; ⊤⦄ := by
  sym only [conleche_grind, bindersStepP] =>
    vcgen [bindersStepL, bindersLeafL_spec ih, hn.triple] <;> finish

/-- By induction on the descent budget (`bindersSpec_all`'s twin). -/
theorem bindersSpecI_all (ih : KnotSpecI .verified .verified eager env fe lv) (fuel : Nat) :
    BindersSpecI eager env fe lv fuel := by
  induction fuel with
  | zero =>
    intro lam d fvs ty₁ body₁ ty₂ body₂ s₀ hs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    sym only [conleche_grind, defeqBinders_zero] =>
      vcgen [defeqBindersL_zero, instListRevM_specI (mode := .verified) (eager := eager) (env := env), defeqDomainI_spec ih,
        mkFVarM_specI (mode := .verified) (eager := eager) (env := env),
        bindersLeafL_spec ih] <;> finish
  | succ n ihn =>
    intro lam d fvs ty₁ body₁ ty₂ body₂ s₀ hs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    sym only [conleche_grind, defeqBinders_succ] =>
      vcgen [defeqBindersL_succ, instListRevM_specI (mode := .verified) (eager := eager) (env := env), defeqDomainI_spec ih,
        mkFVarM_specI (mode := .verified) (eager := eager) (env := env),
        bindersStepL_spec ih ihn] <;> finish

/-- The binder-telescope comparison from the empty accumulator
(`defeqBindersC_spec`'s twin). -/
theorem defeqBindersI_spec (ih : KnotSpecI .verified .verified eager env fe lv) (fuel : Nat) {lam : Bool}
    {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (o1 : OkS s₀ ty₁ = true) (o2 : OkS s₀ body₁ = true) (o3 : OkS s₀ ty₂ = true)
    (o4 : OkS s₀ body₂ = true)
    (w1 : ConLeche.Expr.WScoped d (TrS s₀ ty₁)) (w2 : ConLeche.Expr.WScoped d (TrS s₀ body₁))
    (w3 : ConLeche.Expr.WScoped d (TrS s₀ ty₂)) (w4 : ConLeche.Expr.WScoped d (TrS s₀ body₂))
    (c1 : (TrS s₀ ty₁).looseBVarsBounded 0 = true) (c2 : (TrS s₀ body₁).looseBVarsBounded 1 = true)
    (c3 : (TrS s₀ ty₂).looseBVarsBounded 0 = true) (c4 : (TrS s₀ body₂).looseBVarsBounded 1 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqBindersI .verified fe eager lv lam fuel d #[] ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqBinders .verified (ConLeche.fueledFns .verified eager env) lam fuel d []
        (TrS s₀ ty₁) (TrS s₀ body₁) (TrS s₀ ty₂) (TrS s₀ body₂)) v; ⊤⦄ := by
  have he : (TrSL s₀ (#[] : Array Expr).toList).reverse = [] := TrSL_empty_rev s₀
  have h := BindersSpecI.triple (bindersSpecI_all ih fuel) (lam := lam) (fvs := #[]) hs o1 o2 o3 o4
    (OkSL_empty s₀) (AllClosed_empty s₀)
    (by rw [he, ConLeche.Expr.instantiateList_nil]; exact w1)
    (by rw [he, ConLeche.Expr.instantiateList_nil]; exact w2)
    (by rw [he, ConLeche.Expr.instantiateList_nil]; exact w3)
    (by rw [he, ConLeche.Expr.instantiateList_nil]; exact w4)
    (by rw [he, ConLeche.Expr.instantiateList_nil]; exact c1)
    (by rw [he, ConLeche.Expr.instantiateList_nil]; exact c2)
    (by rw [he, ConLeche.Expr.instantiateList_nil]; exact c3)
    (by rw [he, ConLeche.Expr.instantiateList_nil]; exact c4)
  rwa [he] at h

/-- The easy cases (`quickDefEqC_spec`'s twin). -/
theorem quickDefEqI_spec (ih : KnotSpecI .verified .verified eager env fe lv) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.quickDefEqI .verified fe eager lv d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.quickDefEq .verified (ConLeche.fueledFns .verified eager env) d (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.quickDefEq.eq_def, bindersFuel_eq] =>
    vcgen [InLean.quickDefEqI.eq_def, ih.defeq, mkFVarM_specI (mode := .verified) (eager := eager)
        (env := env), isEquivLM_specI (mode := .verified) (eager := eager) (env := env),
      liftFueled_specI (mode := .verified) (eager := eager) (env := env),
      defeqBindersI_spec ih InLean.bindersFuel] <;> finish

/-- Offsets (`defeqOffsetC_spec`'s twin). -/
theorem defeqOffsetI_spec (ih : KnotSpecI mode mi eager env fe lv) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqOffsetI mi fe eager lv d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqOffset (ConLeche.fueledFns mode eager env) d (TrS s₀ a) (TrS s₀ b)) v;
        ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqOffset] =>
    vcgen [InLean.defeqOffsetI.eq_def, ih.defeq] <;> finish

/-- `try_unfold_proj_app` (`tryUnfoldProjAppC_spec`'s twin). -/
theorem tryUnfoldProjAppI_spec (ih : KnotSpecI mode mi eager env fe lv) {d : Nat} {e : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ e)) (hc : (TrS s₀ e).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.tryUnfoldProjAppI mi fe eager lv d e
    ⦃fun o s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (ConLeche.tryUnfoldProjApp (ConLeche.fueledFns mode eager env) d (TrS s₀ e)) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.tryUnfoldProjApp] =>
    vcgen [InLean.tryUnfoldProjAppI.eq_def, ih.whnfCore] <;> finish

/-- The end of a step (`deltaQuickC_spec`'s twin). -/
theorem deltaQuickI_spec (ih : KnotSpecI .verified .verified eager env fe lv) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.deltaQuickI .verified fe eager lv d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkDS s' v = true ∧
      Runs (ConLeche.deltaQuick .verified (ConLeche.fueledFns .verified eager env) d (TrS s₀ a)
        (TrS s₀ b)) (TrDS s' v) ∧
      StepPairWS d (TrDS s' v) ∧ StepClosedD (TrDS s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.deltaQuick] =>
    vcgen [InLean.deltaQuickI.eq_def, quickDefEqI_spec ih] <;> finish

/-- One lazy-delta step (`lazyDeltaStepC_spec`'s twin). -/
theorem lazyDeltaStepI_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified .verified eager env fe lv)
    {d : Nat} {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.lazyDeltaStepI .verified fe eager lv d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkDS s' v = true ∧
      Runs (ConLeche.lazyDeltaStep .verified (ConLeche.fueledFns .verified eager env) env d
        (TrS s₀ a) (TrS s₀ b)) (TrDS s' v) ∧
      StepPairWS d (TrDS s' v) ∧ StepClosedD (TrDS s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.lazyDeltaStep, ConLeche.unfoldDefinition_WScoped henv] =>
    vcgen [InLean.lazyDeltaStepI.eq_def, tryUnfoldProjAppI_spec ih, deltaQuickI_spec ih, ih.whnfCore,
      hunf, hspine] <;> finish

/-! The lazy-delta loop's continuations, named as the pure ones are
(`ldr…P`, `DiscC5.lean`), each block its own triple. -/

/-- Past the step. -/
@[expose] def ldrStepL (eager : Bool) (fe : InLean.FEnv) (lv : Nat) (d n : Nat)
    (a b : Expr) : InLean.DeltaStep → InLean.CheckCM InLean.LazyRes
  | .cont a' b' => InLean.lazyDeltaReductionI .verified fe eager lv d n a' b'
  | .eq => pure (.verdict true)
  | .diff => pure (.verdict false)
  | .unknown => pure (.unknown a b)

/-- Past the right literal acceleration. -/
@[expose] def ldrNatBL (eager : Bool) (fe : InLean.FEnv) (lv : Nat) (d n : Nat)
    (a b : Expr) : Option Expr → InLean.CheckCM InLean.LazyRes
  | some b₂ => do
    let v ← InLean.defeqI .verified fe eager lv d a b₂
    pure (.verdict v)
  | none => InLean.lazyDeltaStepI .verified fe eager lv d a b >>= ldrStepL eager fe lv d n a b

/-- Past the left literal acceleration. -/
@[expose] def ldrNatAL (eager : Bool) (fe : InLean.FEnv) (lv : Nat) (d n : Nat)
    (a b : Expr) (fold : Bool) : Option Expr → InLean.CheckCM InLean.LazyRes
  | some a₂ => do
    let v ← InLean.defeqI .verified fe eager lv d a₂ b
    pure (.verdict v)
  | none =>
    (if fold then InLean.reduceNatI .verified fe eager lv d b else pure none) >>= ldrNatBL eager fe lv d n a b

/-- Past the offset check. -/
@[expose] def ldrOffL (eager : Bool) (fe : InLean.FEnv) (lv : Nat) (d n : Nat)
    (a b : Expr) : Option Bool → InLean.CheckCM InLean.LazyRes
  | some v => pure (.verdict v)
  | none =>
    (if eager || (!a.hasFVar && !b.hasFVar) then InLean.reduceNatI .verified fe eager lv d a else pure none) >>=
      ldrNatAL eager fe lv d n a b (eager || (!a.hasFVar && !b.hasFVar))

/-- The loop's step with its continuations named. -/
theorem lazyDeltaReductionL_succ (lv : Nat) (d n : Nat)
    (a b : Expr) :
    InLean.lazyDeltaReductionI .verified fe eager lv d (n + 1) a b =
      InLean.defeqOffsetI .verified fe eager lv d a b >>= ldrOffL eager fe lv d n a b := by
  rw [InLean.lazyDeltaReductionI.eq_2]; rfl

/-- The lazy-delta loop at budget `n` (`LazySpec`'s twin, a named predicate). -/
@[expose] def LazySpecI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat)
    (d n : Nat) : Prop :=
  ∀ {a b : Expr} {s₀ : InLean.CState}, CSOKI .verified eager env s₀ →
    OkS s₀ a = true → OkS s₀ b = true →
    ConLeche.Expr.WScoped d (TrS s₀ a) → ConLeche.Expr.WScoped d (TrS s₀ b) →
    (TrS s₀ a).looseBVarsBounded 0 = true → (TrS s₀ b).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.lazyDeltaReductionI .verified fe eager lv d n a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ConLeche.lazyDeltaReduction .verified eager (ConLeche.fueledFns .verified eager env)
        env d n (TrS s₀ a) (TrS s₀ b)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄

theorem LazySpecI.triple {fe : InLean.FEnv} {d n : Nat} (h : LazySpecI eager env fe lv d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.lazyDeltaReductionI .verified fe eager lv d n a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ConLeche.lazyDeltaReduction .verified eager (ConLeche.fueledFns .verified eager env)
        env d n (TrS s₀ a) (TrS s₀ b)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ :=
  h hs hoka hokb hwa hwb hca hcb

theorem ldrStepL_spec {fe : InLean.FEnv} {d n : Nat} (hn : LazySpecI eager env fe lv d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (st : InLean.DeltaStep)
    (hok : OkDS s₀ st = true) (hst : StepPairWS d (TrDS s₀ st))
    (hcst : StepClosedD (TrDS s₀ st) = true) :
    ⦃fun s => s = s₀⦄ ldrStepL eager fe lv d n a b st
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ldrStepP (ConLeche.fueledFns .verified eager env) env d .verified eager n (TrS s₀ a)
        (TrS s₀ b) (TrDS s₀ st)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ldrStepP] =>
    vcgen [ldrStepL, LazySpecI.triple hn] <;> finish

theorem ldrNatBL_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified .verified eager env fe lv)
    {d n : Nat} (hn : LazySpecI eager env fe lv d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (o : Option Expr) (hok : OkO s₀ o = true)
    (ho : OptWS d (TrO s₀ o)) (hco : OptClosed (TrO s₀ o) = true) :
    ⦃fun s => s = s₀⦄ ldrNatBL eager fe lv d n a b o
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ldrNatBP (ConLeche.fueledFns .verified eager env) env d .verified eager n (TrS s₀ a)
        (TrS s₀ b) (TrO s₀ o)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ldrNatBP] =>
    vcgen [ldrNatBL, ih.defeq, lazyDeltaStepI_spec ih hfe henv hunf hspine, ldrStepL_spec hn] <;>
      finish

theorem ldrNatAL_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified .verified eager env fe lv)
    (hnat : ReduceNatSpecI .verified .verified eager env fe lv)
    {d n : Nat} (hn : LazySpecI eager env fe lv d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (o : Option Expr) (hok : OkO s₀ o = true)
    (ho : OptWS d (TrO s₀ o)) (hco : OptClosed (TrO s₀ o) = true) :
    ⦃fun s => s = s₀⦄ ldrNatAL eager fe lv d n a b (eager || (!a.hasFVar && !b.hasFVar)) o
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ldrNatAP (ConLeche.fueledFns .verified eager env) env d .verified eager n (TrS s₀ a)
        (TrS s₀ b) (TrO s₀ o)) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ldrNatAP] =>
    vcgen [ldrNatAL, ih.defeq, hnat, ldrNatBL_spec ih hfe henv hunf hspine hn] <;> finish

theorem ldrOffL_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified .verified eager env fe lv)
    (hnat : ReduceNatSpecI .verified .verified eager env fe lv)
    {d n : Nat} (hn : LazySpecI eager env fe lv d n)
    {a b : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (o : Option Bool) :
    ⦃fun s => s = s₀⦄ ldrOffL eager fe lv d n a b o
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkLR s' v = true ∧
      Runs (ldrOffP (ConLeche.fueledFns .verified eager env) env d .verified eager n (TrS s₀ a)
        (TrS s₀ b) o) (TrLR s' v) ∧
      LazyPairWS d (TrLR s' v) ∧ LazyClosed (TrLR s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ldrOffP] =>
    vcgen [ldrOffL, hnat, ldrNatAL_spec ih hfe henv hunf hspine hnat hn] <;> finish

/-- By induction on the step budget (`lazySpec_all`'s twin). -/
theorem lazySpecI_all {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified .verified eager env fe lv)
    (hnat : ReduceNatSpecI .verified .verified eager env fe lv) {d : Nat} (n : Nat) :
    LazySpecI eager env fe lv d n := by
  induction n with
  | zero =>
    intro a b s₀ hs _ _ _ _ _ _
    sym only [conleche_grind] => vcgen [InLean.lazyDeltaReductionI.eq_def] <;> finish
  | succ n ihn =>
    intro a b s₀ hs _ _ _ _ _ _
    sym only [conleche_grind, lazyDeltaReduction_succ] =>
      vcgen [lazyDeltaReductionL_succ, defeqOffsetI_spec ih,
        ldrOffL_spec ih hfe henv hunf hspine hnat ihn] <;> finish

/-- The projection loop at budget `n` (`LazyProjSpec`'s twin). -/
@[expose] def LazyProjSpecI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat)
    (d : Nat) (sn : Name) (ip n : Nat) : Prop :=
  ∀ {a b : Expr} {s₀ : InLean.CState}, CSOKI .verified eager env s₀ →
    OkS s₀ a = true → OkS s₀ b = true →
    ConLeche.Expr.WScoped d (TrS s₀ a) → ConLeche.Expr.WScoped d (TrS s₀ b) →
    (TrS s₀ a).looseBVarsBounded 0 = true → (TrS s₀ b).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.lazyDeltaProjReductionI .verified fe eager lv d sn ip n a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.lazyDeltaProjReduction .verified (ConLeche.fueledFns .verified eager env) env d
        (toName sn) ip n (TrS s₀ a) (TrS s₀ b)) v; ⊤⦄

theorem LazyProjSpecI.triple {fe : InLean.FEnv} {d : Nat} {sn : Name} {ip n : Nat}
    (h : LazyProjSpecI eager env fe lv d sn ip n) {a b : Expr} {s₀ : InLean.CState}
    (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.lazyDeltaProjReductionI .verified fe eager lv d sn ip n a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.lazyDeltaProjReduction .verified (ConLeche.fueledFns .verified eager env) env d
        (toName sn) ip n (TrS s₀ a) (TrS s₀ b)) v; ⊤⦄ :=
  h hs hoka hokb hwa hwb hca hcb

/-- By induction on the step budget (`lazyProjSpec_all`'s twin). -/
theorem lazyProjSpecI_all {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified .verified eager env fe lv)
    (hproj : ReduceProjSpecI eager env fe lv) {d : Nat} {sn : Name} {ip : Nat} (n : Nat) :
    LazyProjSpecI eager env fe lv d sn ip n := by
  induction n with
  | zero =>
    intro a b s₀ hs _ _ _ _ _ _
    sym only [conleche_grind] => vcgen [InLean.lazyDeltaProjReductionI.eq_def] <;> finish
  | succ n ihn =>
    intro a b s₀ hs _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.lazyDeltaProjReduction] =>
      vcgen [InLean.lazyDeltaProjReductionI.eq_def, lazyDeltaStepI_spec ih hfe henv hunf hspine, hproj,
        ih.defeq, LazyProjSpecI.triple ihn] <;> finish

/-- The proj/proj check (`defeqProjPairC_spec`'s twin). -/
theorem defeqProjPairI_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env)
    (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified .verified eager env fe lv)
    (hproj : ReduceProjSpecI eager env fe lv) {d : Nat} {a b : Expr} {s₀ : InLean.CState}
    (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqProjPairI .verified fe eager lv d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqProjPair .verified (ConLeche.fueledFns .verified eager env) env d
        (TrS s₀ a) (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqProjPair.eq_def, defeqLoopFuel_eq] =>
    vcgen [InLean.defeqProjPairI.eq_def,
      LazyProjSpecI.triple (lazyProjSpecI_all ih hfe henv hunf hspine hproj _)] <;> finish

/-- The stuck comparison (`defeqStuckC_spec`'s twin). -/
theorem defeqStuckI_spec {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv)
    (hfe : DefeqEnvI fe env) (henv : ConLeche.EnvWF env) (hlist : DefEqListSpecI .verified .verified eager env fe lv) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqStuckI .verified fe eager lv d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqStuck .verified (ConLeche.fueledFns .verified eager env) env d
        (TrS s₀ a) (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqStuck.eq_def, ConLeche.strLitToConstructor_WScoped] =>
    vcgen [InLean.defeqStuckI.eq_def, ih.defeq, stuckIrrelI_spec ih hfe henv hlist, etaCertI_spec ih, hlist,
      isEquivListLM_specI (mode := .verified) (eager := eager) (env := env),
      liftFueled_specI (mode := .verified) (eager := eager) (env := env)] <;> finish

/-! The body's continuations, named as the pure ones are (`body…P`,
`DiscC5.lean`), each block its own triple. -/

/-- Past the lazy-delta loop's stuck pair. -/
@[expose] def bodyTailL (fe : InLean.FEnv) (eager : Bool) (lv : Nat) (d : Nat) (a₁ b₁ : Expr) :
    InLean.CheckCM Bool := do
  if ← InLean.defeqProjPairI .verified fe eager lv d a₁ b₁ then pure true else
  if !(InLean.Expr.headIsProj a₁) && !(InLean.Expr.headIsProj b₁) then
    InLean.defeqStuckI .verified fe eager lv d a₁ b₁ else
  let a₂ ← InLean.whnfCoreI .verified fe eager lv false d a₁
  let b₂ ← InLean.whnfCoreI .verified fe eager lv false d b₁
  if a₂ == a₁ && b₂ == b₁ then InLean.defeqStuckI .verified fe eager lv d a₁ b₁
  else InLean.defeqI .verified fe eager lv d a₂ b₂

/-- The lazy-delta loop's outcome. -/
@[expose] def bodyLazyL (fe : InLean.FEnv) (eager : Bool) (lv : Nat) (d : Nat) :
    InLean.LazyRes → InLean.CheckCM Bool
  | .verdict v => pure v
  | .unknown a₁ b₁ => bodyTailL fe eager lv d a₁ b₁

/-- Past `quickDefEq` on the cheaply normalized pair. -/
@[expose] def bodyQ2L (eager : Bool) (fe : InLean.FEnv) (lv : Nat) (d : Nat)
    (a' b' : Expr) : Option Bool → InLean.CheckCM Bool
  | some v => pure v
  | none =>
    InLean.lazyDeltaReductionI .verified fe eager lv d InLean.defeqLoopFuel a' b' >>=
      bodyLazyL fe eager lv d

/-- Past proof irrelevance. -/
@[expose] def bodyPIL (eager : Bool) (fe : InLean.FEnv) (lv : Nat) (d : Nat)
    (a b : Expr) : InLean.CheckCM Bool := do
  if ← InLean.propIrrelI .verified fe eager lv d a b then pure true else
  let a' ← InLean.whnfCoreI .verified fe eager lv true d a
  let b' ← InLean.whnfCoreI .verified fe eager lv true d b
  InLean.quickDefEqI .verified fe eager lv d a' b' >>= bodyQ2L eager fe lv d a' b'

/-- Past `quickDefEq` on the unreduced pair. -/
@[expose] def bodyQ1L (eager : Bool) (fe : InLean.FEnv) (lv : Nat) (d : Nat)
    (a b : Expr) : Option Bool → InLean.CheckCM Bool
  | some v => pure v
  | none => bodyPIL eager fe lv d a b

/-- `defeqBodyI` with its continuations named. -/
theorem defeqBodyL_eq (lv : Nat) (d : Nat) (a b : Expr) :
    InLean.defeqBodyI .verified fe eager lv d a b =
      (if a == b then pure true else do
        if ← (if InLean.Expr.isBoolTrue b && (eager || !a.hasFVar) then
            InLean.boolTrueShortcutI .verified fe eager lv d a else pure false) then pure true else
        InLean.quickDefEqI .verified fe eager lv d a b >>= bodyQ1L eager fe lv d a b :
          InLean.CheckCM Bool) := by
  rw [InLean.defeqBodyI.eq_def]; rfl

section Body

variable {fe : InLean.FEnv} (ih : KnotSpecI .verified .verified eager env fe lv) (hfe : DefeqEnvI fe env)
  (henv : ConLeche.EnvWF env) (hlist : DefEqListSpecI .verified .verified eager env fe lv)
  (hunf : UnfoldDefSpecI .verified eager env fe) (hspine : DefeqSpineSpecI .verified .verified eager env fe lv)
  (hnat : ReduceNatSpecI .verified .verified eager env fe lv) (hproj : ReduceProjSpecI eager env fe lv)
include ih hfe henv hlist hunf hspine hnat hproj

omit hnat in
theorem bodyTailL_spec {d : Nat} {a b : Expr} {s₀ : InLean.CState}
    (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ bodyTailL fe eager lv d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (bodyTailP (ConLeche.fueledFns .verified eager env) env d .verified (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, bodyTailP] =>
    vcgen [bodyTailL, defeqProjPairI_spec ih hfe henv hunf hspine hproj,
      defeqStuckI_spec ih hfe henv hlist, ih.whnfCore, ih.defeq] <;> finish

omit hnat in
theorem bodyLazyL_spec {d : Nat} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (lr : InLean.LazyRes) (hok : OkLR s₀ lr = true) (hlr : LazyPairWS d (TrLR s₀ lr))
    (hc : LazyClosed (TrLR s₀ lr) = true) :
    ⦃fun s => s = s₀⦄ bodyLazyL fe eager lv d lr
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (bodyLazyP (ConLeche.fueledFns .verified eager env) env d .verified (TrLR s₀ lr)) v;
        ⊤⦄ := by
  sym only [conleche_grind, bodyLazyP] =>
    vcgen [bodyLazyL, bodyTailL_spec ih hfe henv hlist hunf hspine hproj] <;> finish

theorem bodyQ2L_spec {d : Nat} {a b : Expr} {s₀ : InLean.CState}
    (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (o : Option Bool) :
    ⦃fun s => s = s₀⦄ bodyQ2L eager fe lv d a b o
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (bodyQ2P (ConLeche.fueledFns .verified eager env) env d .verified eager (TrS s₀ a)
        (TrS s₀ b) o) v; ⊤⦄ := by
  sym only [conleche_grind, bodyQ2P, defeqLoopFuel_eq] =>
    vcgen [bodyQ2L, LazySpecI.triple (lazySpecI_all ih hfe henv hunf hspine hnat _),
      bodyLazyL_spec ih hfe henv hlist hunf hspine hproj] <;> finish

theorem bodyPIL_spec {d : Nat} {a b : Expr} {s₀ : InLean.CState}
    (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ bodyPIL eager fe lv d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (bodyPIP (ConLeche.fueledFns .verified eager env) env d .verified eager (TrS s₀ a)
        (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind, bodyPIP] =>
    vcgen [bodyPIL, propIrrelI_spec ih hfe, ih.whnfCore, quickDefEqI_spec ih,
      bodyQ2L_spec ih hfe henv hlist hunf hspine hnat hproj] <;> finish

theorem bodyQ1L_spec {d : Nat} {a b : Expr} {s₀ : InLean.CState}
    (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) (o : Option Bool) :
    ⦃fun s => s = s₀⦄ bodyQ1L eager fe lv d a b o
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (bodyQ1P (ConLeche.fueledFns .verified eager env) env d .verified eager (TrS s₀ a)
        (TrS s₀ b) o) v; ⊤⦄ := by
  sym only [conleche_grind, bodyQ1P] =>
    vcgen [bodyQ1L, bodyPIL_spec ih hfe henv hlist hunf hspine hnat hproj] <;> finish

/-- **The definitional-equality body simulates its specification**
(`defeqBodyC_spec`'s twin), in `BodySpecBI`'s form. -/
theorem defeqBodyI_spec :
    BodySpecBI .verified eager env (InLean.defeqBodyI .verified fe eager lv)
      (ConLeche.defeqBody .verified eager (ConLeche.fueledFns .verified eager env) env) := by
  intro s₀ d a b hs hoka hokb hwa hwb hca hcb
  sym only [conleche_grind, defeqBody_eq] =>
    vcgen [defeqBodyL_eq, boolTrueShortcutI_spec ih, quickDefEqI_spec ih,
      bodyQ1L_spec ih hfe henv hlist hunf hspine hnat hproj] <;> finish

end Body

end Walks5

end InLeanProof
