module

public import InLeanProof.StateOpsI
public import ConLeche.Verify.Cached.DiscC5

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

end Walks

end InLeanProof
