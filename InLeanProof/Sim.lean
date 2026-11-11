module

public import InLeanProof.Ops
public import ConLeche.Verify.Cached.Grind
/- `Expr.data`'s equations (the computed field), for the hash's lawfulness. -/
import all Lean.Expr

/-!
# The lockstep simulation's foundation (task #451, lane P0)

InLean's checker is a line-by-line twin of con-leche's cached checker
(`ConLeche/Cached/CoreC.lean` & co.).  The proof that it is sound reuses
con-leche's pure fueled checker (`ConLeche/Verify/Fueled.lean`) as the
specification, exactly as `Verify/Cached` does for the cached checker:

* **`CSOKI`, the state invariant**: every entry of every InLean memo,
  translated by `TransS`, satisfies the clause con-leche's `CSOK` states of
  the corresponding cached memo (a run of the pure function on the
  translated key answers the translated value).  It is *not* memo-map
  equality with a cached state: InLean's keys compare by `Expr.keyEq`
  (binder data erased, `mdata` kept), so InLean may miss where the cached
  checker hits; a miss runs the body, which is right by the body's own
  simulation.
* **One generic memo lemma** (`memoEI_ok`, `memoBI_ok`): a hit is right by
  the invariant (the clause respects `keyEq`, since `toCL` erases what
  `keyEq` does), a miss runs the body and the insert keeps the invariant.
* **The bodies** simulate the pure bodies; each is proved by its cached
  twin's script (`Verify/Cached/DiscC*.lean`), with the translation's
  commutation lemmas in the `grind` set.  The pilot is `ensureSortI_ok`.

`mdata` is a stuttering step: `toCL` erases it, and InLean reads through it
(`EO.stripTop`, the transparent spines) without rebuilding a term.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## The translation and what it does not see -/

/-- `toExpr` reads through `erase`: binder names, infos, `nonDep` and `mdata`
are what it drops. -/
theorem toExpr_erase (fv : FVarId → Option ConLeche.Expr) :
    ∀ e : Expr, toExpr fv (erase e) = toExpr fv e := by
  intro e
  induction e <;> simp_all [erase, toExpr]

/-- `toExpr` reads through `eraseK`. -/
theorem toExpr_eraseK (fv : FVarId → Option ConLeche.Expr) :
    ∀ e : Expr, toExpr fv (eraseK e) = toExpr fv e := by
  intro e
  induction e <;> simp_all [eraseK, toExpr]

/-- `toExpr` reads through a node's top-level `mdata`. -/
theorem toExpr_stripTop (fv : FVarId → Option ConLeche.Expr) :
    ∀ e : Expr, toExpr fv (EO.stripTop e) = toExpr fv e := by
  intro e
  induction e <;> simp_all [EO.stripTop, toExpr]

/-! ## The checker's equality on terms in range

`Expr.clEq` tests each pair of nodes on the part of the data word `mdata`
keeps (`clDataNe`).  On terms in range that part is the five structural
fields (`Expr.fieldsOk`), which `erase` does not change, so the test never
rejects an `erase`-equal pair there. -/

theorem rangeS_erase : ∀ e : Expr, rangeS (erase e) = rangeS e := by
  intro e; induction e <;> simp_all [erase, rangeS]

theorem fvarS_erase : ∀ e : Expr, fvarS (erase e) = fvarS e := by
  intro e; induction e <;> simp_all [erase, fvarS]

theorem emvarS_erase : ∀ e : Expr, emvarS (erase e) = emvarS e := by
  intro e; induction e <;> simp_all [erase, emvarS]

theorem elmvarS_erase : ∀ e : Expr, elmvarS (erase e) = elmvarS e := by
  intro e; induction e <;> simp_all [erase, elmvarS]

theorem elparamS_erase : ∀ e : Expr, elparamS (erase e) = elparamS e := by
  intro e; induction e <;> simp_all [erase, elparamS]

/-- Bits 40 to 63 of a word are its range and four flags. -/
theorem shiftRight40_eq {x y : UInt64} (h1 : x.toNat / 2 ^ 44 = y.toNat / 2 ^ 44)
    (h2 : decide (x.toNat / 2 ^ 40 % 2 = 1) = decide (y.toNat / 2 ^ 40 % 2 = 1))
    (h3 : decide (x.toNat / 2 ^ 41 % 2 = 1) = decide (y.toNat / 2 ^ 41 % 2 = 1))
    (h4 : decide (x.toNat / 2 ^ 42 % 2 = 1) = decide (y.toNat / 2 ^ 42 % 2 = 1))
    (h5 : decide (x.toNat / 2 ^ 43 % 2 = 1) = decide (y.toNat / 2 ^ 43 % 2 = 1)) :
    x >>> 40 = y >>> 40 := by
  apply UInt64.toNat_inj.1
  show (UInt64.shiftRight x 40).toNat = (UInt64.shiftRight y 40).toNat
  rw [shiftRight_toNat x 40 (by decide), shiftRight_toNat y 40 (by decide)]
  simp only [decide_eq_decide] at h2 h3 h4 h5
  generalize x.toNat = a at *
  generalize y.toNat = b at *
  simp only [UInt64.reduceToNat]
  omega

/-- The `mdata`-invariant part of a data word is its range and four flags. -/
theorem clDataNe_of_fields {a b : Expr}
    (h1 : a.data.looseBVarRange.toNat = b.data.looseBVarRange.toNat)
    (h2 : a.data.hasFVar = b.data.hasFVar) (h3 : a.data.hasExprMVar = b.data.hasExprMVar)
    (h4 : a.data.hasLevelMVar = b.data.hasLevelMVar)
    (h5 : a.data.hasLevelParam = b.data.hasLevelParam) : clDataNe a b = false := by
  rw [Data.range_read, Data.range_read] at h1
  rw [Data.fvar_read, Data.fvar_read] at h2
  rw [Data.emvar_read, Data.emvar_read] at h3
  rw [Data.lmvar_read, Data.lmvar_read] at h4
  rw [Data.lparam_read, Data.lparam_read] at h5
  have e : dataInv a = dataInv b := shiftRight40_eq h1 h2 h3 h4 h5
  simp [clDataNe, e]

/-- On terms in range, `erase`-equal terms pass the data test. -/
theorem clDataNe_of_erase {a b : Expr} (ha : Expr.RangeOk a) (hb : Expr.RangeOk b)
    (h : erase a = erase b) : clDataNe a b = false := by
  have A := Expr.fieldsOk a ha
  have B := Expr.fieldsOk b hb
  apply clDataNe_of_fields
  · rw [A.range, B.range, ← rangeS_erase a, h, rangeS_erase]
  · rw [A.fvar, B.fvar, ← fvarS_erase a, h, fvarS_erase]
  · rw [A.emvar, B.emvar, ← emvarS_erase a, h, emvarS_erase]
  · rw [A.lmvar, B.lmvar, ← elmvarS_erase a, h, elmvarS_erase]
  · rw [A.lparam, B.lparam, ← elparamS_erase a, h, elparamS_erase]

/-- On terms in range, the plain descent answers `true` on `erase`-equal
terms. -/
theorem clB_complete : ∀ a b, Expr.RangeOk a → Expr.RangeOk b → erase a = erase b →
    clB a b = true := by
  intro a b
  fun_induction clB a b <;> intro ha hb he
  case case1 ih => exact ih ha hb he
  case case2 ih => exact ih ha hb he
  case case8 hc =>
    exact absurd (by rw [← ctorTag_erase_of_ne _ hc.2.1, ← ctorTag_erase_of_ne _ hc.2.2, he]) hc.1
  case case9 => simp [he]
  all_goals
    simp only [Expr.RangeOk, erase, Expr.app.injEq, Expr.lam.injEq, Expr.forallE.injEq,
      Expr.letE.injEq, Expr.proj.injEq, true_and] at ha hb he
    simp_all [clDataNe_of_erase]

/-- **The checker's equality on terms in range is equality after `erase`.** -/
theorem clEq_iff_erase {a b : Expr} (ha : Expr.RangeOk a) (hb : Expr.RangeOk b) :
    Expr.clEq a b = true ↔ erase a = erase b := by
  refine ⟨Expr.clEq_sound, fun h => ?_⟩
  rw [Expr.clEq_eq, clStep, clDataNe_of_erase ha hb h, clB_complete a b ha hb h]; rfl

/-- **O2, one direction**: terms InLean's checker compares equal translate
equal. -/
theorem toExpr_of_clEq (fv : FVarId → Option ConLeche.Expr) {a b : Expr}
    (h : Expr.clEq a b = true) : toExpr fv a = toExpr fv b := by
  rw [← toExpr_erase fv a, Expr.clEq_sound h, toExpr_erase]

/-- Memo keys that compare equal translate equal (`keyEq` erases less than
`toCL`). -/
theorem toExpr_of_keyEq (fv : FVarId → Option ConLeche.Expr) {a b : Expr}
    (h : Expr.keyEq a b = true) : toExpr fv a = toExpr fv b := by
  simp only [Expr.keyEq, decide_eq_true_eq] at h
  rw [← toExpr_eraseK fv a, h, toExpr_eraseK]

/-! ## The memo keys are lawful

Lean's cached hash reads no binder name or binder info (the computed field
`Expr.data`, `InLean.data_eraseK`), so `eraseK`-equal terms hash alike. -/

instance : LawfulHashable EKey where
  hash_eq a b h := by
    show hash a.e = hash b.e
    simp only [BEq.beq, Expr.keyEq, decide_eq_true_eq] at h
    show a.e.data.hash = b.e.data.hash
    rw [← data_eraseK a.e, h, data_eraseK]

/-! ## The translation at a state -/

/-- The state's free-variable table, as the proof reads it. -/
@[expose] def tableOf (s : InLean.CState) : FVarTable := ⟨s.fvTys, s.fvCls⟩

/-- **The translation of InLean's terms at state `s`**: free variables
through the state's interned table (`FVarTable.trans`). -/
@[expose] def TransS (s : InLean.CState) : Expr → Option ConLeche.Expr :=
  toExpr (FVarTable.trans (tableOf s))

/-- **The free-variable table's invariant** (O3), what `mkFVarM` keeps: a
class holds numbers whose types hash to it, distinct numbers of one class
have types unequal after `erase` (the interning is by `Expr.clEq`-class),
every interned type translates at its number (mentioning earlier numbers
only) and is in range, and the `keyEq` fast path points at a live number of an `erase`-equal
type.  From it, a translatable free variable's id is determined by its
translation (`FVarTable.trans_inj`, `InLeanProof/FVar.lean`), as con-leche's
`.fvar d ty` is by its depth and type. -/
structure FVTableOK (s : InLean.CState) : Prop where
  cls : ∀ d h n, n ∈ s.fvCls.getD (d, h) [] → ∃ ty, s.fvTys[n]? = some ty ∧ EO.clHash ty = h
  distinct : ∀ d h n m tn tm, n ∈ s.fvCls.getD (d, h) [] → m ∈ s.fvCls.getD (d, h) [] →
    s.fvTys[n]? = some tn → s.fvTys[m]? = some tm → erase tn = erase tm → n = m
  ty : ∀ n ty, s.fvTys[n]? = some ty → ∃ cty, toExpr ((tableOf s).inner n) ty = some cty
  seen : ∀ d k n, s.fvSeen[(d, EKey.mk k)]? = some n →
    (tableOf s).live d n = true ∧ ∃ tn, s.fvTys[n]? = some tn ∧ erase k = erase tn
  /-- every interned type is in range (what `mkFVarM`'s callers intern; the
  leaf guard's `EO.fvarIds` reads the cached `hasFVar` of the types) -/
  range : ∀ (n : Nat) (ty : Expr), s.fvTys[n]? = some ty → Expr.RangeOk ty

/-! ## The invariant -/

/-- A unary memo's clause: the key and the value translate, the value is in
range (so it has a reading, `OkS`, as every post states) and closed (every
knot answer is: lane P2-infer, the knot's `inferIO` slot has no pure closedness
theorem to read it off), and a run of
the pure function `spec` on the translated key answers the translated
value, at every depth the key is scoped at (`CSOK`'s clause shape). -/
@[expose] def UnaryOK (s : InLean.CState) (spec : Nat → Nat → ConLeche.Expr → ConLeche.CheckM ConLeche.Expr)
    (k v : Expr) : Prop :=
  ∃ ck cv, TransS s k = some ck ∧ TransS s v = some cv ∧ Expr.RangeOk v ∧
    cv.looseBVarsBounded 0 = true ∧
    ∃ F, ∀ d, ck.wscopedB d = true → spec F d ck = .ok cv

/-- The defeq memo's clause. -/
@[expose] def BinaryOK (s : InLean.CState)
    (spec : Nat → Nat → ConLeche.Expr → ConLeche.Expr → ConLeche.CheckM Bool)
    (a b : Expr) (r : Bool) : Prop :=
  ∃ ca cb, TransS s a = some ca ∧ TransS s b = some cb ∧
    ∃ F, ∀ d, ca.wscopedB d = true → cb.wscopedB d = true → spec F d ca cb = .ok r

/-- The eager tower's memos (`ModeMemosOK`'s twin): backed by runs at
`eager := true`, the flag the `defeqE` slot runs them at.  `s` is the state
whose table the entries are read with. -/
structure ModeMemosOKI (mode : ConLeche.CheckMode) (env : ConLeche.Env) (s : InLean.CState)
    (mm : InLean.ModeMemos) : Prop where
  whnfCoreC : ∀ k v, mm.whnfCoreC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.whnfCore mode true env F d e) k v
  whnfCoreCheapC : ∀ k v, mm.whnfCoreCheapC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.whnfCore mode true env F d e true) k v
  whnfC : ∀ k v, mm.whnfC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.whnf mode true env F d e) k v
  inferC : ∀ k v, mm.inferC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.inferTypeCore mode true env F d e) k v
  inferIOC : ∀ k v, mm.inferIOC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.inferTypeIO mode true env F d e) k v
  defeqC : ∀ a b r, mm.defeqC[(EKey.mk a, EKey.mk b)]? = some r →
    BinaryOK s (fun F d x y => ConLeche.isDefEqCore mode true env F d x y) a b r

/-- **`CSOKI`, InLean's state invariant at the pure checker of `env`**:
the free-variable table's invariant, and every entry of every memo
satisfies `CSOK`'s clause for its map, translated: the five unary
entry-point memos and the defeq memo (`UnaryOK`, `BinaryOK`), the
stored-constant caches (`constTy`, `constVal`, `ruleRhs`: the stored term
at the translated levels), the level memos (`lsimp`, `eqv`), the
bulk-instantiation memo (`instC`: con-leche's `instantiateList` at closed,
translated values) and the eager tower's memos (`eager`, at `eager := true`).
A clause is about a *lookup*, so it holds of every `keyEq`-equal key.

Every clause states the translations it reads as *facts* (`TransS s k =
some ck ∧ …`), never as premises: the table only grows (`mkFVarM`), and a
fact stays true at a later state (`toExpr_mono`), so the invariant is kept
by interning (`CSOKI.of_tabLe`, `InLeanProof/StateOpsI.lean`).  A stored
value is in range (`Expr.RangeOk`), so a hit has a reading (`OkS`). -/
structure CSOKI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (s : InLean.CState) : Prop where
  fv : FVTableOK s
  /-- every interned type reads as a closed term (lane P2-infer: an `fvar`'s
  inferred type is its interned one, and the knot's answers are closed) -/
  fvClosed : ∀ (n : Nat) (ty : Expr) (cty : ConLeche.Expr), s.fvTys[n]? = some ty →
    TransS s ty = some cty →
    cty.looseBVarsBounded 0 = true
  whnfCoreC : ∀ k v, s.whnfCoreC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.whnfCore mode eager env F d e) k v
  whnfCoreCheapC : ∀ k v, s.whnfCoreCheapC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.whnfCore mode eager env F d e true) k v
  whnfC : ∀ k v, s.whnfC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.whnf mode eager env F d e) k v
  inferC : ∀ k v, s.inferC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.inferTypeCore mode eager env F d e) k v
  inferIOC : ∀ k v, s.inferIOC[EKey.mk k]? = some v →
    UnaryOK s (fun F d e => ConLeche.inferTypeIO mode eager env F d e) k v
  defeqC : ∀ a b r, s.defeqC[(EKey.mk a, EKey.mk b)]? = some r →
    BinaryOK s (fun F d x y => ConLeche.isDefEqCore mode eager env F d x y) a b r
  constTy : ∀ n us i, s.constTyAt[(n, us)]? = some i → ∃ cus ci ct,
    toLevels us = some cus ∧ env.find? (toName n) = some ci ∧ TransS s i = some ct ∧
    Expr.RangeOk i ∧
    ct = ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams cus
  constVal : ∀ n us i, s.constValAt[(n, us)]? = some i → ∃ cus cv v h cval,
    toLevels us = some cus ∧ env.find? (toName n) = some (.defnInfo cv v h) ∧
    TransS s i = some cval ∧ Expr.RangeOk i ∧ cval = v.instantiateLevelParams cv.levelParams cus
  ruleRhs : ∀ c j us i, s.ruleRhsAt[(c, j, us)]? = some i → ∃ cus cv mI rP isK rules rl cr,
    toLevels us = some cus ∧ env.find? (toName c) = some (.recInfo cv mI rP isK rules) ∧
    rules.find? (fun r' => r'.ctor == toName j) = some rl ∧
    TransS s i = some cr ∧ Expr.RangeOk i ∧ cr = rl.rhs.instantiateLevelParams cv.levelParams cus
  lsimp : ∀ u v, s.lsimpC[u]? = some v → ∀ cu, toLevel u = some cu →
    toLevel v = some (ConLeche.Level.simplify cu)
  eqv : ∀ l r b, s.eqvC[(l, r)]? = some b → ∀ cl cr, toLevel l = some cl → toLevel r = some cr →
    ConLeche.Level.isEquiv cl cr = some b
  instC : ∀ k vs r, s.instC[InstKey.mk k vs]? = some r → ∃ ck cvs cr,
    TransS s k = some ck ∧ vs.mapM (TransS s) = some cvs ∧ TransS s r = some cr ∧
    Expr.RangeOk r ∧ (∀ cv ∈ cvs, cv.looseBVarsBounded 0 = true) ∧
    cr = ck.instantiateList cvs 0
  eager : ModeMemosOKI mode env s s.eagerMemos

/-! ## The generic memo lemma -/

/-- A successful InLean run from `s₀` keeps `Inv` and its value satisfies
`Q` at the final state (the functional form `SimC` has). -/
@[expose] def RunOK {β : Type} (Inv : InLean.CState → Prop) (Q : InLean.CState → β → Prop)
    (c : CheckCM β) (s₀ : InLean.CState) : Prop :=
  ∀ v s', c s₀ = .ok (v, s') → Inv s' ∧ Q s' v

/-- **The memo lemma** (one for every unary memo): a hit answers by the
map's clause, a miss runs the body, and the insert keeps the invariant. -/
theorem memoEI_ok {Inv : InLean.CState → Prop} {R : InLean.CState → Expr → Expr → Prop}
    {get' : InLean.CState → Std.HashMap EKey Expr}
    {set' : InLean.CState → Std.HashMap EKey Expr → InLean.CState}
    {f : Nat → Expr → CheckCM Expr} {d : Nat} {e : Expr} {s₀ : InLean.CState}
    (hit : ∀ s v, Inv s → (get' s)[EKey.mk e]? = some v → R s e v)
    (ins : ∀ s v, Inv s → R s e v →
      Inv (set' (set' s ∅) ((get' s).insert (EKey.mk e) v)) ∧
        R (set' (set' s ∅) ((get' s).insert (EKey.mk e) v)) e v)
    (body : ∀ s, Inv s → RunOK Inv (fun s' v => R s' e v) (f d e) s)
    (h₀ : Inv s₀) : RunOK Inv (fun s' v => R s' e v) (memoEI get' set' f d e) s₀ := by
  intro v s' hrun
  cases hlook : (get' s₀)[EKey.mk e]? with
  | some r =>
    simp [memoEI, hlook, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.bind, Except.pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨h₀, hit _ _ h₀ hlook⟩
  | none =>
    cases hb : f d e s₀ with
    | error x =>
      simp [memoEI, hlook, hb, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Except.bind, Except.pure, pure] at hrun
    | ok p =>
      simp [memoEI, hlook, hb, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind,
        Except.pure] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨hI, hR⟩ := body s₀ h₀ p.1 p.2 hb
      exact ins p.2 p.1 hI hR

/-- The defeq memo's lemma. -/
theorem memoBI_ok {Inv : InLean.CState → Prop} {R : InLean.CState → Expr → Expr → Bool → Prop}
    {f : Nat → Expr → Expr → CheckCM Bool} {d : Nat} {a b : Expr} {s₀ : InLean.CState}
    (hit : ∀ s r, Inv s → s.defeqC[(EKey.mk a, EKey.mk b)]? = some r → R s a b r)
    (ins : ∀ (s : InLean.CState) r, Inv s → R s a b r →
      Inv { s with defeqC := s.defeqC.insert (EKey.mk a, EKey.mk b) r } ∧
        R { s with defeqC := s.defeqC.insert (EKey.mk a, EKey.mk b) r } a b r)
    (body : ∀ s, Inv s → RunOK Inv (fun s' r => R s' a b r) (f d a b) s)
    (h₀ : Inv s₀) : RunOK Inv (fun s' r => R s' a b r) (memoBI f d a b) s₀ := by
  intro r s' hrun
  cases hlook : s₀.defeqC[(EKey.mk a, EKey.mk b)]? with
  | some r' =>
    simp [memoBI, hlook, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.bind, Except.pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨h₀, hit _ _ h₀ hlook⟩
  | none =>
    cases hb : f d a b s₀ with
    | error x =>
      simp [memoBI, hlook, hb, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Except.bind, Except.pure, pure] at hrun
    | ok p =>
      simp [memoBI, hlook, hb, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind,
        Except.pure] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨hI, hR⟩ := body s₀ h₀ p.1 p.2 hb
      exact ins p.2 p.1 hI hR

/-! ## The pilot: `ensureSortI`

The template every body lemma follows: the knot's entry points are
hypotheses in `RunOK` form against the pure entry points, the body's own
reads of a node go through `EO.stripTop` (which the translation does not
see), and the conclusion is the pure body's answer at the translation. -/

/-- InLean's `whnf` slot answers the pure `whnf` at the translation (the
knot hypothesis the bodies take, at level `lv`). -/
@[expose] def WhnfOK (mode : ConLeche.CheckMode) (mi : InLean.CheckMode) (eager : Bool)
    (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat) : Prop :=
  ∀ (s : InLean.CState) (d : Nat) (i : Expr) (ci : ConLeche.Expr), CSOKI mode eager env s →
    TransS s i = some ci →
    RunOK (CSOKI mode eager env)
      (fun s' w => ∃ cw, TransS s' w = some cw ∧
        ConLeche.Cached.Runs ((ConLeche.fueledFns mode eager env).whnf d ci) cw)
      (InLean.whnfI mi fe eager lv d i) s

/-- The translation of a sort is a sort, at the translated level. -/
theorem TransS_sort {s : InLean.CState} {w : Expr} {cw : ConLeche.Expr}
    (h : TransS s w = some cw) :
    ∀ u, EO.stripTop w = .sort u → ∃ cu, toLevel u = some cu ∧ cw = .sort cu := by
  intro u hu
  have := toExpr_stripTop (FVarTable.trans (tableOf s)) w
  unfold TransS at h
  rw [← this, hu] at h
  simp only [toExpr] at h
  cases hl : toLevel u with
  | none => simp [hl] at h
  | some cu => simp [hl] at h; exact ⟨cu, rfl, h.symm⟩

/-- **Pilot: `ensureSortI` runs in lockstep with the pure `ensureSort`**:
from a related input, its level translates to the pure one's. -/
theorem ensureSortI_ok {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {mi : InLean.CheckMode} {fe : InLean.FEnv} {lv : Nat} (hr : WhnfOK mode mi eager env fe lv) {s₀ : InLean.CState} {d : Nat} {i : Expr}
    {ci : ConLeche.Expr} (hs : CSOKI mode eager env s₀) (hi : TransS s₀ i = some ci) :
    RunOK (CSOKI mode eager env)
      (fun _ u => ∃ cu, toLevel u = some cu ∧
        ConLeche.Cached.Runs (ConLeche.ensureSort (ConLeche.fueledFns mode eager env) env d ci) cu)
      (ensureSortI mi fe eager lv d i) s₀ := by
  intro u s' hrun
  cases hw : InLean.whnfI mi fe eager lv d i s₀ with
  | error x => simp [ensureSortI.eq_def, hw, bind, StateT.bind, Except.bind] at hrun
  | ok p =>
    obtain ⟨w, s₁⟩ := p
    obtain ⟨hs₁, cw, hcw, hrw⟩ := hr s₀ d i ci hs hi w s₁ hw
    cases hsw : EO.stripTop w
    case sort u' =>
      simp [ensureSortI.eq_def, hw, hsw, bind, StateT.bind, Except.bind, pure, StateT.pure,
        Except.pure] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨cu, hcu, rfl⟩ := TransS_sort hcw u' hsw
      refine ⟨hs₁, cu, hcu, ?_⟩
      unfold ConLeche.ensureSort
      exact ConLeche.Cached.Runs.bind hrw (ConLeche.Cached.Runs.pure _)
    all_goals
      simp [ensureSortI.eq_def, hw, hsw, bind, StateT.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift] at hrun

end InLeanProof
