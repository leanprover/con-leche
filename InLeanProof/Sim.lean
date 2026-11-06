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

/-- **O2, one direction**: terms InLean's checker compares equal translate
equal. -/
theorem toExpr_of_clEq (fv : FVarId → Option ConLeche.Expr) {a b : Expr}
    (h : Expr.clEq a b = true) : toExpr fv a = toExpr fv b := by
  rw [Expr.clEq_iff] at h
  rw [← toExpr_erase fv a, h, toExpr_erase]

/-- Memo keys that compare equal translate equal (`keyEq` erases less than
`toCL`). -/
theorem toExpr_of_keyEq (fv : FVarId → Option ConLeche.Expr) {a b : Expr}
    (h : Expr.keyEq a b = true) : toExpr fv a = toExpr fv b := by
  simp only [Expr.keyEq, decide_eq_true_eq] at h
  rw [← toExpr_eraseK fv a, h, toExpr_eraseK]

/-! ## The memo keys are lawful

Lean's cached hash reads no binder name, binder info or `nonDep` (the
computed field `Expr.data`), so `eraseK`-equal terms hash alike. -/

theorem data_eraseK : ∀ e : Expr, (eraseK e).data = e.data := by
  intro e
  induction e <;> simp_all [eraseK, Expr.data]

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
only), and the `keyEq` fast path points at a live number of an `erase`-equal
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

/-! ## The invariant -/

/-- A unary memo's clause: the key and the value translate, the value is in
range (so it has a reading, `OkS`, as every post states), and a run of
the pure function `spec` on the translated key answers the translated
value, at every depth the key is scoped at (`CSOK`'s clause shape). -/
@[expose] def UnaryOK (s : InLean.CState) (spec : Nat → Nat → ConLeche.Expr → ConLeche.CheckM ConLeche.Expr)
    (k v : Expr) : Prop :=
  ∃ ck cv, TransS s k = some ck ∧ TransS s v = some cv ∧ Expr.RangeOk v ∧
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
knot hypothesis the bodies take, at fuel `f`). -/
@[expose] def WhnfOK (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (r : CoreFnsI) : Prop :=
  ∀ (s : InLean.CState) (d : Nat) (i : Expr) (ci : ConLeche.Expr), CSOKI mode eager env s →
    TransS s i = some ci →
    RunOK (CSOKI mode eager env)
      (fun s' w => ∃ cw, TransS s' w = some cw ∧
        ConLeche.Cached.Runs ((ConLeche.fueledFns mode eager env).whnf d ci) cw)
      (r.whnf d i) s

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
    {r : CoreFnsI} (hr : WhnfOK mode eager env r) {s₀ : InLean.CState} {d : Nat} {i : Expr}
    {ci : ConLeche.Expr} (hs : CSOKI mode eager env s₀) (hi : TransS s₀ i = some ci) :
    RunOK (CSOKI mode eager env)
      (fun _ u => ∃ cu, toLevel u = some cu ∧
        ConLeche.Cached.Runs (ConLeche.ensureSort (ConLeche.fueledFns mode eager env) env d ci) cu)
      (ensureSortI r d i) s₀ := by
  intro u s' hrun
  cases hw : r.whnf d i s₀ with
  | error x => simp [ensureSortI, hw, bind, StateT.bind, Except.bind] at hrun
  | ok p =>
    obtain ⟨w, s₁⟩ := p
    obtain ⟨hs₁, cw, hcw, hrw⟩ := hr s₀ d i ci hs hi w s₁ hw
    cases hsw : EO.stripTop w
    case sort u' =>
      simp [ensureSortI, hw, hsw, bind, StateT.bind, Except.bind, pure, StateT.pure,
        Except.pure] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨cu, hcu, rfl⟩ := TransS_sort hcw u' hsw
      refine ⟨hs₁, cu, hcu, ?_⟩
      unfold ConLeche.ensureSort
      exact ConLeche.Cached.Runs.bind hrw (ConLeche.Cached.Runs.pure _)
    all_goals
      simp [ensureSortI, hw, hsw, bind, StateT.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift] at hrun

end InLeanProof
