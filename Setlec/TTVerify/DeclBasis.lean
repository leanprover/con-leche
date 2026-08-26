import Setlec.TTVerify.DivModPin

/-!
# The pinned basis blocks

`DeclBasisTT`, the fifth of `checkDecl`'s six cases.

`installBasisDecl` is three lines — a duplicate check and a cons — and
the `.basisDecl` case folds it over `kind.declsA`.  So the whole case
is a **driver** (invert the fold into a chain of fresh conses) plus one
`EnvTT.cons` per pinned constant.

## The driver is written once here

The set model has no per-block install lemma for five of its six
blocks: their drivers are open-coded inline in
`Setlec/Model/Consistency.lean`, ~130 lines of the same inversion
boilerplate repeated six times with the growing `Env` prefix spelled
out.  `BasisChain` plus `foldlM_installBasisDecl_inv` replaces all six
copies with a relation and one induction, and neither mentions a
valuation — so if the model side ever de-duplicates, this is shareable
under #123's criterion rather than something to re-derive
(`DESIGN.md` §14.4).
-/

-- The basis blocks' type computations run one fixed simp set per
-- constant; which of its members fire depends on the constant's shape,
-- so some are unused in some of them.  Same practice as the set model's
-- own basis installs.
set_option linter.unusedSimpArgs false

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The fold, inverted once -/

/-- A successful basis fold: each constant in turn was fresh, and got
consed. -/
inductive BasisChain : Env → List ConstantInfo → Env → Prop
  | nil {env : Env} : BasisChain env [] env
  | cons {env env₂ : Env} {ci : ConstantInfo} {l : List ConstantInfo} :
      env.find? ci.name = none →
      BasisChain ⟨ci :: env.consts⟩ l env₂ →
      BasisChain env (ci :: l) env₂

/-- One pinned install, inverted. -/
theorem installBasisDecl_inv {env env₁ : Env} {ci : ConstantInfo}
    (h : installBasisDecl (m := CheckM) env ci = .ok env₁) :
    env.find? ci.name = none ∧ env₁ = ⟨ci :: env.consts⟩ := by
  unfold installBasisDecl at h
  revert h
  cases hf : env.find? ci.name with
  | none =>
    intro h
    simp only [Option.isNone_none, if_true, pure, Except.pure,
      Except.ok.injEq] at h
    exact ⟨rfl, h.symm⟩
  | some ci' =>
    intro h
    simp only [Option.isNone_some, Bool.false_eq_true, if_false,
      throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    exact nomatch h

/-- **The fold, inverted.**  The one lemma the model's six copies
replace. -/
theorem foldlM_installBasisDecl_inv :
    ∀ (l : List ConstantInfo) {env env₁ : Env},
      l.foldlM (installBasisDecl (m := CheckM)) env = .ok env₁ →
      BasisChain env l env₁
  | [], env, env₁, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | ci :: l, env, env₁, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hi : installBasisDecl (m := CheckM) env ci with
    | error e => intro h; exact nomatch h
    | ok env' =>
      intro h
      obtain ⟨hfresh, rfl⟩ := installBasisDecl_inv hi
      exact .cons hfresh (foldlM_installBasisDecl_inv l h)


/-! ## The per-constant install

`EnvTT.cons` at a pinned basis constant.  Six of its head obligations
are discharged **by computation on the reserved-name list**, which is
what that list is for:

* `hheadUnit` and `hheadEta`'s first disjunct ask for a family whose
  name is *not* reserved, and a basis constant's is;
* `hheadEta`'s second disjunct asks for an eta capability whose
  constructor is the constant being installed — and `EtaFamilyStored`'s
  own first conjunct says a reserved-named constructor never completes
  a family (`Setlec/Verify/EnvGuards.lean`, where the conjunct is
  documented as existing for exactly this);
* `hheadEta`'s third asks for a projection-function name, and
  `projFnName` builds a `Name.num` node where every reserved name is a
  `Name.str`.
-/

/-- A projection function is never a reserved basis name: `projFnName`
builds a `Name.num` node, and every reserved name is a `Name.str`. -/
theorem projFnName_ne_reserved {T n : Name} {j : Nat}
    (h : reservedBasisNames.contains n = true) : projFnName T j ≠ n := by
  intro hh
  subst hh
  simp only [reservedBasisNames, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, projFnName] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h <;> exact nomatch h

/-- The valuation with one name reset to a given term — the basis
install's counterpart of `cvalAt`, which reads a *value* where a pinned
constant has none. -/
def cvalSet (cval : TConstVal) (n : Name) (val : (Name → Nat) → VExpr) :
    TConstVal := fun c ψ => if c = n then val ψ else cval c ψ

@[simp] theorem cvalSet_self {cval : TConstVal} {n : Name}
    {val : (Name → Nat) → VExpr} : cvalSet cval n val n = val := by
  funext ψ; simp [cvalSet]

theorem cvalSet_ne {cval : TConstVal} {n c : Name}
    {val : (Name → Nat) → VExpr} (h : c ≠ n) :
    cvalSet cval n val c = cval c := by
  funext ψ; simp [cvalSet, h]

/-- **One pinned basis constant, installed.**  Every obligation that is
not about *this* constant is discharged here. -/
theorem extendBasisTT {env : Env} (m : EnvTT env) {ci : ConstantInfo}
    {val : (Name → Nat) → VExpr}
    (hres : reservedBasisNames.contains ci.name = true)
    (hpin : isBasisKind ci = true → ci = pinnedInfoT ci.name)
    (hdirect : ∀ (ψ : Name → Nat) (t : VExpr),
      pinnedDirectT ci.name ψ = some t → val ψ = t)
    (hfresh : env.find? ci.name = none)
    (hwf : EnvWF ⟨ci :: env.consts⟩)
    (hclosed : ∀ ψ : Name → Nat, VExpr.Closed (val ψ))
    (hparams : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) → val φ₁ = val φ₂)
    (htype : ∀ φ : Name → Nat, ∃ t,
      denoteClosed (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ
        ci.toConstantVal.type = some t ∧ HasType [] (val φ) t)
    (hnodefn : ∀ cv v h, ci ≠ .defnInfo cv v h)
    (hnothm : ∀ cv v, ci ≠ .thmInfo cv v)
    (hnoax : ∀ cv, ci ≠ .axiomInfo cv)
    (hempty : ci.name = emptyName → ∀ ψ : Name → Nat, ∃ u, val ψ = emptyT u)
    (hheadCtors : ∀ cv mI rP rules, ci = .recInfo cv mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hheadRec : ∀ cv mI rP rules, ci = .recInfo cv mI rP rules →
      ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      rP ≤ mI ∧
      ∀ (φ : Name → Nat) (d : Nat) (us : List Level),
        us.length = cv.levelParams.length →
        ∃ R, denote (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ d
            ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
            = some R ∧
          ∀ (cvj : ConstantVal) (cnP cnF : Nat),
            (⟨ci :: env.consts⟩ : Env).find? (RecRule.ctor rl)
              = some (.ctorInfo cvj cnP cnF) →
          ∀ (Δ : List VExpr) (usj : List Level) (xs ys : List VExpr)
            (TV TVj restR restC : VExpr),
            xs.length = mI →
            ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
            usj.length = cvj.levelParams.length →
            Level.substFn φ cvj.levelParams usj
              = Level.substFn φ cvj.levelParams
                  (recFireComparands rl cv.levelParams us cvj.levelParams
                    [] rP).1 →
            denote (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ d
              (cv.type.instantiateLevelParams cv.levelParams us) = some TV →
            denote (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ d
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              = some TVj →
            VTeleTyped Δ TV
              (xs ++ [VExpr.mkAppN (cvalSet m.cval ci.name val
                (RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys]) restR →
            VTeleTyped Δ TVj ys restC →
            Deq Δ
              (VExpr.mkAppN
                (cvalSet m.cval ci.name val ci.name
                  (Level.substFn φ cv.levelParams us))
                (xs ++ [VExpr.mkAppN (cvalSet m.cval ci.name val
                  (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]))
              (VExpr.mkAppN R
                (xs.take rP ++ ys.drop (RecRule.ctorParams rl))))
    (hheadProj : ∀ entry, ci = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA)
    (hheadProjPair : ∀ i entry, ci = .projInfo entry →
      ci.name = projFnName psigmaName i → entry.native = true)
    (hheadEq : ci.name = eqName →
      EqLawTT ⟨ci :: env.consts⟩ (cvalSet m.cval ci.name val)) :
    ∃ m' : EnvTT ⟨ci :: env.consts⟩,
      m'.cval = cvalSet m.cval ci.name val := by
  have hag : ∀ n, n ≠ ci.name → m.cval n = cvalSet m.cval ci.name val n :=
    fun n hn => (cvalSet_ne hn).symm
  refine ⟨EnvTT.cons m (Installs.of_fresh hfresh hag) hwf
    ?_ ?_ ?_ ?_ ?_ ?_ hheadCtors hheadRec ?_ ?_ hheadProj hheadProjPair
    hheadEq ?_ ?_ ?_ ?_, rfl⟩
  · -- closed
    intro ψ; rw [cvalSet_self]; exact hclosed ψ
  · -- reads only its own level parameters
    intro φ₁ φ₂ hp; rw [cvalSet_self]; exact hparams φ₁ φ₂ hp
  · -- typed
    intro φ
    obtain ⟨t, ht, hd⟩ := htype φ
    exact ⟨t, ht, by rw [cvalSet_self]; exact hd⟩
  · exact fun cv v h heq => absurd heq (hnodefn cv v h)
  · exact fun cv v heq => absurd heq (hnothm cv v)
  · -- `Empty`'s pinned shape
    intro hn ψ
    obtain ⟨u, hu⟩ := hempty hn ψ
    exact ⟨u, by rw [← hn, cvalSet_self]; exact hu⟩
  · -- no eta-capable family is completed by a reserved constant
    intro T cvT caps hf hcape hresT hfam hpart
    rcases hpart with hT | hC | ⟨j, hj, hP⟩
    · rw [← hT] at hres; rw [hres] at hresT; exact nomatch hresT
    · have hf1 := hfam.1
      rw [hC, hres] at hf1
      exact nomatch hf1
    · exact absurd hP (projFnName_ne_reserved hres)
  · -- no unit-like family either
    intro cv caps heq hunit hnres
    rw [hres] at hnres; exact nomatch hnres
  · -- the pinned shape and valuation
    intro _
    exact ⟨hpin, fun ψ t hp => by rw [cvalSet_self]; exact hdirect ψ t hp⟩
  · exact fun cv v h heq => absurd heq (hnodefn cv v h)
  · exact fun cv v h heq => absurd heq (hnodefn cv v h)
  · exact fun cv heq => absurd heq (hnoax cv)


/-- **An earlier constant of the block, denoted.**  Every `htype`
computation in a basis block needs the same step: a constant already
installed by this block resolves in the extended environment, its level
list has the declared length, and its valuation is its pin. -/
theorem denote_const_pin {env : Env} (m : EnvTT env) {ci₀ ci : ConstantInfo}
    {n : Name} {us : List Level} {t : VExpr} {φ : Name → Nat}
    {val : (Name → Nat) → VExpr}
    (hne : ci₀.name ≠ n)
    (hf : env.find? n = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    (hres : reservedBasisNames.contains n = true)
    (hpin : pinnedDirectT n (Level.substFn φ ci.toConstantVal.levelParams us)
      = some t) (d : Nat) :
    denote (cvalSet m.cval ci₀.name val) ⟨ci₀ :: env.consts⟩ φ d (.const n us)
      = some t := by
  rw [denote_const, Env.find?_cons, if_neg hne, hf]
  simp only [if_pos hlen]
  rw [cvalSet_ne (Ne.symm hne)]
  exact congrArg some (cval_pinned m hres (by rw [hf]; rfl) _ hpin)

/-! ### `instantiate1`, constructor by constructor

`denote` opens every binder with `instantiate1` at cut `0`, so a basis
type's computation walks it once per node.  Unfolding the definition
leaves a decidable `if` at each `bvar`; these equations let `simp` take
the step without ever producing one. -/

@[simp] theorem Expr.instantiate1_bvar (i : Nat) (v : Expr) (d : Nat) :
    (Expr.bvar i).instantiate1 v d =
      if i = d then v else if i > d then .bvar (i - 1) else .bvar i := rfl
@[simp] theorem Expr.instantiate1_const (n : Name) (us : List Level)
    (v : Expr) (d : Nat) : (Expr.const n us).instantiate1 v d = .const n us :=
  rfl
@[simp] theorem Expr.instantiate1_sort (u : Level) (v : Expr) (d : Nat) :
    (Expr.sort u).instantiate1 v d = .sort u := rfl
@[simp] theorem Expr.instantiate1_fvar (i : Nat) (n : Name) (ty v : Expr)
    (d : Nat) : (Expr.fvar i n ty).instantiate1 v d = .fvar i n ty := rfl
@[simp] theorem Expr.instantiate1_app (f a v : Expr) (d : Nat) :
    (Expr.app f a).instantiate1 v d
      = .app (f.instantiate1 v d) (a.instantiate1 v d) := rfl
@[simp] theorem Expr.instantiate1_forallE (n : Name) (ty body v : Expr)
    (bi : BinderMeta) (d : Nat) :
    (Expr.forallE n ty body bi).instantiate1 v d
      = .forallE n (ty.instantiate1 v d) (body.instantiate1 v (d + 1)) bi := rfl
@[simp] theorem Expr.instantiate1_lam (n : Name) (ty body v : Expr)
    (bi : BinderMeta) (d : Nat) :
    (Expr.lam n ty body bi).instantiate1 v d
      = .lam n (ty.instantiate1 v d) (body.instantiate1 v (d + 1)) bi := rfl

/-! ## `Empty`

The pilot block: two constants, and `Empty.rec`'s rule list is `[]`, so
the iota obligation does not exist.  What it validates is the driver
and the shape of a `htype` computation — nothing else. -/

/-- `Empty`, installed. -/
theorem extendEmptyTT {env : Env} (m : EnvTT env)
    (hfresh : env.find? emptyName = none)
    (hwf : EnvWF ⟨emptyA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨emptyA :: env.consts⟩,
      m'.cval = cvalSet m.cval emptyA.name (fun _ => emptyT 1) := by
  refine extendBasisTT m (val := fun _ => emptyT 1) (by decide) (fun _ => by
      decide) ?_ hfresh hwf (fun _ => trivial) (fun _ _ _ => rfl) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ ψ => ⟨1, rfl⟩)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro ψ t hp
    simp only [pinnedDirectT, emptyA, ConstantInfo.name] at hp ⊢
    exact (Option.some.inj hp).symm ▸ rfl
  · intro φ
    refine ⟨.sort 1, ?_, HasType.const⟩
    rw [denoteClosed, show (emptyA.toConstantVal.type) = .sort (.succ .zero)
      from rfl, denote_sort]
    rfl

/-- `Empty.rec`, installed.  Its rule list is empty, so both recursor
obligations are vacuous and the whole content is the type
computation. -/
theorem extendEmptyRecTT {env : Env} (m : EnvTT env)
    (hE : env.find? emptyName = some emptyA)
    (hfresh : env.find? (emptyName.str "rec") = none)
    (hwf : EnvWF ⟨emptyRecA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨emptyRecA :: env.consts⟩,
      m'.cval = cvalSet m.cval emptyRecA.name
        (fun ψ => VExpr.const .emptyRec [1, ψ uNT]) := by
  have hpd : ∀ φ : Name → Nat,
      pinnedDirectT emptyName φ = some (VExpr.const .empty [1]) := by
    intro φ
    simp only [pinnedDirectT]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_true]
  have hEv : ∀ φ : Name → Nat, m.cval emptyName φ = emptyT 1 := fun φ =>
    cval_pinned m (by decide) (by rw [hE]; rfl) φ (hpd φ)
  -- `Empty` denotes to the layer's `Empty` at every depth
  have hEc : ∀ d : Nat, ∀ φ : Name → Nat,
      denote (cvalSet m.cval emptyRecA.name
        (fun ψ => VExpr.const .emptyRec [1, ψ uNT]))
        ⟨emptyRecA :: env.consts⟩ φ d (.const emptyName []) = some (emptyT 1) := by
    intro d φ
    rw [denote_const, Env.find?_cons,
      if_neg (show ¬ (ConstantInfo.name emptyRecA = emptyName) by decide)]
    rw [hE]
    simp only [show emptyA.toConstantVal.levelParams = [] from rfl,
      List.length_nil, if_true, substFn_nil]
    rw [cvalSet_ne (show emptyName ≠ emptyRecA.name by decide), hEv]
  refine extendBasisTT m (val := fun ψ => .const .emptyRec [1, ψ uNT])
    (by decide) (fun _ => by decide) ?_ hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => by
      injection heq with _ _ _ h4
      subst h4
      intro r hr; exact nomatch hr)
    (fun _ _ _ _ heq => by
      injection heq with _ _ _ h4
      subst h4
      intro rl hrl; exact nomatch hrl)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro ψ t hp
    have : pinnedDirectT (emptyName.str "rec") ψ
        = some (VExpr.const .emptyRec [1, ψ uNT]) := by
      simp only [pinnedDirectT]
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_true]
    rw [show ConstantInfo.name emptyRecA = emptyName.str "rec" from rfl,
      this] at hp
    exact (Option.some.inj hp)
  · intro φ₁ φ₂ hp
    have h1 : φ₁ uNT = φ₂ uNT := hp uNT (by
      show uNT ∈ [uNT]
      exact List.mem_cons_self)
    rw [h1]
  · intro φ
    refine ⟨.pi (.pi (emptyT 1) (.sort (φ uNT)))
      (.pi (emptyT 1) (.app (.bvar 1) (.bvar 0))), ?_, ?_⟩
    · rw [denoteClosed,
        show emptyRecA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
                (.sort (.param uNT)) { bi := .default })
              (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
                (.app (.bvar 1) (.bvar 0)) { bi := .default })
              { bi := .default } from rfl,
        denote_forallE, denote_forallE]
      rw [hEc 0 φ]
      simp [Expr.instantiate1, denote_sort, Level.eval, denote_forallE,
        hEc 1 φ, denote_app, denote_fvar]
    · exact HasType.const


/-- **The `Empty` block, installed.**  The chain is two links and the
driver walks it. -/
theorem declBasisTT_emptyK {env env₁ : Env} (m : EnvTT env)
    (h : BasisChain env BasisKind.emptyK.declsA env₁) :
    Nonempty (EnvTT env₁) := by
  rw [show BasisKind.emptyK.declsA = [emptyA, emptyRecA] from rfl] at h
  cases h with
  | cons h1 h =>
  cases h with
  | cons h2 h =>
  cases h with
  | nil =>
  have hwf1 : EnvWF ⟨emptyA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, -⟩ := extendEmptyTT m h1 hwf1
  have hE : (⟨emptyA :: env.consts⟩ : Env).find? emptyName = some emptyA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf2 : EnvWF ⟨emptyRecA :: emptyA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq),
      (fun _ _ _ _ heq => by
        injection heq with _ _ _ h4
        subst h4
        intro r hr; exact nomatch hr),
      (fun _ _ heq => nomatch heq)⟩
  case refine_1 =>
    show Expr.constsResolve _ emptyRecA.toConstantVal.type = true
    simp only [show emptyRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
              (.sort (.param uNT)) { bi := .default })
            (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
              (.app (.bvar 1) (.bvar 0)) { bi := .default })
            { bi := .default } from rfl,
      Expr.constsResolve, Bool.and_eq_true, Option.isSome_iff_exists]
    have hf : (⟨emptyRecA :: emptyA :: env.consts⟩ : Env).find? emptyName
        = some emptyA := by
      rw [Env.find?_cons,
        if_neg (show ¬ (ConstantInfo.name emptyRecA = emptyName) by decide)]
      exact hE
    rw [hf]
    simp
  obtain ⟨m2, -⟩ := extendEmptyRecTT m1 hE h2 hwf2
  exact ⟨m2⟩


/-! ## `PUnit`

The first block with a rule, and the smallest one that exercises the
whole of `hheadRec`.  Two things about it generalise.

**The recursor's level list is the reason `pinnedDirectT` had to be
fixed**: `PUnit.rec` binds `u_1, u` with the *motive* first, and the
layer's `punitRec` takes the *type*'s level first.

**The rule's constructor spine carries an arbitrary level.**  Nothing
in `hheadRec` ties the `usj` the major premise is built at to the `us`
the recursor is read at — the telescope only says the spine *inhabits*
the major domain.  For `PUnit` the gap closes with `punitEta`, which
equates any two `PUnit` elements at any two levels; a block without a
unit-like law would have to close it another way, and that is worth
knowing before `Nat` and `PSigma`. -/

/-- `PUnit`, installed. -/
theorem extendPUnitTT {env : Env} (m : EnvTT env)
    (hfresh : env.find? punitName = none)
    (hwf : EnvWF ⟨punitA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨punitA :: env.consts⟩,
      m'.cval = cvalSet m.cval punitA.name (fun ψ => punitT (ψ uNT)) := by
  refine extendBasisTT m (val := fun ψ => punitT (ψ uNT)) (by decide)
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name punitA = punitName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uNT (by show uNT ∈ [uNT]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨.sort (φ uNT), ?_, HasType.const⟩
    rw [denoteClosed, show punitA.toConstantVal.type = Expr.sort (.param uNT)
      from rfl, denote_sort]
    rfl

/-- `PUnit.unit`, installed. -/
theorem extendPUnitUnitTT {env : Env} (m : EnvTT env)
    (hP : env.find? punitName = some punitA)
    (hfresh : env.find? punitUnitName = none)
    (hwf : EnvWF ⟨punitUnitA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨punitUnitA :: env.consts⟩,
      m'.cval = cvalSet m.cval punitUnitA.name
        (fun ψ => punitUnitT (ψ uNT)) := by
  refine extendBasisTT m (val := fun ψ => punitUnitT (ψ uNT)) (by decide)
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name punitUnitA = punitUnitName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uNT (by show uNT ∈ [uNT]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨punitT (φ uNT), ?_, HasType.const⟩
    rw [denoteClosed, show punitUnitA.toConstantVal.type
      = Expr.const punitName [.param uNT] from rfl]
    refine denote_const_pin m (by decide) hP rfl (by decide) ?_ 0
    simp +decide [pinnedDirectT]
    rfl


/-- `PUnit.rec`, installed — the block's whole content. -/
theorem extendPUnitRecTT {env : Env} (m : EnvTT env)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA)
    (hfresh : env.find? (punitName.str "rec") = none)
    (hwf : EnvWF ⟨punitRecA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨punitRecA :: env.consts⟩,
      m'.cval = cvalSet m.cval punitRecA.name
        (fun ψ => VExpr.const .punitRec [ψ uNT, ψ u1NT]) := by
  have hPc : ∀ (d : Nat) (φ : Name → Nat) (l : Level),
      denote (cvalSet m.cval punitRecA.name
          (fun ψ => VExpr.const .punitRec [ψ uNT, ψ u1NT]))
        ⟨punitRecA :: env.consts⟩ φ d (.const punitName [l])
        = some (punitT (l.eval φ)) := by
    intro d φ l
    refine denote_const_pin m (by decide) hP rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  have hUc : ∀ (d : Nat) (φ : Name → Nat) (l : Level),
      denote (cvalSet m.cval punitRecA.name
          (fun ψ => VExpr.const .punitRec [ψ uNT, ψ u1NT]))
        ⟨punitRecA :: env.consts⟩ φ d (.const punitUnitName [l])
        = some (punitUnitT (l.eval φ)) := by
    intro d φ l
    refine denote_const_pin m (by decide) hU rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  refine extendBasisTT m
    (val := fun ψ => VExpr.const .punitRec [ψ uNT, ψ u1NT]) (by decide)
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name punitRecA = punitName.str "rec" from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · -- the valuation reads only `u` and `u_1`
    intro φ₁ φ₂ hp
    rw [hp uNT (by
        show uNT ∈ [u1NT, uNT]
        exact List.mem_cons_of_mem _ List.mem_cons_self),
      hp u1NT (by show u1NT ∈ [u1NT, uNT]; exact List.mem_cons_self)]
  · -- the pinned type, denoted
    intro φ
    refine ⟨_, ?_, HasType.const⟩
    rw [denoteClosed,
      show punitRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t")
              (.const punitName [.param uNT]) (.sort (.param u1NT))
              { bi := .default })
            (Expr.forallE (Name.anonymous.str "unit")
              (.app (.bvar 0) (.const punitUnitName [.param uNT]))
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uNT])
                (.app (.bvar 2) (.bvar 0)) { bi := .default })
              { bi := .default })
            { bi := .implicit } from rfl]
    simp [denote_forallE, denote_sort, denote_app, denote_fvar,
      Expr.instantiate1, Level.eval, hPc, hUc, BConst.type, arrow, punitT,
      punitUnitT]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨punitUnitA.toConstantVal, 0, 0, hU⟩
    · exact nomatch hr'
  · -- the iota rule
    intro cv mI rP rules heq
    injection heq with h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · refine ⟨Nat.le_refl 2, ?_⟩
      intro φ d us hus
      obtain ⟨w1, w2, rfl⟩ : ∃ a b, us = [a, b] := by
        match us, hus with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      have hsu : Level.subst [Name.anonymous.str "u_1", Name.anonymous.str "u"]
          [w1, w2] (.param (Name.anonymous.str "u")) = w2 := by
        simp [Level.subst, Level.subst.go]
      have hsu1 : Level.subst [Name.anonymous.str "u_1", Name.anonymous.str "u"]
          [w1, w2] (.param (Name.anonymous.str "u_1")) = w1 := by
        simp [Level.subst, Level.subst.go]
      have hPc' := fun (d : Nat) (φ : Name → Nat) (l : Level) =>
        hPc d φ l
      have hUc' := fun (d : Nat) (φ : Name → Nat) (l : Level) =>
        hUc d φ l
      simp only [punitName, punitUnitName] at hPc' hUc'
      refine ⟨.lam (.pi (punitT (w2.eval φ)) (.sort (w1.eval φ)))
        (.lam (.app (.bvar 0) (punitUnitT (w2.eval φ))) (.bvar 0)), ?_, ?_⟩
      · simp only [Expr.instantiateLevelParams, List.map_cons, List.map_nil,
          hsu, hsu1, denote_lam, denote_forallE, denote_sort, denote_app,
          Expr.instantiate1_bvar, Expr.instantiate1_const,
          Expr.instantiate1_sort, Expr.instantiate1_fvar,
          Expr.instantiate1_app, Expr.instantiate1_forallE,
          Expr.instantiate1_lam, reduceIte, hPc', hUc', denote_fvar]
        simp
      · intro cvj cnP cnF hfj Δ usj xs ys TV TVj restR restC hxs hys husj
          hlev hTV hTVj hR hC
        -- the rule's constructor is the stored `PUnit.unit`
        have hU' := hU
        simp only [punitUnitName, punitName] at hU'
        rw [Env.find?_cons, if_neg (by decide), hU'] at hfj
        obtain ⟨rfl, rfl, rfl⟩ :
            cvj = punitUnitA.toConstantVal ∧ cnP = 0 ∧ cnF = 0 := by
          injection Option.some.inj hfj with h1 h2 h3
          exact ⟨h1.symm, h2.symm, h3.symm⟩
        obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
        obtain ⟨M, mm, rfl⟩ : ∃ a b, xs = [a, b] := by
          match xs, hxs with
          | [a, b], _ => exact ⟨a, b, rfl⟩
        -- the recursor's type, denoted
        obtain rfl : TV = .pi (.pi (punitT (w2.eval φ)) (.sort (w1.eval φ)))
            (.pi (.app (.bvar 0) (punitUnitT (w2.eval φ)))
              (.pi (punitT (w2.eval φ)) (.app (.bvar 2) (.bvar 0)))) := by
          simp [Expr.instantiateLevelParams, hsu, hsu1, denote_forallE,
            denote_sort, denote_app, denote_fvar, hPc', hUc'] at hTV
          exact hTV.symm
        -- the telescope's three premises
        cases hR with | cons hM hR =>
        cases hR with | cons hm hR =>
        cases hR with | cons hct hR =>
        obtain ⟨l0, rfl⟩ : ∃ a, usj = [a] := by
          match usj, husj with
          | [a], _ => exact ⟨a, rfl⟩
        simp only [VExpr.inst_pi, VExpr.inst_app, VExpr.inst_bvar,
          VExpr.liftN_zero, punitT, punitUnitT, VExpr.inst_const,
          reduceIte] at hm hct
        -- **the fire site's level test does the work the eta law used
        -- to do**: the constructor's valuation is at the recursor's own
        -- level, not at an unrelated one
        have hctorV : cvalSet m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uNT, ψ u1NT])
            ((Name.anonymous.str "PUnit").str "unit")
            (Level.substFn φ punitUnitA.toConstantVal.levelParams [l0])
            = punitUnitT (w2.eval φ) := by
          rw [cvalSet_ne (by decide), hlev]
          refine cval_pinned m (by decide) (by rw [hU']; rfl) _ ?_
          simp +decide [pinnedDirectT]
          rfl
        have hrecV : cvalSet m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uNT, ψ u1NT]) punitRecA.name
            (Level.substFn φ [Name.anonymous.str "u_1", Name.anonymous.str "u"]
              [w1, w2])
            = VExpr.const .punitRec [w2.eval φ, w1.eval φ] := by
          rw [cvalSet_self]
          simp [Level.substFn, uNT, u1NT]
        rw [show VExpr.mkAppN (cvalSet m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uNT, ψ u1NT])
            ((Name.anonymous.str "PUnit").str "unit")
            (Level.substFn φ punitUnitA.toConstantVal.levelParams [l0])) []
          = cvalSet m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uNT, ψ u1NT])
            ((Name.anonymous.str "PUnit").str "unit")
            (Level.substFn φ punitUnitA.toConstantVal.levelParams [l0])
          from rfl, hctorV] at hct ⊢
        rw [hrecV]
        -- the iota rule of the layer
        have hRec : Deq Δ (punitRecT (w2.eval φ) (w1.eval φ) M mm
            (punitUnitT (w2.eval φ))) mm :=
          Deq.intro (HasType.punitRecUnit (T := mm) hM hm)
        -- and the right-hand side beta-reduces to the minor premise
        have hb1 : Deq Δ
            (.app (VExpr.lam (.pi (punitT (w2.eval φ)) (.sort (w1.eval φ)))
              (.lam (.app (.bvar 0) (punitUnitT (w2.eval φ))) (.bvar 0))) M)
            (.lam (.app M (punitUnitT (w2.eval φ))) (.bvar 0)) := by
          have := HasType.beta (T := M) (Γ := Δ) (A := _) (a := M)
            (b := VExpr.lam (.app (.bvar 0) (punitUnitT (w2.eval φ)))
              (.bvar 0)) hM
          simp only [VExpr.inst, VExpr.inst_app, VExpr.inst_bvar,
            VExpr.liftN_zero, reduceIte] at this
          exact Deq.intro this
        have hb2 : Deq Δ
            (.app (VExpr.lam (.app M (punitUnitT (w2.eval φ))) (.bvar 0)) mm)
            mm := by
          have := HasType.beta (T := mm) (Γ := Δ) (a := mm) (b := VExpr.bvar 0)
            hm
          simp only [VExpr.inst, VExpr.inst_bvar, VExpr.liftN_zero,
            reduceIte] at this
          exact Deq.intro this
        exact Deq.trans hRec (Deq.symm (Deq.trans (Deq.appFun hb1) hb2))
    · exact nomatch hr'


/-- **The `PUnit` block, installed.** -/
theorem declBasisTT_punitK {env env₁ : Env} (m : EnvTT env)
    (h : BasisChain env BasisKind.punitK.declsA env₁) :
    Nonempty (EnvTT env₁) := by
  rw [show BasisKind.punitK.declsA = [punitA, punitUnitA, punitRecA] from rfl]
    at h
  cases h with
  | cons h1 h =>
  cases h with
  | cons h2 h =>
  cases h with
  | cons h3 h =>
  cases h with
  | nil =>
  have hwf1 : EnvWF ⟨punitA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, -⟩ := extendPUnitTT m h1 hwf1
  have hP1 : (⟨punitA :: env.consts⟩ : Env).find? punitName = some punitA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf2 : EnvWF ⟨punitUnitA :: punitA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?res2, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res2 =>
    show Expr.constsResolve _ punitUnitA.toConstantVal.type = true
    have hf : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find? punitName
        = some punitA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hP1
    simp only [show punitUnitA.toConstantVal.type
        = Expr.const punitName [.param uNT] from rfl, Expr.constsResolve, hf]
    rfl
  obtain ⟨m2, -⟩ := extendPUnitUnitTT m1 hP1 h2 hwf2
  have hP2 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find? punitName
      = some punitA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hP1
  have hU2 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find? punitUnitName
      = some punitUnitA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf3 : EnvWF ⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ :=
    EnvWF.cons hwf2 ⟨rfl, rfl, ?res3, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec3,
      (fun _ _ heq => nomatch heq)⟩
  case res3 =>
    show Expr.constsResolve _ punitRecA.toConstantVal.type = true
    have hfP : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env).find?
        punitName = some punitA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hP2
    have hfU : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env).find?
        punitUnitName = some punitUnitA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hU2
    rw [show punitRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t")
              (.const punitName [.param uNT]) (.sort (.param u1NT))
              { bi := .default })
            (Expr.forallE (Name.anonymous.str "unit")
              (.app (.bvar 0) (.const punitUnitName [.param uNT]))
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uNT])
                (.app (.bvar 2) (.bvar 0)) { bi := .default })
              { bi := .default })
            { bi := .implicit } from rfl]
    simp only [Expr.constsResolve, hfP, hfU, Option.isSome_some,
      Bool.and_self, Bool.and_true]
  case rec3 =>
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h4'
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
      · subst h1'; rfl
      · have hfP : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ :
            Env).find? punitName = some punitA := by
          rw [Env.find?_cons, if_neg (by decide)]; exact hP2
        have hfU : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ :
            Env).find? punitUnitName = some punitUnitA := by
          rw [Env.find?_cons, if_neg (by decide)]; exact hU2
        show Expr.constsResolve _ (Expr.lam (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t")
              (.const punitName [.param uNT]) (.sort (.param u1NT))
              { bi := .default })
            (Expr.lam (Name.anonymous.str "unit")
              (.app (.bvar 0) (.const punitUnitName [.param uNT]))
              (.bvar 0) { bi := .default })
            { bi := .default }) = true
        simp only [Expr.constsResolve, hfP, hfU, Option.isSome_some,
          Bool.and_self, Bool.and_true]
    · exact nomatch hr'
  obtain ⟨m3, -⟩ := extendPUnitRecTT m2 hP2 hU2 h3 hwf3
  exact ⟨m3⟩


/-- A declaration read at its *own* level parameters is read at the
ambient assignment.  Every basis constant's type mentions its siblings
this way. -/
theorem substFn_param_self (φ : Name → Nat) :
    ∀ (ks : List Name), Level.substFn φ ks (ks.map Level.param) = φ := by
  intro ks
  induction ks with
  | nil => funext n; rfl
  | cons k ks ih =>
    funext n
    by_cases h : k = n
    · subst h; simp [Level.substFn, Level.eval]
    · simp only [List.map_cons, Level.substFn, if_neg h]
      exact congrFun ih n


/-! ### β along a spine

Every basis block's iota rule is the same shape — a λ-tower applied to
the fire site's spine — and every one of them would otherwise spell out
its own chain of intermediate towers.  `BetaSpine` records the chain
and `Deq.ofBetaSpine` collapses it, so a block's iota obligation is
*building the relation*, which the telescope's own typings do. -/

/-- `f` applied to `args` β-reduces to `r`, one binder at a time. -/
inductive BetaSpine (Γ : List VExpr) : VExpr → List VExpr → VExpr → Prop
  | nil {f : VExpr} : BetaSpine Γ f [] f
  | cons {A b x : VExpr} {xs : List VExpr} {r : VExpr} :
      HasType Γ x A → BetaSpine Γ (b.inst x) xs r →
      BetaSpine Γ (.lam A b) (x :: xs) r

/-- A `Deq` under a spine's head. -/
theorem Deq.mkAppN_congrFun {Γ : List VExpr} :
    ∀ (xs : List VExpr) {f f' : VExpr}, Deq Γ f f' →
      Deq Γ (VExpr.mkAppN f xs) (VExpr.mkAppN f' xs)
  | [], _, _, h => h
  | x :: xs, _, _, h => Deq.mkAppN_congrFun xs (Deq.appFun h)

/-- **The chain, collapsed.** -/
theorem Deq.ofBetaSpine {Γ : List VExpr} {f : VExpr} {args : List VExpr}
    {r : VExpr} (h : BetaSpine Γ f args r) :
    Deq Γ (VExpr.mkAppN f args) r := by
  induction h with
  | nil => exact Deq.refl
  | @cons A b x xs r hx _ ih =>
    exact Deq.trans (Deq.mkAppN_congrFun xs
      (Deq.intro (HasType.beta (T := x) hx))) ih


/-- Substituting each level parameter by itself is the identity. -/
theorem Level.subst_param_self (ks : List Name) :
    ∀ l : Level, Level.subst ks (ks.map Level.param) l = l := by
  have hgo : ∀ (ks : List Name) (n : Name),
      Level.subst.go ks (ks.map Level.param) n = .param n := by
    intro ks
    induction ks with
    | nil => intro n; rfl
    | cons k ks ih =>
      intro n
      by_cases h : k = n
      · subst h; simp [Level.subst.go]
      · simp only [List.map_cons, Level.subst.go, if_neg h]
        exact ih n
  intro l
  induction l with
  | zero => rfl
  | succ l ih => simp [Level.subst, ih]
  | max l r ihl ihr => simp [Level.subst, ihl, ihr]
  | imax l r ihl ihr => simp [Level.subst, ihl, ihr]
  | param n => exact hgo ks n

/-- …and so is instantiating a declaration at its own parameters. -/
theorem Expr.instantiateLevelParams_self (ks : List Name) :
    ∀ e : Expr, e.instantiateLevelParams ks (ks.map Level.param) = e := by
  intro e
  have hmap : ∀ us : List Level,
      us.map (Level.subst ks (ks.map Level.param)) = us := by
    intro us
    induction us with
    | nil => rfl
    | cons x xs ih => simp [Level.subst_param_self, ih]
  induction e <;>
    simp_all [Expr.instantiateLevelParams, Level.subst_param_self, hmap]

/-! ## `Eq`

The block whose valuations were **deferred** (§11, and the house rule:
a definition is a conjecture until a consumer elaborates).  Three of the
layer's four derived constants live here, and this is the install that
elaborates them.

`Eq` is the layer's `eqE` former eta-expanded; `Eq.refl` is `.prf`
under two binders; `Eq.rec` returns its minor premise, retyped by
`conv`.  **None of the three needs a computation rule of the layer** —
the block's iota is β, because the layer *derives* the eliminator
rather than carrying it. -/

/-- `Eq`'s valuation: the former, eta-expanded. -/
def eqValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uNT)) (.lam (.bvar 0) (.lam (.bvar 1)
    (.eqE (.bvar 2) (.bvar 1) (.bvar 0))))

/-- `Eq.refl`'s valuation. -/
def eqReflValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uNT)) (.lam (.bvar 0) .prf)

/-- The tower is closed. -/
theorem eqValT_closed (ψ : Name → Nat) : VExpr.Closed (eqValT ψ) := by
  simp only [eqValT, VExpr.Closed, VExpr.bvarsBelow]
  exact ⟨trivial, by omega, by omega, by omega, by omega, by omega⟩

/-- `Eq.refl`'s tower is closed. -/
theorem eqReflValT_closed (ψ : Name → Nat) : VExpr.Closed (eqReflValT ψ) := by
  simp only [eqReflValT, VExpr.Closed, VExpr.bvarsBelow]
  exact ⟨trivial, by omega, trivial⟩

/-- **The `Eq` law, from the tower.**  Three β-steps and the lift
absorptions they leave. -/
theorem eqValT_law {ψ : Name → Nat} {Δ : List VExpr} {A a b : VExpr}
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    Deq Δ (VExpr.mkAppN (eqValT ψ) [A, a, b]) (.eqE A a b) := by
  have h1 : Deq Δ (.app (eqValT ψ) A)
      (.lam A (.lam (VExpr.liftN 1 A 0)
        (.eqE (VExpr.liftN 2 A 0) (.bvar 1) (.bvar 0)))) := by
    have := HasType.beta (T := A) (Γ := Δ) (a := A)
      (b := VExpr.lam (.bvar 0) (.lam (.bvar 1)
        (.eqE (.bvar 2) (.bvar 1) (.bvar 0)))) hA
    simp [VExpr.liftN_zero] at this
    exact Deq.intro this
  have h2 : Deq Δ (.app (.lam A (.lam (VExpr.liftN 1 A 0)
        (.eqE (VExpr.liftN 2 A 0) (.bvar 1) (.bvar 0)))) a)
      (.lam A (.eqE (VExpr.liftN 1 A 0) (VExpr.liftN 1 a 0) (.bvar 0))) := by
    have := HasType.beta (T := a) (Γ := Δ) (a := a)
      (b := VExpr.lam (VExpr.liftN 1 A 0)
        (.eqE (VExpr.liftN 2 A 0) (.bvar 1) (.bvar 0))) ha
    rw [VExpr.inst_lam, VExpr.inst_eqE,
      VExpr.inst_liftN_absorb A (Nat.zero_le _) (Nat.le_refl 0) a,
      VExpr.liftN_zero,
      VExpr.inst_liftN_absorb A (Nat.zero_le _) (by omega) a] at this
    simp [VExpr.liftN_zero] at this
    exact Deq.intro this
  have h3 : Deq Δ (.app (VExpr.lam A
        (.eqE (VExpr.liftN 1 A 0) (VExpr.liftN 1 a 0) (.bvar 0))) b)
      (.eqE A a b) := by
    have := HasType.beta (T := b) (Γ := Δ) (a := b)
      (b := VExpr.eqE (VExpr.liftN 1 A 0) (VExpr.liftN 1 a 0) (.bvar 0)) hb
    rw [VExpr.inst_eqE,
      VExpr.inst_liftN_absorb A (Nat.zero_le _) (Nat.le_refl 0) b,
      VExpr.inst_liftN_absorb a (Nat.zero_le _) (Nat.le_refl 0) b,
      VExpr.liftN_zero, VExpr.liftN_zero] at this
    simp [VExpr.liftN_zero] at this
    exact Deq.intro this
  exact Deq.trans (Deq.appFun (Deq.trans (Deq.appFun h1) h2)) h3


/-- The `Eq` spine is a `Prop`, as a term — the tower's codomain is
`Sort 0` and three `app`s reach it. -/
theorem eqValT_sort {ψ : Name → Nat} {Δ : List VExpr} {A a b : VExpr}
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    HasType Δ (VExpr.mkAppN (eqValT ψ) [A, a, b]) (.sort 0) := by
  have h0 : HasType Δ (eqValT ψ)
      (.pi (.sort (ψ uNT)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) :=
    HasType.weakenNil (.lam (.lam (.lam HasType.eqType))) Δ
  have h1 := HasType.app h0 hA
  simp only [VExpr.inst, VExpr.liftN_zero, reduceIte] at h1
  have h2 := HasType.app h1 ha
  simp only [VExpr.inst, Nat.lt_irrefl, if_false, Nat.zero_lt_one, if_true,
    Nat.zero_add] at h2
  rw [VExpr.inst_liftN_absorb A (Nat.zero_le _) (Nat.le_refl 0) a,
    VExpr.liftN_zero] at h2
  have h3 := HasType.app h2 hb
  simpa [VExpr.mkAppN, VExpr.inst] using h3

/-- `Eq.refl`'s tower, applied. -/
theorem eqReflValT_typed {ψ : Name → Nat} {Δ : List VExpr} {A a : VExpr}
    (hA : HasType Δ A (.sort (ψ uNT))) (ha : HasType Δ a A) :
    HasType Δ (VExpr.mkAppN (eqReflValT ψ) [A, a])
      (VExpr.mkAppN (eqValT ψ) [A, a, a]) := by
  have hbody : HasType [VExpr.bvar 0, VExpr.sort (ψ uNT)] VExpr.prf
      (VExpr.mkAppN (eqValT ψ) [.bvar 1, .bvar 0, .bvar 0]) := by
    have hα : HasType [VExpr.bvar 0, VExpr.sort (ψ uNT)] (.bvar 1)
        (.sort (ψ uNT)) := by
      have := HasType.bvar (Γ := [VExpr.bvar 0, VExpr.sort (ψ uNT)])
        (i := 1) (A := .sort (ψ uNT)) (by simp)
      simpa using this
    have ha' : HasType [VExpr.bvar 0, VExpr.sort (ψ uNT)] (.bvar 0)
        (.bvar 1) := by
      have := HasType.bvar (Γ := [VExpr.bvar 0, VExpr.sort (ψ uNT)])
        (i := 0) (A := VExpr.bvar 0) (by simp)
      simpa [VExpr.liftN] using this
    exact HasType.conv (HasType.refl (T := VExpr.bvar 1))
      ((eqValT_law hα ha' ha').symm.toHasType (VExpr.bvar 1))
  have h0 : HasType Δ (eqReflValT ψ)
      (.pi (.sort (ψ uNT)) (.pi (.bvar 0)
        (VExpr.mkAppN (eqValT ψ) [.bvar 1, .bvar 0, .bvar 0]))) :=
    HasType.weakenNil (.lam (.lam hbody)) Δ
  have h1 := HasType.app h0 hA
  simp only [VExpr.inst, VExpr.mkAppN, VExpr.inst_app,
    VExpr.inst_eq_self_of_closed (eqValT_closed ψ), VExpr.liftN_zero,
    reduceIte] at h1
  have h2 := HasType.app h1 ha
  simp only [VExpr.inst, Nat.lt_irrefl, if_false, Nat.zero_lt_one, if_true,
    Nat.zero_add] at h2
  rw [VExpr.inst_liftN_absorb A (Nat.zero_le _) (Nat.le_refl 0) a,
    VExpr.liftN_zero] at h2
  rw [VExpr.inst_eq_self_of_closed (eqValT_closed ψ)] at h2
  simpa [VExpr.mkAppN, VExpr.liftN_zero] using h2


/-- `Eq.rec`'s valuation: the minor premise, returned.  Transport is
the identity — `eqRec_derivable` (`Setlec/TT/Examples.lean`), which is
why the layer does not carry `Eq.rec` at all. -/
def eqRecValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uNT))
    (.lam (.bvar 0)
      (.lam (.pi (.bvar 1)
          (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1NT))))
        (.lam (.app (.app (.bvar 0) (.bvar 1))
            (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]))
          (.lam (.bvar 3)
            (.lam (VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
              (.bvar 2))))))

/-- `Eq.rec`'s frame, innermost first: `[t, b, refl, motive, a, α]`. -/
def eqRecCtx (ψ : Name → Nat) : List VExpr :=
  [VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0], VExpr.bvar 3,
   VExpr.app (.app (.bvar 0) (.bvar 1))
     (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]),
   VExpr.pi (.bvar 1) (.pi (VExpr.mkAppN (eqValT ψ)
     [.bvar 2, .bvar 1, .bvar 0]) (.sort (ψ u1NT))),
   VExpr.bvar 0, VExpr.sort (ψ uNT)]

/-- **`Eq.rec`'s typing** — the derivable-eliminator shape.  The body
has the motive at `a` and `Eq.refl`, where the motive at `b` and the
hypothesis is wanted; two `congrApp`s close the gap, over the equation
*read off the hypothesis* through the law and proof irrelevance. -/
theorem eqRecValT_typed (ψ : Name → Nat) :
    HasType [] (eqRecValT ψ)
      (.pi (.sort (ψ uNT))
        (.pi (.bvar 0)
          (.pi (.pi (.bvar 1)
              (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
                (.sort (ψ u1NT))))
            (.pi (.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]))
              (.pi (.bvar 3)
                (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
                  (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))) := by
  refine .lam (.lam (.lam (.lam (.lam (.lam ?_)))))
  show HasType (eqRecCtx ψ) (VExpr.bvar 2) _
  have hα : HasType (eqRecCtx ψ) (.bvar 5) (.sort (ψ uNT)) := by
    have := HasType.bvar (Γ := eqRecCtx ψ) (i := 5) (A := .sort (ψ uNT))
      (by simp [eqRecCtx])
    simpa using this
  have ha : HasType (eqRecCtx ψ) (VExpr.bvar 4) (VExpr.bvar 5) := by
    have := HasType.bvar (Γ := eqRecCtx ψ) (i := 4) (A := VExpr.bvar 0)
      (by simp [eqRecCtx])
    simpa [VExpr.liftN] using this
  have hb : HasType (eqRecCtx ψ) (VExpr.bvar 1) (VExpr.bvar 5) := by
    have := HasType.bvar (Γ := eqRecCtx ψ) (i := 1) (A := VExpr.bvar 3)
      (by simp [eqRecCtx])
    simpa [VExpr.liftN] using this
  have ht : HasType (eqRecCtx ψ) (VExpr.bvar 0)
      (VExpr.mkAppN (eqValT ψ) [.bvar 5, .bvar 4, .bvar 1]) := by
    have := HasType.bvar (Γ := eqRecCtx ψ) (i := 0)
      (A := VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
      (by simp [eqRecCtx])
    simpa [VExpr.mkAppN, VExpr.liftN,
      VExpr.liftN_eq_self_of_closed (eqValT_closed ψ)] using this
  have hab : Deq (eqRecCtx ψ) (VExpr.bvar 4) (VExpr.bvar 1) :=
    Deq.intro (HasType.conv ht
      ((eqValT_law hα ha hb).toHasType (VExpr.bvar 5)))
  have hrt : Deq (eqRecCtx ψ) (VExpr.mkAppN (eqReflValT ψ) [.bvar 5, .bvar 4])
      (VExpr.bvar 0) :=
    Deq.intro (HasType.proofIrrel (eqValT_sort hα ha ha)
      (eqValT_sort hα ha hb) (eqReflValT_typed hα ha) ht)
  have hmot : HasType (eqRecCtx ψ) (VExpr.bvar 2)
      (VExpr.app (.app (.bvar 3) (.bvar 4))
        (VExpr.mkAppN (eqReflValT ψ) [.bvar 5, .bvar 4])) := by
    have := HasType.bvar (Γ := eqRecCtx ψ) (i := 2)
      (A := VExpr.app (.app (.bvar 0) (.bvar 1))
        (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1])) (by simp [eqRecCtx])
    simpa [VExpr.mkAppN, VExpr.liftN,
      VExpr.liftN_eq_self_of_closed (eqReflValT_closed ψ)] using this
  exact HasType.conv hmot
    ((Deq.app (Deq.appArg hab) hrt).toHasType
      (VExpr.app (.app (.bvar 3) (.bvar 4))
        (VExpr.mkAppN (eqReflValT ψ) [.bvar 5, .bvar 4])))


/-- `Eq.rec`'s tower is closed. -/
theorem eqRecValT_closed (ψ : Name → Nat) : VExpr.Closed (eqRecValT ψ) := by
  simp only [eqRecValT, VExpr.Closed, VExpr.bvarsBelow, VExpr.mkAppN,
    eqValT, eqReflValT]
  repeat' apply And.intro
  all_goals first | trivial | omega


/-- The towers read the assignment only at their own level names. -/
theorem eqValT_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uNT = ψ₂ uNT) :
    eqValT ψ₁ = eqValT ψ₂ := by rw [eqValT, eqValT, h]

theorem eqReflValT_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uNT = ψ₂ uNT) :
    eqReflValT ψ₁ = eqReflValT ψ₂ := by rw [eqReflValT, eqReflValT, h]

/-- **`Eq.rec`'s pinned type, denoted at any depth and any levels.**

The general form is the one `hheadRec` supplies at a fire site — depth
`d`, the recursor's own `us` — and the install's own `htype` is its
special case at depth `0` and the declaration's own parameters
(`substFn_param_self`).  Written once for the same reason `BetaSpine`
and the `instantiate1` kit were: every block needs exactly this
shape. -/
theorem denote_eqRec_type {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w1 w2 : Level)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.cval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.cval eqReflName ψ = eqReflValT ψ) :
    denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ d
        (eqRecA.toConstantVal.type.instantiateLevelParams
          eqRecA.toConstantVal.levelParams [w1, w2])
      = some (.pi (.sort (w2.eval φ))
        (.pi (.bvar 0)
          (.pi (.pi (.bvar 1)
              (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uNT] [w2]))
                  [.bvar 2, .bvar 1, .bvar 0])
                (.sort (w1.eval φ))))
            (.pi (.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uNT] [w2]))
                  [.bvar 2, .bvar 1]))
              (.pi (.bvar 3)
                (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uNT] [w2]))
                    [.bvar 4, .bvar 3, .bvar 0])
                  (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))) := by
  have hsu : Level.subst [u1NT, uNT] [w1, w2] (.param uNT) = w2 := by
    simp [Level.subst, Level.subst.go, uNT, u1NT]
  have hsu1 : Level.subst [u1NT, uNT] [w1, w2] (.param u1NT) = w1 := by
    simp [Level.subst, Level.subst.go, u1NT]
  have hEc : ∀ e : Nat,
      denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqName [w2]) = some (eqValT (Level.substFn φ [uNT] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([w2] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hEv]
    rfl
  have hRc : ∀ e : Nat,
      denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqReflName [w2])
        = some (eqReflValT (Level.substFn φ [uNT] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hR]
    simp only [show ([w2] : List Level).length
      = eqReflA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hRv]
    rfl
  rw [show eqRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uNT))
          (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.app (.const eqName [.param uNT]) (.bvar 2))
                    (.bvar 1)) (.bvar 0))
                  (.sort (.param u1NT)) { bi := .default })
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "refl")
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uNT]) (.bvar 2))
                    (.bvar 1)))
                (Expr.forallE (Name.anonymous.str "b") (.bvar 3)
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.app (.const eqName [.param uNT]) (.bvar 4))
                      (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                    { bi := .default })
                  { bi := .implicit })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show eqRecA.toConstantVal.levelParams = [u1NT, uNT] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsu1, denote_forallE, denote_sort,
    denote_app, denote_fvar, hEc, hRc, VExpr.mkAppN]


/-- `Eq.rec`'s single stored rule. -/
def eqRecRule : RecRule :=
  { ctor := eqReflName, nfields := 0, ctorParams := 2, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "α") (.sort (.param uNT))
      (Expr.lam (Name.anonymous.str "a") (.bvar 0)
        (Expr.lam (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
            (Expr.forallE (Name.anonymous.str "t")
              (.app (.app (.app (.const eqName [.param uNT]) (.bvar 2))
                (.bvar 1)) (.bvar 0))
              (.sort (.param u1NT)) { bi := .default })
            { bi := .default })
          (Expr.lam (Name.anonymous.str "refl")
            (.app (.app (.bvar 0) (.bvar 1))
              (.app (.app (.const eqReflName [.param uNT]) (.bvar 2))
                (.bvar 1)))
            (.bvar 0) { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .implicit } }

/-- The stored declaration, with its rule named. -/
theorem eqRecA_eq :
    eqRecA = .recInfo eqRecA.toConstantVal 5 4 [eqRecRule] := rfl

/-- **`Eq.rec`'s rule right-hand side, denoted** — the same four
domains the type has, over the minor premise. -/
theorem denote_eqRec_rhs {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w1 w2 : Level)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.cval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.cval eqReflName ψ = eqReflValT ψ) :
    denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ d
        ((RecRule.rhs eqRecRule).instantiateLevelParams
          eqRecA.toConstantVal.levelParams [w1, w2])
      = some (.lam (.sort (w2.eval φ))
        (.lam (.bvar 0)
          (.lam (.pi (.bvar 1)
              (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uNT] [w2]))
                  [.bvar 2, .bvar 1, .bvar 0])
                (.sort (w1.eval φ))))
            (.lam (.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uNT] [w2]))
                  [.bvar 2, .bvar 1]))
              (.bvar 0))))) := by
  have hsu : Level.subst [u1NT, uNT] [w1, w2] (.param uNT) = w2 := by
    simp [Level.subst, Level.subst.go, uNT, u1NT]
  have hsu1 : Level.subst [u1NT, uNT] [w1, w2] (.param u1NT) = w1 := by
    simp [Level.subst, Level.subst.go, u1NT]
  have hEc : ∀ e : Nat,
      denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqName [w2]) = some (eqValT (Level.substFn φ [uNT] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([w2] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hEv]
    rfl
  have hRc : ∀ e : Nat,
      denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqReflName [w2])
        = some (eqReflValT (Level.substFn φ [uNT] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hR]
    simp only [show ([w2] : List Level).length
      = eqReflA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hRv]
    rfl
  rw [show eqRecA.toConstantVal.levelParams = [u1NT, uNT] from rfl]
  simp only [eqRecRule]
  simp [Expr.instantiateLevelParams, hsu, hsu1, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hEc, hRc, VExpr.mkAppN]


/-- **`Eq`, installed** — and with it §11's law, discharged from the
tower rather than assumed. -/
theorem extendEqTT {env : Env} (m : EnvTT env)
    (hfresh : env.find? eqName = none)
    (hwf : EnvWF ⟨eqA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨eqA :: env.consts⟩,
      m'.cval = cvalSet m.cval eqA.name eqValT := by
  refine extendBasisTT m (val := eqValT) (by decide) (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name eqA = eqName from rfl] at hp
      simp +decide [pinnedDirectT] at hp)
    hfresh hwf (fun _ => by
      simp only [eqValT, VExpr.Closed, VExpr.bvarsBelow]
      exact ⟨trivial, by omega, by omega, by omega, by omega, by omega⟩) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq) ?_
  · intro φ₁ φ₂ hp
    rw [eqValT, eqValT,
      hp uNT (by show uNT ∈ [uNT]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨.pi (.sort (φ uNT)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0))), ?_,
      ?_⟩
    · rw [denoteClosed,
        show eqA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "α") (.sort (.param uNT))
              (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
                (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                  (.sort .zero) { bi := .default }) { bi := .default })
              { bi := .implicit } from rfl]
      simp [denote_forallE, denote_sort, denote_fvar, Level.eval]
    · exact .lam (.lam (.lam HasType.eqType))
  · -- **§11's law**: three β-steps on the tower
    intro _ _ ψ Δ A a b hA ha hb
    rw [show cvalSet m.cval eqA.name eqValT eqName = eqValT from
      cvalSet_self (n := eqA.name)]
    exact eqValT_law hA ha hb


/-- `Eq.refl`, installed. -/
theorem extendEqReflTT {env : Env} (m : EnvTT env)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, m.cval eqName ψ = eqValT ψ)
    (hfresh : env.find? eqReflName = none)
    (hwf : EnvWF ⟨eqReflA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨eqReflA :: env.consts⟩,
      m'.cval = cvalSet m.cval eqReflA.name eqReflValT := by
  have hEc : ∀ (d : Nat) (φ : Name → Nat),
      denote (cvalSet m.cval eqReflA.name eqReflValT)
        ⟨eqReflA :: env.consts⟩ φ d (.const eqName [.param uNT])
        = some (eqValT φ) := by
    intro d φ
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([Level.param uNT] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide),
      show Level.substFn φ eqA.toConstantVal.levelParams [Level.param uNT]
        = φ from substFn_param_self φ [uNT], hEv]
  refine extendBasisTT m (val := eqReflValT) (by decide) (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name eqReflA = eqReflName from rfl] at hp
      simp +decide [pinnedDirectT] at hp)
    hfresh hwf (fun _ => by
      simp only [eqReflValT, VExpr.Closed, VExpr.bvarsBelow]
      exact ⟨trivial, by omega, trivial⟩) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [eqReflValT, eqReflValT,
      hp uNT (by show uNT ∈ [uNT]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨.pi (.sort (φ uNT)) (.pi (.bvar 0)
      (VExpr.mkAppN (eqValT φ) [.bvar 1, .bvar 0, .bvar 0])), ?_, ?_⟩
    · rw [denoteClosed,
        show eqReflA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "α") (.sort (.param uNT))
              (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
                (.app (.app (.app (.const eqName [.param uNT]) (.bvar 1))
                  (.bvar 0)) (.bvar 0)) { bi := .default })
              { bi := .implicit } from rfl]
      simp [denote_forallE, denote_sort, denote_app, denote_fvar, Level.eval,
        hEc, VExpr.mkAppN]
    · refine .lam (.lam ?_)
      have hα : HasType [VExpr.bvar 0, VExpr.sort (φ uNT)] (.bvar 1)
          (.sort (φ uNT)) := by
        have := HasType.bvar (Γ := [VExpr.bvar 0, VExpr.sort (φ uNT)])
          (i := 1) (A := .sort (φ uNT)) (by simp)
        simpa using this
      have ha : HasType [VExpr.bvar 0, VExpr.sort (φ uNT)] (.bvar 0)
          (.bvar 1) := by
        have := HasType.bvar (Γ := [VExpr.bvar 0, VExpr.sort (φ uNT)])
          (i := 0) (A := VExpr.bvar 0) (by simp)
        simpa [VExpr.liftN] using this
      exact HasType.conv (HasType.refl (T := VExpr.bvar 1))
        ((eqValT_law hα ha ha).symm.toHasType (VExpr.bvar 1))


/-- **`Eq.rec`, installed** — the block's whole iota is β, because the
layer derives the eliminator rather than carrying it. -/
theorem extendEqRecTT {env : Env} (m : EnvTT env)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.cval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.cval eqReflName ψ = eqReflValT ψ)
    (hfresh : env.find? (eqName.str "rec") = none)
    (hwf : EnvWF ⟨eqRecA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨eqRecA :: env.consts⟩,
      m'.cval = cvalSet m.cval eqRecA.name eqRecValT := by
  refine extendBasisTT m (val := eqRecValT) (by decide) (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name eqRecA = eqName.str "rec" from rfl] at hp
      simp +decide [pinnedDirectT] at hp)
    hfresh hwf (fun ψ => eqRecValT_closed ψ) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · -- the valuation reads only `u` and `u_1`
    intro φ₁ φ₂ hp
    have hu : φ₁ uNT = φ₂ uNT := hp uNT (by
      show uNT ∈ [u1NT, uNT]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [eqRecValT, eqRecValT, hu,
      hp u1NT (by show u1NT ∈ [u1NT, uNT]; exact List.mem_cons_self),
      eqValT_congr hu, eqReflValT_congr hu]
  · -- the pinned type, denoted
    intro φ
    refine ⟨_, ?_, HasType.weakenNil (eqRecValT_typed φ) []⟩
    rw [denoteClosed, ← Expr.instantiateLevelParams_self
        eqRecA.toConstantVal.levelParams eqRecA.toConstantVal.type,
      show eqRecA.toConstantVal.levelParams.map Level.param
        = [Level.param u1NT, Level.param uNT] from rfl,
      denote_eqRec_type m φ 0 (.param u1NT) (.param uNT) hE hR hEv hRv,
      show Level.substFn φ [uNT] [Level.param uNT] = φ from
        substFn_param_self φ [uNT]]
    rfl
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨eqReflA.toConstantVal, 2, 0, hR⟩
    · exact nomatch hr'
  · -- the iota rule: two β-chains meeting at the minor premise
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h1'; subst h2'; subst h3'; subst h4'
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · refine ⟨by omega, ?_⟩
      intro φ d us hus
      obtain ⟨w1, w2, rfl⟩ : ∃ a b, us = [a, b] := by
        match us, hus with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      refine ⟨_, denote_eqRec_rhs m (val := eqRecValT) φ d w1 w2 hE hR hEv
        hRv, ?_⟩
      intro cvj cnP cnF hfj Δ usj xs ys TV TVj restR restC hxs hys husj hlev
        hdTV hdTVj hfitR hfitC
      have hRu := hR
      simp only [eqReflName, eqName] at hRu
      rw [Env.find?_cons, if_neg (by decide), hRu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = eqReflA.toConstantVal ∧ cnP = 2 ∧ cnF = 0 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain ⟨q1, q2, rfl⟩ : ∃ a b, ys = [a, b] := by
        match ys, hys with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      obtain ⟨xα, xa, xM, xh, xb, rfl⟩ :
          ∃ a b c e f, xs = [a, b, c, e, f] := by
        match xs, hxs with
        | [a, b, c, e, f], _ => exact ⟨a, b, c, e, f, rfl⟩
      obtain rfl : TV = _ :=
        (Option.some.inj ((denote_eqRec_type m (val := eqRecValT) φ d w1 w2
          hE hR hEv hRv).symm.trans hdTV)).symm
      -- the constructor's valuation sits at the recursor's own level
      have hctor : cvalSet m.cval eqRecA.name eqRecValT
          ((Name.anonymous.str "Eq").str "refl")
          (Level.substFn φ eqReflA.toConstantVal.levelParams usj)
          = eqReflValT (Level.substFn φ [uNT] [w2]) := by
        have hRv' := hRv
        simp only [eqReflName, eqName] at hRv'
        rw [cvalSet_ne (by decide), hRv']
        refine eqReflValT_congr ?_
        have := congrFun hlev uNT
        simp only [recFireComparands] at this
        rw [this]
        rfl
      rw [hctor] at hfitR
      rw [cvalSet_self, hctor]
      -- the telescope's six typings
      cases hfitR with | cons t1 hfitR =>
      cases hfitR with | cons t2 hfitR =>
      cases hfitR with | cons t3 hfitR =>
      cases hfitR with | cons t4 hfitR =>
      cases hfitR with | cons t5 hfitR =>
      cases hfitR with | cons t6 hfitR =>
      -- **the two β-chains**: the telescope's typings are exactly what
      -- `BetaSpine` wants, at exactly the instantiated domains
      refine Deq.trans (Deq.ofBetaSpine
        (.cons t1 (.cons t2 (.cons t3 (.cons t4 (.cons t5
          (.cons t6 .nil))))))) ?_
      refine Deq.trans ?_ (Deq.ofBetaSpine
        (f := VExpr.lam (.sort (w2.eval φ))
          (.lam (.bvar 0)
            (.lam (.pi (.bvar 1)
                (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uNT] [w2]))
                    [.bvar 2, .bvar 1, .bvar 0])
                  (.sort (w1.eval φ))))
              (.lam (.app (.app (.bvar 0) (.bvar 1))
                  (VExpr.mkAppN (eqReflValT (Level.substFn φ [uNT] [w2]))
                    [.bvar 2, .bvar 1]))
                (.bvar 0)))))
        (.cons t1 (.cons t2 (.cons t3 (.cons t4 .nil))))).symm
      show Deq Δ (((VExpr.liftN 2 xh 0).inst xb 1).inst
          (VExpr.mkAppN (eqReflValT (Level.substFn φ [uNT] [w2])) [q1, q2]) 0)
        (VExpr.liftN 0 xh 0)
      rw [VExpr.inst_liftN_absorb xh (Nat.zero_le _) (Nat.le_refl 1) xb,
        VExpr.inst_liftN_absorb xh (Nat.zero_le _) (Nat.le_refl 0) _]
    · exact nomatch hr'


/-- **The `Eq` block, installed.**  Two `BetaSpine`s meeting at the
minor premise are the whole of its iota — the block whose eliminator
the layer derives is the block whose install has no computation
obligation. -/
theorem declBasisTT_eqK {env env₁ : Env} (m : EnvTT env)
    (h : BasisChain env BasisKind.eqK.declsA env₁) :
    Nonempty (EnvTT env₁) := by
  rw [show BasisKind.eqK.declsA = [eqA, eqReflA, eqRecA] from rfl] at h
  cases h with
  | cons h1 h =>
  cases h with
  | cons h2 h =>
  cases h with
  | cons h3 h =>
  cases h with
  | nil =>
  have hwf1 : EnvWF ⟨eqA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, hm1⟩ := extendEqTT m h1 hwf1
  have hE1 : (⟨eqA :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hEv1 : ∀ ψ : Name → Nat, m1.cval eqName ψ = eqValT ψ := by
    intro ψ; rw [hm1]; rfl
  have hwf2 : EnvWF ⟨eqReflA :: eqA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?res2, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res2 =>
    show Expr.constsResolve _ eqReflA.toConstantVal.type = true
    have hf : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
        = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE1
    rw [show eqReflA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "α") (.sort (.param uNT))
            (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
              (.app (.app (.app (.const eqName [.param uNT]) (.bvar 1))
                (.bvar 0)) (.bvar 0)) { bi := .default })
            { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m2, hm2⟩ := extendEqReflTT m1 hE1 hEv1 h2 hwf2
  have hE2 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
      = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE1
  have hR2 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hEv2 : ∀ ψ : Name → Nat, m2.cval eqName ψ = eqValT ψ := by
    intro ψ
    rw [hm2, cvalSet_ne (by decide)]
    exact hEv1 ψ
  have hRv2 : ∀ ψ : Name → Nat, m2.cval eqReflName ψ = eqReflValT ψ := by
    intro ψ; rw [hm2]; rfl
  have hwf3 : EnvWF ⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ :=
    EnvWF.cons hwf2 ⟨rfl, rfl, ?res3, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec3,
      (fun _ _ heq => nomatch heq)⟩
  case res3 =>
    show Expr.constsResolve _ eqRecA.toConstantVal.type = true
    have hfE : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
        = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE2
    have hfR : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
        eqReflName = some eqReflA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hR2
    rw [show eqRecA.toConstantVal.type = Expr.forallE (Name.anonymous.str "α") (.sort (.param uNT))
          (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.app (.const eqName [.param uNT]) (.bvar 2))
                    (.bvar 1)) (.bvar 0))
                  (.sort (.param u1NT)) { bi := .default })
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "refl")
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uNT]) (.bvar 2))
                    (.bvar 1)))
                (Expr.forallE (Name.anonymous.str "b") (.bvar 3)
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.app (.const eqName [.param uNT]) (.bvar 4))
                      (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                    { bi := .default })
                  { bi := .implicit })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfE, hfR]
  case rec3 =>
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h4'
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
      · subst h1'; rfl
      · have hfE : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
            eqName = some eqA := by
          rw [Env.find?_cons, if_neg (by decide)]; exact hE2
        have hfR : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
            eqReflName = some eqReflA := by
          rw [Env.find?_cons, if_neg (by decide)]; exact hR2
        show Expr.constsResolve _ (RecRule.rhs eqRecRule) = true
        simp [Expr.constsResolve, eqRecRule, hfE, hfR]
    · exact nomatch hr'
  obtain ⟨m3, -⟩ := extendEqRecTT m2 hE2 hR2 hEv2 hRv2 h3 hwf3
  exact ⟨m3⟩


end Setlec.TTVerify

