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
    Nonempty (EnvTT ⟨ci :: env.consts⟩) := by
  have hag : ∀ n, n ≠ ci.name → m.cval n = cvalSet m.cval ci.name val n :=
    fun n hn => (cvalSet_ne hn).symm
  refine ⟨EnvTT.cons m (Installs.of_fresh hfresh hag) hwf ?_ ?_ ?_ ?_ ?_ ?_
    hheadCtors hheadRec ?_ ?_ hheadProj hheadProjPair hheadEq ?_ ?_ ?_ ?_⟩
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
    Nonempty (EnvTT ⟨emptyA :: env.consts⟩) := by
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
    Nonempty (EnvTT ⟨emptyRecA :: env.consts⟩) := by
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
  obtain ⟨m1⟩ := extendEmptyTT m h1 hwf1
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
  exact extendEmptyRecTT m1 hE h2 hwf2


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
    Nonempty (EnvTT ⟨punitA :: env.consts⟩) := by
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
    Nonempty (EnvTT ⟨punitUnitA :: env.consts⟩) := by
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
    Nonempty (EnvTT ⟨punitRecA :: env.consts⟩) := by
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
  obtain ⟨m1⟩ := extendPUnitTT m h1 hwf1
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
  obtain ⟨m2⟩ := extendPUnitUnitTT m1 hP1 h2 hwf2
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
  exact extendPUnitRecTT m2 hP2 hU2 h3 hwf3


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


/-- **`Eq`, installed** — and with it §11's law, discharged from the
tower rather than assumed. -/
theorem extendEqTT {env : Env} (m : EnvTT env)
    (hfresh : env.find? eqName = none)
    (hwf : EnvWF ⟨eqA :: env.consts⟩) :
    Nonempty (EnvTT ⟨eqA :: env.consts⟩) := by
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


end Setlec.TTVerify

