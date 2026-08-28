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
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨ci :: env.consts⟩ T caps →
      (T = ci.name ∨ caps.etaCtor = ci.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = ci.name) →
      EtaLawTT ⟨ci :: env.consts⟩ (cvalSet m.cval ci.name val) T cvT caps)
    (hheadUnit : ∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      UnitLawTT ⟨ci :: env.consts⟩ (cvalSet m.cval ci.name val) ci.name cv caps)
    (hheadResid : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps)
      (cvC : ConstantVal),
      (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains caps.etaCtor = false →
      (⟨ci :: env.consts⟩ : Env).find? caps.etaCtor =
        some (.ctorInfo cvC caps.etaParams caps.etaFields) →
      (T = ci.name ∨ caps.etaCtor = ci.name) →
      CtorResidualPin T cvT.levelParams cvC caps.etaParams
        caps.etaFields)
    (hpin : ConstantInfo.isBasis ci = true → ci = pinnedInfo ci.name)
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
    -- **not** `ci ≠ .axiomInfo cv`: `Quot.sound` is a stored axiom, and
    -- the only obligation an axiom carries is the reduce-op one, which
    -- it discharges by not being a reduce op.  Every non-axiom call site
    -- still passes `fun _ heq => nomatch heq`.
    (hnoax : ∀ cv, ci = .axiomInfo cv → ci.name ∈ reduceOpNames → False)
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
            (RecRule.fire rl = .plain →
              ∀ i, i < RecRule.ctorParams rl → i < mI →
                Deq Δ (ys.getD i default) (xs.getD i default)) →
            (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
              ∀ i, i < RecRule.ctorParams rl →
              ∀ vp : VExpr,
                denote (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ rP
                  (openRev 0 rP ((pins.getD i
                    default).instantiateLevelParams cv.levelParams us))
                  = some vp →
                Deq Δ (ys.getD i default)
                  (VExpr.instRevChain (xs.take rP) vp)) →
            IotaIndexPin Δ restC (RecRule.ctorParams rl) mI rP xs →
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
    ?_ ?_ ?_ ?_ ?_ ?_ hheadCtors hheadRec ?_ ?_ hheadResid hheadProj
    hheadProjPair hheadEq ?_ ?_ ?_ ?_, rfl⟩
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
  · exact hheadEta
  · exact hheadUnit
  · -- the pinned shape and valuation
    intro _
    exact ⟨hpin, fun ψ t hp => by rw [cvalSet_self]; exact hdirect ψ t hp⟩
  · exact fun cv v h heq => absurd heq (hnodefn cv v h)
  · exact fun cv v h heq => absurd heq (hnodefn cv v h)
  · exact fun cv heq hmem => absurd (hnoax cv heq hmem) not_false


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


/-! ### The reserved case, factored

Twenty of the twenty-two pinned constants have **reserved** names, and
for those the eta and unit-like head obligations are vacuous by
computation on that list.  The other two are the pinned pair's
projection functions, whose names are `Name.num` nodes and therefore
never reserved (`projFnName_ne_reserved`) — which is why
`extendBasisTT` takes the three head obligations as *parameters* rather
than assuming reservedness.  These two helpers supply them for the
twenty. -/

theorem basisEtaVacuous {env : Env} (m : EnvTT env) {ci : ConstantInfo}
    {val : (Name → Nat) → VExpr}
    (hres : reservedBasisNames.contains ci.name = true) :
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨ci :: env.consts⟩ T caps →
      (T = ci.name ∨ caps.etaCtor = ci.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = ci.name) →
      EtaLawTT ⟨ci :: env.consts⟩ (cvalSet m.cval ci.name val) T cvT caps := by
  intro T cvT caps hf hcape hresT hfam hpart
  rcases hpart with hT | hC | ⟨j, hj, hP⟩
  · rw [← hT] at hres; rw [hres] at hresT; exact nomatch hresT
  · have hf1 := hfam.1
    rw [hC, hres] at hf1
    exact nomatch hf1
  · exact absurd hP (projFnName_ne_reserved hres)

/-- The residual-pin head obligation is vacuous at a reserved name:
both disjuncts contradict the clause's own reservation guards. -/
theorem basisResidVacuous {env : Env} {ci : ConstantInfo}
    (hres : reservedBasisNames.contains ci.name = true) :
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps)
      (cvC : ConstantVal),
      (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains caps.etaCtor = false →
      (⟨ci :: env.consts⟩ : Env).find? caps.etaCtor =
        some (.ctorInfo cvC caps.etaParams caps.etaFields) →
      (T = ci.name ∨ caps.etaCtor = ci.name) →
      CtorResidualPin T cvT.levelParams cvC caps.etaParams
        caps.etaFields := by
  intro T cvT caps cvC _ _ hrT hrC _ hor
  rcases hor with hT | hC
  · rw [hT, hres] at hrT; exact nomatch hrT
  · rw [hC, hres] at hrC; exact nomatch hrC

theorem basisUnitVacuous {env : Env} (m : EnvTT env) {ci : ConstantInfo}
    {val : (Name → Nat) → VExpr}
    (hres : reservedBasisNames.contains ci.name = true) :
    ∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      UnitLawTT ⟨ci :: env.consts⟩ (cvalSet m.cval ci.name val) ci.name
        cv caps := by
  intro cv caps heq hunit hnres
  rw [hres] at hnres; exact nomatch hnres


/-- Projection-function names determine their parent. -/
theorem projFnName_inj {T T' : Name} {i j : Nat}
    (h : projFnName T i = projFnName T' j) : T = T' := by
  unfold projFnName at h
  injection h with h1 _
  injection h1

/-- The pinned pair's projection valuations: the layer's `proj` former
under the parameter binders (`psigmaFst_derivable`). -/
def pairProjValT (i : Nat) (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN))
    (.lam (.pi (.bvar 0) (.sort (ψ vN)))
      (.lam (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
          [.bvar 1, .bvar 0])
        (.proj i (.bvar 0))))

theorem pairProjValT_closed (i : Nat) (ψ : Name → Nat) :
    VExpr.Closed (pairProjValT i ψ) := by
  simp only [pairProjValT, VExpr.Closed, VExpr.bvarsBelow, VExpr.mkAppN]
  repeat' apply And.intro
  all_goals first | trivial | omega

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
  refine extendBasisTT m (val := fun _ => emptyT 1)
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide) ?_ hfresh hwf (fun _ => trivial) (fun _ _ _ => rfl) ?_
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
        (fun ψ => VExpr.const .emptyRec [1, ψ uN]) := by
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
        (fun ψ => VExpr.const .emptyRec [1, ψ uN]))
        ⟨emptyRecA :: env.consts⟩ φ d (.const emptyName []) = some (emptyT 1) := by
    intro d φ
    rw [denote_const, Env.find?_cons,
      if_neg (show ¬ (ConstantInfo.name emptyRecA = emptyName) by decide)]
    rw [hE]
    simp only [show emptyA.toConstantVal.levelParams = [] from rfl,
      List.length_nil, if_true, substFn_nil]
    rw [cvalSet_ne (show emptyName ≠ emptyRecA.name by decide), hEv]
  refine extendBasisTT m (val := fun ψ => .const .emptyRec [1, ψ uN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide) ?_ hfresh hwf (fun _ => trivial) ?_ ?_
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
        = some (VExpr.const .emptyRec [1, ψ uN]) := by
      simp only [pinnedDirectT]
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_true]
    rw [show ConstantInfo.name emptyRecA = emptyName.str "rec" from rfl,
      this] at hp
    exact (Option.some.inj hp)
  · intro φ₁ φ₂ hp
    have h1 : φ₁ uN = φ₂ uN := hp uN (by
      show uN ∈ [uN]
      exact List.mem_cons_self)
    rw [h1]
  · intro φ
    refine ⟨.pi (.pi (emptyT 1) (.sort (φ uN)))
      (.pi (emptyT 1) (.app (.bvar 1) (.bvar 0))), ?_, ?_⟩
    · rw [denoteClosed,
        show emptyRecA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
                (.sort (.param uN)) { bi := .default })
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
              (.sort (.param uN)) { bi := .default })
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
      m'.cval = cvalSet m.cval punitA.name (fun ψ => punitT (ψ uN)) := by
  refine extendBasisTT m (val := fun ψ => punitT (ψ uN)) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
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
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨.sort (φ uN), ?_, HasType.const⟩
    rw [denoteClosed, show punitA.toConstantVal.type = Expr.sort (.param uN)
      from rfl, denote_sort]
    rfl

/-- `PUnit.unit`, installed. -/
theorem extendPUnitUnitTT {env : Env} (m : EnvTT env)
    (hP : env.find? punitName = some punitA)
    (hfresh : env.find? punitUnitName = none)
    (hwf : EnvWF ⟨punitUnitA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨punitUnitA :: env.consts⟩,
      m'.cval = cvalSet m.cval punitUnitA.name
        (fun ψ => punitUnitT (ψ uN)) := by
  refine extendBasisTT m (val := fun ψ => punitUnitT (ψ uN)) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
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
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨punitT (φ uN), ?_, HasType.const⟩
    rw [denoteClosed, show punitUnitA.toConstantVal.type
      = Expr.const punitName [.param uN] from rfl]
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
        (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N]) := by
  have hPc : ∀ (d : Nat) (φ : Name → Nat) (l : Level),
      denote (cvalSet m.cval punitRecA.name
          (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N]))
        ⟨punitRecA :: env.consts⟩ φ d (.const punitName [l])
        = some (punitT (l.eval φ)) := by
    intro d φ l
    refine denote_const_pin m (by decide) hP rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  have hUc : ∀ (d : Nat) (φ : Name → Nat) (l : Level),
      denote (cvalSet m.cval punitRecA.name
          (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N]))
        ⟨punitRecA :: env.consts⟩ φ d (.const punitUnitName [l])
        = some (punitUnitT (l.eval φ)) := by
    intro d φ l
    refine denote_const_pin m (by decide) hU rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  refine extendBasisTT m
    (val := fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N]) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
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
    rw [hp uN (by
        show uN ∈ [u1N, uN]
        exact List.mem_cons_of_mem _ List.mem_cons_self),
      hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self)]
  · -- the pinned type, denoted
    intro φ
    refine ⟨_, ?_, HasType.const⟩
    rw [denoteClosed,
      show punitRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t")
              (.const punitName [.param uN]) (.sort (.param u1N))
              { bi := .default })
            (Expr.forallE (Name.anonymous.str "unit")
              (.app (.bvar 0) (.const punitUnitName [.param uN]))
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uN])
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
          hlev _ _ _ hTV hTVj hR hC
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
            (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N])
            ((Name.anonymous.str "PUnit").str "unit")
            (Level.substFn φ punitUnitA.toConstantVal.levelParams [l0])
            = punitUnitT (w2.eval φ) := by
          rw [cvalSet_ne (by decide), hlev]
          refine cval_pinned m (by decide) (by rw [hU']; rfl) _ ?_
          simp +decide [pinnedDirectT]
          rfl
        have hrecV : cvalSet m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N]) punitRecA.name
            (Level.substFn φ [Name.anonymous.str "u_1", Name.anonymous.str "u"]
              [w1, w2])
            = VExpr.const .punitRec [w2.eval φ, w1.eval φ] := by
          rw [cvalSet_self]
          simp [Level.substFn, uN, u1N]
        rw [show VExpr.mkAppN (cvalSet m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N])
            ((Name.anonymous.str "PUnit").str "unit")
            (Level.substFn φ punitUnitA.toConstantVal.levelParams [l0])) []
          = cvalSet m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N])
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
        = Expr.const punitName [.param uN] from rfl, Expr.constsResolve, hf]
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
              (.const punitName [.param uN]) (.sort (.param u1N))
              { bi := .default })
            (Expr.forallE (Name.anonymous.str "unit")
              (.app (.bvar 0) (.const punitUnitName [.param uN]))
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uN])
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
              (.const punitName [.param uN]) (.sort (.param u1N))
              { bi := .default })
            (Expr.lam (Name.anonymous.str "unit")
              (.app (.bvar 0) (.const punitUnitName [.param uN]))
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
  | _ :: xs, _, _, h => Deq.mkAppN_congrFun xs (Deq.appFun h)

/-- **The chain, collapsed.** -/
theorem Deq.ofBetaSpine {Γ : List VExpr} {f : VExpr} {args : List VExpr}
    {r : VExpr} (h : BetaSpine Γ f args r) :
    Deq Γ (VExpr.mkAppN f args) r := by
  induction h with
  | nil => exact Deq.refl
  | @cons A b x xs r hx _ ih =>
    exact Deq.trans (Deq.mkAppN_congrFun xs
      (Deq.intro (HasType.beta (T := x) hx))) ih


/-- A lifted telescope variable, recovered: `k` lifts and the `k`
instantiations that consume them cancel exactly.  Every fired spine
produces these chains, and nothing else stands between the computed
`inst` and the variable it started as. -/
theorem inst_chain1 (x e : VExpr) : (VExpr.liftN 1 x 0).inst e 0 = x := by
  rw [VExpr.inst_liftN_absorb x (Nat.zero_le _) (Nat.le_refl 0) e,
    VExpr.liftN_zero]

/-- The same absorptions stopping *short* of zero: a telescope entry
that still sits under binders keeps the residual lift.  Named at each
arity because `simp` matches numerals, not `m + 1`. -/
theorem inst_absorb21 (x e : VExpr) :
    (VExpr.liftN 2 x 0).inst e 1 = VExpr.liftN 1 x 0 :=
  VExpr.inst_liftN_absorb x (Nat.zero_le _) (by omega) e

theorem inst_absorb32 (x e : VExpr) :
    (VExpr.liftN 3 x 0).inst e 2 = VExpr.liftN 2 x 0 :=
  VExpr.inst_liftN_absorb x (Nat.zero_le _) (by omega) e

theorem inst_absorb43 (x e : VExpr) :
    (VExpr.liftN 4 x 0).inst e 3 = VExpr.liftN 3 x 0 :=
  VExpr.inst_liftN_absorb x (Nat.zero_le _) (by omega) e

theorem inst_absorb54 (x e : VExpr) :
    (VExpr.liftN 5 x 0).inst e 4 = VExpr.liftN 4 x 0 :=
  VExpr.inst_liftN_absorb x (Nat.zero_le _) (by omega) e

theorem inst_chain2 (x e1 e0 : VExpr) :
    ((VExpr.liftN 2 x 0).inst e1 1).inst e0 0 = x := by
  rw [VExpr.inst_liftN_absorb x (Nat.zero_le _) (by omega) e1, inst_chain1]

theorem inst_chain3 (x e2 e1 e0 : VExpr) :
    (((VExpr.liftN 3 x 0).inst e2 2).inst e1 1).inst e0 0 = x := by
  rw [VExpr.inst_liftN_absorb x (Nat.zero_le _) (by omega) e2, inst_chain2]

theorem inst_chain4 (x e3 e2 e1 e0 : VExpr) :
    ((((VExpr.liftN 4 x 0).inst e3 3).inst e2 2).inst e1 1).inst e0 0 = x := by
  rw [VExpr.inst_liftN_absorb x (Nat.zero_le _) (by omega) e3, inst_chain3]

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
  .lam (.sort (ψ uN)) (.lam (.bvar 0) (.lam (.bvar 1)
    (.eqE (.bvar 2) (.bvar 1) (.bvar 0))))

/-- `Eq.refl`'s valuation. -/
def eqReflValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) .prf)

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
    (hA : HasType Δ A (.sort (ψ uN))) (ha : HasType Δ a A)
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
    (hA : HasType Δ A (.sort (ψ uN))) (ha : HasType Δ a A)
    (hb : HasType Δ b A) :
    HasType Δ (VExpr.mkAppN (eqValT ψ) [A, a, b]) (.sort 0) := by
  have h0 : HasType Δ (eqValT ψ)
      (.pi (.sort (ψ uN)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) :=
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
    (hA : HasType Δ A (.sort (ψ uN))) (ha : HasType Δ a A) :
    HasType Δ (VExpr.mkAppN (eqReflValT ψ) [A, a])
      (VExpr.mkAppN (eqValT ψ) [A, a, a]) := by
  have hbody : HasType [VExpr.bvar 0, VExpr.sort (ψ uN)] VExpr.prf
      (VExpr.mkAppN (eqValT ψ) [.bvar 1, .bvar 0, .bvar 0]) := by
    have hα : HasType [VExpr.bvar 0, VExpr.sort (ψ uN)] (.bvar 1)
        (.sort (ψ uN)) := by
      have := HasType.bvar (Γ := [VExpr.bvar 0, VExpr.sort (ψ uN)])
        (i := 1) (A := .sort (ψ uN)) (by simp)
      simpa using this
    have ha' : HasType [VExpr.bvar 0, VExpr.sort (ψ uN)] (.bvar 0)
        (.bvar 1) := by
      have := HasType.bvar (Γ := [VExpr.bvar 0, VExpr.sort (ψ uN)])
        (i := 0) (A := VExpr.bvar 0) (by simp)
      simpa [VExpr.liftN] using this
    exact HasType.conv (HasType.refl (T := VExpr.bvar 1))
      ((eqValT_law hα ha' ha').symm.toHasType (VExpr.bvar 1))
  have h0 : HasType Δ (eqReflValT ψ)
      (.pi (.sort (ψ uN)) (.pi (.bvar 0)
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
  .lam (.sort (ψ uN))
    (.lam (.bvar 0)
      (.lam (.pi (.bvar 1)
          (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1N))))
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
     [.bvar 2, .bvar 1, .bvar 0]) (.sort (ψ u1N))),
   VExpr.bvar 0, VExpr.sort (ψ uN)]

/-- **`Eq.rec`'s typing** — the derivable-eliminator shape.  The body
has the motive at `a` and `Eq.refl`, where the motive at `b` and the
hypothesis is wanted; two `congrApp`s close the gap, over the equation
*read off the hypothesis* through the law and proof irrelevance. -/
theorem eqRecValT_typed (ψ : Name → Nat) :
    HasType [] (eqRecValT ψ)
      (.pi (.sort (ψ uN))
        (.pi (.bvar 0)
          (.pi (.pi (.bvar 1)
              (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
                (.sort (ψ u1N))))
            (.pi (.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]))
              (.pi (.bvar 3)
                (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
                  (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))) := by
  refine .lam (.lam (.lam (.lam (.lam (.lam ?_)))))
  show HasType (eqRecCtx ψ) (VExpr.bvar 2) _
  have hα : HasType (eqRecCtx ψ) (.bvar 5) (.sort (ψ uN)) := by
    have := HasType.bvar (Γ := eqRecCtx ψ) (i := 5) (A := .sort (ψ uN))
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
theorem eqValT_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqValT ψ₁ = eqValT ψ₂ := by rw [eqValT, eqValT, h]

theorem eqReflValT_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
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
              (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1, .bvar 0])
                (.sort (w1.eval φ))))
            (.pi (.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1]))
              (.pi (.bvar 3)
                (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                    [.bvar 4, .bvar 3, .bvar 0])
                  (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))) := by
  have hsu : Level.subst [u1N, uN] [w1, w2] (.param uN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, u1N]
  have hsu1 : Level.subst [u1N, uN] [w1, w2] (.param u1N) = w1 := by
    simp [Level.subst, Level.subst.go, u1N]
  have hEc : ∀ e : Nat,
      denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqName [w2]) = some (eqValT (Level.substFn φ [uN] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([w2] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hEv]
    rfl
  have hRc : ∀ e : Nat,
      denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqReflName [w2])
        = some (eqReflValT (Level.substFn φ [uN] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hR]
    simp only [show ([w2] : List Level).length
      = eqReflA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hRv]
    rfl
  rw [show eqRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.app (.const eqName [.param uN]) (.bvar 2))
                    (.bvar 1)) (.bvar 0))
                  (.sort (.param u1N)) { bi := .default })
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "refl")
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uN]) (.bvar 2))
                    (.bvar 1)))
                (Expr.forallE (Name.anonymous.str "b") (.bvar 3)
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.app (.const eqName [.param uN]) (.bvar 4))
                      (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                    { bi := .default })
                  { bi := .implicit })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show eqRecA.toConstantVal.levelParams = [u1N, uN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsu1, denote_forallE, denote_sort,
    denote_app, denote_fvar, hEc, hRc, VExpr.mkAppN]


/-- `Eq.rec`'s single stored rule. -/
def eqRecRule : RecRule :=
  { ctor := eqReflName, nfields := 0, ctorParams := 2, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "α") (.sort (.param uN))
      (Expr.lam (Name.anonymous.str "a") (.bvar 0)
        (Expr.lam (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
            (Expr.forallE (Name.anonymous.str "t")
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 2))
                (.bvar 1)) (.bvar 0))
              (.sort (.param u1N)) { bi := .default })
            { bi := .default })
          (Expr.lam (Name.anonymous.str "refl")
            (.app (.app (.bvar 0) (.bvar 1))
              (.app (.app (.const eqReflName [.param uN]) (.bvar 2))
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
              (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1, .bvar 0])
                (.sort (w1.eval φ))))
            (.lam (.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1]))
              (.bvar 0))))) := by
  have hsu : Level.subst [u1N, uN] [w1, w2] (.param uN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, u1N]
  have hsu1 : Level.subst [u1N, uN] [w1, w2] (.param u1N) = w1 := by
    simp [Level.subst, Level.subst.go, u1N]
  have hEc : ∀ e : Nat,
      denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqName [w2]) = some (eqValT (Level.substFn φ [uN] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([w2] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hEv]
    rfl
  have hRc : ∀ e : Nat,
      denote (cvalSet m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqReflName [w2])
        = some (eqReflValT (Level.substFn φ [uN] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hR]
    simp only [show ([w2] : List Level).length
      = eqReflA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hRv]
    rfl
  rw [show eqRecA.toConstantVal.levelParams = [u1N, uN] from rfl]
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
  refine extendBasisTT m (val := eqValT) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
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
      hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨.pi (.sort (φ uN)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0))), ?_,
      ?_⟩
    · rw [denoteClosed,
        show eqA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
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
        ⟨eqReflA :: env.consts⟩ φ d (.const eqName [.param uN])
        = some (eqValT φ) := by
    intro d φ
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([Level.param uN] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide),
      show Level.substFn φ eqA.toConstantVal.levelParams [Level.param uN]
        = φ from substFn_param_self φ [uN], hEv]
  refine extendBasisTT m (val := eqReflValT) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
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
      hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨.pi (.sort (φ uN)) (.pi (.bvar 0)
      (VExpr.mkAppN (eqValT φ) [.bvar 1, .bvar 0, .bvar 0])), ?_, ?_⟩
    · rw [denoteClosed,
        show eqReflA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
              (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
                (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.bvar 0)) { bi := .default })
              { bi := .implicit } from rfl]
      simp [denote_forallE, denote_sort, denote_app, denote_fvar, Level.eval,
        hEc, VExpr.mkAppN]
    · refine .lam (.lam ?_)
      have hα : HasType [VExpr.bvar 0, VExpr.sort (φ uN)] (.bvar 1)
          (.sort (φ uN)) := by
        have := HasType.bvar (Γ := [VExpr.bvar 0, VExpr.sort (φ uN)])
          (i := 1) (A := .sort (φ uN)) (by simp)
        simpa using this
      have ha : HasType [VExpr.bvar 0, VExpr.sort (φ uN)] (.bvar 0)
          (.bvar 1) := by
        have := HasType.bvar (Γ := [VExpr.bvar 0, VExpr.sort (φ uN)])
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
  refine extendBasisTT m (val := eqRecValT) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
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
    have hu : φ₁ uN = φ₂ uN := hp uN (by
      show uN ∈ [u1N, uN]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [eqRecValT, eqRecValT, hu,
      hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self),
      eqValT_congr hu, eqReflValT_congr hu]
  · -- the pinned type, denoted
    intro φ
    refine ⟨_, ?_, HasType.weakenNil (eqRecValT_typed φ) []⟩
    rw [denoteClosed, ← Expr.instantiateLevelParams_self
        eqRecA.toConstantVal.levelParams eqRecA.toConstantVal.type,
      show eqRecA.toConstantVal.levelParams.map Level.param
        = [Level.param u1N, Level.param uN] from rfl,
      denote_eqRec_type m φ 0 (.param u1N) (.param uN) hE hR hEv hRv,
      show Level.substFn φ [uN] [Level.param uN] = φ from
        substFn_param_self φ [uN]]
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
        _ _ _ hdTV hdTVj hfitR hfitC
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
          = eqReflValT (Level.substFn φ [uN] [w2]) := by
        have hRv' := hRv
        simp only [eqReflName, eqName] at hRv'
        rw [cvalSet_ne (by decide), hRv']
        refine eqReflValT_congr ?_
        have := congrFun hlev uN
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
                (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                    [.bvar 2, .bvar 1, .bvar 0])
                  (.sort (w1.eval φ))))
              (.lam (.app (.app (.bvar 0) (.bvar 1))
                  (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                    [.bvar 2, .bvar 1]))
                (.bvar 0)))))
        (.cons t1 (.cons t2 (.cons t3 (.cons t4 .nil))))).symm
      show Deq Δ (((VExpr.liftN 2 xh 0).inst xb 1).inst
          (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2])) [q1, q2]) 0)
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
        = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
            (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
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
    rw [show eqRecA.toConstantVal.type = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.app (.const eqName [.param uN]) (.bvar 2))
                    (.bvar 1)) (.bvar 0))
                  (.sort (.param u1N)) { bi := .default })
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "refl")
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uN]) (.bvar 2))
                    (.bvar 1)))
                (Expr.forallE (Name.anonymous.str "b") (.bvar 3)
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.app (.const eqName [.param uN]) (.bvar 4))
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


/-! ## `Nat`

Four constants, and the level question does not arise: `Nat.zero` and
`Nat.succ` bind **no** level parameters, so a fired rule's `usj` is
forced to `[]` (§14.4).  Everything here is pinned, so no tower is
needed and each valuation is read back through `BasisPinnedTT`. -/

/-- `Nat`, installed. -/
theorem extendNatTT {env : Env} (m : EnvTT env)
    (hfresh : env.find? natName = none)
    (hwf : EnvWF ⟨natA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨natA :: env.consts⟩,
      m'.cval = cvalSet m.cval natA.name (fun _ => natT) := by
  refine extendBasisTT m (val := fun _ => natT) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name natA = natName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) (fun _ _ _ => rfl) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ
    refine ⟨.sort 1, ?_, HasType.const⟩
    rw [denoteClosed, show natA.toConstantVal.type = Expr.sort (.succ .zero)
      from rfl, denote_sort]
    rfl

/-- `Nat.zero`, installed. -/
theorem extendNatZeroTT {env : Env} (m : EnvTT env)
    (hN : env.find? natName = some natA)
    (hfresh : env.find? natZeroName = none)
    (hwf : EnvWF ⟨natZeroA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨natZeroA :: env.consts⟩,
      m'.cval = cvalSet m.cval natZeroA.name (fun _ => natZeroT) := by
  refine extendBasisTT m (val := fun _ => natZeroT) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name natZeroA = natZeroName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) (fun _ _ _ => rfl) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ
    refine ⟨natT, ?_, HasType.const⟩
    rw [denoteClosed, show natZeroA.toConstantVal.type
      = Expr.const natName [] from rfl]
    refine denote_const_pin m (by decide) hN rfl (by decide) ?_ 0
    simp +decide [pinnedDirectT]
    rfl

/-- `Nat.succ`, installed. -/
theorem extendNatSuccTT {env : Env} (m : EnvTT env)
    (hN : env.find? natName = some natA)
    (hfresh : env.find? natSuccName = none)
    (hwf : EnvWF ⟨natSuccA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨natSuccA :: env.consts⟩,
      m'.cval = cvalSet m.cval natSuccA.name (fun _ => VExpr.const .natSucc []) := by
  have hNc : ∀ d : Nat, ∀ φ : Name → Nat,
      denote (cvalSet m.cval natSuccA.name (fun _ => VExpr.const .natSucc []))
        ⟨natSuccA :: env.consts⟩ φ d (.const natName []) = some natT := by
    intro d φ
    refine denote_const_pin m (by decide) hN rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  refine extendBasisTT m (val := fun _ => VExpr.const .natSucc []) (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name natSuccA = natSuccName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) (fun _ _ _ => rfl) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ
    refine ⟨.pi natT natT, ?_, HasType.const⟩
    rw [denoteClosed, show natSuccA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "n") (.const natName [])
          (.const natName []) { bi := .default } from rfl]
    simp [denote_forallE, Expr.instantiate1, hNc]


/-- The `Nat` block's earlier constants, denoted in the environment
`Nat.rec` is going into. -/
theorem denote_natRec_consts {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    (∀ d : Nat, denote (cvalSet m.cval natRecA.name val)
        ⟨natRecA :: env.consts⟩ φ d (.const natName []) = some natT) ∧
    (∀ d : Nat, denote (cvalSet m.cval natRecA.name val)
        ⟨natRecA :: env.consts⟩ φ d (.const natZeroName [])
        = some natZeroT) ∧
    (∀ d : Nat, denote (cvalSet m.cval natRecA.name val)
        ⟨natRecA :: env.consts⟩ φ d (.const natSuccName [])
        = some (VExpr.const .natSucc [])) := by
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_⟩
  · refine denote_const_pin m (by decide) hN rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  · refine denote_const_pin m (by decide) hZ rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  · refine denote_const_pin m (by decide) hS rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]

/-- **`Nat.rec`'s pinned type, denoted at any depth and any level.** -/
theorem denote_natRec_type {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (cvalSet m.cval natRecA.name val) ⟨natRecA :: env.consts⟩ φ d
        (natRecA.toConstantVal.type.instantiateLevelParams
          natRecA.toConstantVal.levelParams [w])
      = some (.pi (.pi natT (.sort (w.eval φ)))
        (.pi (.app (.bvar 0) natZeroT)
          (.pi (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (VExpr.const .natSucc []) (.bvar 1)))))
            (.pi natT (.app (.bvar 3) (.bvar 0)))))) := by
  obtain ⟨hNc, hZc, hSc⟩ := denote_natRec_consts m (val := val) φ hN hZ hS
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go]
  rw [show natRecA.toConstantVal.levelParams = [uN] from rfl,
    show natRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "t") (.const natName [])
            (.sort (.param uN)) { bi := .default })
          (Expr.forallE (Name.anonymous.str "zero")
            (.app (.bvar 0) (.const natZeroName []))
            (Expr.forallE (Name.anonymous.str "succ")
              (Expr.forallE (Name.anonymous.str "n") (.const natName [])
                (Expr.forallE (Name.anonymous.str "n_ih")
                  (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (.const natSuccName []) (.bvar 1)))
                  { bi := .default })
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "t") (.const natName [])
                (.app (.bvar 3) (.bvar 0)) { bi := .default })
              { bi := .default })
            { bi := .default })
          { bi := .implicit } from rfl]
  simp [Expr.instantiateLevelParams, hsu, denote_forallE, denote_sort,
    denote_app, denote_fvar, hNc, hZc, hSc]


/-- `Nat.rec`'s two stored rules. -/
def natRecZeroRule : RecRule :=
  { ctor := natZeroName, nfields := 0, ctorParams := 0, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "motive")
      (Expr.forallE (Name.anonymous.str "t") (.const natName [])
        (.sort (.param uN)) { bi := .default })
      (Expr.lam (Name.anonymous.str "zero")
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam (Name.anonymous.str "succ")
          (Expr.forallE (Name.anonymous.str "n") (.const natName [])
            (Expr.forallE (Name.anonymous.str "n_ih") (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { bi := .default })
            { bi := .default })
          (.bvar 1) { bi := .default })
        { bi := .default })
      { bi := .default } }

def natRecSuccRule : RecRule :=
  { ctor := natSuccName, nfields := 1, ctorParams := 0, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "motive")
      (Expr.forallE (Name.anonymous.str "t") (.const natName [])
        (.sort (.param uN)) { bi := .default })
      (Expr.lam (Name.anonymous.str "zero")
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam (Name.anonymous.str "succ")
          (Expr.forallE (Name.anonymous.str "n") (.const natName [])
            (Expr.forallE (Name.anonymous.str "n_ih") (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { bi := .default })
            { bi := .default })
          (Expr.lam (Name.anonymous.str "n") (.const natName [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app (.const (natName.str "rec")
                [.param uN]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)))
            { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .default } }

theorem natRecA_eq :
    natRecA = .recInfo natRecA.toConstantVal 3 3
      [natRecZeroRule, natRecSuccRule] := rfl

/-- The `zero` rule's right-hand side, denoted. -/
theorem denote_natRec_zeroRhs {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (cvalSet m.cval natRecA.name val) ⟨natRecA :: env.consts⟩ φ d
        ((RecRule.rhs natRecZeroRule).instantiateLevelParams
          natRecA.toConstantVal.levelParams [w])
      = some (.lam (.pi natT (.sort (w.eval φ)))
        (.lam (.app (.bvar 0) natZeroT)
          (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (VExpr.const .natSucc []) (.bvar 1)))))
            (.bvar 1)))) := by
  obtain ⟨hNc, hZc, hSc⟩ := denote_natRec_consts m (val := val) φ hN hZ hS
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go]
  rw [show natRecA.toConstantVal.levelParams = [uN] from rfl]
  simp only [natRecZeroRule]
  simp [Expr.instantiateLevelParams, hsu, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hNc, hZc, hSc]


/-- **The `succ` rule's right-hand side, denoted** — the first stored
rule in any block whose right-hand side mentions the recursor being
installed.  It resolves to `cval'`, the post-install valuation, which
`hheadRec` has always been stated at. -/
theorem denote_natRec_succRhs {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (cvalSet m.cval natRecA.name val) ⟨natRecA :: env.consts⟩ φ d
        ((RecRule.rhs natRecSuccRule).instantiateLevelParams
          natRecA.toConstantVal.levelParams [w])
      = some (.lam (.pi natT (.sort (w.eval φ)))
        (.lam (.app (.bvar 0) natZeroT)
          (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (VExpr.const .natSucc []) (.bvar 1)))))
            (.lam natT
              (.app (.app (.bvar 1) (.bvar 0))
                (VExpr.mkAppN (val (Level.substFn φ [uN] [w]))
                  [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))))) := by
  obtain ⟨hNc, hZc, hSc⟩ := denote_natRec_consts m (val := val) φ hN hZ hS
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go]
  have hRc : ∀ e : Nat,
      denote (cvalSet m.cval natRecA.name val) ⟨natRecA :: env.consts⟩ φ e
        (.const (natName.str "rec") [w])
        = some (val (Level.substFn φ [uN] [w])) := by
    intro e
    rw [denote_const, Env.find?_cons,
      if_pos (show ConstantInfo.name natRecA = natName.str "rec" from rfl)]
    simp only [show ([w] : List Level).length
      = natRecA.toConstantVal.levelParams.length from rfl, if_true]
    rw [show cvalSet m.cval natRecA.name val (natName.str "rec") = val from
      cvalSet_self (n := natRecA.name)]
    rfl
  rw [show natRecA.toConstantVal.levelParams = [uN] from rfl]
  simp only [natRecSuccRule]
  simp [Expr.instantiateLevelParams, hsu, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hNc, hZc, hSc, hRc,
    VExpr.mkAppN]


/-- **`Nat.rec`, installed.**  Two rules, and the `succ` one is the
first obligation in any block whose constructor spine has a *field* —
so it is where `VTeleTyped`'s `cons` must hand `BetaSpine`'s `cons`
something the recursor's own telescope does not supply. -/
theorem extendNatRecTT {env : Env} (m : EnvTT env)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hfresh : env.find? (natName.str "rec") = none)
    (hwf : EnvWF ⟨natRecA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨natRecA :: env.consts⟩,
      m'.cval = cvalSet m.cval natRecA.name
        (fun ψ => VExpr.const .natRec [ψ uN]) := by
  refine extendBasisTT m (val := fun ψ => VExpr.const .natRec [ψ uN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name natRecA = natName.str "rec" from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, HasType.const⟩
    rw [denoteClosed, ← Expr.instantiateLevelParams_self
        natRecA.toConstantVal.levelParams natRecA.toConstantVal.type,
      show natRecA.toConstantVal.levelParams.map Level.param
        = [Level.param uN] from rfl,
      denote_natRec_type m (val := fun ψ => VExpr.const .natRec [ψ uN])
        φ 0 (.param uN) hN hZ hS]
    rfl
  · -- both rules' constructors are stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨natZeroA.toConstantVal, 0, 0, hZ⟩
    · rcases List.mem_cons.mp hr' with rfl | hr''
      · exact ⟨natSuccA.toConstantVal, 0, 1, hS⟩
      · exact nomatch hr''
  · -- the two iota rules
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h1'; subst h2'; subst h3'; subst h4'
    intro rl hrl _
    refine ⟨by omega, ?_⟩
    intro φ d us hus
    obtain ⟨w, rfl⟩ : ∃ a, us = [a] := by
      match us, hus with
      | [a], _ => exact ⟨a, rfl⟩
    rcases List.mem_cons.mp hrl with rfl | hr'
    · -- `Nat.rec … Nat.zero ↦ zero`
      refine ⟨_, denote_natRec_zeroRhs m
        (val := fun ψ => VExpr.const .natRec [ψ uN]) φ d w hN hZ hS, ?_⟩
      intro cvj cnP cnF hfj Δ usj xs ys TV TVj restR restC hxs hys husj hlev
        _ _ _ hdTV hdTVj hfitR hfitC
      have hZu := hZ
      simp only [natZeroName, natName] at hZu
      rw [Env.find?_cons, if_neg (by decide), hZu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = natZeroA.toConstantVal ∧ cnP = 0 ∧ cnF = 0 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
      obtain ⟨xM, xz, xs', rfl⟩ : ∃ a b c, xs = [a, b, c] := by
        match xs, hxs with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      obtain rfl : TV = _ :=
        (Option.some.inj ((denote_natRec_type m
          (val := fun ψ => VExpr.const .natRec [ψ uN]) φ d w hN hZ
          hS).symm.trans hdTV)).symm
      have hctor : cvalSet m.cval natRecA.name
          (fun ψ => VExpr.const .natRec [ψ uN])
          ((Name.anonymous.str "Nat").str "zero")
          (Level.substFn φ natZeroA.toConstantVal.levelParams usj)
          = natZeroT := by
        rw [cvalSet_ne (by decide)]
        exact cval_pinned m (by decide) (by rw [hZu]; rfl) _
          (by simp +decide [pinnedDirectT]; rfl)
      rw [hctor] at hfitR
      rw [cvalSet_self, hctor]
      cases hfitR with | cons t1 hfitR =>
      cases hfitR with | cons t2 hfitR =>
      cases hfitR with | cons t3 hfitR =>
      cases hfitR with | cons t4 hfitR =>
      have hbeta : Deq Δ (VExpr.mkAppN
          (VExpr.lam (.pi natT (.sort (w.eval φ)))
            (.lam (.app (.bvar 0) natZeroT)
              (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (VExpr.const .natSucc []) (.bvar 1)))))
                (.bvar 1)))) [xM, xz, xs']) xz := by
        have h := Deq.ofBetaSpine (Γ := Δ)
          (f := VExpr.lam (.pi natT (.sort (w.eval φ)))
            (.lam (.app (.bvar 0) natZeroT)
              (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (VExpr.const .natSucc []) (.bvar 1)))))
                (.bvar 1))))
          (.cons t1 (.cons t2 (.cons t3 .nil)))
        rw [show ((VExpr.bvar 1).inst xM 2).inst xz 1 = VExpr.liftN 1 xz 0
            from rfl] at h
        rw [VExpr.inst_liftN_absorb xz (Nat.zero_le _) (Nat.le_refl 0) xs',
          VExpr.liftN_zero] at h
        exact h
      refine Deq.trans (Deq.intro (HasType.natRecZero (T := xz) t1 ?_ ?_))
        hbeta.symm
      · simpa [VExpr.liftN_zero] using t2
      · rw [natStepT]
        simp only [VExpr.inst, Nat.zero_add, Nat.reduceAdd] at t3
        rw [if_neg (show ¬ ((2:Nat) < 2) by omega),
          if_pos (show (0:Nat) < 2 by omega),
          if_neg (show ¬ ((3:Nat) < 3) by omega), if_true, if_true] at t3
        rw [VExpr.inst_liftN_absorb xM (Nat.zero_le _) (Nat.le_refl 1) xz,
          VExpr.inst_liftN_absorb xM (Nat.zero_le _)
            (show (2:Nat) ≤ 0 + 2 by omega) xz] at t3
        exact t3
    · rcases List.mem_cons.mp hr' with rfl | hr''
      · -- `Nat.rec … (Nat.succ n) ↦ succ n (Nat.rec … n)`
        refine ⟨_, denote_natRec_succRhs m
          (val := fun ψ => VExpr.const .natRec [ψ uN]) φ d w hN hZ hS, ?_⟩
        intro cvj cnP cnF hfj Δ usj xs ys TV TVj restR restC hxs hys husj
          hlev _ _ _ hdTV hdTVj hfitR hfitC
        have hSu := hS
        simp only [natSuccName, natName] at hSu
        rw [Env.find?_cons, if_neg (by decide), hSu] at hfj
        obtain ⟨rfl, rfl, rfl⟩ :
            cvj = natSuccA.toConstantVal ∧ cnP = 0 ∧ cnF = 1 := by
          injection Option.some.inj hfj with a1 a2 a3
          exact ⟨a1.symm, a2.symm, a3.symm⟩
        obtain ⟨xn, rfl⟩ : ∃ a, ys = [a] := by
          match ys, hys with
          | [a], _ => exact ⟨a, rfl⟩
        obtain ⟨xM, xz, xs', rfl⟩ : ∃ a b c, xs = [a, b, c] := by
          match xs, hxs with
          | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
        obtain rfl : TV = _ :=
          (Option.some.inj ((denote_natRec_type m
            (val := fun ψ => VExpr.const .natRec [ψ uN]) φ d w hN hZ
            hS).symm.trans hdTV)).symm
        have hctor : cvalSet m.cval natRecA.name
            (fun ψ => VExpr.const .natRec [ψ uN])
            ((Name.anonymous.str "Nat").str "succ")
            (Level.substFn φ natSuccA.toConstantVal.levelParams usj)
            = VExpr.const .natSucc [] := by
          rw [cvalSet_ne (by decide)]
          exact cval_pinned m (by decide) (by rw [hSu]; rfl) _
            (by simp +decide [pinnedDirectT])
        -- the field's typing, from the *constructor's* telescope
        obtain ⟨hNc, hZc, hSc⟩ := denote_natRec_consts m
          (val := fun ψ => VExpr.const .natRec [ψ uN]) φ hN hZ hS
        obtain rfl : TVj = VExpr.pi natT natT := by
          rw [show natSuccA.toConstantVal.type.instantiateLevelParams
              natSuccA.toConstantVal.levelParams usj
              = Expr.forallE (Name.anonymous.str "n") (.const natName [])
                (.const natName []) { bi := .default } from rfl] at hdTVj
          simp [denote_forallE, Expr.instantiate1, hNc] at hdTVj
          exact hdTVj.symm
        rw [hctor] at hfitR
        rw [cvalSet_self, hctor]
        cases hfitR with | cons t1 hfitR =>
        cases hfitR with | cons t2 hfitR =>
        cases hfitR with | cons t3 hfitR =>
        cases hfitR with | cons t4 hfitR =>
        cases hfitC with | cons tn hfitC =>
        have hz : HasType Δ xz (.app xM natZeroT) := by
          simpa [VExpr.liftN_zero] using t2
        have hs : HasType Δ xs' (natStepT xM) := by
          rw [natStepT]
          simp only [VExpr.inst, Nat.zero_add, Nat.reduceAdd] at t3
          rw [if_neg (show ¬ ((2:Nat) < 2) by omega),
            if_pos (show (0:Nat) < 2 by omega),
            if_neg (show ¬ ((3:Nat) < 3) by omega), if_true, if_true] at t3
          rw [VExpr.inst_liftN_absorb xM (Nat.zero_le _) (Nat.le_refl 1) xz,
            VExpr.inst_liftN_absorb xM (Nat.zero_le _)
              (show (2:Nat) ≤ 0 + 2 by omega) xz] at t3
          exact t3
        have hn : HasType Δ xn natT := by simpa [VExpr.liftN_zero] using tn
        refine Deq.trans
          (Deq.intro (HasType.natRecSucc (T := xz) t1 hz hs hn)) ?_
        have hb := (Deq.ofBetaSpine (Γ := Δ)
          (f := VExpr.lam (.pi natT (.sort (w.eval φ)))
            (.lam (.app (.bvar 0) natZeroT)
              (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (VExpr.const .natSucc []) (.bvar 1)))))
                (.lam natT
                  (.app (.app (.bvar 1) (.bvar 0))
                    (VExpr.mkAppN (VExpr.const .natRec
                        [Level.substFn φ [uN] [w] uN])
                      [.bvar 3, .bvar 2, .bvar 1, .bvar 0]))))))
          (.cons t1 (.cons t2 (.cons t3 (.cons tn .nil)))))
        have a1 : (VExpr.liftN 3 xM 0).inst xz 2 = VExpr.liftN 2 xM 0 :=
          VExpr.inst_liftN_absorb (m := 2) xM (Nat.zero_le _) (by omega) xz
        have a2 : (VExpr.liftN 2 xM 0).inst xs' 1 = VExpr.liftN 1 xM 0 :=
          VExpr.inst_liftN_absorb (m := 1) xM (Nat.zero_le _) (by omega) xs'
        have a3 : (VExpr.liftN 1 xM 0).inst xn 0 = xM := by
          rw [VExpr.inst_liftN_absorb (m := 0) xM (Nat.zero_le _) (by omega)
            xn, VExpr.liftN_zero]
        have b1 : (VExpr.liftN 2 xz 0).inst xs' 1 = VExpr.liftN 1 xz 0 :=
          VExpr.inst_liftN_absorb (m := 1) xz (Nat.zero_le _) (by omega) xs'
        have b2 : (VExpr.liftN 1 xz 0).inst xn 0 = xz := by
          rw [VExpr.inst_liftN_absorb (m := 0) xz (Nat.zero_le _) (by omega)
            xn, VExpr.liftN_zero]
        have c1 : (VExpr.liftN 1 xs' 0).inst xn 0 = xs' := by
          rw [VExpr.inst_liftN_absorb (m := 0) xs' (Nat.zero_le _) (by omega)
            xn, VExpr.liftN_zero]
        have d1 : VExpr.liftN 0 xn 0 = xn := VExpr.liftN_zero xn 0
        simp +decide only [VExpr.mkAppN, VExpr.inst, Nat.zero_add,
          Nat.reduceAdd, if_true, if_false, a1, a2, a3, b1, b2, c1,
          d1] at hb
        exact hb.symm
      · exact nomatch hr''


/-- **The `Nat` block, installed.** -/
theorem declBasisTT_natK {env env₁ : Env} (m : EnvTT env)
    (h : BasisChain env BasisKind.natK.declsA env₁) :
    Nonempty (EnvTT env₁) := by
  rw [show BasisKind.natK.declsA = [natA, natZeroA, natSuccA, natRecA]
    from rfl] at h
  cases h with
  | cons h1 h =>
  cases h with
  | cons h2 h =>
  cases h with
  | cons h3 h =>
  cases h with
  | cons h4 h =>
  cases h with
  | nil =>
  have hwf1 : EnvWF ⟨natA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, -⟩ := extendNatTT m h1 hwf1
  have hN1 : (⟨natA :: env.consts⟩ : Env).find? natName = some natA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf2 : EnvWF ⟨natZeroA :: natA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?res2, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res2 =>
    show Expr.constsResolve _ natZeroA.toConstantVal.type = true
    have hf : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natName
        = some natA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hN1
    rw [show natZeroA.toConstantVal.type = Expr.const natName [] from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m2, -⟩ := extendNatZeroTT m1 hN1 h2 hwf2
  have hN2 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natName
      = some natA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hN1
  have hZ2 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natZeroName
      = some natZeroA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf3 : EnvWF ⟨natSuccA :: natZeroA :: natA :: env.consts⟩ :=
    EnvWF.cons hwf2 ⟨rfl, rfl, ?res3, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res3 =>
    show Expr.constsResolve _ natSuccA.toConstantVal.type = true
    have hf : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
        natName = some natA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hN2
    rw [show natSuccA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "n") (.const natName [])
        (.const natName []) { bi := .default } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m3, -⟩ := extendNatSuccTT m2 hN2 h3 hwf3
  have hN3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      natName = some natA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hN2
  have hZ3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      natZeroName = some natZeroA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hZ2
  have hS3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      natSuccName = some natSuccA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf4 : EnvWF ⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ :=
    EnvWF.cons hwf3 ⟨rfl, rfl, ?res4, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec4,
      (fun _ _ heq => nomatch heq)⟩
  case res4 =>
    show Expr.constsResolve _ natRecA.toConstantVal.type = true
    have hfN : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ :
        Env).find? natName = some natA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hN3
    have hfZ : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ :
        Env).find? natZeroName = some natZeroA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hZ3
    have hfS : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ :
        Env).find? natSuccName = some natSuccA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hS3
    rw [show natRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t") (.const natName [])
              (.sort (.param uN)) { bi := .default })
            (Expr.forallE (Name.anonymous.str "zero")
              (.app (.bvar 0) (.const natZeroName []))
              (Expr.forallE (Name.anonymous.str "succ")
                (Expr.forallE (Name.anonymous.str "n") (.const natName [])
                  (Expr.forallE (Name.anonymous.str "n_ih")
                    (.app (.bvar 2) (.bvar 0))
                    (.app (.bvar 3)
                      (.app (.const natSuccName []) (.bvar 1)))
                    { bi := .default })
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "t") (.const natName [])
                  (.app (.bvar 3) (.bvar 0)) { bi := .default })
                { bi := .default })
              { bi := .default })
            { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfN, hfZ, hfS]
  case rec4 =>
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h4'
    have hfN : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ :
        Env).find? natName = some natA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hN3
    have hfZ : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ :
        Env).find? natZeroName = some natZeroA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hZ3
    have hfS : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ :
        Env).find? natSuccName = some natSuccA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hS3
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
      · subst h1'; rfl
      · show Expr.constsResolve _ (RecRule.rhs natRecZeroRule) = true
        simp [Expr.constsResolve, natRecZeroRule, hfN, hfZ, hfS]
    · rcases List.mem_cons.mp hr' with rfl | hr''
      · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
        · subst h1'; rfl
        · show Expr.constsResolve _ (RecRule.rhs natRecSuccRule) = true
          have hfR : (⟨natRecA :: natSuccA :: natZeroA :: natA ::
              env.consts⟩ : Env).find? (natName.str "rec")
              = some natRecA := by
            rw [Env.find?_cons]; exact if_pos rfl
          simp [Expr.constsResolve, natRecSuccRule, hfN, hfZ, hfS, hfR]
      · exact nomatch hr''
  obtain ⟨m4, -⟩ := extendNatRecTT m3 hN3 hZ3 hS3 h4 hwf4
  exact ⟨m4⟩


/-! ## `PSigma'`

Five constants: the type and its constructor (pinned), the recursor
(the fourth of the layer's *derived* four), and two `projInfo`
entries — the only block that installs any. -/

/-- `PSigma'`, installed. -/
theorem extendPSigmaTT {env : Env} (m : EnvTT env)
    (hfresh : env.find? psigmaName = none)
    (hwf : EnvWF ⟨psigmaA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨psigmaA :: env.consts⟩,
      m'.cval = cvalSet m.cval psigmaA.name
        (fun ψ => VExpr.const .psigma [ψ uN, ψ vN]) := by
  refine extendBasisTT m (val := fun ψ => VExpr.const .psigma [ψ uN, ψ vN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name psigmaA = psigmaName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, HasType.const⟩
    rw [denoteClosed, show psigmaA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "β")
            (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
              (.sort (.param vN)) { bi := .default })
            (.sort (.max (.param uN) (.param vN))) { bi := .default })
          { bi := .implicit } from rfl]
    simp [denote_forallE, denote_sort, denote_fvar, Level.eval]
    rfl

/-- `PSigma'.mk`, installed. -/
theorem extendPSigmaMkTT {env : Env} (m : EnvTT env)
    (hP : env.find? psigmaName = some psigmaA)
    (hfresh : env.find? psigmaMkName = none)
    (hwf : EnvWF ⟨psigmaMkA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨psigmaMkA :: env.consts⟩,
      m'.cval = cvalSet m.cval psigmaMkA.name
        (fun ψ => VExpr.const .psigmaMk [ψ uN, ψ vN]) := by
  have hPc : ∀ (d : Nat) (φ : Name → Nat),
      denote (cvalSet m.cval psigmaMkA.name
        (fun ψ => VExpr.const .psigmaMk [ψ uN, ψ vN]))
        ⟨psigmaMkA :: env.consts⟩ φ d
        (.const psigmaName [.param uN, .param vN])
        = some (VExpr.const .psigma [φ uN, φ vN]) := by
    intro d φ
    refine denote_const_pin m (by decide) hP rfl (by decide) ?_ d
    rw [show Level.substFn φ psigmaA.toConstantVal.levelParams
        [Level.param uN, Level.param vN] = φ from
      substFn_param_self φ [uN, vN]]
    simp +decide [pinnedDirectT]
  refine extendBasisTT m
    (val := fun ψ => VExpr.const .psigmaMk [ψ uN, ψ vN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name psigmaMkA = psigmaMkName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, HasType.const⟩
    rw [denoteClosed, show psigmaMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "β")
            (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
              (.sort (.param vN)) { bi := .default })
            (Expr.forallE (Name.anonymous.str "fst") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "snd")
                (.app (.bvar 1) (.bvar 0))
                (.app (.app (.const psigmaName
                    [.param uN, .param vN]) (.bvar 3)) (.bvar 2))
                { bi := .default })
              { bi := .default })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [denote_forallE, denote_sort, denote_app, denote_fvar, Level.eval,
      hPc]
    rfl


/-- The projections' towers are typed by the layer's own projection
rules — `projFst` and `projSnd`, at the three binders the pinned type
declares. -/
theorem pairProjValT_typed (φ : Name → Nat) :
    HasType [] (pairProjValT 0 φ)
      (.pi (.sort (φ uN))
        (.pi (.pi (.bvar 0) (.sort (φ vN)))
          (.pi (VExpr.mkAppN (VExpr.const .psigma [φ uN, φ vN])
              [.bvar 1, .bvar 0])
            (.bvar 2)))) ∧
    HasType [] (pairProjValT 1 φ)
      (.pi (.sort (φ uN))
        (.pi (.pi (.bvar 0) (.sort (φ vN)))
          (.pi (VExpr.mkAppN (VExpr.const .psigma [φ uN, φ vN])
              [.bvar 1, .bvar 0])
            (.app (.bvar 1) (VExpr.proj 0 (.bvar 0)))))) := by
  have hA : HasType [VExpr.mkAppN (VExpr.const .psigma [φ uN, φ vN])
        [.bvar 1, .bvar 0], VExpr.pi (.bvar 0) (.sort (φ vN)),
      VExpr.sort (φ uN)] (.bvar 2) (.sort (φ uN)) := by
    have := HasType.bvar (Γ := [VExpr.mkAppN (VExpr.const .psigma
        [φ uN, φ vN]) [.bvar 1, .bvar 0],
      VExpr.pi (.bvar 0) (.sort (φ vN)), VExpr.sort (φ uN)])
      (i := 2) (A := VExpr.sort (φ uN)) (by simp)
    simpa using this
  have hB : HasType [VExpr.mkAppN (VExpr.const .psigma [φ uN, φ vN])
        [.bvar 1, .bvar 0], VExpr.pi (.bvar 0) (.sort (φ vN)),
      VExpr.sort (φ uN)] (.bvar 1)
      (arrow (.bvar 2) (.sort (φ vN))) := by
    have := HasType.bvar (Γ := [VExpr.mkAppN (VExpr.const .psigma
        [φ uN, φ vN]) [.bvar 1, .bvar 0],
      VExpr.pi (.bvar 0) (.sort (φ vN)), VExpr.sort (φ uN)])
      (i := 1) (A := VExpr.pi (.bvar 0) (.sort (φ vN))) (by simp)
    simpa [arrow, VExpr.liftN] using this
  have hp : HasType [VExpr.mkAppN (VExpr.const .psigma [φ uN, φ vN])
        [.bvar 1, .bvar 0], VExpr.pi (.bvar 0) (.sort (φ vN)),
      VExpr.sort (φ uN)] (.bvar 0)
      (psigmaT (φ uN) (φ vN) (.bvar 2) (.bvar 1)) := by
    have := HasType.bvar (Γ := [VExpr.mkAppN (VExpr.const .psigma
        [φ uN, φ vN]) [.bvar 1, .bvar 0],
      VExpr.pi (.bvar 0) (.sort (φ vN)), VExpr.sort (φ uN)])
      (i := 0) (A := VExpr.mkAppN (VExpr.const .psigma [φ uN, φ vN])
        [.bvar 1, .bvar 0]) (by simp)
    simpa [psigmaT, VExpr.mkAppN, VExpr.liftN] using this
  exact ⟨.lam (.lam (.lam (HasType.projFst hA hB hp))),
    .lam (.lam (.lam (HasType.projSnd hA hB hp)))⟩


/-- **The pinned pair's projections, installed.**  The only `projInfo`
constants any block installs — and therefore the only test of
`hheadProj`, `hheadProjPair`, and of `hheadEta` at a head that is *not*
reserved. -/
theorem extendPairProjTT {env : Env} (m : EnvTT env) {i : Nat}
    {entry : ProjEntry} {ci : ConstantInfo}
    (hci : ci = .projInfo entry)
    (hentry : entry = pairFstEntry ∨ entry = pairSndEntry)
    (hnat : entry.native = true)
    (hname : ci.name = projFnName psigmaName i)
    (hlp : ci.toConstantVal.levelParams = [uN, vN])
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hfresh : env.find? ci.name = none)
    (hwf : EnvWF ⟨ci :: env.consts⟩)
    (htype : ∀ φ : Name → Nat, ∃ t,
      denoteClosed (cvalSet m.cval ci.name (pairProjValT i))
        ⟨ci :: env.consts⟩ φ ci.toConstantVal.type = some t ∧
        HasType [] (pairProjValT i φ) t) :
    ∃ m' : EnvTT ⟨ci :: env.consts⟩,
      m'.cval = cvalSet m.cval ci.name (pairProjValT i) := by
  refine extendBasisTT m (val := pairProjValT i) ?eta ?unit
    (fun T cvT caps cvC hfT _ _ _ hfcC hor => by
      rcases hor with hT | hC
      · rw [hT, Env.find?_cons, if_pos rfl, hci] at hfT
        exact nomatch hfT
      · rw [hC, Env.find?_cons, if_pos rfl, hci] at hfcC
        exact nomatch hfcC)
    (fun hb => by rw [hci] at hb; exact nomatch hb)
    (fun ψ t hp => by
      rw [hname] at hp
      simp only [pinnedDirectT] at hp
      rw [if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide)),
        if_neg (projFnName_ne_reserved (by decide))] at hp
      exact nomatch hp)
    hfresh hwf (fun ψ => pairProjValT_closed i ψ) ?params htype
    (fun _ _ _ heq => by rw [hci] at heq; exact nomatch heq)
    (fun _ _ heq => by rw [hci] at heq; exact nomatch heq)
    (fun _ heq => by rw [hci] at heq; exact nomatch heq)
    (fun hemp => by
      rw [hname] at hemp
      exact absurd hemp (projFnName_ne_reserved (n := emptyName) (by decide)))
    (fun _ _ _ _ heq => by rw [hci] at heq; exact nomatch heq)
    (fun _ _ _ _ heq => by rw [hci] at heq; exact nomatch heq)
    (fun e heq _ => by
      rw [hci] at heq
      injection heq with he
      exact ⟨he ▸ hentry, hP, hM⟩)
    (fun _ e heq _ => by
      rw [hci] at heq
      injection heq with he
      exact he ▸ hnat)
    (fun heq => by
      rw [hname] at heq
      exact absurd heq (projFnName_ne_reserved (n := eqName) (by decide)))
  case params =>
    intro φ₁ φ₂ hp
    rw [hlp] at hp
    rw [pairProjValT, pairProjValT,
      hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  case eta =>
    intro T cvT caps hf hcape hresT hfam hpart
    rcases hpart with hT | hC | ⟨j, hj, hP'⟩
    · rw [hT, Env.find?_cons, if_pos rfl, hci] at hf; exact nomatch hf
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [hC, Env.find?_cons, if_pos rfl, hci] at hfC; exact nomatch hfC
    · rw [hname] at hP'
      obtain rfl : T = psigmaName := projFnName_inj hP'
      rw [show reservedBasisNames.contains psigmaName = true from by decide]
        at hresT
      exact nomatch hresT
  case unit =>
    intro cv caps heq _ _
    rw [hci] at heq; exact nomatch heq


/-- `PSigma'.fst`, installed. -/
theorem extendPairFstTT {env : Env} (m : EnvTT env)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hfresh : env.find? pairFstA.name = none)
    (hwf : EnvWF ⟨pairFstA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨pairFstA :: env.consts⟩,
      m'.cval = cvalSet m.cval pairFstA.name (pairProjValT 0) := by
  refine extendPairProjTT m rfl (Or.inl rfl) (by decide) rfl rfl hP hM
    hfresh hwf ?_
  intro φ
  have hPc : ∀ d : Nat,
      denote (cvalSet m.cval pairFstA.name (pairProjValT 0))
        ⟨pairFstA :: env.consts⟩ φ d
        (.const psigmaName [.param uN, .param vN])
        = some (VExpr.const .psigma [φ uN, φ vN]) := by
    intro d
    refine denote_const_pin m (by decide) hP rfl (by decide) ?_ d
    rw [show Level.substFn φ psigmaA.toConstantVal.levelParams
        [Level.param uN, Level.param vN] = φ from
      substFn_param_self φ [uN, vN]]
    simp +decide [pinnedDirectT]
  refine ⟨_, ?_, (pairProjValT_typed φ).1⟩
  rw [denoteClosed, show pairFstA.toConstantVal.type
    = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
        (Expr.forallE (Name.anonymous.str "β")
          (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
            (.sort (.param vN)) { bi := .default })
          (Expr.forallE (Name.anonymous.str "t")
            (.app (.app (.const psigmaName [.param uN, .param vN])
              (.bvar 1)) (.bvar 0))
            (.bvar 2) { bi := .default })
          { bi := .implicit })
        { bi := .implicit } from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar, Level.eval,
    hPc, VExpr.mkAppN]

/-- `PSigma'.snd`, installed. -/
theorem extendPairSndTT {env : Env} (m : EnvTT env)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hfresh : env.find? pairSndA.name = none)
    (hwf : EnvWF ⟨pairSndA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨pairSndA :: env.consts⟩,
      m'.cval = cvalSet m.cval pairSndA.name (pairProjValT 1) := by
  refine extendPairProjTT m rfl (Or.inr rfl) (by decide) rfl rfl hP hM
    hfresh hwf ?_
  intro φ
  have hPc : ∀ d : Nat,
      denote (cvalSet m.cval pairSndA.name (pairProjValT 1))
        ⟨pairSndA :: env.consts⟩ φ d
        (.const psigmaName [.param uN, .param vN])
        = some (VExpr.const .psigma [φ uN, φ vN]) := by
    intro d
    refine denote_const_pin m (by decide) hP rfl (by decide) ?_ d
    rw [show Level.substFn φ psigmaA.toConstantVal.levelParams
        [Level.param uN, Level.param vN] = φ from
      substFn_param_self φ [uN, vN]]
    simp +decide [pinnedDirectT]
  refine ⟨_, ?_, (pairProjValT_typed φ).2⟩
  rw [denoteClosed, show pairSndA.toConstantVal.type
    = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
        (Expr.forallE (Name.anonymous.str "β")
          (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
            (.sort (.param vN)) { bi := .default })
          (Expr.forallE (Name.anonymous.str "t")
            (.app (.app (.const psigmaName [.param uN, .param vN])
              (.bvar 1)) (.bvar 0))
            (.app (.bvar 1) (.proj psigmaName 0 (.bvar 0)))
            { bi := .default })
          { bi := .implicit })
        { bi := .implicit } from rfl]
  simp [denote_forallE, denote_sort, denote_app, denote_fvar, denote_proj,
    Expr.instantiate1, Level.eval, hPc, VExpr.mkAppN]


/-- `PSigma'.rec`'s valuation: the minor premise at the subject's two
projections — `psigmaRec_derivable` (`Setlec/TT/Examples.lean`).  The
last of the layer's *derived* four, and the one that derives through
**structure η** where `Eq.rec` derived through proof irrelevance. -/
def psigmaRecValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN))
    (.lam (.pi (.bvar 0) (.sort (ψ vN)))
      (.lam (.pi (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
            [.bvar 1, .bvar 0]) (.sort 0))
        (.lam (.pi (.bvar 2)
            (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 2) (VExpr.mkAppN
                (VExpr.const .psigmaMk [ψ uN, ψ vN])
                [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))
          (.lam (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
              [.bvar 3, .bvar 2])
            (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
              (.proj 1 (.bvar 0)))))))

/-- `PSigma'.rec`'s frame, innermost first: `[t, mk, motive, β, α]`. -/
def psigmaRecCtx (ψ : Name → Nat) : List VExpr :=
  [VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN]) [.bvar 3, .bvar 2],
   VExpr.pi (.bvar 2)
     (.pi (.app (.bvar 2) (.bvar 0))
       (.app (.bvar 2) (VExpr.mkAppN (VExpr.const .psigmaMk [ψ uN, ψ vN])
         [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))),
   VExpr.pi (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
     [.bvar 1, .bvar 0]) (.sort 0),
   VExpr.pi (.bvar 0) (.sort (ψ vN)),
   VExpr.sort (ψ uN)]

/-- **`PSigma'.rec`'s typing.**  The minor premise applied to the two
projections lands at the motive *at the reassembled pair*; structure η
converts that to the motive at the subject. -/
theorem psigmaRecValT_typed (ψ : Name → Nat) :
    HasType [] (psigmaRecValT ψ)
      (.pi (.sort (ψ uN))
        (.pi (.pi (.bvar 0) (.sort (ψ vN)))
          (.pi (.pi (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
                [.bvar 1, .bvar 0]) (.sort 0))
            (.pi (.pi (.bvar 2)
                (.pi (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 2) (VExpr.mkAppN
                    (VExpr.const .psigmaMk [ψ uN, ψ vN])
                    [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))
              (.pi (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
                  [.bvar 3, .bvar 2])
                (.app (.bvar 2) (.bvar 0))))))) := by
  refine .lam (.lam (.lam (.lam (.lam ?_))))
  show HasType (psigmaRecCtx ψ) _ _
  have hα : HasType (psigmaRecCtx ψ) (.bvar 4) (.sort (ψ uN)) := by
    have := HasType.bvar (Γ := psigmaRecCtx ψ) (i := 4)
      (A := VExpr.sort (ψ uN)) (by simp [psigmaRecCtx])
    simpa using this
  have hβ : HasType (psigmaRecCtx ψ) (.bvar 3)
      (arrow (.bvar 4) (.sort (ψ vN))) := by
    have := HasType.bvar (Γ := psigmaRecCtx ψ) (i := 3)
      (A := VExpr.pi (.bvar 0) (.sort (ψ vN))) (by simp [psigmaRecCtx])
    simpa [arrow, VExpr.liftN] using this
  have hp : HasType (psigmaRecCtx ψ) (.bvar 0)
      (psigmaT (ψ uN) (ψ vN) (.bvar 4) (.bvar 3)) := by
    have := HasType.bvar (Γ := psigmaRecCtx ψ) (i := 0)
      (A := VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
        [.bvar 3, .bvar 2]) (by simp [psigmaRecCtx])
    simpa [psigmaT, VExpr.mkAppN, VExpr.liftN] using this
  have hmk : HasType (psigmaRecCtx ψ) (.bvar 1)
      (.pi (.bvar 4)
        (.pi (.app (.bvar 4) (.bvar 0))
          (.app (.bvar 4) (VExpr.mkAppN
            (VExpr.const .psigmaMk [ψ uN, ψ vN])
            [.bvar 6, .bvar 5, .bvar 1, .bvar 0])))) := by
    have := HasType.bvar (Γ := psigmaRecCtx ψ) (i := 1)
      (A := VExpr.pi (.bvar 2)
        (.pi (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 2) (VExpr.mkAppN
            (VExpr.const .psigmaMk [ψ uN, ψ vN])
            [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))
      (by simp [psigmaRecCtx])
    simpa [VExpr.mkAppN, VExpr.liftN] using this
  -- `psigmaRec_derivable` (`Setlec/TT/Examples.lean`), inlined: the
  -- bridge does not import the layer's demo file.
  refine HasType.conv (T := .sort 0)
    (HasType.app (HasType.app hmk (HasType.projFst hα hβ hp))
      (HasType.projSnd hα hβ hp))
    (HasType.congrApp (T := .sort 0)
      (T' := psigmaT (ψ uN) (ψ vN) (.bvar 4) (.bvar 3)) (T'' := .sort 0)
      (HasType.refl (T := .sort 0))
      (HasType.symm (T' := psigmaT (ψ uN) (ψ vN) (.bvar 4) (.bvar 3))
        (HasType.psigmaEta hα hβ hp)))

/-- The tower is closed. -/
theorem psigmaRecValT_closed (ψ : Name → Nat) :
    VExpr.Closed (psigmaRecValT ψ) := by
  simp only [psigmaRecValT, VExpr.Closed, VExpr.bvarsBelow, VExpr.mkAppN]
  repeat' apply And.intro
  all_goals first | trivial | omega

/-- The tower reads the assignment only at its own level names. -/
theorem psigmaRecValT_congr {ψ₁ ψ₂ : Name → Nat}
    (hu : ψ₁ uN = ψ₂ uN) (hv : ψ₁ vN = ψ₂ vN) :
    psigmaRecValT ψ₁ = psigmaRecValT ψ₂ := by
  rw [psigmaRecValT, psigmaRecValT, hu, hv]


/-- The `PSigma'` block's two earlier constants, denoted in the
environment the recursor's install works in. -/
theorem denote_psigmaRec_consts {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (w1 w2 : Level)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hPv : ∀ ψ : Name → Nat,
      m.cval psigmaName ψ = VExpr.const .psigma [ψ uN, ψ vN])
    (hMv : ∀ ψ : Name → Nat,
      m.cval psigmaMkName ψ = VExpr.const .psigmaMk [ψ uN, ψ vN]) :
    (∀ e : Nat,
      denote (cvalSet m.cval psigmaRecA.name val)
        ⟨psigmaRecA :: env.consts⟩ φ e (.const psigmaName [w1, w2])
        = some (VExpr.const .psigma [w1.eval φ, w2.eval φ])) ∧
    (∀ e : Nat,
      denote (cvalSet m.cval psigmaRecA.name val)
        ⟨psigmaRecA :: env.consts⟩ φ e (.const psigmaMkName [w1, w2])
        = some (VExpr.const .psigmaMk [w1.eval φ, w2.eval φ])) := by
  constructor
  · intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hP]
    simp only [show ([w1, w2] : List Level).length
      = psigmaA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hPv]
    rfl
  · intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hM]
    simp only [show ([w1, w2] : List Level).length
      = psigmaMkA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (by decide), hMv]
    rfl

/-- **`PSigma'.rec`'s pinned type, denoted at any depth and any
levels.** -/
theorem denote_psigmaRec_type {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w1 w2 : Level)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hPv : ∀ ψ : Name → Nat,
      m.cval psigmaName ψ = VExpr.const .psigma [ψ uN, ψ vN])
    (hMv : ∀ ψ : Name → Nat,
      m.cval psigmaMkName ψ = VExpr.const .psigmaMk [ψ uN, ψ vN]) :
    denote (cvalSet m.cval psigmaRecA.name val) ⟨psigmaRecA :: env.consts⟩ φ d
        (psigmaRecA.toConstantVal.type.instantiateLevelParams
          psigmaRecA.toConstantVal.levelParams [w1, w2])
      = some (.pi (.sort (w1.eval φ))
        (.pi (.pi (.bvar 0) (.sort (w2.eval φ)))
          (.pi (.pi (VExpr.mkAppN
                (VExpr.const .psigma [w1.eval φ, w2.eval φ])
                [.bvar 1, .bvar 0]) (.sort 0))
            (.pi (.pi (.bvar 2)
                (.pi (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 2) (VExpr.mkAppN
                    (VExpr.const .psigmaMk [w1.eval φ, w2.eval φ])
                    [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))
              (.pi (VExpr.mkAppN
                  (VExpr.const .psigma [w1.eval φ, w2.eval φ])
                  [.bvar 3, .bvar 2])
                (.app (.bvar 2) (.bvar 0))))))) := by
  have hsu : Level.subst [uN, vN] [w1, w2] (.param uN) = w1 := by
    simp [Level.subst, Level.subst.go, uN]
  have hsv : Level.subst [uN, vN] [w1, w2] (.param vN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, vN]
  have hsz : Level.subst [uN, vN] [w1, w2] .zero = .zero := by
    simp [Level.subst, Level.subst.go]
  obtain ⟨hPc, hMc⟩ := denote_psigmaRec_consts m (val := val) φ w1 w2 hP hM
    hPv hMv
  rw [show psigmaRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "β")
            (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
              (.sort (.param vN)) { bi := .default })
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (.app (.app (.const psigmaName [.param uN, .param vN])
                  (.bvar 1)) (.bvar 0))
                (.sort .zero) { bi := .default })
              (Expr.forallE (Name.anonymous.str "mk")
                (Expr.forallE (Name.anonymous.str "fst") (.bvar 2)
                  (Expr.forallE (Name.anonymous.str "snd")
                    (.app (.bvar 2) (.bvar 0))
                    (.app (.bvar 2)
                      (.app (.app (.app (.app (.const psigmaMkName
                        [.param uN, .param vN]) (.bvar 4)) (.bvar 3))
                        (.bvar 1)) (.bvar 0)))
                    { bi := .default })
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.const psigmaName [.param uN, .param vN])
                    (.bvar 3)) (.bvar 2))
                  (.app (.bvar 2) (.bvar 0)) { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show psigmaRecA.toConstantVal.levelParams = [uN, vN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsv, denote_forallE, denote_sort,
    denote_app, denote_fvar, hPc, hMc, hsz, VExpr.mkAppN, Level.eval]

/-- `PSigma'.mk`'s pinned type, denoted — the constructor telescope the
fire site's `hfitC` is stated against. -/
theorem denote_psigmaMk_type {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w1 w2 : Level)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hPv : ∀ ψ : Name → Nat,
      m.cval psigmaName ψ = VExpr.const .psigma [ψ uN, ψ vN])
    (hMv : ∀ ψ : Name → Nat,
      m.cval psigmaMkName ψ = VExpr.const .psigmaMk [ψ uN, ψ vN]) :
    denote (cvalSet m.cval psigmaRecA.name val) ⟨psigmaRecA :: env.consts⟩ φ d
        (psigmaMkA.toConstantVal.type.instantiateLevelParams
          psigmaMkA.toConstantVal.levelParams [w1, w2])
      = some (.pi (.sort (w1.eval φ))
        (.pi (.pi (.bvar 0) (.sort (w2.eval φ)))
          (.pi (.bvar 1)
            (.pi (.app (.bvar 1) (.bvar 0))
              (VExpr.mkAppN (VExpr.const .psigma [w1.eval φ, w2.eval φ])
                [.bvar 3, .bvar 2]))))) := by
  have hsu : Level.subst [uN, vN] [w1, w2] (.param uN) = w1 := by
    simp [Level.subst, Level.subst.go, uN]
  have hsv : Level.subst [uN, vN] [w1, w2] (.param vN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, vN]
  obtain ⟨hPc, -⟩ := denote_psigmaRec_consts m (val := val) φ w1 w2 hP hM
    hPv hMv
  rw [show psigmaMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "β")
            (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
              (.sort (.param vN)) { bi := .default })
            (Expr.forallE (Name.anonymous.str "fst") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "snd")
                (.app (.bvar 1) (.bvar 0))
                (.app (.app (.const psigmaName
                    [.param uN, .param vN]) (.bvar 3)) (.bvar 2))
                { bi := .default })
              { bi := .default })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show psigmaMkA.toConstantVal.levelParams = [uN, vN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsv, denote_forallE, denote_sort,
    denote_app, denote_fvar, hPc, VExpr.mkAppN, Level.eval]

/-- `PSigma'.rec`'s single stored rule. -/
def psigmaRecRule : RecRule :=
  { ctor := psigmaMkName, nfields := 2, ctorParams := 2, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "α") (.sort (.param uN))
      (Expr.lam (Name.anonymous.str "β")
        (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
          (.sort (.param vN)) { bi := .default })
        (Expr.lam (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "t")
            (.app (.app (.const psigmaName [.param uN, .param vN])
              (.bvar 1)) (.bvar 0))
            (.sort .zero) { bi := .default })
          (Expr.lam (Name.anonymous.str "mk")
            (Expr.forallE (Name.anonymous.str "fst") (.bvar 2)
              (Expr.forallE (Name.anonymous.str "snd")
                (.app (.bvar 2) (.bvar 0))
                (.app (.bvar 2)
                  (.app (.app (.app (.app (.const psigmaMkName
                    [.param uN, .param vN]) (.bvar 4)) (.bvar 3))
                    (.bvar 1)) (.bvar 0)))
                { bi := .default })
              { bi := .default })
            (Expr.lam (Name.anonymous.str "fst") (.bvar 3)
              (Expr.lam (Name.anonymous.str "snd")
                (.app (.bvar 3) (.bvar 0))
                (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                { bi := .default })
              { bi := .default })
            { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .implicit } }

/-- The stored declaration, with its rule named. -/
theorem psigmaRecA_eq :
    psigmaRecA = .recInfo psigmaRecA.toConstantVal 4 4 [psigmaRecRule] := rfl

/-- `PSigma'.rec`'s rule right-hand side, denoted — named, because the
iota proof has to hand it to `BetaSpine` as an explicit head. -/
def psigmaRecRhsV (a b : Nat) : VExpr :=
  .lam (.sort a)
    (.lam (.pi (.bvar 0) (.sort b))
      (.lam (.pi (VExpr.mkAppN (VExpr.const .psigma [a, b])
            [.bvar 1, .bvar 0]) (.sort 0))
        (.lam (.pi (.bvar 2)
            (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 2) (VExpr.mkAppN (VExpr.const .psigmaMk [a, b])
                [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))
          (.lam (.bvar 3)
            (.lam (.app (.bvar 3) (.bvar 0))
              (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))))))

/-- **`PSigma'.rec`'s rule right-hand side, denoted.** -/
theorem denote_psigmaRec_rhs {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w1 w2 : Level)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hPv : ∀ ψ : Name → Nat,
      m.cval psigmaName ψ = VExpr.const .psigma [ψ uN, ψ vN])
    (hMv : ∀ ψ : Name → Nat,
      m.cval psigmaMkName ψ = VExpr.const .psigmaMk [ψ uN, ψ vN]) :
    denote (cvalSet m.cval psigmaRecA.name val) ⟨psigmaRecA :: env.consts⟩ φ d
        ((RecRule.rhs psigmaRecRule).instantiateLevelParams
          psigmaRecA.toConstantVal.levelParams [w1, w2])
      = some (psigmaRecRhsV (w1.eval φ) (w2.eval φ)) := by
  have hsu : Level.subst [uN, vN] [w1, w2] (.param uN) = w1 := by
    simp [Level.subst, Level.subst.go, uN]
  have hsv : Level.subst [uN, vN] [w1, w2] (.param vN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, vN]
  have hsz : Level.subst [uN, vN] [w1, w2] .zero = .zero := by
    simp [Level.subst, Level.subst.go]
  obtain ⟨hPc, hMc⟩ := denote_psigmaRec_consts m (val := val) φ w1 w2 hP hM
    hPv hMv
  rw [show psigmaRecA.toConstantVal.levelParams = [uN, vN] from rfl]
  simp only [psigmaRecRule]
  simp [Expr.instantiateLevelParams, hsu, hsv, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hPc, hMc, hsz, psigmaRecRhsV,
    VExpr.mkAppN, Level.eval]


/-- **`PSigma'.rec`, installed.**  Unlike `Eq`'s, this block's iota has
real content past β: the tower returns the minor premise at the two
*projections*, and the rule's right-hand side wants it at the two
*fields*, so the two projection computations (`projFstMk`, `projSndMk`)
close the gap — applied on the rule's side, where the constructor
spine's own telescope supplies their premises. -/
theorem extendPSigmaRecTT {env : Env} (m : EnvTT env)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hPv : ∀ ψ : Name → Nat,
      m.cval psigmaName ψ = VExpr.const .psigma [ψ uN, ψ vN])
    (hMv : ∀ ψ : Name → Nat,
      m.cval psigmaMkName ψ = VExpr.const .psigmaMk [ψ uN, ψ vN])
    (hfresh : env.find? (psigmaName.str "rec") = none)
    (hwf : EnvWF ⟨psigmaRecA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨psigmaRecA :: env.consts⟩,
      m'.cval = cvalSet m.cval psigmaRecA.name psigmaRecValT := by
  refine extendBasisTT m (val := psigmaRecValT)
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name psigmaRecA = psigmaName.str "rec" from rfl]
        at hp
      simp +decide [pinnedDirectT] at hp)
    hfresh hwf (fun ψ => psigmaRecValT_closed ψ) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · -- the valuation reads only `u` and `v`
    intro φ₁ φ₂ hp
    exact psigmaRecValT_congr
      (hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self))
      (hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self))
  · -- the pinned type, denoted
    intro φ
    refine ⟨_, ?_, HasType.weakenNil (psigmaRecValT_typed φ) []⟩
    rw [denoteClosed, ← Expr.instantiateLevelParams_self
        psigmaRecA.toConstantVal.levelParams psigmaRecA.toConstantVal.type,
      show psigmaRecA.toConstantVal.levelParams.map Level.param
        = [Level.param uN, Level.param vN] from rfl,
      denote_psigmaRec_type m φ 0 (.param uN) (.param vN) hP hM hPv hMv]
    rfl
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨psigmaMkA.toConstantVal, 2, 2, hM⟩
    · exact nomatch hr'
  · -- the iota rule
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
      refine ⟨_, denote_psigmaRec_rhs m (val := psigmaRecValT) φ d w1 w2
        hP hM hPv hMv, ?_⟩
      intro cvj cnP cnF hfj Δ usj xs ys TV TVj restR restC hxs hys husj hlev
        _ _ _ hdTV hdTVj hfitR hfitC
      have hMu := hM
      simp only [psigmaMkName, psigmaName] at hMu
      rw [Env.find?_cons, if_neg (by decide), hMu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = psigmaMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 2 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain ⟨y1, y2, ya, yb, rfl⟩ : ∃ a b c e, ys = [a, b, c, e] := by
        match ys, hys with
        | [a, b, c, e], _ => exact ⟨a, b, c, e, rfl⟩
      obtain ⟨xα, xβ, xM, xmk, rfl⟩ : ∃ a b c e, xs = [a, b, c, e] := by
        match xs, hxs with
        | [a, b, c, e], _ => exact ⟨a, b, c, e, rfl⟩
      obtain ⟨v1, v2, rfl⟩ : ∃ a b, usj = [a, b] := by
        match usj, husj with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      -- **the fire site's levels**: `hlev` pins the constructor's to the
      -- recursor's, which is what makes the two denoted shapes comparable
      have hlps : psigmaMkA.toConstantVal.levelParams = [uN, vN] := rfl
      have hlu : Level.eval φ v1 = Level.eval φ w1 := by
        have := congrFun hlev uN
        rw [hlps] at this
        simpa [recFireComparands, Level.substFn, Level.subst, Level.subst.go,
          uN, vN] using this
      have hlv : Level.eval φ v2 = Level.eval φ w2 := by
        have := congrFun hlev vN
        rw [hlps] at this
        simpa [recFireComparands, Level.substFn, Level.subst, Level.subst.go,
          uN, vN] using this
      have hctor : cvalSet m.cval psigmaRecA.name psigmaRecValT
          ((Name.anonymous.str "PSigma'").str "mk")
          (Level.substFn φ psigmaMkA.toConstantVal.levelParams [v1, v2])
          = VExpr.const .psigmaMk [Level.eval φ w1, Level.eval φ w2] := by
        have hMv' := hMv
        simp only [psigmaMkName, psigmaName] at hMv'
        rw [cvalSet_ne (by decide), hMv']
        simp only [show Level.substFn φ psigmaMkA.toConstantVal.levelParams
          [v1, v2] uN = Level.eval φ v1 from by
            rw [hlps]; simp [Level.substFn, uN],
          show Level.substFn φ psigmaMkA.toConstantVal.levelParams
            [v1, v2] vN = Level.eval φ v2 from by
              rw [hlps]; simp [Level.substFn, uN, vN],
          hlu, hlv]
      obtain rfl : TV = _ :=
        (Option.some.inj ((denote_psigmaRec_type m (val := psigmaRecValT) φ d
          w1 w2 hP hM hPv hMv).symm.trans hdTV)).symm
      obtain rfl : TVj = _ :=
        (Option.some.inj ((denote_psigmaMk_type m (val := psigmaRecValT) φ d
          v1 v2 hP hM hPv hMv).symm.trans hdTVj)).symm
      rw [hctor] at hfitR
      rw [hlu, hlv] at hfitC
      rw [cvalSet_self, hctor]
      cases hfitR with | cons t1 hfitR =>
      cases hfitR with | cons t2 hfitR =>
      cases hfitR with | cons t3 hfitR =>
      cases hfitR with | cons t4 hfitR =>
      cases hfitR with | cons t5 hfitR =>
      cases hfitC with | cons c1 hfitC =>
      cases hfitC with | cons c2 hfitC =>
      cases hfitC with | cons c3 hfitC =>
      cases hfitC with | cons c4 hfitC =>
      -- the telescope entries, with the fired spine's lift/inst chains
      -- collapsed — the form the layer's projection rules ask for
      have hα : HasType Δ xα (VExpr.sort (Level.eval φ w1)) := t1
      have hβ : HasType Δ xβ (arrow xα (VExpr.sort (Level.eval φ w2))) := by
        simpa [arrow, VExpr.liftN_zero] using t2
      have hp : HasType Δ
          (VExpr.mkAppN (VExpr.const .psigmaMk
            [Level.eval φ w1, Level.eval φ w2]) [y1, y2, ya, yb])
          (psigmaT (Level.eval φ w1) (Level.eval φ w2) xα xβ) := by
        simpa [psigmaT, VExpr.mkAppN, inst_chain3, inst_chain2] using t5
      have hy1 : HasType Δ y1 (VExpr.sort (Level.eval φ w1)) := c1
      have hy2 : HasType Δ y2 (arrow y1 (VExpr.sort (Level.eval φ w2))) := by
        simpa [arrow, VExpr.liftN_zero] using c2
      have hya : HasType Δ ya y1 := by simpa [inst_chain1] using c3
      have hyb : HasType Δ yb (.app y2 ya) := by
        simpa [inst_chain1, VExpr.liftN_zero] using c4
      -- **the two projection computations** — the block's whole content
      -- past β, and the reason this install is not `Eq.rec`'s
      have hfstD : Deq Δ (VExpr.proj 0 (VExpr.mkAppN (VExpr.const .psigmaMk
          [Level.eval φ w1, Level.eval φ w2]) [y1, y2, ya, yb])) ya :=
        Deq.intro (HasType.projFstMk (T := xα) hy1 hy2 hya hyb)
      have hsndD : Deq Δ (VExpr.proj 1 (VExpr.mkAppN (VExpr.const .psigmaMk
          [Level.eval φ w1, Level.eval φ w2]) [y1, y2, ya, yb])) yb :=
        Deq.intro (HasType.projSndMk (T := xα) hy1 hy2 hya hyb)
      -- the same two projections, typed at the *recursor's* parameters,
      -- which is what the right-hand side's last two binders want
      have hfstT : HasType Δ (VExpr.proj 0 (VExpr.mkAppN (VExpr.const .psigmaMk
          [Level.eval φ w1, Level.eval φ w2]) [y1, y2, ya, yb]))
          ((((VExpr.liftN 3 xα 0).inst xβ 2).inst xM 1).inst xmk 0) := by
        rw [inst_chain3]; exact HasType.projFst hα hβ hp
      have hsndT : HasType Δ (VExpr.proj 1 (VExpr.mkAppN (VExpr.const .psigmaMk
          [Level.eval φ w1, Level.eval φ w2]) [y1, y2, ya, yb]))
          (.app ((((VExpr.liftN 3 xβ 0).inst xM 2).inst xmk 1).inst
              (VExpr.proj 0 (VExpr.mkAppN (VExpr.const .psigmaMk
                [Level.eval φ w1, Level.eval φ w2]) [y1, y2, ya, yb])) 0)
            (VExpr.liftN 0 (VExpr.proj 0
              (VExpr.mkAppN (VExpr.const .psigmaMk
                [Level.eval φ w1, Level.eval φ w2]) [y1, y2, ya, yb])) 0)) := by
        rw [inst_chain3, VExpr.liftN_zero]
        exact HasType.projSnd hα hβ hp
      -- β on the tower, β on the right-hand side, and the projections
      -- in between
      refine Deq.trans (Deq.ofBetaSpine
        (.cons t1 (.cons t2 (.cons t3 (.cons t4 (.cons t5 .nil))))))
        (Deq.trans ?_ (Deq.trans (Deq.symm (Deq.ofBetaSpine
          (f := psigmaRecRhsV (Level.eval φ w1) (Level.eval φ w2))
          (.cons t1 (.cons t2 (.cons t3 (.cons t4
            (.cons hfstT (.cons hsndT .nil)))))))) ?_))
      · simp only [VExpr.inst, VExpr.liftN, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceSub, reduceIte, inst_chain1, inst_chain2,
          VExpr.liftN_zero, VExpr.mkAppN, List.foldl_cons, List.foldl_nil]
        exact Deq.refl
      · exact Deq.app (Deq.appArg hfstD) hsndD
    · exact nomatch hr'


/-- **The `PSigma'` block, installed.**  Five constants — the block that
installs the only `projInfo` constants any block installs, and the only
one whose iota needs more than β. -/
theorem declBasisTT_psigmaK {env env₁ : Env} (m : EnvTT env)
    (h : BasisChain env BasisKind.psigmaK.declsA env₁) :
    Nonempty (EnvTT env₁) := by
  rw [show BasisKind.psigmaK.declsA
    = [psigmaA, psigmaMkA, psigmaRecA, pairFstA, pairSndA] from rfl] at h
  cases h with
  | cons h1 h =>
  cases h with
  | cons h2 h =>
  cases h with
  | cons h3 h =>
  cases h with
  | cons h4 h =>
  cases h with
  | cons h5 h =>
  cases h with
  | nil =>
  have hwf1 : EnvWF ⟨psigmaA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, -⟩ := extendPSigmaTT m h1 hwf1
  have hP1 : (⟨psigmaA :: env.consts⟩ : Env).find? psigmaName
      = some psigmaA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf2 : EnvWF ⟨psigmaMkA :: psigmaA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?res2, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res2 =>
    show Expr.constsResolve _ psigmaMkA.toConstantVal.type = true
    have hf : (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find? psigmaName
        = some psigmaA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hP1
    rw [show psigmaMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "β")
            (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
              (.sort (.param vN)) { bi := .default })
            (Expr.forallE (Name.anonymous.str "fst") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "snd")
                (.app (.bvar 1) (.bvar 0))
                (.app (.app (.const psigmaName
                    [.param uN, .param vN]) (.bvar 3)) (.bvar 2))
                { bi := .default })
              { bi := .default })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m2, -⟩ := extendPSigmaMkTT m1 hP1 h2 hwf2
  have hP2 : (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find? psigmaName
      = some psigmaA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hP1
  have hM2 : (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find? psigmaMkName
      = some psigmaMkA := by
    rw [Env.find?_cons]; exact if_pos rfl
  -- the two valuations the recursor's install needs are the invariant's,
  -- not the chain's: both constants are pinned
  have hPv2 : ∀ ψ : Name → Nat,
      m2.cval psigmaName ψ = VExpr.const .psigma [ψ uN, ψ vN] := fun ψ =>
    cval_pinned m2 (by decide) (by rw [hP2]; rfl) ψ
      (by simp +decide [pinnedDirectT])
  have hMv2 : ∀ ψ : Name → Nat,
      m2.cval psigmaMkName ψ = VExpr.const .psigmaMk [ψ uN, ψ vN] :=
    fun ψ => cval_pinned m2 (by decide) (by rw [hM2]; rfl) ψ
      (by simp +decide [pinnedDirectT])
  have hwf3 : EnvWF ⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ :=
    EnvWF.cons hwf2 ⟨rfl, rfl, ?res3, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec3,
      (fun _ _ heq => nomatch heq)⟩
  case res3 =>
    show Expr.constsResolve _ psigmaRecA.toConstantVal.type = true
    have hfP : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ :
        Env).find? psigmaName = some psigmaA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hP2
    have hfM : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ :
        Env).find? psigmaMkName = some psigmaMkA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hM2
    rw [show psigmaRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
                (.sort (.param vN)) { bi := .default })
              (Expr.forallE (Name.anonymous.str "motive")
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.const psigmaName [.param uN, .param vN])
                    (.bvar 1)) (.bvar 0))
                  (.sort .zero) { bi := .default })
                (Expr.forallE (Name.anonymous.str "mk")
                  (Expr.forallE (Name.anonymous.str "fst") (.bvar 2)
                    (Expr.forallE (Name.anonymous.str "snd")
                      (.app (.bvar 2) (.bvar 0))
                      (.app (.bvar 2)
                        (.app (.app (.app (.app (.const psigmaMkName
                          [.param uN, .param vN]) (.bvar 4)) (.bvar 3))
                          (.bvar 1)) (.bvar 0)))
                      { bi := .default })
                    { bi := .default })
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.const psigmaName [.param uN, .param vN])
                      (.bvar 3)) (.bvar 2))
                    (.app (.bvar 2) (.bvar 0)) { bi := .default })
                  { bi := .default })
                { bi := .implicit })
              { bi := .implicit })
            { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfP, hfM]
  case rec3 =>
    intro cv mI rP rules heq
    injection heq with h1' _ _ h4'
    subst h1'; subst h4'
    have hfP : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ :
        Env).find? psigmaName = some psigmaA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hP2
    have hfM : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ :
        Env).find? psigmaMkName = some psigmaMkA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hM2
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨rfl, rfl, by
        show Expr.constsResolve _ (RecRule.rhs psigmaRecRule) = true
        simp [Expr.constsResolve, psigmaRecRule, hfP, hfM], rfl,
        fun lvls pins heqf => nomatch heqf⟩
    · exact nomatch hr'
  obtain ⟨m3, -⟩ := extendPSigmaRecTT m2 hP2 hM2 hPv2 hMv2 h3 hwf3
  have hP3 : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ :
      Env).find? psigmaName = some psigmaA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hP2
  have hM3 : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ :
      Env).find? psigmaMkName = some psigmaMkA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hM2
  have hwf4 : EnvWF ⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA ::
      env.consts⟩ :=
    EnvWF.cons hwf3 ⟨rfl, rfl, ?res4, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res4 =>
    show Expr.constsResolve _ pairFstA.toConstantVal.type = true
    have hfP : (⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA ::
        env.consts⟩ : Env).find? psigmaName = some psigmaA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hP3
    rw [show pairFstA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
                (.sort (.param vN)) { bi := .default })
              (Expr.forallE (Name.anonymous.str "t")
                (.app (.app (.const psigmaName [.param uN, .param vN])
                  (.bvar 1)) (.bvar 0))
                (.bvar 2) { bi := .default })
              { bi := .implicit })
            { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfP]
  obtain ⟨m4, -⟩ := extendPairFstTT m3 hP3 hM3 h4 hwf4
  have hP4 : (⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA ::
      env.consts⟩ : Env).find? psigmaName = some psigmaA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hP3
  have hM4 : (⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA ::
      env.consts⟩ : Env).find? psigmaMkName = some psigmaMkA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hM3
  have hwf5 : EnvWF ⟨pairSndA :: pairFstA :: psigmaRecA :: psigmaMkA ::
      psigmaA :: env.consts⟩ :=
    EnvWF.cons hwf4 ⟨rfl, rfl, ?res5, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res5 =>
    show Expr.constsResolve _ pairSndA.toConstantVal.type = true
    have hfP : (⟨pairSndA :: pairFstA :: psigmaRecA :: psigmaMkA ::
        psigmaA :: env.consts⟩ : Env).find? psigmaName = some psigmaA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hP4
    rw [show pairSndA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
                (.sort (.param vN)) { bi := .default })
              (Expr.forallE (Name.anonymous.str "t")
                (.app (.app (.const psigmaName [.param uN, .param vN])
                  (.bvar 1)) (.bvar 0))
                (.app (.bvar 1) (.proj psigmaName 0 (.bvar 0))) { bi := .default })
              { bi := .implicit })
            { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfP]
  obtain ⟨m5, -⟩ := extendPairSndTT m4 hP4 hM4 h5 hwf5
  exact ⟨m5⟩


/-! ## `Quot`

Five constants: a stored inductive, its constructor, two stored
recursors, and — uniquely — a stored **axiom**.  Both recursors' rules
are `.inert`, so the block has no iota obligation at all: the checker's
quotient reduction is not `iotaRec`'s, and `RecRulesTT` constrains only
fireable rules.  What the block does have is the first *Eq-bridged*
types: `Quot.lift`'s and `Quot.sound`'s stored types end in the pinned
`Eq` applied to three arguments, where the layer's constants conclude
at `.eqE`.  §11's law is exactly that gap, and `congrPi` carries it out
through the telescope. -/

/-- Congruence for the dependent product, in `Deq` form. -/
theorem Deq.pi {Γ : List VExpr} {A A' B B' : VExpr}
    (hA : Deq Γ A A') (hB : Deq (A :: Γ) B B') :
    Deq Γ (.pi A B) (.pi A' B') :=
  ⟨A, HasType.congrPi (T'' := A) (hA.toHasType A) (hB.toHasType B)⟩

/-- The common case: only the codomain moves. -/
theorem Deq.piCod {Γ : List VExpr} {A B B' : VExpr}
    (hB : Deq (A :: Γ) B B') : Deq Γ (.pi A B) (.pi A B') :=
  Deq.pi Deq.refl hB

/-- `Quot`, installed. -/
theorem extendQuotTT {env : Env} (m : EnvTT env)
    (hfresh : env.find? quotName = none)
    (hwf : EnvWF ⟨quotA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨quotA :: env.consts⟩,
      m'.cval = cvalSet m.cval quotA.name
        (fun ψ => VExpr.const .quot [ψ uN]) := by
  refine extendBasisTT m (val := fun ψ => VExpr.const .quot [ψ uN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotA = quotName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, HasType.const⟩
    rw [denoteClosed, show quotA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (.sort (.param uN)) { bi := .default })
          { bi := .implicit } from rfl]
    simp [denote_forallE, denote_sort, denote_fvar, Level.eval]
    rfl

/-- `Quot.mk`, installed. -/
theorem extendQuotMkTT {env : Env} (m : EnvTT env)
    (hQ : env.find? quotName = some quotA)
    (hfresh : env.find? quotMkName = none)
    (hwf : EnvWF ⟨quotMkA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨quotMkA :: env.consts⟩,
      m'.cval = cvalSet m.cval quotMkA.name
        (fun ψ => VExpr.const .quotMk [ψ uN]) := by
  have hQc : ∀ (d : Nat) (φ : Name → Nat),
      denote (cvalSet m.cval quotMkA.name
        (fun ψ => VExpr.const .quotMk [ψ uN]))
        ⟨quotMkA :: env.consts⟩ φ d (.const quotName [.param uN])
        = some (VExpr.const .quot [φ uN]) := by
    intro d φ
    refine denote_const_pin m (by decide) hQ rfl (by decide) ?_ d
    rw [show Level.substFn φ quotA.toConstantVal.levelParams
        [Level.param uN] = φ from substFn_param_self φ [uN]]
    simp +decide [pinnedDirectT]
  refine extendBasisTT m (val := fun ψ => VExpr.const .quotMk [ψ uN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotMkA = quotMkName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, HasType.const⟩
    rw [denoteClosed, show quotMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (.app (.app (.const quotName [.param uN]) (.bvar 2))
                (.bvar 1)) { bi := .default })
            { bi := .default })
          { bi := .implicit } from rfl]
    simp [denote_forallE, denote_sort, denote_app, denote_fvar, Level.eval,
      hQc]
    rfl

/-- The `Quot` block's earlier constants, denoted in the environment
`Quot.ind`'s install works in. -/
theorem denote_quotInd_consts {env : Env} {ci : ConstantInfo}
    (m : EnvTT env) {val : (Name → Nat) → VExpr} (φ : Name → Nat)
    (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hnQ : ci.name ≠ quotName) (hnM : ci.name ≠ quotMkName) :
    (∀ e : Nat,
      denote (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ e
        (.const quotName [w]) = some (VExpr.const .quot [w.eval φ])) ∧
    (∀ e : Nat,
      denote (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ e
        (.const quotMkName [w]) = some (VExpr.const .quotMk [w.eval φ])) := by
  have hQv : ∀ ψ : Name → Nat,
      m.cval quotName ψ = VExpr.const .quot [ψ uN] := fun ψ =>
    cval_pinned m (by decide) (by rw [hQ]; rfl) ψ
      (by simp +decide [pinnedDirectT])
  have hMv : ∀ ψ : Name → Nat,
      m.cval quotMkName ψ = VExpr.const .quotMk [ψ uN] := fun ψ =>
    cval_pinned m (by decide) (by rw [hM]; rfl) ψ
      (by simp +decide [pinnedDirectT])
  constructor
  · intro e
    rw [denote_const, Env.find?_cons, if_neg hnQ, hQ]
    simp only [show ([w] : List Level).length
      = quotA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (Ne.symm hnQ), hQv]
    rfl
  · intro e
    rw [denote_const, Env.find?_cons, if_neg hnM, hM]
    simp only [show ([w] : List Level).length
      = quotMkA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalSet_ne (Ne.symm hnM), hMv]
    rfl

/-- `Quot.mk`'s pinned type, denoted — the constructor telescope a fire
site's `hfitC` is stated against. -/
theorem denote_quotMk_type {env : Env} {ci : ConstantInfo}
    (m : EnvTT env) {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hnQ : ci.name ≠ quotName) (hnM : ci.name ≠ quotMkName) :
    denote (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ d
        (quotMkA.toConstantVal.type.instantiateLevelParams
          quotMkA.toConstantVal.levelParams [w])
      = some (.pi (.sort (w.eval φ))
        (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
          (.pi (.bvar 1)
            (VExpr.mkAppN (VExpr.const .quot [w.eval φ])
              [.bvar 2, .bvar 1])))) := by
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go, uN]
  have hsz : Level.subst [uN] [w] .zero = .zero := by
    simp [Level.subst, Level.subst.go]
  obtain ⟨hQc, -⟩ := denote_quotInd_consts m (val := val) φ w hQ hM hnQ hnM
  rw [show quotMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (.app (.app (.const quotName [.param uN]) (.bvar 2))
                (.bvar 1)) { bi := .default })
            { bi := .default })
          { bi := .implicit } from rfl,
    show quotMkA.toConstantVal.levelParams = [uN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsz, denote_forallE, denote_sort,
    denote_app, denote_fvar, hQc, VExpr.mkAppN, Level.eval]

/-- **`Quot.ind`'s pinned type, denoted at any depth and any level.** -/
theorem denote_quotInd_type {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denote (cvalSet m.cval quotIndA.name val) ⟨quotIndA :: env.consts⟩ φ d
        (quotIndA.toConstantVal.type.instantiateLevelParams
          quotIndA.toConstantVal.levelParams [w])
      = some (.pi (.sort (w.eval φ))
        (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
          (.pi (.pi (VExpr.mkAppN (VExpr.const .quot [w.eval φ])
                [.bvar 1, .bvar 0]) (.sort 0))
            (.pi (.pi (.bvar 2)
                (.app (.bvar 1) (VExpr.mkAppN
                  (VExpr.const .quotMk [w.eval φ])
                  [.bvar 3, .bvar 2, .bvar 0])))
              (.pi (VExpr.mkAppN (VExpr.const .quot [w.eval φ])
                  [.bvar 3, .bvar 2])
                (.app (.bvar 2) (.bvar 0))))))) := by
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go, uN]
  have hsz : Level.subst [uN] [w] .zero = .zero := by
    simp [Level.subst, Level.subst.go]
  obtain ⟨hQc, hMc⟩ := denote_quotInd_consts m (ci := quotIndA) (val := val)
    φ w hQ hM (by decide) (by decide)
  rw [show quotIndA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "a")
                (.app (.app (.const quotName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.sort .zero) { bi := .default })
              (Expr.forallE (Name.anonymous.str "mk")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2)
                  (.app (.bvar 1)
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 3)) (.bvar 2)) (.bvar 0)))
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "q")
                  (.app (.app (.const quotName [.param uN]) (.bvar 3))
                    (.bvar 2))
                  (.app (.bvar 2) (.bvar 0)) { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show quotIndA.toConstantVal.levelParams = [uN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsz, denote_forallE, denote_sort,
    denote_app, denote_fvar, hQc, hMc, VExpr.mkAppN, Level.eval]

/-- `Quot.ind`'s single stored rule. -/
def quotIndRule : RecRule :=
  { ctor := quotMkName, nfields := 1, ctorParams := 2, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "α") (.sort (.param uN))
      (Expr.lam (Name.anonymous.str "r")
        (Expr.forallE Name.anonymous (.bvar 0)
          (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
            { bi := .default }) { bi := .default })
        (Expr.lam (Name.anonymous.str "β")
          (Expr.forallE (Name.anonymous.str "a")
            (.app (.app (.const quotName [.param uN]) (.bvar 1)) (.bvar 0))
            (.sort .zero) { bi := .default })
          (Expr.lam (Name.anonymous.str "mk")
            (Expr.forallE (Name.anonymous.str "a") (.bvar 2)
              (.app (.bvar 1)
                (.app (.app (.app (.const quotMkName [.param uN])
                  (.bvar 3)) (.bvar 2)) (.bvar 0)))
              { bi := .default })
            (Expr.lam (Name.anonymous.str "a") (.bvar 3)
              (.app (.bvar 1) (.bvar 0)) { bi := .default })
            { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .default } }

/-- The stored declaration, with its rule named. -/
theorem quotIndA_eq :
    quotIndA = .recInfo quotIndA.toConstantVal 4 4 [quotIndRule] := rfl

/-- `Quot.ind`'s right-hand side, denoted. -/
def quotIndRhsV (a : Nat) : VExpr :=
  .lam (.sort a)
    (.lam (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
      (.lam (.pi (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 1, .bvar 0])
          (.sort 0))
        (.lam (.pi (.bvar 2)
            (.app (.bvar 1) (VExpr.mkAppN (VExpr.const .quotMk [a])
              [.bvar 3, .bvar 2, .bvar 0])))
          (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))))))

theorem denote_quotInd_rhs {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denote (cvalSet m.cval quotIndA.name val) ⟨quotIndA :: env.consts⟩ φ d
        ((RecRule.rhs quotIndRule).instantiateLevelParams
          quotIndA.toConstantVal.levelParams [w])
      = some (quotIndRhsV (w.eval φ)) := by
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go, uN]
  have hsz : Level.subst [uN] [w] .zero = .zero := by
    simp [Level.subst, Level.subst.go]
  obtain ⟨hQc, hMc⟩ := denote_quotInd_consts m (ci := quotIndA) (val := val)
    φ w hQ hM (by decide) (by decide)
  rw [show quotIndA.toConstantVal.levelParams = [uN] from rfl]
  simp only [quotIndRule]
  simp [Expr.instantiateLevelParams, hsu, hsz, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hQc, hMc, quotIndRhsV,
    VExpr.mkAppN, Level.eval]


/-- **`Quot.ind`, installed.**  Its iota is *proof irrelevance*: the
motive lands in `Prop` by the stored type's own `Sort 0`, and the layer
carries no `quotIndMk` rule, so both sides are simply proofs.  The
right-hand side's field slot is typed at the **recursor's** parameter,
which is what the fire site's parameter test supplies. -/
theorem extendQuotIndTT {env : Env} (m : EnvTT env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hfresh : env.find? quotIndName = none)
    (hwf : EnvWF ⟨quotIndA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨quotIndA :: env.consts⟩,
      m'.cval = cvalSet m.cval quotIndA.name
        (fun ψ => VExpr.const .quotInd [ψ uN]) := by
  refine extendBasisTT m (val := fun ψ => VExpr.const .quotInd [ψ uN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotIndA = quotIndName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, HasType.const⟩
    rw [denoteClosed, ← Expr.instantiateLevelParams_self
        quotIndA.toConstantVal.levelParams quotIndA.toConstantVal.type,
      show quotIndA.toConstantVal.levelParams.map Level.param
        = [Level.param uN] from rfl,
      denote_quotInd_type m φ 0 (.param uN) hQ hM]
    simp [Level.eval, BConst.type, quotT, quotMkT, relT, lv, VExpr.mkAppN,
      VExpr.liftN]
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨quotMkA.toConstantVal, 2, 1, hM⟩
    · exact nomatch hr'
  · -- the iota rule
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h1'; subst h2'; subst h3'; subst h4'
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · refine ⟨by omega, ?_⟩
      intro φ d us hus
      obtain ⟨w, rfl⟩ : ∃ a, us = [a] := by
        match us, hus with
        | [a], _ => exact ⟨a, rfl⟩
      refine ⟨_, denote_quotInd_rhs m
        (val := fun ψ => VExpr.const .quotInd [ψ uN]) φ d w hQ hM, ?_⟩
      intro cvj cnP cnF hfj Δ usj xs ys TV TVj restR restC hxs hys husj hlev
        hpar _ _ hdTV hdTVj hfitR hfitC
      have hMu := hM
      simp only [quotMkName, quotName] at hMu
      rw [Env.find?_cons, if_neg (by decide), hMu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain ⟨y1, y2, ya, rfl⟩ : ∃ a b c, ys = [a, b, c] := by
        match ys, hys with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      obtain ⟨xα, xr, xβ, xmk, rfl⟩ : ∃ a b c e, xs = [a, b, c, e] := by
        match xs, hxs with
        | [a, b, c, e], _ => exact ⟨a, b, c, e, rfl⟩
      obtain ⟨v1, rfl⟩ : ∃ a, usj = [a] := by
        match usj, husj with
        | [a], _ => exact ⟨a, rfl⟩
      have hlps : quotMkA.toConstantVal.levelParams = [uN] := rfl
      have hlu : Level.eval φ v1 = Level.eval φ w := by
        have := congrFun hlev uN
        rw [hlps] at this
        simpa [recFireComparands, Level.substFn, Level.subst, Level.subst.go,
          uN] using this
      have hctor : cvalSet m.cval quotIndA.name
          (fun ψ => VExpr.const .quotInd [ψ uN])
          ((Name.anonymous.str "Quot").str "mk")
          (Level.substFn φ quotMkA.toConstantVal.levelParams [v1])
          = VExpr.const .quotMk [Level.eval φ w] := by
        rw [cvalSet_ne (by decide)]
        have hv := cval_pinned m (n := quotMkName) (by decide)
          (by rw [hM]; rfl)
          (Level.substFn φ quotMkA.toConstantVal.levelParams [v1])
          (t := VExpr.const .quotMk
            [Level.substFn φ quotMkA.toConstantVal.levelParams [v1] uN])
          (by simp +decide [pinnedDirectT])
        simp only [quotMkName, quotName] at hv
        rw [hv]
        simp only [show Level.substFn φ quotMkA.toConstantVal.levelParams
          [v1] uN = Level.eval φ v1 from by
            rw [hlps]; simp [Level.substFn, uN], hlu]
      obtain rfl : TV = _ :=
        (Option.some.inj ((denote_quotInd_type m
          (val := fun ψ => VExpr.const .quotInd [ψ uN]) φ d w
          hQ hM).symm.trans hdTV)).symm
      obtain rfl : TVj = _ :=
        (Option.some.inj ((denote_quotMk_type m (ci := quotIndA)
          (val := fun ψ => VExpr.const .quotInd [ψ uN]) φ d v1
          hQ hM (by decide) (by decide)).symm.trans hdTVj)).symm
      rw [hctor] at hfitR
      rw [hlu] at hfitC
      rw [cvalSet_self, hctor]
      have hfitR0 := hfitR
      cases hfitR with | cons t1 hfitR =>
      cases hfitR with | cons t2 hfitR =>
      cases hfitR with | cons t3 hfitR =>
      cases hfitR with | cons t4 hfitR =>
      cases hfitR with | cons t5 hfitR =>
      cases hfitR with | nil =>
      cases hfitC with | cons c1 hfitC =>
      cases hfitC with | cons c2 hfitC =>
      cases hfitC with | cons c3 hfitC =>
      -- **the parameter test**: the fired constructor's `α` and `r`
      -- are the recursor's
      have hp0 : Deq Δ y1 xα := by
        have := hpar rfl 0 ?_ ?_
        · simpa using this
        · exact Nat.zero_lt_succ _
        · exact Nat.zero_lt_succ _
      -- the telescope entries, cleaned
      have hβ : HasType Δ xβ
          (.pi (VExpr.mkAppN (VExpr.const .quot [Level.eval φ w]) [xα, xr])
            (.sort 0)) := by
        simpa [VExpr.mkAppN, inst_chain1, VExpr.liftN_zero] using t3
      have hq : HasType Δ
          (VExpr.mkAppN (VExpr.const .quotMk [Level.eval φ w]) [y1, y2, ya])
          (VExpr.mkAppN (VExpr.const .quot [Level.eval φ w]) [xα, xr]) := by
        simpa [VExpr.mkAppN, inst_chain3, inst_chain2] using t5
      have hya : HasType Δ ya y1 := by simpa [inst_chain1] using c3
      have hya' : HasType Δ ya xα := Deq.conv hya hp0
      -- the minor premise at the recursor's parameter
      have hyaD : HasType Δ ya (((VExpr.liftN 2 xα 0).inst xr 1).inst xβ 0) := by
        rw [inst_chain2]; exact hya'
      have hmkT : HasType Δ (.app xmk ya)
          (.app xβ (VExpr.mkAppN (VExpr.const .quotMk [Level.eval φ w])
            [xα, xr, ya])) := by
        simpa [VExpr.mkAppN, inst_chain1, inst_chain2, inst_chain3,
          VExpr.liftN_zero] using HasType.app t4 hyaD
      -- both sides are proofs
      have hyaL : HasType Δ ya ((VExpr.liftN 1 xα 0).inst xr 0) := by
        rw [inst_chain1]; exact hya'
      have hqmk : HasType Δ
          (VExpr.mkAppN (VExpr.const .quotMk [Level.eval φ w]) [xα, xr, ya])
          (VExpr.mkAppN (VExpr.const .quot [Level.eval φ w]) [xα, xr]) := by
        simpa [VExpr.mkAppN, quotT, lv, inst_chain1, inst_chain2,
          VExpr.liftN_zero] using
          HasType.app (HasType.app (HasType.app
            (HasType.const (Γ := Δ) (c := BConst.quotMk)
              (us := [Level.eval φ w])) t1) t2) hyaL
      have hRProp : HasType Δ (.app xβ
          (VExpr.mkAppN (VExpr.const .quotMk [Level.eval φ w]) [xα, xr, ya]))
          (.sort 0) := HasType.app hβ hqmk
      have hLProp : HasType Δ (.app xβ
          (VExpr.mkAppN (VExpr.const .quotMk [Level.eval φ w]) [y1, y2, ya]))
          (.sort 0) := HasType.app hβ hq
      have hLhs := hfitR0.appN (HasType.const (Γ := Δ) (c := BConst.quotInd)
        (us := [Level.eval φ w]))
      simp only [VExpr.inst, VExpr.liftN, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, reduceIte, inst_chain1, inst_chain2,
        VExpr.liftN_zero] at hLhs
      -- **proof irrelevance**, then β on the right-hand side
      refine Deq.trans (Deq.intro (HasType.proofIrrel hLProp hRProp hLhs
        hmkT)) (Deq.symm (Deq.trans (Deq.ofBetaSpine
          (f := quotIndRhsV (Level.eval φ w))
          (.cons t1 (.cons t2 (.cons t3 (.cons t4 (.cons ?hya .nil))))))
          ?hmid))
      case hya =>
        simp only [VExpr.inst, VExpr.liftN, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceSub, reduceIte, inst_chain3]
        exact hya'
      case hmid =>
        simp only [VExpr.inst, VExpr.liftN, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceSub, reduceIte, inst_chain1, VExpr.liftN_zero]
        exact Deq.refl
    · exact nomatch hr'


/-! ### The `Eq`-bridged types

`Quot.lift`'s and `Quot.sound`'s stored types end in the **pinned `Eq`
former applied to three arguments**, where the layer's constants
conclude at `.eqE`.  §11's law is exactly that gap, and it is consumed
here rather than assumed: `EnvTT.eq_law` is a field, so the block needs
only the checker's own guard that `Eq` is stored — which
`Setlec/Kernel/Checker.lean`'s `basisDecl` case supplies
(`unless env.find? eqName = some eqA do throw`). -/

/-- `Quot.lift`'s invariance premise as the *stored* type denotes it:
the pinned `Eq` former's valuation applied to three arguments, where
`quotInvT` has `.eqE`. -/
def quotInvV (E A r B f : VExpr) : VExpr :=
  .pi A (.pi (A.liftN 1)
    (.pi (VExpr.mkAppN (r.liftN 2) [.bvar 1, .bvar 0])
      (VExpr.mkAppN E [B.liftN 3, .app (f.liftN 3) (.bvar 2),
        .app (f.liftN 3) (.bvar 1)])))

/-- **The bridge**, once: three binders of `congrPi` over §11's law. -/
theorem quotInv_deq {env : Env} (m : EnvTT env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat)
    {Γ : List VExpr} {A r B f : VExpr}
    (hB : HasType Γ B (.sort (ψ uN)))
    (hf : HasType Γ f (arrow A B)) :
    Deq Γ (quotInvV (m.cval eqName ψ) A r B f) (quotInvT A r B f) := by
  have hlc : VExpr.liftN 3 (VExpr.liftN 1 B 0) 1
      = VExpr.liftN 1 (VExpr.liftN 3 B 0) 0 :=
    (VExpr.liftN_liftN_comm B (Nat.le_refl 0) 1 3).symm
  have hla : VExpr.liftN 2 (VExpr.liftN 1 A 0) 0 = VExpr.liftN 3 A 0 :=
    VExpr.liftN_liftN_add A 1 2 0
  refine Deq.piCod (Deq.piCod (Deq.piCod ?_))
  have hB3 : HasType (VExpr.mkAppN (VExpr.liftN 2 r 0)
        [.bvar 1, .bvar 0] :: VExpr.liftN 1 A 0 :: A :: Γ)
      (VExpr.liftN 3 B 0) (.sort (ψ uN)) :=
    hB.weakenN (.zero [VExpr.mkAppN (VExpr.liftN 2 r 0) [.bvar 1, .bvar 0],
      VExpr.liftN 1 A 0, A] rfl)
  have hf3 : HasType (VExpr.mkAppN (VExpr.liftN 2 r 0)
        [.bvar 1, .bvar 0] :: VExpr.liftN 1 A 0 :: A :: Γ)
      (VExpr.liftN 3 f 0)
      (.pi (VExpr.liftN 3 A 0) (VExpr.liftN 3 (VExpr.liftN 1 B 0) 1)) :=
    hf.weakenN (.zero [VExpr.mkAppN (VExpr.liftN 2 r 0) [.bvar 1, .bvar 0],
      VExpr.liftN 1 A 0, A] rfl)
  rw [hlc] at hf3
  have haa : HasType (VExpr.mkAppN (VExpr.liftN 2 r 0)
        [.bvar 1, .bvar 0] :: VExpr.liftN 1 A 0 :: A :: Γ)
      (.bvar 2) (VExpr.liftN 3 A 0) := HasType.bvar rfl
  have hbb : HasType (VExpr.mkAppN (VExpr.liftN 2 r 0)
        [.bvar 1, .bvar 0] :: VExpr.liftN 1 A 0 :: A :: Γ)
      (.bvar 1) (VExpr.liftN 3 A 0) := by
    have h := HasType.bvar (Γ := VExpr.mkAppN (VExpr.liftN 2 r 0)
      [.bvar 1, .bvar 0] :: VExpr.liftN 1 A 0 :: A :: Γ) (i := 1)
      (A := VExpr.liftN 1 A 0) rfl
    rwa [hla] at h
  have hfa : HasType (VExpr.mkAppN (VExpr.liftN 2 r 0)
        [.bvar 1, .bvar 0] :: VExpr.liftN 1 A 0 :: A :: Γ)
      (.app (VExpr.liftN 3 f 0) (.bvar 2)) (VExpr.liftN 3 B 0) := by
    have h := HasType.app hf3 haa
    rwa [inst_chain1] at h
  have hfb : HasType (VExpr.mkAppN (VExpr.liftN 2 r 0)
        [.bvar 1, .bvar 0] :: VExpr.liftN 1 A 0 :: A :: Γ)
      (.app (VExpr.liftN 3 f 0) (.bvar 1)) (VExpr.liftN 3 B 0) := by
    have h := HasType.app hf3 hbb
    rwa [inst_chain1] at h
  exact m.eq_law hE ψ _ _ _ _ hB3 hfa hfb


/-- `Quot.lift`'s pinned type, as it denotes: the layer's, with the
stored `Eq` former's valuation in the invariance premise. -/
def quotLiftTyV (E : VExpr) (a b : Nat) : VExpr :=
  .pi (.sort a)
    (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
      (.pi (.sort b)
        (.pi (.pi (.bvar 2) (.bvar 1))
          (.pi (quotInvV E (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
            (.pi (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3])
              (.bvar 3))))))

/-- …and its rule's right-hand side, the same telescope returning
`f a`. -/
def quotLiftRhsV (E : VExpr) (a b : Nat) : VExpr :=
  .lam (.sort a)
    (.lam (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
      (.lam (.sort b)
        (.lam (.pi (.bvar 2) (.bvar 1))
          (.lam (quotInvV E (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
            (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0)))))))

/-- The pinned `Eq` former, denoted at the level `Quot.lift`'s stored
type reads it at. -/
theorem denote_quot_eqConst {env : Env} {ci : ConstantInfo} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (w : Level)
    (hE : env.find? eqName = some eqA) (hnE : ci.name ≠ eqName) (e : Nat) :
    denote (cvalSet m.cval ci.name val) ⟨ci :: env.consts⟩ φ e
        (.const eqName [w])
      = some (m.cval eqName (Level.substFn φ [uN] [w])) := by
  rw [denote_const, Env.find?_cons, if_neg hnE, hE]
  simp only [show ([w] : List Level).length
    = eqA.toConstantVal.levelParams.length from rfl, if_true]
  rw [cvalSet_ne (Ne.symm hnE)]
  rfl

/-- **`Quot.lift`'s pinned type, denoted.** -/
theorem denote_quotLift_type {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w1 w2 : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA) :
    denote (cvalSet m.cval quotLiftA.name val) ⟨quotLiftA :: env.consts⟩ φ d
        (quotLiftA.toConstantVal.type.instantiateLevelParams
          quotLiftA.toConstantVal.levelParams [w1, w2])
      = some (quotLiftTyV (m.cval eqName (Level.substFn φ [uN] [w2]))
        (w1.eval φ) (w2.eval φ)) := by
  have hsu : Level.subst [uN, vN] [w1, w2] (.param uN) = w1 := by
    simp [Level.subst, Level.subst.go, uN]
  have hsv : Level.subst [uN, vN] [w1, w2] (.param vN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, vN]
  have hsz : Level.subst [uN, vN] [w1, w2] .zero = .zero := by
    simp [Level.subst, Level.subst.go]
  obtain ⟨hQc, -⟩ := denote_quotInd_consts m (ci := quotLiftA) (val := val)
    φ w1 hQ hM (by decide) (by decide)
  have hEc := denote_quot_eqConst m (ci := quotLiftA) (val := val) φ w2 hE
    (by decide)
  rw [show quotLiftA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "β") (.sort (.param vN))
              (Expr.forallE (Name.anonymous.str "f")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2) (.bvar 1)
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "a")
                  (Expr.forallE (Name.anonymous.str "a") (.bvar 3)
                    (Expr.forallE (Name.anonymous.str "b") (.bvar 4)
                      (Expr.forallE (Name.anonymous.str "a")
                        (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                        (.app (.app (.app (.const eqName [.param vN])
                          (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                          (.app (.bvar 3) (.bvar 1)))
                        { bi := .default }) { bi := .default })
                    { bi := .default })
                  (Expr.forallE (Name.anonymous.str "a")
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3))
                    (.bvar 3) { bi := .default })
                  { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show quotLiftA.toConstantVal.levelParams = [uN, vN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsv, hsz, denote_forallE,
    denote_sort, denote_app, denote_fvar, hQc, hEc, quotLiftTyV, quotInvV,
    VExpr.mkAppN, VExpr.liftN, Level.eval]

/-- `Quot.lift`'s single stored rule. -/
def quotLiftRule : RecRule :=
  { ctor := quotMkName, nfields := 1, ctorParams := 2, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "α") (.sort (.param uN))
      (Expr.lam (Name.anonymous.str "r")
        (Expr.forallE Name.anonymous (.bvar 0)
          (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
            { bi := .default }) { bi := .default })
        (Expr.lam (Name.anonymous.str "β") (.sort (.param vN))
          (Expr.lam (Name.anonymous.str "f")
            (Expr.forallE (Name.anonymous.str "a") (.bvar 2) (.bvar 1)
              { bi := .default })
            (Expr.lam (Name.anonymous.str "h")
              (Expr.forallE (Name.anonymous.str "a") (.bvar 3)
                (Expr.forallE (Name.anonymous.str "b") (.bvar 4)
                  (Expr.forallE (Name.anonymous.str "a")
                    (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                    (.app (.app (.app (.const eqName [.param vN])
                      (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                      (.app (.bvar 3) (.bvar 1)))
                    { bi := .default }) { bi := .default })
                { bi := .default })
              (Expr.lam (Name.anonymous.str "a") (.bvar 4)
                (.app (.bvar 2) (.bvar 0)) { bi := .default })
              { bi := .default })
            { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .default } }

theorem quotLiftA_eq :
    quotLiftA = .recInfo quotLiftA.toConstantVal 5 5 [quotLiftRule] := rfl

/-- **`Quot.lift`'s right-hand side, denoted.** -/
theorem denote_quotLift_rhs {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w1 w2 : Level)
    (hE : env.find? eqName = some eqA) :
    denote (cvalSet m.cval quotLiftA.name val) ⟨quotLiftA :: env.consts⟩ φ d
        ((RecRule.rhs quotLiftRule).instantiateLevelParams
          quotLiftA.toConstantVal.levelParams [w1, w2])
      = some (quotLiftRhsV (m.cval eqName (Level.substFn φ [uN] [w2]))
        (w1.eval φ) (w2.eval φ)) := by
  have hsu : Level.subst [uN, vN] [w1, w2] (.param uN) = w1 := by
    simp [Level.subst, Level.subst.go, uN]
  have hsv : Level.subst [uN, vN] [w1, w2] (.param vN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, vN]
  have hsz : Level.subst [uN, vN] [w1, w2] .zero = .zero := by
    simp [Level.subst, Level.subst.go]
  have hEc := denote_quot_eqConst m (ci := quotLiftA) (val := val) φ w2 hE
    (by decide)
  rw [show quotLiftA.toConstantVal.levelParams = [uN, vN] from rfl]
  simp only [quotLiftRule]
  simp [Expr.instantiateLevelParams, hsu, hsv, hsz, denote_lam,
    denote_forallE, denote_sort, denote_app, denote_fvar, hEc,
    quotLiftRhsV, quotInvV, VExpr.mkAppN, VExpr.liftN, Level.eval]


/-- **`Quot.lift`, installed.**  Its iota is the layer's `quotLiftMk`
after a congruence moves the fired major from the *constructor's*
parameters onto the *recursor's* — the parameter test again, this time
under a spine rather than at a typing. -/
theorem extendQuotLiftTT {env : Env} (m : EnvTT env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA)
    (hfresh : env.find? quotLiftName = none)
    (hwf : EnvWF ⟨quotLiftA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨quotLiftA :: env.consts⟩,
      m'.cval = cvalSet m.cval quotLiftA.name
        (fun ψ => VExpr.const .quotLift [ψ uN, ψ vN]) := by
  refine extendBasisTT m
    (val := fun ψ => VExpr.const .quotLift [ψ uN, ψ vN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotLiftA = quotLiftName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  · -- the pinned type, denoted — and the layer's constant conv'd onto it
    intro φ
    refine ⟨quotLiftTyV
      (m.cval eqName (Level.substFn φ [uN] [Level.param vN]))
      (φ uN) (φ vN), ?_, ?_⟩
    · rw [denoteClosed, ← Expr.instantiateLevelParams_self
          quotLiftA.toConstantVal.levelParams quotLiftA.toConstantVal.type,
        show quotLiftA.toConstantVal.levelParams.map Level.param
          = [Level.param uN, Level.param vN] from rfl,
        denote_quotLift_type m φ 0 (.param uN) (.param vN) hQ hM hE]
      simp [Level.eval]
    · refine Deq.conv HasType.const ?_
      have hψ : Level.substFn φ [uN] [Level.param vN] uN = φ vN := rfl
      refine Deq.piCod (Deq.piCod (Deq.piCod (Deq.piCod
        (Deq.pi (Deq.symm (quotInv_deq m hE
          (Level.substFn φ [uN] [Level.param vN])
          (Γ := [VExpr.pi (.bvar 2) (.bvar 1), VExpr.sort (φ vN),
            VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
            VExpr.sort (φ uN)])
          (A := .bvar 3) (r := .bvar 2) (B := .bvar 1) (f := .bvar 0)
          ?_ ?_)) Deq.refl))))
      · rw [hψ]
        have h := HasType.bvar (Γ := [VExpr.pi (.bvar 2) (.bvar 1),
          VExpr.sort (φ vN), VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]) (i := 1) (A := VExpr.sort (φ vN)) rfl
        simpa using h
      · have h := HasType.bvar (Γ := [VExpr.pi (.bvar 2) (.bvar 1),
          VExpr.sort (φ vN), VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]) (i := 0)
          (A := VExpr.pi (.bvar 2) (.bvar 1)) rfl
        simpa [arrow, VExpr.liftN] using h
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨quotMkA.toConstantVal, 2, 1, hM⟩
    · exact nomatch hr'
  · -- the iota rule
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
      refine ⟨_, denote_quotLift_rhs m
        (val := fun ψ => VExpr.const .quotLift [ψ uN, ψ vN]) φ d w1 w2
        hE, ?_⟩
      intro cvj cnP cnF hfj Δ usj xs ys TV TVj restR restC hxs hys husj hlev
        hpar _ _ hdTV hdTVj hfitR hfitC
      have hMu := hM
      simp only [quotMkName, quotName] at hMu
      rw [Env.find?_cons, if_neg (by decide), hMu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain ⟨y1, y2, ya, rfl⟩ : ∃ a b c, ys = [a, b, c] := by
        match ys, hys with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      obtain ⟨xα, xr, xβ, xf, xh, rfl⟩ :
          ∃ a b c e g, xs = [a, b, c, e, g] := by
        match xs, hxs with
        | [a, b, c, e, g], _ => exact ⟨a, b, c, e, g, rfl⟩
      obtain ⟨v1, rfl⟩ : ∃ a, usj = [a] := by
        match usj, husj with
        | [a], _ => exact ⟨a, rfl⟩
      have hlps : quotMkA.toConstantVal.levelParams = [uN] := rfl
      have hlu : Level.eval φ v1 = Level.eval φ w1 := by
        have h := congrFun hlev uN
        rw [hlps] at h
        simpa [recFireComparands, Level.substFn, Level.subst, Level.subst.go,
          uN, vN] using h
      have hctor : cvalSet m.cval quotLiftA.name
          (fun ψ => VExpr.const .quotLift [ψ uN, ψ vN])
          ((Name.anonymous.str "Quot").str "mk")
          (Level.substFn φ quotMkA.toConstantVal.levelParams [v1])
          = VExpr.const .quotMk [Level.eval φ w1] := by
        rw [cvalSet_ne (by decide)]
        have hv := cval_pinned m (n := quotMkName) (by decide)
          (by rw [hM]; rfl)
          (Level.substFn φ quotMkA.toConstantVal.levelParams [v1])
          (t := VExpr.const .quotMk
            [Level.substFn φ quotMkA.toConstantVal.levelParams [v1] uN])
          (by simp +decide [pinnedDirectT])
        simp only [quotMkName, quotName] at hv
        rw [hv]
        simp only [show Level.substFn φ quotMkA.toConstantVal.levelParams
          [v1] uN = Level.eval φ v1 from by
            rw [hlps]; simp [Level.substFn, uN], hlu]
      obtain rfl : TV = _ :=
        (Option.some.inj ((denote_quotLift_type m
          (val := fun ψ => VExpr.const .quotLift [ψ uN, ψ vN]) φ d w1 w2
          hQ hM hE).symm.trans hdTV)).symm
      obtain rfl : TVj = _ :=
        (Option.some.inj ((denote_quotMk_type m (ci := quotLiftA)
          (val := fun ψ => VExpr.const .quotLift [ψ uN, ψ vN]) φ d v1
          hQ hM (by decide) (by decide)).symm.trans hdTVj)).symm
      rw [hctor] at hfitR
      rw [hlu] at hfitC
      rw [cvalSet_self, hctor]
      cases hfitR with | cons t1 hfitR =>
      cases hfitR with | cons t2 hfitR =>
      cases hfitR with | cons t3 hfitR =>
      cases hfitR with | cons t4 hfitR =>
      cases hfitR with | cons t5 hfitR =>
      cases hfitR with | cons t6 hfitR =>
      cases hfitC with | cons c1 hfitC =>
      cases hfitC with | cons c2 hfitC =>
      cases hfitC with | cons c3 hfitC =>
      have hp0 : Deq Δ y1 xα := by
        have h := hpar rfl 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
        simpa using h
      have hp1 : Deq Δ y2 xr := by
        have h := hpar rfl 1 (by decide) (by decide)
        simpa using h
      -- the six telescope entries, cleaned
      have hr : HasType Δ xr (relT xα) := by
        simpa [relT, VExpr.liftN_zero] using t2
      have hf : HasType Δ xf (arrow xα xβ) := by
        simpa [arrow, inst_chain2] using t4
      have hh0 : HasType Δ xh
          (quotInvV (m.cval eqName (Level.substFn φ [uN] [w2]))
            xα xr xβ xf) := by
        simpa [quotInvV, VExpr.mkAppN, inst_chain1, inst_chain2, inst_chain3,
          inst_absorb21, inst_absorb32, inst_absorb43, VExpr.liftN_zero,
          VExpr.inst_eq_self_of_closed (m.cval_closed eqName
            (Level.substFn φ [uN] [w2]))] using t5
      have hh : HasType Δ xh (quotInvT xα xr xβ xf) :=
        Deq.conv hh0 (quotInv_deq m hE _ t3 hf)
      have hya : HasType Δ ya y1 := by simpa [inst_chain1] using c3
      have hya' : HasType Δ ya xα := Deq.conv hya hp0
      -- the fired major, moved onto the recursor's parameters
      have hcong : Deq Δ
          (VExpr.mkAppN (VExpr.const .quotMk [Level.eval φ w1]) [y1, y2, ya])
          (VExpr.mkAppN (VExpr.const .quotMk [Level.eval φ w1]) [xα, xr, ya]) :=
        Deq.app (Deq.app (Deq.appArg hp0) hp1) Deq.refl
      refine Deq.trans (Deq.appArg hcong) (Deq.trans
        (Deq.intro (HasType.quotLiftMk (T := xβ) t1 hr t3 hf hh hya'))
        (Deq.symm (Deq.trans (Deq.ofBetaSpine
          (f := quotLiftRhsV (m.cval eqName (Level.substFn φ [uN] [w2]))
            (Level.eval φ w1) (Level.eval φ w2))
          (.cons t1 (.cons t2 (.cons t3 (.cons t4 (.cons t5
            (.cons ?hya .nil))))))) ?hmid)))
      case hya =>
        simp only [VExpr.inst, VExpr.liftN, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceSub, reduceIte, inst_chain4]
        exact hya'
      case hmid =>
        simp only [VExpr.inst, VExpr.liftN, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceSub, reduceIte, inst_chain2, VExpr.liftN_zero]
        exact Deq.refl
    · exact nomatch hr'


/-- `Quot.sound`'s pinned type, as it denotes. -/
def quotSoundTyV (E : VExpr) (a : Nat) : VExpr :=
  .pi (.sort a)
    (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
      (.pi (.bvar 1)
        (.pi (.bvar 2)
          (.pi (VExpr.mkAppN (.bvar 2) [.bvar 1, .bvar 0])
            (VExpr.mkAppN E
              [VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3],
               VExpr.mkAppN (VExpr.const .quotMk [a])
                 [.bvar 4, .bvar 3, .bvar 2],
               VExpr.mkAppN (VExpr.const .quotMk [a])
                 [.bvar 4, .bvar 3, .bvar 1]])))))

/-- **`Quot.sound`'s pinned type, denoted.** -/
theorem denote_quotSound_type {env : Env} (m : EnvTT env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA) :
    denote (cvalSet m.cval quotSoundA.name val) ⟨quotSoundA :: env.consts⟩ φ d
        (quotSoundA.toConstantVal.type.instantiateLevelParams
          quotSoundA.toConstantVal.levelParams [w])
      = some (quotSoundTyV (m.cval eqName (Level.substFn φ [uN] [w]))
        (w.eval φ)) := by
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go, uN]
  have hsz : Level.subst [uN] [w] .zero = .zero := by
    simp [Level.subst, Level.subst.go]
  obtain ⟨hQc, hMc⟩ := denote_quotInd_consts m (ci := quotSoundA) (val := val)
    φ w hQ hM (by decide) (by decide)
  have hEc := denote_quot_eqConst m (ci := quotSoundA) (val := val) φ w hE
    (by decide)
  rw [show quotSoundA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "b") (.bvar 2)
                (Expr.forallE Name.anonymous
                  (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const eqName [.param uN])
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 2)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 1)))
                  { bi := .default }) { bi := .implicit })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show quotSoundA.toConstantVal.levelParams = [uN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsz, denote_forallE, denote_sort,
    denote_app, denote_fvar, hQc, hMc, hEc, quotSoundTyV, VExpr.mkAppN,
    Level.eval]

/-- **`Quot.sound`, installed** — the block's, and the basis's, only
stored *axiom*.  Its type is `Eq`-bridged like `Quot.lift`'s, and the
bridge is the same five `congrPi`s over §11's law; the axiom itself
needs nothing else, because the layer carries `.quotSound` as a
constant with exactly this type. -/
theorem extendQuotSoundTT {env : Env} (m : EnvTT env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA)
    (hfresh : env.find? quotSoundName = none)
    (hwf : EnvWF ⟨quotSoundA :: env.consts⟩) :
    ∃ m' : EnvTT ⟨quotSoundA :: env.consts⟩,
      m'.cval = cvalSet m.cval quotSoundA.name
        (fun ψ => VExpr.const .quotSound [ψ uN]) := by
  refine extendBasisTT m (val := fun ψ => VExpr.const .quotSound [ψ uN])
    (basisEtaVacuous m (by decide)) (basisUnitVacuous m (by decide))
    (basisResidVacuous (by decide))
    (fun h => nomatch h)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotSoundA = quotSoundName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ _ hmem => absurd hmem (by decide)) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨quotSoundTyV
      (m.cval eqName (Level.substFn φ [uN] [Level.param uN])) (φ uN),
      ?_, ?_⟩
    · rw [denoteClosed, ← Expr.instantiateLevelParams_self
          quotSoundA.toConstantVal.levelParams quotSoundA.toConstantVal.type,
        show quotSoundA.toConstantVal.levelParams.map Level.param
          = [Level.param uN] from rfl,
        denote_quotSound_type m φ 0 (.param uN) hQ hM hE]
      simp [Level.eval]
    · refine Deq.conv HasType.const ?_
      refine Deq.piCod (Deq.piCod (Deq.piCod (Deq.piCod (Deq.piCod ?_))))
      have hα : HasType [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]
          (.bvar 4) (.sort (φ uN)) := by
        have h := HasType.bvar (Γ := [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)])
          (i := 4) (A := VExpr.sort (φ uN)) rfl
        simpa using h
      have hr : HasType [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]
          (.bvar 3) (.pi (.bvar 4) (.pi (.bvar 5) (.sort 0))) := by
        have h := HasType.bvar (Γ := [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)])
          (i := 3) (A := VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0))) rfl
        simpa [VExpr.liftN] using h
      have haa : HasType [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]
          (.bvar 2) (.bvar 4) := by
        have h := HasType.bvar (Γ := [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)])
          (i := 2) (A := VExpr.bvar 1) rfl
        simpa [VExpr.liftN] using h
      have hbb : HasType [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]
          (.bvar 1) (.bvar 4) := by
        have h := HasType.bvar (Γ := [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)])
          (i := 1) (A := VExpr.bvar 2) rfl
        simpa [VExpr.liftN] using h
      have hQty : HasType [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]
          (VExpr.mkAppN (VExpr.const .quot [φ uN]) [.bvar 4, .bvar 3])
          (.sort (φ uN)) :=
        HasType.app (HasType.app (HasType.const (c := BConst.quot)
          (us := [φ uN])) hα) hr
      have hmk1 : HasType [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]
          (VExpr.mkAppN (VExpr.const .quotMk [φ uN])
            [.bvar 4, .bvar 3, .bvar 2])
          (VExpr.mkAppN (VExpr.const .quot [φ uN]) [.bvar 4, .bvar 3]) :=
        HasType.app (HasType.app (HasType.app (HasType.const
          (c := BConst.quotMk) (us := [φ uN])) hα) hr) haa
      have hmk2 : HasType [VExpr.mkAppN (VExpr.bvar 2) [VExpr.bvar 1, VExpr.bvar 0],
          VExpr.bvar 2, VExpr.bvar 1,
          VExpr.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)),
          VExpr.sort (φ uN)]
          (VExpr.mkAppN (VExpr.const .quotMk [φ uN])
            [.bvar 4, .bvar 3, .bvar 1])
          (VExpr.mkAppN (VExpr.const .quot [φ uN]) [.bvar 4, .bvar 3]) :=
        HasType.app (HasType.app (HasType.app (HasType.const
          (c := BConst.quotMk) (us := [φ uN])) hα) hr) hbb
      exact Deq.symm (m.eq_law hE (Level.substFn φ [uN] [Level.param uN])
        _ _ _ _ hQty hmk1 hmk2)

/-- **The `Quot` block, installed.**  Five constants: a stored
inductive, its constructor, two stored recursors and — uniquely — a
stored *axiom*.

`Eq`'s presence is a hypothesis, and it is the **checker's own** guard
that supplies it: `Setlec/Kernel/Checker.lean`'s `basisDecl` case runs
`unless env.find? eqName = some eqA do throw` before folding this
block, precisely because two of its types mention the pinned equality
former.

*The block that dodges nothing is the block that audits the
invariant.*  `Quot` was scheduled last on cost grounds; it turned out
to be the only block with constructor parameters, a kept field, no
projections and no eta — and so the only one that could not route
around `hheadRec`'s missing parameter premise (§8.2's fifth instance).
Four blocks passed over the defect; the fifth could not. -/
theorem declBasisTT_quotK {env env₁ : Env} (m : EnvTT env)
    (hE : env.find? eqName = some eqA)
    (h : BasisChain env BasisKind.quotK.declsA env₁) :
    Nonempty (EnvTT env₁) := by
  rw [show BasisKind.quotK.declsA
    = [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA] from rfl] at h
  cases h with
  | cons h1 h =>
  cases h with
  | cons h2 h =>
  cases h with
  | cons h3 h =>
  cases h with
  | cons h4 h =>
  cases h with
  | cons h5 h =>
  cases h with
  | nil =>
  have hwf1 : EnvWF ⟨quotA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, -⟩ := extendQuotTT m h1 hwf1
  have hQ1 : (⟨quotA :: env.consts⟩ : Env).find? quotName = some quotA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hE1 : (⟨quotA :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE
  have hwf2 : EnvWF ⟨quotMkA :: quotA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?res2, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res2 =>
    show Expr.constsResolve _ quotMkA.toConstantVal.type = true
    have hf : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotName
        = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ1
    rw [show quotMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (.app (.app (.const quotName [.param uN]) (.bvar 2))
                (.bvar 1)) { bi := .default })
            { bi := .default })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m2, -⟩ := extendQuotMkTT m1 hQ1 h2 hwf2
  have hQ2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotName
      = some quotA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hQ1
  have hM2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hE2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? eqName
      = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE1
  have hwf3 : EnvWF ⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :=
    EnvWF.cons hwf2 ⟨rfl, rfl, ?res3, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec3,
      (fun _ _ heq => nomatch heq)⟩
  case res3 =>
    show Expr.constsResolve _ quotLiftA.toConstantVal.type = true
    have hfQ : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
        quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ2
    have hfE : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
        eqName = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE2
    rw [show quotLiftA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "β") (.sort (.param vN))
              (Expr.forallE (Name.anonymous.str "f")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2) (.bvar 1)
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "a")
                  (Expr.forallE (Name.anonymous.str "a") (.bvar 3)
                    (Expr.forallE (Name.anonymous.str "b") (.bvar 4)
                      (Expr.forallE (Name.anonymous.str "a")
                        (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                        (.app (.app (.app (.const eqName [.param vN])
                          (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                          (.app (.bvar 3) (.bvar 1)))
                        { bi := .default }) { bi := .default })
                    { bi := .default })
                  (Expr.forallE (Name.anonymous.str "a")
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3))
                    (.bvar 3) { bi := .default })
                  { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfQ, hfE]
  case rec3 =>
    intro cv mI rP rules heq
    injection heq with h1' _ _ h4'
    subst h1'; subst h4'
    have hfQ : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
        quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ2
    have hfE : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
        eqName = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE2
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨rfl, rfl, by
        show Expr.constsResolve _ (RecRule.rhs quotLiftRule) = true
        simp [Expr.constsResolve, quotLiftRule, hfQ, hfE], rfl,
        fun lvls pins heqf => nomatch heqf⟩
    · exact nomatch hr'
  obtain ⟨m3, -⟩ := extendQuotLiftTT m2 hQ2 hM2 hE2 h3 hwf3
  have hQ3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
      quotName = some quotA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hQ2
  have hM3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
      quotMkName = some quotMkA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hM2
  have hE3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
      eqName = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE2
  have hwf4 : EnvWF ⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
      env.consts⟩ :=
    EnvWF.cons hwf3 ⟨rfl, rfl, ?res4, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec4,
      (fun _ _ heq => nomatch heq)⟩
  case res4 =>
    show Expr.constsResolve _ quotIndA.toConstantVal.type = true
    have hfQ : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ3
    have hfM : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotMkName = some quotMkA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hM3
    rw [show quotIndA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "a")
                (.app (.app (.const quotName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.sort .zero) { bi := .default })
              (Expr.forallE (Name.anonymous.str "mk")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2)
                  (.app (.bvar 1)
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 3)) (.bvar 2)) (.bvar 0)))
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "q")
                  (.app (.app (.const quotName [.param uN]) (.bvar 3))
                    (.bvar 2))
                  (.app (.bvar 2) (.bvar 0)) { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfQ, hfM]
  case rec4 =>
    intro cv mI rP rules heq
    injection heq with h1' _ _ h4'
    subst h1'; subst h4'
    have hfQ : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ3
    have hfM : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotMkName = some quotMkA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hM3
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨rfl, rfl, by
        show Expr.constsResolve _ (RecRule.rhs quotIndRule) = true
        simp [Expr.constsResolve, quotIndRule, hfQ, hfM], rfl,
        fun lvls pins heqf => nomatch heqf⟩
    · exact nomatch hr'
  obtain ⟨m4, -⟩ := extendQuotIndTT m3 hQ3 hM3 h4 hwf4
  have hQ4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
      env.consts⟩ : Env).find? quotName = some quotA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hQ3
  have hM4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
      env.consts⟩ : Env).find? quotMkName = some quotMkA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hM3
  have hE4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
      env.consts⟩ : Env).find? eqName = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE3
  have hwf5 : EnvWF ⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA ::
      quotA :: env.consts⟩ :=
    EnvWF.cons hwf4 ⟨rfl, rfl, ?res5, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res5 =>
    show Expr.constsResolve _ quotSoundA.toConstantVal.type = true
    have hfQ : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ4
    have hfM : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotMkName = some quotMkA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hM4
    have hfE : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? eqName = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE4
    rw [show quotSoundA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "b") (.bvar 2)
                (Expr.forallE Name.anonymous
                  (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const eqName [.param uN])
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 2)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 1)))
                  { bi := .default }) { bi := .implicit })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfQ, hfM, hfE]
  obtain ⟨m5, -⟩ := extendQuotSoundTT m4 hQ4 hM4 hE4 h5 hwf5
  exact ⟨m5⟩


/-! ## The dispatch

`checkDecl`'s `basisDecl` case is a guard and a fold; the transpose is
the same guard and `foldlM_installBasisDecl_inv`, then one block lemma
per kind.  Nothing else belongs here — which is why the six blocks
above are each a *theorem* rather than a case of one long proof. -/

/-- **`DeclBasisTT`, discharged.** -/
theorem declBasisTT {F : Nat} : DeclBasisTT F := by
  intro env env₁ kind h m
  have hsplit : (kind = .quotK → env.find? eqName = some eqA) ∧
      kind.declsA.foldlM (installBasisDecl (m := CheckM)) env = .ok env₁ := by
    simp only [checkDecl, Bind.bind, Except.bind, pure, Except.pure] at h
    by_cases hk : kind = .quotK
    · subst hk
      by_cases hEq : env.find? eqName = some eqA
      · simp only [hEq, if_true, reduceIte] at h
        exact ⟨fun _ => hEq, h⟩
      · simp [hEq] at h
    · simp only [if_neg hk] at h
      exact ⟨fun hh => absurd hh hk, h⟩
  obtain ⟨hEq, hfold⟩ := hsplit
  have hchain := foldlM_installBasisDecl_inv _ hfold
  cases kind with
  | eqK => exact declBasisTT_eqK m hchain
  | natK => exact declBasisTT_natK m hchain
  | psigmaK => exact declBasisTT_psigmaK m hchain
  | punitK => exact declBasisTT_punitK m hchain
  | emptyK => exact declBasisTT_emptyK m hchain
  | quotK => exact declBasisTT_quotK m (hEq rfl) hchain


end Setlec.TTVerify

