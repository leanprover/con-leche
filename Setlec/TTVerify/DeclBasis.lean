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


end Setlec.TTVerify

