import Setlec.SetR.Install.ValueKinds
import Setlec.Verify.OfReducePin

/-!
# The `axiom` case (task #148, T5)

Transpose of `Setlec/TTVerify/DeclAxiom.lean`: the tolerated-skip
branch is one line (the environment never moves), and the three
installing branches owe a **closed inhabitant of the axiom's denoted
pinned type** — there is no value to denote, so the valuation is
chosen outright (`cvalWith`) and the model must supply the membership.

The three keys mirror the TT lane's split (`StdAxiomKeyTT` /
`TrustCompilerKeyTT` / `OfReduceKeyTT`), with `HasType [] (V ψ) t`
replaced by the membership-plus-truthfulness pair the `EnvS` fields
want.  `trustCompiler` is discharged here (the pin fixes the type to
the stored `True` on the nose, and the stored `True.intro`'s
`mem_type` is the inhabitant); the standard axioms and the
`ofReduce*` pair are stated as obligations and discharged in their
own modules (the `Model/StdAxioms.lean` / `Model/TrustAxioms.lean`
re-hangs).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## Small [set] helpers -/

/-- `eraseNames` fixes a bare constant (local twin of the TT lane's
`eraseNames_const_inv`). -/
theorem eraseNames_const_invS {e : Expr} {n : Name} {us : List Level}
    (h : e.eraseNames = .const n us) : e = .const n us := by
  cases e <;> simp only [Expr.eraseNames] at h <;> first
    | exact h
    | exact nomatch h

/-- `stdAxiomOk` accepts only the two standard axioms' names (local
twin of the TT lane's `stdAxiomOk_name`). -/
theorem stdAxiomOk_nameS {env : Env} {cvA : ConstantVal}
    (h : stdAxiomOk env cvA = true) :
    cvA.name = propextName ∨ cvA.name = choiceName := by
  by_cases h1 : cvA.name = propextName
  · exact Or.inl h1
  by_cases h2 : cvA.name = choiceName
  · exact Or.inr h2
  rw [stdAxiomOk, if_neg h1, if_neg h2] at h
  exact nomatch h

/-- A stored level-monomorphic constant's bare reference denotes to its
valuation. -/
theorem denote_const_nolevelsS {env : Env} {cval : TConstVal} {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (ψ : Name → Nat) (d : Nat) :
    denote cval env ψ d (.const n []) = some (cval n ψ) := by
  rw [denote_const, hf]
  dsimp only
  rw [if_pos (by rw [hlp]; rfl), hlp,
    show Level.substFn ψ [] [] = ψ from funext fun _ => rfl]

/-- A stored constant's valuation inhabits its denoted type, which is
truthful — `mem_type` keyed on a `find?` hit. -/
theorem EnvS.cval_memType {env : Env} (m : EnvS V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci) (ψ : Name → Nat) :
    ∃ t, denoteClosed m.cval env ψ ci.toConstantVal.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.cval n ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t := by
  obtain ⟨t, ht, hlaw⟩ := m.mem_type ci (Env.find?_mem hf) ψ
  refine ⟨t, ht, fun ρ => ?_⟩
  have := hlaw ρ
  rwa [Env.find?_name hf] at this

/-! ## The axiom install -/

/-- **The axiom install** — transpose of `extendAxiomTT`: the
valuation is chosen outright; `defn_eq` and `thm_ok` are vacuous at an
`axiomInfo`, so the install is strictly smaller than the value one. -/
theorem extendAxiomS {env : Env} (m : EnvS V env) {cv : ConstantVal}
    {Vf : (Name → Nat) → VExpr}
    (hfresh : env.find? cv.name = none)
    (hwf : EnvWF ⟨ConstantInfo.axiomInfo cv :: env.consts⟩)
    (hVcl : ∀ ψ : Name → Nat, VExpr.Closed (Vf ψ))
    (hVp : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂)
    (hVannot : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ))
    (hkey : ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env ψ cv.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t)
    (hnres : reservedBasisNames.contains cv.name = false)
    (hnred : cv.name ∉ reduceOpNames) :
    Nonempty (EnvS V ⟨ConstantInfo.axiomInfo cv :: env.consts⟩) := by
  have hi : Installs env m.cval (cvalWith m.cval cv.name Vf)
      (.axiomInfo cv) :=
    Installs.of_fresh hfresh (fun n hn => (cvalWith_ne hn).symm)
  refine ⟨EnvS.cons m hi hwf ?_ ?_ ?_ ?_ (fun _ _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq) ?_
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    ?_ (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq) ?_ ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ heq => nomatch heq) ?_⟩
  · intro ψ
    show VExpr.Closed (cvalWith m.cval cv.name Vf cv.name ψ)
    rw [cvalWith_self]; exact hVcl ψ
  · intro φ₁ φ₂ hp
    show cvalWith m.cval cv.name Vf cv.name φ₁
      = cvalWith m.cval cv.name Vf cv.name φ₂
    rw [cvalWith_self]
    exact hVp φ₁ φ₂ hp
  · intro ψ ρ
    show AnnotOkV V ρ (cvalWith m.cval cv.name Vf cv.name ψ)
    rw [cvalWith_self]
    exact hVannot ψ ρ
  · intro φ
    obtain ⟨t, ht, hd⟩ := hkey φ
    refine ⟨t, hi.denoteUp ht, ?_⟩
    show ∀ ρ : Nat → V,
      interp V ρ (cvalWith m.cval cv.name Vf cv.name φ) ∈ˢ interp V ρ t ∧
      AnnotOkV V ρ t
    rw [cvalWith_self]
    exact hd
  · intro hE
    have : reservedBasisNames.contains emptyName = false := by
      rw [show emptyName = cv.name from hE.symm]; exact hnres
    exact nomatch this
  · intro T cvT caps hf hcape hres hfam hpart
    rcases hpart with hT | hC | ⟨j, hj, hP⟩
    · rw [hT, Env.find?_cons, if_pos rfl] at hf; exact nomatch hf
    · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [hC, Env.find?_cons, if_pos rfl] at hfC; exact nomatch hfC
    · obtain ⟨-, -, hfP⟩ := hfam
      obtain ⟨cvP, mI, rP, rules, hfPj⟩ := hfP j hj
      rw [hP, Env.find?_cons, if_pos rfl] at hfPj; exact nomatch hfPj
  · intro hE
    rw [show (ConstantInfo.axiomInfo cv).name = cv.name from rfl] at hE
    rw [hE] at hnres
    exact nomatch hnres
  · intro hres
    rw [show (ConstantInfo.axiomInfo cv).name = cv.name from rfl] at hres
    rw [hres] at hnres
    exact nomatch hnres
  · intro cv2 heq hmem
    exact absurd hmem hnred

/-! ## The three keys -/

/-- The two standard axioms are inhabited (`propext` through the
pinned `Iff` family, `Classical.choice` through the pinned
`Nonempty`) — the `Model/StdAxioms.lean` re-hang's interface. -/
def StdAxiomKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → env.find? cvA.name = none →
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t

/-- The `ofReduce*` axioms are inhabited: the identity certificate
(`reduce_ops`) makes the hypothesis be the conclusion — the
`Model/TrustAxioms.lean` re-hang's interface. -/
def OfReduceKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {cvA : ConstantVal},
    ofReduceAxOk env cvA = true →
    (cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName) →
    env.find? cvA.name = none →
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t

/-! ## `Lean.trustCompiler`, discharged

The smallest key, mirroring `trustCompilerKeyTT`: the pin fixes the
axiom's type to the stored `True` on the nose, so the witness is the
stored `True.intro`'s valuation and the membership is its own
`mem_type` (whose denoted type is the same bare constant). -/

/-- **The `trustCompiler` key.** -/
theorem trustCompilerKeyS {env : Env} (m : EnvS V env)
    {cvA : ConstantVal} (hok : trustCompilerOk env cvA = true)
    (_hname : cvA.name = trustCompilerName)
    (_hfresh : env.find? cvA.name = none) :
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      ∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t := by
  simp only [trustCompilerOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hT, hTi⟩, hA⟩ := hok
  cases hfT : env.find? trueName with
  | none => rw [hfT] at hT; exact nomatch hT
  | some ciT =>
  cases hfTi : env.find? trueIntroName with
  | none => rw [hfTi] at hTi; exact nomatch hTi
  | some ciTi =>
  rw [hfT] at hT
  rw [hfTi] at hTi
  have hlpT : ciT.toConstantVal.levelParams = [] := by
    cases ciT with
    | indInfo cvT caps =>
      simp only [ConstantVal.matchesPin, Bool.and_eq_true,
        decide_eq_true_eq] at hT
      exact hT.1.2
    | _ => exact nomatch hT
  obtain ⟨hlpTi, htyTi⟩ : ciTi.toConstantVal.levelParams = [] ∧
      ciTi.toConstantVal.type = .const trueName [] := by
    cases ciTi with
    | ctorInfo cvTi nP nF =>
      match nP, nF, hTi with
      | 0, 0, hTi =>
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hTi
        exact ⟨hTi.1.2, eraseNames_const_invS hTi.2⟩
    | _ => exact nomatch hTi
  have htyA : cvA.type = .const trueName [] := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hA
    exact eraseNames_const_invS hA.2
  refine ⟨fun ψ => m.cval trueIntroName ψ, fun ψ => m.cval_closed _ _,
    ?_, fun ψ ρ => m.annot_okV _ _ ρ, fun ψ => ?_⟩
  · intro φ₁ φ₂ _
    exact m.val_params trueIntroName ciTi hfTi φ₁ φ₂ (by
      rw [hlpTi]; intro p hp; exact nomatch hp)
  · obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfTi ψ
    rw [htyTi] at ht
    rw [show denoteClosed m.cval env ψ (Expr.const trueName [])
        = denote m.cval env ψ 0 (.const trueName []) from rfl,
      denote_const_nolevelsS hfT hlpT ψ 0] at ht
    obtain rfl := Option.some.inj ht
    refine ⟨m.cval trueName ψ, ?_, hlaw⟩
    rw [htyA]
    show denote m.cval env ψ 0 (.const trueName []) = _
    rw [denote_const_nolevelsS hfT hlpT ψ 0]

/-! ## The guard chain -/

/-- An accepted `axiom` extends the invariant, given the two remaining
keys.  The tolerated skip installs nothing and owes nothing. -/
theorem declAxiomS (hstd : StdAxiomKeyS V) (hofr : OfReduceKeyS V)
    {μ : CheckMode} {F : Nat} {env env₂ : Env} {cv : ConstantVal}
    (m : EnvS V env) (h : DeclAxiomR μ F env m.cval cv env₂) :
    Nonempty (EnvS V env₂) := by
  obtain ⟨type', hcv, hbranch⟩ := h
  obtain ⟨hfind, hres, hpshape, hnd, hlbt, hitf, hann, htp, htr, hfrontT⟩ :=
    hcv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none := Option.isNone_iff_eq_none.mp hfind
  have hwfc : EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨htf', htp, Expr.constsResolve_mono htr, hbt',
      ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 value2 heq; exact nomatch heq
  have hgo : ∀ (Vf : (Name → Nat) → VExpr),
      (∀ ψ, VExpr.Closed (Vf ψ)) →
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cv.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) →
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) →
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ type' = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t) →
      cv.name ∉ reduceOpNames →
      Nonempty (EnvS V ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
        env.consts⟩) := by
    intro Vf hVcl hVp hVannot hkey hnr
    exact extendAxiomS m (Vf := Vf) hfresh hwfc hVcl hVp hVannot hkey
      hres hnr
  rcases hbranch with ⟨hstdok, rfl⟩ | ⟨hnameTC, htcok, rfl⟩ |
    ⟨hofn, hofok, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey⟩ := hstd m hstdok hfresh
    exact hgo Vf hVcl hVp hVannot hkey
      (by rcases stdAxiomOk_nameS hstdok with hh | hh <;> rw [hh] <;> decide)
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey⟩ :=
      trustCompilerKeyS m htcok hnameTC hfresh
    exact hgo Vf hVcl hVp hVannot hkey (by rw [hnameTC]; decide)
  · obtain ⟨Vf, hVcl, hVp, hVannot, hkey⟩ := hofr m hofok hofn hfresh
    exact hgo Vf hVcl hVp hVannot hkey
      (by rcases hofn with hh | hh <;> rw [hh] <;> decide)
  · exact ⟨m⟩


/-- The equality former's valuation at the pinned level `1`. -/
def eqVS {env : Env} (m : EnvS V env) (ψ : Name → Nat) : VExpr :=
  m.cval eqName
    (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])

/-- **The pinned `ofReduce` type, denoted.**  The `EnvS` restatement
of `denote_ofReducePin`: it used its `EnvTT` only through
`denote_const_nolevels`. -/
theorem denote_ofReducePinS {env : Env} (m : EnvS V env) {n : Name}
    (hn : n = ofReduceNatName ∨ n = ofReduceBoolName)
    {ciE : ConstantInfo} {cvR : ConstantVal}
    (hfE : env.find? (reduceElemName (ofReduceOp n)) = some ciE)
    (hlpE : ciE.toConstantVal.levelParams = [])
    (hfR : env.find? (ofReduceOp n) = some (.axiomInfo cvR))
    (hlpR : cvR.levelParams = [])
    (hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    denote m.cval env ψ 0 (ofReducePinA n).type =
      some (.pi (m.cval (reduceElemName (ofReduceOp n)) ψ)
        (.pi (m.cval (reduceElemName (ofReduceOp n)) ψ)
          (.pi (VExpr.mkAppN (eqVS m ψ)
              [m.cval (reduceElemName (ofReduceOp n)) ψ,
               .app (m.cval (ofReduceOp n) ψ) (.bvar 1), .bvar 0])
            (VExpr.mkAppN (eqVS m ψ)
              [m.cval (reduceElemName (ofReduceOp n)) ψ,
               .bvar 2, .bvar 1])))) := by
  have hE : ∀ d, denote m.cval env ψ d
      (.const (reduceElemName (ofReduceOp n)) [])
      = some (m.cval (reduceElemName (ofReduceOp n)) ψ) :=
    fun d => denote_const_nolevelsS hfE hlpE ψ d
  have hR : ∀ d, denote m.cval env ψ d (.const (ofReduceOp n) [])
      = some (m.cval (ofReduceOp n) ψ) :=
    fun d => denote_const_nolevelsS hfR hlpR ψ d
  have hQ : ∀ d, denote m.cval env ψ d (.const eqName [.succ .zero])
      = some (eqVS m ψ) := by
    intro d
    rw [denote_const, hEq, eqVS]
    exact if_pos rfl
  rw [ofReducePin_type hn]
  simp [denote_forallE, hE, Expr.instantiate1, denote_app, denote_fvar,
    Expr.mkAppN, VExpr.mkAppN, hQ, hR]

end Setlec.SetR
