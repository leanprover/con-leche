import Setlec.TTVerify.DeclStep

/-!
# The value-carrying installs

`def`, `theorem` and `opaque` are the same install: a checked constant
whose *value* is checked against its type, stored, and — this is the
whole content on the bridge side — **valued by the value's
denotation**.

That choice is forced, not designed.  `EnvTT`'s `defn_eq` and `thm_ok`
say a stored definition's valuation *is* its body's denotation, so the
install has no freedom; and once it is made, `has_type` for the new
constant is exactly the inference claim at the checked value, with the
`defeq` verdict converting it to the declared type.  `extendValueTT`
below packages that once and the three kinds differ only in which
`ConstantInfo` they store and which of `defn_eq` / `thm_ok` is
non-vacuous.

## Duplicated inversions

`checkConstantVal_inv` and the `fueledOps` projection equations are
restated here.  They are `V`-free and live in `Setlec/Model/Extend/
Inversions.lean`, whose *whole* content is `V`-free — the sixth member
of the misfiled class named at `EtaFamilyStoredT`, and the clearest one
yet: the file's own docstring says "small syntactic inversion lemmas".
Importing it would drag `Setlec/Model/TypeChecker` and four install
modules into the bridge, which is the coupling the relocation note
forbids; the fix remains the relocation, when it is safe to make.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {F : Nat}

/-! ## The record's projection equations -/

theorem fueledOps_annotate (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps F).annotate env d e = annotateCore env F d e := rfl
theorem fueledOps_inferType (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps F).inferType env d e = inferTypeCore env F d e := rfl
theorem fueledOps_isDefEq (F : Nat) (env : Env) (d : Nat) (a b : Expr) :
    (fueledOps F).isDefEq env d a b = isDefEqCore env F d a b := rfl
theorem fueledOps_ensureSort (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps F).ensureSort env d e = ensureSortCore env F d e := rfl
theorem fueledOps_whnf (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps F).whnf env d e = Setlec.whnf env F d e := rfl

/-- Inversion for `checkConstantVal`.  A duplicate; see the module
docstring. -/
theorem checkConstantVal_invT {env : Env} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps F) env cv = .ok cv') :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ type stype u,
      annotateCore env F 0 cv.type = .ok type ∧
      type.allLevelParamsDefined cv.levelParams = true ∧
      type.constsResolve env = true ∧
      inferTypeCore env F 0 type = .ok stype ∧
      ensureSortCore env F 0 stype = .ok u ∧
      cv' = { cv with type := type } := by
  simp only [checkConstantVal, fueledOps_annotate, fueledOps_inferType,
    fueledOps_ensureSort, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  case pos => simp [hfind] at h
  simp only [hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  case pos => rw [if_pos hres] at h; exact nomatch h
  simp only [hres] at h
  by_cases hpshape : cv.name.isProjFnShape = true
  case pos => rw [if_pos hpshape] at h; exact nomatch h
  rw [if_neg hpshape] at h
  have hpshapeF : cv.name.isProjFnShape = false := by
    revert hpshape; cases cv.name.isProjFnShape <;> simp
  by_cases hnd : Name.nodup cv.levelParams = true
  case neg => simp [hnd] at h
  simp only [hnd] at h
  by_cases hlb : cv.type.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : cv.type.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  cases hann : annotateCore env F 0 cv.type with
  | error e => rw [hann] at h; exact nomatch h
  | ok type =>
  rw [hann] at h
  try dsimp only at h
  by_cases htp : type.allLevelParamsDefined cv.levelParams = true
  case neg => simp [htp] at h
  simp only [htp] at h
  by_cases htr : type.constsResolve env = true
  case neg => simp [htr] at h
  simp only [htr] at h
  cases hst : inferTypeCore env F 0 type with
  | error e => rw [hst] at h; exact nomatch h
  | ok stype =>
  rw [hst] at h
  try dsimp only at h
  cases hsort : ensureSortCore env F 0 stype with
  | error e => rw [hsort] at h; exact nomatch h
  | ok u =>
  rw [hsort] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  have hfind0 : env.find? cv.name = none := by
    revert hfind
    cases env.find? cv.name <;> simp
  exact ⟨hfind0, by simpa using hres, hpshapeF, hnd, hlb,
    by simpa using hif,
    type, stype, u, rfl, htp, htr, hst, hsort, h.symm⟩

/-! ## The valuation an install chooses

At a fresh name, by the value's denotation; everywhere else unchanged.
`EnvTT`'s `defn_eq` field is what fixes this — there is no other
function that could satisfy it. -/

/-- Extend a valuation at one name by a closed expression's
denotation. -/
def cvalAt (cval : TConstVal) (env : Env) (n : Name) (value : Expr) :
    TConstVal := fun c ψ =>
  if c = n then (denoteClosed cval env ψ value).getD (cval c ψ)
  else cval c ψ

theorem cvalAt_ne {cval : TConstVal} {env : Env} {n : Name} {value : Expr}
    {c : Name} (h : c ≠ n) : cvalAt cval env n value c = cval c := by
  funext ψ; simp [cvalAt, h]

theorem cvalAt_self {cval : TConstVal} {env : Env} {n : Name}
    {value : Expr} {ψ : Name → Nat} {v : VExpr}
    (h : denoteClosed cval env ψ value = some v) :
    cvalAt cval env n value n ψ = v := by
  simp [cvalAt, h]

/-! ## The shared install

Everything a `def`, a `theorem` and an `opaque` have in common.  The
head hypotheses that are *not* shared — the `Nat`-operation
recurrences, the div/mod clauses, the compiler-trust identity — stay
parameters, because each kind discharges them differently (and two of
the three discharge them vacuously). -/

/-- **The value-carrying install.**  Transpose of `extend_model`. -/
theorem extendValueTT {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {name : Name} {lps : List Name} {type value : Expr}
    (hc₀cv : c₀.toConstantVal = ⟨name, lps, type⟩)
    (hc₀name : c₀.name = name)
    (hfresh : env.find? name = none)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    (hvf : value.hasFvar = false)
    (hvb : value.looseBVarsBounded 0 = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v t,
      denoteClosed m.cval env ψ value = some v ∧
      denoteClosed m.cval env ψ type = some t ∧ HasType [] v t)
    (hparams : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ lps, φ₁ p = φ₂ p) →
      denoteClosed m.cval env φ₁ value = denoteClosed m.cval env φ₂ value)
    (hc₀defn : ∀ cv2 value2 h2, c₀ = .defnInfo cv2 value2 h2 →
      value2 = value)
    (hc₀thm : ∀ cv2 value2, c₀ = .thmInfo cv2 value2 → value2 = value)
    (hc₀nrec : ∀ cv2 mI rP rules, c₀ ≠ .recInfo cv2 mI rP rules)
    (hc₀nind : ∀ cv2 caps, c₀ ≠ .indInfo cv2 caps)
    (hc₀nproj : ∀ entry, c₀ ≠ .projInfo entry)
    (hnres : reservedBasisNames.contains name = false)
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStoredT ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawTT ⟨c₀ :: env.consts⟩ (cvalAt m.cval env name value) T cvT caps)
    (hheadNat : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natOpNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∀ φ : Name → Nat, ∃ L R,
        denote (cvalAt m.cval env name value) ⟨c₀ :: env.consts⟩ φ 2 eq.1
          = some L ∧
        denote (cvalAt m.cval env name value) ⟨c₀ :: env.consts⟩ φ 2 eq.2
          = some R ∧
        Deq [cvalAt m.cval env name value natName φ,
             cvalAt m.cval env name value natName φ] L R)
    (hheadDivMod : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natDivModNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ (φ : Name → Nat) (Δ : List VExpr) (x y : VExpr),
        HasType Δ x (cvalAt m.cval env name value natName φ) →
        HasType Δ y (cvalAt m.cval env name value natName φ) →
        DivModClausesTT (cvalAt m.cval env name value) c₀.name φ Δ x y)
    (hheadReduce : ∀ cv, c₀ = .axiomInfo cv → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
          = true ∧
        ∀ (φ : Name → Nat) (Δ : List VExpr) (X : VExpr),
          HasType Δ X
            (cvalAt m.cval env name value (reduceElemName c₀.name) φ) →
          Deq Δ (.app (cvalAt m.cval env name value c₀.name φ) X) X) :
    Nonempty (EnvTT ⟨c₀ :: env.consts⟩) := by
  have hfresh' : env.find? c₀.name = none := by rw [hc₀name]; exact hfresh
  have hi : Installs env m.cval (cvalAt m.cval env name value) c₀ :=
    Installs.of_fresh hfresh' (fun n hn => by
      rw [hc₀name] at hn; exact (cvalAt_ne hn).symm)
  refine ⟨EnvTT.cons m hi hwf ?_ ?_ ?_ ?_ ?_ ?_
    (fun cv2 mI rP rules heq => absurd heq (hc₀nrec cv2 mI rP rules))
    ?_ hheadEta ?_ ?_ ?_ hheadNat hheadDivMod hheadReduce⟩
  · -- the new valuation is closed
    intro ψ
    obtain ⟨v, t, hv, -, -⟩ := hkey ψ
    rw [hc₀name, cvalAt_self hv]
    exact denote_closed m.cval_closed hvf hvb hv
  · -- it reads only the declared level parameters
    intro φ₁ φ₂ hp
    rw [hc₀name] at *
    obtain ⟨v₁, -, hv₁, -, -⟩ := hkey φ₁
    obtain ⟨v₂, -, hv₂, -, -⟩ := hkey φ₂
    rw [cvalAt_self hv₁, cvalAt_self hv₂]
    have := hparams φ₁ φ₂ (by rw [hc₀cv] at hp; exact hp)
    rw [hv₁, hv₂] at this
    exact Option.some.inj this
  · -- and it has a derivation of the declared type
    intro φ
    obtain ⟨v, t, hv, ht, hd⟩ := hkey φ
    refine ⟨t, ?_, ?_⟩
    · rw [hc₀cv]
      exact hi.denoteUp ht
    · rw [hc₀name, cvalAt_self hv]
      exact hd
  · -- a stored definition is denoted by its body
    intro cv2 value2 h2 heq φ
    obtain rfl := hc₀defn cv2 value2 h2 heq
    obtain ⟨v, -, hv, -, -⟩ := hkey φ
    have hn : cv2.name = name := by
      rw [← hc₀name, heq]; rfl
    rw [hn, cvalAt_self hv]
    exact hi.denoteUp hv
  · -- and a stored theorem by its proof
    intro cv2 value2 heq φ
    obtain rfl := hc₀thm cv2 value2 heq
    obtain ⟨v, -, hv, -, -⟩ := hkey φ
    have hn : cv2.name = name := by
      rw [← hc₀name, heq]; rfl
    rw [hn, cvalAt_self hv]
    exact hi.denoteUp hv
  · -- `Empty` is reserved, so this install is not at it
    intro hE
    rw [hc₀name] at hE
    exact absurd (hE ▸ hnres) (by decide)
  · -- no recursor rules are installed
    intro cv2 mI rP rules heq
    exact absurd heq (hc₀nrec cv2 mI rP rules)
  · -- no unit-like family is installed
    intro cv2 caps heq
    exact absurd heq (hc₀nind cv2 caps)
  · -- no projection-table entry is installed
    intro entry heq
    exact absurd heq (hc₀nproj entry)
  · -- and the name is not reserved, so the pinned clause is vacuous
    intro hres
    rw [hc₀name] at hres
    rw [hres] at hnres
    exact nomatch hnres

end Setlec.TTVerify
