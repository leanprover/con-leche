import Setlec.TTVerify.DeclStep
import Setlec.Verify.Extend.Inversions

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

/-! ## The inversions, now shared

`checkConstantVal_inv` and the `fueledOps` projection equations were
duplicated here while they lived in `Setlec/Model/Extend/*`.  Task #123
relocated that whole tier to `Setlec/Verify/*` — the file's own
docstring now says both paths may import it — so the duplicates are
gone and this is an alias for the call sites' benefit. -/

theorem checkConstantVal_invT {env : Env} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cv') :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ type stype u,
      annotateCore mode env F 0 cv.type = .ok type ∧
      type.allLevelParamsDefined cv.levelParams = true ∧
      type.constsResolve env = true ∧
      inferTypeCore mode env F 0 type = .ok stype ∧
      ensureSortCore mode env F 0 stype = .ok u ∧
      cv' = { cv with type := type } :=
  checkConstantVal_inv h

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
    (hc₀nctor : ∀ cv2 cnP cnF, c₀ ≠ .ctorInfo cv2 cnP cnF)
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
    ?_ hheadEta ?_
    (fun T cvT caps cvC hfT _ _ _ hfcC hor => by
      rcases hor with hT | hC
      · rw [hT, Env.find?_cons, if_pos rfl] at hfT
        exact absurd (Option.some.inj hfT) (hc₀nind cvT caps)
      · rw [hC, Env.find?_cons, if_pos rfl] at hfcC
        exact absurd (Option.some.inj hfcC)
          (hc₀nctor cvC caps.etaParams caps.etaFields))
    ?_ (fun _ entry heq _ => absurd heq (hc₀nproj entry)) ?_
    ?_ hheadNat hheadDivMod hheadReduce⟩
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
  · -- `Eq` is reserved, so this install is not at it
    intro hE
    rw [hc₀name] at hE
    rw [hE] at hnres
    exact nomatch hnres

end Setlec.TTVerify
