module

import ConLeche.Semantics.DeclRun
public import ConLeche.Model.Harvest
import ConLeche.Model.AxiomMem

public section

/-!
# The pin tier (task #161)

`DeclAxiomRun`'s branches at the P invariant: the tolerated skip,
`Lean.trustCompiler` and the two standard axioms land here;
`ofReduceNat`/`ofReduceBool` are `Model/AxiomReduce.lean`'s, and
`axiomStepPB_of` (`Model/Fold.lean`) assembles them.

## What a branch owes

`harvestAxiom` (`Model/Harvest.lean`) is the wrapper: the *type*
side is harvested from `ConstantValRun`'s own run, and what the branch
must supply is the leaf `A` with

* `hAvclosed`/`hAparams` — syntactic, from the branch key and
  the `EnvModel` fields;
* `hAok` — free at a `BConst` or `acval` leaf (`WellDenoted`'s
  `.const`/`.prf` clauses are `True`, and an `acval` leaf carries it as
  an invariant field);
* `hmemA` — **the semantic content**: `interp` of the leaf inhabits
  `interp` of the *stored* type's `denote` reading.

## The stored type's reading is the pin's

`matchesPin` is plain equality, so the pin fixes the stored type on
the nose, and its reading is the pin's.
The memberships are `Model/AxiomMem.lean`'s.

`Lean.trustCompiler`'s type is a **bare constant**, so the pin fixes
`type' = .const trueName []` and
the leaf is the stored `True.intro`'s valuation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-! ## The tolerated skip -/

/-- **The tolerated-axiom skip.**  `DeclAxiomRun`'s fourth branch stores
nothing (`env₂ = env`), so there is no leaf, no extension and no
crossing: the P invariant at the successor environment *is* the one
held at the prefix. -/
theorem axiomSkip (mp : EnvModelM V μ env) :
    CoverStep mp env := CoverTo.refl mp []

/-! ## `Lean.trustCompiler` -/

/-- **The `trustCompiler` branch, discharged.**

The pin fixes the axiom's type to the stored `True` *on the nose* —
`ConstantVal.matchesPin` is plain equality — so this is the one pinned axiom
whose `denote` reading is computable from the pin alone (see the
module docstring).  The leaf is the stored `True.intro`'s
leaf valuation, and the membership is that constant's own
`mem_type`, whose type reads to the same `acval trueName ψ` the
axiom's does. -/
theorem axiomTrustCompiler (hμ : μ.isVerified = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValRun μ F env cv type')
    (hname : cv.name = ConLeche.trustCompilerName)
    (hok : ConLeche.trustCompilerOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    CoverStep mp
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hnd, hlbt, hitf, hann, htp, htr,
    -⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := stored_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the guard's two pin hits, unpacked
  have hokc := hok
  simp only [ConLeche.trustCompilerOk, Bool.and_eq_true] at hokc
  obtain ⟨⟨hT, hTi⟩, hA⟩ := hokc
  cases hfT : env.find? ConLeche.trueName with
  | none => rw [hfT] at hT; exact nomatch hT
  | some ciT =>
  cases hfTi : env.find? ConLeche.trueIntroName with
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
      ciTi.toConstantVal.type = .const ConLeche.trueName [] := by
    cases ciTi with
    | ctorInfo cvTi nP nF =>
      match nP, nF, hTi with
      | 0, 0, hTi =>
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hTi
        exact ⟨hTi.1.2, hTi.2⟩
    | _ => exact nomatch hTi
  -- **the pin bites on the nose**
  have htyA : type' = .const ConLeche.trueName [] := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hA
    exact hA.2
  have hnameTi : ciTi.name = ConLeche.trueIntroName := Env.find?_name hfTi
  -- the leaf: the stored `True.intro`'s leaf valuation
  refine harvestAxiom (V := V) hμ mp hcv
    (A := fun ψ => mp.base2.acval ConLeche.trueIntroName ψ)
    (fun ψ => mp.base2.cval_closed _ ψ) ?_ ?_ ?_
    -- `trustCompiler` is not a compiler-trust *operation*: the pin
    -- fixes the name, and the two operations are installed as opaques
    (by rw [hname]; decide)
  · -- `hAparams`: `True.intro` is level-monomorphic, so the premise is
    -- vacuous
    intro ψ₁ ψ₂ _
    exact mp.base2.acval_params _ ciTi hfTi ψ₁ ψ₂ (by
      rw [hlpTi]; intro p hp; exact nomatch hp)
  · exact fun ψ ρ => mp.base2.acval_wellDenoted _ ψ ρ
  · -- `hmemA`: the axiom's type and `True.intro`'s stored type are the
    -- *same* bare constant, so they have the same reading, and the
    -- membership is that constant's own `mem_type`
    intro ψ ta hta ρ
    rw [htyA, denote_levelless_const hfT hlpT] at hta
    obtain rfl : ta = mp.base2.acval ConLeche.trueName ψ :=
      (Option.some.inj hta).symm
    have hmem := mp.mem_type ciTi (Env.find?_mem hfTi) ψ
      (mp.base2.acval ConLeche.trueName ψ)
      (by rw [htyTi]; exact denote_levelless_const hfT hlpT) ρ
    rwa [hnameTi] at hmem

/-! ## A native `bv_decide` axiom's stub (task #368) -/

/-- **The stub branch**: a native `bv_decide` axiom is stored with type
`True` (`bvStubCv`), checked as such, and interpreted by `True.intro` —
`axiomTrustCompiler`'s argument at another name. -/
theorem axiomBVStub (hμ : μ.isVerified = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal}
    (hcv : ConstantValRun μ F env (ConLeche.bvStubCv cv) (ConLeche.bvStubCv cv).type)
    (hok : ConLeche.bvStubOk env cv = true) :
    CoverStep mp
      ⟨.axiomInfo (ConLeche.bvStubCv cv) :: env.consts, env.tables⟩ := by
  have hokc := hok
  simp only [ConLeche.bvStubOk, Bool.and_eq_true] at hokc
  obtain ⟨⟨⟨hT, hTi⟩, -⟩, hnat⟩ := hokc
  cases hfT : env.find? ConLeche.trueName with
  | none => rw [hfT] at hT; exact nomatch hT
  | some ciT =>
  cases hfTi : env.find? ConLeche.trueIntroName with
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
      ciTi.toConstantVal.type = .const ConLeche.trueName [] := by
    cases ciTi with
    | ctorInfo cvTi nP nF =>
      match nP, nF, hTi with
      | 0, 0, hTi =>
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hTi
        exact ⟨hTi.1.2, hTi.2⟩
    | _ => exact nomatch hTi
  have hnameTi : ciTi.name = ConLeche.trueIntroName := Env.find?_name hfTi
  have hnr : (ConLeche.bvStubCv cv).name ∉ ConLeche.reduceOpNames := by
    intro hmem
    simp only [ConLeche.bvStubCv] at hmem
    simp only [ConLeche.reduceOpNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> rw [h] at hnat <;> revert hnat <;> decide
  exact harvestAxiom (V := V) (cv := ConLeche.bvStubCv cv) (type' := (ConLeche.bvStubCv cv).type)
    hμ mp hcv
    (A := fun ψ => mp.base2.acval ConLeche.trueIntroName ψ)
    (fun ψ => mp.base2.cval_closed _ ψ)
    (fun ψ₁ ψ₂ _ => mp.base2.acval_params _ ciTi hfTi ψ₁ ψ₂ (by
      rw [hlpTi]; intro p hp; exact nomatch hp))
    (fun ψ ρ => mp.base2.acval_wellDenoted _ ψ ρ)
    (by
      intro ψ ta hta ρ
      change denote _ _ _ _ (.const ConLeche.trueName []) = _ at hta
      rw [denote_levelless_const hfT hlpT] at hta
      obtain rfl : ta = mp.base2.acval ConLeche.trueName ψ :=
        (Option.some.inj hta).symm
      have hmem := mp.mem_type ciTi (Env.find?_mem hfTi) ψ
        (mp.base2.acval ConLeche.trueName ψ)
        (by rw [htyTi]; exact denote_levelless_const hfT hlpT) ρ
      rwa [hnameTi] at hmem)
    hnr

/-! ## The two standard axioms

`DeclAxiomRun`'s first branch, both halves; the memberships are
`Model/AxiomMem.lean`'s. -/

/-- **The standard-axiom branch, discharged.**  The leaf is the layer's
own constant in both halves, so every syntactic obligation is `rfl` or
a `const` clause, and the whole content is the membership. -/
theorem axiomStd (hμ : μ.isVerified = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValRun μ F env cv type')
    (hok : ConLeche.stdAxiomOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    CoverStep mp
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hnd, hlbt, hitf, hann, htp, htr,
    -⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := stored_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  have hwfc : ConLeche.EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts, env.tables⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf
      ⟨htf', htp, Expr.constsResolve_mono htr, hbt', ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro cv2 caps heq; exact nomatch heq
  by_cases hn : cv.name = propextName
  · refine harvestAxiom (V := V) hμ mp hcv
      (A := fun _ => .const .propext []) (fun _ => trivial)
      (fun _ _ _ => rfl) (fun _ _ => by simp)
      ?_ (by rw [hn]; decide)
    intro ψ ta hta ρ
    exact propext_mem mp hok hn ψ ta hta ρ
  · by_cases hn2 : cv.name = choiceName
    · -- the pin fixes the axiom's one level parameter, so the leaf
      -- reads only `ψ uN`
      have huN : ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → ψ₁ uN = ψ₂ uN := by
        intro ψ₁ ψ₂ hp
        obtain ⟨-, -, -, hApin⟩ := nonempty_shapes hok hn2
        have hlpA : cv.levelParams = choiceA.levelParams :=
          (matchesPin_invT hApin).2
        refine hp uN ?_
        rw [hlpA, show choiceA.levelParams = [uN] from rfl]
        exact List.Mem.head _
      refine harvestAxiom (V := V) hμ mp hcv
        (A := fun ψ => .const .choice [ψ uN])
        (fun _ => trivial)
        (fun ψ₁ ψ₂ hp => by
          show Term.const .choice [ψ₁ uN] = Term.const .choice [ψ₂ uN]
          rw [huN ψ₁ ψ₂ hp])
        (fun _ _ => by simp) ?_
        (by rw [hn2]; decide)
      intro ψ ta hta ρ
      exact choice_mem mp hok hn2 ψ ta hta ρ
    · exfalso
      unfold ConLeche.stdAxiomOk at hok
      rw [show (⟨cv.name, cv.levelParams, type'⟩ : ConstantVal).name
        = cv.name from rfl] at hok
      rw [ite_eq_right hn, ite_eq_right hn2] at hok
      exact nomatch hok

end ConLeche.Model
