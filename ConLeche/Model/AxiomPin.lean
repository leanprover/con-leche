module

import ConLeche.Semantics.DeclRun
public import ConLeche.Model.AxiomMem

public section

/-!
# The pin tier, at the validated-annotation currency (task #161)

`DeclAxiomRun`'s branches at the P invariant: the tolerated skip,
`Lean.trustCompiler` and the two standard axioms land here;
`ofReduceNat`/`ofReduceBool` are `Model/AxiomReduce.lean`'s, and
`axiomStepPB_of` (`Model/Fold.lean`) assembles them.

## What a branch owes

`harvestAxiom` (`Model/Harvest.lean`) is the wrapper: the *type*
side is harvested from `ConstantValRun`'s own run, and what the branch
must supply is the leaf `A` with

* `hAclosed`/`hAparams` — syntactic, from the branch key and
  the `EnvModel` fields;
* `hAok`/`hAvalid` — free at a `BConst` or `acval` leaf (`WellDenoted`'s
  and `AnnotValid`'s `.const`/`.prf` clauses are `True`, and an
  `acval` leaf carries both as invariant fields);
* `hmemA` — **the semantic content**: `interp` of the leaf inhabits
  `interp` of the *stored* type's `denoteMeta` reading.

## The stored type's reading is not the pin's

`hmemA` speaks about the reading of `type'`, the *stored* annotated
type.  Every branch key knows the type only through `matchesPin`,
which compares `erasePw` — so the pin fixes the stored
type **up to binder names and binder `pw` data**.  `denoteMeta`'s
binder clauses read `pwBit φ mb.pw`, and `erasePw` normalizes every
datum to `.never`, whose bit is `1`; so `denoteMeta (e.erasePw) =
denoteMeta e` fails at the first Prop-codomain binder.  The bits are
therefore taken from the recorded run, never from the match verdict:
`ConstantValRun`'s run gives `inferTypeCore μ env F 0 type' = .ok
stype`; inverting it through `inferTypeCore_forall_inv` once per binder
yields `Level.zeronessOf v = mb.pw`, hence (`pwBit_zeronessOf`)
`pwBit φ mb.pw = 0 ↔ Level.eval φ v = 0`, and knowing `Level.eval φ v`
is one symbolic-inference lemma per pinned family
(`Model/AxiomBits.lean`; the telescope collapse `imax x y = 0 ↔ y = 0`
makes it one fact per pin rather than one per binder).  The
memberships are `Model/AxiomMem.lean`'s.

`Lean.trustCompiler` is the exception: its type is a **bare constant**,
which carries no binder datum, so the pin fixes `type' = .const
trueName []` **on the nose** (`erasePw_const_invS`) and the leaf is the
stored `True.intro`'s annotated valuation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
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
`ConstantVal.matchesPin` compares through `erasePw`, and
neither erasure moves a `.const` — so this is the one pinned axiom
whose `denoteMeta` reading is computable from the pin alone (see the
module docstring).  The leaf is the stored `True.intro`'s
annotated valuation, and the membership is that constant's own
`mem_type`, whose type reads to the same `acval trueName ψ` the
axiom's does. -/
theorem axiomTrustCompiler (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValRun μ F env cv type')
    (hname : cv.name = ConLeche.trustCompilerName)
    (hok : ConLeche.trustCompilerOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    CoverStep mp
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩ := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
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
        exact ⟨hTi.1.2, erasePw_const_invS hTi.2⟩
    | _ => exact nomatch hTi
  -- **the pin bites on the nose**: a `.const` has no binder, so
  -- `erasePw` forgives nothing here
  have htyA : type' = .const ConLeche.trueName [] := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hA
    exact erasePw_const_invS hA.2
  have hnameTi : ciTi.name = ConLeche.trueIntroName := Env.find?_name hfTi
  -- the leaf: the stored `True.intro`'s *annotated* valuation
  refine harvestAxiom (V := V) hμ mp hcv
    (A := fun ψ => mp.base2.acval ConLeche.trueIntroName ψ)
    (fun ψ => mp.base2.cval_closedL _ ψ) ?_ ?_ ?_ ?_ ?_
    -- `trustCompiler` is not a compiler-trust *operation*: the pin
    -- fixes the name, and the two operations are installed as opaques
    (by rw [hname]; decide)
  · -- `hAclosed`
    exact fun ψ k => mp.base2.acval_closed _ ψ k
  · -- `hAparams`: `True.intro` is level-monomorphic, so the premise is
    -- vacuous
    intro ψ₁ ψ₂ _
    exact mp.base2.acval_params _ ciTi hfTi ψ₁ ψ₂ (by
      rw [hlpTi]; intro p hp; exact nomatch hp)
  · exact fun ψ ρ => mp.base2.acval_wellDenoted _ ψ ρ
  · exact fun ψ ρ => mp.acval_validV _ ψ ρ
  · -- `hmemA`: the axiom's type and `True.intro`'s stored type are the
    -- *same* bare constant, so they have the same reading, and the
    -- membership is that constant's own `mem_type`
    intro ψ ta hta ρ
    rw [htyA, denoteMeta_levelless_const hfT hlpT] at hta
    obtain rfl : ta = mp.base2.acval ConLeche.trueName ψ :=
      (Option.some.inj hta).symm
    have hmem := mp.mem_type ciTi (Env.find?_mem hfTi) ψ
      (mp.base2.acval ConLeche.trueName ψ)
      (by rw [htyTi]; exact denoteMeta_levelless_const hfT hlpT) ρ
    rwa [hnameTi] at hmem

/-! ## The two standard axioms

`DeclAxiomRun`'s first branch, both halves.  The bits come from
`Model/AxiomBits.lean` (the axiom's *own* recorded run) and the
memberships from `Model/AxiomMem.lean`. -/

/-- **The standard-axiom branch, discharged.**  The leaf is the layer's
own constant in both halves, so every syntactic obligation is `rfl` or
a `const` clause, and the whole content is the membership. -/
theorem axiomStd (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal} {type' : Expr}
    (hcv : ConstantValRun μ F env cv type')
    (hok : ConLeche.stdAxiomOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    CoverStep mp
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩ := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  obtain ⟨stype, usort, hst, hens⟩ := hrunT
  have hwfc : ConLeche.EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf
      ⟨htf', htp, Expr.constsResolve_mono htr, hbt', ?_, ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro tbl heq; exact nomatch heq
    · intro cv2 caps heq; exact nomatch heq
  by_cases hn : cv.name = propextName
  · refine harvestAxiom (V := V) hμ mp hcv
      (A := fun _ => .const .propext []) (fun _ => trivial)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => by simp)
      (fun _ _ => by simp) ?_ (by rw [hn]; decide)
    intro ψ ta hta ρ
    exact propext_mem hμ mp hok hn hst ψ ta hta ρ
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
        (fun _ _ => rfl)
        (fun ψ₁ ψ₂ hp => by
          show AnnotTerm.const .choice [ψ₁ uN] = AnnotTerm.const .choice [ψ₂ uN]
          rw [huN ψ₁ ψ₂ hp])
        (fun _ _ => by simp) (fun _ _ => by simp) ?_
        (by rw [hn2]; decide)
      intro ψ ta hta ρ
      exact choice_mem hμ mp hok hn2 hst ψ ta hta ρ
    · exfalso
      unfold ConLeche.stdAxiomOk at hok
      rw [show (⟨cv.name, cv.levelParams, type'⟩ : ConstantVal).name
        = cv.name from rfl] at hok
      rw [ite_eq_right hn, ite_eq_right hn2] at hok
      exact nomatch hok

end ConLeche.Model
