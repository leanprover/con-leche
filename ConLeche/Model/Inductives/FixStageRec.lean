module

public import ConLeche.Model.Inductives.FixRuleData
import ConLeche.Model.Inductives.FixRecReadDefs
import ConLeche.Model.Inductives.FixChainFacts
import ConLeche.Model.Inductives.SumRecFrames
import ConLeche.Semantics.Tower.FixSquashI
import ConLeche.Kernel.PropWhen
public import ConLeche.Model.Inductives.FixRecLaw
import ConLeche.Semantics.Tower.FixWire
public section

/-!
# The recursive recursor's stage, part 1: the rule law (task #188)

The semantic data of a recursive block at an assignment (`fssOfR`,
`essOfR`, `eissOfR`, `rssOfK`), the recursor leaf (`fixLeafAV`), the
rule's binder data as domains (`fixRuleDataAV_map_dom`), and **the
rule law** at the recursor's cons (`fixRecRuleLaw`): the sum route's
`sumRecRuleLaw` with the rule read at the cons (`fixRuleData_of`),
its gradedness from the model (`fixRuleOk`, supplied), and the
recursor's iota (`fixRecLawCore`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The semantic data of a block -/

/-- The constructors' field lists. -/
@[expose] def fssOfR (nP : Nat) (cds : List CtorDatumR) : List (List AnnotTerm) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The constructors' index readings. -/
@[expose] def essOfR (cds : List CtorDatumR) : List (List AnnotTerm) := cds.map fun cd => cd.2.2.2.1


omit [SetTheory V] in
theorem fssOfR_getElem? (nP : Nat) (cds : List CtorDatumR) (j : Nat) :
    (fssOfR nP cds)[j]? = (cds[j]?).map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_getElem? (cds : List CtorDatumR) (j : Nat) :
    (essOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.1 := by simp [essOfR]


omit [SetTheory V] in
theorem fssOfR_length (nP : Nat) (cds : List CtorDatumR) : (fssOfR nP cds).length = cds.length := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_length (cds : List CtorDatumR) : (essOfR cds).length = cds.length := by simp [essOfR]

/-! ## The recursor leaf -/

/-- The restriction of an assignment to a level-parameter list. -/
@[expose] def restrictΨ (lps : List Name) (ψ : Name → Nat) : Name → Nat :=
  fun q => if q ∈ lps then ψ q else 0

omit [SetTheory V] in
theorem restrictΨ_agree (lps : List Name) (ψ : Name → Nat) :
    ∀ q ∈ lps, restrictΨ lps ψ q = ψ q := by
  intro q hq
  simp [restrictΨ, hq]

omit [SetTheory V] in
theorem restrictΨ_congr {lps : List Name} {ψ₁ ψ₂ : Name → Nat}
    (h : ∀ q ∈ lps, ψ₁ q = ψ₂ q) : restrictΨ lps ψ₁ = restrictΨ lps ψ₂ := by
  funext q
  unfold restrictΨ
  split
  · next hq => exact h q hq
  · rfl

/-! ## The data at the parameters -/

omit [SetTheory V] in
/-- The constructor data at two assignments agreeing on the data. -/
theorem fixCtorDataList_congr {dsF₁ dsF₂ : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF₁ esF₂ : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF₁ eissF₂ : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF₁ tssF₂ : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ₁ ψ₂ : Name → Nat} :
    ∀ (cs : List (ConstantVal × Nat)) (j : Nat),
      (∀ i, i < cs.length → dsF₁ (j + i) ψ₁ = dsF₂ (j + i) ψ₂ ∧ esF₁ (j + i) ψ₁ = esF₂ (j + i) ψ₂ ∧
        eissF₁ (j + i) ψ₁ = eissF₂ (j + i) ψ₂ ∧ tssF₁ (j + i) ψ₁ = tssF₂ (j + i) ψ₂) →
      fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ₁ cs j = fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ₂ cs j
  | [], _, _ => rfl
  | c :: cs, j, h => by
    simp only [fixCtorDataList]
    obtain ⟨h1, h2, h3, h4⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h1 h2 h3 h4
    rw [h1, h2, h3, h4, fixCtorDataList_congr cs (j + 1) fun i hi => by
      have := h (i + 1) (by simpa using hi)
      rwa [show j + (i + 1) = j + 1 + i from by omega] at this]

/-! ## The subsingleton criterion at a field (task #202 A2) -/

/-- An unsourced field of a source-bounded chain is a truth value at
every fitting prefix spine. -/
theorem fieldsBoundSrc_at {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {srcs : List (Option Nat)} {i : Nat} {fs : List V},
      FieldsBoundSrc ρ Fs srcs → srcs[i]? = some none → SpineFit ρ (Fs.take i) fs → i < Fs.length →
      interp V (consList fs ρ) (Fs.getD i default) ∈ˢ (univ 0 : V)
  | [], _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, hs, _, _ => by simp at hs
  | F :: Fs, s :: srcs, 0, fs, hb, hs, hsp, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    cases fs with
    | nil => exact hb.1 hs
    | cons a fs' => exact hsp.elim
  | F :: Fs, s :: srcs, i + 1, fs, hb, hs, hsp, hi => by
    cases fs with
    | nil => exact hsp.elim
    | cons a fs' =>
      obtain ⟨ha, hsp'⟩ := hsp
      rw [consList_cons, List.getD_cons_succ]
      exact fieldsBoundSrc_at (hb.2 a ha) (by simpa using hs) hsp' (by simpa using hi)

end ConLeche.Model
