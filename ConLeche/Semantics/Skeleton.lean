module

import ConLeche.Semantics.WellDenoted
import ConLeche.Semantics.Sat
public import ConLeche.Semantics.Univ
public import ConLeche.Semantics.BasisOk

@[expose] public section

/-!
# The second soundness's per-former skeleton (task #151, arc step 4)

*(Re-based to `ConLeche/SetBase/*` at THE SEPARATION's S2, task #161: the
per-former rows are stated over `WellDenoted`/`interp`/`Sat` and nothing
else — that is the module's own design rule — so they carry no
environment, and BOTH lanes' inference quarters close their rows with
them.  Its `Annot/EnvModel` import was transitive cover (`Sat`, now
`SetBase/Sat`).  Path and module name changed; namespaces, statements
and proofs verbatim.)*


The case statements of the `interp` soundness, one per `AnnotTerm`
former, each stated over **exactly the facts the frozen Claims2
interface carries** and nothing else.  Hypothesis-first per the
`CheckStepR` precedent: a case that needs a fact the interface lacks is
a finding, not a hypothesis to invent.

## What a case is

The assembly architecture rules out re-signing the 44-case mutual
induction: the soundness is **per-step graded lemmas on `AnnotTerm`**,
composed along the bridge claims, with annotations following the run
rather than crossing a bare `Red`.  So each case here takes the
subterms' two facts — hereditary truthfulness (`WellDenoted`) and
membership — and produces the node's, in the shape the run-level claim
will thread.

Two conventions, both forced:

* **membership is stated at the annotated type**, never at a bare
  value, because the node's type is what the next case consumes;
* **the binder cases take their numeral's justification as a
  hypothesis**, not the numeral alone.  The numeral is in the term;
  what a case needs is what the numeral is
  *worth* semantically, and that is the sort fact — supplier
  `HasSort.mem_univ` (`Annot/Kinding.lean`), which is where every
  binder row's `hcod`/`hdom` premise below comes from.

## The λ row's freedom, recorded where it is used

`sound_lam` has **no** empty-domain side condition, and needs no
validity metatheorem: `lamR_mem`'s premise is a `∀ x ∈ˢ ⟦A⟧`, which at
`⟦A⟧ = ∅` is vacuous, and so is the kind-`0` fibre condition.  The
numeral still matters — `lamR 0 ∅ F = pt` and `lamR 1 ∅ F = ∅` are
different values — but it comes from the *term*, and no semantic fact
about it is required to close the case.  This is why `ValidInfer`'s
refutation (`Annot/Validity.lean`) does not block the consumer lane.

## What the app row owes to the slot amendment

`sound_app` closes at **both** kinds.  Before the app clause gained its
kind-`0` fibre component (the consumer seal) it did not: `app_mem_piR`'s
`hB0` had no supplier, and the truth-value route gives only that the
fibre is inhabited.  The amendment is what makes the app row a theorem
rather than a residue.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable (V : Type w) [SetTheory V]

/-! ## The leaf rows -/

/-- **`sort`.**  Interface facts: none.  The universe tower's own
membership; the annotated type of `.sort u` is `.sort (u + 1)`. -/
theorem sound_sort (ρ : Nat → V) (u : Nat) :
    WellDenoted V ρ (.sort u) ∧
      interp V ρ (.sort u) ∈ˢ interp V ρ (.sort (u + 1)) := by
  refine ⟨by simp, ?_⟩
  rw [interp_sort, interp_sort]
  exact univ_mem_univ u

/-! ## The binder rows -/

/-- **`pi`.**  Interface facts: the domain's membership at its own
numeral `u`, the codomain's at `v` under the binder, and the two
hereditary halves.  The formation law is the `imax` rule *exactly*
(`piR_mem_univ`), so the annotated type is `.sort (ConLeche.Term.imax u v)`
on the nose — no "may land lower" slack. -/
theorem sound_pi {u v : Nat} {ρ : Nat → V} {Aa Ba : AnnotTerm}
    (hokA : WellDenoted V ρ Aa)
    (hokB : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) Ba)
    (hA : interp V ρ Aa ∈ˢ (univ u : V))
    (hB : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univ v : V)) :
    WellDenoted V ρ (.pi u v Aa Ba) ∧
      interp V ρ (.pi u v Aa Ba)
        ∈ˢ interp V ρ (.sort (ConLeche.Term.imax u v)) := by
  refine ⟨by rw [WellDenoted_pi]; exact ⟨hokA, hokB⟩, ?_⟩
  rw [interp_pi, interp_sort]
  exact piR_mem_univ hA hB

/-- **`lam`.**  Interface facts: the body's membership in the codomain
under the binder, the codomain's kind-`0` fibre condition (the
numeral's worth, from `HasSort.mem_univ`), and the two hereditary
halves.  **No empty-domain side condition** — see the module
docstring.  The `Π`'s domain numeral `u` is free: `interp`'s `pi`
clause discards it (only the codomain sort dispatches), so the row
holds at every annotation of the domain. -/
theorem sound_lam {u v : Nat} {ρ : Nat → V} {Aa ba Ba : AnnotTerm}
    (hokA : WellDenoted V ρ Aa)
    (hokb : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) ba)
    (hb : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) ba ∈ˢ interp V (cons x ρ) Ba)
    (hcod : v = 0 → ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univZero : V)) :
    WellDenoted V ρ (.lam v Aa ba) ∧
      interp V ρ (.lam v Aa ba)
        ∈ˢ interp V ρ (.pi u v Aa Ba) := by
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_lam]
    exact ⟨hokA, hokb, fun x => interp V (cons x ρ) Ba, hb, hcod⟩
  · rw [interp_lam, interp_pi]
    exact lamR_mem hb

/-! ## The application row -/

/-- **`app`.**  Interface facts: the function's membership at an
*annotated* `Π`, the argument's in its domain, and the `Π`'s kind-`0`
fibre condition.  Closes at **both** kinds — the kind-`0` premise is
exactly `app_mem_piR`'s, and its supplier is the `Π`'s own numeral. -/
theorem sound_app {u v : Nat} {ρ : Nat → V} {fa aa Aa Ba : AnnotTerm}
    (hokf : WellDenoted V ρ fa) (hoka : WellDenoted V ρ aa)
    (hf : interp V ρ fa ∈ˢ interp V ρ (.pi u v Aa Ba))
    (ha : interp V ρ aa ∈ˢ interp V ρ Aa)
    (hcod : v = 0 → ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univZero : V)) :
    WellDenoted V ρ (.app fa aa) ∧
      interp V ρ (.app fa aa) ∈ˢ interp V ρ (Ba.inst aa) := by
  refine ⟨WellDenoted_app_of V hokf hoka hf ha hcod, ?_⟩
  rw [interp_pi] at hf
  rw [interp_app, interp_inst0]
  exact app_mem_piR hf ha hcod

/-! ## The projection rows

The `Σ`-eliminations, general in the fibre family (`Interp/Value.lean`
states them for the `bval` tower's `fun x => app B x`; the invariant's
proj clause carries a meta-level `Bf`, so the two below are the
general forms `mem_sigma_elim` supports directly). -/

/-- First projection: a member of a `Σ` has its first component in the
base. -/
theorem sfst_mem_gen {u v : Nat} {A p : V} {Bf : V → V}
    (hA : A ∈ˢ (univ u : V))
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A Bf) : sfst p ∈ˢ A := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · have hu : u = 0 := Nat.le_zero.mp (hw ▸ Nat.le_max_left u v)
    rw [h0 hw, sfst_pt]
    exact (mem_univ_zero (hu ▸ hA) ha) ▸ ha
  · rw [hne hw, sfst_spair]; exact ha

/-- Second projection: the second component lies in the fibre over the
first. -/
theorem ssnd_mem_gen {u v : Nat} {A p : V} {Bf : V → V}
    (hA : A ∈ˢ (univ u : V))
    (hB : ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V))
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A Bf) :
    ssnd p ∈ˢ Bf (sfst p) := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · have hu : u = 0 := Nat.le_zero.mp (hw ▸ Nat.le_max_left u v)
    have hv : v = 0 := Nat.le_zero.mp (hw ▸ Nat.le_max_right u v)
    have hapt : a = pt := mem_univ_zero (hu ▸ hA) ha
    have hBa : Bf a ∈ˢ (univ 0 : V) := hv ▸ hB a ha
    have hbpt : b = pt := mem_univ_zero hBa hb
    rw [h0 hw, ssnd_pt, sfst_pt, show Bf pt = Bf a by rw [hapt]]
    exact hbpt ▸ hb
  · rw [hne hw, ssnd_spair, sfst_spair]; exact hb

end ConLeche.Semantics
