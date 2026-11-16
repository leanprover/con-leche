module

import ConLeche.Semantics.WellDenoted
import ConLeche.Semantics.Sat
public import ConLeche.Semantics.Univ
public import ConLeche.Semantics.BasisOk

@[expose] public section

/-!
# The second soundness's per-former skeleton (task #151, arc step 4)

The case statements of the `interp` soundness, one per `Term`
former, each stated over `WellDenoted`/`interp`/`Sat` and nothing else,
so they carry no environment.  A case that needs a fact the claim
interface lacks is a finding, not a hypothesis to invent.

## What a case is

The assembly architecture rules out re-signing the 44-case mutual
induction: the soundness is **per-step graded lemmas on `Term`**,
composed along the bridge claims, with the readings following the run
rather than crossing a bare `Red`.  So each case here takes the
subterms' two facts — hereditary truthfulness (`WellDenoted`) and
membership — and produces the node's, in the shape the run-level claim
will thread.

Membership is stated at the spelled type, never at a bare value,
because the node's type is what the next case consumes.  The binder
rows read their regime off the values (`piV`/`lamV`), so they need no
regime premise: the λ row needs its codomain fibres to be types
(`lamV_mem`), the application row nothing beyond the memberships and
the domain's type (`app_mem_piV`).
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory


universe w

variable (V : Type w) [SetTheory V]

/-! ## The leaf rows -/

/-- **`sort`.**  Interface facts: none.  The universe tower's own
membership; the spelled type of `.sort u` is `.sort (u + 1)`. -/
theorem sound_sort (ρ : Nat → V) (u : Nat) :
    WellDenoted V ρ (.sort u) ∧
      interp V ρ (.sort u) ∈ˢ interp V ρ (.sort (u + 1)) := by
  refine ⟨by simp, ?_⟩
  rw [interp_sort, interp_sort]
  exact univ_mem_univ u

/-! ## The binder rows -/

/-- **`pi`.**  Interface facts: the domain's membership in `Sort u`,
the codomain's in `Sort v` under the binder, and the two hereditary
halves.  The formation law is the `imax` rule (`piV_mem_univ`). -/
theorem sound_pi {u v : Nat} {ρ : Nat → V} {Aa Ba : Term}
    (hokA : WellDenoted V ρ Aa)
    (hokB : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) Ba)
    (hA : interp V ρ Aa ∈ˢ (univ u : V))
    (hB : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univ v : V)) :
    WellDenoted V ρ (.pi Aa Ba) ∧
      interp V ρ (.pi Aa Ba)
        ∈ˢ interp V ρ (.sort (ConLeche.Term.imax u v)) := by
  refine ⟨by
    rw [WellDenoted_pi]
    exact ⟨hokA, IsTy_of_mem_univ hA, hokB, fun x hx => IsTy_of_mem_univ (hB x hx)⟩, ?_⟩
  rw [interp_pi, interp_sort]
  exact piV_mem_univ hA hB

/-- **`lam`.**  Interface facts: the body's membership in the codomain
under the binder, the two hereditary halves, and the typing of the
domain and the codomain fibres.  No empty-domain side condition. -/
theorem sound_lam {ρ : Nat → V} {Aa ba Ba : Term}
    (hokA : WellDenoted V ρ Aa) (hAt : IsTy (interp V ρ Aa))
    (hokb : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) ba)
    (hb : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) ba ∈ˢ interp V (cons x ρ) Ba)
    (hBt : ∀ x, x ∈ˢ interp V ρ Aa → IsTy (interp V (cons x ρ) Ba)) :
    WellDenoted V ρ (.lam Aa ba) ∧
      interp V ρ (.lam Aa ba)
        ∈ˢ interp V ρ (.pi Aa Ba) := by
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_lam]
    exact ⟨hokA, hAt, hokb⟩
  · rw [interp_lam, interp_pi]
    exact lamV_mem hb hBt

/-! ## The application row -/

/-- **`app`.**  Interface facts: the function's membership at a `Π`,
the argument's in its domain, and the domain's typing. -/
theorem sound_app {ρ : Nat → V} {fa aa Aa Ba : Term}
    (hokf : WellDenoted V ρ fa) (hoka : WellDenoted V ρ aa)
    (hf : interp V ρ fa ∈ˢ interp V ρ (.pi Aa Ba))
    (ha : interp V ρ aa ∈ˢ interp V ρ Aa)
    (hdom : IsTy (interp V ρ Aa)) :
    WellDenoted V ρ (.app fa aa) ∧
      interp V ρ (.app fa aa) ∈ˢ interp V ρ (Ba.inst aa) := by
  refine ⟨WellDenoted_app_of V hokf hoka hf ha hdom, ?_⟩
  rw [interp_pi] at hf
  rw [interp_app, interp_inst0]
  exact app_mem_piV hf ha

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
