import Setlec.SetR.Interp2.BasisConsP
import Setlec.SetBase.EqTower

/-!
# The annotated hand-built basis towers, `Eq` family (task #161, ENDGAME E)

The ENDGAME D seal's §4 named the basis tier's one wall: `pinnedDirectT`
has no entry for `Eq`, `Eq.refl`, `Eq.rec` or `PSigma'.rec`, and `BConst`
has no such constructors, so `acval_basis_pinned` — which unlocks the
other five blocks' leaves — is *empty* on `eqK`.  v1 builds those leaves
by hand (`Install/BasisS.lean`'s `eqValT`/`eqReflValT`/`eqRecValT`) and
derives `EqLawV` from the tower; the P tier needs the **annotated**
towers, whose binder numerals `interp2` dispatches on.

## The bits are NOT chosen — `mem_typeP` pins every one of them

The DESIGN entry "the chosen bits of the hand-built basis towers"
licensed a *choice* here (graph-regime bits, model-side data, no
establishment doctrine touched) and fenced it as the campaign's only
such site.  **The license is not exercised, because there is nothing
left to choose.**  Every one of these towers is stored at a constant
whose type is *also* stored, and `EnvS2PM.mem_typeP` demands

> `interp2 ρ (acval n ψ) ∈ˢ interp2 ρ (the type's reading)`

whose right-hand side is a `piR` tower whose numerals are the pinned
declaration's own `pw` data (`pwBit ψ`).  `lamR`/`piR` disagree
irreconcilably across the regime split — `bit_forced_pos` and
`bit_forced_zero` below — so the tower's λ bit at every binder is
*forced* to agree in zero-ness with the corresponding `pi` bit of the
pinned type.  Concretely:

| tower | pinned `pw` | forced bits |
|---|---|---|
| `eqValT2` | `.never` ×3 | all **nonzero** (the ratified choice, arrived at by force) |
| `eqReflValT2` | `.ifAllZero []` ×2 | all **zero** |
| `eqRecValT2` | `.ifAllZero [u_1]` ×6 | zero **iff `ψ u_1 = 0`** |

So the design entry's counterfactual (iii) is right about `Eq` and
inverted at `Eq.refl`: there bit `0` is not the collapse, it is the only
legal value, and a nonzero bit is what would break the law.  Nothing is
free; the doctrine "bits are never taken from a metatheorem" holds here
in its strongest form — the bits come from the *pin*, exactly as at the
sixteen `pinnedDirectT` blocks, only through `mem_typeP` rather than
through `pinnedDirectT`.

The scope fence in the DESIGN entry therefore stands unused, and should
be recorded as such rather than deleted: a future hand-built value at a
constant whose type is *not* stored would still have a genuine choice.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS eqValT eqReflValT eqRecValT)
open Setlec (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The forcing lemmas

Two lines each, and together they are the whole reason this file has no
freedom.  A λ-tower's numeral and its type's numeral must agree in
zero-ness, because the two regimes' inhabitants are disjoint: above
zero a `lamR` is a graph and a `piR` is a set of graphs; at zero a
`lamR` is `pt` and a `piR` is a truth value, whose only member is
`pt`. -/

/-- **A graph-regime abstraction never inhabits a squash-regime
product.**  So a tower whose stored type's binder carries bit `0` may
not carry a nonzero bit. -/
theorem bit_forced_pos {v : Nat} {A : V} {F B : V → V} (hv : v ≠ 0)
    (h : lamR v A F ∈ˢ piR 0 A B) : False :=
  lamR_ne_pt hv (eq_pt_of_mem_piR_zero h)

/-- **A squash-regime abstraction inhabits a graph-regime product only
if the product is degenerate.**  The complement of `bit_forced_pos`:
`pt` is not a graph, so at a nonempty domain with inhabited fibres the
membership fails.  (Stated as the contrapositive the towers use: from
the membership and a domain witness, the product's fibre at that
witness is a truth value.) -/
theorem bit_forced_zero {v : Nat} {A a : V} {F B : V → V} (hv : v ≠ 0)
    (h : lamR 0 A F ∈ˢ piR v A B) (ha : a ∈ˢ A) :
    (pt : V) ∈ˢ B a := by
  rw [lamR_zero] at h
  exact app_pt (V := V) a ▸ app_mem_piR_pos hv h ha

/-! ## `Eq` — all three bits nonzero, forced

The pinned `Eq` carries `pw = .never` at all three binders, and it is
right to: the codomain of the innermost binder is `Prop`, and `Prop`
*as a type* lives in `Sort 1`.  The `v'`-for-a-`Sort` trap
(`Interp2/BasisType.lean`'s docstring) is exactly what makes the `Eq`
former a graph and not a proof point. -/

/-- `Eq`'s annotated valuation: v1's `eqValT` with all three binders in
the graph regime (forced — see the module docstring). -/
def eqValT2 (ψ : Name → Nat) : AVExpr :=
  .lam 1 (.sort (ψ uN)) (.lam 1 (.bvar 0) (.lam 1 (.bvar 1)
    (.eqE (.bvar 2) (.bvar 1) (.bvar 0))))

/-- `Eq.refl`'s annotated valuation: `.prf` under two **squash-regime**
binders (forced: the pinned `pw` is `.ifAllZero []` at both, because
`Eq α a a` is a proposition). -/
def eqReflValT2 (ψ : Name → Nat) : AVExpr :=
  .lam 0 (.sort (ψ uN)) (.lam 0 (.bvar 0) .prf)

/-- `Eq.rec`'s annotated valuation: the minor premise, returned, under
six binders whose bit is the motive level's own zero test — the pinned
`pw` is `.ifAllZero [u_1]` at every one of them. -/
def eqRecValT2 (ψ : Name → Nat) : AVExpr :=
  let m : Nat := pwBit ψ (.ifAllZero [u1N])
  .lam m (.sort (ψ uN))
    (.lam m (.bvar 0)
      (.lam m (.pi 0 1 (.bvar 1)
          (.pi 0 (ψ u1N + 1)
            (AVExpr.mkAppN (eqValT2 ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1N))))
        (.lam m (.app (.app (.bvar 0) (.bvar 1))
            (AVExpr.mkAppN (eqReflValT2 ψ) [.bvar 2, .bvar 1]))
          (.lam m (.bvar 3)
            (.lam m (AVExpr.mkAppN (eqValT2 ψ) [.bvar 4, .bvar 3, .bvar 0])
              (.bvar 2))))))

/-! ### Erasure: the towers project onto v1's -/

@[simp] theorem eqValT2_erase (ψ : Name → Nat) :
    (eqValT2 ψ).erase = eqValT ψ := rfl

@[simp] theorem eqReflValT2_erase (ψ : Name → Nat) :
    (eqReflValT2 ψ).erase = eqReflValT ψ := rfl

@[simp] theorem eqRecValT2_erase (ψ : Name → Nat) :
    (eqRecValT2 ψ).erase = eqRecValT ψ := rfl

/-! ### The towers read the assignment only at their own level names -/

theorem eqValT2_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqValT2 ψ₁ = eqValT2 ψ₂ := by rw [eqValT2, eqValT2, h]

theorem eqReflValT2_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqReflValT2 ψ₁ = eqReflValT2 ψ₂ := by rw [eqReflValT2, eqReflValT2, h]

/-! ## `Eq`'s tower, interpreted -/

/-- **`Eq`'s tower, interpreted**: a three-deep graph-regime `lamR` over
the truth-set former. -/
theorem eqValT2_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (eqValT2 ψ)
      = lamR 1 (univ (ψ uN))
        (fun a => lamR 1 a (fun x => lamR 1 a (fun y => eqv x y))) := by
  simp [eqValT2, cons]

/-- **The full spine's value** — `EqLawP`'s first conjunct at the tower:
three `app_lamR_pos`, one per binder, each on its domain. -/
theorem eqValT2_app₃ (ψ : Name → Nat) (ρ : Nat → V) (A a b : V)
    (hA : A ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app
        (interp2 V ρ (eqValT2 ψ)) A) a) b = eqv a b := by
  rw [eqValT2_interp, app_lamR_pos Nat.one_ne_zero hA,
    app_lamR_pos Nat.one_ne_zero ha, app_lamR_pos Nat.one_ne_zero hb]

/-- The tower inhabits the `Eq` former's product tower, at the pinned
type's own numerals (all nonzero). -/
theorem eqValT2_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (eqValT2 ψ) ∈ˢ piR 1 (univ (ψ uN) : V)
      (fun a => piR 1 a (fun _ => piR 1 a (fun _ => univZero))) := by
  rw [eqValT2_interp]
  exact lamR_mem (fun _a _ => lamR_mem (fun _x _ =>
    lamR_mem (fun _y _ => eqv_mem_univZero _ _)))

/-- The tower is graded (`AnnotOk2`), at every environment. -/
theorem eqValT2_ok2 (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOk2 V ρ (eqValT2 ψ) := by
  refine ⟨trivial, fun A _ => ⟨trivial, fun a _ => ⟨trivial,
    fun b _ => ⟨trivial, trivial⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨fun _ => univZero, fun _ _ => eqv_mem_univZero _ _,
      fun h => nomatch h⟩
  · exact ⟨fun _ => piR 1 A (fun _ => univZero),
      fun _ _ => lamR_mem fun _ _ => eqv_mem_univZero _ _,
      fun h => nomatch h⟩
  · exact ⟨fun x => piR 1 x (fun _ => piR 1 x (fun _ => univZero)),
      fun _ _ => lamR_mem fun _ _ =>
        lamR_mem fun _ _ => eqv_mem_univZero _ _,
      fun h => nomatch h⟩

/-- The tower is bit-valid (`AnnotValidV`) — the `lam` clause is
bit-free, so this is pure structure. -/
theorem eqValT2_validV (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotValidV V ρ (eqValT2 ψ) := by
  refine ⟨trivial, fun A _ => ⟨trivial, fun a _ => ⟨trivial,
    fun b _ => ⟨trivial, trivial⟩⟩⟩⟩

/-- The P currency, packaged. -/
theorem eqValT2_okP (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (eqValT2 ψ) :=
  ⟨eqValT2_ok2 ψ ρ, eqValT2_validV ψ ρ⟩

/-! ## `Eq.refl`'s tower, interpreted — the squash regime, forced -/

/-- **`Eq.refl`'s tower, interpreted**: `pt`, because its outer binder's
codomain `(a : α) → Eq α a a` is a proposition. -/
theorem eqReflValT2_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (eqReflValT2 ψ) = (pt : V) := by
  simp [eqReflValT2, lamR_zero]

/-- The tower inhabits `Eq.refl`'s product tower at the pinned type's
numerals (both zero) — `pt_mem_piR_zero_of` twice, bottoming at
`pt_mem_eqv_self`. -/
theorem eqReflValT2_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (eqReflValT2 ψ) ∈ˢ piR 0 (univ (ψ uN) : V)
      (fun a => piR 0 a (fun x => eqv x x)) := by
  rw [eqReflValT2_interp]
  exact pt_mem_piR_zero_of fun _A _ =>
    pt_mem_piR_zero_of fun x _ => pt_mem_eqv_self x

theorem eqReflValT2_ok2 (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOk2 V ρ (eqReflValT2 ψ) := by
  refine ⟨trivial, fun A _ => ⟨trivial, fun _a _ => trivial, ?_⟩, ?_⟩
  · exact ⟨fun x => eqv x x, fun x _ => pt_mem_eqv_self x,
      fun _ x _ => eqv_mem_univZero x x⟩
  · exact ⟨fun x => piR 0 x (fun y => eqv y y),
      fun _ _ => pt_mem_piR_zero_of fun y _ => pt_mem_eqv_self y,
      fun _ _ _ => piR_zero_mem_univZero⟩

theorem eqReflValT2_validV (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotValidV V ρ (eqReflValT2 ψ) :=
  ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩

theorem eqReflValT2_okP (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (eqReflValT2 ψ) :=
  ⟨eqReflValT2_ok2 ψ ρ, eqReflValT2_validV ψ ρ⟩

/-! ## `EqLawP`, discharged from the tower

The field the ENDGAME D seal named as `eqK`'s whole content, and the
reason `eqLawP_cons_fresh` is structurally unavailable at this block
(its side condition is `eqName ≠ c₀.name` and the cons *is* `Eq`).
Both conjuncts come off `eqValT2` directly:

* the **value** clause is `eqValT2_app₃` — three `app_lamR_pos`, one
  per binder, each on its own domain.  v1 needs two `app_lamC`s and
  states the law at the two-fold application because its η/unit
  consumers want the rigidity clause; the P consumers read the
  three-fold form, so all three fire here;
* the **grading** clause — which v1 has no analogue of — is the
  `AnnotOk2` `.app` chain over `eqValT2_mem`, whose three `v = 0`
  fibre obligations are all vacuous (the bits are nonzero), plus
  `eqv_mem_univZero` for the propositionhood half. -/

/-- **The `Eq` spine over the tower is graded, and is a proposition.**
`EqLawP`'s second conjunct, factored out: the `Eq.refl` and `Eq.rec`
type readings both mention the spine directly, not through the
field. -/
theorem eqValT2_app₃_okP (ψ : Name → Nat) (ρ : Nat → V)
    {Aa la ra : AVExpr} (hAa : AnnotOkP V ρ Aa) (hla : AnnotOkP V ρ la)
    (hra : AnnotOkP V ρ ra)
    (hA : interp2 V ρ Aa ∈ˢ (univ (ψ uN) : V))
    (ha : interp2 V ρ la ∈ˢ interp2 V ρ Aa)
    (hb : interp2 V ρ ra ∈ˢ interp2 V ρ Aa) :
    AnnotOkP V ρ (.app (.app (.app (eqValT2 ψ) Aa) la) ra) ∧
      interp2 V ρ (.app (.app (.app (eqValT2 ψ) Aa) la) ra)
        ∈ˢ (univZero : V) := by
  have hmem := eqValT2_mem (V := V) ψ ρ
  have h1 : SetTheory.app (interp2 V ρ (eqValT2 ψ)) (interp2 V ρ Aa)
      ∈ˢ piR 1 (interp2 V ρ Aa)
        (fun _ => piR 1 (interp2 V ρ Aa) (fun _ => univZero)) :=
    app_mem_piR_pos Nat.one_ne_zero hmem hA
  have h2 : SetTheory.app (SetTheory.app (interp2 V ρ (eqValT2 ψ))
        (interp2 V ρ Aa)) (interp2 V ρ la)
      ∈ˢ piR 1 (interp2 V ρ Aa) (fun _ => univZero) :=
    app_mem_piR_pos Nat.one_ne_zero h1 ha
  refine ⟨⟨⟨⟨⟨eqValT2_ok2 ψ ρ, hAa.1, 1, _, _, hmem, hA,
      fun h => nomatch h⟩, hla.1, 1, _, _, h1, ha,
      fun h => nomatch h⟩, hra.1, 1, _, _, h2, hb,
      fun h => nomatch h⟩,
    ⟨⟨eqValT2_validV ψ ρ, hAa.2⟩, hla.2⟩, hra.2⟩, ?_⟩
  rw [interp2_app, interp2_app, interp2_app,
    eqValT2_app₃ ψ ρ _ _ _ hA ha hb]
  exact eqv_mem_univZero _ _

/-- **`EqLawP` from the tower.**  Any environment carrier whose `Eq`
leaf is the annotated tower satisfies the field. -/
theorem eqLawP_of_tower {env : Setlec.Env} (m : EnvS2Core V env)
    (hleaf : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT2 ψ) :
    EqLawP m := by
  intro _hf ψ
  refine ⟨fun ρ A a b hA ha hb => ?_, fun ρ Aa la ra hAa hla hra
    hA ha hb => ?_⟩
  · rw [hleaf]; exact eqValT2_app₃ ψ ρ A a b hA ha hb
  · rw [hleaf]
    exact eqValT2_app₃_okP ψ ρ hAa hla hra hA ha hb

end Setlec.SetR.Interp2
