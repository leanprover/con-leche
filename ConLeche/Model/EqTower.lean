module

public import ConLeche.Model.BasisCons
public import ConLeche.Semantics.EqTower

public section

/-!
# The hand-built basis towers, `Eq` family (task #161)

`pinnedStructT` has no entry for `Eq`, `Eq.refl` or `Eq.rec`, and
`BConst` has no such constructors, so `EnvModel.acval_pinned` — which
unlocks the other blocks' leaves — is *empty* on `eqK`.  The leaves are
built by hand: `Semantics/EqTower.lean`'s `eqValT`/`eqReflValT`/
`eqRecValT`, and here are their laws.

The binders carry no regime: `interp` reads it off the values
(`lamV`).  `Eq`'s innermost body is a truth value, never the point, so
its tower is a graph wherever its domains are inhabited; `Eq.refl`'s
body is the proof, so its tower is the point.  Each inhabits its
pinned type's (value-read) reading by `lamV_mem`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (eqValT eqReflValT eqRecValT)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ### The towers read the assignment only at their own level names -/

theorem eqValT_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqValT ψ₁ = eqValT ψ₂ := by rw [eqValT, eqValT, h]

theorem eqReflValT_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqReflValT ψ₁ = eqReflValT ψ₂ := by rw [eqReflValT, eqReflValT, h]

/-! ## `Eq`'s tower, interpreted -/

/-- **`Eq`'s tower, interpreted**: a three-deep `lamV` over the
truth-set former. -/
theorem eqValT_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValT ψ)
      = lamV (univ (ψ uN))
        (fun a => lamV a (fun x => lamV a (fun y => eqv x y))) := by
  simp [eqValT, cons]

/-- **The full spine's value** — `EqLaw`'s first conjunct at the tower:
three `app_lamV`, one per binder, each on its domain. -/
theorem eqValT_app₃ (ψ : Name → Nat) (ρ : Nat → V) (A a b : V)
    (hA : A ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app
        (interp V ρ (eqValT ψ)) A) a) b = eqv a b := by
  rw [eqValT_interp, app_lamV hA, app_lamV ha, app_lamV hb]

/-- The tower inhabits the `Eq` former's function-space tower. -/
theorem eqValT_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValT ψ) ∈ˢ piV (univ (ψ uN) : V)
      (fun a => piV a (fun _ => piV a (fun _ => univZero))) := by
  rw [eqValT_interp]
  exact lamV_mem (fun _a _ => lamV_mem (fun _x _ =>
    lamV_mem (fun _y _ => eqv_mem_univZero _ _) (fun _ _ => IsTy_univZero))
    (fun _ _ => IsTy_piV)) (fun _ _ => IsTy_piV)

/-- The tower is graded (`WellDenoted`), at every environment. -/
theorem eqValT_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (eqValT ψ) := by
  refine ⟨trivial, IsTy_univ _, fun A hA => ⟨trivial, IsTy_of_mem_univ hA,
    fun a _ => ⟨trivial, IsTy_of_mem_univ hA,
    fun b _ => ⟨trivial, trivial⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨fun _ => univZero, fun _ _ => eqv_mem_univZero _ _,
      fun _ _ => IsTy_univZero⟩
  · exact ⟨fun _ => piV A (fun _ => univZero),
      fun _ _ => lamV_mem (fun _ _ => eqv_mem_univZero _ _) (fun _ _ => IsTy_univZero),
      fun _ _ => IsTy_piV⟩
  · exact ⟨fun x => piV x (fun _ => piV x (fun _ => univZero)),
      fun _ _ => lamV_mem (fun _ _ =>
        lamV_mem (fun _ _ => eqv_mem_univZero _ _) (fun _ _ => IsTy_univZero))
        (fun _ _ => IsTy_piV),
      fun _ _ => IsTy_piV⟩

/-! ## `Eq.refl`'s tower, interpreted: the point -/

/-- **`Eq.refl`'s tower, interpreted**: `pt`, because its body is the
proof at every value. -/
theorem eqReflValT_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqReflValT ψ) = (pt : V) := by
  simp only [eqReflValT, interp_lam, interp_prf]
  exact lamV_eq_pt fun A _ => lamV_eq_pt fun _ _ => rfl

/-- The tower inhabits `Eq.refl`'s function-space tower: both fibres
are truth values, so it is `pt_mem_piR_zero_of` twice, bottoming at
`pt_mem_eqv_self`. -/
theorem eqReflValT_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqReflValT ψ) ∈ˢ piV (univ (ψ uN) : V)
      (fun a => piV a (fun x => eqv x x)) := by
  rw [eqReflValT_interp, piV_eq_zero fun A _ => by
    rw [piV_eq_zero fun x _ => eqv_mem_univZero x x]; exact piR_zero_mem_univZero]
  exact pt_mem_piR_zero_of fun A _ => by
    rw [piV_eq_zero fun x _ => eqv_mem_univZero x x]
    exact pt_mem_piR_zero_of fun x _ => pt_mem_eqv_self x

theorem eqReflValT_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (eqReflValT ψ) := by
  refine ⟨trivial, IsTy_univ _, fun A hA => ⟨trivial, IsTy_of_mem_univ hA,
    fun _a _ => trivial, ?_⟩, ?_⟩
  · exact ⟨fun x => eqv x x, fun x _ => pt_mem_eqv_self x,
      fun x _ => IsTy_eqv x x⟩
  · exact ⟨fun x => piV x (fun y => eqv y y),
      fun _ _ => lamV_mem (fun y _ => pt_mem_eqv_self y) (fun y _ => IsTy_eqv y y),
      fun _ _ => IsTy_piV⟩

/-! ## `EqLaw`, discharged from the tower

`eqK`'s whole content, and the reason `eqLaw_cons_fresh` is structurally unavailable at this block
(its side condition is `eqName ≠ c₀.name` and the cons *is* `Eq`).
Both conjuncts come off `eqValT` directly:

* the **value** clause is `eqValT_app₃` — three `app_lamV`, one
  per binder, each on its own domain (the consumers read the
  three-fold form);
* the **grading** clause is the `WellDenoted` `.app` chain over
  `eqValT_mem` (each slot read off the `piV` membership), plus
  `eqv_mem_univZero` for the propositionhood half. -/

/-- **The `Eq` spine over the tower is graded, and is a proposition.**
`EqLaw`'s second conjunct, factored out: the `Eq.refl` and `Eq.rec`
type readings both mention the spine directly, not through the
field. -/
theorem eqValT_app₃_okP (ψ : Name → Nat) (ρ : Nat → V)
    {Aa la ra : Term} (hAa : WellDenoted V ρ Aa) (hla : WellDenoted V ρ la)
    (hra : WellDenoted V ρ ra)
    (hA : interp V ρ Aa ∈ˢ (univ (ψ uN) : V))
    (ha : interp V ρ la ∈ˢ interp V ρ Aa)
    (hb : interp V ρ ra ∈ˢ interp V ρ Aa) :
    WellDenoted V ρ (.app (.app (.app (eqValT ψ) Aa) la) ra) ∧
      interp V ρ (.app (.app (.app (eqValT ψ) Aa) la) ra)
        ∈ˢ (univZero : V) := by
  have hmem := eqValT_mem (V := V) ψ ρ
  have h1 : SetTheory.app (interp V ρ (eqValT ψ)) (interp V ρ Aa)
      ∈ˢ piV (interp V ρ Aa)
        (fun _ => piV (interp V ρ Aa) (fun _ => univZero)) :=
    app_mem_piV hmem hA
  have h2 : SetTheory.app (SetTheory.app (interp V ρ (eqValT ψ))
        (interp V ρ Aa)) (interp V ρ la)
      ∈ˢ piV (interp V ρ Aa) (fun _ => univZero) :=
    app_mem_piV h1 ha
  have hAty : IsTy (interp V ρ Aa) := IsTy_of_mem_univ hA
  -- the application slot, read off a `piV` membership (`propN`)
  have slot : ∀ {f a A : V} {B : V → V}, f ∈ˢ piV A B → a ∈ˢ A → IsTy A →
      ∃ (v : Nat) (A' : V) (B' : V → V), f ∈ˢ piR v A' B' ∧ a ∈ˢ A' ∧
        (v = 0 → ∀ x, x ∈ˢ A' → B' x ∈ˢ (univZero : V)) ∧ (v ≠ 0 → IsTy A') :=
    fun {_ _ A B} hf ha hT => ⟨propN A B, A, B, hf, ha, propN_eq_zero.mp, fun _ => hT⟩
  refine ⟨⟨⟨⟨eqValT_wellDenoted ψ ρ, hAa, slot hmem hA (IsTy_univ _)⟩,
      hla, slot h1 ha hAty⟩, hra, slot h2 hb hAty⟩, ?_⟩
  rw [interp_app, interp_app, interp_app,
    eqValT_app₃ ψ ρ _ _ _ hA ha hb]
  exact eqv_mem_univZero _ _

/-- **`EqLaw` from the tower.**  Any environment carrier whose `Eq`
leaf is the tower `eqValT` satisfies the field. -/
theorem eqLaw_of_tower {env : ConLeche.Env} (m : EnvModel V env)
    (hE : env.find? eqName = some eqA)
    (hleaf : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValT ψ) :
    EqLaw m := by
  intro ci p hf hp ψ
  rw [hE] at hf
  obtain rfl := Option.some.inj hf
  have hp' : [uN] = [p] := hp
  obtain rfl : uN = p := (List.cons.inj hp').1
  refine ⟨fun ρ A a b hA ha hb => ?_, fun ρ Aa la ra hAa hla hra
    hA ha hb => ?_⟩
  · rw [hleaf]; exact eqValT_app₃ ψ ρ A a b hA ha hb
  · rw [hleaf]
    exact eqValT_app₃_okP ψ ρ hAa hla hra hA ha hb

end ConLeche.Model
