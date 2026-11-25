module

public import ConLeche.Model.Env.EnvModelM
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Model.Currency
public import ConLeche.Rules.Rel
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.WellDenotedTransport
import ConLeche.Rules.Rigid

public section

/-!
# The io grade's claim: hereditary membership, keyed on the type's syntax (task #342 L18)

The fragment's `IORel` (`whitepaper/Fragment/IOGrade.lean`, task #346)
at the real checker's syntax.  An io-inferred type does not hold its
term: `(fun (h : False) => (h.elim : Nat)) 0` is well-denoted, denotes
the point (an abstraction over an empty domain), and the point is no
member of `Nat`; and "a member unless the point" fails at λ:
`fun (x : Bool) => h x 0` with `h : (b : Bool) → Bool.rec False Nat b →
Nat` is a graph that is the point at `false` and no member of
`Bool → Nat`.  What holds is the hereditary claim: the value is the
point, or a member of the type, or — when the type is syntactically a
∀ — a graph over the ∀'s domain, not the point everywhere, whose
every application satisfies the claim at the ∀'s opened body.

It is keyed on the type's *syntax* (an `Expr` at its opening depth),
not on its reading: two ∀s with equal values need not have equal
domains, and a stored constant may read as a Π.  It is carried along a
reduction of the type by `Red.rigid` (a ∀ reduces only to itself), and
through the substitution of an application's argument by
`denote_substFvarAt`.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **The member half**: the type reads, is a graded type, and holds
the value. -/
@[expose] def IOMem (m : EnvModel V env) (φ : Name → Nat) (d : Nat) (T : Expr)
    (ρ : Nat → V) (v : V) : Prop :=
  ∃ ta, denote m.acval env φ d T = some ta ∧ WellDenotedTy V ρ ta ∧
    v ∈ˢ interp V ρ ta

/-- **The hereditary half**, by recursion on the type's syntax: at a
∀, a graph over its domain (a graded type) that is not everywhere the
point, whose every application is the point, a member of, or
hereditarily in the ∀'s body opened at the domain.  Nothing at any
other type. -/
@[expose] def IOHered (m : EnvModel V env) (φ : Name → Nat) :
    Nat → Expr → (Nat → V) → V → Prop
  | d, .forallE ty body, ρ, v =>
    ∃ tya, denote m.acval env φ d ty = some tya ∧ WellDenotedTy V ρ tya ∧
      (∃ (F : V → V) (hG : HasGraph (interp V ρ tya) F),
        v = graph F (interp V ρ tya) hG) ∧
      (∃ x, x ∈ˢ interp V ρ tya ∧ SetTheory.app v x ≠ pt) ∧
      ∀ x, x ∈ˢ interp V ρ tya →
        SetTheory.app v x = pt ∨
          IOMem m φ (d + 1) (body.instantiate1 (.fvar d ty)) (cons x ρ)
            (SetTheory.app v x) ∨
          IOHered m φ (d + 1) (body.instantiate1 (.fvar d ty)) (cons x ρ)
            (SetTheory.app v x)
  | _, _, _, _ => False
termination_by _ e => e.sizeB
decreasing_by
  rw [ConLeche.Expr.sizeB_instantiate1 _ rfl]; simp [ConLeche.Expr.sizeB]; omega

/-- **The io claim**: the point, a member, or hereditarily a member. -/
@[expose] def IORel (m : EnvModel V env) (φ : Name → Nat) (d : Nat) (T : Expr)
    (ρ : Nat → V) (v : V) : Prop :=
  v = pt ∨ IOMem m φ d T ρ v ∨ IOHered m φ d T ρ v

/-- **The io claim with its neutral clause**: at a subject whose spine
head is no λ and no `let` (`Expr.ioNeutral`), not hereditary. -/
@[expose] def IORelN (m : EnvModel V env) (φ : Name → Nat) (d : Nat) (e T : Expr)
    (ρ : Nat → V) (v : V) : Prop :=
  IORel m φ d T ρ v ∧ (e.ioNeutral = true → v = pt ∨ IOMem m φ d T ρ v)

variable {m : EnvModel V env} {φ : Name → Nat}

theorem IOHered_forallE {d : Nat} {ty body : Expr}
    {ρ : Nat → V} {v : V} :
    IOHered m φ d (.forallE ty body) ρ v ↔
      ∃ tya, denote m.acval env φ d ty = some tya ∧ WellDenotedTy V ρ tya ∧
        (∃ (F : V → V) (hG : HasGraph (interp V ρ tya) F),
        v = graph F (interp V ρ tya) hG) ∧
        (∃ x, x ∈ˢ interp V ρ tya ∧ SetTheory.app v x ≠ pt) ∧
        ∀ x, x ∈ˢ interp V ρ tya →
          IORel m φ (d + 1) (body.instantiate1 (.fvar d ty)) (cons x ρ)
            (SetTheory.app v x) := by
  rw [IOHered]; rfl

/-- The hereditary half lives at a ∀ only. -/
theorem IOHered.forallE {d : Nat} {T : Expr} {ρ : Nat → V} {v : V}
    (h : IOHered m φ d T ρ v) :
    ∃ ty body, T = .forallE ty body := by
  cases T with
  | forallE ty body => exact ⟨ty, body, rfl⟩
  | _ => simp [IOHered] at h

/-- The member half at a known reading. -/
theorem IOMem.of_reading {d : Nat} {T : Expr} {ta : Term} {ρ : Nat → V} {v : V}
    (hT : denote m.acval env φ d T = some ta) (h : IOMem m φ d T ρ v) :
    WellDenotedTy V ρ ta ∧ v ∈ˢ interp V ρ ta := by
  obtain ⟨ta', hta', hw, hmem⟩ := h
  obtain rfl : ta' = ta := Option.some.inj (hta'.symm.trans hT)
  exact ⟨hw, hmem⟩

/-- A membership is the io claim, neutral clause included. -/
theorem IORelN.of_mem {d : Nat} {e T : Expr} {ta : Term} {ρ : Nat → V} {v : V}
    (hT : denote m.acval env φ d T = some ta) (hw : WellDenotedTy V ρ ta)
    (hmem : v ∈ˢ interp V ρ ta) : IORelN m φ d e T ρ v :=
  ⟨Or.inr (Or.inl ⟨ta, hT, hw, hmem⟩), fun _ => Or.inr ⟨ta, hT, hw, hmem⟩⟩

/-- The point satisfies the io claim. -/
theorem IORelN.pt {d : Nat} {e T : Expr} {ρ : Nat → V} :
    IORelN m φ d e T ρ (pt : V) :=
  ⟨Or.inl rfl, fun _ => Or.inl rfl⟩

/-- **Where the type is not a ∀, the claim is the point or a member.** -/
theorem IORel.of_not_forallE {d : Nat} {T : Expr} {ρ : Nat → V} {v : V}
    (h : IORel m φ d T ρ v) (hT : ∀ ty body, T ≠ .forallE ty body) :
    v = pt ∨ IOMem m φ d T ρ v := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨ty, body, rfl⟩ := h.forallE
    exact absurd rfl (hT ty body)

/-- **The claim at a type that reduces to a non-∀** is the point or a
member: a hereditary claim's type is a ∀, which reduces only to itself
(`Red.rigid`).  So a value that is not the point is a member — the io
claim's consumers whose type reduces to a family's application (the
rescues' and structure η's major discovery, unit-like structures,
projections). -/
theorem IORel.mem_of_red {d : Nat} {T T' : Expr} {ρ : Nat → V} {v : V}
    (h : IORel m φ d T ρ v) (hv : v ≠ pt) (hr : ConLeche.Rules.Red env d T T')
    (hT' : ∀ ty body, T' ≠ .forallE ty body) : IOMem m φ d T ρ v := by
  rcases h with h | h | h
  · exact absurd h hv
  · exact h
  · obtain ⟨ty, body, rfl⟩ := h.forallE
    exact absurd (ConLeche.Rules.Red.rigid hr trivial) (hT' ty body)

/-- A constant-headed application is no ∀. -/
theorem not_forallE_of_getAppFn {T : Expr} {c : Name} {us : List ConLeche.Level}
    (h : T.getAppFn = .const c us) : ∀ ty body, T ≠ .forallE ty body := by
  rintro ty body rfl; exact nomatch h

/-! ## Through the substitution of a free variable -/

/-- **The claim through `substFvarAt`** — the hereditary claim at a
binder's opened body, at the valuation holding the argument's value,
is the claim at the body instantiated with the argument.  One direction
suffices: a type that is not a ∀ may become one (a variable
instantiated with a ∀), and a member of the variable's value is then a
member of the ∀'s. -/
theorem IOMem_substFvarAt {p : Nat} {a : Expr} {x : Term}
    (hwa : Expr.WScoped p a) (hba : a.looseBVarsBounded 0 = true)
    (ha : denote m.acval env φ p a = some x)
    {e : Expr} {D : Nat} {ρ : Nat → V} {v : V} (hpD : p ≤ D)
    (hfb : Expr.fvarsBelow (D + 1) e)
    (hwx : WellDenoted V (shiftE (D - p) 0 ρ) x)
    (h : IOMem m φ (D + 1) e (instE (D - p) (interp V (shiftE (D - p) 0 ρ) x) ρ) v) :
    IOMem m φ D (Expr.substFvarAt p a e) ρ v := by
  obtain ⟨ta, hta, hwT, hmem⟩ := h
  refine ⟨ta.inst x (D - p), ?_, ?_, ?_⟩
  · rw [denote_substFvarAt m.acval_closed (acval_inst_self m) hwa hba ha e D hpD hfb,
      hta]; rfl
  · refine ⟨(WellDenoted_inst V ta x (D - p) ρ hwx).mpr hwT.1, ?_⟩
    rw [interp_inst]; exact hwT.2
  · rw [interp_inst]; exact hmem

theorem IORel_substFvarAt {p : Nat} {a : Expr} {x : Term}
    (hwa : Expr.WScoped p a) (hba : a.looseBVarsBounded 0 = true)
    (ha : denote m.acval env φ p a = some x) :
    ∀ (e : Expr) (D : Nat) (ρ : Nat → V) (v : V), p ≤ D →
      Expr.fvarsBelow (D + 1) e →
      WellDenoted V (shiftE (D - p) 0 ρ) x →
      IORel m φ (D + 1) e (instE (D - p) (interp V (shiftE (D - p) 0 ρ) x) ρ) v →
      IORel m φ D (Expr.substFvarAt p a e) ρ v
  | .forallE ty body, D, ρ, v, hpD, hfb, hwx, h => by
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (IOMem_substFvarAt hwa hba ha hpD hfb hwx h))
    · rw [IOHered_forallE] at h
      obtain ⟨tya, htya, hwT, ⟨F, hG, hF⟩, ⟨x₀, hx₀, hne⟩, hall⟩ := h
      have hfb' : Expr.fvarsBelow (D + 1) ty ∧ Expr.fvarsBelow (D + 1) body := hfb
      refine Or.inr (Or.inr ?_)
      show IOHered m φ D
        (.forallE (Expr.substFvarAt p a ty) (Expr.substFvarAt p a body)) ρ v
      rw [IOHered_forallE]
      have hint : interp V ρ (tya.inst x (D - p))
          = interp V (instE (D - p) (interp V (shiftE (D - p) 0 ρ) x) ρ) tya :=
        interp_inst V tya x (D - p) ρ
      refine ⟨tya.inst x (D - p), ?_,
        ⟨(WellDenoted_inst V tya x (D - p) ρ hwx).mpr hwT.1, by rw [hint]; exact hwT.2⟩,
        ⟨F, hint ▸ hG, by simp only [hint]; exact hF⟩, ⟨x₀, by rw [hint]; exact hx₀, hne⟩, fun y hy => ?_⟩
      · rw [denote_substFvarAt m.acval_closed (acval_inst_self m) hwa hba ha ty D hpD
          hfb'.1, htya]; rfl
      rw [hint] at hy
      have hrec := IORel_substFvarAt hwa hba ha (body.instantiate1 (.fvar (D + 1) ty))
        (D + 1) (cons y ρ) (SetTheory.app v y) (by omega)
        (ConLeche.Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (by rw [show D + 1 - p = (D - p) + 1 by omega, shiftE_succ_cons]; exact hwx)
        (by
          rw [show D + 1 - p = (D - p) + 1 by omega, shiftE_succ_cons, ← cons_instE]
          exact hall y hy)
      rwa [ConLeche.Expr.substFvarAt_instantiate1 hpD hba body 0] at hrec
  | .bvar _, _, _, _, hpD, hfb, hwx, h | .fvar _ _, _, _, _, hpD, hfb, hwx, h
  | .sort _, _, _, _, hpD, hfb, hwx, h | .const _ _, _, _, _, hpD, hfb, hwx, h
  | .app _ _, _, _, _, hpD, hfb, hwx, h | .lam _ _, _, _, _, hpD, hfb, hwx, h
  | .letE _ _ _, _, _, _, hpD, hfb, hwx, h | .lit _, _, _, _, hpD, hfb, hwx, h
  | .proj _ _ _, _, _, _, hpD, hfb, hwx, h => by
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (IOMem_substFvarAt hwa hba ha hpD hfb hwx h))
    · obtain ⟨_, _, he⟩ := h.forallE; exact nomatch he
termination_by e => e.sizeB
decreasing_by
  rw [ConLeche.Expr.sizeB_instantiate1 _ rfl]; simp [ConLeche.Expr.sizeB]; omega

end ConLeche.Model.Rules
