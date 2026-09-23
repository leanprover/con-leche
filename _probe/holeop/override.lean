import ConLeche.Model.Annot.BitInst
import ConLeche.Semantics.Kit

/-!
# HOLEOP probe: "members := X" as a valuation OVERRIDE is the fvar abstraction

The maintainer's override — read a constructor field with the block's
members interpreted as the hole — is, at the `denoteMeta` level, the
Expr-level ABSTRACTION `dom^abs := dom[T_m ↦ x_m]` (a fresh fvar `x_m`)
read at a frame holding the hole's curried family at `x_m`'s slot.
The two readings are tied by the EXISTING substitution lemma
`denoteMeta_substFvarAt`: substituting the member constant back for
the fvar reads as instantiating the abstract reading at the member's
LEAF.  Nothing new is needed; this file checks that the lemma's
premises are met by a constant (`WScoped` trivial, no loose bvars,
`denoteMeta_const`).

`hacl`/`hainst` are `EnvModel.acval_closed` and its `inst`
consequence; they are hypotheses here to keep the probe below the
`EnvModel` structure.
-/

open ConLeche ConLeche.Model ConLeche.Semantics ConLeche.Verify

universe w

variable {V : Type w} [SetTheory V]

/-- **The override law at `denoteMeta`.**  Reading the CONCRETE field
`dom = dom^abs[x_m := T_m.{us}]` at depth `D` is reading the ABSTRACT
field `dom^abs` at depth `D + 1` and instantiating the hole's bvar
(`D - p`) at the member's leaf `acval T_m ψ`. -/
theorem denoteMeta_override {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {T : Name} {us : List Level} {ci : ConstantInfo} (hf : env.find? T = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    {p : Nat} (e : Expr) (D : Nat) (hpD : p ≤ D) (hfb : Expr.fvarsBelow (D + 1) e) :
    denoteMeta acval env φ D (Expr.substFvarAt p (.const T us) e) =
      (denoteMeta acval env φ (D + 1) e).map
        (AnnotTerm.inst · (acval T (Level.substFn φ ci.toConstantVal.levelParams us)) (D - p)) :=
  denoteMeta_substFvarAt hacl hainst (p := p) (a := .const T us) (by simp [Expr.WScoped]) rfl
    (denoteMeta_const hf hlen) e D hpD hfb

/-- **The override law at `interp`.**  If the abstract field reads to
`A`, the concrete field reads to some `A'` whose value at any frame
`ρ` is `A`'s value at the frame with the LEAF'S VALUE inserted at the
hole's slot — so "members := X" at `X := ⟦T⟧` IS the stored field's
reading (the "at the carrier" law), and at any other `X` it is the
uniform operator's entry. -/
theorem interp_override {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {T : Name} {us : List Level} {ci : ConstantInfo} (hf : env.find? T = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    {p : Nat} (e : Expr) (D : Nat) (hpD : p ≤ D) (hfb : Expr.fvarsBelow (D + 1) e)
    {A : AnnotTerm} (he : denoteMeta acval env φ (D + 1) e = some A) :
    ∃ A', denoteMeta acval env φ D (Expr.substFvarAt p (.const T us) e) = some A' ∧
      ∀ ρ : Nat → V, interp V ρ A' =
        interp V (instE (D - p)
          (interp V (shiftE (D - p) 0 ρ) (acval T (Level.substFn φ ci.toConstantVal.levelParams us)))
          ρ) A := by
  refine ⟨_, by rw [denoteMeta_override hacl hainst hf hlen e D hpD hfb, he]; rfl, fun ρ => ?_⟩
  exact interp_inst V A _ (D - p) ρ

#print axioms denoteMeta_override
#print axioms interp_override
