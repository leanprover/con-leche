module

public import ConLeche.Verify.EnvPreds
public import ConLeche.Verify.Denote.VClosed

@[expose] public section

/-!
# The `Eq` block's canonical value towers (task #161, S1)

The three canonical `Term` towers of the `Eq` basis block.  They are
**model-free data** — closed `Term` literals over the level valuation,
naming no `interp` and no relation of the `Infer`/`DefEq` family.
`Model/EqTower.lean` states its annotated towers' `erase` against them
by `rfl`.
-/

namespace ConLeche.Semantics
open ConLeche.Term

/-- `Eq`'s valuation: the former, eta-expanded. -/
def eqValT (ψ : Name → Nat) : Term :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) (.lam (.bvar 1)
    (.eqE (.bvar 1) (.bvar 0))))

/-- `Eq.refl`'s valuation. -/
def eqReflValT (ψ : Name → Nat) : Term :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) .prf)

/-- `Eq.rec`'s valuation: the minor premise, returned.  Transport is
the identity, which is why the layer does not carry `Eq.rec` at all. -/
def eqRecValT (ψ : Name → Nat) : Term :=
  .lam (.sort (ψ uN))
    (.lam (.bvar 0)
      (.lam (.pi (.bvar 1)
          (.pi (Term.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1N))))
        (.lam (.app (.app (.bvar 0) (.bvar 1))
            (Term.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]))
          (.lam (.bvar 3)
            (.lam (Term.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
              (.bvar 2))))))



/-! ## The tower's closedness -/

/-- The tower is closed. -/
theorem eqValT_closed (ψ : Name → Nat) : Term.Closed (eqValT ψ) := by
  simp only [eqValT, Term.Closed, Term.bvarsBelow]
  exact ⟨trivial, by omega, by omega, by omega, by omega⟩


/-- `Eq.refl`'s tower is closed. -/
theorem eqReflValT_closed (ψ : Name → Nat) : Term.Closed (eqReflValT
  ψ) := by
  simp only [eqReflValT, Term.Closed, Term.bvarsBelow]
  exact ⟨trivial, by omega, trivial⟩

/-- `Eq.rec`'s tower is closed. -/
theorem eqRecValT_closed (ψ : Name → Nat) : Term.Closed (eqRecValT
  ψ) := by
  simp only [eqRecValT, Term.Closed, Term.bvarsBelow, Term.mkAppN,
    eqValT, eqReflValT]
  repeat' apply And.intro
  all_goals first | trivial | omega


end ConLeche.Semantics
