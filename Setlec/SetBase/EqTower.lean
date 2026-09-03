import Setlec.Verify.EnvPreds
import Setlec.Verify.Denote.VClosed

/-!
# The `Eq` block's canonical value towers (task #161, S1)

THE SEPARATION's shared base: the three canonical `VExpr` towers of the
`Eq` basis block, lifted out of `SetR/Install/BasisS.lean` (design
census §3.3, edge 5).  They are **model-free data** — closed `VExpr`
literals over the level valuation, naming no `EnvS`, no `interp` and no
relation of the `Infer`/`DefEq` family.  The collapsed lane installs
them (`Install/BasisS.lean`, which keeps every lemma ABOUT them); the
graded lane's `Interp2/EqTowerP.lean` states its annotated towers'
`erase` against them by `rfl`.

Statements verbatim from their old home; the namespace is unchanged.
-/

namespace Setlec.SetR
open Setlec.TT

/-- `Eq`'s valuation: the former, eta-expanded. -/
def eqValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) (.lam (.bvar 1)
    (.eqE (.bvar 2) (.bvar 1) (.bvar 0))))

/-- `Eq.refl`'s valuation. -/
def eqReflValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) .prf)

/-- `Eq.rec`'s valuation: the minor premise, returned.  Transport is
the identity — `eqRec_derivable` (`Setlec/TT/Examples.lean`), which is
why the layer does not carry `Eq.rec` at all. -/
def eqRecValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN))
    (.lam (.bvar 0)
      (.lam (.pi (.bvar 1)
          (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1N))))
        (.lam (.app (.app (.bvar 0) (.bvar 1))
            (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]))
          (.lam (.bvar 3)
            (.lam (VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
              (.bvar 2))))))


end Setlec.SetR
