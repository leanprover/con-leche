import Setlec.Kernel.Env

/-!
# The pinned basis inductives

The lean-inductive-models preprocessor reduces every supported inductive
to the five-member basis `Eq`, `Nat`, `PSigma'`, `PUnit`, `Quot` (plus
standard axioms); these are the only inductives the checker implements
natively (hand-written set models).  The declarations here are pinned to
exactly what the preprocessor emits — the frontend compares incoming
records against these and declines anything else.

This file is generated from the preprocessor's own emission (see
DESIGN.md); do not edit the expressions by hand.
-/

namespace Setlec

open Name (anonymous)

/-- The name of the basis dependent-pair type. -/
def psigmaName : Name := anonymous |>.str "PSigma'"

/-- The name of the basis dependent-pair constructor. -/
def psigmaMkName : Name := psigmaName |>.str "mk"

/-- The pinned `Eq` basis block. -/
def eqBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Eq"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.forallE (anonymous |>.str "b") (.bvar 1) (.sort .zero) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩,
  .ctorInfo ⟨((anonymous |>.str "Eq") |>.str "refl"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 1)) (.bvar 0)) (.bvar 0)) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩ 2 0,
  .recInfo ⟨((anonymous |>.str "Eq") |>.str "rec"), [(anonymous |>.str "u_1"), (anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "b") (.bvar 1) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, none⟩) ⟨.default, none⟩) (.forallE (anonymous |>.str "refl") (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const ((anonymous |>.str "Eq") |>.str "refl") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1))) (.forallE (anonymous |>.str "b") (.bvar 3) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 4)) (.bvar 3)) (.bvar 0)) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) ⟨.default, none⟩) ⟨.implicit, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩)⟩ 2 1 1 1
    [⟨((anonymous |>.str "Eq") |>.str "refl"), 0, (.lam (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.lam (anonymous |>.str "a") (.bvar 0) (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "b") (.bvar 1) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, none⟩) ⟨.default, none⟩) (.lam (anonymous |>.str "refl") (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const ((anonymous |>.str "Eq") |>.str "refl") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1))) (.bvar 0) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩]]

/-- The pinned `Nat` basis block. -/
def natBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Nat"), [], (.sort (.succ .zero))⟩,
  .ctorInfo ⟨((anonymous |>.str "Nat") |>.str "zero"), [], (.const (anonymous |>.str "Nat") [])⟩ 0 0,
  .ctorInfo ⟨((anonymous |>.str "Nat") |>.str "succ"), [], (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.const (anonymous |>.str "Nat") []) ⟨.default, none⟩)⟩ 0 1,
  .recInfo ⟨((anonymous |>.str "Nat") |>.str "rec"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.forallE (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, none⟩) ⟨.default, none⟩) (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.app (.bvar 3) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩ 0 1 2 0
    [⟨((anonymous |>.str "Nat") |>.str "zero"), 0, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, none⟩) (.lam (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.lam (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, none⟩) ⟨.default, none⟩) (.bvar 1) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩)⟩,
      ⟨((anonymous |>.str "Nat") |>.str "succ"), 1, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, none⟩) (.lam (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.lam (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, none⟩) ⟨.default, none⟩) (.lam (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.app (.app (.bvar 1) (.bvar 0)) (.app (.app (.app (.app (.const ((anonymous |>.str "Nat") |>.str "rec") [(.param (anonymous |>.str "u"))]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩)⟩]]

/-- The pinned `PSigma'` basis block. -/
def psigmaBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "PSigma'"), [(anonymous |>.str "u"), (anonymous |>.str "v")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "β") (.forallE (anonymous |>.str "x") (.bvar 0) (.sort (.param (anonymous |>.str "v"))) ⟨.default, none⟩) (.sort (.max (.param (anonymous |>.str "u")) (.param (anonymous |>.str "v")))) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩,
  .ctorInfo ⟨((anonymous |>.str "PSigma'") |>.str "mk"), [(anonymous |>.str "u"), (anonymous |>.str "v")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "β") (.forallE (anonymous |>.str "x") (.bvar 0) (.sort (.param (anonymous |>.str "v"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "fst") (.bvar 1) (.forallE (anonymous |>.str "snd") (.app (.bvar 1) (.bvar 0)) (.app (.app (.const (anonymous |>.str "PSigma'") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 3)) (.bvar 2)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩)⟩ 2 2,
  .recInfo ⟨((anonymous |>.str "PSigma'") |>.str "rec"), [(anonymous |>.str "u"), (anonymous |>.str "v")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "β") (.forallE (anonymous |>.str "x") (.bvar 0) (.sort (.param (anonymous |>.str "v"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.app (.app (.const (anonymous |>.str "PSigma'") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 1)) (.bvar 0)) (.sort .zero) ⟨.default, none⟩) (.forallE (anonymous |>.str "mk") (.forallE (anonymous |>.str "fst") (.bvar 2) (.forallE (anonymous |>.str "snd") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 2) (.app (.app (.app (.app (.const ((anonymous |>.str "PSigma'") |>.str "mk") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))) ⟨.default, none⟩) ⟨.default, none⟩) (.forallE (anonymous |>.str "t") (.app (.app (.const (anonymous |>.str "PSigma'") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 3)) (.bvar 2)) (.app (.bvar 2) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩)⟩ 2 1 1 0
    [⟨((anonymous |>.str "PSigma'") |>.str "mk"), 2, (.lam (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.lam (anonymous |>.str "β") (.forallE (anonymous |>.str "x") (.bvar 0) (.sort (.param (anonymous |>.str "v"))) ⟨.default, none⟩) (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.app (.app (.const (anonymous |>.str "PSigma'") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 1)) (.bvar 0)) (.sort .zero) ⟨.default, none⟩) (.lam (anonymous |>.str "mk") (.forallE (anonymous |>.str "fst") (.bvar 2) (.forallE (anonymous |>.str "snd") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 2) (.app (.app (.app (.app (.const ((anonymous |>.str "PSigma'") |>.str "mk") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))) ⟨.default, none⟩) ⟨.default, none⟩) (.lam (anonymous |>.str "fst") (.bvar 3) (.lam (anonymous |>.str "snd") (.app (.bvar 3) (.bvar 0)) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩]]

/-- The pinned `PUnit` basis block. -/
def punitBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "PUnit"), [(anonymous |>.str "u")], (.sort (.param (anonymous |>.str "u")))⟩,
  .ctorInfo ⟨((anonymous |>.str "PUnit") |>.str "unit"), [(anonymous |>.str "u")], (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))])⟩ 0 0,
  .recInfo ⟨((anonymous |>.str "PUnit") |>.str "rec"), [(anonymous |>.str "u_1"), (anonymous |>.str "u")], (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "unit") (.app (.bvar 0) (.const ((anonymous |>.str "PUnit") |>.str "unit") [(.param (anonymous |>.str "u"))])) (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.app (.bvar 2) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩ 0 1 1 0
    [⟨((anonymous |>.str "PUnit") |>.str "unit"), 0, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, none⟩) (.lam (anonymous |>.str "unit") (.app (.bvar 0) (.const ((anonymous |>.str "PUnit") |>.str "unit") [(.param (anonymous |>.str "u"))])) (.bvar 0) ⟨.default, none⟩) ⟨.default, none⟩)⟩]]

/-- The constants of one basis block, in dependency order. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .psigmaK => psigmaBasis
  | .punitK => punitBasis

end Setlec
