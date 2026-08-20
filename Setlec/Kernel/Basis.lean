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

/-- The name of the basis equality type. -/
def eqName : Name := anonymous |>.str "Eq"

/-- The name of the basis equality constructor. -/
def eqReflName : Name := eqName |>.str "refl"

/-- The name of the basis unit type. -/
def punitName : Name := anonymous |>.str "PUnit"

/-- The name `Nat`. -/
def natName : Name := anonymous |>.str "Nat"

/-- The name `Nat.zero`. -/
def natZeroName : Name := natName |>.str "zero"

/-- The name `Nat.succ`. -/
def natSuccName : Name := natName |>.str "succ"

/-- The name of the basis unit constructor. -/
def punitUnitName : Name := punitName |>.str "unit"

def emptyName : Name := anonymous |>.str "Empty"

/-- Names reserved for the pinned basis blocks; no other declaration
may use them. -/
def reservedBasisNames : List Name :=
  [eqName, eqReflName, eqName.str "rec",
   natName, natZeroName, natSuccName, natName.str "rec",
   psigmaName, psigmaMkName, psigmaName.str "rec",
   punitName, punitUnitName, punitName.str "rec",
   emptyName, emptyName.str "rec"]

/-- The pinned `Eq` basis block. -/
def eqBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Eq"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.forallE (anonymous |>.str "b") (.bvar 1) (.sort .zero) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩ {},
  .ctorInfo ⟨((anonymous |>.str "Eq") |>.str "refl"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 1)) (.bvar 0)) (.bvar 0)) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩ 2 0,
  .recInfo ⟨((anonymous |>.str "Eq") |>.str "rec"), [(anonymous |>.str "u_1"), (anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "b") (.bvar 1) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, none⟩) ⟨.default, none⟩) (.forallE (anonymous |>.str "refl") (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const ((anonymous |>.str "Eq") |>.str "refl") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1))) (.forallE (anonymous |>.str "b") (.bvar 3) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 4)) (.bvar 3)) (.bvar 0)) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) ⟨.default, none⟩) ⟨.implicit, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩)⟩ 2 1 1 1
    [⟨((anonymous |>.str "Eq") |>.str "refl"), 0, (.lam (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.lam (anonymous |>.str "a") (.bvar 0) (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "b") (.bvar 1) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, none⟩) ⟨.default, none⟩) (.lam (anonymous |>.str "refl") (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const ((anonymous |>.str "Eq") |>.str "refl") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1))) (.bvar 0) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩]]

/-- The pinned `Nat` basis block. -/
def natBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Nat"), [], (.sort (.succ .zero))⟩ {},
  .ctorInfo ⟨((anonymous |>.str "Nat") |>.str "zero"), [], (.const (anonymous |>.str "Nat") [])⟩ 0 0,
  .ctorInfo ⟨((anonymous |>.str "Nat") |>.str "succ"), [], (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.const (anonymous |>.str "Nat") []) ⟨.default, none⟩)⟩ 0 1,
  .recInfo ⟨((anonymous |>.str "Nat") |>.str "rec"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.forallE (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, none⟩) ⟨.default, none⟩) (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.app (.bvar 3) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩ 0 1 2 0
    [⟨((anonymous |>.str "Nat") |>.str "zero"), 0, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, none⟩) (.lam (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.lam (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, none⟩) ⟨.default, none⟩) (.bvar 1) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩)⟩,
      ⟨((anonymous |>.str "Nat") |>.str "succ"), 1, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, none⟩) (.lam (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.lam (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, none⟩) ⟨.default, none⟩) (.lam (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.app (.app (.bvar 1) (.bvar 0)) (.app (.app (.app (.app (.const ((anonymous |>.str "Nat") |>.str "rec") [(.param (anonymous |>.str "u"))]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩)⟩]]

/-- The pinned `PSigma'` basis block. -/
def psigmaBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "PSigma'"), [(anonymous |>.str "u"), (anonymous |>.str "v")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "β") (.forallE (anonymous |>.str "x") (.bvar 0) (.sort (.param (anonymous |>.str "v"))) ⟨.default, none⟩) (.sort (.max (.param (anonymous |>.str "u")) (.param (anonymous |>.str "v")))) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩ { eta := true },
  .ctorInfo ⟨((anonymous |>.str "PSigma'") |>.str "mk"), [(anonymous |>.str "u"), (anonymous |>.str "v")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "β") (.forallE (anonymous |>.str "x") (.bvar 0) (.sort (.param (anonymous |>.str "v"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "fst") (.bvar 1) (.forallE (anonymous |>.str "snd") (.app (.bvar 1) (.bvar 0)) (.app (.app (.const (anonymous |>.str "PSigma'") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 3)) (.bvar 2)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩)⟩ 2 2,
  .recInfo ⟨((anonymous |>.str "PSigma'") |>.str "rec"), [(anonymous |>.str "u"), (anonymous |>.str "v")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "β") (.forallE (anonymous |>.str "x") (.bvar 0) (.sort (.param (anonymous |>.str "v"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.app (.app (.const (anonymous |>.str "PSigma'") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 1)) (.bvar 0)) (.sort .zero) ⟨.default, none⟩) (.forallE (anonymous |>.str "mk") (.forallE (anonymous |>.str "fst") (.bvar 2) (.forallE (anonymous |>.str "snd") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 2) (.app (.app (.app (.app (.const ((anonymous |>.str "PSigma'") |>.str "mk") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))) ⟨.default, none⟩) ⟨.default, none⟩) (.forallE (anonymous |>.str "t") (.app (.app (.const (anonymous |>.str "PSigma'") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 3)) (.bvar 2)) (.app (.bvar 2) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩) ⟨.implicit, none⟩)⟩ 2 1 1 0
    [⟨((anonymous |>.str "PSigma'") |>.str "mk"), 2, (.lam (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.lam (anonymous |>.str "β") (.forallE (anonymous |>.str "x") (.bvar 0) (.sort (.param (anonymous |>.str "v"))) ⟨.default, none⟩) (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.app (.app (.const (anonymous |>.str "PSigma'") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 1)) (.bvar 0)) (.sort .zero) ⟨.default, none⟩) (.lam (anonymous |>.str "mk") (.forallE (anonymous |>.str "fst") (.bvar 2) (.forallE (anonymous |>.str "snd") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 2) (.app (.app (.app (.app (.const ((anonymous |>.str "PSigma'") |>.str "mk") [(.param (anonymous |>.str "u")), (.param (anonymous |>.str "v"))]) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))) ⟨.default, none⟩) ⟨.default, none⟩) (.lam (anonymous |>.str "fst") (.bvar 3) (.lam (anonymous |>.str "snd") (.app (.bvar 3) (.bvar 0)) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩]]

/-- The pinned `PUnit` basis block. -/
def punitBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "PUnit"), [(anonymous |>.str "u")], (.sort (.param (anonymous |>.str "u")))⟩ { unitlike := true },
  .ctorInfo ⟨((anonymous |>.str "PUnit") |>.str "unit"), [(anonymous |>.str "u")], (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))])⟩ 0 0,
  .recInfo ⟨((anonymous |>.str "PUnit") |>.str "rec"), [(anonymous |>.str "u_1"), (anonymous |>.str "u")], (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "unit") (.app (.bvar 0) (.const ((anonymous |>.str "PUnit") |>.str "unit") [(.param (anonymous |>.str "u"))])) (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.app (.bvar 2) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩) ⟨.implicit, none⟩)⟩ 0 1 1 0
    [⟨((anonymous |>.str "PUnit") |>.str "unit"), 0, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, none⟩) (.lam (anonymous |>.str "unit") (.app (.bvar 0) (.const ((anonymous |>.str "PUnit") |>.str "unit") [(.param (anonymous |>.str "u"))])) (.bvar 0) ⟨.default, none⟩) ⟨.default, none⟩)⟩]]

/-- The pinned `Empty` basis block (no constructors, no iota rules). -/
def emptyBasis : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Empty"), [], (.sort (.succ .zero))⟩ {},
  .recInfo ⟨((anonymous |>.str "Empty") |>.str "rec"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Empty") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, none⟩) (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Empty") []) (.app (.bvar 1) (.bvar 0)) ⟨.default, none⟩) ⟨.default, none⟩)⟩ 0 1 0 0 []]

/-- The constants of one basis block, in dependency order. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .psigmaK => psigmaBasis
  | .punitK => punitBasis
  | .emptyK => emptyBasis


/-! ## The annotated basis declarations

Generated by running the checker's own `annotate` over the pinned
blocks in install order (`AnnotateBasis.lean`); the installation stores
these verbatim, and the model proofs work against them.  Do not edit by
hand. -/

/-- Annotated basis declaration (generated). -/
def emptyA : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "Empty",
      levelParams := [],
      type := Setlec.Expr.sort (Setlec.Level.succ (Setlec.Level.zero)) }
    { eta := false, unitlike := false, ruleK := false }

/-- Annotated basis declaration (generated). -/
def emptyRecA : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Empty") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Empty") [])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.succ (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Empty") [])
                  (Setlec.Expr.app (Setlec.Expr.bvar 1) (Setlec.Expr.bvar 0))
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) })
                { bi := Setlec.BinderInfo.default,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.succ (Setlec.Level.zero))
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) } }
    0
    1
    0
    0
    []

/-- Annotated basis declaration (generated). -/
def eqA : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "Eq",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "a")
                  (Setlec.Expr.bvar 0)
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "b")
                    (Setlec.Expr.bvar 1)
                    (Setlec.Expr.sort (Setlec.Level.zero))
                    { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.succ (Setlec.Level.zero)) })
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.succ (Setlec.Level.zero))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                           (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.succ (Setlec.Level.zero)))) } }
    { eta := false, unitlike := false, ruleK := false }

/-- Annotated basis declaration (generated). -/
def eqReflA : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Eq") "refl",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "a")
                  (Setlec.Expr.bvar 0)
                  (Setlec.Expr.app
                    (Setlec.Expr.app
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                          [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                        (Setlec.Expr.bvar 1))
                      (Setlec.Expr.bvar 0))
                    (Setlec.Expr.bvar 0))
                  { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.zero) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                           (Setlec.Level.zero)) } }
    2
    0

/-- Annotated basis declaration (generated). -/
def eqRecA : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Eq") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u_1", Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "a")
                  (Setlec.Expr.bvar 0)
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "b")
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "t")
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.const
                                (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                                [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                              (Setlec.Expr.bvar 2))
                            (Setlec.Expr.bvar 1))
                          (Setlec.Expr.bvar 0))
                        (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))
                        { bi := Setlec.BinderInfo.default,
                          cod := some (Setlec.Level.succ
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))) })
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.imax
                                 (Setlec.Level.zero)
                                 (Setlec.Level.succ
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))) })
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "refl")
                      (Setlec.Expr.app
                        (Setlec.Expr.app (Setlec.Expr.bvar 0) (Setlec.Expr.bvar 1))
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.const
                              (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Eq") "refl")
                              [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                            (Setlec.Expr.bvar 2))
                          (Setlec.Expr.bvar 1)))
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "b")
                        (Setlec.Expr.bvar 3)
                        (Setlec.Expr.forallE
                          (Setlec.Name.str (Setlec.Name.anonymous) "t")
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.const
                                  (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                                  [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                                (Setlec.Expr.bvar 4))
                              (Setlec.Expr.bvar 3))
                            (Setlec.Expr.bvar 0))
                          (Setlec.Expr.app
                            (Setlec.Expr.app (Setlec.Expr.bvar 3) (Setlec.Expr.bvar 1))
                            (Setlec.Expr.bvar 0))
                          { bi := Setlec.BinderInfo.default,
                            cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")) })
                        { bi := Setlec.BinderInfo.implicit,
                          cod := some (Setlec.Level.imax
                                   (Setlec.Level.zero)
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))) })
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.zero)
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))) })
                    { bi := Setlec.BinderInfo.implicit,
                      cod := some (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.zero)
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))))) })
                  { bi := Setlec.BinderInfo.implicit,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                               (Setlec.Level.imax
                                 (Setlec.Level.zero)
                                 (Setlec.Level.succ
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))))
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.zero)
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                           (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                               (Setlec.Level.imax
                                 (Setlec.Level.zero)
                                 (Setlec.Level.succ
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))))
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.zero)
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))))))) } }
    2
    1
    1
    1
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Eq") "refl",
       nfields := 0,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.lam
                  (Setlec.Name.str (Setlec.Name.anonymous) "a")
                  (Setlec.Expr.bvar 0)
                  (Setlec.Expr.lam
                    (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "b")
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "t")
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.const
                                (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                                [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                              (Setlec.Expr.bvar 2))
                            (Setlec.Expr.bvar 1))
                          (Setlec.Expr.bvar 0))
                        (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))
                        { bi := Setlec.BinderInfo.default,
                          cod := some (Setlec.Level.succ
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))) })
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.imax
                                 (Setlec.Level.zero)
                                 (Setlec.Level.succ
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))) })
                    (Setlec.Expr.lam
                      (Setlec.Name.str (Setlec.Name.anonymous) "refl")
                      (Setlec.Expr.app
                        (Setlec.Expr.app (Setlec.Expr.bvar 0) (Setlec.Expr.bvar 1))
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.const
                              (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Eq") "refl")
                              [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                            (Setlec.Expr.bvar 2))
                          (Setlec.Expr.bvar 1)))
                      (Setlec.Expr.bvar 0)
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")) })
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))) })
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                               (Setlec.Level.imax
                                 (Setlec.Level.zero)
                                 (Setlec.Level.succ
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))))
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                           (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                               (Setlec.Level.imax
                                 (Setlec.Level.zero)
                                 (Setlec.Level.succ
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))))
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))))) } }]

/-- Annotated basis declaration (generated). -/
def natA : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "Nat",
      levelParams := [],
      type := Setlec.Expr.sort (Setlec.Level.succ (Setlec.Level.zero)) }
    { eta := false, unitlike := false, ruleK := false }

/-- Annotated basis declaration (generated). -/
def natZeroA : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "zero",
      levelParams := [],
      type := Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [] }
    0
    0

/-- Annotated basis declaration (generated). -/
def natSuccA : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "succ",
      levelParams := [],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "n")
                (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.succ (Setlec.Level.zero)) } }
    0
    1

/-- Annotated basis declaration (generated). -/
def natRecA : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.succ (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "zero")
                  (Setlec.Expr.app
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "zero") []))
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "succ")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "n")
                      (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "n_ih")
                        (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                        (Setlec.Expr.app
                          (Setlec.Expr.bvar 3)
                          (Setlec.Expr.app
                            (Setlec.Expr.const
                              (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "succ")
                              [])
                            (Setlec.Expr.bvar 1)))
                        { bi := Setlec.BinderInfo.default,
                          cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) })
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "t")
                      (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                      (Setlec.Expr.app (Setlec.Expr.bvar 3) (Setlec.Expr.bvar 0))
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) })
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))))
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                           (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))))
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))))) } }
    0
    1
    2
    0
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "zero",
       nfields := 0,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.succ (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                (Setlec.Expr.lam
                  (Setlec.Name.str (Setlec.Name.anonymous) "zero")
                  (Setlec.Expr.app
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "zero") []))
                  (Setlec.Expr.lam
                    (Setlec.Name.str (Setlec.Name.anonymous) "succ")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "n")
                      (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "n_ih")
                        (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                        (Setlec.Expr.app
                          (Setlec.Expr.bvar 3)
                          (Setlec.Expr.app
                            (Setlec.Expr.const
                              (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "succ")
                              [])
                            (Setlec.Expr.bvar 1)))
                        { bi := Setlec.BinderInfo.default,
                          cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) })
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                    (Setlec.Expr.bvar 1)
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) })
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))))
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                { bi := Setlec.BinderInfo.default,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                           (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))))
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))) } },
     { ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "succ",
       nfields := 1,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.succ (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                (Setlec.Expr.lam
                  (Setlec.Name.str (Setlec.Name.anonymous) "zero")
                  (Setlec.Expr.app
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "zero") []))
                  (Setlec.Expr.lam
                    (Setlec.Name.str (Setlec.Name.anonymous) "succ")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "n")
                      (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "n_ih")
                        (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                        (Setlec.Expr.app
                          (Setlec.Expr.bvar 3)
                          (Setlec.Expr.app
                            (Setlec.Expr.const
                              (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "succ")
                              [])
                            (Setlec.Expr.bvar 1)))
                        { bi := Setlec.BinderInfo.default,
                          cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) })
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                    (Setlec.Expr.lam
                      (Setlec.Name.str (Setlec.Name.anonymous) "n")
                      (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                      (Setlec.Expr.app
                        (Setlec.Expr.app (Setlec.Expr.bvar 1) (Setlec.Expr.bvar 0))
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.const
                                  (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "rec")
                                  [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                                (Setlec.Expr.bvar 3))
                              (Setlec.Expr.bvar 2))
                            (Setlec.Expr.bvar 1))
                          (Setlec.Expr.bvar 0)))
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) })
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))) })
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))))
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))) })
                { bi := Setlec.BinderInfo.default,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                           (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))))
                             (Setlec.Level.imax
                               (Setlec.Level.succ (Setlec.Level.zero))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))))) } }]

/-- Annotated basis declaration (generated). -/
def psigmaA : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "PSigma'",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u", Setlec.Name.str (Setlec.Name.anonymous) "v"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "β")
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "x")
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.succ
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))) })
                  (Setlec.Expr.sort
                    (Setlec.Level.max
                      (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                      (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))))
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.succ
                             (Setlec.Level.max
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.succ (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))))
                           (Setlec.Level.succ
                             (Setlec.Level.max
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))))) } }
    { eta := true, unitlike := false, ruleK := false }

/-- Annotated basis declaration (generated). -/
def psigmaMkA : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'") "mk",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u", Setlec.Name.str (Setlec.Name.anonymous) "v"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "β")
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "x")
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.succ
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))) })
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "fst")
                    (Setlec.Expr.bvar 1)
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "snd")
                      (Setlec.Expr.app (Setlec.Expr.bvar 1) (Setlec.Expr.bvar 0))
                      (Setlec.Expr.app
                        (Setlec.Expr.app
                          (Setlec.Expr.const
                            (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'")
                            [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"),
                             Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")])
                          (Setlec.Expr.bvar 3))
                        (Setlec.Expr.bvar 2))
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.max
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))) })
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                               (Setlec.Level.max
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))) })
                  { bi := Setlec.BinderInfo.implicit,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                               (Setlec.Level.max
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.succ (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))))
                           (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.imax
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                               (Setlec.Level.max
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))))) } }
    2
    2

/-- Annotated basis declaration (generated). -/
def psigmaRecA : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u", Setlec.Name.str (Setlec.Name.anonymous) "v"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "β")
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "x")
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.succ
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))) })
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "t")
                      (Setlec.Expr.app
                        (Setlec.Expr.app
                          (Setlec.Expr.const
                            (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'")
                            [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"),
                             Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")])
                          (Setlec.Expr.bvar 1))
                        (Setlec.Expr.bvar 0))
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.succ (Setlec.Level.zero)) })
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "mk")
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "fst")
                        (Setlec.Expr.bvar 2)
                        (Setlec.Expr.forallE
                          (Setlec.Name.str (Setlec.Name.anonymous) "snd")
                          (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                          (Setlec.Expr.app
                            (Setlec.Expr.bvar 2)
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.app
                                  (Setlec.Expr.app
                                    (Setlec.Expr.const
                                      (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'") "mk")
                                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"),
                                       Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")])
                                    (Setlec.Expr.bvar 4))
                                  (Setlec.Expr.bvar 3))
                                (Setlec.Expr.bvar 1))
                              (Setlec.Expr.bvar 0)))
                          { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.zero) })
                        { bi := Setlec.BinderInfo.default,
                          cod := some (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)) })
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "t")
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.const
                              (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'")
                              [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"),
                               Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")])
                            (Setlec.Expr.bvar 3))
                          (Setlec.Expr.bvar 2))
                        (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                        { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.zero) })
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.imax
                                 (Setlec.Level.max
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                                 (Setlec.Level.zero)) })
                    { bi := Setlec.BinderInfo.implicit,
                      cod := some (Setlec.Level.imax
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)))
                               (Setlec.Level.imax
                                 (Setlec.Level.max
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                                 (Setlec.Level.zero))) })
                  { bi := Setlec.BinderInfo.implicit,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.max
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                               (Setlec.Level.succ (Setlec.Level.zero)))
                             (Setlec.Level.imax
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)))
                               (Setlec.Level.imax
                                 (Setlec.Level.max
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                                 (Setlec.Level.zero)))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.succ (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))))
                           (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.max
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                               (Setlec.Level.succ (Setlec.Level.zero)))
                             (Setlec.Level.imax
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)))
                               (Setlec.Level.imax
                                 (Setlec.Level.max
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                                 (Setlec.Level.zero))))) } }
    2
    1
    1
    0
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'") "mk",
       nfields := 2,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.lam
                  (Setlec.Name.str (Setlec.Name.anonymous) "β")
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "x")
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.succ
                               (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))) })
                  (Setlec.Expr.lam
                    (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "t")
                      (Setlec.Expr.app
                        (Setlec.Expr.app
                          (Setlec.Expr.const
                            (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'")
                            [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"),
                             Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")])
                          (Setlec.Expr.bvar 1))
                        (Setlec.Expr.bvar 0))
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.succ (Setlec.Level.zero)) })
                    (Setlec.Expr.lam
                      (Setlec.Name.str (Setlec.Name.anonymous) "mk")
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "fst")
                        (Setlec.Expr.bvar 2)
                        (Setlec.Expr.forallE
                          (Setlec.Name.str (Setlec.Name.anonymous) "snd")
                          (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                          (Setlec.Expr.app
                            (Setlec.Expr.bvar 2)
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.app
                                  (Setlec.Expr.app
                                    (Setlec.Expr.const
                                      (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PSigma'") "mk")
                                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"),
                                       Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")])
                                    (Setlec.Expr.bvar 4))
                                  (Setlec.Expr.bvar 3))
                                (Setlec.Expr.bvar 1))
                              (Setlec.Expr.bvar 0)))
                          { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.zero) })
                        { bi := Setlec.BinderInfo.default,
                          cod := some (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)) })
                      (Setlec.Expr.lam
                        (Setlec.Name.str (Setlec.Name.anonymous) "fst")
                        (Setlec.Expr.bvar 3)
                        (Setlec.Expr.lam
                          (Setlec.Name.str (Setlec.Name.anonymous) "snd")
                          (Setlec.Expr.app (Setlec.Expr.bvar 3) (Setlec.Expr.bvar 0))
                          (Setlec.Expr.app
                            (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 1))
                            (Setlec.Expr.bvar 0))
                          { bi := Setlec.BinderInfo.default, cod := some (Setlec.Level.zero) })
                        { bi := Setlec.BinderInfo.default,
                          cod := some (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)) })
                      { bi := Setlec.BinderInfo.default,
                        cod := some (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero))) })
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.imax
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)))) })
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.max
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                               (Setlec.Level.succ (Setlec.Level.zero)))
                             (Setlec.Level.imax
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero))))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.succ (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))))
                           (Setlec.Level.imax
                             (Setlec.Level.imax
                               (Setlec.Level.max
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                               (Setlec.Level.succ (Setlec.Level.zero)))
                             (Setlec.Level.imax
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)))
                               (Setlec.Level.imax
                                 (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                                 (Setlec.Level.imax
                                   (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v"))
                                   (Setlec.Level.zero)))))) } }]

/-- Annotated basis declaration (generated). -/
def punitA : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "PUnit",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) }
    { eta := false, unitlike := true, ruleK := false }

/-- Annotated basis declaration (generated). -/
def punitUnitA : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "unit",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.const
                (Setlec.Name.str (Setlec.Name.anonymous) "PUnit")
                [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")] }
    0
    0

/-- Annotated basis declaration (generated). -/
def punitRecA : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u_1", Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const
                    (Setlec.Name.str (Setlec.Name.anonymous) "PUnit")
                    [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.succ
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))) })
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "unit")
                  (Setlec.Expr.app
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.const
                      (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "unit")
                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")]))
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "t")
                    (Setlec.Expr.const
                      (Setlec.Name.str (Setlec.Name.anonymous) "PUnit")
                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                    (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                    { bi := Setlec.BinderInfo.default,
                      cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")) })
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))) })
                { bi := Setlec.BinderInfo.implicit,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))
                           (Setlec.Level.imax
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u"))
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))) } }
    0
    1
    1
    0
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "unit",
       nfields := 0,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const
                    (Setlec.Name.str (Setlec.Name.anonymous) "PUnit")
                    [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.succ
                             (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))) })
                (Setlec.Expr.lam
                  (Setlec.Name.str (Setlec.Name.anonymous) "unit")
                  (Setlec.Expr.app
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.const
                      (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "unit")
                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")]))
                  (Setlec.Expr.bvar 0)
                  { bi := Setlec.BinderInfo.default,
                    cod := some (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")) })
                { bi := Setlec.BinderInfo.default,
                  cod := some (Setlec.Level.imax
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))
                           (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1"))) } }]

/-- The annotated constants of one basis block, in dependency order. -/
def BasisKind.declsA : BasisKind → List ConstantInfo
  | .eqK => [eqA, eqReflA, eqRecA]
  | .natK => [natA, natZeroA, natSuccA, natRecA]
  | .psigmaK => [psigmaA, psigmaMkA, psigmaRecA]
  | .punitK => [punitA, punitUnitA, punitRecA]
  | .emptyK => [emptyA, emptyRecA]

-- placeholder annotated Empty declarations; regenerated below


end Setlec
