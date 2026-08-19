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

/-- The name of the basis unit constructor. -/
def punitUnitName : Name := punitName |>.str "unit"

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


/-! ## The annotated basis declarations

Generated by running the checker's own `annotate` over the pinned
blocks in install order (`AnnotateBasis.lean`); the installation stores
these verbatim, and the model proofs work against them.  Do not edit by
hand. -/

/-- Annotated basis declaration (generated). -/
def eqA : ConstantInfo :=
  ConstantInfo.indInfo
  { name := Name.str (Name.anonymous) "Eq",
    levelParams := [Name.str (Name.anonymous) "u"],
    type := Expr.forallE
              (Name.str (Name.anonymous) "α")
              (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
              (Expr.forallE
                (Name.str (Name.anonymous) "a")
                (Expr.bvar 0)
                (Expr.forallE
                  (Name.str (Name.anonymous) "b")
                  (Expr.bvar 1)
                  (Expr.sort (Level.zero))
                  { bi := BinderInfo.default, cod := some (Level.succ (Level.zero)) })
                { bi := BinderInfo.default,
                  cod := some (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.succ (Level.zero))) })
              { bi := BinderInfo.implicit,
                cod := some (Level.imax
                         (Level.param (Name.str (Name.anonymous) "u"))
                         (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.succ (Level.zero)))) } }

/-- Annotated basis declaration (generated). -/
def eqReflA : ConstantInfo :=
  ConstantInfo.ctorInfo
  { name := Name.str (Name.str (Name.anonymous) "Eq") "refl",
    levelParams := [Name.str (Name.anonymous) "u"],
    type := Expr.forallE
              (Name.str (Name.anonymous) "α")
              (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
              (Expr.forallE
                (Name.str (Name.anonymous) "a")
                (Expr.bvar 0)
                (Expr.app
                  (Expr.app
                    (Expr.app
                      (Expr.const
                        (Name.str (Name.anonymous) "Eq")
                        [Level.param (Name.str (Name.anonymous) "u")])
                      (Expr.bvar 1))
                    (Expr.bvar 0))
                  (Expr.bvar 0))
                { bi := BinderInfo.default, cod := some (Level.zero) })
              { bi := BinderInfo.implicit,
                cod := some (Level.imax
                         (Level.param (Name.str (Name.anonymous) "u"))
                         (Level.zero)) } }
  2
  0

/-- Annotated basis declaration (generated). -/
def eqRecA : ConstantInfo :=
  ConstantInfo.recInfo
  { name := Name.str (Name.str (Name.anonymous) "Eq") "rec",
    levelParams := [Name.str (Name.anonymous) "u_1", Name.str (Name.anonymous) "u"],
    type := Expr.forallE
              (Name.str (Name.anonymous) "α")
              (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
              (Expr.forallE
                (Name.str (Name.anonymous) "a")
                (Expr.bvar 0)
                (Expr.forallE
                  (Name.str (Name.anonymous) "motive")
                  (Expr.forallE
                    (Name.str (Name.anonymous) "b")
                    (Expr.bvar 1)
                    (Expr.forallE
                      (Name.str (Name.anonymous) "t")
                      (Expr.app
                        (Expr.app
                          (Expr.app
                            (Expr.const
                              (Name.str (Name.anonymous) "Eq")
                              [Level.param (Name.str (Name.anonymous) "u")])
                            (Expr.bvar 2))
                          (Expr.bvar 1))
                        (Expr.bvar 0))
                      (Expr.sort (Level.param (Name.str (Name.anonymous) "u_1")))
                      { bi := BinderInfo.default,
                        cod := some (Level.succ
                                 (Level.param (Name.str (Name.anonymous) "u_1"))) })
                    { bi := BinderInfo.default,
                      cod := some (Level.imax
                               (Level.zero)
                               (Level.succ
                                 (Level.param (Name.str (Name.anonymous) "u_1")))) })
                  (Expr.forallE
                    (Name.str (Name.anonymous) "refl")
                    (Expr.app
                      (Expr.app (Expr.bvar 0) (Expr.bvar 1))
                      (Expr.app
                        (Expr.app
                          (Expr.const
                            (Name.str (Name.str (Name.anonymous) "Eq") "refl")
                            [Level.param (Name.str (Name.anonymous) "u")])
                          (Expr.bvar 2))
                        (Expr.bvar 1)))
                    (Expr.forallE
                      (Name.str (Name.anonymous) "b")
                      (Expr.bvar 3)
                      (Expr.forallE
                        (Name.str (Name.anonymous) "t")
                        (Expr.app
                          (Expr.app
                            (Expr.app
                              (Expr.const
                                (Name.str (Name.anonymous) "Eq")
                                [Level.param (Name.str (Name.anonymous) "u")])
                              (Expr.bvar 4))
                            (Expr.bvar 3))
                          (Expr.bvar 0))
                        (Expr.app
                          (Expr.app (Expr.bvar 3) (Expr.bvar 1))
                          (Expr.bvar 0))
                        { bi := BinderInfo.default,
                          cod := some (Level.param (Name.str (Name.anonymous) "u_1")) })
                      { bi := BinderInfo.implicit,
                        cod := some (Level.imax
                                 (Level.zero)
                                 (Level.param (Name.str (Name.anonymous) "u_1"))) })
                    { bi := BinderInfo.default,
                      cod := some (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.imax
                                 (Level.zero)
                                 (Level.param (Name.str (Name.anonymous) "u_1")))) })
                  { bi := BinderInfo.implicit,
                    cod := some (Level.imax
                             (Level.param (Name.str (Name.anonymous) "u_1"))
                             (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.imax
                                 (Level.zero)
                                 (Level.param (Name.str (Name.anonymous) "u_1"))))) })
                { bi := BinderInfo.implicit,
                  cod := some (Level.imax
                           (Level.imax
                             (Level.param (Name.str (Name.anonymous) "u"))
                             (Level.imax
                               (Level.zero)
                               (Level.succ
                                 (Level.param (Name.str (Name.anonymous) "u_1")))))
                           (Level.imax
                             (Level.param (Name.str (Name.anonymous) "u_1"))
                             (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.imax
                                 (Level.zero)
                                 (Level.param (Name.str (Name.anonymous) "u_1")))))) })
              { bi := BinderInfo.implicit,
                cod := some (Level.imax
                         (Level.param (Name.str (Name.anonymous) "u"))
                         (Level.imax
                           (Level.imax
                             (Level.param (Name.str (Name.anonymous) "u"))
                             (Level.imax
                               (Level.zero)
                               (Level.succ
                                 (Level.param (Name.str (Name.anonymous) "u_1")))))
                           (Level.imax
                             (Level.param (Name.str (Name.anonymous) "u_1"))
                             (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.imax
                                 (Level.zero)
                                 (Level.param (Name.str (Name.anonymous) "u_1"))))))) } }
  2
  1
  1
  1
  [{ ctor := Name.str (Name.str (Name.anonymous) "Eq") "refl",
     nfields := 0,
     rhs := Expr.lam
              (Name.str (Name.anonymous) "α")
              (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
              (Expr.lam
                (Name.str (Name.anonymous) "a")
                (Expr.bvar 0)
                (Expr.lam
                  (Name.str (Name.anonymous) "motive")
                  (Expr.forallE
                    (Name.str (Name.anonymous) "b")
                    (Expr.bvar 1)
                    (Expr.forallE
                      (Name.str (Name.anonymous) "t")
                      (Expr.app
                        (Expr.app
                          (Expr.app
                            (Expr.const
                              (Name.str (Name.anonymous) "Eq")
                              [Level.param (Name.str (Name.anonymous) "u")])
                            (Expr.bvar 2))
                          (Expr.bvar 1))
                        (Expr.bvar 0))
                      (Expr.sort (Level.param (Name.str (Name.anonymous) "u_1")))
                      { bi := BinderInfo.default, cod := none })
                    { bi := BinderInfo.default, cod := none })
                  (Expr.lam
                    (Name.str (Name.anonymous) "refl")
                    (Expr.app
                      (Expr.app (Expr.bvar 0) (Expr.bvar 1))
                      (Expr.app
                        (Expr.app
                          (Expr.const
                            (Name.str (Name.str (Name.anonymous) "Eq") "refl")
                            [Level.param (Name.str (Name.anonymous) "u")])
                          (Expr.bvar 2))
                        (Expr.bvar 1)))
                    (Expr.bvar 0)
                    { bi := BinderInfo.default, cod := none })
                  { bi := BinderInfo.default, cod := none })
                { bi := BinderInfo.default, cod := none })
              { bi := BinderInfo.implicit, cod := none } }]

/-- Annotated basis declaration (generated). -/
def natA : ConstantInfo :=
  ConstantInfo.indInfo
  { name := Name.str (Name.anonymous) "Nat",
    levelParams := [],
    type := Expr.sort (Level.succ (Level.zero)) }

/-- Annotated basis declaration (generated). -/
def natZeroA : ConstantInfo :=
  ConstantInfo.ctorInfo
  { name := Name.str (Name.str (Name.anonymous) "Nat") "zero",
    levelParams := [],
    type := Expr.const (Name.str (Name.anonymous) "Nat") [] }
  0
  0

/-- Annotated basis declaration (generated). -/
def natSuccA : ConstantInfo :=
  ConstantInfo.ctorInfo
  { name := Name.str (Name.str (Name.anonymous) "Nat") "succ",
    levelParams := [],
    type := Expr.forallE
              (Name.str (Name.anonymous) "n")
              (Expr.const (Name.str (Name.anonymous) "Nat") [])
              (Expr.const (Name.str (Name.anonymous) "Nat") [])
              { bi := BinderInfo.default, cod := some (Level.succ (Level.zero)) } }
  0
  1

/-- Annotated basis declaration (generated). -/
def natRecA : ConstantInfo :=
  ConstantInfo.recInfo
  { name := Name.str (Name.str (Name.anonymous) "Nat") "rec",
    levelParams := [Name.str (Name.anonymous) "u"],
    type := Expr.forallE
              (Name.str (Name.anonymous) "motive")
              (Expr.forallE
                (Name.str (Name.anonymous) "t")
                (Expr.const (Name.str (Name.anonymous) "Nat") [])
                (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
                { bi := BinderInfo.default,
                  cod := some (Level.succ (Level.param (Name.str (Name.anonymous) "u"))) })
              (Expr.forallE
                (Name.str (Name.anonymous) "zero")
                (Expr.app
                  (Expr.bvar 0)
                  (Expr.const (Name.str (Name.str (Name.anonymous) "Nat") "zero") []))
                (Expr.forallE
                  (Name.str (Name.anonymous) "succ")
                  (Expr.forallE
                    (Name.str (Name.anonymous) "n")
                    (Expr.const (Name.str (Name.anonymous) "Nat") [])
                    (Expr.forallE
                      (Name.str (Name.anonymous) "n_ih")
                      (Expr.app (Expr.bvar 2) (Expr.bvar 0))
                      (Expr.app
                        (Expr.bvar 3)
                        (Expr.app
                          (Expr.const
                            (Name.str (Name.str (Name.anonymous) "Nat") "succ")
                            [])
                          (Expr.bvar 1)))
                      { bi := BinderInfo.default,
                        cod := some (Level.param (Name.str (Name.anonymous) "u")) })
                    { bi := BinderInfo.default,
                      cod := some (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "u"))) })
                  (Expr.forallE
                    (Name.str (Name.anonymous) "t")
                    (Expr.const (Name.str (Name.anonymous) "Nat") [])
                    (Expr.app (Expr.bvar 3) (Expr.bvar 0))
                    { bi := BinderInfo.default,
                      cod := some (Level.param (Name.str (Name.anonymous) "u")) })
                  { bi := BinderInfo.default,
                    cod := some (Level.imax
                             (Level.succ (Level.zero))
                             (Level.param (Name.str (Name.anonymous) "u"))) })
                { bi := BinderInfo.default,
                  cod := some (Level.imax
                           (Level.imax
                             (Level.succ (Level.zero))
                             (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "u"))))
                           (Level.imax
                             (Level.succ (Level.zero))
                             (Level.param (Name.str (Name.anonymous) "u")))) })
              { bi := BinderInfo.implicit,
                cod := some (Level.imax
                         (Level.param (Name.str (Name.anonymous) "u"))
                         (Level.imax
                           (Level.imax
                             (Level.succ (Level.zero))
                             (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "u"))))
                           (Level.imax
                             (Level.succ (Level.zero))
                             (Level.param (Name.str (Name.anonymous) "u"))))) } }
  0
  1
  2
  0
  [{ ctor := Name.str (Name.str (Name.anonymous) "Nat") "zero",
     nfields := 0,
     rhs := Expr.lam
              (Name.str (Name.anonymous) "motive")
              (Expr.forallE
                (Name.str (Name.anonymous) "t")
                (Expr.const (Name.str (Name.anonymous) "Nat") [])
                (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
                { bi := BinderInfo.default, cod := none })
              (Expr.lam
                (Name.str (Name.anonymous) "zero")
                (Expr.app
                  (Expr.bvar 0)
                  (Expr.const (Name.str (Name.str (Name.anonymous) "Nat") "zero") []))
                (Expr.lam
                  (Name.str (Name.anonymous) "succ")
                  (Expr.forallE
                    (Name.str (Name.anonymous) "n")
                    (Expr.const (Name.str (Name.anonymous) "Nat") [])
                    (Expr.forallE
                      (Name.str (Name.anonymous) "n_ih")
                      (Expr.app (Expr.bvar 2) (Expr.bvar 0))
                      (Expr.app
                        (Expr.bvar 3)
                        (Expr.app
                          (Expr.const
                            (Name.str (Name.str (Name.anonymous) "Nat") "succ")
                            [])
                          (Expr.bvar 1)))
                      { bi := BinderInfo.default, cod := none })
                    { bi := BinderInfo.default, cod := none })
                  (Expr.bvar 1)
                  { bi := BinderInfo.default, cod := none })
                { bi := BinderInfo.default, cod := none })
              { bi := BinderInfo.default, cod := none } },
   { ctor := Name.str (Name.str (Name.anonymous) "Nat") "succ",
     nfields := 1,
     rhs := Expr.lam
              (Name.str (Name.anonymous) "motive")
              (Expr.forallE
                (Name.str (Name.anonymous) "t")
                (Expr.const (Name.str (Name.anonymous) "Nat") [])
                (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
                { bi := BinderInfo.default, cod := none })
              (Expr.lam
                (Name.str (Name.anonymous) "zero")
                (Expr.app
                  (Expr.bvar 0)
                  (Expr.const (Name.str (Name.str (Name.anonymous) "Nat") "zero") []))
                (Expr.lam
                  (Name.str (Name.anonymous) "succ")
                  (Expr.forallE
                    (Name.str (Name.anonymous) "n")
                    (Expr.const (Name.str (Name.anonymous) "Nat") [])
                    (Expr.forallE
                      (Name.str (Name.anonymous) "n_ih")
                      (Expr.app (Expr.bvar 2) (Expr.bvar 0))
                      (Expr.app
                        (Expr.bvar 3)
                        (Expr.app
                          (Expr.const
                            (Name.str (Name.str (Name.anonymous) "Nat") "succ")
                            [])
                          (Expr.bvar 1)))
                      { bi := BinderInfo.default, cod := none })
                    { bi := BinderInfo.default, cod := none })
                  (Expr.lam
                    (Name.str (Name.anonymous) "n")
                    (Expr.const (Name.str (Name.anonymous) "Nat") [])
                    (Expr.app
                      (Expr.app (Expr.bvar 1) (Expr.bvar 0))
                      (Expr.app
                        (Expr.app
                          (Expr.app
                            (Expr.app
                              (Expr.const
                                (Name.str (Name.str (Name.anonymous) "Nat") "rec")
                                [Level.param (Name.str (Name.anonymous) "u")])
                              (Expr.bvar 3))
                            (Expr.bvar 2))
                          (Expr.bvar 1))
                        (Expr.bvar 0)))
                    { bi := BinderInfo.default, cod := none })
                  { bi := BinderInfo.default, cod := none })
                { bi := BinderInfo.default, cod := none })
              { bi := BinderInfo.default, cod := none } }]

/-- Annotated basis declaration (generated). -/
def psigmaA : ConstantInfo :=
  ConstantInfo.indInfo
  { name := Name.str (Name.anonymous) "PSigma'",
    levelParams := [Name.str (Name.anonymous) "u", Name.str (Name.anonymous) "v"],
    type := Expr.forallE
              (Name.str (Name.anonymous) "α")
              (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
              (Expr.forallE
                (Name.str (Name.anonymous) "β")
                (Expr.forallE
                  (Name.str (Name.anonymous) "x")
                  (Expr.bvar 0)
                  (Expr.sort (Level.param (Name.str (Name.anonymous) "v")))
                  { bi := BinderInfo.default,
                    cod := some (Level.succ
                             (Level.param (Name.str (Name.anonymous) "v"))) })
                (Expr.sort
                  (Level.max
                    (Level.param (Name.str (Name.anonymous) "u"))
                    (Level.param (Name.str (Name.anonymous) "v"))))
                { bi := BinderInfo.default,
                  cod := some (Level.succ
                           (Level.max
                             (Level.param (Name.str (Name.anonymous) "u"))
                             (Level.param (Name.str (Name.anonymous) "v")))) })
              { bi := BinderInfo.implicit,
                cod := some (Level.imax
                         (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.succ (Level.param (Name.str (Name.anonymous) "v"))))
                         (Level.succ
                           (Level.max
                             (Level.param (Name.str (Name.anonymous) "u"))
                             (Level.param (Name.str (Name.anonymous) "v"))))) } }

/-- Annotated basis declaration (generated). -/
def psigmaMkA : ConstantInfo :=
  ConstantInfo.ctorInfo
  { name := Name.str (Name.str (Name.anonymous) "PSigma'") "mk",
    levelParams := [Name.str (Name.anonymous) "u", Name.str (Name.anonymous) "v"],
    type := Expr.forallE
              (Name.str (Name.anonymous) "α")
              (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
              (Expr.forallE
                (Name.str (Name.anonymous) "β")
                (Expr.forallE
                  (Name.str (Name.anonymous) "x")
                  (Expr.bvar 0)
                  (Expr.sort (Level.param (Name.str (Name.anonymous) "v")))
                  { bi := BinderInfo.default,
                    cod := some (Level.succ
                             (Level.param (Name.str (Name.anonymous) "v"))) })
                (Expr.forallE
                  (Name.str (Name.anonymous) "fst")
                  (Expr.bvar 1)
                  (Expr.forallE
                    (Name.str (Name.anonymous) "snd")
                    (Expr.app (Expr.bvar 1) (Expr.bvar 0))
                    (Expr.app
                      (Expr.app
                        (Expr.const
                          (Name.str (Name.anonymous) "PSigma'")
                          [Level.param (Name.str (Name.anonymous) "u"),
                           Level.param (Name.str (Name.anonymous) "v")])
                        (Expr.bvar 3))
                      (Expr.bvar 2))
                    { bi := BinderInfo.default,
                      cod := some (Level.max
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "v"))) })
                  { bi := BinderInfo.default,
                    cod := some (Level.imax
                             (Level.param (Name.str (Name.anonymous) "v"))
                             (Level.max
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "v")))) })
                { bi := BinderInfo.implicit,
                  cod := some (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.imax
                             (Level.param (Name.str (Name.anonymous) "v"))
                             (Level.max
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "v"))))) })
              { bi := BinderInfo.implicit,
                cod := some (Level.imax
                         (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.succ (Level.param (Name.str (Name.anonymous) "v"))))
                         (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.imax
                             (Level.param (Name.str (Name.anonymous) "v"))
                             (Level.max
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "v")))))) } }
  2
  2

/-- Annotated basis declaration (generated). -/
def psigmaRecA : ConstantInfo :=
  ConstantInfo.recInfo
  { name := Name.str (Name.str (Name.anonymous) "PSigma'") "rec",
    levelParams := [Name.str (Name.anonymous) "u", Name.str (Name.anonymous) "v"],
    type := Expr.forallE
              (Name.str (Name.anonymous) "α")
              (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
              (Expr.forallE
                (Name.str (Name.anonymous) "β")
                (Expr.forallE
                  (Name.str (Name.anonymous) "x")
                  (Expr.bvar 0)
                  (Expr.sort (Level.param (Name.str (Name.anonymous) "v")))
                  { bi := BinderInfo.default,
                    cod := some (Level.succ
                             (Level.param (Name.str (Name.anonymous) "v"))) })
                (Expr.forallE
                  (Name.str (Name.anonymous) "motive")
                  (Expr.forallE
                    (Name.str (Name.anonymous) "t")
                    (Expr.app
                      (Expr.app
                        (Expr.const
                          (Name.str (Name.anonymous) "PSigma'")
                          [Level.param (Name.str (Name.anonymous) "u"),
                           Level.param (Name.str (Name.anonymous) "v")])
                        (Expr.bvar 1))
                      (Expr.bvar 0))
                    (Expr.sort (Level.zero))
                    { bi := BinderInfo.default, cod := some (Level.succ (Level.zero)) })
                  (Expr.forallE
                    (Name.str (Name.anonymous) "mk")
                    (Expr.forallE
                      (Name.str (Name.anonymous) "fst")
                      (Expr.bvar 2)
                      (Expr.forallE
                        (Name.str (Name.anonymous) "snd")
                        (Expr.app (Expr.bvar 2) (Expr.bvar 0))
                        (Expr.app
                          (Expr.bvar 2)
                          (Expr.app
                            (Expr.app
                              (Expr.app
                                (Expr.app
                                  (Expr.const
                                    (Name.str (Name.str (Name.anonymous) "PSigma'") "mk")
                                    [Level.param (Name.str (Name.anonymous) "u"),
                                     Level.param (Name.str (Name.anonymous) "v")])
                                  (Expr.bvar 4))
                                (Expr.bvar 3))
                              (Expr.bvar 1))
                            (Expr.bvar 0)))
                        { bi := BinderInfo.default, cod := some (Level.zero) })
                      { bi := BinderInfo.default,
                        cod := some (Level.imax
                                 (Level.param (Name.str (Name.anonymous) "v"))
                                 (Level.zero)) })
                    (Expr.forallE
                      (Name.str (Name.anonymous) "t")
                      (Expr.app
                        (Expr.app
                          (Expr.const
                            (Name.str (Name.anonymous) "PSigma'")
                            [Level.param (Name.str (Name.anonymous) "u"),
                             Level.param (Name.str (Name.anonymous) "v")])
                          (Expr.bvar 3))
                        (Expr.bvar 2))
                      (Expr.app (Expr.bvar 2) (Expr.bvar 0))
                      { bi := BinderInfo.default, cod := some (Level.zero) })
                    { bi := BinderInfo.default,
                      cod := some (Level.imax
                               (Level.max
                                 (Level.param (Name.str (Name.anonymous) "u"))
                                 (Level.param (Name.str (Name.anonymous) "v")))
                               (Level.zero)) })
                  { bi := BinderInfo.implicit,
                    cod := some (Level.imax
                             (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.imax
                                 (Level.param (Name.str (Name.anonymous) "v"))
                                 (Level.zero)))
                             (Level.imax
                               (Level.max
                                 (Level.param (Name.str (Name.anonymous) "u"))
                                 (Level.param (Name.str (Name.anonymous) "v")))
                               (Level.zero))) })
                { bi := BinderInfo.implicit,
                  cod := some (Level.imax
                           (Level.imax
                             (Level.max
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "v")))
                             (Level.succ (Level.zero)))
                           (Level.imax
                             (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.imax
                                 (Level.param (Name.str (Name.anonymous) "v"))
                                 (Level.zero)))
                             (Level.imax
                               (Level.max
                                 (Level.param (Name.str (Name.anonymous) "u"))
                                 (Level.param (Name.str (Name.anonymous) "v")))
                               (Level.zero)))) })
              { bi := BinderInfo.implicit,
                cod := some (Level.imax
                         (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.succ (Level.param (Name.str (Name.anonymous) "v"))))
                         (Level.imax
                           (Level.imax
                             (Level.max
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.param (Name.str (Name.anonymous) "v")))
                             (Level.succ (Level.zero)))
                           (Level.imax
                             (Level.imax
                               (Level.param (Name.str (Name.anonymous) "u"))
                               (Level.imax
                                 (Level.param (Name.str (Name.anonymous) "v"))
                                 (Level.zero)))
                             (Level.imax
                               (Level.max
                                 (Level.param (Name.str (Name.anonymous) "u"))
                                 (Level.param (Name.str (Name.anonymous) "v")))
                               (Level.zero))))) } }
  2
  1
  1
  0
  [{ ctor := Name.str (Name.str (Name.anonymous) "PSigma'") "mk",
     nfields := 2,
     rhs := Expr.lam
              (Name.str (Name.anonymous) "α")
              (Expr.sort (Level.param (Name.str (Name.anonymous) "u")))
              (Expr.lam
                (Name.str (Name.anonymous) "β")
                (Expr.forallE
                  (Name.str (Name.anonymous) "x")
                  (Expr.bvar 0)
                  (Expr.sort (Level.param (Name.str (Name.anonymous) "v")))
                  { bi := BinderInfo.default, cod := none })
                (Expr.lam
                  (Name.str (Name.anonymous) "motive")
                  (Expr.forallE
                    (Name.str (Name.anonymous) "t")
                    (Expr.app
                      (Expr.app
                        (Expr.const
                          (Name.str (Name.anonymous) "PSigma'")
                          [Level.param (Name.str (Name.anonymous) "u"),
                           Level.param (Name.str (Name.anonymous) "v")])
                        (Expr.bvar 1))
                      (Expr.bvar 0))
                    (Expr.sort (Level.zero))
                    { bi := BinderInfo.default, cod := none })
                  (Expr.lam
                    (Name.str (Name.anonymous) "mk")
                    (Expr.forallE
                      (Name.str (Name.anonymous) "fst")
                      (Expr.bvar 2)
                      (Expr.forallE
                        (Name.str (Name.anonymous) "snd")
                        (Expr.app (Expr.bvar 2) (Expr.bvar 0))
                        (Expr.app
                          (Expr.bvar 2)
                          (Expr.app
                            (Expr.app
                              (Expr.app
                                (Expr.app
                                  (Expr.const
                                    (Name.str (Name.str (Name.anonymous) "PSigma'") "mk")
                                    [Level.param (Name.str (Name.anonymous) "u"),
                                     Level.param (Name.str (Name.anonymous) "v")])
                                  (Expr.bvar 4))
                                (Expr.bvar 3))
                              (Expr.bvar 1))
                            (Expr.bvar 0)))
                        { bi := BinderInfo.default, cod := none })
                      { bi := BinderInfo.default, cod := none })
                    (Expr.lam
                      (Name.str (Name.anonymous) "fst")
                      (Expr.bvar 3)
                      (Expr.lam
                        (Name.str (Name.anonymous) "snd")
                        (Expr.app (Expr.bvar 3) (Expr.bvar 0))
                        (Expr.app
                          (Expr.app (Expr.bvar 2) (Expr.bvar 1))
                          (Expr.bvar 0))
                        { bi := BinderInfo.default, cod := none })
                      { bi := BinderInfo.default, cod := none })
                    { bi := BinderInfo.default, cod := none })
                  { bi := BinderInfo.default, cod := none })
                { bi := BinderInfo.default, cod := none })
              { bi := BinderInfo.implicit, cod := none } }]

/-- Annotated basis declaration (generated). -/
def punitA : ConstantInfo :=
  ConstantInfo.indInfo
  { name := Name.str (Name.anonymous) "PUnit",
    levelParams := [Name.str (Name.anonymous) "u"],
    type := Expr.sort (Level.param (Name.str (Name.anonymous) "u")) }

/-- Annotated basis declaration (generated). -/
def punitUnitA : ConstantInfo :=
  ConstantInfo.ctorInfo
  { name := Name.str (Name.str (Name.anonymous) "PUnit") "unit",
    levelParams := [Name.str (Name.anonymous) "u"],
    type := Expr.const
              (Name.str (Name.anonymous) "PUnit")
              [Level.param (Name.str (Name.anonymous) "u")] }
  0
  0

/-- Annotated basis declaration (generated). -/
def punitRecA : ConstantInfo :=
  ConstantInfo.recInfo
  { name := Name.str (Name.str (Name.anonymous) "PUnit") "rec",
    levelParams := [Name.str (Name.anonymous) "u_1", Name.str (Name.anonymous) "u"],
    type := Expr.forallE
              (Name.str (Name.anonymous) "motive")
              (Expr.forallE
                (Name.str (Name.anonymous) "t")
                (Expr.const
                  (Name.str (Name.anonymous) "PUnit")
                  [Level.param (Name.str (Name.anonymous) "u")])
                (Expr.sort (Level.param (Name.str (Name.anonymous) "u_1")))
                { bi := BinderInfo.default,
                  cod := some (Level.succ
                           (Level.param (Name.str (Name.anonymous) "u_1"))) })
              (Expr.forallE
                (Name.str (Name.anonymous) "unit")
                (Expr.app
                  (Expr.bvar 0)
                  (Expr.const
                    (Name.str (Name.str (Name.anonymous) "PUnit") "unit")
                    [Level.param (Name.str (Name.anonymous) "u")]))
                (Expr.forallE
                  (Name.str (Name.anonymous) "t")
                  (Expr.const
                    (Name.str (Name.anonymous) "PUnit")
                    [Level.param (Name.str (Name.anonymous) "u")])
                  (Expr.app (Expr.bvar 2) (Expr.bvar 0))
                  { bi := BinderInfo.default,
                    cod := some (Level.param (Name.str (Name.anonymous) "u_1")) })
                { bi := BinderInfo.default,
                  cod := some (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.param (Name.str (Name.anonymous) "u_1"))) })
              { bi := BinderInfo.implicit,
                cod := some (Level.imax
                         (Level.param (Name.str (Name.anonymous) "u_1"))
                         (Level.imax
                           (Level.param (Name.str (Name.anonymous) "u"))
                           (Level.param (Name.str (Name.anonymous) "u_1")))) } }
  0
  1
  1
  0
  [{ ctor := Name.str (Name.str (Name.anonymous) "PUnit") "unit",
     nfields := 0,
     rhs := Expr.lam
              (Name.str (Name.anonymous) "motive")
              (Expr.forallE
                (Name.str (Name.anonymous) "t")
                (Expr.const
                  (Name.str (Name.anonymous) "PUnit")
                  [Level.param (Name.str (Name.anonymous) "u")])
                (Expr.sort (Level.param (Name.str (Name.anonymous) "u_1")))
                { bi := BinderInfo.default, cod := none })
              (Expr.lam
                (Name.str (Name.anonymous) "unit")
                (Expr.app
                  (Expr.bvar 0)
                  (Expr.const
                    (Name.str (Name.str (Name.anonymous) "PUnit") "unit")
                    [Level.param (Name.str (Name.anonymous) "u")]))
                (Expr.bvar 0)
                { bi := BinderInfo.default, cod := none })
              { bi := BinderInfo.default, cod := none } }]


/-- The annotated constants of one basis block, in dependency order. -/
def BasisKind.declsA : BasisKind → List ConstantInfo
  | .eqK => [eqA, eqReflA, eqRecA]
  | .natK => [natA, natZeroA, natSuccA, natRecA]
  | .psigmaK => [psigmaA, psigmaMkA, psigmaRecA]
  | .punitK => [punitA, punitUnitA, punitRecA]

end Setlec
