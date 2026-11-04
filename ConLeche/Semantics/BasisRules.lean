module

import ConLeche.Kernel.BasisA
public import ConLeche.Verify.EnvPreds

@[expose] public section

/-!
# The basis blocks' stored rules (task #161 S7)

`Nat.rec`'s two stored rules and the entry equation that names them.
They are pure `RecRule`/`Expr` syntax — no `V`, no `denote`.
-/

namespace ConLeche.Semantics

open ConLeche
/-- `Nat.rec`'s two stored rules. -/
def natRecZeroRule : RecRule :=
  { ctor := natZeroName, nfields := 0, fire := .plain,
    rhs := Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)))
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE (.app (.bvar 2)
              (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))))
          (.bvar 1))) }

def natRecSuccRule : RecRule :=
  { ctor := natSuccName, nfields := 1, fire := .plain,
    rhs := Expr.lam
      (Expr.forallE (.const natName [])
        (.sort (.param uN)))
      (Expr.lam
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam
          (Expr.forallE (.const natName [])
            (Expr.forallE (.app (.bvar 2)
              (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))))
          (Expr.lam (.const natName [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app (.const (natName.str "rec")
                [.param uN]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar
                  0)))))) }

theorem natRecA_eq :
    natRecA = .recInfo natRecA.toConstantVal 3 3
      false [natRecZeroRule, natRecSuccRule] := by
  show natRecA = _
  rfl

/-- `Quot.ind`'s single stored rule. -/
def quotIndRule : RecRule :=
  { ctor := quotMkName, nfields := 1, fire := .plain,
    rhs := Expr.lam (.sort (.param uN))
      (Expr.lam
        (Expr.forallE (.bvar 0)
          (Expr.forallE (.bvar 1) (.sort .zero)))
        (Expr.lam
          (Expr.forallE
            (.app (.app (.const quotName [.param uN]) (.bvar 1)) (.bvar
              0))
            (.sort .zero))
          (Expr.lam
            (Expr.forallE (.bvar 2)
              (.app (.bvar 1)
                (.app (.app (.app (.const quotMkName [.param uN])
                  (.bvar 3)) (.bvar 2)) (.bvar 0))))
            (Expr.lam (.bvar 3)
              (.app (.bvar 1) (.bvar 0)))))) }


/-- `Quot.lift`'s single stored rule. -/
def quotLiftRule : RecRule :=
  { ctor := quotMkName, nfields := 1, fire := .plain,
    rhs := Expr.lam (.sort (.param uN))
      (Expr.lam
        (Expr.forallE (.bvar 0)
          (Expr.forallE (.bvar 1) (.sort .zero)))
        (Expr.lam (.sort (.param vN))
          (Expr.lam
            (Expr.forallE (.bvar 2) (.bvar 1))
            (Expr.lam
              (Expr.forallE (.bvar 3)
                (Expr.forallE (.bvar 4)
                  (Expr.forallE
                    (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                    (.app (.app (.app (.const eqName [.param vN])
                      (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                      (.app (.bvar 3) (.bvar 1))))))
              (Expr.lam (.bvar 4)
                (.app (.bvar 2) (.bvar 0))))))) }


/-- `Eq.rec`'s single stored rule. -/
def eqRecRule : RecRule :=
  { ctor := eqReflName, nfields := 0, fire := .plain,
    rhs := Expr.lam (.sort (.param uN))
      (Expr.lam (.bvar 0)
        (Expr.lam
          (Expr.forallE (.bvar 1)
            (Expr.forallE
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 2))
                (.bvar 1)) (.bvar 0))
              (.sort (.param u1N))))
          (Expr.lam
            (.app (.app (.bvar 0) (.bvar 1))
              (.app (.app (.const eqReflName [.param uN]) (.bvar 2))
                (.bvar 1)))
            (.bvar 0)))) }


/-- The stored declaration, with its rule named. -/
theorem quotIndA_eq :
    quotIndA = .recInfo quotIndA.toConstantVal 4 4 false [quotIndRule] := by rfl


theorem quotLiftA_eq :
    quotLiftA = .recInfo quotLiftA.toConstantVal 5 5 false [quotLiftRule] := by
      rfl


/-- The stored declaration, with its rule named. -/
theorem eqRecA_eq :
    eqRecA = .recInfo eqRecA.toConstantVal 5 4 true [eqRecRule] := by rfl


end ConLeche.Semantics
