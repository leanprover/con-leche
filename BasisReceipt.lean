import Setlec.Kernel.TrustAxioms

/-!
# Byte-identity receipt for the basis literals (task: basis-literals)

TEMPORARY.  Holds the pre-change **generated** literals verbatim (as
they stood at master `bc53a72e`) beside the new hand-written raw pins
and the `#annotate_basis`-computed annotated forms, and checks with
`rfl` that every one of them is the same closed term.  Deleted once the
receipt has been taken (see DESIGN.md).
-/

namespace Setlec

open Name (anonymous)

namespace Receipt

def eqBasisOld : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Eq"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.forallE (anonymous |>.str "b") (.bvar 1) (.sort .zero) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.implicit, .never⟩)⟩ { ruleK := true },
  .ctorInfo ⟨((anonymous |>.str "Eq") |>.str "refl"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 1)) (.bvar 0)) (.bvar 0)) ⟨.default, .never⟩) ⟨.implicit, .never⟩)⟩ 2 0,
  .recInfo ⟨((anonymous |>.str "Eq") |>.str "rec"), [(anonymous |>.str "u_1"), (anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "a") (.bvar 0) (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "b") (.bvar 1) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, .never⟩) ⟨.default, .never⟩) (.forallE (anonymous |>.str "refl") (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const ((anonymous |>.str "Eq") |>.str "refl") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1))) (.forallE (anonymous |>.str "b") (.bvar 3) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 4)) (.bvar 3)) (.bvar 0)) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) ⟨.default, .never⟩) ⟨.implicit, .never⟩) ⟨.default, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩)⟩ 5 4
    [⟨((anonymous |>.str "Eq") |>.str "refl"), 0, 0, .inert, (.lam (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.lam (anonymous |>.str "a") (.bvar 0) (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "b") (.bvar 1) (.forallE (anonymous |>.str "t") (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, .never⟩) ⟨.default, .never⟩) (.lam (anonymous |>.str "refl") (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const ((anonymous |>.str "Eq") |>.str "refl") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1))) (.bvar 0) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.implicit, .never⟩)⟩]]

def eqAOld : ConstantInfo :=
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
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.never } }
    { eta := false,
      etaCtor := Setlec.Name.anonymous,
      etaParams := 0,
      etaFields := 0,
      unitlike := false,
      unitParams := 0,
      ruleK := true }

def eqReflAOld : ConstantInfo :=
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
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.ifAllZero [] } }
    2
    0

def eqRecAOld : ConstantInfo :=
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
                        { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
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
                            pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                        { bi := Setlec.BinderInfo.implicit,
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                      { bi := Setlec.BinderInfo.default,
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                    { bi := Setlec.BinderInfo.implicit,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                  { bi := Setlec.BinderInfo.implicit,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                { bi := Setlec.BinderInfo.implicit,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] } }
    5
    4
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Eq") "refl",
       nfields := 0,
       ctorParams := 2,
       fire := Setlec.RecRuleFire.plain,
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
                        { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
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
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                    { bi := Setlec.BinderInfo.default,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                { bi := Setlec.BinderInfo.implicit,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] } }]

def natBasisOld : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Nat"), [], (.sort (.succ .zero))⟩ {},
  .ctorInfo ⟨((anonymous |>.str "Nat") |>.str "zero"), [], (.const (anonymous |>.str "Nat") [])⟩ 0 0,
  .ctorInfo ⟨((anonymous |>.str "Nat") |>.str "succ"), [], (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.const (anonymous |>.str "Nat") []) ⟨.default, .never⟩)⟩ 0 1,
  .recInfo ⟨((anonymous |>.str "Nat") |>.str "rec"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, .never⟩) (.forallE (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.forallE (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, .never⟩) ⟨.default, .never⟩) (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.app (.bvar 3) (.bvar 0)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.implicit, .never⟩)⟩ 3 3
    [⟨((anonymous |>.str "Nat") |>.str "zero"), 0, 0, .inert, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, .never⟩) (.lam (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.lam (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, .never⟩) ⟨.default, .never⟩) (.bvar 1) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩,
      ⟨((anonymous |>.str "Nat") |>.str "succ"), 1, 0, .inert, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Nat") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, .never⟩) (.lam (anonymous |>.str "zero") (.app (.bvar 0) (.const ((anonymous |>.str "Nat") |>.str "zero") [])) (.lam (anonymous |>.str "succ") (.forallE (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.forallE (anonymous |>.str "n_ih") (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const ((anonymous |>.str "Nat") |>.str "succ") []) (.bvar 1))) ⟨.default, .never⟩) ⟨.default, .never⟩) (.lam (anonymous |>.str "n") (.const (anonymous |>.str "Nat") []) (.app (.app (.bvar 1) (.bvar 0)) (.app (.app (.app (.app (.const ((anonymous |>.str "Nat") |>.str "rec") [(.param (anonymous |>.str "u"))]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩]]

def natAOld : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "Nat",
      levelParams := [],
      type := Setlec.Expr.sort (Setlec.Level.succ (Setlec.Level.zero)) }
    { eta := false,
      etaCtor := Setlec.Name.anonymous,
      etaParams := 0,
      etaFields := 0,
      unitlike := false,
      unitParams := 0,
      ruleK := false }

def natZeroAOld : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "zero",
      levelParams := [],
      type := Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [] }
    0
    0

def natSuccAOld : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "succ",
      levelParams := [],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "n")
                (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never } }
    0
    1

def natRecAOld : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
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
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                      { bi := Setlec.BinderInfo.default,
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "t")
                      (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                      (Setlec.Expr.app (Setlec.Expr.bvar 3) (Setlec.Expr.bvar 0))
                      { bi := Setlec.BinderInfo.default,
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                    { bi := Setlec.BinderInfo.default,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                { bi := Setlec.BinderInfo.implicit,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] } }
    3
    3
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "zero",
       nfields := 0,
       ctorParams := 0,
       fire := Setlec.RecRuleFire.plain,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
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
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                      { bi := Setlec.BinderInfo.default,
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                    (Setlec.Expr.bvar 1)
                    { bi := Setlec.BinderInfo.default,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                { bi := Setlec.BinderInfo.default,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] } },
     { ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nat") "succ",
       nfields := 1,
       ctorParams := 0,
       fire := Setlec.RecRuleFire.plain,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
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
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                      { bi := Setlec.BinderInfo.default,
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
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
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                    { bi := Setlec.BinderInfo.default,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                { bi := Setlec.BinderInfo.default,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] } }]

def punitBasisOld : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "PUnit"), [(anonymous |>.str "u")], (.sort (.param (anonymous |>.str "u")))⟩
    { eta := true, etaCtor := ((anonymous |>.str "PUnit") |>.str "unit"),
      etaParams := 0, etaFields := 0, unitlike := true },
  .ctorInfo ⟨((anonymous |>.str "PUnit") |>.str "unit"), [(anonymous |>.str "u")], (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))])⟩ 0 0,
  .recInfo ⟨((anonymous |>.str "PUnit") |>.str "rec"), [(anonymous |>.str "u_1"), (anonymous |>.str "u")], (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, .never⟩) (.forallE (anonymous |>.str "unit") (.app (.bvar 0) (.const ((anonymous |>.str "PUnit") |>.str "unit") [(.param (anonymous |>.str "u"))])) (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.app (.bvar 2) (.bvar 0)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.implicit, .never⟩)⟩ 2 2
    [⟨((anonymous |>.str "PUnit") |>.str "unit"), 0, 0, .inert, (.lam (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "PUnit") [(.param (anonymous |>.str "u"))]) (.sort (.param (anonymous |>.str "u_1"))) ⟨.default, .never⟩) (.lam (anonymous |>.str "unit") (.app (.bvar 0) (.const ((anonymous |>.str "PUnit") |>.str "unit") [(.param (anonymous |>.str "u"))])) (.bvar 0) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩]]

def punitAOld : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "PUnit",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")) }
    { eta := true,
      etaCtor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "unit",
      etaParams := 0,
      etaFields := 0,
      unitlike := true,
      unitParams := 0,
      ruleK := false }

def punitUnitAOld : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "unit",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.const
                (Setlec.Name.str (Setlec.Name.anonymous) "PUnit")
                [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")] }
    0
    0

def punitRecAOld : ConstantInfo :=
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
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
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
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                { bi := Setlec.BinderInfo.implicit,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] } }
    2
    2
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "unit",
       nfields := 0,
       ctorParams := 0,
       fire := Setlec.RecRuleFire.plain,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const
                    (Setlec.Name.str (Setlec.Name.anonymous) "PUnit")
                    [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u_1")))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                (Setlec.Expr.lam
                  (Setlec.Name.str (Setlec.Name.anonymous) "unit")
                  (Setlec.Expr.app
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.const
                      (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "PUnit") "unit")
                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")]))
                  (Setlec.Expr.bvar 0)
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] })
                { bi := Setlec.BinderInfo.default,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u_1"] } }]

def emptyBasisOld : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Empty"), [], (.sort (.succ .zero))⟩ {},
  .recInfo ⟨((anonymous |>.str "Empty") |>.str "rec"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Empty") []) (.sort (.param (anonymous |>.str "u"))) ⟨.default, .never⟩) (.forallE (anonymous |>.str "t") (.const (anonymous |>.str "Empty") []) (.app (.bvar 1) (.bvar 0)) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩ 1 1 []]

def emptyAOld : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "Empty",
      levelParams := [],
      type := Setlec.Expr.sort (Setlec.Level.succ (Setlec.Level.zero)) }
    { eta := false,
      etaCtor := Setlec.Name.anonymous,
      etaParams := 0,
      etaFields := 0,
      unitlike := false,
      unitParams := 0,
      ruleK := false }

def emptyRecAOld : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Empty") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Empty") [])
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "t")
                  (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Empty") [])
                  (Setlec.Expr.app (Setlec.Expr.bvar 1) (Setlec.Expr.bvar 0))
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                { bi := Setlec.BinderInfo.default,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] } }
    1
    1
    []

def quotBasisOld : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Quot"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "r") (.forallE (anonymous) (.bvar 0) (.forallE (anonymous) (.bvar 1) (.sort (.zero)) ⟨.default, .never⟩) ⟨.default, .never⟩) (.sort (.param (anonymous |>.str "u"))) ⟨.default, .never⟩) ⟨.implicit, .never⟩)⟩ {},
  .ctorInfo ⟨((anonymous |>.str "Quot") |>.str "mk"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "r") (.forallE (anonymous) (.bvar 0) (.forallE (anonymous) (.bvar 1) (.sort (.zero)) ⟨.default, .never⟩) ⟨.default, .never⟩) (.forallE (anonymous |>.str "a") (.bvar 1) (.app (.app (.const (anonymous |>.str "Quot") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 1)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.implicit, .never⟩)⟩ 2 1,
  .recInfo ⟨((anonymous |>.str "Quot") |>.str "lift"), [(anonymous |>.str "u"), (anonymous |>.str "v")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "r") (.forallE (anonymous) (.bvar 0) (.forallE (anonymous) (.bvar 1) (.sort (.zero)) ⟨.default, .never⟩) ⟨.default, .never⟩) (.forallE (anonymous |>.str "β") (.sort (.param (anonymous |>.str "v"))) (.forallE (anonymous |>.str "f") (.forallE (anonymous |>.str "a") (.bvar 2) (.bvar 1) ⟨.default, .never⟩) (.forallE (anonymous |>.str "a") (.forallE (anonymous |>.str "a") (.bvar 3) (.forallE (anonymous |>.str "b") (.bvar 4) (.forallE (anonymous |>.str "a") (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "v"))]) (.bvar 4)) (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1))) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) (.forallE (anonymous |>.str "a") (.app (.app (.const (anonymous |>.str "Quot") [(.param (anonymous |>.str "u"))]) (.bvar 4)) (.bvar 3)) (.bvar 3) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩)⟩ 5 5
    [⟨((anonymous |>.str "Quot") |>.str "mk"), 1, 0, .inert, (.lam (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.lam (anonymous |>.str "r") (.forallE (anonymous) (.bvar 0) (.forallE (anonymous) (.bvar 1) (.sort (.zero)) ⟨.default, .never⟩) ⟨.default, .never⟩) (.lam (anonymous |>.str "β") (.sort (.param (anonymous |>.str "v"))) (.lam (anonymous |>.str "f") (.forallE (anonymous |>.str "a") (.bvar 2) (.bvar 1) ⟨.default, .never⟩) (.lam (anonymous |>.str "h") (.forallE (anonymous |>.str "a") (.bvar 3) (.forallE (anonymous |>.str "b") (.bvar 4) (.forallE (anonymous |>.str "a") (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "v"))]) (.bvar 4)) (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1))) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) (.lam (anonymous |>.str "a") (.bvar 4) (.app (.bvar 2) (.bvar 0)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩],
  .recInfo ⟨((anonymous |>.str "Quot") |>.str "ind"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "r") (.forallE (anonymous) (.bvar 0) (.forallE (anonymous) (.bvar 1) (.sort (.zero)) ⟨.default, .never⟩) ⟨.default, .never⟩) (.forallE (anonymous |>.str "β") (.forallE (anonymous |>.str "a") (.app (.app (.const (anonymous |>.str "Quot") [(.param (anonymous |>.str "u"))]) (.bvar 1)) (.bvar 0)) (.sort (.zero)) ⟨.default, .never⟩) (.forallE (anonymous |>.str "mk") (.forallE (anonymous |>.str "a") (.bvar 2) (.app (.bvar 1) (.app (.app (.app (.const ((anonymous |>.str "Quot") |>.str "mk") [(.param (anonymous |>.str "u"))]) (.bvar 3)) (.bvar 2)) (.bvar 0))) ⟨.default, .never⟩) (.forallE (anonymous |>.str "q") (.app (.app (.const (anonymous |>.str "Quot") [(.param (anonymous |>.str "u"))]) (.bvar 3)) (.bvar 2)) (.app (.bvar 2) (.bvar 0)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩)⟩ 4 4
    [⟨((anonymous |>.str "Quot") |>.str "mk"), 1, 0, .inert, (.lam (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.lam (anonymous |>.str "r") (.forallE (anonymous) (.bvar 0) (.forallE (anonymous) (.bvar 1) (.sort (.zero)) ⟨.default, .never⟩) ⟨.default, .never⟩) (.lam (anonymous |>.str "β") (.forallE (anonymous |>.str "a") (.app (.app (.const (anonymous |>.str "Quot") [(.param (anonymous |>.str "u"))]) (.bvar 1)) (.bvar 0)) (.sort (.zero)) ⟨.default, .never⟩) (.lam (anonymous |>.str "mk") (.forallE (anonymous |>.str "a") (.bvar 2) (.app (.bvar 1) (.app (.app (.app (.const ((anonymous |>.str "Quot") |>.str "mk") [(.param (anonymous |>.str "u"))]) (.bvar 3)) (.bvar 2)) (.bvar 0))) ⟨.default, .never⟩) (.lam (anonymous |>.str "a") (.bvar 3) (.app (.bvar 1) (.bvar 0)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩],
  .axiomInfo ⟨((anonymous |>.str "Quot") |>.str "sound"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "r") (.forallE (anonymous) (.bvar 0) (.forallE (anonymous) (.bvar 1) (.sort (.zero)) ⟨.default, .never⟩) ⟨.default, .never⟩) (.forallE (anonymous |>.str "a") (.bvar 1) (.forallE (anonymous |>.str "b") (.bvar 2) (.forallE (anonymous) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.const (anonymous |>.str "Eq") [(.param (anonymous |>.str "u"))]) (.app (.app (.const (anonymous |>.str "Quot") [(.param (anonymous |>.str "u"))]) (.bvar 4)) (.bvar 3))) (.app (.app (.app (.const ((anonymous |>.str "Quot") |>.str "mk") [(.param (anonymous |>.str "u"))]) (.bvar 4)) (.bvar 3)) (.bvar 2))) (.app (.app (.app (.const ((anonymous |>.str "Quot") |>.str "mk") [(.param (anonymous |>.str "u"))]) (.bvar 4)) (.bvar 3)) (.bvar 1))) ⟨.default, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩) ⟨.implicit, .never⟩)⟩]

def quotAOld : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "Quot",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "r")
                  (Setlec.Expr.forallE
                    (Setlec.Name.anonymous)
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.forallE
                      (Setlec.Name.anonymous)
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.never } }
    { eta := false,
      etaCtor := Setlec.Name.anonymous,
      etaParams := 0,
      etaFields := 0,
      unitlike := false,
      unitParams := 0,
      ruleK := false }

def quotMkAOld : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "mk",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "r")
                  (Setlec.Expr.forallE
                    (Setlec.Name.anonymous)
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.forallE
                      (Setlec.Name.anonymous)
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "a")
                    (Setlec.Expr.bvar 1)
                    (Setlec.Expr.app
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.anonymous) "Quot")
                          [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                        (Setlec.Expr.bvar 2))
                      (Setlec.Expr.bvar 1))
                    { bi := Setlec.BinderInfo.default,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                { bi := Setlec.BinderInfo.implicit,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] } }
    2
    1

def quotLiftAOld : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "lift",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u", Setlec.Name.str (Setlec.Name.anonymous) "v"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "r")
                  (Setlec.Expr.forallE
                    (Setlec.Name.anonymous)
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.forallE
                      (Setlec.Name.anonymous)
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "β")
                    (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "f")
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "a")
                        (Setlec.Expr.bvar 2)
                        (Setlec.Expr.bvar 1)
                        { bi := Setlec.BinderInfo.default,
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "a")
                        (Setlec.Expr.forallE
                          (Setlec.Name.str (Setlec.Name.anonymous) "a")
                          (Setlec.Expr.bvar 3)
                          (Setlec.Expr.forallE
                            (Setlec.Name.str (Setlec.Name.anonymous) "b")
                            (Setlec.Expr.bvar 4)
                            (Setlec.Expr.forallE
                              (Setlec.Name.str (Setlec.Name.anonymous) "a")
                              (Setlec.Expr.app
                                (Setlec.Expr.app (Setlec.Expr.bvar 4) (Setlec.Expr.bvar 1))
                                (Setlec.Expr.bvar 0))
                              (Setlec.Expr.app
                                (Setlec.Expr.app
                                  (Setlec.Expr.app
                                    (Setlec.Expr.const
                                      (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")])
                                    (Setlec.Expr.bvar 4))
                                  (Setlec.Expr.app (Setlec.Expr.bvar 3) (Setlec.Expr.bvar 2)))
                                (Setlec.Expr.app (Setlec.Expr.bvar 3) (Setlec.Expr.bvar 1)))
                              { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                            { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                          { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                        (Setlec.Expr.forallE
                          (Setlec.Name.str (Setlec.Name.anonymous) "a")
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.const
                                (Setlec.Name.str (Setlec.Name.anonymous) "Quot")
                                [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                              (Setlec.Expr.bvar 4))
                            (Setlec.Expr.bvar 3))
                          (Setlec.Expr.bvar 3)
                          { bi := Setlec.BinderInfo.default,
                            pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                        { bi := Setlec.BinderInfo.default,
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                      { bi := Setlec.BinderInfo.default,
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                    { bi := Setlec.BinderInfo.implicit,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                  { bi := Setlec.BinderInfo.implicit,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                { bi := Setlec.BinderInfo.implicit,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] } }
    5
    5
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "mk",
       nfields := 1,
       ctorParams := 2,
       fire := Setlec.RecRuleFire.plain,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.lam
                  (Setlec.Name.str (Setlec.Name.anonymous) "r")
                  (Setlec.Expr.forallE
                    (Setlec.Name.anonymous)
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.forallE
                      (Setlec.Name.anonymous)
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  (Setlec.Expr.lam
                    (Setlec.Name.str (Setlec.Name.anonymous) "β")
                    (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")))
                    (Setlec.Expr.lam
                      (Setlec.Name.str (Setlec.Name.anonymous) "f")
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "a")
                        (Setlec.Expr.bvar 2)
                        (Setlec.Expr.bvar 1)
                        { bi := Setlec.BinderInfo.default,
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                      (Setlec.Expr.lam
                        (Setlec.Name.str (Setlec.Name.anonymous) "h")
                        (Setlec.Expr.forallE
                          (Setlec.Name.str (Setlec.Name.anonymous) "a")
                          (Setlec.Expr.bvar 3)
                          (Setlec.Expr.forallE
                            (Setlec.Name.str (Setlec.Name.anonymous) "b")
                            (Setlec.Expr.bvar 4)
                            (Setlec.Expr.forallE
                              (Setlec.Name.str (Setlec.Name.anonymous) "a")
                              (Setlec.Expr.app
                                (Setlec.Expr.app (Setlec.Expr.bvar 4) (Setlec.Expr.bvar 1))
                                (Setlec.Expr.bvar 0))
                              (Setlec.Expr.app
                                (Setlec.Expr.app
                                  (Setlec.Expr.app
                                    (Setlec.Expr.const
                                      (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "v")])
                                    (Setlec.Expr.bvar 4))
                                  (Setlec.Expr.app (Setlec.Expr.bvar 3) (Setlec.Expr.bvar 2)))
                                (Setlec.Expr.app (Setlec.Expr.bvar 3) (Setlec.Expr.bvar 1)))
                              { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                            { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                          { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                        (Setlec.Expr.lam
                          (Setlec.Name.str (Setlec.Name.anonymous) "a")
                          (Setlec.Expr.bvar 4)
                          (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                          { bi := Setlec.BinderInfo.default,
                            pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                        { bi := Setlec.BinderInfo.default,
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                      { bi := Setlec.BinderInfo.default,
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                    { bi := Setlec.BinderInfo.default,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] })
                { bi := Setlec.BinderInfo.default,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "v"] } }]

def quotIndAOld : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "ind",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "r")
                  (Setlec.Expr.forallE
                    (Setlec.Name.anonymous)
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.forallE
                      (Setlec.Name.anonymous)
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "β")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "a")
                      (Setlec.Expr.app
                        (Setlec.Expr.app
                          (Setlec.Expr.const
                            (Setlec.Name.str (Setlec.Name.anonymous) "Quot")
                            [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                          (Setlec.Expr.bvar 1))
                        (Setlec.Expr.bvar 0))
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "mk")
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "a")
                        (Setlec.Expr.bvar 2)
                        (Setlec.Expr.app
                          (Setlec.Expr.bvar 1)
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.const
                                  (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "mk")
                                  [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                                (Setlec.Expr.bvar 3))
                              (Setlec.Expr.bvar 2))
                            (Setlec.Expr.bvar 0)))
                        { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "q")
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.const
                              (Setlec.Name.str (Setlec.Name.anonymous) "Quot")
                              [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                            (Setlec.Expr.bvar 3))
                          (Setlec.Expr.bvar 2))
                        (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                        { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                    { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.ifAllZero [] })
                  { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.ifAllZero [] } }
    4
    4
    [{ ctor := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "mk",
       nfields := 1,
       ctorParams := 2,
       fire := Setlec.RecRuleFire.plain,
       rhs := Setlec.Expr.lam
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.lam
                  (Setlec.Name.str (Setlec.Name.anonymous) "r")
                  (Setlec.Expr.forallE
                    (Setlec.Name.anonymous)
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.forallE
                      (Setlec.Name.anonymous)
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  (Setlec.Expr.lam
                    (Setlec.Name.str (Setlec.Name.anonymous) "β")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "a")
                      (Setlec.Expr.app
                        (Setlec.Expr.app
                          (Setlec.Expr.const
                            (Setlec.Name.str (Setlec.Name.anonymous) "Quot")
                            [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                          (Setlec.Expr.bvar 1))
                        (Setlec.Expr.bvar 0))
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    (Setlec.Expr.lam
                      (Setlec.Name.str (Setlec.Name.anonymous) "mk")
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "a")
                        (Setlec.Expr.bvar 2)
                        (Setlec.Expr.app
                          (Setlec.Expr.bvar 1)
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.const
                                  (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "mk")
                                  [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                                (Setlec.Expr.bvar 3))
                              (Setlec.Expr.bvar 2))
                            (Setlec.Expr.bvar 0)))
                        { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                      (Setlec.Expr.lam
                        (Setlec.Name.str (Setlec.Name.anonymous) "a")
                        (Setlec.Expr.bvar 3)
                        (Setlec.Expr.app (Setlec.Expr.bvar 1) (Setlec.Expr.bvar 0))
                        { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] } }]

def quotSoundAOld : ConstantInfo :=
  Setlec.ConstantInfo.axiomInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "sound",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "r")
                  (Setlec.Expr.forallE
                    (Setlec.Name.anonymous)
                    (Setlec.Expr.bvar 0)
                    (Setlec.Expr.forallE
                      (Setlec.Name.anonymous)
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.sort (Setlec.Level.zero))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "a")
                    (Setlec.Expr.bvar 1)
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "b")
                      (Setlec.Expr.bvar 2)
                      (Setlec.Expr.forallE
                        (Setlec.Name.anonymous)
                        (Setlec.Expr.app (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 1)) (Setlec.Expr.bvar 0))
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.const
                                (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                                [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                              (Setlec.Expr.app
                                (Setlec.Expr.app
                                  (Setlec.Expr.const
                                    (Setlec.Name.str (Setlec.Name.anonymous) "Quot")
                                    [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                                  (Setlec.Expr.bvar 4))
                                (Setlec.Expr.bvar 3)))
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.app
                                  (Setlec.Expr.const
                                    (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "mk")
                                    [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                                  (Setlec.Expr.bvar 4))
                                (Setlec.Expr.bvar 3))
                              (Setlec.Expr.bvar 2)))
                          (Setlec.Expr.app
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.const
                                  (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Quot") "mk")
                                  [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                                (Setlec.Expr.bvar 4))
                              (Setlec.Expr.bvar 3))
                            (Setlec.Expr.bvar 1)))
                        { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                      { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.ifAllZero [] })
                    { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.ifAllZero [] })
                  { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.implicit, pw := Setlec.PropWhen.ifAllZero [] } }

def iffFamilyOld : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Iff"), [], (.forallE (anonymous |>.str "a") (.sort (.zero)) (.forallE (anonymous |>.str "b") (.sort (.zero)) (.sort (.zero)) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩ {},
  .ctorInfo ⟨((anonymous |>.str "Iff") |>.str "intro"), [], (.forallE (anonymous |>.str "a") (.sort (.zero)) (.forallE (anonymous |>.str "b") (.sort (.zero)) (.forallE (anonymous |>.str "mp") (.forallE (anonymous) (.bvar 1) (.bvar 1) ⟨.default, .never⟩) (.forallE (anonymous |>.str "mpr") (.forallE (anonymous) (.bvar 1) (.bvar 3) ⟨.default, .never⟩) (.app (.app (.const (anonymous |>.str "Iff") []) (.bvar 3)) (.bvar 2)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩ 2 2,
  .recInfo ⟨((anonymous |>.str "Iff") |>.str "rec"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "a") (.sort (.zero)) (.forallE (anonymous |>.str "b") (.sort (.zero)) (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.app (.app (.const (anonymous |>.str "Iff") []) (.bvar 1)) (.bvar 0)) (.sort (.param (anonymous |>.str "u"))) ⟨.default, .never⟩) (.forallE (anonymous |>.str "intro") (.forallE (anonymous |>.str "mp") (.forallE (anonymous |>.str "right") (.bvar 2) (.bvar 2) ⟨.default, .never⟩) (.forallE (anonymous |>.str "mpr") (.forallE (anonymous) (.bvar 2) (.bvar 4) ⟨.default, .never⟩) (.app (.bvar 2) (.app (.app (.app (.app (.const ((anonymous |>.str "Iff") |>.str "intro") []) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))) ⟨.default, .never⟩) ⟨.default, .never⟩) (.forallE (anonymous |>.str "t") (.app (.app (.const (anonymous |>.str "Iff") []) (.bvar 3)) (.bvar 2)) (.app (.bvar 2) (.bvar 0)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩ 4 4 []]

def propextRawOld : ConstantVal := ⟨(anonymous |>.str "propext"), [], (.forallE (anonymous |>.str "a") (.sort (.zero)) (.forallE (anonymous |>.str "b") (.sort (.zero)) (.forallE (anonymous) (.app (.app (.const (anonymous |>.str "Iff") []) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.const (anonymous |>.str "Eq") [(.succ (.zero))]) (.sort (.zero))) (.bvar 2)) (.bvar 1)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩

def nonemptyFamilyOld : List ConstantInfo := [
  .indInfo ⟨(anonymous |>.str "Nonempty"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.sort (.zero)) ⟨.default, .never⟩)⟩ {},
  .ctorInfo ⟨((anonymous |>.str "Nonempty") |>.str "intro"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "val") (.bvar 0) (.app (.const (anonymous |>.str "Nonempty") [(.param (anonymous |>.str "u"))]) (.bvar 1)) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩ 1 1,
  .recInfo ⟨((anonymous |>.str "Nonempty") |>.str "rec"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous |>.str "motive") (.forallE (anonymous |>.str "t") (.app (.const (anonymous |>.str "Nonempty") [(.param (anonymous |>.str "u"))]) (.bvar 0)) (.sort (.zero)) ⟨.default, .never⟩) (.forallE (anonymous |>.str "intro") (.forallE (anonymous |>.str "val") (.bvar 1) (.app (.bvar 1) (.app (.app (.const ((anonymous |>.str "Nonempty") |>.str "intro") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.bvar 0))) ⟨.default, .never⟩) (.forallE (anonymous |>.str "t") (.app (.const (anonymous |>.str "Nonempty") [(.param (anonymous |>.str "u"))]) (.bvar 2)) (.app (.bvar 2) (.bvar 0)) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩ 3 3 []]

def choiceRawOld : ConstantVal := ⟨((anonymous |>.str "Classical") |>.str "choice"), [(anonymous |>.str "u")], (.forallE (anonymous |>.str "α") (.sort (.param (anonymous |>.str "u"))) (.forallE (anonymous) (.app (.const (anonymous |>.str "Nonempty") [(.param (anonymous |>.str "u"))]) (.bvar 0)) (.bvar 1) ⟨.default, .never⟩) ⟨.default, .never⟩)⟩

def iffAOld : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "Iff",
      levelParams := [],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "a")
                (Setlec.Expr.sort (Setlec.Level.zero))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "b")
                  (Setlec.Expr.sort (Setlec.Level.zero))
                  (Setlec.Expr.sort (Setlec.Level.zero))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never } }
    { eta := false,
      etaCtor := Setlec.Name.anonymous,
      etaParams := 0,
      etaFields := 0,
      unitlike := false,
      unitParams := 0,
      ruleK := false }

def iffIntroAOld : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Iff") "intro",
      levelParams := [],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "a")
                (Setlec.Expr.sort (Setlec.Level.zero))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "b")
                  (Setlec.Expr.sort (Setlec.Level.zero))
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "mp")
                    (Setlec.Expr.forallE
                      (Setlec.Name.anonymous)
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.bvar 1)
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "mpr")
                      (Setlec.Expr.forallE
                        (Setlec.Name.anonymous)
                        (Setlec.Expr.bvar 1)
                        (Setlec.Expr.bvar 3)
                        { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                      (Setlec.Expr.app
                        (Setlec.Expr.app
                          (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Iff") [])
                          (Setlec.Expr.bvar 3))
                        (Setlec.Expr.bvar 2))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] } }
    2
    2

def iffRecAOld : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Iff") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "a")
                (Setlec.Expr.sort (Setlec.Level.zero))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "b")
                  (Setlec.Expr.sort (Setlec.Level.zero))
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "t")
                      (Setlec.Expr.app
                        (Setlec.Expr.app
                          (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Iff") [])
                          (Setlec.Expr.bvar 1))
                        (Setlec.Expr.bvar 0))
                      (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "intro")
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "mp")
                        (Setlec.Expr.forallE
                          (Setlec.Name.str (Setlec.Name.anonymous) "right")
                          (Setlec.Expr.bvar 2)
                          (Setlec.Expr.bvar 2)
                          { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                        (Setlec.Expr.forallE
                          (Setlec.Name.str (Setlec.Name.anonymous) "mpr")
                          (Setlec.Expr.forallE
                            (Setlec.Name.anonymous)
                            (Setlec.Expr.bvar 2)
                            (Setlec.Expr.bvar 4)
                            { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                          (Setlec.Expr.app
                            (Setlec.Expr.bvar 2)
                            (Setlec.Expr.app
                              (Setlec.Expr.app
                                (Setlec.Expr.app
                                  (Setlec.Expr.app
                                    (Setlec.Expr.const
                                      (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Iff") "intro")
                                      [])
                                    (Setlec.Expr.bvar 4))
                                  (Setlec.Expr.bvar 3))
                                (Setlec.Expr.bvar 1))
                              (Setlec.Expr.bvar 0)))
                          { bi := Setlec.BinderInfo.default,
                            pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                        { bi := Setlec.BinderInfo.default,
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                      (Setlec.Expr.forallE
                        (Setlec.Name.str (Setlec.Name.anonymous) "t")
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Iff") [])
                            (Setlec.Expr.bvar 3))
                          (Setlec.Expr.bvar 2))
                        (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                        { bi := Setlec.BinderInfo.default,
                          pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                      { bi := Setlec.BinderInfo.default,
                        pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                    { bi := Setlec.BinderInfo.default,
                      pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                  { bi := Setlec.BinderInfo.default,
                    pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
                { bi := Setlec.BinderInfo.default,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] } }
    4
    4
    []

def nonemptyAOld : ConstantInfo :=
  Setlec.ConstantInfo.indInfo
    { name := Setlec.Name.str (Setlec.Name.anonymous) "Nonempty",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.sort (Setlec.Level.zero))
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never } }
    { eta := false,
      etaCtor := Setlec.Name.anonymous,
      etaParams := 0,
      etaFields := 0,
      unitlike := false,
      unitParams := 0,
      ruleK := false }

def nonemptyIntroAOld : ConstantInfo :=
  Setlec.ConstantInfo.ctorInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nonempty") "intro",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "val")
                  (Setlec.Expr.bvar 0)
                  (Setlec.Expr.app
                    (Setlec.Expr.const
                      (Setlec.Name.str (Setlec.Name.anonymous) "Nonempty")
                      [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                    (Setlec.Expr.bvar 1))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] } }
    1
    1

def nonemptyRecAOld : ConstantInfo :=
  Setlec.ConstantInfo.recInfo
    { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nonempty") "rec",
      levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
      type := Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "α")
                (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "motive")
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "t")
                    (Setlec.Expr.app
                      (Setlec.Expr.const
                        (Setlec.Name.str (Setlec.Name.anonymous) "Nonempty")
                        [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                      (Setlec.Expr.bvar 0))
                    (Setlec.Expr.sort (Setlec.Level.zero))
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never })
                  (Setlec.Expr.forallE
                    (Setlec.Name.str (Setlec.Name.anonymous) "intro")
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "val")
                      (Setlec.Expr.bvar 1)
                      (Setlec.Expr.app
                        (Setlec.Expr.bvar 1)
                        (Setlec.Expr.app
                          (Setlec.Expr.app
                            (Setlec.Expr.const
                              (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Nonempty") "intro")
                              [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                            (Setlec.Expr.bvar 2))
                          (Setlec.Expr.bvar 0)))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                    (Setlec.Expr.forallE
                      (Setlec.Name.str (Setlec.Name.anonymous) "t")
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.anonymous) "Nonempty")
                          [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                        (Setlec.Expr.bvar 2))
                      (Setlec.Expr.app (Setlec.Expr.bvar 2) (Setlec.Expr.bvar 0))
                      { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                    { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] } }
    3
    3
    []

def propextAOld : ConstantVal :=
  { name := Setlec.Name.str (Setlec.Name.anonymous) "propext",
    levelParams := [],
    type := Setlec.Expr.forallE
              (Setlec.Name.str (Setlec.Name.anonymous) "a")
              (Setlec.Expr.sort (Setlec.Level.zero))
              (Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "b")
                (Setlec.Expr.sort (Setlec.Level.zero))
                (Setlec.Expr.forallE
                  (Setlec.Name.anonymous)
                  (Setlec.Expr.app
                    (Setlec.Expr.app
                      (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Iff") [])
                      (Setlec.Expr.bvar 1))
                    (Setlec.Expr.bvar 0))
                  (Setlec.Expr.app
                    (Setlec.Expr.app
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                          [Setlec.Level.succ (Setlec.Level.zero)])
                        (Setlec.Expr.sort (Setlec.Level.zero)))
                      (Setlec.Expr.bvar 2))
                    (Setlec.Expr.bvar 1))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
              { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] } }

def choiceAOld : ConstantVal :=
  { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Classical") "choice",
    levelParams := [Setlec.Name.str (Setlec.Name.anonymous) "u"],
    type := Setlec.Expr.forallE
              (Setlec.Name.str (Setlec.Name.anonymous) "α")
              (Setlec.Expr.sort (Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")))
              (Setlec.Expr.forallE
                (Setlec.Name.anonymous)
                (Setlec.Expr.app
                  (Setlec.Expr.const
                    (Setlec.Name.str (Setlec.Name.anonymous) "Nonempty")
                    [Setlec.Level.param (Setlec.Name.str (Setlec.Name.anonymous) "u")])
                  (Setlec.Expr.bvar 0))
                (Setlec.Expr.bvar 1)
                { bi := Setlec.BinderInfo.default,
                  pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] })
              { bi := Setlec.BinderInfo.default,
                pw := Setlec.PropWhen.ifAllZero [Setlec.Name.str (Setlec.Name.anonymous) "u"] } }

def reduceNatCvAOld : ConstantVal :=
  { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Lean") "reduceNat",
    levelParams := [],
    type := Setlec.Expr.forallE
              (Setlec.Name.str (Setlec.Name.anonymous) "n")
              (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
              (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
              { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never } }

def reduceBoolCvAOld : ConstantVal :=
  { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Lean") "reduceBool",
    levelParams := [],
    type := Setlec.Expr.forallE
              (Setlec.Name.str (Setlec.Name.anonymous) "n")
              (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Bool") [])
              (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Bool") [])
              { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.never } }

def ofReduceNatAOld : ConstantVal :=
  { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Lean") "ofReduceNat",
    levelParams := [],
    type := Setlec.Expr.forallE
              (Setlec.Name.str (Setlec.Name.anonymous) "a")
              (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
              (Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "b")
                (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") [])
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "h")
                  (Setlec.Expr.app
                    (Setlec.Expr.app
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                          [Setlec.Level.succ (Setlec.Level.zero)])
                        (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") []))
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Lean") "reduceNat")
                          [])
                        (Setlec.Expr.bvar 1)))
                    (Setlec.Expr.bvar 0))
                  (Setlec.Expr.app
                    (Setlec.Expr.app
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                          [Setlec.Level.succ (Setlec.Level.zero)])
                        (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Nat") []))
                      (Setlec.Expr.bvar 2))
                    (Setlec.Expr.bvar 1))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
              { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] } }

def ofReduceBoolAOld : ConstantVal :=
  { name := Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Lean") "ofReduceBool",
    levelParams := [],
    type := Setlec.Expr.forallE
              (Setlec.Name.str (Setlec.Name.anonymous) "a")
              (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Bool") [])
              (Setlec.Expr.forallE
                (Setlec.Name.str (Setlec.Name.anonymous) "b")
                (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Bool") [])
                (Setlec.Expr.forallE
                  (Setlec.Name.str (Setlec.Name.anonymous) "h")
                  (Setlec.Expr.app
                    (Setlec.Expr.app
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                          [Setlec.Level.succ (Setlec.Level.zero)])
                        (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Bool") []))
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.str (Setlec.Name.anonymous) "Lean") "reduceBool")
                          [])
                        (Setlec.Expr.bvar 1)))
                    (Setlec.Expr.bvar 0))
                  (Setlec.Expr.app
                    (Setlec.Expr.app
                      (Setlec.Expr.app
                        (Setlec.Expr.const
                          (Setlec.Name.str (Setlec.Name.anonymous) "Eq")
                          [Setlec.Level.succ (Setlec.Level.zero)])
                        (Setlec.Expr.const (Setlec.Name.str (Setlec.Name.anonymous) "Bool") []))
                      (Setlec.Expr.bvar 2))
                    (Setlec.Expr.bvar 1))
                  { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
                { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] })
              { bi := Setlec.BinderInfo.default, pw := Setlec.PropWhen.ifAllZero [] } }
end Receipt

/-! ## The receipt -/

example : eqBasis = Receipt.eqBasisOld := by rfl
example : eqA = Receipt.eqAOld := by rfl
example : eqReflA = Receipt.eqReflAOld := by rfl
example : eqRecA = Receipt.eqRecAOld := by rfl
example : natBasis = Receipt.natBasisOld := by rfl
example : natA = Receipt.natAOld := by rfl
example : natZeroA = Receipt.natZeroAOld := by rfl
example : natSuccA = Receipt.natSuccAOld := by rfl
example : natRecA = Receipt.natRecAOld := by rfl
example : punitBasis = Receipt.punitBasisOld := by rfl
example : punitA = Receipt.punitAOld := by rfl
example : punitUnitA = Receipt.punitUnitAOld := by rfl
example : punitRecA = Receipt.punitRecAOld := by rfl
example : emptyBasis = Receipt.emptyBasisOld := by rfl
example : emptyA = Receipt.emptyAOld := by rfl
example : emptyRecA = Receipt.emptyRecAOld := by rfl
example : quotBasis = Receipt.quotBasisOld := by rfl
example : quotA = Receipt.quotAOld := by rfl
example : quotMkA = Receipt.quotMkAOld := by rfl
example : quotLiftA = Receipt.quotLiftAOld := by rfl
example : quotIndA = Receipt.quotIndAOld := by rfl
example : quotSoundA = Receipt.quotSoundAOld := by rfl
example : iffFamily = Receipt.iffFamilyOld := by rfl
example : propextRaw = Receipt.propextRawOld := by rfl
example : nonemptyFamily = Receipt.nonemptyFamilyOld := by rfl
example : choiceRaw = Receipt.choiceRawOld := by rfl
example : iffA = Receipt.iffAOld := by rfl
example : iffIntroA = Receipt.iffIntroAOld := by rfl
example : iffRecA = Receipt.iffRecAOld := by rfl
example : nonemptyA = Receipt.nonemptyAOld := by rfl
example : nonemptyIntroA = Receipt.nonemptyIntroAOld := by rfl
example : nonemptyRecA = Receipt.nonemptyRecAOld := by rfl
example : propextA = Receipt.propextAOld := by rfl
example : choiceA = Receipt.choiceAOld := by rfl
example : reduceNatCvA = Receipt.reduceNatCvAOld := by rfl
example : reduceBoolCvA = Receipt.reduceBoolCvAOld := by rfl
example : ofReduceNatA = Receipt.ofReduceNatAOld := by rfl
example : ofReduceBoolA = Receipt.ofReduceBoolAOld := by rfl

end Setlec
