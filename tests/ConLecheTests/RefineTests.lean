module

public import ConLeche
public import ConLeche.Frontend.Prelude
/- The `#guard`s below are EVALUATED, so the constants they name have to
be reachable from meta code too; a module needed at both levels is
imported twice. -/
meta import ConLeche
meta import ConLeche.Frontend.Prelude

public section

/-!
# Reduction at a refinement (task #469)

`envS` refines `envD` (`Rules.EnvRefines`): the two agree but for `two`, a definition
(`two := 2`) in `envD` and its statement (the axiom `two : Nat`) in `envS`, as an importer holds an
unexposed definition of another module.  The pure kernel's runs at the two environments differ
WITHOUT failing at `envS`:

* `whnf two` is `two` at `envS` and the literal `2` at `envD`;
* `isDefEq two 2` is `false` at `envS` and `true` at `envD`;
* the former `Foo : T (two + 1)`, `T` an exposed definition by `Nat.rec`
  (`T 0 = Type`, `T (k+1) = P k → Type`), reduces at both, to DIFFERENT telescopes.  At `envD`
  the major `Nat.add two 1` is folded by the literal fast path to `3`, whose constructor form binds
  `k := 2`: `P 2 → Type`.  At `envS` the fast path finds no literal and `Nat.add` unfolds, by its
  recursion on the literal `1`, to `Nat.succ (Nat.rec two … 0)`, which binds that recursor
  application: `P (Nat.rec two … 0) → Type`.  So a successful `reducedFormer`/`familyTelescope`
  at a refinement need not be the one at the refined environment; what carries over is the
  derivation (`Rules.Red.refine`, `Rules.reducedFormer_refine`).
-/

namespace ConLecheTests.Refine

open ConLeche

@[expose] def nm (s : String) : Name := .str .anonymous s
@[expose] def lv : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (lv n)
@[expose] def cNat : Expr := .const natName []
@[expose] def cP : Expr := .const (nm "P") []
@[expose] def cTwo : Expr := .const (nm "two") []
@[expose] def cT : Expr := .const (nm "T") []

/-- The prelude's records: `Nat` with its recursor and the literal support. -/
@[expose] def base : Env :=
  match ConLeche.Frontend.builtinPreludeE with
  | .ok p => streamEnv p.decls.toList
  | .error _ => Env.empty

/-- `T := fun n => Nat.rec (motive := fun _ => Type 1) Type (fun k _ => P k → Type) n`. -/
@[expose] def tVal : Expr :=
  .lam cNat (Expr.mkAppN (.const (natName.str "rec") [lv 2])
    [.lam cNat (.sort (lv 2)), .sort (lv 1),
     .lam cNat (.lam (.sort (lv 2)) (.forallE (.app cP (.bvar 1)) (.sort (lv 1)))),
     .bvar 0])

/-- `Nat.add := fun a b => Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.succ ih) b`, the
prelude's structural recursion on the second argument. -/
@[expose] def addRec (a b : Expr) : Expr :=
  Expr.mkAppN (.const (natName.str "rec") [lv 1])
    [.lam cNat cNat, a, .lam cNat (.lam cNat (.app (.const natSuccName []) (.bvar 0))), b]

@[expose] def addVal : Expr := .lam cNat (.lam cNat (addRec (.bvar 1) (.bvar 0)))

/-- The constants both environments share. -/
@[expose] def shared : List ConstantInfo :=
  [.defnInfo ⟨nm "T", [], .forallE cNat (.sort (lv 2))⟩ tVal (.regular 2),
   .defnInfo ⟨natAddName, [], .forallE cNat (.forallE cNat cNat)⟩ addVal (.regular 1),
   .axiomInfo ⟨nm "P", [], .forallE cNat (.sort (lv 1))⟩]

/-- `two` a definition. -/
@[expose] def envD : Env :=
  ⟨.defnInfo ⟨nm "two", [], cNat⟩ (.lit (.natVal 2)) (.regular 1) :: shared ++ base.consts,
    base.tables⟩

/-- `two` its statement. -/
@[expose] def envS : Env :=
  ⟨.axiomInfo ⟨nm "two", [], cNat⟩ :: shared ++ base.consts, base.tables⟩

@[expose] def ops : CheckerOps CheckM := pureOps .verified

/-- `Foo : T (Nat.add two 1)`. -/
@[expose] def cvFoo : ConstantVal :=
  ⟨nm "Foo", [], .app cT (Expr.mkAppN (.const natAddName []) [cTwo, .lit (.natVal 1)])⟩

@[expose] def teleD : Expr := .forallE (.app cP (.lit (.natVal 2))) (.sort (lv 1))
@[expose] def teleS : Expr := .forallE (.app cP (addRec cTwo (.lit (.natVal 0)))) (.sort (lv 1))

-- the prelude parsed (else every guard below would run on an empty base)
#guard (base.find? natName).isSome

-- `whnf`: stuck at the statement, a literal at the definition
#guard (ops.whnf envS 0 cTwo).toOption == some cTwo
#guard (ops.whnf envD 0 cTwo).toOption == some (.lit (.natVal 2))

-- `isDefEq`: `false` at the statement, `true` at the definition, neither failing
#guard (ops.isDefEq envS 0 cTwo (.lit (.natVal 2))).toOption == some false
#guard (ops.isDefEq envD 0 cTwo (.lit (.natVal 2))).toOption == some true

-- the former's reduced telescope: both succeed, at different telescopes
#guard ((reducedFormer ops envD cvFoo 1).toOption.map (·.type)) == some teleD
#guard ((reducedFormer ops envS cvFoo 1).toOption.map (·.type)) == some teleS
#guard teleD != teleS

end ConLecheTests.Refine
