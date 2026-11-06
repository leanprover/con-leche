module

public import InLean
public import ConLeche.Kernel.ExprOps

/-!
# `toCL`: Lean's data read as con-leche's (task #451, lane F)

The simulation of InLean onto con-leche's checker relates every InLean
value to the con-leche value it stands for.  `toCL` erases what
con-leche's representation does not have — binder names and infos,
`mdata`, a `let`'s `nonDep` flag — and is undefined (`none`) on what
con-leche's checker never sees: metavariables, level metavariables, and
free variables outside InLean's interned table.

**Free variables.**  InLean interns a free variable as the pair (depth,
type) under an `FVarId` `fvRoot.num n` (`InLean.mkFVar`, `St.fvDeps`,
`St.fvTys`); con-leche's free variable is the value `.fvar depth type`.
`toExpr` takes the translation of the ids as a parameter `fv`;
`FVarTable.trans` builds it from InLean's table.  A type mentions only
variables interned before it (its own context's), so the table is
translated by recursion on the id.
-/

@[expose] public section

namespace InLeanProof

/-- Names: the same three constructors. -/
def toName : Lean.Name → ConLeche.Name
  | .anonymous => .anonymous
  | .str p s => .str (toName p) s
  | .num p n => .num (toName p) n

/-- Levels; a level metavariable has no con-leche reading. -/
def toLevel : Lean.Level → Option ConLeche.Level
  | .zero => some .zero
  | .succ u => (toLevel u).map .succ
  | .max u v => do pure (.max (← toLevel u) (← toLevel v))
  | .imax u v => do pure (.imax (← toLevel u) (← toLevel v))
  | .param n => some (.param (toName n))
  | .mvar _ => none

def toLevels : List Lean.Level → Option (List ConLeche.Level)
  | [] => some []
  | u :: us => do pure ((← toLevel u) :: (← toLevels us))

def toLit : Lean.Literal → ConLeche.Literal
  | .natVal n => .natVal n
  | .strVal s => .strVal s

/-- Expressions, given the translation `fv` of free-variable ids. -/
def toExpr (fv : Lean.FVarId → Option ConLeche.Expr) : Lean.Expr → Option ConLeche.Expr
  | .bvar i => some (.bvar i)
  | .fvar id => fv id
  | .mvar _ => none
  | .sort u => (toLevel u).map .sort
  | .const n us => (toLevels us).map (.const (toName n))
  | .app f a => do pure (.app (← toExpr fv f) (← toExpr fv a))
  | .lam _ t b _ => do pure (.lam (← toExpr fv t) (← toExpr fv b))
  | .forallE _ t b _ => do pure (.forallE (← toExpr fv t) (← toExpr fv b))
  | .letE _ t v b _ => do pure (.letE (← toExpr fv t) (← toExpr fv v) (← toExpr fv b))
  | .lit l => some (.lit (toLit l))
  | .mdata _ e => toExpr fv e
  | .proj s i e => (toExpr fv e).map (.proj (toName s) i)

/-- InLean's interned free-variable table, as the proof reads it. -/
structure FVarTable where
  deps : Array Nat
  tys : Array Lean.Expr

/-- The translation of interned id `n`, by recursion on `n` (an interned
type mentions earlier ids only; a later one reads as untranslatable). -/
def FVarTable.transNum (t : FVarTable) : Nat → Option ConLeche.Expr
  | n => do
    let d ← t.deps[n]?
    let ty ← t.tys[n]?
    let cty ← toExpr (fun id =>
      match InLean.fvNum? id with
      | some m => if m < n then t.transNum m else none
      | none => none) ty
    pure (.fvar d cty)
termination_by n => n
decreasing_by all_goals assumption

/-- The id translation `toExpr` takes. -/
def FVarTable.trans (t : FVarTable) (id : Lean.FVarId) : Option ConLeche.Expr :=
  match InLean.fvNum? id with
  | some n => t.transNum n
  | none => none

/-- The closed reading (no free variables): declarations' own terms. -/
def toExprC : Lean.Expr → Option ConLeche.Expr := toExpr (fun _ => none)

end InLeanProof
