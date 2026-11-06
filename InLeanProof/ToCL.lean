module

public import InLean
public import ConLeche.Kernel.Install

/-!
# `toCL`: Lean's data read as con-leche's (task #451, lane F)

The simulation of InLean onto con-leche's checker relates every InLean
value to the con-leche value it stands for.  `toCL` erases what
con-leche's representation does not have — binder names and infos,
`mdata`, a `let`'s `nonDep` flag — and is undefined (`none`) on what
con-leche's checker never sees: metavariables, level metavariables, and
free variables outside InLean's interned table.

**Free variables.**  InLean interns a free variable as the pair (depth,
type) under the id `fvRoot.d.n` (`InLean.mkFVarM`; the depth `d` is in the
id, the type is `CState.fvTys[n]`); con-leche's free variable is the value
`.fvar d type`.  `toExpr` takes the translation of the ids as a parameter
`fv`; `FVarTable.trans` builds it from InLean's table.  Numbers are global
and the classes are per depth, so only a *live* pair (the number registered
in its depth's class, `FVarTable.live`) translates: a number read at another
depth is no id the checker built.  A type mentions only variables interned
before it (its own context's), so the table is translated by recursion on
the number.

**Declarations.**  A Lean declaration group (one constant, the quotient
package's constant, an inductive block's formers, constructors and
recursors) reads as con-leche's record of it (`toDecl`): the record the
export writes for it, in the stream's shape (`indInfo` without
capabilities, rules `.plain`).  What con-leche installs for it is then
`declConstants`/`declTables` of the record (`ConLeche/Kernel/Install.lean`).
-/

@[expose] public section

namespace InLeanProof

/-- Names: the same three constructors. -/
def toName : Lean.Name → ConLeche.Name
  | .anonymous => .anonymous
  | .str p s => .str (toName p) s
  | .num p n => .num (toName p) n

/-- Names back. -/
def fromName : ConLeche.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (fromName p) s
  | .num p n => .num (fromName p) n

theorem fromName_toName : ∀ n : Lean.Name, fromName (toName n) = n
  | .anonymous => rfl
  | .str p s => by simp [toName, fromName, fromName_toName p]
  | .num p n => by simp [toName, fromName, fromName_toName p]

theorem toName_inj {a b : Lean.Name} (h : toName a = toName b) : a = b := by
  rw [← fromName_toName a, h, fromName_toName]

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

/-- InLean's interned free-variable table, as the proof reads it: the types
(`CState.fvTys`) and the classes (`CState.fvCls`, keyed by depth and
`EO.clHash` of the type). -/
structure FVarTable where
  tys : Array Lean.Expr
  cls : Std.HashMap (Nat × UInt64) (List Nat)

/-- **Number `n` is live at depth `d`**: it was interned at that depth, so it
sits in the class list of its depth and its type's hash.  Only a live pair
is an id the checker builds (`InLean.mkFVarM`); a number read at another
depth is not one. -/
def FVarTable.live (t : FVarTable) (d n : Nat) : Bool :=
  match t.tys[n]? with
  | some ty => (t.cls.getD (d, InLean.EO.clHash ty) []).contains n
  | none => false

/-- The translation of interned number `n` at depth `d`, by recursion on
`n` (an interned type mentions earlier numbers only; a later one, or a pair
that is not live, reads as untranslatable). -/
def FVarTable.transNum (t : FVarTable) (d : Nat) : Nat → Option ConLeche.Expr
  | n => if t.live d n then do
      let ty ← t.tys[n]?
      let cty ← toExpr (fun id =>
        match InLean.fvParts? id with
        | some (d', m) => if m < n then t.transNum d' m else none
        | none => none) ty
      pure (.fvar d cty)
    else none
termination_by n => n
decreasing_by all_goals assumption

/-- The id translation `toExpr` takes. -/
def FVarTable.trans (t : FVarTable) (id : Lean.FVarId) : Option ConLeche.Expr :=
  match InLean.fvParts? id with
  | some (d, n) => t.transNum d n
  | none => none

/-- The id translation an interned type at number `n` is read with: the
numbers below `n` only. -/
def FVarTable.inner (t : FVarTable) (n : Nat) (id : Lean.FVarId) : Option ConLeche.Expr :=
  match InLean.fvParts? id with
  | some (d', m) => if m < n then t.transNum d' m else none
  | none => none

theorem FVarTable.transNum_eq (t : FVarTable) (d n : Nat) :
    t.transNum d n = if t.live d n then (do
      let ty ← t.tys[n]?
      let cty ← toExpr (t.inner n) ty
      pure (.fvar d cty)) else none := by
  rw [FVarTable.transNum]; rfl

/-- The closed reading (no free variables): declarations' own terms. -/
def toExprC : Lean.Expr → Option ConLeche.Expr := toExpr (fun _ => none)

/-! ## Constants and declaration groups -/

/-- A constant's name, levels and type. -/
def toCV (v : Lean.ConstantVal) : Option ConLeche.ConstantVal := do
  pure ⟨toName v.name, v.levelParams.map toName, ← toExprC v.type⟩

/-- Reducibility hints. -/
def toHint : Lean.ReducibilityHints → ConLeche.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- A recursor rule, as the export writes it (`.plain`, con-leche's install
reads the firing mode off the block). -/
def toRule (r : Lean.RecursorRule) : Option ConLeche.RecRule := do
  pure ⟨toName r.ctor, r.nfields, .plain, ← toExprC r.rhs⟩

def toRules : List Lean.RecursorRule → Option (List ConLeche.RecRule)
  | [] => some []
  | r :: rs => do pure ((← toRule r) :: (← toRules rs))

/-- An inductive block's constant, as the export's record of it. -/
def toBlockRecord : Lean.ConstantInfo → Option ConLeche.ConstantInfo
  | .inductInfo v => do pure (.indInfo (← toCV v.toConstantVal) {})
  | .ctorInfo v => do pure (.ctorInfo (← toCV v.toConstantVal) v.numParams v.numFields)
  | .recInfo v => do
    pure (.recInfo (← toCV v.toConstantVal)
      (v.numParams + v.numMotives + v.numMinors + v.numIndices)
      (v.numParams + v.numMotives + v.numMinors) v.k (← toRules v.rules))
  | _ => none

def toBlock : List Lean.ConstantInfo → Option (List ConLeche.ConstantInfo)
  | [] => some []
  | c :: cs => do pure ((← toBlockRecord c) :: (← toBlock cs))

/-- The quotient kinds. -/
def toQuotKind : Lean.QuotKind → ConLeche.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-- **A declaration group, read as con-leche's record**: one constant, or an
inductive block (formers, constructors, recursors; its parameter count is
the first former's). -/
def toDecl : List Lean.ConstantInfo → Option ConLeche.Declaration
  | [.axiomInfo v] => do pure (.axiomDecl (← toCV v.toConstantVal))
  | [.defnInfo v] => do
    pure (.defnDecl (← toCV v.toConstantVal) (← toExprC v.value) (toHint v.hints))
  | [.thmInfo v] => do pure (.thmDecl (← toCV v.toConstantVal) (← toExprC v.value))
  | [.opaqueInfo v] => do pure (.opaqueDecl (← toCV v.toConstantVal) (← toExprC v.value))
  | [.quotInfo v] => do pure (.quotDecl (toQuotKind v.kind) (← toCV v.toConstantVal))
  | cs@(.inductInfo v :: _) => do pure (.indDecl (← toBlock cs) v.numParams)
  | _ => none

end InLeanProof
