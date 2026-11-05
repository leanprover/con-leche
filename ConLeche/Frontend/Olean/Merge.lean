module

public import ConLeche.Frontend.Olean.Closure

@[expose] public section

/-!
# Reading `.olean` files: the closure's constants merged

A name stored by two modules is kept once, by `subsumesInfo`'s rule
(`Lean/Environment.lean`): the later copy replaces the earlier one when it
subsumes it, the earlier one stays when it subsumes the later, and otherwise
the closure is invalid; Lean's own import refuses it ("environment already
contains").
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- Lean's `isPropCheap`: the statement is a telescope over a constant
applied to as many arguments as its own type has binders before a
`Prop` result. -/
def isPropCheap (m : Std.HashMap Name CEntry) (ty : Expr) : Bool :=
  let rec body : Expr → Expr
    | .forallE _ b => body b
    | e => e
  let rec head : Expr → Nat → Option (Name × Nat)
    | .app f _, k => head f (k + 1)
    | .const n _, k => some (n, k)
    | _, _ => none
  let rec drop : Expr → Nat → Option Expr
    | e, 0 => some e
    | .forallE _ b, k + 1 => drop b k
    | _, _ => none
  match head (body ty) 0 with
  | some (n, k) =>
    match m[n]? with
    | some d => match drop d.type k with
      | some (.sort .zero) => true
      | _ => false
    | none => false
  | none => false

/-- `subsumesInfo` (`Lean/Environment.lean`): may `c₁` stand for `c₂`? -/
def subsumes (m : Std.HashMap Name CEntry) (c₁ c₂ : CEntry) : Bool :=
  c₁.name == c₂.name && c₁.type == c₂.type && c₁.levelParams == c₂.levelParams &&
  match c₁.kind, c₂.kind with
  | .thm _ a₁, .thm _ a₂ => a₁ == a₂
  | .thm _ a₁, .ax u₂ => a₁ == [c₂.name] && !u₂
  | .ax u₁, .ax u₂ => u₁ == u₂ && isPropCheap m c₁.type
  | _, _ => false

/-- The merged constants and the order they were first stored in. -/
structure Merged where
  map : Std.HashMap Name CEntry := {}
  order : Array Name := #[]

/-- **Merge one constant** (`finalizeImport`'s rule). -/
def mergeEntry (mg : Merged) (c : CEntry) : Except CheckError Merged :=
  match mg.map[c.name]? with
  | none =>
    let { map, order } := mg
    pure { map := map.insert c.name c, order := order.push c.name }
  | some prev =>
    if subsumes mg.map c prev then
      let { map, order } := mg
      pure { map := map.insert c.name c, order }
    else if subsumes mg.map prev c then pure mg
    else throw (.invalid s!"two modules store different constants named {c.name}")

def mergeAll (ls : Array Loaded) : Except CheckError Merged :=
  ls.foldlM (fun mg l => l.constants.foldlM mergeEntry mg) {}

end ConLeche.Frontend.Olean
