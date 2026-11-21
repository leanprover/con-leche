module
prelude

/- Task #448: a theorem at a compiler-trust name (`Lean.reduceBool`, an opaque constant in
   Lean's own `Init.Core`).  Lean accepts it.  Its home refuses it (task #501: the name is reserved
   to the opaque constant of the pin's shape), a reject Lean does not make; an importer reading
   it would present its statement as an axiom at that name, which presents nothing this module
   declares (a record at a compiler-trust name is presented as itself), so the importer's reach
   refuses it too.  `Bool` is what the name's fast path reads (`pinFootprint`). -/

public section

inductive Bool where
  | false
  | true

inductive RtT : Prop where
  | mk : RtT

theorem Lean.reduceBool : RtT := RtT.mk

end
