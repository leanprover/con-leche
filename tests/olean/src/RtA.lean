module
prelude

/- Task #448: a theorem at a compiler-trust name (`Lean.reduceBool`, an opaque constant in
   Lean's own `Init.Core`).  Its home accepts it; an importer reading it would present its
   statement as an axiom at that name, which presents nothing this module declares (a record
   at a compiler-trust name is presented as itself), so the importer's reach refuses it.  `Bool` is what the
   name's fast path reads (`pinFootprint`). -/

public section

inductive Bool where
  | false
  | true

inductive RtT : Prop where
  | mk : RtT

theorem Lean.reduceBool : RtT := RtT.mk

end
