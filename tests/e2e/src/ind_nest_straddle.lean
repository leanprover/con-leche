--#export Straddle.self

/- End-to-end fixture (task #315 R2): a nested block whose
   CONSTANT-HEADED pin-target edge has a STRADDLING argument — an
   argument of the container's own field domain that becomes a nested
   occurrence only after the pin's substitution.

   `Box`'s stored field domain is `List (Option α)`: head `List` (a
   constant, so `nestedPinOrderAt` classifies the edge as
   constant-headed and checks the declaration order), argument
   `Option α` (a container application).  At the block the elimination
   mints

     pin 0 = Box Straddle            components [Straddle]
     pin 1 = List (Option Straddle)  components [Option Straddle]
     pin 2 = Option Straddle         components [Straddle]

   and K.59's rewrite of pin 1's component is the MIMIC
   `_nested.Option_3`, not `Option Straddle` — which is why the model's
   law (M) is not a compositional fact at such an edge (DESIGN,
   "#### R2: the candidate component family, priced").

   official: 0.  con-leche: 0 raw; nested shadow `Straddle=accept`. -/
inductive Box (α : Type) where
  | mk (l : List (Option α))

inductive Straddle where
  | node (b : Box Straddle)

theorem Straddle.self (x : Straddle) : x = x := rfl
