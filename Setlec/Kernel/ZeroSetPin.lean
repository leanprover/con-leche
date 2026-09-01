import Setlec.Kernel.ZeroSet
import Setlec.PinGen

/-!
# `ToExpr` for the canonical zero-ness datum (task #161, P5 candidate)

The pin generator (`Setlec/PinGen.lean`, task #53) quotes checker data
into elaborated literals.  `ZeroSet` carries a `Prop` field, so it has
no derivable `ToExpr`; the hand-written instance below quotes the
canonicalizer applied to the raw list — **never** the proof term.

Two P5 concerns this answers:

* **No proofs in generated pins** (the #113 module-strip interaction):
  the module system strips proofs from imported modules, so a quoted
  proof term would be unusable at pin-generation time and fragile
  afterwards.  Quoting `ZeroSet.ofList [...]` rebuilds the invariant
  by computation (`rfl`/`decide` at elaboration), so the literal is
  proof-free and the stored value is the canonical set.
* **Stability of the literal**: `ofList` is idempotent on canonical
  input (`ZeroSet.ofList_names`), so re-quoting a quoted datum is the
  identity — pin regeneration is a fixed point.

Layering: this module sits beside the other `ToExpr` instances
(`Setlec/PinGen.lean`) and is imported only where pins are generated;
`Setlec/Kernel/ZeroSet.lean` itself stays free of any `Lean` import.
-/

namespace Setlec.PinGen

open Lean

/-- Quote a `ZeroSet` as `ZeroSet.ofList [...]` — the invariant is
rebuilt by computation, no proof term is embedded. -/
instance : ToExpr Setlec.ZeroSet where
  toExpr s :=
    .app (.const ``Setlec.ZeroSet.ofList []) (toExpr s.names)
  toTypeExpr := .const ``Setlec.ZeroSet []

/-- Quote a `ZPropWhen`; the parameter set goes through `ofList`. -/
instance : ToExpr Setlec.ZPropWhen where
  toExpr
    | .never => .const ``Setlec.ZPropWhen.never []
    | .ifAllZero s => .app (.const ``Setlec.ZPropWhen.ifAllZero []) (toExpr s)
  toTypeExpr := .const ``Setlec.ZPropWhen []

end Setlec.PinGen
