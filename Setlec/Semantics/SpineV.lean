import Setlec.Verify.Denote
import Setlec.Verify.Denote.OpenVars
import Setlec.Verify.Denote.VClosed

/-!
# `VExpr`-level spine builders

Three transposes of the checker's spine builders onto the `VExpr` side.
They mention `VExpr`, `TConstVal` and `Name` and nothing else — no
relation, no model, no `Env` invariant — and the graded lane uses all
three (`SetP/Annot/EnvS2P.lean`, `SetP/IndEtaLawP.lean`,
`SetP/Step2/Proj{Pins,Rows}P.lean`, `SetBase/ProjPins.lean`).

**Why they live here** (2026-09-05).  They were written inside
`SetBase/Rel.lean`, the collapsed model's relation family, because that
is where the rules that needed them were.  The SetR removal's Stage C
deleted the relation family — `Red`, `Infer`, `DefEq`, `Tele`, `DefEqL`
and the whole derivation bridge above them — and these three had to be
extracted first, because deleting a module whose *representation-free
residue* has live consumers is a re-statement, not a deletion.  That is
the interned removal's stage-3 rule, and this file is it at one tenth
the scale.

The statements are byte-unchanged from `SetBase/Rel.lean`; only the
namespace prefix's home moved, and `Setlec.SetR` is unchanged, so no
consumer needed a rename.
-/

namespace Setlec.Semantics

open Setlec.TT
open Setlec.TTVerify

/-- The projection spines of a structural-eta comparison: field `j` is
the installed projection function applied to the type's arguments and
the stuck side.  Transpose of the map in `structEtaCertWith`
(`Core.lean:966-968`); `ψt` is the *type's* level assignment
(`structEtaProjCerts` pins `cvp.levelParams = cvT.levelParams`). -/
def projSpinesV (cval : TConstVal) (T : Name) (ψt : Name → Nat)
    (ts : List VExpr) (b : VExpr) (nF : Nat) : List VExpr :=
  (List.range nF).map fun j =>
    VExpr.mkAppN (cval (projFnName T j) ψt) (ts ++ [b])

/-- The eta-rescue fabrication's argument spine: the reduced type's
arguments followed by the projections of the stuck major.  Transpose of
`etaFabArgs` (`Core.lean:1058-1061`). -/
def etaFabArgsV (cval : TConstVal) (T : Name) (ψt : Name → Nat)
    (ts : List VExpr) (major : VExpr) (nF : Nat) : List VExpr :=
  ts ++ projSpinesV cval T ψt ts major nF

/-- `VExpr`-level residual of a `pi`-telescope along an argument list —
the transpose of `piResidual` (`Core.lean:747-750`), used to spell a
projection's conclusion type without mentioning the checker's
`Expr`s. -/
def piResidualV : VExpr → List VExpr → Option VExpr
  | T, [] => some T
  | .pi _ B, a :: as => piResidualV (B.inst a) as
  | _, _ :: _ => none

end Setlec.Semantics
