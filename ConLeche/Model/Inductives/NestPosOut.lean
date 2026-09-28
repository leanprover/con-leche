module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Subst
public import ConLeche.Model.Inductives.ErasureKit
public import ConLeche.Model.Inductives.ClassWalkShape

public section

/-!
# The positivity walk's OUTPUT: syntactic lemmas

`nestPos` (`Kernel/Inductives/Positivity.lean`) returns, besides a
field's kind, the field's NORMAL FORM.  This file holds the erasure- and
occurrence-level lemmas its readings need; the output's shape is read
off the positivity DERIVATION (`PosDerivShape.lean`), and
how the normal form relates to the declared type is semantic
(`NestPosRed.lean`).
-/

namespace ConLeche.Model

open ConLeche (Env Expr Name Level NestCtx BinderMeta closeTelescope openPisAtFvars)

/-! ## Erasure-level lemmas -/

end ConLeche.Model
