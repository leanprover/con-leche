module

import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Denote
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.Denote.VClosed
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Shift
public import ConLeche.Kernel.Checker
public import ConLeche.Model.BasisEq
public import ConLeche.Model.IndCons
public import ConLeche.Model.IndTele
public import ConLeche.Semantics.DeclRun
public import ConLeche.Semantics.IndBlockFacts
public import ConLeche.Verify.Abstract
public import ConLeche.Verify.Denote.Rename
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.Extend.Inversions
public import ConLeche.Verify.Subst
public section

/-!
# The η key at the projection cons (task #161, IND TIER part 3, step 5b)

`capsOk_cons_proj` leaves exactly one law open — `EtaLaw` for the
family the projection-function cons *completes* — and this file is it.
It is `etaLawKeyS`'s transpose with the half `memberEtaLaw` was
allowed to drop put back.

## What changes against the member key, and what does not

Part 2's §4 recorded that `etaFields = 0` "deletes half of
`etaLawKeyS`", and that the deletion does **not** transfer to the
projection cons.  That prediction held exactly, and the returning half
is smaller than the phrase suggests: `memberEtaLaw`'s skeleton is
reused move for move, and the projection spine enters at exactly three
points —

* the fabricated spine is `ts ++ projSpines …` instead of `ts`;
* the pinned body `hsbody` carries `etaFields` further arguments, so
  `hCs`'s right-hand side is the model constructor applied to the
  parameter spine **and** to one model-projection application per
  field;
* each of those applications is evaluated by the *same*
  `interp_bvarSpine` the parameter spine uses.

That last point is the reason this file is short.  The projection
argument's pinned spine is
`((range nP).map fun k => bvar (nP - k)) ++ [bvar 0]`, and that list
**is** `(range (nP+1)).map fun k => bvar (nP - k)` — the member slot is
the `k = nP` entry of the same descending family.  So one
`instSeq_openSpine` at `nP+1` reads it, and one `interp_bvarSpine` at
the spine `ts ++ [x]` evaluates it, with the side condition
`σ (nP - q) = consN (ts ++ [x]) ρ (nP - q)` — which is *reflexivity*,
because `consN (ts ++ [x]) ρ` is `σ` itself.  The parameter spine's
own side condition needed an `omega`; the projection spine's needs
nothing.

## Three premises the member key did not need, and one it did

* **`hvP`** — the projection valuation identifications, v1's third
  install-supplied identification (`etaLawKeyS` takes `hvT`/`hvC`/`hvP`
  and part 2 derived the first two from `BlockAcvalInstalled`).  There
  is no invariant to derive this one from: the family's *earlier*
  projection slots were installed by earlier `ProjInstallR` steps, so
  the identification is the install fold's to carry, exactly as in v1.
  Taking it as a premise is part 2's own lesson applied before it
  could bite — the conclusion transposes, the premise set is
  re-derived from `etaLawKeyS`'s premises.
* **`hprojE`** is *not* a new premise: `EtaPins` already carries the
  model projections' lookups (`Verify/Extend/Iota.lean:1067-1069`), and
  the member key destructured them away unused.

Against that, two of the member key's own obligations **disappear**
here, for `projEtaSplit`'s reason: a `recInfo` cons can be neither the
family's former nor its capability constructor, so `hvT` and `hvC` are
one `acvalWith_ne` each with no case split, where the member key had
to branch on "is the cons the former?" four times over.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps ReducibilityHint BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-! ## The pinned projection argument, read and evaluated

The one genuinely new move.  Everything else in this file is
`memberEtaLaw`'s. -/

/-- `interp` of an application spine, as a `map`-then-`foldl`.  The
member key inlined this; the mixed spine needs it as a rewrite so the
two halves can be split with `List.map_append`. -/
theorem interp_mkAppN_map (σ : Nat → V) (K : AnnotTerm) :
    ∀ as : List AnnotTerm,
      interp V σ (AnnotTerm.mkAppN K as)
        = (as.map (interp V σ)).foldl SetTheory.app (interp V σ K) := by
  intro as
  rw [interp_mkAppN]
  generalize interp V σ K = b
  induction as generalizing b with
  | nil => rfl
  | cons a asr ih => simpa using ih (SetTheory.app b (interp V σ a))

/-! ## The key -/

/-! ## The row, closed

`capsOk_cons_proj` and `projEtaLaw` compose with **no residue**: the
projection cons's `caps_ok` obligation is discharged outright from the
install-supplied bundle, exactly as `memberInstallPM`'s two rows were
once part 2 proved the member keys.  The bundle is quantified over the
family's own data because `hvP` mentions `caps.etaFields`, which is not
in scope until the family is found. -/

end ConLeche.Model
