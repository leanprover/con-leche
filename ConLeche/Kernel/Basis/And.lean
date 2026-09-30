module

public import ConLeche.Kernel.Basis.Builder

@[expose] public section

/-!
# The pinned `And` block

The raw pin — the `And` block exactly as an export carries it: the
toolchain's `Init.Prelude` structure

    structure And (a b : Prop) : Prop where
      intro :: (left : a) (right : b)

at the parser's raw binder annotations (its projection functions
`And.left`/`And.right` are ordinary definition records of their own).

**Why `And` is pinned, and how that differs from the basis blocks.**
The checker has code for "the" `And`: the stuck-proof rescue
(`majorToCtor`'s `And` branch, `ConLeche/Kernel/Core.lean`) fabricates
`And.intro a b h.1 h.2` for an `And.rec` whose major is a proof that
does not reduce to a constructor.  That branch must be available in
every accepted run, so the name must denote the toolchain's `And`.
Unlike `Eq`, `Nat`, `Empty` and `False`, `And` has no hand-written set
model and is not installed from literals: the fold only RECOGNISES the
block (`andPinOk`, `ConLeche/Kernel/Basis.lean`) and rejects any other
record claiming one of its three names; the matching block then goes
through the ordinary inductive installer, which stores its projection
table like any structure's.  The rescue's soundness needs none of this
(its certificate is proof irrelevance, sound whatever `And` is); the
pin is what makes it *present*.
-/

namespace ConLeche

open BasisDSL

/-- The name `And.intro`. -/
def andIntroName : Name := andName.str "intro"

/-- The name `And.rec`. -/
def andRecName : Name := andName.str "rec"

/-- `And (a b : Prop) : Prop`. -/
def andRaw : ConstantInfo :=
  .indInfo ⟨andName, [], pi "a" prop (pi "b" prop prop)⟩
    { all := [andName], nparams := 2, ctors := [andIntroName] }

/-- `And.intro {a b : Prop} (left : a) (right : b) : And a b`. -/
def andIntroRaw : ConstantInfo :=
  .ctorInfo ⟨andIntroName, [],
    piI "a" prop <|
    piI "b" prop <|
    pi "left" (bv 1) <|
    pi "right" (bv 1) <|
    ap2 (cnst andName) (bv 3) (bv 2)⟩
    2 2

/-- The motive of `And.rec`: `And a b → Sort u`, in the `a`/`b` binder
context (`a` is `#1`, `b` is `#0`). -/
def andRecMotive : Expr :=
  pi "t" (ap2 (cnst andName) (bv 1) (bv 0)) (srt u)

/-- The minor premise of `And.rec`:
`(left : a) → (right : b) → motive (And.intro left right)`, in the
`a`/`b`/`motive` binder context. -/
def andRecMinor : Expr :=
  pi "left" (bv 2) <|
  pi "right" (bv 2) <|
  .app (bv 2) (ap4 (cnst andIntroName) (bv 4) (bv 3) (bv 1) (bv 0))

/-- `And.rec.{u} {a b : Prop} {motive : And a b → Sort u}
(intro : (left : a) → (right : b) → motive ⟨left, right⟩)
(t : And a b) : motive t`. -/
def andRecRaw : ConstantInfo :=
  .recInfo ⟨andRecName, [uN],
    piI "a" prop <|
    piI "b" prop <|
    piI "motive" andRecMotive <|
    pi "intro" andRecMinor <|
    pi "t" (ap2 (cnst andName) (bv 3) (bv 2)) <|
    .app (bv 2) (bv 0)⟩
    4 4
    [rule andIntroName 2 <|
      lmI "a" prop <|
      lmI "b" prop <|
      lmI "motive" andRecMotive <|
      lm "intro" andRecMinor <|
      lm "left" (bv 3) <|
      lm "right" (bv 3) <|
      ap2 (bv 2) (bv 1) (bv 0)]

/-- The pinned `And` block, in the order an export lists it. -/
def andPin : List ConstantInfo := [andRaw, andIntroRaw, andRecRaw]

/-- The names the pinned `And` block declares: no other record may
declare any of them (`andPinOk`). -/
def andPinNames : List Name := [andName, andIntroName, andRecName]

end ConLeche
