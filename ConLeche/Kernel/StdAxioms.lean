module

public import ConLeche.Kernel.BasisA

@[expose] public section

/-!
# Recognized standard axioms and their prerequisite shapes

A stream may use the standard axioms `propext` and `Classical.choice`.
Both are true in the set-theoretic model — `propext` by extensionality
of propositions (derived through the stored `Iff` recursor),
`Classical.choice` by global choice (through the stored `Nonempty`
recursor) — so the checker accepts exactly these two axioms, after
pinning their types and the *shapes of the inductives they quantify
over* to the toolchain's.  The pins below are hand-written through the
builder in `ConLeche/Kernel/Basis/Builder.lean`.

**Binder annotations (tasks #142, #203, #205).**  A pin carries no
binder name and no binder info — `Expr` has neither field (task #205),
so `propext`'s `{a b : Prop}` and `Classical.choice`'s `{α}` are
`pi`/`piI` for the reader only.  Binders carry no datum either (task
#342), so the comparison `ConstantVal.matchesPin` is plain equality;
`Expr.ErasedEq` — the model's "same denotation" relation, up to `fvar`
type annotations — bridges a hit.
-/

namespace ConLeche

open Name (anonymous)
open BasisDSL

/-- The name `propext`. -/
def propextName : Name := anonymous |>.str "propext"

/-- The name `Classical.choice`. -/
def choiceName : Name := (anonymous |>.str "Classical") |>.str "choice"

/-- The name `Iff`. -/
def iffName : Name := anonymous |>.str "Iff"

/-- The name `Iff.intro`. -/
def iffIntroName : Name := iffName |>.str "intro"

/-- The name `Iff.rec`. -/
def iffRecName : Name := iffName |>.str "rec"

/-- The name `Nonempty`. -/
def nonemptyName : Name := anonymous |>.str "Nonempty"

/-- The name `Nonempty.intro`. -/
def nonemptyIntroName : Name := nonemptyName |>.str "intro"

/-- The name `Nonempty.rec`. -/
def nonemptyRecName : Name := nonemptyName |>.str "rec"

/-- Shape comparison for the standard pins: exact name, level
parameters and type.

**Guidance for anyone adding a pin.**  Two properties of a pin decide
how expensive it is for a *consumer* of the pin (the checker's own
soundness proofs, and the type-theory bridge of task #119):

* **Pin the level when the artifact only ever needs one.**  A pin that
  quantifies a level is more general, and that generality is paid for
  by every consumer: it must supply a level assignment and carry it
  through each application.  Measured instance —
  `Nonempty.rec`'s motive sort is pinned to `Prop` while
  `Iff.rec.{u_1,u}` quantifies its, and the bridge's `Iff` elimination
  needed a bespoke assignment driving `u_1` to `0` where the
  `Nonempty` one needed nothing at all.  *A pin that fixes a level is
  easier to consume than a pin that quantifies one, even when the
  quantified pin is more general.*
* **What this comparison forgives is what the interpretation ignores.**
  `matchesPin` accepts a stored type equal to the pin *up to binder
  names*, and neither the set model's `interp` nor
  `denote` reads a binder name — a binder is opened with a variable
  whose meaning is its de Bruijn index.  That alignment is why a
  `matchesPin` hit is usable at all: a consumer may compute on the
  *pin* rather than on whatever spelling the input stream sent.
  Preserve it — a pin comparison must never forgive something the
  interpretation reads.

**The comparison is plain equality** (task #342): `Expr` carries no
binder name, no binder info and no binder datum, so nothing is left to
forgive.  `Expr`'s `==` is the memoised, pointer-first `Expr.beq`, so a
DAG-shared stream side is compared without unfolding it (the
`tests/e2e/tower_axiom_pin.ndjson` shape, task #226). -/
def ConstantVal.matchesPin (cv pin : ConstantVal) : Bool :=
  cv.name = pin.name && cv.levelParams = pin.levelParams &&
    cv.type == pin.type

/-- `Iff (a b : Prop) : Prop`. -/
def iffA : ConstantInfo :=
  .indInfo ⟨iffName, [], pi "a" prop <| pi "b" prop prop⟩ {}

/-- `Iff.intro (a b : Prop) (mp : a → b) (mpr : b → a) : Iff a b`. -/
def iffIntroA : ConstantInfo :=
  .ctorInfo ⟨iffIntroName, [],
    pi "a" prop <|
    pi "b" prop <|
    pi "mp" (piA (bv 1) (bv 1)) <|
    pi "mpr" (piA (bv 1) (bv 3)) <|
    ap2 (cnst iffName) (bv 3) (bv 2)⟩
    2 2

/-- `Iff.rec`'s minor premise, in the `a`/`b`/`motive` binder context:
`∀ (mp : a → b) (mpr : b → a), motive (Iff.intro a b mp mpr)`. -/
def iffRecIntro : Expr :=
  pi "mp" (pi "right" (bv 2) (bv 2)) <|
  pi "mpr" (piA (bv 2) (bv 4)) <|
  .app (bv 2) (ap4 (cnst iffIntroName) (bv 4) (bv 3) (bv 1) (bv 0))

/-- `Iff.rec.{u} (a b : Prop) (motive : Iff a b → Sort u)
(intro : ∀ mp mpr, motive (Iff.intro a b mp mpr)) (t : Iff a b) :
motive t`. -/
def iffRecA : ConstantInfo :=
  .recInfo ⟨iffRecName, [uN],
    pi "a" prop <|
    pi "b" prop <|
    pi "motive" (pi "t" (ap2 (cnst iffName) (bv 1) (bv 0)) (srt u)) <|
    pi "intro" iffRecIntro <|
    pi "t" (ap2 (cnst iffName) (bv 3) (bv 2)) (.app (bv 2) (bv 0))⟩
    4 4 false []

/-- The raw `propext` declaration:
`propext (a b : Prop) : Iff a b → Eq.{1} Prop a b`. -/
def propextA : ConstantVal :=
  ⟨propextName, [],
    pi "a" prop <|
    pi "b" prop <|
    piA (ap2 (cnst iffName) (bv 1) (bv 0)) <|
    ap3 (cnst eqName [.succ .zero]) prop (bv 2) (bv 1)⟩

/-- `Nonempty.{u} (α : Sort u) : Prop`. -/
def nonemptyA : ConstantInfo :=
  .indInfo ⟨nonemptyName, [uN], pi "α" (srt u) prop⟩ {}

/-- `Nonempty.intro.{u} (α : Sort u) (val : α) : Nonempty α`. -/
def nonemptyIntroA : ConstantInfo :=
  .ctorInfo ⟨nonemptyIntroName, [uN],
    pi "α" (srt u) <|
    pi "val" (bv 0) <|
    .app (cnst nonemptyName [u]) (bv 1)⟩
    1 1

/-- `Nonempty.rec.{u} (α : Sort u) (motive : Nonempty α → Prop)
(intro : ∀ val, motive (Nonempty.intro α val)) (t : Nonempty α) :
motive t`.  The motive sort is pinned to `Prop` (see the guidance
above). -/
def nonemptyRecA : ConstantInfo :=
  .recInfo ⟨nonemptyRecName, [uN],
    pi "α" (srt u) <|
    pi "motive" (pi "t" (.app (cnst nonemptyName [u]) (bv 0)) prop) <|
    pi "intro"
      (pi "val" (bv 1) <|
        .app (bv 1) (ap2 (cnst nonemptyIntroName [u]) (bv 2) (bv 0))) <|
    pi "t" (.app (cnst nonemptyName [u]) (bv 2)) (.app (bv 2) (bv 0))⟩
    3 3 false []

/-- The raw `Classical.choice` declaration:
`Classical.choice.{u} (α : Sort u) : Nonempty α → α`. -/
def choiceA : ConstantVal :=
  ⟨choiceName, [uN],
    pi "α" (srt u) <|
    piA (.app (cnst nonemptyName [u]) (bv 0)) (bv 1)⟩

/-- Is this checked axiom one of the two recognized standard axioms,
over standardly-shaped stored `Iff` / `Nonempty` families (and the
pinned `Eq` basis)?  A pure predicate so the checker's `axiomDecl`
arm stays a single conditional.

**Why all three of the family's constants are pinned, not just the
type.**  The verification has to *realize* the axiom, and the two
spellings differ: the checker's `propext` takes `Iff a b`, while the
declarative layer's takes the two implications separately
(`ConLeche/Term/Const.lean`).  Bridging them needs the implications
extracted from the `Iff` — and **nothing in the layer turns an
inhabitant of an opaque family into its fields except that family's own
recursor**.  So `Iff.rec` (resp. `Nonempty.rec`) has to be pinned
alongside the type, and `Iff.intro` (resp. `Nonempty.intro`) with it,
because the recursor's minor premise is stated at the constructor.
Only the recursors' *types* are used — never their reduction rules
(DESIGN.md, task #209).  This is the reason the pins are right. -/
def stdAxiomOk (env : Env) (cv : ConstantVal) : Bool :=
  if cv.name = propextName then
    decide (env.find? eqName = some eqA) &&
    (match env.find? iffName with
     | some (.indInfo cvI _) => ConstantVal.matchesPin cvI iffA.toConstantVal
     | _ => false) &&
    (match env.find? iffIntroName with
     | some (.ctorInfo cvIi 2 2) =>
       ConstantVal.matchesPin cvIi iffIntroA.toConstantVal
     | _ => false) &&
    (match env.find? iffRecName with
     | some (.recInfo cvIr 4 4 _ _) =>
       ConstantVal.matchesPin cvIr iffRecA.toConstantVal
     | _ => false) &&
    ConstantVal.matchesPin cv propextA
  else if cv.name = choiceName then
    (match env.find? nonemptyName with
     | some (.indInfo cvN _) =>
       ConstantVal.matchesPin cvN nonemptyA.toConstantVal
     | _ => false) &&
    (match env.find? nonemptyIntroName with
     | some (.ctorInfo cvNi 1 1) =>
       ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal
     | _ => false) &&
    (match env.find? nonemptyRecName with
     | some (.recInfo cvNr 3 3 _ _) =>
       ConstantVal.matchesPin cvNr nonemptyRecA.toConstantVal
     | _ => false) &&
    ConstantVal.matchesPin cv choiceA
  else false

end ConLeche
