module

public import ConLeche.Kernel.Env
public import ConLeche.Kernel.ExprOps

@[expose] public section

/-!
# Fast prop-ness off the head symbol (task #168)

Two pure readers that answer "is this type a proposition?" / "is this
term a proof?" from the **head symbol, the arity and the validated
`pw` annotations** — no inference, no reduction, no memo.  Both are
arities of ONE recursive reader, `typePWAt`.

Prop-ness is invariant under application: `zeronessOf (imax u v) =
zeronessOf v`, so the zero-ness of the sort of the type of `c a⃗` is
that of `c`'s *stored* type at every arity, over-application included.
The datum a head-symbol reader needs is therefore **one `PropWhen` per
constant** — the zero-ness of the sort of its type, read off the
stored (annotated, validated) type and instantiated at the use's
levels by `substPW`.

Both readers are three-valued (`some pw` = the datum, `none` = unknown,
fall back to inference).  The kernel's verdict on a datum is exactly the
slow path's `Level.isEquiv u .zero`: `pw == (.ifAllZero [])` ⟺ the
sort is zero at every valuation.

**Two grades** (task #301).  A λ head carries the answer too: the sort
of `(fun x => b) a⃗` is the sort of `b` (a level never depends on a
term), and an unapplied λ's own datum is the zero-ness of the sort of
its body's type at every arity.  The `beta` flag turns those two
clauses on.  It is `true` for the annotation pass (`annotPwPi`,
`annotPwLam`), whose writes are untrusted and validated by the front
door — so completing the reader there costs only agreement, and buys a
dependent container's pin components a reading instead of an inference
(the copies' data, DESIGN `#### K.7`).  It is `false` for the
proof-irrelevance fast path below, whose "yes" arm is a *licence*: it
is proved head shape by head shape in the model, and a β redex's
denotation needs a law that lane does not have — so the licence keeps
reading the head it can see, exactly as before.

Trust: the readers consume annotations the checker validates
(`(forall-cod)`, `(lam-cod-leaf)`/`(lam-cod-chain)` in `inferBody`;
the stored types were validated at install), so they may only be
*consulted* at the verified modes (`mode.verifiedChecks`) — the trusted core
writes no data and the parser default stays.  The **"definitely not a
proof" arm** (`notProofFast`) needs no model theorem: refusing the
proof-irrelevance shortcut is always sound; its obligation is
kernel-level agreement with the slow path, which the landing census
records (DESIGN.md, task #168).  The **"definitely a proof" arm** is a
squash-regime licence (`ConLeche/Model/Steps/IrrelFast.lean`); both arms
read at `beta := false` for that reason.
-/

namespace ConLeche

namespace Expr

/-- The residual after peeling `k` *syntactic* ∀ binders whose data
are all `.never` (no substitution — the residual may mention the
peeled binders; the readers only look at its head shape).  The
`.never` requirement costs no coverage on validated types — the
binders of a type former `∀ p⃗, Sort u` all carry the datum of a
`succ` codomain sort — and it is what licenses the "yes" arm's
telescope walk without a certificate (`neverChain_of_peel`,
`ConLeche/Model/Steps/IrrelFast.lean`: every slot is in the graph
regime, `io_domain_transfer`). -/
def peelNeverPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ b m => if m.pw.isNever then peelNeverPis k b else none
  | _ + 1, _ => none

/-- The number of arguments of an application spine. -/
def numArgs : Expr → Nat
  | .app f _ => numArgs f + 1
  | _ => 0

end Expr

/-- The zero-ness datum of the sort of a *residual type*: a `Sort u`
residual says the type inhabits `Sort u`.  (A ∀ residual would mean
the applied head is a function, not a type — unreachable on
well-typed input, and unknown here.) -/
def residualPW : Option Expr → Option PropWhen
  | some (.sort u) => some (Level.zeronessOf u)
  | _ => none

/-- **The reader, at an arity** (task #301): the zero-ness datum of the
sort of the type `e a⃗`, where `a⃗` are `n` further arguments — `none`
where the reader declines.  One recursive clause set, structural in the
expression:

* an **application** peels an argument into the arity (the datum of
  `f a a⃗` is the datum of `f` at one more argument);
* a **λ** peels a binder against an argument — the β clause: the sort
  of `(fun x => b) a` is the sort of `b`, because a level never depends
  on a term, so the substitution cannot move it.  Unapplied, a λ is not
  a type and the reader declines (the `n = 0` fall-through);
* a **∀** answers, unapplied, with its own stored datum
  (`(forall-cod)`); applied it would be a function, not a type;
* a **`Sort`** answers, unapplied, `.never` (the sort of a sort is a
  successor); applied it is not a type;
* a **constant** reads its stored type (level-instantiated), an
  **fvar** its declared type, peeling the arity syntactically and
  reading the residual.

`beta` gates the β clause.  It is `true` for the annotation pass's own
read (`annotPwPi`/`annotPwLam`, untrusted writes the front door
validates) and for everything reasoning about that pass; it is `false`
for the proof-irrelevance fast path (`isProofFast`/`notProofFast`),
whose "yes" arm is a squash-regime licence with one model theorem per
head shape (`prf_of_isProofFast`, `ConLeche/Model/Steps/IrrelFast.lean`)
— a redex's denotation is a β law that lane does not have, so the
licence keeps reading the head it can see. -/
def typePWAt (find? : Name → Option ConstantInfo) (beta : Bool) :
    Expr → Nat → Option PropWhen
  | .const I us, n =>
    match find? I with
    | some ci =>
      if ci.isTowerEntry then none else
      let cv := ci.toConstantVal
      if us.length = cv.levelParams.length then
        (residualPW (cv.type.peelNeverPis n)).map
          (Level.substPW cv.levelParams us)
      else none
    | none => none
  | .fvar _ ty, n => residualPW (ty.peelNeverPis n)
  | .app f _, n => typePWAt find? beta f (n + 1)
  | .lam _ b _, n + 1 => if beta then typePWAt find? beta b n else none
  | .forallE _ _ m, 0 => some m.pw
  | .sort _, 0 => some .never
  | _, _ => none

/-- The datum of a type-former application's *head* at `n` arguments
(`typePWAt` at a head; the `.app` clause is unreachable on a
`getAppFn`). -/
def headTypePW (find? : Name → Option ConstantInfo) (beta : Bool)
    (hd : Expr) (n : Nat) : Option PropWhen := typePWAt find? beta hd n

/-- The zero-ness datum of the sort of the *type* `T` ("is `T` a
proposition?"), read off `T`'s head symbol and the annotations: a ∀
carries it on its binder (`(forall-cod)`); a sort's sort is never zero;
a constant- or fvar-headed type-former application reads the head's
stored/declared type, peels the arity syntactically and reads the
residual, level-instantiated for a constant; a λ-headed one (a β redex)
reads through the binder when `beta`.  `none` = unknown. -/
def typeSortPW (find? : Name → Option ConstantInfo) (beta : Bool)
    (T : Expr) : Option PropWhen := typePWAt find? beta T 0

/-- The datum of a term's *head* (any arity): a constant head answers
from its stored type (prop-ness is invariant under application), an
fvar head from its declared type, a λ head from its own datum — the
zero-ness of the sort of the body's type, which is the zero-ness of the
sort of the type of `(fun x => b) a⃗` at every arity, gated on `beta`
as the β clause is; sorts, ∀s and literals are never proofs. -/
def headProofPW (find? : Name → Option ConstantInfo) (beta : Bool) : Expr →
    Option PropWhen
  | .const c us =>
    match find? c with
    | some ci =>
      if ci.isTowerEntry then none else
      let cv := ci.toConstantVal
      if us.length = cv.levelParams.length then
        (typeSortPW find? beta cv.type).map (Level.substPW cv.levelParams us)
      else none
    | none => none
  | .fvar _ ty => typeSortPW find? beta ty
  | .lam _ _ m => if beta then some m.pw else none
  | .sort _ | .forallE .. | .lit _ => some .never
  | _ => none

/-- The zero-ness datum of the sort of the *type* of `a` ("is `a` a
proof?"), read off `a`'s head symbol at any arity: a constant or fvar
head answers from its stored/declared type; an unapplied λ answers from
its own datum (the zero-ness of the sort of the body's type,
`(lam-cod-leaf)`); sorts, ∀s and literals are never proofs.  `none` =
unknown. -/
def proofPW (find? : Name → Option ConstantInfo) (beta : Bool) (a : Expr) :
    Option PropWhen :=
  match a with
  | .lam _ _ m => some m.pw
  | a => headProofPW find? beta a.getAppFn

/-- Is the datum "always zero" — the sort is `Prop` at every
valuation? -/
@[inline] def PropWhen.isProp (pw : PropWhen) : Bool :=
  pw == (.ifAllZero [])

/-- **Definitely not a proof** (the no arm): the datum is known and is
not always-zero. -/
def notProofFast (find? : Name → Option ConstantInfo) (a : Expr) : Bool :=
  match proofPW find? false a with
  | some pw => !pw.isProp
  | none => false

/-- **Definitely a proof** (the yes arm): the datum is known and
always-zero. -/
def isProofFast (find? : Name → Option ConstantInfo) (a : Expr) : Bool :=
  match proofPW find? false a with
  | some pw => pw.isProp
  | none => false

end ConLeche
