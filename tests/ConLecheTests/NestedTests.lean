module

public import ConLeche
/- The `#guard`s below are EVALUATED, so the constants they name have to
be reachable from meta code too; a module needed at both levels is
imported twice. -/
meta import ConLeche

public section

/-!
# Positivity through containers, unit tests (lane NESTPOS)

`nestedBlockPositivity` (`ConLeche/Kernel/Inductives/Positivity.lean`)
is GATED out of the install; the e2e corpus measures it through
`--nested-shadow` (`tests/nested-shadow.sh`).  These guards run the
PURE instantiation (`pureOps`) directly on a hand-built environment —
a container `L α | nil | cons : α → L α → L α`, a container negative in
its parameter `N α | mk : (α → Nat) → N α`, and the member `T : Type`
— so the pure path is exercised too, on each of official's clauses.
-/

namespace ConLecheTests.Nested

open ConLeche

@[expose] def nm (s : String) : Name := .str .anonymous s
@[expose] def ty1 : Expr := .sort (.succ .zero)
@[expose] def pi (d b : Expr) : Expr := .forallE d b default
@[expose] def cL : Expr := .const (nm "L") []
@[expose] def cN : Expr := .const (nm "N") []
@[expose] def cT : Expr := .const (nm "T") []
@[expose] def cNat : Expr := .const (nm "Nat") []

/-- The environment the block's constructors are read at: the two
containers with their constructors, and the member's former. -/
@[expose] def envT : Env := ⟨[
  .indInfo ⟨nm "T", [], ty1⟩ {},
  .ctorInfo ⟨nm "N.mk", [], pi ty1 (pi (pi (.bvar 0) cNat) (.app cN (.bvar 1)))⟩ 1 1,
  .indInfo ⟨nm "N", [], pi ty1 ty1⟩ {},
  .ctorInfo ⟨nm "L.cons", [],
    pi ty1 (pi (.bvar 0) (pi (.app cL (.bvar 1)) (.app cL (.bvar 2))))⟩ 1 2,
  .ctorInfo ⟨nm "L.nil", [], pi ty1 (.app cL (.bvar 0))⟩ 1 0,
  .indInfo ⟨nm "L", [], pi ty1 ty1⟩ {}]⟩

/-- The one-member block `T : Type`, no parameters. -/
@[expose] def ctxT : NestCtx :=
  ⟨[nm "T"], [], 0, [0], [], .succ .zero, envT.find?, envT.consts⟩

/-- `T` with one constructor `T.mk : dom → T`. -/
@[expose] def runT (dom : Expr) : Except CheckError NestedPositivity :=
  nestedBlockPositivity (pureOps .verified) envT ctxT
    [[(⟨nm "T.mk", [], pi dom cT⟩, 1)]]

@[expose] def kindsOf : Except CheckError NestedPositivity → Option (List NestFieldKind)
  | .ok r => some (r.kinds.flatten.flatten)
  | .error _ => none

@[expose] def keysOf : Except CheckError NestedPositivity → Option (List Name)
  | .ok r => some (r.keys.toList.map (·.key.cname))
  | .error _ => none

-- a plain recursive field: no instance located
#guard kindsOf (runT cT) == some [.recursive 0]
#guard keysOf (runT cT) == some []
-- `L T`: one instance, the field nests through it
#guard kindsOf (runT (.app cL cT)) == some [.nested 0 false]
#guard keysOf (runT (.app cL cT)) == some [nm "L"]
-- `Nat → L T`: a reflexive nested field
#guard kindsOf (runT (pi cNat (.app cL cT))) == some [.nested 0 true]
-- `L (L T)`: outermost first, then the instance its constructors reach
#guard keysOf (runT (.app cL (.app cL cT))) == some [nm "L", nm "L"]
-- `N T`: the instantiated constructor `(T → Nat) → …` is negative
#guard runT (.app cN cT) matches .error (.invalid _)
-- `L T → Nat`: a negative occurrence at the field itself
#guard runT (pi (.app cL cT) cNat) matches .error (.invalid _)
-- `(x : Type) → L (x → T) → T`: a container parameter mentioning a
-- field ("parameters cannot contain local variables")
#guard (nestedBlockPositivity (pureOps .verified) envT ctxT
    [[(⟨nm "T.mk", [], pi ty1 (pi (.app cL (pi (.bvar 0) cT)) cT)⟩, 2)]])
  matches .error (.invalid _)

/-! ### The container case at a CONCRETE instantiation, λ included -/

/-- `LF (f : Nat → Type) | mk : f 0 → LF f` — its parameter is a
FUNCTION, so an instantiation at a λ creates a redex the function
reduces with the kernel's whnf (`(fun _ => T) 0 ⇝ T`). -/
@[expose] def cLF : Expr := .const (nm "LF") []
@[expose] def envF : Env := ⟨[
  .indInfo ⟨nm "T", [], ty1⟩ {},
  .ctorInfo ⟨nm "LF.mk", [], pi (pi cNat ty1) (pi (.app (.bvar 0) (.lit (.natVal 0)))
    (.app cLF (.bvar 1)))⟩ 1 1,
  .indInfo ⟨nm "LF", [], pi (pi cNat ty1) ty1⟩ {}] ++ envT.consts⟩
@[expose] def ctxF : NestCtx :=
  ⟨[nm "T"], [], 0, [0], [], .succ .zero, envF.find?, envF.consts⟩
@[expose] def runF (dom : Expr) : Except CheckError NestedPositivity :=
  nestedBlockPositivity (pureOps .verified) envF ctxF [[(⟨nm "T.mk", [], pi dom cT⟩, 1)]]

-- `LF (fun _ => T)`: the λ-pin is an ordinary instantiation
#guard kindsOf (runF (.app cLF (.lam cNat cT default))) == some [.nested 0 false]
-- `LF (fun _ => T → Nat)`: negative AT this instantiation
#guard runF (.app cLF (.lam cNat (pi cT cNat) default)) matches .error (.invalid _)

/-! ### The holes are variables (lane POSPROOF, S1/S2)

The members are abstracted to free variables BEFORE the walk
(unapplied), so a redex that produces a member only after whnf still
reaches the hole; a container's own occurrences in its constructors are
its frame's hole; an instantiation in progress met as a CONSTANT (a
cycle through a mutual container group) restarts its frame with the
group-mates abstracted too (S3). -/

-- `(fun (_ : Type) => T) Nat`: a hole only after β
#guard kindsOf (runT (.app (.lam ty1 cT default) cNat)) == some [.recursive 0]

/-- Mutual containers `A α | mk : B α → A α` and `B α | mk : A α → B α`. -/
@[expose] def cA : Expr := .const (nm "A") []
@[expose] def cB : Expr := .const (nm "B") []
@[expose] def envM : Env := ⟨[
  .indInfo ⟨nm "T", [], ty1⟩ {},
  .ctorInfo ⟨nm "B.mk", [], pi ty1 (pi (.app cA (.bvar 0)) (.app cB (.bvar 1)))⟩ 1 1,
  .ctorInfo ⟨nm "A.mk", [], pi ty1 (pi (.app cB (.bvar 0)) (.app cA (.bvar 1)))⟩ 1 1,
  .indInfo ⟨nm "B", [], pi ty1 ty1⟩ {},
  .indInfo ⟨nm "A", [], pi ty1 ty1⟩ {}]⟩
@[expose] def ctxM : NestCtx :=
  ⟨[nm "T"], [], 0, [0], [], .succ .zero, envM.find?, envM.consts⟩
@[expose] def runM (dom : Expr) : Except CheckError NestedPositivity :=
  nestedBlockPositivity (pureOps .verified) envM ctxM [[(⟨nm "T.mk", [], pi dom cT⟩, 1)]]

-- `A T`: accepted; the cycle `A T → B T → A T` restarts `A T`'s frame
-- with `B` abstracted too, so both are walked in one frame
#guard (runM (.app cA cT)) matches .ok _
#guard keysOf (runM (.app cA cT)) == some [nm "B", nm "A"]

/-- A container whose own constructor uses it at ANOTHER parameter
(`W α | mk : W Nat → W α`, which no installed inductive has): the
frame's hole at other parameters is DECLINED. -/
@[expose] def cW : Expr := .const (nm "W") []
@[expose] def envW : Env := ⟨[
  .indInfo ⟨nm "T", [], ty1⟩ {},
  .ctorInfo ⟨nm "W.mk", [], pi ty1 (pi (.app cW cNat) (.app cW (.bvar 1)))⟩ 1 1,
  .indInfo ⟨nm "W", [], pi ty1 ty1⟩ {}]⟩
@[expose] def ctxW : NestCtx :=
  ⟨[nm "T"], [], 0, [0], [], .succ .zero, envW.find?, envW.consts⟩
#guard (nestedBlockPositivity (pureOps .verified) envW ctxW
    [[(⟨nm "T.mk", [], pi (.app cW cT) cT⟩, 1)]]) matches .error (.notImplemented _)

/-- A cycle through an intermediate container (`F α | mk : L (G α) → F α`,
`G α | mk : F α → G α`) and a three-member cycle (`P → Q → R → P`). -/
@[expose] def cF : Expr := .const (nm "F") []
@[expose] def cG : Expr := .const (nm "G") []
@[expose] def cP : Expr := .const (nm "P") []
@[expose] def cQ : Expr := .const (nm "Q") []
@[expose] def cR : Expr := .const (nm "R") []
@[expose] def envC : Env := ⟨[
  .indInfo ⟨nm "T", [], ty1⟩ {},
  .ctorInfo ⟨nm "R.mk", [], pi ty1 (pi (.app cP (.bvar 0)) (.app cR (.bvar 1)))⟩ 1 1,
  .ctorInfo ⟨nm "Q.mk", [], pi ty1 (pi (.app cR (.bvar 0)) (.app cQ (.bvar 1)))⟩ 1 1,
  .ctorInfo ⟨nm "P.mk", [], pi ty1 (pi (.app cQ (.bvar 0)) (.app cP (.bvar 1)))⟩ 1 1,
  .indInfo ⟨nm "R", [], pi ty1 ty1⟩ {},
  .indInfo ⟨nm "Q", [], pi ty1 ty1⟩ {},
  .indInfo ⟨nm "P", [], pi ty1 ty1⟩ {},
  .ctorInfo ⟨nm "G.mk", [], pi ty1 (pi (.app cF (.bvar 0)) (.app cG (.bvar 1)))⟩ 1 1,
  .ctorInfo ⟨nm "F.mk", [], pi ty1 (pi (.app cL (.app cG (.bvar 0))) (.app cF (.bvar 1)))⟩ 1 1,
  .indInfo ⟨nm "G", [], pi ty1 ty1⟩ {},
  .indInfo ⟨nm "F", [], pi ty1 ty1⟩ {}] ++ envT.consts⟩
@[expose] def ctxC : NestCtx :=
  ⟨[nm "T"], [], 0, [0], [], .succ .zero, envC.find?, envC.consts⟩
@[expose] def runC (dom : Expr) : Except CheckError NestedPositivity :=
  nestedBlockPositivity (pureOps .verified) envC ctxC [[(⟨nm "T.mk", [], pi dom cT⟩, 1)]]

#guard (runC (.app cF cT)) matches .ok _
#guard (runC (.app cP cT)) matches .ok _
#guard (keysOf (runC (.app cP cT))).map (·.length) == some 3

/-! ### U4 and the normal form (lane POSPROOF)

U4: a later field using a recursive field declines — reachable only in
a hand-built environment (`F4 : T → Type` after `T`): on a stream
official accepts, a later field's normal form never mentions a
recursive field (anything applied to it would mention the block, which
official rejects).  The normal form: `nestedBlockPositivity` returns
every constructor's type in official's `check_positivity` form (a
field `Id' T` stored as `T`), the one function's product. -/

@[expose] def cF4 : Expr := .const (nm "F4") []
@[expose] def cId : Expr := .const (nm "Id'") []
@[expose] def envU : Env := ⟨[
  .axiomInfo ⟨nm "F4", [], pi cT ty1⟩,
  .defnInfo ⟨nm "Id'", [], pi ty1 ty1⟩ (.lam ty1 (.bvar 0) default) .abbrev] ++ envT.consts⟩
@[expose] def ctxU : NestCtx :=
  ⟨[nm "T"], [], 0, [0], [], .succ .zero, envU.find?, envU.consts⟩

-- `(t : T) → F4 t → T`: a later field uses the recursive field: DECLINED
#guard (nestedBlockPositivity (pureOps .verified) envU ctxU
    [[(⟨nm "T.mk", [], pi cT (pi (.app cF4 (.bvar 0)) cT)⟩, 2)]])
  matches .error (.notImplemented _)
-- `Id' T → T`: recursive after δβ; stored as `T → T`
#guard (nestedBlockPositivity (pureOps .verified) envU ctxU
    [[(⟨nm "T.mk", [], pi (.app cId cT) cT⟩, 1)]]).toOption.map (·.normals)
  == some [[pi cT cT]]

end ConLecheTests.Nested
