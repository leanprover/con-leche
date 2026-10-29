module

public import ConLeche.Cached.CoreC

/-!
# The stored recursor rules agree with the generated ones (task #386)

The installer GENERATES every recursor of an inductive block — its type
and its rules (`genRecCheck`, `ConLeche/Kernel/Inductives/GenRec.lean`)
— and installs the generated ones; the record's rules take no part in
the install.  A tool that loads the input as it is (Lean's kernel on an
`.olean`) runs the record's rules, and official's replay rejects a
record whose recursor is not the one it generates ("Invalid
recursor").  So after a successful install, every recursor record of an
inductive block must carry rules that agree with the installed ones
(`recRulesAgree`):

* as many rules, for the same constructors in the same order, each with
  the same field count;
* each right-hand side closed, its level parameters the record's, and
  definitionally equal to the generated one (the checker's own
  `isDefEq`, after a full-grade inference of the stored body) under the
  rule's telescope — the parameters, motives, minor premises and fields
  — opened with the GENERATED rule's binder types: an iota step applies
  the rule to the recursor's arguments and β-reduces, so the domains of
  those leading binders are never read.  A right-hand side equal to the
  generated one but for those domains is accepted without the defeq
  call (`rhsSameUnder`, the fast path every well-formed file takes).

The check is a pure guard: it reads the installed environment and the
records and adds rejections only; nothing it computes is installed.
It runs at the environment view that ends with the block (a later
constant is not visible to the comparison).  A comparison that cannot
be decided (a resource limit) is a decline, as everywhere in the
checker.
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche.Cached

/-- The fast path: `a` and `b` equal after `n` leading λ-binders on
each, whose domains are not compared. -/
def rhsSameUnder : Nat → Expr → Expr → Bool
  | n + 1, .lam _ a, .lam _ b => rhsSameUnder n a b
  | _, a, b => a == b

/-- The rule's telescope opened: `n` leading binders of the generated
right-hand side `g`, from local `d` on, each a local of the generated
binder's type; the stored right-hand side `s` instantiated (or, short of
a λ, applied) at the same locals.  Returns the depth reached and the
two bodies. -/
def openRule : Nat → Nat → Expr → Expr → Nat × Expr × Expr
  | n + 1, d, s, .lam ty gb =>
    let fv := Expr.fvar d ty
    let s' := match s with
      | .lam _ sb => sb.instantiate1 fv
      | s => .app s fv
    openRule n (d + 1) s' (gb.instantiate1 fv)
  | _, d, s, g => (d, s, g)

/-- The message prefix of a failed comparison: `what` is the step
(the stored right-hand side's inference, or the comparison). -/
def ruleErr (rec ctor : Name) (what : String) : CheckError → CheckError
  | .invalid m => .invalid s!"the recursor {rec}'s rule for {ctor}: {what}: {m}"
  | .notImplemented m => .notImplemented s!"the recursor {rec}'s rule for {ctor}: {what}: {m}"
  | .internal m => .internal s!"the recursor {rec}'s rule for {ctor}: {what}: {m}"

/-- One stored rule `a` against the generated `b` (already read at the
record's level parameters `lps`), at the view `fe`; `pre` is the
recursor's rule prefix (parameters, motives, minor premises). -/
def ruleAgrees (mode : CheckMode) (fe : FEnv) (rec : Name) (lps : List Name) (pre : Nat)
    (a b : RecRule) : Except CheckError Unit := do
  if a.ctor != b.ctor || a.nfields != b.nfields then
    throw (.invalid s!"the recursor {rec}'s rule for {a.ctor} is not the generated one's \
      (constructor {b.ctor}, {b.nfields} fields)")
  let n := pre + b.nfields
  if rhsSameUnder n a.rhs b.rhs then return
  unless Expr.looseBVarsBounded 0 a.rhs && !Expr.hasFvar a.rhs do
    throw (.invalid s!"the recursor {rec}'s rule for {a.ctor} has a right-hand side that is \
      not closed")
  unless Expr.allLevelParamsDefinedC lps a.rhs do
    throw (.invalid s!"the recursor {rec}'s rule for {a.ctor} has an undeclared universe \
      parameter")
  let (d, s, g) := openRule n 0 a.rhs b.rhs
  let r := coreKnotI mode fe checkFuel
  -- the stored body type-checks (the full grade) under the telescope …
  let st ← match r.infer d s {} with
    | .error e => throw (ruleErr rec a.ctor "the stored right-hand side does not type-check" e)
    | .ok (_, st) => pure st
  -- … and is definitionally equal to the generated one
  match r.defeq d s g st with
  | .error e => throw (ruleErr rec a.ctor "comparing with the generated right-hand side" e)
  | .ok (true, _) => pure ()
  | .ok (false, _) =>
    throw (.invalid s!"the recursor {rec}'s rule for {a.ctor} has a right-hand side that is \
      not definitionally equal to the generated one")

/-- One recursor record against the installed (generated) recursor of
its name, at the view `fe`. -/
def recAgrees (mode : CheckMode) (fe : FEnv) (cv : ConstantVal) (rules : List RecRule) :
    Except CheckError Unit :=
  match fe.find? cv.name with
  | some (.recInfo cvG _ pre gen) => do
    -- a pinned basis block is installed under the pin's own level
    -- parameter names: the generated rules are read at the record's
    let gen := if cvG.levelParams == cv.levelParams then gen else
      let lv := cv.levelParams.map Level.param
      gen.map fun r => { r with rhs := r.rhs.instantiateLevelParams cvG.levelParams lv }
    if rules.length != gen.length then
      throw (.invalid s!"the recursor {cv.name} carries {rules.length} rules, the generated \
        one {gen.length}")
    for (a, b) in rules.zip gen do
      ruleAgrees mode fe cv.name cv.levelParams pre a b
  | _ => throw (.internal s!"the recursor {cv.name} is not installed as a recursor")

/-- The view that ends with the block's recursors: below the largest
install counter among them (the whole environment if one of them is not
in the index). -/
def blockView (fe : FEnv) (block : List ConstantInfo) : FEnv :=
  let ks := block.filterMap fun ci => match ci with
    | .recInfo cv _ _ _ => some ((fe.idx[cv.name]?).map (·.1))
    | _ => none
  if ks.all Option.isSome then
    match ks.filterMap id with
    | [] => fe
    | k :: rest => fe.restrictTo (rest.foldl max k + 1)
  else fe

/-- **The stored recursor rules agree with the generated ones** (task
#386; the module docstring).  `fe` is the environment the install of
`ds` produced; the error carries the position of the first record in
`ds` that disagrees. -/
def recRulesAgree (mode : CheckMode) (fe : FEnv) (ds : Array Declaration) :
    Except (CheckError × Nat) Unit := do
  for h : i in [0:ds.size] do
    match ds[i] with
    | .indDecl block _ =>
      let feB := blockView fe block
      for ci in block do
        match ci with
        | .recInfo cv _ _ rules =>
          match recAgrees mode feB cv rules with
          | .ok () => pure ()
          | .error e => throw (e, i)
        | _ => pure ()
    | _ => pure ()

end ConLeche.Driver
