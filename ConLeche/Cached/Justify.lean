module

public import ConLeche.Cached.ParsedC
public import ConLeche.Cached.Needs

@[expose] public section

/-!
# Axioms justified by a sidecar

A stream may declare more axioms than the standard ones when a **sidecar** justifies them: a
second stream, checked as usual, whose environment holds a constant of the same name and the
same type.  Holes and axioms are one concept: a definition, theorem or opaque constant whose
value uses `sorryAx` is the axiom of its statement (`sideRecord` makes such a definition the
axiom record, `justifiable` reads the statement of the others).

**The rule** (`justifyWhy`).  An axiom `cv` of the input, at the input's index `fe`, is
justified by the sidecar's index `J` when

* `J` stores a constant of `cv`'s name whose statement is `cv` up to a positional renaming of
  the level parameters (`sameCvUpToLevels`: as many names, neither list with a repeat, the
  sidecar's at the input's names equal to `cv`), of any kind; and
* everything `cv`'s type reads is the same constant in both indices up to the names of its
  level parameters, closed under reads (`coneGo`): the input's copy is the sidecar's
  (`refinesB`: the sidecar's constant, or the statement of a sidecar definition, theorem or
  axiom, each up to a positional renaming of the level parameters where no recursor rule reads
  the constant, `copyB`), with the same projection table, and what that copy reads is again
  shared — its
  type, a definition's value, a recursor's rules, a type former's block members and
  constructors and recursors, a pinned constant's fast-path names, a table's names
  (`entryNeeds`).

So the input's model can take the sidecar model's value for the axiom: the two models agree on
everything its type reads.  The built-in axioms (`propext`, `Classical.choice`, `Quot.sound`
with the pinned `Quot` block, the compiler-trust family) and the placeholder `sorryAx` keep
their own route.  Without a sidecar, every record takes its own check (`checkRecordC` at
`none` is `checkDeclStepC`), so the verdicts of plain checking are unchanged; with one, an
axiom the sidecar does not justify is rejected, with the reason.
-/

namespace ConLeche.Cached

open ConLeche

/-! ## Which records offer a statement -/

/-- **The built-in axioms**: they keep their own check (`checkDeclKindC`'s axiom arm), sidecar
or not. -/
def builtinAxiomName (n : Name) : Bool :=
  n == propextName || n == choiceName || n == quotSoundName || n == sorryAxName ||
    n == trustCompilerName || n == ofReduceNatName || n == ofReduceBoolName

/-- **A definition whose value uses a hole is the axiom of its statement**, where a sidecar may
justify it (`IsModel` reads it so: `Declaration.records`).  A definition at a built-in axiom's
name keeps its own check. -/
def sideRecord : Declaration → Declaration
  | d@(.defnDecl cv v _) =>
    if !builtinAxiomName cv.name && Expr.mentionsAnyConstC [sorryAxName] v then .axiomDecl cv
    else d
  | d => d

/-- **The records a fold checks**: the input's, and with a sidecar every definition whose value
uses a hole as the axiom of its statement (`sideRecord`). -/
def sideRecords : Option Env → Array Declaration → Array Declaration
  | none, ds => ds
  | some _, ds => ds.map sideRecord

/-- **The statement a record offers to a sidecar**: an axiom's, other than a built-in one, and
a theorem's or opaque constant's whose value uses `sorryAx` (a definition's is an axiom by then,
`sideRecord`). -/
def justifiable : Declaration → Option ConstantVal
  | .axiomDecl cv => if builtinAxiomName cv.name then none else some cv
  | .thmDecl cv v | .opaqueDecl cv v =>
    if Expr.mentionsAnyConstC [sorryAxName] v then some cv else none
  | _ => none

/-- **The constant a justified record installs**: a theorem's statement as a theorem, any other
statement as an axiom (`declConstants`). -/
def justifiedInfo (pd : Declaration) (cv : ConstantVal) : ConstantInfo :=
  match pd with
  | .thmDecl .. => .thmInfo cv
  | _ => .axiomInfo cv

/-! ## The comparison -/

/-- Two lists of level-parameter names a renaming relates: as many, neither with a repeat. -/
def levelsRenaming (ps ps' : List Name) : Bool :=
  ps.length == ps'.length && decide ps.Nodup && decide ps'.Nodup

/-- **The input's statement, the sidecar's up to the names of its level parameters**: the same,
or as many names, each list without repeats, and the sidecar's (`cv'`) at the input's names the
input's.  The sidecar's is the one renamed: it is checked, so its level parameters are all among
its names, and the renaming reads it whole. -/
def sameCvUpToLevels (cv cv' : ConstantVal) : Bool :=
  if cv.levelParams == cv'.levelParams then cv.beqP cv'
  else levelsRenaming cv.levelParams cv'.levelParams && (cv'.atLpsC cv.levelParams).beqP cv

/-- A projection table, pointer-first. -/
def _root_.ConLeche.ProjTable.beqP (a b : ProjTable) : Bool :=
  a.structName == b.structName && a.levelParams == b.levelParams &&
    a.numParams == b.numParams && a.ctor == b.ctor && a.numFields == b.numFields &&
    a.bodies == b.bodies

/-- Two lookups' tables, pointer-first. -/
def tableBeqP : Option ProjTable → Option ProjTable → Bool
  | none, none => true
  | some a, some b => a.beqP b
  | _, _ => false

/-- **A constant no recursor rule's equation reads**: neither a recursor nor a constructor (the
model's `RuleFree`).  Only those may be copied at other level-parameter names: ι reads a
recursor's rules and its constructors' records at their own names. -/
def ruleFreeB : ConstantInfo → Bool
  | .recInfo .. => false
  | .ctorInfo .. => false
  | _ => true

/-- **The input's constant `ci` is a copy of the sidecar's `ci'`** (the model's `ConstCopy ci'
ci`): the same, or, for a constant no rule reads (`ruleFreeB`), the sidecar's at the input's
level-parameter names, as many, neither list with a repeat. -/
def copyB (ci' ci : ConstantInfo) : Bool :=
  let ps := ci.toConstantVal.levelParams
  if ps == ci'.toConstantVal.levelParams then ci.beqP ci'
  else ruleFreeB ci' && levelsRenaming ci'.toConstantVal.levelParams ps &&
    (ci'.atLpsC ps).beqP ci

/-- **The input's copy is the sidecar's**: a copy of it (`copyB`: the same, or at other
level-parameter names), or a copy of the statement (an axiom of the same name and type) of a
sidecar definition, theorem or axiom. -/
def refinesB (ci ci' : ConstantInfo) : Bool :=
  copyB ci' ci ||
    match ci with
    | .axiomInfo _ => ci'.isStmtKind && copyB (.axiomInfo ci'.toConstantVal) ci
    | _ => false

/-- **What the justification follows from a constant**: its laws' names (`NeedsSt.const`), a
type former's constructors and its block's recursors (`T.rec` at every member, the names
`blockRecNameSetOk` gives them), and the names of its projection table.  So a block is shared
whole or not at all: every constant of it reads a former, and a former reads the rest. -/
def entryNeeds (findT : Name → Option ProjTable) (ci : ConstantInfo) : Array Name :=
  let x := NeedsSt.const ({}, #[]) ci
  let x := match ci with
    | .indInfo _ caps => x.names (caps.ctors ++ caps.all.map (fun m : Name => m.str "rec"))
    | _ => x
  match findT ci.toConstantVal.name with
  | some t => (x.table t).2
  | none => x.2

/-- **The cone walk**: every name of `work`, and everything it reads, is the same constant in
the input's index (its lookups `find`, `findT`) and the sidecar's `J` (`refinesB`, the same
table); `none`, or the first name that is not.  Each name is compared once (`seen`); `fuel`
bounds the names compared, and the sidecar's name count bounds those (every compared name is
the sidecar's). -/
def coneGo (J : FEnv) (find : Name → Option ConstantInfo) (findT : Name → Option ProjTable)
    (fuel : Nat) (seen : Std.HashSet Name) (work : List Name) : Option Name :=
  match work with
  | [] => none
  | n :: work =>
    if seen.contains n then coneGo J find findT fuel seen work
    else match fuel with
      | 0 => some n
      | fuel + 1 =>
        match find n, J.find? n with
        | some ci, some ci' =>
          if refinesB ci ci' && tableBeqP (findT n) (J.findTable? n) then
            coneGo J find findT fuel (seen.insert n) ((entryNeeds findT ci).toList ++ work)
          else some n
        | _, _ => some n
termination_by (fuel, work.length)

/-- **Is the statement `cv` justified by the sidecar `J`**, at the input's index `fe`: `none`,
or why not. -/
def justifyWhy (J fe : FEnv) (cv : ConstantVal) : Option String :=
  match J.find? cv.name with
  | none => some s!"the sidecar has no constant {cv.name}"
  | some cS =>
    if !sameCvUpToLevels cv cS.toConstantVal then
      some s!"the sidecar's {cv.name} has another type"
    else
      match coneGo J fe.find? fe.findTable? (J.idx.size + 1) {} (needsGo {} #[] cv.type).2.toList with
      | none => none
      | some n => some s!"its type reads {n}, which the sidecar does not declare alike"

/-! ## The check of one record, with a sidecar -/

/-- **The check of one record**, with a sidecar's index `J` or none.  A record that offers a
statement (`justifiable`) takes the justification route where there is a sidecar: the
statement justified (`justifyWhy`), its type checked (`checkConstantValC`), the reserved names'
check, and its constant installed.  Every other record, and every record without a sidecar,
takes its own check (`checkDeclStepC`). -/
def checkRecordC (mode : CheckMode) (pins : List NatOpPinSet) (J : Option FEnv) (fe : FEnv)
    (pd : Declaration) : CheckCM FEnv :=
  match J, justifiable pd with
  | some J, some cv => do
    flushC
    if let some why := justifyWhy J fe cv then
      throw (.invalid s!"{declCLabel pd} is not justified by the sidecar: {why}")
    checkConstantValC mode fe cv
    unless basisNamesOk pd do
      throw (basisNamesError pd)
    pure (fe.push (justifiedInfo pd cv))
  | _, _ => checkDeclStepC mode pins fe pd

end ConLeche.Cached
