module

public import ConLeche.Kernel.Basis.Names
public import ConLeche.Kernel.Basis.Builder
public import ConLeche.Kernel.Basis.Eq
public import ConLeche.Kernel.Basis.Nat
public import ConLeche.Kernel.Basis.Empty
public import ConLeche.Kernel.Basis.False
public import ConLeche.Kernel.Basis.Quot
public import ConLeche.Kernel.Basis.And
public import ConLeche.Kernel.Canon
public import ConLeche.Kernel.Level

@[expose] public section

/-!
# The pinned basis inductives

The checker pins `Eq`, `Nat`, `Quot`, `Empty` and `False`
natively (hand-written set models), and pins `And` by recognition
alone (below).  The pinned declarations are the toolchain's own — a
block's check compares its records against these (a differing block under
a pinned name is rejected, a differing quotient record declined).  One
module per pinned type under `ConLeche/Kernel/Basis/`, hand-written
against the toolchain's `Init.Prelude` through the small builder in
`Basis/Builder.lean`.

**The stream's constants are what the environment holds**: a pinned block
is installed at the level-parameter names its records declare
(`ConstantInfo.atLps`), and the comparison with the pin (up to those
names) is the block's check, in the check phase.  A quotient record is
compared the same way with its slot's pin and stores that pin at its names
(`quotPinHit`, `quotAt`).
-/

namespace ConLeche

/-- The constants of one basis block, in dependency order. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .emptyK => emptyBasis
  | .falseK => falseBasis
  | .quotK => quotBasis

/-! ## A pin at a stream's level-parameter names

Lean's exporter picks level-parameter names freely (`Eq.{u_1}`), and
the environment holds them as the stream wrote them.  A pinned constant
therefore stands for a family of constants, one per list of names: the
pin with its parameters renamed positionally. -/

/-- A constant's common data at other level-parameter names. -/
def ConstantVal.atLps (cv : ConstantVal) (ps : List Name) : ConstantVal :=
  ⟨cv.name, ps, cv.type.instantiateLevelParams cv.levelParams (ps.map .param)⟩

/-- A firing mode at other level-parameter names. -/
def RecRuleFire.atLps (lps : List Name) (us : List Level) : RecRuleFire → RecRuleFire
  | .levels lvls => .levels (lvls.map (Level.subst lps us))
  | f => f

/-- **A stored constant at other level-parameter names**: its type, its
rules' right-hand sides renamed; nothing else. -/
def ConstantInfo.atLps (ci : ConstantInfo) (ps : List Name) : ConstantInfo :=
  let lps := ci.toConstantVal.levelParams
  let us := ps.map Level.param
  match ci with
  | .axiomInfo cv => .axiomInfo (cv.atLps ps)
  | .defnInfo cv v h => .defnInfo (cv.atLps ps) (v.instantiateLevelParams lps us) h
  | .thmInfo cv => .thmInfo (cv.atLps ps)
  | .indInfo cv caps =>
    .indInfo (cv.atLps ps) caps
  | .ctorInfo cv nP nF => .ctorInfo (cv.atLps ps) nP nF
  | .recInfo cv mI rP isK rules =>
    .recInfo (cv.atLps ps) mI rP isK
      (rules.map fun rl => { rl with
        rhs := rl.rhs.instantiateLevelParams lps us
        fire := rl.fire.atLps lps us })

/-- A record against the pin at the record's own names: what the record
writes.  An inductive record has no capabilities to compare. -/
def pinAgrees : ConstantInfo → ConstantInfo → Bool
  | .indInfo v _, .indInfo v' _ => v.beqP v'
  | c, c' => c.beqP c'

/-- **Is the record the pin, up to its level-parameter names?**  Distinct
names, as many as the pin's. -/
def pinCopyOk (ci pin : ConstantInfo) : Bool :=
  let ps := ci.toConstantVal.levelParams
  Name.nodup ps && ps.length == pin.toConstantVal.levelParams.length &&
    pinAgrees ci (pin.atLps ps)

/-- **What a recursor's rule reads off its constructor's parameters**, by
name (`recFireComparands`' `.plain` arm): the constructor's parameters
at the recursor's names.  The stream's names must link the two the way
the pin's do: this is the constant part of that comparison. -/
def pinLinkOk (R Rp : List Name) (C Cp : List Name) : Bool :=
  C.map Level.param == Cp.map fun p => Level.subst Rp (R.map Level.param) (.param p)

/-- The constant of a list by name. -/
def constNamed? (cs : List ConstantInfo) (n : Name) : Option ConstantInfo :=
  cs.find? fun c => c.name == n

/-- The stream's recursor links its rules' constructors as the pin's
does (`pinLinkOk`), and a constructor carries its former's names. -/
def blockLinksOk (block pins : List ConstantInfo) : Bool :=
  let former := (block.head?.map (·.toConstantVal.levelParams)).getD []
  (List.zip block pins).all fun (c, p) =>
    match c, p with
    | .ctorInfo cv _ _, _ => cv.levelParams == former
    | .recInfo cv .., .recInfo cvp _ _ _ rules =>
      rules.all fun rl =>
        match constNamed? block rl.ctor, constNamed? pins rl.ctor with
        | some C, some Cp =>
          pinLinkOk cv.levelParams cvp.levelParams C.toConstantVal.levelParams
            Cp.toConstantVal.levelParams
        | _, _ => false
    | _, _ => true

/-- **The block's comparison with its pin** (the check phase's). -/
def pinListOk (block pins : List ConstantInfo) : Bool :=
  listBeqBy pinCopyOk block pins && blockLinksOk block pins

/-! ## Recognising a pinned block in a stream record

The decoder emits the file's records and nothing else, so a stream's
`Nat` block reaches the fold as an ordinary `indDecl`.  The NAMES decide
that it is the pinned block's record (a function of the group);
comparing it with the pin is the block's check.  A block with a pinned
block's names that is not the pin is invalid input; a quotient record
that does not match its pin is a decline. -/

/-- **The pinned block a record declares**, by its members' names. -/
def basisNameHit (block : List ConstantInfo) : Option BasisKind :=
  [BasisKind.eqK, .natK, .emptyK, .falseK].find? fun k =>
    k.decls.map (·.name) == block.map (·.name)

/-- **What a pinned block's check installs**: each pin at the names its
record declares. -/
def BasisKind.atBlock (kind : BasisKind) (block : List ConstantInfo) : List ConstantInfo :=
  List.zipWith (fun pin c => pin.atLps c.toConstantVal.levelParams) kind.decls block

/-- A record with the capabilities its pin carries (a record has none):
what the install pushes without looking at anything but the group. -/
def withPinCaps (pin c : ConstantInfo) : ConstantInfo :=
  match pin.atLps c.toConstantVal.levelParams, c with
  | .indInfo _ caps, .indInfo cv _ => .indInfo cv caps
  | _, _ => c

/-- The pinned quotient package's constant at a slot. -/
def quotPin (k : QuotKind) : ConstantInfo :=
  BasisKind.quotK.decls.getD k.slot (.axiomInfo default)

/-- **What a quotient record stores**: its slot's pin at the names it
declares. -/
def quotAt (k : QuotKind) (cv : ConstantVal) : ConstantInfo :=
  (quotPin k).atLps cv.levelParams

/-- **The quotient-pin match**: the record is the pinned package's
constant at the slot it declares itself at, up to its level-parameter
names: distinct, as many as the pin's. -/
def quotPinHit (k : QuotKind) (cv : ConstantVal) : Bool :=
  Name.nodup cv.levelParams &&
    cv.levelParams.length == (quotPin k).toConstantVal.levelParams.length &&
    cv.beqP ((quotPin k).toConstantVal.atLps cv.levelParams)

/-- **What a quotient record's slot needs stored before it**: the
constants its type mentions.  A reserved name is stored only as a copy of
its pin, at whatever names, and references are positional. -/
def quotPredsOk (find? : Name → Option ConstantInfo) (k : QuotKind) : Bool :=
  let hasEq := (find? eqName).isSome
  let hasQ := (find? quotName).isSome
  let hasM := (find? quotMkName).isSome
  match k with
  | .type => hasEq
  | .ctor => hasQ
  | .lift => hasEq && hasQ && hasM
  | .ind => hasQ && hasM
  | .sound => hasEq && hasQ && hasM

/-! ## The pinned `And`

`And` is recognised, not installed from literals
(`ConLeche/Kernel/Basis/And.lean`): the block that matches the pin goes
through the ordinary inductive installer.  What the pin adds is a
REJECT — a record that declares `And`, `And.intro` or `And.rec` and is
not the pinned block is invalid input, as a basis redefinition is — so
that in every accepted environment the name `And` is the toolchain's
`And` and the stuck-proof rescue that serves it (`majorToCtor`'s `And`
branch) is available.  The fold asks this of every record before its
dispatch (`installDeclStep`, `ConLeche/Cached/Installed.lean`). -/

/-- **The `And` pin's test**: the record declares none of the pinned
`And` block's names, or it IS that block — two parameters, and equal
to `andPin` up to `ConstantInfo.canon`. -/
def andPinOk : Declaration → Bool
  | .indDecl block nP =>
    !(block.any fun c => andPinNames.contains c.name) ||
      (nP == 2 && canonEqList block andPin)
  | .axiomDecl cv | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv ..
  | .quotDecl _ cv => !andPinNames.contains cv.name

end ConLeche
