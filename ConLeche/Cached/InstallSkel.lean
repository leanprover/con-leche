module

public import ConLeche.Kernel.Inductives.BlockParts
public import ConLeche.Kernel.BasisA

/-!
# The install skeleton of a record

What a record installs, read off the record alone: the names and the
install-guarded data (`InstallSkel`) of the constants the fold's step
pushes for it, in push order, newest first (`declCSkels`).  The
skeleton forgets everything a core computes, so it is a pure function
of the declaration — no environment, no core.

Two consumers.  The trusted/verified agreement floor
(`ConLeche/Verify/Cached/AgreeFloor.lean`) proves that every accepting
step installs exactly these skeletons.  The parallel install
(`ConLeche/Driver/ParInstall.lean`) predicts from them,
before any record is installed, the name and the counter of every
constant the stream will install: the slots of its frozen base index.
A misprediction is an internal error (the commit's counter or slot
check fails, exit 3), never a verdict; no input reaches it, since every
accepting step installs exactly these skeletons.
-/

@[expose] public section

namespace ConLeche.Cached

open ConLeche

/-! ## The install skeleton

Exactly the data of an installed constant that the *drivers'* install
guards read.  Everything a core computes — the annotated type, the
annotated value, `IndCaps`, a rule's right-hand side and its
`plain`/`inert` fire tag — is deliberately **forgotten**: those are the
class-1/2/3 divergent data, and forgetting them is what keeps the floor
free of core reasoning. -/

/-- The install skeleton of a constant. -/
inductive InstallSkel where
  | ax   (n : Name)
  | defn (n : Name)
  | thm  (n : Name)
  | ind  (n : Name)
  | ctor (n : Name) (numParams numFields : Nat)
  | recr (n : Name) (majorIdx rulePrefix : Nat)
  | proj (n : Name)
  deriving DecidableEq, Repr, Inhabited

/-- The declared name of a skeleton. -/
def skelName : InstallSkel → Name
  | .ax n | .defn n | .thm n | .ind n => n
  | .ctor n _ _ | .recr n _ _ | .proj n => n

/-- The skeleton of an installed constant. -/
def ciSkel : ConstantInfo → InstallSkel
  | .axiomInfo cv => .ax cv.name
  | .defnInfo cv _ _ => .defn cv.name
  | .thmInfo cv => .thm cv.name
  | .indInfo cv _ => .ind cv.name
  | .ctorInfo cv nP nF => .ctor cv.name nP nF
  | .recInfo cv mI rP _ => .recr cv.name mI rP
  | .projInfo tbl => .proj (projTableName tbl.structName)

@[simp] theorem skelName_ciSkel (ci : ConstantInfo) :
    skelName (ciSkel ci) = ci.name := by
  cases ci <;> rfl

/-- The skeleton list of an environment (newest first, as `consts`). -/
def envSkels (env : Env) : List InstallSkel := env.consts.map ciSkel

/-! ## The specification fold

One pure function per driver clause, computing the skeletons the clause
installs from the declaration and the skeletons already installed.  It
is **total**: on inputs the drivers reject it is junk, and `Yields`
makes junk vacuous. -/

/-! The block's member classifiers.  They are *named* (rather than
inlined `match` lambdas as in the driver) for one reason: the driver's
own lambdas compile to per-declaration matcher constants, so a rewrite
with the block-shape equation `split` hands back needs a rigid head to
aim at.  Each is definitionally the driver's lambda, so the bridge is
`exact`. -/

/-! ### The constructors' conses

The install decisions are the block's own; only the *number* of
constants pushed varies with the block (one per constructor). -/

/-- The constructors' conses at the skeleton level (the first
constructor deepest, as `consSumCtors`). -/
def sumCtorSkels (nP : Nat) (cs : List (Name × Nat)) (sk : List InstallSkel) :
    List InstallSkel :=
  cs.foldl (fun acc c => .ctor c.1 nP c.2 :: acc) sk

/-! ### The block install's skeleton

The INSTALL ORDER at k members (the floor's agreement is positional):
the k type formers, then every constructor of every member in block
order, then the k recursors, then one projection table per
structure-like member. -/

/-- The k type formers (member 0 deepest, as `consBlockInds`). -/
def blockIndSkels : List MemberShape → List InstallSkel → List InstallSkel
  | [], sk => sk
  | ms :: rest, sk => blockIndSkels rest (.ind ms.cvT.name :: sk)

/-- Every member's constructors, in block order. -/
def blockCtorSkels (nP : Nat) : List MemberShape → List InstallSkel → List InstallSkel
  | [], sk => sk
  | ms :: rest, sk =>
    blockCtorSkels nP rest (sumCtorSkels nP (ms.ctors.map fun c => (c.1.name, c.2)) sk)

/-- The block's recursors, each with its TARGET member's rules and its
OWN argument sums (`BlockShape.rulePrefixAt`/`recTgtAt`: the recursor
record's — the install conses exactly these). -/
def blockRecSkels (q : BlockShape) : Nat → List RecShape → List InstallSkel →
    List InstallSkel
  | _, [], sk => sk
  | r, rc :: rest, sk =>
    blockRecSkels q (r + 1) rest
      (.recr rc.cvR.name (q.majorIdxAt r) (q.rulePrefixAt r) :: sk)

/-- The projection table of every structure-like member. -/
def blockTableSkels : List MemberShape → List InstallSkel → List InstallSkel
  | [], sk => sk
  | ms :: rest, sk =>
    blockTableSkels rest
      (if ms.ctors.length == 1 && ms.nIdx == 0 then
        .proj (projTableName ms.cvT.name) :: sk else sk)

/-- The uniform install's skeleton. -/
def blockSkels (p : BlockParts) (sk : List InstallSkel) : List InstallSkel :=
  blockTableSkels p.members
    (blockRecSkels p.toBlockShape 0 p.recs
      (blockCtorSkels p.nP p.members (blockIndSkels p.members sk)))

/-- The inductive dispatch: the k-ary skeleton; a
block the recogniser does not read installs nothing (it declines).  The
RECOGNISER decides, and nothing else (task #219), so the skeleton list
needs no environment at all. -/
def indDeclSkels (nP : Nat) (block : List ConstantInfo) (sk : List InstallSkel) :
    List InstallSkel :=
  match blockParts? nP block with
  | some p => blockSkels p sk
  | none => sk

/-- The skeletons one declaration installs. -/
def declCSkels : Declaration → List InstallSkel → List InstallSkel
  | .defnDecl cv _ _, sk => .defn cv.name :: sk
  | .thmDecl cv _, sk => .thm cv.name :: sk
  | .opaqueDecl cv _, sk => .ax cv.name :: sk
  | .axiomDecl cv, sk =>
    -- task #293: `Quot.sound` is the pinned quotient block's own
    -- record and installs nothing of its own, like `sorryAx`
    if cv.name = sorryAxName ∨ cv.name = quotSoundName then sk
    else .ax cv.name :: sk
  | .basisDecl kind, sk =>
    kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
  -- task #293: the quotient package's `type` record installs the
  -- pinned block; its other records are members of that block
  | .quotDecl k _, sk =>
    match k with
    | .type => BasisKind.quotK.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
    | _ => sk
  | .indDecl block nP, sk =>
    -- task #293: a block the fold recognises as a pinned one installs
    -- the pin
    match basisPinHit block with
    | some kind => kind.declsA.foldl (fun acc ci => ciSkel ci :: acc) sk
    | none => indDeclSkels nP block sk

/-- **The names a record installs, in push order** (oldest first): the
parallel install's prediction of the record's slots. -/
def predictSlots (pd : Declaration) : Array Name :=
  ((declCSkels pd []).map skelName).reverse.toArray

end ConLeche.Cached
