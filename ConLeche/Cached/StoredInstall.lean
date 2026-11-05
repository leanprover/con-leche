module

public import ConLeche.Cached.CheckerC

@[expose] public section

/-!
# The stored install of an inductive block (task #431)

The install phase pushes an inductive block **as the input stores
it**: every constant the checked install pushes is read off the block's
records (`storedInstall`), and nothing is generated — no positivity
walk, no recursor generation, no inference; the one reduction is a
def-headed former's telescope.  The block's checked install runs
later, as a job of the check phase
(`DeferredCheck`, `ConLeche/Verify/Cached/Defer.lean`), and compares what
it pushes with what this install pushed, pointer-first
(`ConstantInfo.beqP`, `ProjTable.beqP`); a difference is an internal
error naming the block (exit 3: this reading is wrong, the stream is
not).  So this file is unverified: nothing about the reading is proved,
the job's comparison is what the fold's step is taken from.

Every inductive block is installed this way (task #431 cont. 5): a
block matching a basis pin as the pin's constants, a block the
recogniser does not read as nothing, every other block by the reading
below.  What is read, and from where (the checked install's own
functions on the same inputs wherever one exists):
* the formers: each at its telescope, with `blockCapsAt` at official's
  `is_rec` (`blockRawRec`) and member 0's result sort.  The telescope is
  the stored type where that is a syntactic telescope ending in a sort,
  else (a def-headed former, #195) the reduced telescope official's
  `whnf` loop reads, as the checked install computes it (`storedTele`) —
  the binders the stored recursor shows; the sort is on no record;
* the constructors as declared (`consSumCtorsF`'s records);
* the recursors: each record as it stands (type, K flag, rules), its
  rules' firing mode read off the record alone (`storedFire`);
* the projection tables: the bodies by substitution
  (`structProjBodiesC`), a value in the environment's table map like the
  checked install's.

Where a part cannot be read, it is pushed at its record as declared
(a former, a recursor's rules) or left out (a table): the block is one
the checked install rejects, and its job reports it; the pushes keep the
slots the prediction made for the block filled.
-/

namespace ConLeche

end ConLeche

namespace ConLeche.Cached

open ConLeche

/-! ## The reading -/

variable (mode : CheckMode)

/-- **A former's telescope, as the checked install computes it** (task
#195's `checkSumTeleF`, without its checks): the stored type where it
is a syntactic telescope of `n` binders ending in a sort; else the
telescope official's `whnf` loop reads (`whnfTelescope` at the view,
from a fresh memo), closed — the reduced form the stored recursor's
binders show.  `none` where the loop does not reach a sort (the checked
install rejects the block there). -/
def storedTele (W : FEnv) (cv : ConstantVal) (n : Nat) : Option (ConstantVal × Level) :=
  match cv.type.stripPis n with
  | some (_, .sort s) => some (cv, s)
  | _ =>
    let run : CheckCM (List Expr × Level) := do
      flushC
      whnfTelescope (sharedOpsC mode W) W.env 0 n cv.type
    match run {} with
    | .ok ((bs, s), _) => some ({ cv with type := closeTelescope bs 0 (.sort s) }, s)
    | .error _ => none

/-- The members' formers at their telescopes (`storedTele`), each at its
record as declared where its telescope cannot be read, and member 0's
result sort (the recogniser's placeholder where it cannot be read). -/
def storedFormers (W : FEnv) (p : BlockParts) : List ConstantVal × Level :=
  let ts := p.members.map fun ms => (ms.cvT, storedTele mode W ms.cvT (p.nP + ms.nIdx))
  (ts.map fun (cv, t?) => (t?.map (·.1)).getD cv,
    match ts.head? with
    | some (_, some (_, s)) => s
    | _ => p.resSort)

/-- **A recursor record's rules, read off the group alone**: its rules
as declared (constructor, field count, right-hand side), firing `.plain`
at a member major (`rc.tgt`, the recogniser's reading) and `.nested` at an
outside one: the levels and the arguments of the major's domain, read off
the record's type at its `mI` binders, the record's `mI - rP` trailing
index variables dropped and the rest closed over the rule prefix.  No
lookup: what is outside the block (the container's parameter count) is not
needed, the index count being the record's. -/
def storedFire (p : BlockShape) (rc : RecShape) : Option RecRuleFire :=
  if rc.tgt < p.k then some .plain
  else do
    let (_, body) ← openPisAtFvars rc.mI rc.cvR.type 0
    let .forallE dom _ := body | none
    let .const _ us := dom.getAppFn | none
    let args := dom.getAppArgs
    some (.nested us ((args.take (args.length - (rc.mI - rc.rP))).map (Expr.abstractPrefix rc.rP 0)))

/-- The recursors' records, in the block's order; a recursor whose major
cannot be read keeps its rules as declared (the checked install rejects
the block there). -/
def storedRecs (p : BlockShape) : Nat → List RecShape → List ConstantInfo
  | _, [] => []
  | r, rc :: rest =>
    let rules := match storedFire p rc with
      | some f => rc.rules.map fun rl => { rl with fire := f }
      | none => rc.rules
    .recInfo rc.cvR (p.majorIdxAt r) (p.rulePrefixAt r) rc.isK rules :: storedRecs p (r + 1) rest

/-- The projection tables, member by member in block order, at every
structure-like member (one constructor, no index); none where the
bodies cannot be built (the checked install rejects the block there). -/
def storedTables (p : BlockShape) : List MemberShape → List ProjTable
  | [] => []
  | ms :: rest =>
    let rs := storedTables p rest
    match ms.ctors with
    | [c] =>
      if ms.nIdx == 0 then
        match structProjBodiesC ms.cvT.name p.nP c.2 c.1.type with
        | some bodies =>
          ⟨ms.cvT.name, p.lps, p.nP, c.1.name, c.2, p.resSort, bodies⟩ :: rs
        | none => rs
      else rs
    | _ => rs

/-- **The stored install of a block** at the view `W`: the constants it
pushes (formers, constructors, recursors, in the checked install's push
order) and its tables (in install order).  Total: a block matching a
basis pin pushes the pin's constants, a block the recogniser does not
read pushes nothing (the checked install's pushes and the prediction's
skeleton, `declCSkels`, in both cases), and every other block its
reading, each part at its record as declared where the reading fails —
the blocks the checked install rejects, which its job reports. -/
def storedInstall (W : FEnv) (block : List ConstantInfo) (nP : Nat) :
    List ConstantInfo × List ProjTable :=
  match basisNameHit block with
  | some kind => (List.zipWith withPinCaps kind.decls block, [])
  | none =>
    match blockParts? nP block with
    | none => ([], [])
    | some p₀ =>
      let (cvTs, s0) := storedFormers mode W p₀
      let p := p₀.toBlockShape.withSort s0
      let isRec := blockRawRec p₀
      let formers := (cvTs.zipIdx).map fun (cv, i) => ConstantInfo.indInfo cv (blockCapsAt p i isRec)
      let ctors := p.members.flatMap fun ms =>
        ms.ctors.map fun c => ConstantInfo.ctorInfo c.1 p.nP c.2
      (formers ++ ctors ++ storedRecs p 0 p.recs, storedTables p p.members)

end ConLeche.Cached
