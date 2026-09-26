module

public import ConLeche.Kernel.Inductives.Positivity

@[expose] public section

/-!
# The k-ary block: the record and the recogniser
(the uniform inductive route)

`BlockParts` is the shape a block on the fixpoint route is read into,
at ANY number `k` of mutually recursive members: the members with
their own index counts, constructors and recursors, the shared
parameter count, the shared elimination level and result sort.  Its
one-member reading `BlockParts.toNative` (`NativeParts`,
`ConLeche/Conformance/RecGen.lean`) is used only by the reject-only
conformance check (`checkBlockRecConform`).

**The route takes every block the recogniser reads**, at any number
of members, nested blocks included; a block `blockParts?` does not
read declines at the dispatch (`checkShapeless`).

The three pieces:

* **the record** (`MemberShape`/`BlockShape`/`BlockParts`) with the
  `complete`/`withSort` projections the proofs' `generalize` dance
  needs;
* **the recogniser** (`blockSplit`, `blockCounts?`, `blockShape?`,
  `blockParts?`) — official's `add_inductive` reads the type formers,
  the constructors and the parameter count and GENERATES the recursors,
  so nothing the recursor records claim is a condition of recognition:
  their structural pin travels with the record (`blockRecPinOk`,
  `blockRecLpsOk`) and the install throws on it (task #220's
  arrangement, at k members);
* **positivity** lives in its own module
  (`ConLeche/Kernel/Inductives/Positivity.lean`) and runs at
  install (`checkBlockPositivity`); the record carries no field kinds.

The constructors are assigned to members by their result head
(`ctorMember?`), official's own reading: a constructor belongs to the
type its result names.  A head that is no member of the block leaves
the constructor in member 0's group, where the install rejects it with
official's message ("invalid return type", `structCtorResidOk`); a
grouping that is not monotone in block order contradicts the generated
recursors' minor order and is rejected by the recursor pin
(`blockRecPinOk`'s last conjunct).
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

/-! ## The record -/

/-- One member of a block: its type former, its own index count and
its constructors (member-local, in block order).

**The member carries no recursor**: recursor NAMES are the stream's
business, a member may carry any
number of them (zero included), and a recursor is assigned to its
member by its MAJOR premise, not by its name — so the recursors are a
list of their own (`RecShape`, `BlockShape.recs`). -/
structure MemberShape where
  /-- the member's type former -/
  cvT : ConstantVal
  /-- the member's index count -/
  nIdx : Nat
  /-- the member's constructors in block order, each with its field count -/
  ctors : List (ConstantVal × Nat)
  deriving Repr, Inhabited

/-- **One recursor of a block, as the stream carries it**.  Its NAME is the
stream's business — nothing here is
compared with `T.rec` — and what makes it a recursor of member `tgt`
is its MAJOR premise, read off its type at the record's own `mI`. -/
structure RecShape where
  /-- the recursor's constant (name, level parameters, type) -/
  cvR : ConstantVal
  /-- **the recursor record's own rule prefix** (`recInfo`'s `rP`): the
  number of binders the recursor's type has before its INDEX binders —
  the parameters, then the stretch official fills with the motives and
  the minor premises, which the uniform route never looks inside.  Read
  off the record: a motive is a parameter like any other.  A rule's λ-prefix
  is `rP + nF`. -/
  rP : Nat
  /-- **the recursor record's own major-premise index** (`recInfo`'s
  `mI`): the binder its MAJOR sits at, read off the record too. -/
  mI : Nat
  /-- **the member its MAJOR names** (`recTargetOf`, read syntactically
  by the recogniser).  `k` — no member at all — is the nested block's
  auxiliary recursor, whose major is a CONTAINER: the recursor stage
  resolves it as an outside major (`targetMajorOf`). -/
  tgt : Nat
  /-- the recursor's rules' right-hand sides as exported, in the
  constructor order of its target member -/
  rhss : List Expr
  deriving Repr, Inhabited

/-- The pieces of a recognised block at any number of members: the
members, the recursors, the SHARED parameter count, elimination level
parameter and result sort (official requires the parameters to agree
definitionally and the result sorts to be equivalent —
`check_inductive_types`, and one elimination level for all the
recursors, which is D-d). -/
structure BlockShape where
  /-- the members in block order -/
  members : List MemberShape
  /-- the block's recursors, in the order the stream exports them (any
  number, assigned to their members by their majors) -/
  recs : List RecShape
  /-- the shared parameter count -/
  nP : Nat
  /-- the recursors' fresh elimination level parameter (`large` only;
  `.anonymous` for a small eliminator) -/
  elim : Name
  /-- the result sort (member 0's; the others are `Level.isEquiv` to it) -/
  resSort : Level
  /-- large eliminator (a fresh elimination level parameter in front) -/
  large : Bool
  /-- the result sort is provably `Prop` -/
  isProp : Bool
  deriving Repr, Inhabited

/-- The constructors of a list of members, counted (a recursion, not a
`foldl`, so that ONE member's count is `n + 0` and reduces). -/
def numCtorsOf : List MemberShape → Nat
  | [] => 0
  | ms :: rest => ms.ctors.length + numCtorsOf rest

namespace BlockShape

/-- The number of members. -/
def k (p : BlockShape) : Nat := p.members.length
/-- The number of constructors of the whole block. -/
def numCtors (p : BlockShape) : Nat := numCtorsOf p.members
/-- The constructors of the members before `m`. -/
def offs (p : BlockShape) (m : Nat) : Nat := numCtorsOf (p.members.take m)
/-- The members' names, in block order (the positivity walk's `names`). -/
def memberNames (p : BlockShape) : List Name := p.members.map (·.cvT.name)
/-- The members' index counts, in block order. -/
def nIdxs (p : BlockShape) : List Nat := p.members.map (·.nIdx)
/-- The block's level parameters (member 0's; every member carries
them — the recogniser checks it). -/
def lps (p : BlockShape) : List Name :=
  (p.members.head?.map (·.cvT.levelParams)).getD []
/-- The constructors of the whole block, in block order. -/
def allCtors (p : BlockShape) : List (ConstantVal × Nat) :=
  (p.members.map (·.ctors)).flatten
/-- **The member recursor `r` belongs to, as the INSTALL uses it.**

It is the target the recogniser read off the MAJOR (`RecShape.tgt`). -/
def recTgtAt (p : BlockShape) (r : Nat) : Nat :=
  (p.recs.getD r default).tgt

/-- **Recursor `r`'s rule prefix, as the INSTALL uses it.**

It is the RECORD's (`RecShape.rP`): the motive-free check never
derives the sum, it reads it and requires only `nP ≤ rP` (no
motive-count floor). -/
def rulePrefixAt (p : BlockShape) (r : Nat) : Nat :=
  (p.recs.getD r default).rP

/-- Recursor `r`'s major-premise index, at the same reading — the
RECORD's (`RecShape.mI`). -/
def majorIdxAt (p : BlockShape) (r : Nat) : Nat :=
  (p.recs.getD r default).mI

/-- The record completed with the former stage's result sort (task
#195 at k members: the sort is read off member 0's checked telescope,
the other members' being `Level.isEquiv` to it). -/
def withSort (p : BlockShape) (s : Level) : BlockShape :=
  { p with resSort := s, isProp := Level.isEquiv s .zero == some true }

@[simp] theorem withSort_members (p : BlockShape) (s : Level) :
    (p.withSort s).members = p.members := rfl
@[simp] theorem withSort_recs (p : BlockShape) (s : Level) :
    (p.withSort s).recs = p.recs := rfl
@[simp] theorem withSort_nP (p : BlockShape) (s : Level) : (p.withSort s).nP = p.nP := rfl
@[simp] theorem withSort_elim (p : BlockShape) (s : Level) : (p.withSort s).elim = p.elim := rfl
@[simp] theorem withSort_resSort (p : BlockShape) (s : Level) :
    (p.withSort s).resSort = s := rfl
@[simp] theorem withSort_large (p : BlockShape) (s : Level) :
    (p.withSort s).large = p.large := rfl
@[simp] theorem withSort_isProp (p : BlockShape) (s : Level) :
    (p.withSort s).isProp = (Level.isEquiv s .zero == some true) := rfl
@[simp] theorem withSort_k (p : BlockShape) (s : Level) : (p.withSort s).k = p.k := rfl
@[simp] theorem withSort_numCtors (p : BlockShape) (s : Level) :
    (p.withSort s).numCtors = p.numCtors := rfl
@[simp] theorem withSort_memberNames (p : BlockShape) (s : Level) :
    (p.withSort s).memberNames = p.memberNames := rfl
@[simp] theorem withSort_nIdxs (p : BlockShape) (s : Level) :
    (p.withSort s).nIdxs = p.nIdxs := rfl
@[simp] theorem withSort_lps (p : BlockShape) (s : Level) : (p.withSort s).lps = p.lps := rfl
@[simp] theorem withSort_allCtors (p : BlockShape) (s : Level) :
    (p.withSort s).allCtors = p.allCtors := rfl

end BlockShape

/-- The pieces of a recognised block: its shape and the recursor
records' structural pin. -/
structure BlockParts extends BlockShape where
  /-- **the stream's recursor records passed the structural pin**
  (task #220 at k members): each recursor's two argument sums, its rule
  count, each rule's constructor and field count, and the constructors'
  grouping being monotone in block order (the generated minors are in
  block order, so a permuted export cannot match them).  The recogniser
  records the verdict; the recursor stage THROWS on `false`. -/
  recPinned : Bool
  deriving Repr, Inhabited

/-- **The record completed by the formers' stage**: the shape the
formers' run returned (its result sort read through `whnf`) with the
recogniser's pin. -/
def BlockParts.complete (p₀ : BlockParts) (p₁ : BlockShape) : BlockParts :=
  ⟨p₁, p₀.recPinned⟩

@[simp] theorem BlockParts.complete_toBlockShape (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).toBlockShape = p₁ := rfl
@[simp] theorem BlockParts.complete_recPinned (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).recPinned = p₀.recPinned := rfl
@[simp] theorem BlockParts.complete_members (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).members = p₁.members := rfl
@[simp] theorem BlockParts.complete_recs (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).recs = p₁.recs := rfl
@[simp] theorem BlockParts.complete_nP (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).nP = p₁.nP := rfl
@[simp] theorem BlockParts.complete_elim (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).elim = p₁.elim := rfl
@[simp] theorem BlockParts.complete_resSort (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).resSort = p₁.resSort := rfl
@[simp] theorem BlockParts.complete_large (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).large = p₁.large := rfl
@[simp] theorem BlockParts.complete_isProp (p₀ : BlockParts) (p₁ : BlockShape) :
    (p₀.complete p₁).isProp = p₁.isProp := rfl

/-! ## Recognition

The block's members after the type formers: the constructors, then the
closing recursors.  Nothing is refused by COUNT here: a
block with any number of formers splits. -/

/-- The closing recursors. -/
def blockSplitRecs : List ConstantInfo →
    Option (List (ConstantVal × Nat × Nat × List RecRule))
  | [] => some []
  | .recInfo cvR mI rP rules :: rest =>
    (blockSplitRecs rest).map fun rs => (cvR, mI, rP, rules) :: rs
  | _ => none

/-- The constructors, then the recursors. -/
def blockSplitCtors : List ConstantInfo →
    Option (List (ConstantVal × Nat × Nat) × List (ConstantVal × Nat × Nat × List RecRule))
  | .ctorInfo cvC nP nF :: rest =>
    (blockSplitCtors rest).map fun q => ((cvC, nP, nF) :: q.1, q.2)
  | rest => (blockSplitRecs rest).map fun rs => ([], rs)

/-- The type formers, the constructors and the recursors. -/
def blockSplit : List ConstantInfo →
    Option (List ConstantVal × List (ConstantVal × Nat × Nat) ×
      List (ConstantVal × Nat × Nat × List RecRule))
  | .indInfo cvT _ :: rest =>
    (blockSplit rest).map fun q => (cvT :: q.1, q.2)
  | rest => (blockSplitCtors rest).map fun q => ([], q.1, q.2)

/-- **The member a recursor's MAJOR names** (recursor NAMES are the
stream's business, and what makes a recursor this member's is its major
premise).

Strip the `mI` binders the record claims off the stored type; the next
binder is the MAJOR, and its domain's head constant is read against
the block's member names, at the recursor's first `nP` binders (the
block's parameters).  `names.length` — no member — when the type does
not have those binders, when the major's domain heads something else, a
constant outside the block (a NESTED block's auxiliary recursors: their
majors are containers), or a member at other parameters (an instance
of the block as a class of its own, PRIMREC). -/
def recTargetOf (names : List Name) (nP mI : Nat) (ty : Expr) : Nat :=
  match ty.stripPis mI with
  | some (_, .forallE dom _ _) =>
    (match dom.getAppFn with
     | .const n _ =>
       if dom.getAppArgs.take nP == (List.range nP).map (fun k => Expr.bvar (mI - 1 - k)) then
         names.findIdx? (· == n)
       else none
     | _ => none).getD names.length
  | _ => names.length

/-- **One member's parameter and index counts**, read as official
reads them: `nP` is the count the
DECLARATION carries and `nIdx` is what is left of the member's
Π-telescope once those binders are peeled.  At a former declared AT A
DEFINITION (task #195) the syntactic telescope is not the one official
walks and a recursor record's argument sums are the only reading
available — with `nP + k + N` the rule prefix at k members; `r` is
then the sums of a recursor whose MAJOR names this member, and `none`
when there is none.  `nR` is the block's recursor count: at a NESTED
block (`nR > k`, official's auxiliary recursors ride along) the prefix
also carries one motive per auxiliary recursor and the auxiliary
constructors' minors, whose number the block does not record — there
the prefix is only bounded below (the former's own
telescope is checked by the install's whnf loop at the count read
here, so a wrong claim is rejected there). -/
def blockCounts? (nPd k nC nR : Nat) (cvT : ConstantVal) (r : Option (Nat × Nat)) :
    Option (Nat × Nat) :=
  match cvT.type.piBinders with
  | (bs, .sort _) => if nPd ≤ bs.length then some (nPd, bs.length - nPd) else none
  | _ =>
    match r with
    | none => none
    | some (mI, rP) =>
      if rP < nC + k || mI < rP then none
      else if rP - (nC + k) == nPd then some (nPd, mI - rP)
      else if k < nR && nPd + nR + nC ≤ rP then some (nPd, mI - rP)
      else none

/-- The member a constructor belongs to: the one its RESULT names
(official's own reading — `check_constructors` checks each constructor
against the type its result heads). -/
def ctorMember? (names : List Name) (lps : List Name) (nP : Nat)
    (c : ConstantVal × Nat) : Option Nat :=
  match c.1.type.stripPis (nP + c.2) with
  | some (_, cbody) => memberIdxAt? names (lps.map .param) cbody.getAppFn
  | none => none

/-- **The constructors grouped by member**, in block order.

At ONE member the assignment is forced and nothing is read: the
constructor's result head is official's "invalid return type" check,
thrown by the constructor stage (`structCtorResidOk`,
`ConLeche/Kernel/Inductives/SumInstall.lean`).  At two or more members the
group is read off the result head; a
constructor whose head is no member of the block stays in NO group and
is caught by the recursor pin's grouping conjunct
(`blockRecPinOk`) — a `.invalid`, as official's is. -/
def blockGroups (names : List Name) (lps : List Name) (nP k : Nat)
    (cs : List (ConstantVal × Nat)) : List (List (ConstantVal × Nat)) :=
  if k == 1 then [cs]
  else (List.range k).map fun m => cs.filter fun c => ctorMember? names lps nP c == some m

/-- **The recursor records' structural pin** (task #220 at k members),
thrown at the recursor stage: every recursor's two argument sums, one
rule per constructor of ITS member in block order, each rule naming its
constructor with its field count — and the grouping itself, which must
exhaust the block's constructors in block order (the generated minors
are the block's constructors in block order, so a grouping that is not
monotone cannot match any generated recursor). -/
def blockRecPinOk (p : BlockShape) (block : List ConstantInfo) : Bool :=
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    cvTs.length == p.k && rs.length == p.recs.length &&
    (p.allCtors.map (·.1.name) == cs.map (·.1.name)) &&
    (List.range p.recs.length).all fun r =>
      match rs[r]?, p.members[p.recTgtAt r]? with
      | some (_, _mI, _rP, rules), some ms =>
        rules.length == ms.ctors.length &&
        (List.range ms.ctors.length).all fun j =>
          match rules[j]?, cs[p.offs (p.recTgtAt r) + j]? with
          | some rule, some (cvC, _, nF) => rule.ctor == cvC.name && rule.nfields == nF
          | _, _ => false
      | _, _ => false
  | none => false

/-- **The recursor records' level-parameter pin** (task #220 at k
members, per RECURSOR): official
generates ONE elimination level parameter for the whole block, so
every recursor carries the block's own level parameters with that one
in front at the large eliminator. -/
def blockRecLpsOk (p : BlockShape) : Bool :=
  p.recs.all fun rc =>
    if p.large then rc.cvR.levelParams == p.elim :: p.lps
    else rc.cvR.levelParams == p.lps

/-- **The recursor names, as a SET** ("no red tutorial tests — a
simple recursor-NAME conformance check").  A block's recursors must
carry exactly the names official generates for it, `T_m.rec` at every
member, each once — as a SET: WHICH recursor carries which name is
not checked here, and never is, because a recursor is assigned to its
member by its MAJOR premise (`RecShape.tgt`) and by nothing else.

The member names are pairwise distinct (each former passed
`checkConstantVal` in the environment the previous ones were consed
into), so mutual containment at equal length is set equality and a
repeated recursor name cannot slip through: a duplicate leaves some
`T_m.rec` unmatched.

This check is a pure accept-shrinker — the verified route and the
model never read a recursor's name — and it is what keeps a stream
from declaring a second eliminator on one member, or an eliminator
under a name the stream's own definitions then use for something
else. -/
def blockRecNameSetOk (p : BlockShape) : Bool :=
  let want := p.members.map fun ms => ms.cvT.name.str "rec"
  let got := p.recs.map fun rc => rc.cvR.name
  got.length == want.length &&
    want.all (fun n => got.contains n) && got.all (fun n => want.contains n)

/-- **No recursor takes a name the environment's own guards look up**
(`reservedRecName`, `ConLeche/Kernel/CoreDefs.lean`): a basis pin, a
literal-guard slot or a certified `Nat` operation.  Implied by
`blockRecNameSetOk` for every block a reasonable stream writes — the
guards' names do not end in `rec` — but checked in its own right,
because it is the fact the MODEL consumes (the literal guards are
congruent across the recursors' cons) and nothing about it should
depend on the conformance check's exact shape. -/
def blockRecNamesUnreserved (p : BlockShape) : Bool :=
  p.recs.all fun rc => reservedRecName rc.cvR.name == false

/-- **The members' index counts**, one `blockCounts?` per member off
the member's OWN former telescope — and, at a def-headed former (task
#195) where there is no telescope to read, off the argument sums of a
recursor whose MAJOR names that member. -/
def blockMemberCounts? (nPd k nC : Nat) (names : List Name)
    (rs : List (ConstantVal × Nat × Nat × List RecRule)) :
    Nat → List ConstantVal → Option (List Nat)
  | _, [] => some []
  | m, cvT :: ts =>
    let r := (rs.find? fun q => recTargetOf names nPd q.2.1 q.1.type == m).map
      fun q => (q.2.1, q.2.2.1)
    match blockCounts? nPd k nC rs.length cvT r with
    | some c => (blockMemberCounts? nPd k nC names rs (m + 1) ts).map fun ns => c.2 :: ns
    | none => none

/-- The block's shape: the members with their counts, the shared
parameter count, the result sort read off member 0 (or the placeholder
the install replaces, task #195) and which eliminator the recursor
records claim.  Nothing of the recursor records is pinned here
(`blockRecPinOk`/`blockRecLpsOk` travel with the record and the install
throws on them) — the arrangement of task #220, so that a block whose
recursor record is a stub is REJECTED by its own type and constructors
rather than declined. -/
def blockShape? (nPd : Nat) (block : List ConstantInfo) : Option BlockShape :=
  match blockSplit block with
  | some (cvTs, cs, rs) =>
    match cvTs, rs with
    | cvT0 :: _, (cvR0, _, _, _) :: _ =>
      let lps := cvT0.levelParams
      let names := cvTs.map (·.name)
      let k := cvTs.length
      match blockMemberCounts? nPd k cs.length names rs 0 cvTs with
      | none => none
      | some nIdxs =>
        let nP := nPd
        if (cvTs.all fun c => reservedBasisNames.contains c.name == false) &&
            (rs.all fun r => reservedBasisNames.contains r.1.name == false) &&
            (cvTs.all fun c => c.levelParams == lps) &&
            cs.all (fun c => c.2.1 == nP && c.1.levelParams == lps &&
              reservedBasisNames.contains c.1.name == false) then
          -- the result sort: member 0's, read off its declared type when
          -- that is a syntactic telescope ending in a sort; otherwise
          -- (task #195) a PLACEHOLDER the install's whnf loop replaces
          let s : Level := match cvT0.type.stripPis (nP + nIdxs.headD 0) with
            | some (_, .sort s) => s
            | _ => .zero
          let isProp := Level.isEquiv s .zero == some true
          let ctors : List (ConstantVal × Nat) :=
            cs.map fun (c : ConstantVal × Nat × Nat) => (c.1, c.2.2)
          let groups := blockGroups names lps nP k ctors
          let members := ((cvTs.zip nIdxs).zip groups).map
            fun (a : (ConstantVal × Nat) × List (ConstantVal × Nat)) =>
              (⟨a.1.1, a.1.2, a.2⟩ : MemberShape)
          -- **the recursors, in the stream's own order**, each with the
          -- member its MAJOR names (`recTargetOf`)
          let recsL := rs.map
            fun (r : ConstantVal × Nat × Nat × List RecRule) =>
              (⟨r.1, r.2.2.1, r.2.1, recTargetOf names nPd r.2.1 r.1.type,
                r.2.2.2.map RecRule.rhs⟩ : RecShape)
          -- WHICH ELIMINATOR the recursors are: the LARGE one carries a
          -- fresh elimination level parameter in front of the block's.
          -- Read off member 0's; the others are `blockRecLpsOk`'s, thrown
          -- at the recursor stage
          let large? : Option Name :=
            match cvR0.levelParams with
            | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
            | [] => none
          match large? with
          | some elim => some ⟨members, recsL, nP, elim, s, true, isProp⟩
          | none => some ⟨members, recsL, nP, .anonymous, s, false, isProp⟩
        else none
    | _, _ => none
  | none => none

/-- Recognise a block for the uniform fixpoint route, at any number of
members: its SHAPE (`blockShape?`) and the recursor records'
structural pin (`blockRecPinOk`), which the recursor stage throws on. -/
def blockParts? (nPd : Nat) (block : List ConstantInfo) : Option BlockParts :=
  match blockShape? nPd block with
  | some p => some ⟨p, blockRecPinOk p block⟩
  | none => none

end ConLeche
