import Setlec.Kernel.Direct.Parts

/-!
# The direct sum class: recognition (task #175 sum-types)

A **direct sum** is a non-recursive, non-indexed, non-nested inductive
with **any number of constructors other than one** — enumerations
(`Bool`, `Ordering`), option- and sum-like types (`Option`, `Sum`,
`Decidable`), propositional disjunctions (`Or`), and the empty
inductives (zero constructors).  The single-constructor class is the
direct *structure* route (`Setlec/Kernel/Direct/Parts.lean`), which
keeps its projection table, eta and unit-likeness; a sum has none of
those (the official kernel's `is_structure_like` needs one
constructor), so the two routes are disjoint by the constructor count
and this recogniser rejects `n = 1` outright.

The model is the **tagged disjoint union** of one tuple tower per
constructor (`Setlec/SetModel/TaggedSum.lean`): a value is the pair of
a numeral tag (the constructor's index) and the constructor's tower;
the recursor cases on the tag.  Installation is the direct route's
(`Setlec/Kernel/Direct/SumInstall.lean`): the reference checks alone,
no `_model` artifact consumed, the recursor generated and compared
(task #175 S2 — `directRecTy`/`directRecRhs` were written over a
constructor list from the start).

The checks mirror the reference kernels' inductive-declaration checks
restricted to this class (lean4lean `Lean4Lean/Inductive/Add.lean`,
the official `inductive.cpp`):

* the type former's type is a `∀`-telescope of exactly `numParams`
  binders ending in a `Sort`; index-free means the telescope ends there;
* every constructor's type is a `∀`-telescope whose first `numParams`
  binders are the parameters, ending in the type former applied to
  exactly those parameters (`isValidIndAppIdx`); the parameter domains
  are pinned definitionally at install (`checkDirectDomsAt`);
* no recursive occurrence: every constructor binder domain resolves
  in the pre-block environment (`directSumNonRec`), which subsumes
  positivity for this class and is what the model construction needs;
* the recursor is `T.rec` with no indices, one motive, one minor per
  constructor (`majorIdx = rulePrefix = numParams + 1 + n`), one rule
  per constructor in constructor order whose right-hand side is
  `λ p⃗ motive minor⃗ f⃗_j, minor_j f⃗_j` (`mkRecRules`); the large
  eliminator carries a fresh elimination level parameter in front of
  the block's, the small one the block's own.  The recursor's *type*
  is not pinned here: it is generated and compared at install (S2).
* **the elimination restriction** (official `elim_only_at_universe_zero`):
  an inductive whose result sort is not provably nonzero
  (`Level.isNeverZero`) and which has two or more constructors
  eliminates into `Prop` only — a large eliminator on such a block is
  rejected at install (`checkDirectSum`).  This is the rule that keeps
  the model's iota law consistent: at a squash instantiation every
  constructor value is the proof point, and two rules firing to two
  different minors on the same value would contradict each other.
-/

namespace Setlec

/-- The right-hand side body of the rule for constructor `j` of `n`:
the minor premise `j` (sitting `n - 1 - j` binders above the fields)
applied to the field variables.  `directRuleBody nF = directRuleBodyAt
nF 1 0`. -/
def directRuleBodyAt (nF n j : Nat) : Expr :=
  Expr.mkAppN (.bvar (nF + n - 1 - j)) ((List.range nF).map fun k => Expr.bvar (nF - 1 - k))

/-- The pieces of a recognised direct sum block. -/
structure DirectSumParts where
  /-- the type former -/
  cvT : ConstantVal
  /-- the constructors in declaration order, each with its field count -/
  ctors : List (ConstantVal × Nat)
  /-- parameter count -/
  nP : Nat
  /-- the recursor -/
  cvR : ConstantVal
  /-- the recursor's fresh elimination level parameter (`large` only;
  `.anonymous` for a small eliminator) -/
  elim : Name
  /-- the result sort -/
  resSort : Level
  /-- the rules' right-hand sides as exported, in constructor order -/
  rhss : List Expr
  /-- large eliminator (a fresh elimination level parameter in front) -/
  large : Bool
  /-- the result sort is provably `Prop` -/
  isProp : Bool
  deriving Repr

/-- The block's members after the type former: the constructors, then
the closing recursor. -/
def directSumSplit : List ConstantInfo →
    Option (List (ConstantVal × Nat × Nat) × ConstantVal × Nat × Nat × List RecRule)
  | [.recInfo cvR mI rP rules] => some ([], cvR, mI, rP, rules)
  | .ctorInfo cvC nP nF :: rest =>
    (directSumSplit rest).map fun q => ((cvC, nP, nF) :: q.1, q.2)
  | _ => none

/-- The rules of a recognised block, in constructor order: rule `j`
fires constructor `j` with its field count and the canonical
right-hand side shape. -/
def directSumRulesOk (nP n : Nat) (cs : List (ConstantVal × Nat × Nat))
    (rules : List RecRule) : Bool :=
  rules.length == n &&
  (List.range n).all fun j =>
    match rules[j]?, cs[j]? with
    | some rule, some (cvC, _, nF) =>
      rule.ctor == cvC.name && rule.nfields == nF &&
      (match rule.rhs.stripLams (nP + 1 + n + nF) with
       | some (_, rbody) => rbody == directRuleBodyAt nF n j
       | none => false)
    | _, _ => false

/-- Recognise a direct sum block (see the module docs).  `none` means
"not this class" — the caller falls through to the modeled path. -/
def directSumPartsCore? (block : List ConstantInfo) : Option DirectSumParts :=
  match block with
  | .indInfo cvT _ :: rest =>
    match directSumSplit rest with
    | some (cs, cvR, mI, rP, rules) =>
      let T := cvT.name
      let lps := cvT.levelParams
      let n := cs.length
      -- one constructor is the direct structure route; the parameter
      -- count is read off the recursor (`rulePrefix = nP + 1 + n`)
      -- and must agree with every constructor's
      if n == 1 || rP < n + 1 then none else
      let nP := rP - (n + 1)
      if cvR.name == T.str "rec" && mI == rP &&
          reservedBasisNames.contains T == false &&
          reservedBasisNames.contains cvR.name == false &&
          cs.all (fun c => c.2.1 == nP && c.1.levelParams == lps &&
            reservedBasisNames.contains c.1.name == false &&
            (match c.1.type.stripPis (nP + c.2.2) with
             | some (_, cbody) => cbody == directFam T lps nP c.2.2
             | none => false)) &&
          directSumRulesOk nP n cs rules then
        match cvT.type.stripPis nP with
        | some (_, .sort s) =>
          let isProp := Level.isEquiv s .zero == some true
          let ctors := cs.map fun c => (c.1, c.2.2)
          let rhss := rules.map (·.rhs)
          let large? : Option Name :=
            match cvR.levelParams with
            | elim :: relps =>
              if relps == lps && !lps.contains elim then some elim else none
            | [] => none
          match large? with
          | some elim => some ⟨cvT, ctors, nP, cvR, elim, s, rhss, true, isProp⟩
          | none =>
            if cvR.levelParams == lps then
              some ⟨cvT, ctors, nP, cvR, .anonymous, s, rhss, false, isProp⟩
            else none
        | _ => none
      else none
    | none => none
  | _ => none

/-- **Non-recursive**: every binder domain of every constructor
resolves in the pre-block environment (see `directNonRec`). -/
def directSumNonRec (env : Env) (p : DirectSumParts) : Bool :=
  p.ctors.all fun c =>
    match c.1.type.stripPis (p.nP + c.2) with
    | some (cbs, _) => cbs.all fun b => b.2.1.constsResolve env
    | none => false

/-- Recognise a direct sum block against an environment.  Like
`directParts?` this is a priority gate: a recognised block installs
directly whether or not the stream carries `_model` artifacts for it. -/
def directSumParts? (env : Env) (block : List ConstantInfo) :
    Option DirectSumParts :=
  match directSumPartsCore? block with
  | some p => if directSumNonRec env p then some p else none
  | none => none

end Setlec
