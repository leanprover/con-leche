import Lech.Kernel.Direct.Parts

/-!
# The direct sum class: recognition (task #175 sum-types, indexed)

A **direct sum** is a non-recursive, non-nested inductive with **any
number of constructors other than one**, or — task #175 indexed — an
**indexed family** (`numIndices > 0`) with any number of constructors:
enumerations (`Bool`, `Ordering`), option- and sum-like types
(`Option`, `Sum`, `Decidable`), propositional disjunctions (`Or`), the
empty inductives (zero constructors), and the index-carrying families
(`Eq`-shaped propositions, `Vector`-like non-recursive families,
`SigmaHom`).  The single-constructor index-free class is the direct
*structure* route (`Lech/Kernel/Direct/Parts.lean`), which keeps its
projection table, eta and unit-likeness; nothing here has those (the
official kernel's `is_structure_like` needs one constructor AND no
index), so the two routes are disjoint and this recogniser rejects
`n = 1 ∧ nIdx = 0` outright.

The model is the **tagged disjoint union** of one tuple tower per
constructor (`Lech/SetModel/TaggedSum.lean`), the family's carrier
at an index tuple being the union of the towers RESTRICTED to the
index equation `e⃗_k f⃗ = ı⃗` (one extra proof-field per constructor,
`Lech/Semantics/Tower/SumLeaf.lean`): a value is the pair of a
numeral tag (the constructor's index) and the constructor's tower;
the recursor cases on the tag.  Installation is the direct route's
(`Lech/Kernel/Direct/SumInstall.lean`): the reference checks alone,
no `_model` artifact consumed, the recursor generated and compared
(task #175 S2 — `directRecTyI`/`directRecRhs`).

The checks mirror the reference kernels' inductive-declaration checks
restricted to this class (lean4lean `Lean4Lean/Inductive/Add.lean`,
the official `inductive.cpp`):

* the type former's type is a `∀`-telescope of exactly
  `numParams + numIndices` binders ending in a `Sort`;
* every constructor's type is a `∀`-telescope whose first `numParams`
  binders are the parameters, ending in the type former applied to
  exactly those parameters followed by `numIndices` index expressions
  (`isValidIndAppIdx`); the parameter domains are pinned
  definitionally at install (`checkDirectDomsAt`);
* no recursive occurrence: every constructor binder domain resolves
  in the pre-block environment (`directSumNonRec`), which subsumes
  positivity for this class and is what the model construction needs;
* the recursor is `T.rec` with `numIndices` indices, one motive, one
  minor per constructor (`rulePrefix = numParams + 1 + n`, `majorIdx =
  rulePrefix + numIndices`), one rule per constructor in constructor
  order whose right-hand side is
  `λ p⃗ motive minor⃗ f⃗_j, minor_j f⃗_j` (`mkRecRules`); the large
  eliminator carries a fresh elimination level parameter in front of
  the block's, the small one the block's own.  The recursor's *type*
  is not pinned here: it is generated and compared at install (S2).
* **the elimination restriction** (official `elim_only_at_universe_zero`):
  an inductive whose result sort is not provably nonzero
  (`Level.isNeverZero`) and which has two or more constructors
  eliminates into `Prop` only — a large eliminator on such a block is
  rejected at install (`checkDirectSum`); with ONE constructor every
  field that is not a proposition must be one of the residual's index
  expressions (`checkDirectFieldSortsI`, official's subsingleton-
  elimination criterion — `Eq`'s rule).  This is the rule that keeps
  the model's iota law consistent: at a squash instantiation every
  constructor value is the proof point, and two rules firing to two
  different minors on the same value would contradict each other;
  with one constructor the recursor reads the data fields off the
  index arguments instead of the (squashed) value.
-/

namespace Lech

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
  /-- index count (task #175 indexed; `0` at a plain sum) -/
  nIdx : Nat
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
      -- the parameter and index counts are read off the recursor
      -- (`rulePrefix = nP + 1 + n`, `majorIdx = rulePrefix + nIdx`)
      -- and must agree with every constructor's; one constructor
      -- without an index is the direct structure route
      if rP < n + 1 || mI < rP then none else
      let nP := rP - (n + 1)
      let nIdx := mI - rP
      if n == 1 && nIdx == 0 then none else
      if cvR.name == T.str "rec" &&
          reservedBasisNames.contains T == false &&
          reservedBasisNames.contains cvR.name == false &&
          cs.all (fun c => c.2.1 == nP && c.1.levelParams == lps &&
            reservedBasisNames.contains c.1.name == false &&
            (match c.1.type.stripPis (nP + c.2.2) with
             | some (_, cbody) => directCtorResidOk T lps nP c.2.2 nIdx cbody
             | none => false)) &&
          directSumRulesOk nP n cs rules then
        -- the result sort: read off the declared type when it is a
        -- syntactic telescope ending in a sort; otherwise (task #195: a
        -- former declared AT A DEFINITION that only unfolds to its
        -- telescope, `inductive … : Presieve X`) a PLACEHOLDER that the
        -- install's whnf loop replaces (`checkDirectSumInd`,
        -- `DirectSumParts.withSort`) — official's own
        -- `check_inductive_types` reads the telescope through `whnf`
        let s : Level := match cvT.type.stripPis (nP + nIdx) with
          | some (_, .sort s) => s
          | _ => .zero
        let isProp := Level.isEquiv s .zero == some true
        let ctors := cs.map fun c => (c.1, c.2.2)
        let rhss := rules.map (·.rhs)
        let large? : Option Name :=
          match cvR.levelParams with
          | elim :: relps =>
            if relps == lps && !lps.contains elim then some elim else none
          | [] => none
        match large? with
        | some elim => some ⟨cvT, ctors, nP, nIdx, cvR, elim, s, rhss, true, isProp⟩
        | none =>
          if cvR.levelParams == lps then
            some ⟨cvT, ctors, nP, nIdx, cvR, .anonymous, s, rhss, false, isProp⟩
          else none
      else none
    | none => none
  | _ => none

/-- The record completed with the former's result sort (task #195):
the install stage reads the sort off the checked telescope — the
declared one, or official's whnf'd one — and every later stage runs
on this record.  `isProp` is recomputed so that the recogniser's
invariant `isProp = (isEquiv resSort zero == some true)` holds by
definition. -/
def DirectSumParts.withSort (p : DirectSumParts) (s : Level) : DirectSumParts :=
  { p with resSort := s, isProp := Level.isEquiv s .zero == some true }

@[simp] theorem DirectSumParts.withSort_cvT (p : DirectSumParts) (s : Level) :
    (p.withSort s).cvT = p.cvT := rfl
@[simp] theorem DirectSumParts.withSort_ctors (p : DirectSumParts) (s : Level) :
    (p.withSort s).ctors = p.ctors := rfl
@[simp] theorem DirectSumParts.withSort_nP (p : DirectSumParts) (s : Level) :
    (p.withSort s).nP = p.nP := rfl
@[simp] theorem DirectSumParts.withSort_nIdx (p : DirectSumParts) (s : Level) :
    (p.withSort s).nIdx = p.nIdx := rfl
/-- Completing a record that already carries its own sort (with the
`isProp` flag the recogniser pinned) changes nothing (task #188: the
recursive route's recogniser reads the telescope syntactically). -/
theorem DirectSumParts.withSort_self (p : DirectSumParts)
    (h : p.isProp = (Level.isEquiv p.resSort .zero == some true)) :
    p.withSort p.resSort = p := by
  cases p with
  | mk cvT ctors nP nIdx cvR elim resSort rhss large isProp =>
    simp only [DirectSumParts.withSort]
    simp only at h
    rw [← h]
@[simp] theorem DirectSumParts.withSort_cvR (p : DirectSumParts) (s : Level) :
    (p.withSort s).cvR = p.cvR := rfl
@[simp] theorem DirectSumParts.withSort_elim (p : DirectSumParts) (s : Level) :
    (p.withSort s).elim = p.elim := rfl
@[simp] theorem DirectSumParts.withSort_resSort (p : DirectSumParts) (s : Level) :
    (p.withSort s).resSort = s := rfl
@[simp] theorem DirectSumParts.withSort_rhss (p : DirectSumParts) (s : Level) :
    (p.withSort s).rhss = p.rhss := rfl
@[simp] theorem DirectSumParts.withSort_large (p : DirectSumParts) (s : Level) :
    (p.withSort s).large = p.large := rfl
@[simp] theorem DirectSumParts.withSort_isProp (p : DirectSumParts) (s : Level) :
    (p.withSort s).isProp = (Level.isEquiv s .zero == some true) := rfl

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

end Lech
