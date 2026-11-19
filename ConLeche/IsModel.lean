module

public import ConLeche.Kernel.Install
public import ConLeche.Verify.Level
public import ConLeche.SetModel.Ops
public import ConLeche.SetTheory.Derive.Sigma

@[expose] public section

/-!
# What a model of a declaration stream is

This module is the *statement* half of the main theorem: what it means for a set-theoretic
`model` to be a model of the declarations `ds` the checker reads.  It reads the INPUT: every
clause below is about one record of `ds`, as the stream carries it, and nothing here looks at
the environment the checker builds.  It is written to be read top to bottom in one sitting —
the reading `Expr.eval` of a term as a set, the recursors' rules as propositions (`iotaEqAt`),
one clause per record (`Satisfies`), and the definition `IsModel` — and it imports nothing
from the proof tiers.  The theorem is stated in `ConLeche/Challenge.lean` (with `sorry`) and
proved in `ConLeche/MainTheorem.lean`.

## The model

A model is one function `model : Name → List Nat → V`: the set a constant denotes, given the
values of its universe levels, positionally.  `IsModel V model ds` says: every record of every
declaration of `ds` holds in `model`.  It is a conjunction over `ds` — the order of the
declarations does not matter, and a name two declarations declare must satisfy both clauses.

## The reading

`Expr.eval model φ ρ e` is the set the checker term `e` denotes, when `φ` assigns a natural to
every universe parameter (`LevelParam`, a name) and `ρ` a set to every de Bruijn index
(`BVarIdx`).  It is a total function by structural recursion, one equation per syntax form:

* a constant `c.{us}` denotes `model c` at the values of `us`;
* `Sort u` denotes `univ (Level.eval φ u)`, the types at that level;
* application is the value of a graph at a point (`app`);
* a `∀` denotes the set of dependent function graphs over its domain (`piV`) — or a truth
  value, where its body denotes a truth value on the whole domain; a `λ` denotes the graph of
  its body over its domain (`lamV`) — or the canonical proof `pt`, where its body denotes `pt`
  on the whole domain.  The regime is read off the values, classically, so propositions are
  subsets of a one-element set: proof irrelevance and impredicativity are built into the
  reading, and no typing is consulted;
* a `let` denotes its body at its value;
* a projection `.proj T i e` denotes field `i + 1` of the pair chain `e` denotes (a structure
  value is a right-nested chain whose first component is the constructor's tag);
* a literal denotes what its constructor form (`natLitToConstructor`, `strLitToConstructor`)
  denotes.

Some terms denote junk: a free variable (`fvar`) denotes `∅`, a projection out of something
that is not a structure value denotes whatever that pair chain's component is, and a constant
used at the wrong number of levels reads the first values.  That is harmless: the checker
stores only closed, well-formed terms, and the theorems speak of nothing else.

**Why a total function on the checker's `Expr`.**  The proofs interpret the checker's terms
through their own translation (`interp` over the internal `Term`, `ConLeche/Semantics`), which
is partial — it reads only where the checker's invariant says it can — and carries the
proof's bookkeeping.  A reader of the theorem needs neither: `Expr.eval` reads the input's own
terms, directly, in a dozen lines, and the proofs show that it agrees with their translation
wherever that one reads.

## The set theory

`SetTheory V` (`ConLeche/SetTheory/Core.lean`) is membership `∈ˢ` with extensionality,
pairing, union, power set, regularity, replacement, and an ω-chain of Grothendieck universes.
The reading uses these derived sets (`ConLeche/SetTheory/Derive/*`): `empty`; the pair with its
projections `sfst`/`ssnd`; `app f a`, the value of a graph at a point (`app pt _ = pt`); the
proof point `pt`, the truth values `truthVal p` (`{pt}` if `p`, `∅` otherwise) and
`eqv a b = truthVal (a = b)`; and `univ n`, the types at level `n`: `univ 0` is the set of
truth values.
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

/-- A universe parameter: a name. -/
abbrev LevelParam := Name

/-- A de Bruijn index: the number of binders between a variable's
occurrence and its binder. -/
abbrev BVarIdx := Nat

variable {V : Type w} [SetTheory V]

/-- Extend a variable environment: the innermost binder gets `x`, every
other index moves up by one. -/
def push (x : V) (ρ : BVarIdx → V) : BVarIdx → V
  | 0 => x
  | i + 1 => ρ i

/-- Component `i` of a right-nested pair chain `⟨x₀, ⟨x₁, ⟨x₂, …⟩⟩⟩`. -/
noncomputable def field : Nat → V → V
  | 0, p => sfst p
  | i + 1, p => field i (ssnd p)

/-- **A declaration's level parameters at values**: the `i`-th parameter gets the `i`-th value
(the first occurrence wins), any other name `0`. -/
def Level.assign : List LevelParam → List Nat → LevelParam → Nat
  | p :: ps, v :: vs, n => if p = n then v else Level.assign ps vs n
  | _, _, _ => 0

/-! ## The reading -/

/-- What the literal `n` denotes: `Nat.zero`, or `Nat.succ` applied to `n - 1`'s. -/
noncomputable def natLitVal (model : Name → List Nat → V) : Nat → V
  | 0 => model natZeroName []
  | n + 1 => app (model natSuccName []) (natLitVal model n)

/-- What a string literal denotes: `String.ofList` of its characters' list, each character
`Char.ofNat` of its code (`strLitToConstructor`). -/
noncomputable def strLitVal (model : Name → List Nat → V) (s : String) : V :=
  app (model stringOfListName []) <|
    s.toList.foldr
      (init := app (model listNilName [0]) (model charName []))
      fun c acc =>
        app (app (app (model listConsName [0]) (model charName []))
          (app (model charOfNatName []) (natLitVal model c.toNat))) acc

/-- **The set a term denotes**: see the module docstring. -/
noncomputable def Expr.eval (model : Name → List Nat → V) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Expr → V
  | ρ, .bvar i => ρ i
  | _, .fvar _ _ => empty
  | _, .sort u => univ (Level.eval φ u)
  | _, .const n us => model n (us.map (Level.eval φ))
  | ρ, .app f a => SetTheory.app (Expr.eval model φ ρ f) (Expr.eval model φ ρ a)
  | ρ, .lam ty body =>
    lamV (Expr.eval model φ ρ ty) fun x => Expr.eval model φ (push x ρ) body
  | ρ, .forallE ty body =>
    piV (Expr.eval model φ ρ ty) fun x => Expr.eval model φ (push x ρ) body
  | ρ, .letE _ v body => Expr.eval model φ (push (Expr.eval model φ ρ v) ρ) body
  | _, .lit (.natVal n) => natLitVal model n
  | _, .lit (.strVal s) => strLitVal model s
  | ρ, .proj _ i e => field (i + 1) (Expr.eval model φ ρ e)

/-- The variable environment a closed term is read at (it reads none of it). -/
noncomputable def ρ₀ : BVarIdx → V := fun _ => empty

/-! ## The recursor rules as propositions -/

/-- The levels a recursor rule's constructor is used at, over the
recursor's own level parameters: the rule's recorded levels where it
records them (a nested or a quotient rule), else the constructor's
own parameters, which are the recursor's. -/
def RecRule.ctorLevels (rl : RecRule) (ctorLps : List Name) : List Level :=
  match rl.fire with
  | .nested lvls _ => lvls
  | .levels lvls => lvls
  | .plain => ctorLps.map .param

/-- The sort level of a recursor's motive: the motive application `body`
(under the rule prefix `pre`, the `nIdx` indices and the major) has a
prefix variable as its head, and that binder's domain ends in `Sort u`. -/
def motiveLevel? (pre : List Expr) (nIdx : Nat) (body : Expr) : Option Level :=
  match body.getAppFn with
  | .bvar k =>
    if nIdx + 1 ≤ k ∧ k < nIdx + 1 + pre.length then
      match (pre.getD (pre.length - 1 - (k - (nIdx + 1))) default).piResult with
      | .sort u => some u
      | _ => none
    else none
  | _ => none

/-- The parameters a recursor rule applies its constructor to, in the rule prefix's context
(`rP` binders): a nested rule's recorded pins, else the prefix's first `cnP` variables (as many
as the prefix has: `iotaEqAt` asks for `cnP` of them). -/
def RecRule.iotaParams (rl : RecRule) (rP cnP : Nat) : List Expr :=
  match rl.fire with
  | .nested _ pins => pins
  | _ => (List.range (min cnP rP)).map fun i => .bvar (rP - 1 - i)

/-- **A recursor rule's ι equation, as a proposition.**  For the
recursor `cv` (major position `mI`, rule prefix `rP`), its rule `rl`
and the constructor record `cvj` (with `cnP` parameters) the rule names,
at the recursor's own level parameters:

    ∀ (prefix : the recursor's first rP binders) (fields : C's fields),
      @Eq.{u} (motive indices (C params fields))
        (rec prefix indices (C params fields)) (rl.rhs prefix fields)

`params` are the constructor's parameters in the prefix context: the
recursor's leading arguments, or a nested rule's recorded instantiations;
the field binders are the constructor's, at those parameters; `indices`
are the arguments of the constructor type's conclusion behind its
parameters.  The equation's type is the recursor type's body at the indices
and the major, and `u` the sort of the motive it applies.  `none` where
the records do not have this shape. -/
def iotaEqAt (cvj : ConstantVal) (cnP : Nat) (cv : ConstantVal) (mI rP : Nat)
    (rl : RecRule) : Option Expr := do
  let nF := rl.nfields
  let nIdx := mI - rP
  -- the recursor's telescope: the rule prefix, the indices and the major, the body
  let (pre, rest) ← cv.type.stripPis rP
  let (_, body) ← rest.stripPis (nIdx + 1)
  let u ← motiveLevel? pre nIdx body
  -- the constructor at the rule's levels, its parameters in the prefix context
  let lvls := rl.ctorLevels cvj.levelParams
  let params := rl.iotaParams rP cnP
  let (_, ctorBody) ← (cvj.type.instantiateLevelParams cvj.levelParams lvls).stripPis cnP
  let (fieldDoms, concl) ← (ctorBody.instantiateLift params.reverse).stripPis nF
  let indices := concl.getAppArgs.drop cnP
  guard (params.length = cnP ∧ rP ≤ mI ∧ indices.length = nIdx)
  -- under the prefix and the fields
  let xs := (List.range rP).map fun i => Expr.bvar (rP + nF - 1 - i)
  let fs := (List.range nF).map fun j => Expr.bvar (nF - 1 - j)
  let major := Expr.mkAppN (.const rl.ctor lvls) (params.map (·.liftLooseBVars nF 0) ++ fs)
  let lhs := Expr.mkAppN (.const cv.name (cv.levelParams.map .param)) (xs ++ indices ++ [major])
  let rhs := Expr.mkAppN rl.rhs (xs ++ fs)
  let ty := (body.liftLooseBVars nF (nIdx + 1)).instantiateLift (major :: indices.reverse)
  pure <| (pre ++ fieldDoms).foldr .forallE
    (.app (.app (.app (.const eqName [u]) ty) lhs) rhs)

/-- **How a recursor's rules fire, read off its own type**: its major binder (behind the `mI`
binders) has a domain `C us args`.  Where `C` is a type former of the recursor's own block
(`formers`), the rules are plain: the constructor is used at the recursor's levels and its
leading arguments.  Otherwise the major is a container of a nested block and the rules use
the constructor at `us` and at the container's parameters (`args` without the `mI - rP`
index variables, moved from under the index binders to the rule prefix). -/
def inputFire (formers : List Name) (cv : ConstantVal) (mI rP : Nat) : RecRuleFire :=
  match cv.type.stripPis mI with
  | some (_, .forallE dom _) =>
    match dom.getAppFn with
    | .const c us =>
      if formers.contains c then .plain
      else
        let nI := mI - rP
        let args := dom.getAppArgs
        .nested us ((args.take (args.length - nI)).map (Expr.dropVars nI))
    | _ => .plain
  | _ => .plain

/-! ## The records of a declaration -/

/-- The names of a block's type formers. -/
def blockFormerNames (block : List ConstantInfo) : List Name :=
  block.filterMap fun
    | .indInfo cv _ => some cv.name
    | _ => none

/-- The block's records, its recursors' rules with their firing mode (`inputFire`, read off
the recursor's type against the block's type formers). -/
def blockRecords (block : List ConstantInfo) : List ConstantInfo :=
  block.map fun
    | .recInfo cv mI rP isK rules =>
      .recInfo cv mI rP isK
        (rules.map ({ · with fire := inputFire (blockFormerNames block) cv mI rP }))
    | c => c

/-- Does a value use a hole (`sorryAx`)? -/
def usesSorry (v : Expr) : Bool := v.mentionsAnyConst [sorryAxName]

/-- **The records a declaration contributes to the model's clauses.**

* An axiom is its statement.  `sorryAx`, the hole, contributes nothing: a hole is read where it
  is used, as the axiom of the statement it fills.
* A definition is its statement and its value — unless the value uses a hole: then it is read
  as an axiom of its statement.
* A theorem and an `opaque` are their statements: the value is never read, so an opaque
  constant stays free.
* An inductive block is its records, its recursors' rules firing as their types say
  (`blockRecords`).
* A quotient record, and the axiom `Quot.sound`, are the quotient package's constant at the
  record's level-parameter names (`quotAt`): `Quot.lift` and `Quot.ind` carry their ι rule
  there. -/
def Declaration.records : Declaration → List ConstantInfo
  | .axiomDecl cv =>
    if cv.name = quotSoundName then [quotAt .sound cv]
    else if cv.name = sorryAxName then []
    else [.axiomInfo cv]
  | .defnDecl cv v hint => if usesSorry v then [.axiomInfo cv] else [.defnInfo cv v hint]
  | .thmDecl cv _ => [.thmInfo cv]
  | .opaqueDecl cv _ => [.axiomInfo cv]
  | .quotDecl k cv => [quotAt k cv]
  | .indDecl block _ => blockRecords block

/-! ## The clauses -/

/-- **A recursor rule holds** at the level assignment `φ`: for every constructor record of
`ds` the rule names, the rule's ι equation denotes an inhabited set (a true proposition). -/
def RuleHolds (V : Type w) [SetTheory V] (model : Name → List Nat → V) (ds : List Declaration)
    (φ : LevelParam → Nat) (cv : ConstantVal) (mI rP : Nat) (rl : RecRule) : Prop :=
  ∀ d ∈ ds, ∀ cvj cnP nF T, ConstantInfo.ctorInfo cvj cnP nF T ∈ d.records →
    cvj.name = rl.ctor →
    ∀ e, iotaEqAt cvj cnP cv mI rP rl = some e → ∃ x, x ∈ˢ Expr.eval model φ ρ₀ e

/-- **A record holds in `model`**: at every list of level values `vals`, one per level
parameter, read through `φ := Level.assign ps vals`,

* the constant is a member of what its type denotes;
* a definition is what its value denotes;
* every rule of a recursor holds (`RuleHolds`). -/
def Satisfies (V : Type w) [SetTheory V] (model : Name → List Nat → V) (ds : List Declaration)
    (c : ConstantInfo) : Prop :=
  ∀ vals : List Nat, vals.length = c.toConstantVal.levelParams.length →
    let φ := Level.assign c.toConstantVal.levelParams vals
    model c.name vals ∈ˢ Expr.eval model φ ρ₀ c.toConstantVal.type ∧
    match c with
    | .defnInfo _ value _ => model c.name vals = Expr.eval model φ ρ₀ value
    | .recInfo cv mI rP _ rules => ∀ rl ∈ rules, RuleHolds V model ds φ cv mI rP rl
    | _ => True

/-- **`model` is a model of the declaration `d`** (of the stream `ds`, where its recursors
find their constructors): every record of `d` holds. -/
def IsModelOfDecl (V : Type w) [SetTheory V] (model : Name → List Nat → V)
    (ds : List Declaration) (d : Declaration) : Prop :=
  ∀ c ∈ d.records, Satisfies V model ds c

/-- **`model` is a model of the declarations `ds`**: of every one of them. -/
def IsModel (V : Type w) [SetTheory V] (model : Name → List Nat → V)
    (ds : List Declaration) : Prop :=
  ∀ d ∈ ds, IsModelOfDecl V model ds d

/-! ## The prelude's `False` and `Eq`

Nothing above treats `False` or `Eq` specially: `False` is whatever `model` makes it, and so is
`Eq`.  What makes them mean the empty proposition and equality is their declarations, through
their own clauses: `False.rec`'s membership forces `⟦False⟧ = ∅`, and `Eq.refl` with `Eq.rec`
force `⟦@Eq A a b⟧ = eqv a b` (`IsModel.false_empty`, `IsModel.eq_eqv`,
`ConLeche/Semantics/IsModelBasis.lean`).  These are the records the prelude declares them
with, as a stream carries them (at any level-parameter names); the checker accepts a stream
declaring `False` or `Eq` only with them. -/

/-- `ds` has a record named `n`. -/
def DeclaresName (ds : List Declaration) (n : Name) : Prop :=
  ∃ d ∈ ds, ∃ c ∈ d.records, c.name = n

/-- `ds` has a record declaring `n` at the level parameters `ps` with the type `T`. -/
def HasRecord (ds : List Declaration) (n : Name) (ps : List LevelParam) (T : Expr) : Prop :=
  ∃ d ∈ ds, ∃ c ∈ d.records, c.toConstantVal = ⟨n, ps, T⟩

/-- `False.rec.{u} : (motive : False → Sort u) → (t : False) → motive t`. -/
def falseRecType (u : Level) : Expr :=
  .forallE (.forallE (.const falseName []) (.sort u)) <|
    .forallE (.const falseName []) (.app (.bvar 1) (.bvar 0))

/-- `Eq.{u} : {α : Sort u} → α → α → Prop`. -/
def eqType (u : Level) : Expr :=
  .forallE (.sort u) <| .forallE (.bvar 0) <| .forallE (.bvar 1) (.sort .zero)

/-- `@Eq.{u} α a b`, under binders where `α`, `a`, `b` are the given terms. -/
def eqApp (u : Level) (α a b : Expr) : Expr :=
  .app (.app (.app (.const eqName [u]) α) a) b

/-- `Eq.refl.{u} : ∀ {α : Sort u} (a : α), @Eq α a a`. -/
def eqReflType (u : Level) : Expr :=
  .forallE (.sort u) <| .forallE (.bvar 0) (eqApp u (.bvar 1) (.bvar 0) (.bvar 0))

/-- `Eq.rec.{u_1, u} : ∀ {α : Sort u} {a : α} {motive : (b : α) → a = b → Sort u_1},
motive a (Eq.refl a) → ∀ {b : α} (t : a = b), motive b t`. -/
def eqRecType (u₁ u : Level) : Expr :=
  .forallE (.sort u) <|
  .forallE (.bvar 0) <|
  .forallE (.forallE (.bvar 1) (.forallE (eqApp u (.bvar 2) (.bvar 1) (.bvar 0)) (.sort u₁))) <|
  .forallE (.app (.app (.bvar 0) (.bvar 1))
    (.app (.app (.const eqReflName [u]) (.bvar 2)) (.bvar 1))) <|
  .forallE (.bvar 3) <|
  .forallE (eqApp u (.bvar 4) (.bvar 3) (.bvar 0)) <|
  .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)

/-- **`ds` declares the prelude's `False`**: its eliminator, at some level-parameter name. -/
def DeclaresFalse (ds : List Declaration) : Prop :=
  ∃ p, HasRecord ds (falseName.str "rec") [p] (falseRecType (.param p))

/-- **`ds` declares the prelude's `Eq`**: the type former, `Eq.refl` and `Eq.rec`, each at
some (distinct) level-parameter names. -/
def DeclaresEq (ds : List Declaration) : Prop :=
  (∃ p, HasRecord ds eqName [p] (eqType (.param p))) ∧
  (∃ p, HasRecord ds eqReflName [p] (eqReflType (.param p))) ∧
  (∃ p₁ p, p₁ ≠ p ∧ HasRecord ds (eqName.str "rec") [p₁, p] (eqRecType (.param p₁) (.param p)))

end ConLeche
