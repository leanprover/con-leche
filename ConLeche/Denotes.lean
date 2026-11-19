module

public import ConLeche.IsModel

@[expose] public section

/-!
# What a checker term denotes, and what a model of an environment is

This module is the *statement* half of the main theorem: it says what it
means for the environment the checker builds to have a model in a set
theory `V`.  It is written to be read top to bottom in one sitting —
three one-line helpers, the relation `Denotes`, the recursors' rules as
propositions (`ruleEqs`), the structure `Model` — and it imports nothing from the proof tiers.  The theorem itself is
stated in `ConLeche/Challenge.lean` (with `sorry`) and proved in
`ConLeche/MainTheorem.lean`.

## The relation

`Denotes cval env φ ρ e v` says: the checker term `e` denotes the set
`v`, when

* every constant `n` at every assignment `ψ` of naturals to its
  universe parameters (`LevelParam`, a name) denotes the set `cval n ψ`,
* `env` is the environment (read only to learn a constant's universe
  parameters and a structure's projection table),
* `φ` assigns a natural to every universe parameter in scope, and
* `ρ` assigns a set to every de Bruijn index (`BVarIdx`) in scope.

There is one rule per syntax form and no rule at all for a free
variable (`fvar`) or a term that does not resolve, so such a term
denotes nothing.  That is the right reading for stored constants: the
checker stores every constant's type as a **closed** term — bound
variables are de Bruijn indices under their binders, there is no
`fvar` — and the relation reads a binder's body by pushing the bound
value onto `ρ`, with no renaming and no instantiation.  A `let` is read
the same way: its value, then its body with the value pushed; its type
is not read, as no rule reads a type.

The two clauses that carry the type theory:

* **Binders read their regime off the values.**  A `∀` whose fibres
  over its domain are all truth values (`univ 0` is the set of truth
  values) denotes a truth value (the proposition "every `x ∈ A` has a
  `y ∈ B x`"); otherwise it denotes the set of dependent function
  graphs (`piV`).  A `λ` whose body denotes the proof point (`pt`) at
  every value of its domain denotes the one canonical proof; otherwise
  it denotes the literal graph of its body (`lamV`,
  `ConLeche/SetModel/Ops.lean`).  So propositions are subsets of a
  one-element set: proof irrelevance and impredicativity are built into
  the reading, and no typing is consulted.  Over an empty domain both
  read as propositions.  The bodies are read on the domain only:
  `piV`/`lamV` look at nothing else.
* **Projections read a pair chain.**  A structure value is a
  right-nested pair chain; `field i p` is its `i`-th component
  (`sfst ∘ ssnd^i`).  The chain starts with the constructor's tag, so
  field `i` of a structure (one with a projection table,
  `env.findProj?`) sits at position `i + 1`.  A projection from
  anything without a table denotes nothing.

A universe level denotes a natural (`Level.eval φ u`, the ordinary
evaluation with `imax u 0 = 0`), and `Sort u` denotes `univ u`, the
types at level `u` (below).  A constant is used at a list of
levels `us`; `Level.substFn φ ps us` is the assignment sending the
constant's own parameters `ps` to the values of `us` at `φ`
(`ConLeche/Verify/Level.lean`).  A literal denotes what its constructor
form denotes — the checker's own `natLitToConstructor`
(`n + 1` ↦ `Nat.succ (lit n)`) and `strLitToConstructor`
(`String.ofList [Char.ofNat (lit c₁), …]`).

`Denotes_functional`, proved just below the relation, states that a
term has at most one denotation, so `∃ T, Denotes … T ∧ …` below is a
statement about *the* denotation.

## The set theory

`SetTheory V` (`ConLeche/SetTheory/Core.lean`) is membership `∈ˢ` with
extensionality, pairing, union, power set, regularity, replacement, and
an ω-chain of Grothendieck universes.  The reading uses these derived
sets (`ConLeche/SetTheory/Derive/*`, each a few lines): `empty`; the
Kuratowski pair with its projections `sfst`/`ssnd`; `graph F A`, the
graph of `F` on `A`, and `app f a`, the value of a graph at a point
(`app pt _ = pt`: a proof applied to anything is a proof); `piSet A B`,
the graphs in `(x : A) → B x`; the proof point `pt`, the truth values
`truthVal p` (`{pt}` if `p`, `∅` otherwise), and `univ n`, the types
at level `n`: `univ 0` is the set of truth values, and above `0`
`univ n` holds the members of the universe `tg n` (`tg (n+1)` is the
chain's universe `n+2`) that are truth values or strict (not `pt` and
without `pt` as a member).
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- `Denotes cval env φ ρ e v`: the term `e` denotes the set `v`.  See
the module docstring. -/
inductive Denotes (cval : Name → (LevelParam → Nat) → V) (env : Env) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Expr → V → Prop
  /-- a bound variable denotes what the environment assigns it -/
  | bvar {ρ : BVarIdx → V} {i : BVarIdx} :
      Denotes cval env φ ρ (.bvar i) (ρ i)
  /-- `Sort u` denotes the universe at the level `u` evaluates to -/
  | sort {ρ : BVarIdx → V} {u : Level} :
      Denotes cval env φ ρ (.sort u) (univ (Level.eval φ u))
  /-- a stored constant, used at as many levels as it has parameters,
  denotes its `cval` at the assignment those levels induce -/
  | const {ρ : BVarIdx → V} {n : Name} {us : List Level} {ci : ConstantInfo}
      (hf : env.find? n = some ci)
      (hlen : us.length = ci.toConstantVal.levelParams.length) :
      Denotes cval env φ ρ (.const n us)
        (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
  /-- an application denotes the value of the function's graph at the
  argument -/
  | app {ρ : BVarIdx → V} {f a : Expr} {F X : V}
      (hf : Denotes cval env φ ρ f F) (ha : Denotes cval env φ ρ a X) :
      Denotes cval env φ ρ (.app f a) (app F X)
  /-- a `λ` denotes the graph of its body over its domain, or the
  canonical proof where the body denotes a proof (`pt`) on the whole
  domain -/
  | lam {ρ : BVarIdx → V} {ty body : Expr} {A : V} {F : V → V}
      (hA : Denotes cval env φ ρ ty A)
      (hF : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) body (F x)) :
      Denotes cval env φ ρ (.lam ty body) (lamV A F)
  /-- a `∀` denotes the set of dependent function graphs over its
  domain, or a truth value where its body denotes a truth value on the
  whole domain -/
  | pi {ρ : BVarIdx → V} {ty body : Expr} {A : V} {B : V → V}
      (hA : Denotes cval env φ ρ ty A)
      (hB : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) body (B x)) :
      Denotes cval env φ ρ (.forallE ty body) (piV A B)
  /-- a `let` denotes its body at its value; the type is not read -/
  | letE {ρ : BVarIdx → V} {ty v body : Expr} {Y X : V}
      (hv : Denotes cval env φ ρ v Y) (hb : Denotes cval env φ (push Y ρ) body X) :
      Denotes cval env φ ρ (.letE ty v body) X
  /-- a projection at a stored table reads the field's position in the
  pair chain, behind the tag -/
  | proj_table {ρ : BVarIdx → V} {T : Name} {i : Nat} {e : Expr} {entry : ProjEntry} {P : V}
      (ht : env.findProj? T i = some entry) (he : Denotes cval env φ ρ e P) :
      Denotes cval env φ ρ (.proj T i e) (field (i + 1) P)
  /-- a `Nat` literal denotes what its constructor form denotes -/
  | natLit {ρ : BVarIdx → V} {n : Nat} {X : V}
      (h : Denotes cval env φ ρ (natLitToConstructor n) X) :
      Denotes cval env φ ρ (.lit (.natVal n)) X
  /-- a `String` literal denotes what its constructor form denotes -/
  | strLit {ρ : BVarIdx → V} {s : String} {X : V}
      (h : Denotes cval env φ ρ (strLitToConstructor s) X) :
      Denotes cval env φ ρ (.lit (.strVal s)) X

/-- **A term has at most one denotation.**  Every rule of `Denotes` is
determined by the term's syntax form — the two `proj` rules that could
overlap are separated by whether the environment holds a projection
table — so the relation is a partial function, and `∃ T, Denotes … T ∧ …`
in `Model.mem` below is a statement about *the* denotation. -/
theorem Denotes_functional {V : Type w} [SetTheory V]
    {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {e : Expr} {v w : V}
    (hv : Denotes cval env φ ρ e v) (hw : Denotes cval env φ ρ e w) :
    v = w := by
  induction hv generalizing w with
  | bvar => cases hw; rfl
  | sort => cases hw; rfl
  | const hf _ =>
    cases hw with
    | const hf' _ => rw [hf] at hf'; cases hf'; rfl
  | app _ _ ihf iha =>
    cases hw with
    | app hf' ha' => rw [ihf hf', iha ha']
  | lam _ _ ihA ihF =>
    cases hw with
    | lam hA' hF' =>
      obtain rfl := ihA hA'
      exact ConLeche.SetModel.lamV_congr fun x hx => ihF x hx (hF' x hx)
  | pi _ _ ihA ihB =>
    cases hw with
    | pi hA' hB' =>
      obtain rfl := ihA hA'
      exact ConLeche.SetModel.piV_congr fun x hx => ihB x hx (hB' x hx)
  | letE _ _ ihv ihb =>
    cases hw with
    | letE hv' hb' =>
      obtain rfl := ihv hv'
      exact ihb hb'
  | proj_table _ _ ih =>
    cases hw with
    | proj_table _ he' => rw [ih he']
  | natLit _ ih =>
    cases hw with
    | natLit h' => exact ih h'
  | strLit _ ih =>
    cases hw with
    | strLit h' => exact ih h'

/-! ### The recursor rules as propositions -/

/-- **A stored recursor rule's ι equation** (`iotaEqAt`, `ConLeche/IsModel.lean`), at the
constructor record the environment stores under the rule's constructor name. -/
def iotaEq (find? : Name → Option ConstantInfo) (cv : ConstantVal) (mI rP : Nat)
    (rl : RecRule) : Option Expr := do
  let .ctorInfo cvj cnP _ _ ← find? rl.ctor | none
  iotaEqAt cvj cnP cv mI rP rl

/-- **The ι equations of an environment**: every stored recursor rule's
`iotaEq` (the quotient eliminators' among them: `Quot.lift` and
`Quot.ind` are stored recursors with one rule each).  A recursor is read
the way `Denotes` reads a constant, through its name. -/
def ruleEqs (env : Env) : List Expr :=
  env.consts.flatMap fun c => match env.find? c.name with
    | some (.recInfo cv mI rP _ rules) => rules.filterMap (iotaEq env.find? cv mI rP)
    | _ => []

/-- **The ι equations hold** in `cval`: wherever one denotes, what it
denotes is inhabited, at every level assignment (the equation is closed;
its level parameters are the recursor's). -/
def RuleEqsHold (cval : Name → (LevelParam → Nat) → V) (env : Env) : Prop :=
  ∀ e ∈ ruleEqs env, ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (P : V),
    Denotes cval env φ ρ e P → ∃ x, x ∈ˢ P

/-- **A model of the environment `env` in the set theory `V`**: one
assignment `cval` of a set to every constant at every level
assignment — fixed once, for the whole environment — under which every
stored constant is a member of what its type denotes, the built-in
`False` is the empty set, the built-in `Eq` is set equality, every
stored definition means its value and every recursor rule holds.

The interpretation of the constants *is* the model: there is nothing
else to choose (`Sort`, `∀`, `λ`, application and projection are read
by fixed set operations).  `mem` is what makes every stored theorem
true — a theorem `t : P` is a constant whose type `P` denotes a truth
value, and `cval t φ ∈ˢ ⟦P⟧` says that truth value is `{pt}` — and
`false_empty` is what makes truth mean something: a proof of `False`
would be a member of `∅`.

`False` and `Eq` are both built in (the checker installs them from its
own pins and rejects a stream that declares them otherwise), so the
last two fields are facts about the checker's own constants, not
hypotheses about the input; each is stated of whatever the stored
constant denotes, so it says nothing when nothing is stored.

A model is also a model in the logician's sense for definitions:
`defn_eq` makes every stored definition's defining equation hold, read
off the environment's own data, so that a definition hidden behind an
import still means its value.  Any other definitional equality a reader
cares about can be stated as a theorem `h : a = b` proved by `rfl`;
`mem` puts `cval h φ` in what `Eq A a b` denotes, which by
`eq_equality` is `eqv ⟦a⟧ ⟦b⟧`, inhabited only when `⟦a⟧ = ⟦b⟧`
(`SetTheory.eq_of_mem_eqv`).

The recursors are free constants in this reading too, but their rules
are not: `rule_eqs` makes every stored recursor rule's ι equation
(`iotaEq` above, an `Eq` between the recursor applied to a constructor
and the rule's right-hand side) hold, so that a recursor hidden behind
an import still computes as its rules say. -/
structure Model (V : Type w) [SetTheory V] (env : Env) where
  /-- the set a constant denotes, per level assignment -/
  cval : Name → (LevelParam → Nat) → V
  /-- every stored constant is a member of what its type denotes, at
  every level assignment (and every variable environment — the type
  is closed) -/
  mem : ∀ c ∈ env.consts, ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
    ∃ T, Denotes cval env φ ρ c.toConstantVal.type T ∧ cval c.name φ ∈ˢ T
  /-- whatever the built-in `False` denotes is the empty set -/
  false_empty : ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (F : V),
    Denotes cval env φ ρ (.const falseName []) F → F = empty
  /-- whatever the built-in `Eq` denotes is set equality: at a type `A`
  of the universe the level `u` names, and two of its members `a` and
  `b`, `@Eq.{u} A a b` denotes the truth value of `a = b`.  The three
  membership premises are the graph's domains — `Eq`'s denotation is a
  three-fold graph over `univ (Level.eval φ u)`, then over `A`, then
  over `A` again, and a graph read off its domain says nothing -/
  eq_equality : ∀ (u : Level) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (E A a b : V),
    Denotes cval env φ ρ (.const eqName [u]) E →
    A ∈ˢ univ (Level.eval φ u) → a ∈ˢ A → b ∈ˢ A →
    app (app (app E A) a) b = eqv a b
  /-- **a stored definition means its value**: at every level
  assignment, the value denotes what the constant does.  The value is
  read at the definition's own level parameters (an instance `c.{us}`
  is the same equation at the assignment `us` induces).  Definitions
  only: a theorem is stored by its statement (its record carries no
  value), and an opaque constant's value is never unfolded, so it stays
  free -/
  defn_eq : ∀ (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes cval env φ ρ value (cval cv.name φ)
  /-- **a recursor computes by its rules**: every stored rule's ι
  equation denotes an inhabited truth value, at every level assignment -/
  rule_eqs : RuleEqsHold cval env

/-- **A stored definition's value fixes the constant**: in every model,
whatever the value denotes is what the constant denotes. -/
theorem Model.cval_of_defn {V : Type w} [SetTheory V] {env : Env} (M : Model V env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (h : ConstantInfo.defnInfo cv value hint ∈ env.consts)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {X : V}
    (hX : Denotes M.cval env φ ρ value X) : M.cval cv.name φ = X :=
  Denotes_functional (M.defn_eq cv value hint h φ ρ) hX

end ConLeche
