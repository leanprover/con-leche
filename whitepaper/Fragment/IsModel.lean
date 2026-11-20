module

public import Fragment.EnvModel

@[expose] public section

/-!
# What a model of the input is

The statement half of the main theorem: what it means for an
assignment `M` to be a model of the constants the input declares.  It
reads the INPUT: every clause below is about one constant, as a
declaration stores it, and nothing here looks at how the checker or
the proof builds a model.  It is written to be read top to bottom —
the reading of a recursor's rule off the recursor's own type
(`RuleHolds`), one clause per constant (`ModelOf`), and the
definition `IsModel`.

## The model

A model is one function `M : Name → List Nat → V`: the set a constant
denotes, given the values of its universe levels, positionally.  A
term is read by `interp` (`Interp.lean`): a constant at levels is `M`
at their values, a sort the types of its universe, application the
value of a graph at a point, a `∀` a dependent function space (or a
truth value, where every fibre is one), a lambda a graph (or the point,
where every body value is), a `let` its body at its value.  A stored
type or value is closed, read under the valuation `valOf ps vals` of
the constant's level parameters `ps` and the variable environment
`base` (which a closed term does not read).

`IsModel V M C` says: every constant of `C` holds in `M`
(`ModelOf M c ci`), where `C : Name → ConstInfo → Prop` is a set of
named constants given by its membership predicate; for a list of
declarations it is `constantsOf ds` (`Modular.lean`), the entries the
declarations store.  It is pointwise: `ModelOf M c ci` reads the
constant `c` and nothing else — not even a recursor's constructors, as
a recursor's rules are read off its own type.  So the order of the
constants does not matter, and a name two constants share must satisfy
both clauses.

* A constant is a member of what its type denotes.
* A definition is what its value denotes.
* A recursor's rules hold (`RuleHolds`).
* An assumption — a theorem's statement, an axiom, a hole — is
  membership only.

Con-leche's counterpart: `ConLeche/IsModel.lean`, which reads the
same clauses off the lean4export records, a recursor rule as an
equation of Lean's `Eq` read off the recursor's type.  The fragment
has no `Eq`, so the rule is stated on values directly.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V]

/-- **The closed base environment**: every variable the point.  A closed
term does not read it. -/
def base : Nat → V := fun _ => pt

/-- **The valuation of level parameters at values**, positionally (the
first occurrence wins); a parameter not in the list is `0`. -/
def valOf (ps : List Name) (ls : List Nat) : Name → Nat :=
  fun n => ((ps.zip ls).lookup n).getD 0

/-! ## Reading a telescope -/

namespace Expr

/-- The domain of the binder at position `q` (outermost first) of a
`∀`-telescope. -/
def piDom? : Expr → Nat → Option Expr
  | .pi A _, 0 => some A
  | .pi _ B, q + 1 => piDom? B q
  | _, _ => none

/-- The number of leading binders of a `∀`-telescope. -/
def piCount : Expr → Nat
  | .pi _ B => piCount B + 1
  | _ => 0

/-- The conclusion of a `∀`-telescope, behind all its binders. -/
def piConcl : Expr → Expr
  | .pi _ B => piConcl B
  | e => e

/-- The head of an application spine. -/
def head : Expr → Expr
  | .app f _ => head f
  | e => e

/-- The arguments of an application spine, outermost first. -/
def args : Expr → List Expr
  | .app f a => args f ++ [a]
  | _ => []

/-- The variable heading an application spine, if any. -/
def headVar? (e : Expr) : Option Nat :=
  match e.head with
  | .bvar k => some k
  | _ => none

/-- **The motive a recursor's type concludes with**: the position
(outermost first) of the binder heading the conclusion. -/
def motivePos (T : Expr) : Option Nat :=
  T.piConcl.headVar?.map fun k => T.piCount - 1 - k

end Expr

/-- **The minor premises of the motive at position `mot`** among the
first `numBefore` binders of a recursor's type `T` (its parameters,
motives and minor premises): the positions `q`, in order, of the
binders after the motive whose conclusion, behind all their own
binders, is headed by that motive. -/
def minorsOf (T : Expr) (numBefore mot : Nat) : List Nat :=
  (List.range numBefore).filter fun q =>
    decide (mot < q) &&
      match T.piDom? q with
      | some D => D.piConcl.headVar? == some (D.piCount + (q - 1 - mot))
      | none => false

/-- **The conclusion of a telescope, read**: behind all its binders,
with the environment those binders extend `ρ` by, each read as the
point.  It is applied to a minor premise behind its fields: the
remaining binders are the induction hypotheses, which the conclusion
does not mention. -/
def conclV : (Nat → V) → Expr → Expr × (Nat → V)
  | ρ, .pi _ B => conclV (cons pt ρ) B
  | ρ, e => (e, ρ)

/-! ## The clauses -/

/-- **A recursor's rule holds**: the recursor (whose set is `r`, whose
type is `T`, read at `φ`) applied to its first `numBefore` arguments
(the parameters, motives and minor premises) and then to the indices
and the major premise a minor premise concludes with, is the rule's
right-hand side applied to the same first arguments and the minor
premise's fields:

    rec xs idx (C params ys) = rhs xs ys

Rule `i` reads the `i`-th minor premise of the motive the recursor's
type concludes with (`minorsOf`), at position `q`: its domain `D` is
read under the first `q` values (`piBodyV`), its first `rl.nfields`
binders are the fields `ys`, and its conclusion, behind the fields and
the induction hypotheses (`conclV`), is the motive applied to the
indices `idx` and the major premise `C params ys` — which the left-hand
side reads.  The equation holds at every list of values fitting the
binders (`TeleFitV`), unconditionally.  Nothing else is read: no
constructor constant, no comparison of levels or parameters, no firing
mode. -/
def RuleHolds (M : Name → List Nat → V) (φ : Name → Nat) (r : V) (T : Expr)
    (numBefore i : Nat) (rl : RecRule) : Prop :=
  ∀ (mot q : Nat), T.motivePos = some mot → (minorsOf T numBefore mot)[i]? = some q →
  ∀ (xs ys : List V) (D B C : Expr) (ρq ρc : Nat → V),
    xs.length = numBefore → TeleFitV M φ base T xs →
    piBodyV base T (xs.take q) = some (.pi D B, ρq) →
    ys.length = rl.nfields → TeleFitV M φ ρq D ys →
    (piBodyV ρq D ys).map (fun p => conclV p.2 p.1) = some (C, ρc) →
    appList r (xs ++ C.args.map (interp M φ ρc)) = appList (interp M φ base rl.rhs) (xs ++ ys)

/-- **The constant `c`, stored as `ci`, holds in `M`**: at every list
of level values `vals`, one per level parameter, read through
`valOf ci.lparams vals`,

* the constant is a member of what its type denotes;
* a definition is what its value denotes;
* every rule of a recursor holds (`RuleHolds`), by its position.

An assumption (a theorem's statement, a hole) is membership only.  It
reads `c` alone. -/
def ModelOf (M : Name → List Nat → V) (c : Name) (ci : ConstInfo) : Prop :=
  ∀ vals : List Nat, vals.length = ci.lparams.length →
    M c vals ∈ˢ interp M (valOf ci.lparams vals) base ci.type ∧
    match ci.kind with
    | .defn v => M c vals = interp M (valOf ci.lparams vals) base v
    | .recursor nP nMot nMin _ rules => ∀ i rl, rules[i]? = some rl →
        RuleHolds M (valOf ci.lparams vals) (M c vals) ci.type (nP + nMot + nMin) i rl
    | _ => True

variable (V) in
/-- **`M` is a model of the constants `C`**: every one of them holds,
each on its own (`ModelOf`).  Of a list of declarations `ds`, it is a
model of `constantsOf ds` (`Modular.lean`). -/
def IsModel (M : Name → List Nat → V) (C : Name → ConstInfo → Prop) : Prop :=
  ∀ c ci, C c ci → ModelOf M c ci

end Fragment
