import Setlec.Kernel.Level

/-!
# NbE pilot (task #159): syntax

A minimal term language for the NbE / environment-machine regime pilot:
Π, λ, application, sorts with full universe polymorphism (the campaign's
own `Level` type and comparison), de Bruijn *indices* for bound
variables, and constants drawn from an environment of definitions.

Two deliberate absences, which are the regime's whole point:

* **No `fvar` constructor.**  Fresh variables exist only at the *value*
  level (`Setlec.NbE.Value`), created during conversion/readback as de
  Bruijn levels.  Input terms are closed.
* **No lifting and no substitution.**  This module defines no `liftN`,
  no `inst`, no `abstract`.  β is closure application in the evaluator;
  the term syntax is never rewritten.

The one substitution-shaped operation that *does* remain is
`Term.instL`: level instantiation at δ-unfolding and constant-type
lookup, exactly as in the official kernel and nanoda.  Universe levels
are not term variables — no binder in the term language binds them — so
this does not reintroduce the term-substitution transport problem; its
(unconditional) transport lemma is `Setlec.NbE.dTerm_instL` in the
verification tier.

Levels are the campaign's own `Setlec.Level` (params, `max`, `imax`,
`isEquiv`), imported from the kernel implementation — not simplified
away, per the pilot charter.
-/

namespace Setlec.NbE

/-- Terms.  Closed input syntax: `bvar` de Bruijn indices only. -/
inductive Term where
  | bvar (i : Nat)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Term)
  | lam (dom body : Term)
  | pi (dom body : Term)
  deriving DecidableEq, Repr, Inhabited

/-- Level instantiation: replace the level parameters `ks` by `us`
throughout (sorts and constant level arguments).  Applied once per
δ-unfold / constant-type lookup; the only syntax traversal the
checker performs. -/
def Term.instL (ks : List Name) (us : List Level) : Term → Term
  | .bvar i => .bvar i
  | .sort u => .sort (Level.subst ks us u)
  | .const n vs => .const n (vs.map (Level.subst ks us))
  | .app f a => .app (f.instL ks us) (a.instL ks us)
  | .lam d b => .lam (d.instL ks us) (b.instL ks us)
  | .pi d b => .pi (d.instL ks us) (b.instL ks us)

/-- Are all level parameters occurring in `t` among `params`?
Front-door check; the verification tier needs it so that a constant's
denotation depends only on its declared parameters. -/
def Term.lvlDefined (params : List Name) : Term → Bool
  | .bvar _ => true
  | .sort u => u.allParamsDefined params
  | .const _ us => us.all (Level.allParamsDefined params)
  | .app f a => f.lvlDefined params && a.lvlDefined params
  | .lam d b | .pi d b => d.lvlDefined params && b.lvlDefined params

/-- A checked constant: a *definition* (type and value).  The pilot
environment holds definitions only — every constant unfolds (δ), so the
glued evaluator never meets an opaque constant, and the environment
denotation is total.  (Axioms/opaques would puncture the consistency
story and are out of the slice.) -/
structure ConstInfo where
  name : Name
  lvlParams : List Name
  type : Term
  value : Term
  deriving DecidableEq, Repr

/-- The environment: newest constant first.  A definition's value may
mention only *earlier* (deeper-in-the-list) constants; the front door
enforces this by checking against the environment-so-far. -/
structure Env where
  consts : List ConstInfo := []
  deriving DecidableEq, Repr

def Env.lookup (E : Env) (n : Name) : Option ConstInfo :=
  E.consts.find? (·.name == n)

/-- Install a checked constant (front of the list). -/
def Env.push (E : Env) (ci : ConstInfo) : Env := ⟨ci :: E.consts⟩

end Setlec.NbE
