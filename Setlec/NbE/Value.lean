import Setlec.NbE.Term

/-!
# NbE pilot: values

The value domain of the environment machine.

* Closures are **defunctionalized**: a captured environment (list of
  values for the de Bruijn indices of the body) plus the unevaluated
  body term.  This keeps `Value` a first-order inductive the
  verification tier can recurse over.
* Neutral values carry a head (a fresh variable as a de Bruijn *level*,
  or a constant with its level arguments) and the argument spine.
* **Gluing** (the smalltt / NbE-arena shape): a constant-headed neutral
  *is* the glued value — the spine is the cheap face (readback never
  unfolds; conversion tries spine equality first), and the δ-unfolded
  face is produced on demand by `unfoldNeu` (evaluate the definition's
  value at the spine's levels, re-apply the spine).

  **Finding (representation):** carrying the unfolded face *inside* the
  value as a lazy thunk (`Thunk (Option Value)` — the memoizing variant
  smalltt/sokonanoda use) makes `Value` a reflexive inductive
  (`Unit → Option Value` field), for which Lean cannot derive `SizeOf`,
  killing every recursion the verification tier needs.  The pilot
  therefore *recomputes* the unfolding at each force; the thunk is a
  cache a production implementation would add behind the same
  interface.  Verification-side, the recompute variant is strictly
  simpler: the δ-coherence lemma speaks directly about `eval`, and no
  "every thunk in every reachable value is pedigreed" invariant (a
  fuel-indexed value-wellformedness tier) needs to be threaded through
  the evaluator.  That invariant is the price tag of cached gluing.

Fresh variables are **untyped**: a de Bruijn level and nothing else.
No sort, no type value.  Conversion runs on values without consulting
any typing — the realism constraint of the pilot.  (Where the
*soundness proof* then needs typing facts is exactly what the
verification tier charts.)
-/

namespace Setlec.NbE

/-- Head of a neutral value. -/
inductive Head where
  | fvar (lvl : Nat)
  | const (n : Name) (us : List Level)
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Values.  `neu h args`: the head applied to the spine `args` (oldest
first).  A constant-headed neutral is a *glued* value: `unfoldNeu`
recovers its δ-unfolded face on demand. -/
inductive Value where
  | sort (u : Level)
  | pi (dom : Value) (cl : Closure)
  | lam (dom : Value) (cl : Closure)
  | neu (h : Head) (args : List Value)

/-- A closure: captured environment plus unevaluated body. -/
inductive Closure where
  | mk (env : List Value) (body : Term)
end

instance : Inhabited Value := ⟨.sort .zero⟩
instance : Inhabited Closure := ⟨.mk [] (.sort .zero)⟩

/-- The captured environment of a closure. -/
def Closure.env : Closure → List Value
  | .mk ρ _ => ρ

/-- The body of a closure. -/
def Closure.body : Closure → Term
  | .mk _ b => b

/-- A fresh (untyped!) variable at de Bruijn level `k`. -/
def freshV (k : Nat) : Value := .neu (.fvar k) []

/-- The environment `[freshV (k-1), …, freshV 0]`: de Bruijn index `i`
refers to the fresh variable at level `k - 1 - i`.  Used to re-close a
quoted term over an ambient telescope of fresh variables. -/
def freshEnv (k : Nat) : List Value := (List.range k).reverse.map freshV

end Setlec.NbE
