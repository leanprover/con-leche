import Setlec.NbE.Value

/-!
# NbE pilot: the environment machine

Fueled evaluation of terms into values.  β never touches syntax: a
redex is discharged by evaluating the closure body in an *extended
environment* (`applyV`).  δ is glued: `eval` of a constant yields the
neutral spine head immediately; `unfoldNeu` recomputes the unfolded
face only when conversion or head-forcing demands it.

Fuel conventions (arena style): `none` is *fuel exhaustion or an
internal error*, never a verdict.  All functions consume fuel
monotonically; the front door supplies a generous budget.

`quote` is the readback: values to terms, fresh variables (levels) to
de Bruijn indices.  On a glued neutral it reads back the *spine* —
readback never unfolds a definition, which is the gluing payoff for
cheap type reconstruction (`infer` of a λ quotes the body's inferred
type value to re-close it as a Π).
-/

namespace Setlec.NbE

mutual

/-- Evaluate a term in a value environment (`ρ` innermost-first). -/
def eval (E : Env) : Nat → List Value → Term → Option Value
  | 0, _, _ => none
  | _ + 1, ρ, .bvar i => ρ[i]?
  | _ + 1, _, .sort u => some (.sort u)
  | _ + 1, _, .const n us =>
    match E.lookup n with
    | some ci =>
      if ci.lvlParams.length = us.length then some (.neu (.const n us) []) else none
    | none => none
  | fuel + 1, ρ, .app f a =>
    match eval E fuel ρ f, eval E fuel ρ a with
    | some vf, some va => applyV E fuel vf va
    | _, _ => none
  | fuel + 1, ρ, .lam d b =>
    match eval E fuel ρ d with
    | some vd => some (.lam vd (.mk ρ b))
    | none => none
  | fuel + 1, ρ, .pi d b =>
    match eval E fuel ρ d with
    | some vd => some (.pi vd (.mk ρ b))
    | none => none
termination_by fuel _ _ => (fuel, 0)

/-- Apply a value to a value.  β = evaluate the closure body in the
extended environment; a neutral grows its spine. -/
def applyV (E : Env) : Nat → Value → Value → Option Value
  | 0, _, _ => none
  | fuel + 1, .lam _ (.mk ρ b), a => eval E fuel (a :: ρ) b
  | _ + 1, .neu h args, a => some (.neu h (args ++ [a]))
  | _ + 1, _, _ => none
termination_by fuel _ _ => (fuel, 1)

end

/-- Apply a closure to an argument value. -/
def applyCl (E : Env) (fuel : Nat) : Closure → Value → Option Value
  | .mk ρ b, a => eval E fuel (a :: ρ) b

/-- Apply a value to a spine of arguments, left to right. -/
def applyArgs (E : Env) (fuel : Nat) : Value → List Value → Option Value
  | v, [] => some v
  | v, a :: as =>
    match applyV E fuel v a with
    | some w => applyArgs E fuel w as
    | none => none

/-- The δ-unfolded face of a glued neutral: evaluate the definition's
value at the spine's level arguments and re-apply the spine. -/
def unfoldNeu (E : Env) (fuel : Nat) (n : Name) (us : List Level)
    (args : List Value) : Option Value :=
  match E.lookup n with
  | some ci =>
    match eval E fuel [] (ci.value.instL ci.lvlParams us) with
    | some v => applyArgs E fuel v args
    | none => none
  | none => none

/-- Force a value to a rigid head form: unfold glued neutrals until a
sort, Π, λ, or fvar-headed neutral appears. -/
def forceV (E : Env) : Nat → Value → Option Value
  | 0, _ => none
  | fuel + 1, .neu (.const n us) args =>
    match unfoldNeu E fuel n us args with
    | some w => forceV E fuel w
    | none => none
  | _ + 1, v => some v

mutual

/-- Readback: quote a value at fresh-variable frontier `k` into a term.
Fresh variables (levels) become de Bruijn indices; glued neutrals read
back their spine — a definition is never unfolded by readback. -/
def quote (E : Env) : Nat → Nat → Value → Option Term
  | 0, _, _ => none
  | _ + 1, _, .sort u => some (.sort u)
  | fuel + 1, k, .pi d cl =>
    match quote E fuel k d, applyCl E fuel cl (freshV k) with
    | some td, some vb =>
      match quote E fuel (k + 1) vb with
      | some tb => some (.pi td tb)
      | none => none
    | _, _ => none
  | fuel + 1, k, .lam d cl =>
    match quote E fuel k d, applyCl E fuel cl (freshV k) with
    | some td, some vb =>
      match quote E fuel (k + 1) vb with
      | some tb => some (.lam td tb)
      | none => none
    | _, _ => none
  | fuel + 1, k, .neu h args =>
    match h with
    | .fvar l =>
      if l < k then quoteArgs E fuel k (.bvar (k - 1 - l)) args else none
    | .const n us => quoteArgs E fuel k (.const n us) args
termination_by fuel _ _ => (fuel, 0)

/-- Quote a spine onto an already-quoted head. -/
def quoteArgs (E : Env) (fuel k : Nat) : Term → List Value → Option Term
  | acc, [] => some acc
  | acc, a :: as =>
    match quote E fuel k a with
    | some ta => quoteArgs E fuel k (.app acc ta) as
    | none => none
termination_by _ as => (fuel, as.length + 1)

end

end Setlec.NbE
