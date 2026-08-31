import Setlec.NbE.Eval

/-!
# NbE pilot: conversion

Definitional equality on *values*, untyped (the realism constraint: no
typing information is consulted after the front door, no certificates
are produced).

* Sorts compare by the campaign's own `Level.isEquiv` (params,
  `max`/`imax` — the real thing, not a simplification).
* Binders (Π, λ) compare domains, then bodies with both closures
  applied to the *same* fresh untyped variable (de Bruijn level `k`).
* Glued neutrals with equal constant heads try the **spine-equality
  shortcut** first: equivalent level lists and pairwise-convertible
  spines decide `true` *without unfolding*.  A failed shortcut is not a
  verdict — both sides are unfolded (δ) and compared again.  A glued
  neutral against anything else unfolds the glued side.
* No η in this slice (λ vs. neutral is `false`); no proof irrelevance
  (second-slice questions, see the pilot memo).

`none` = fuel exhaustion / internal error, never a verdict; soundness
claims speak only about `some true`.
-/

namespace Setlec.NbE

mutual

/-- Conversion at fresh-variable frontier `k`. -/
def conv (E : Env) : Nat → Nat → Value → Value → Option Bool
  | 0, _, _, _ => none
  | fuel + 1, k, v, w =>
    match v, w with
    | .sort u, .sort u' => Level.isEquiv u u'
    | .pi d cl, .pi d' cl' => convBinder E fuel k d cl d' cl'
    | .lam d cl, .lam d' cl' => convBinder E fuel k d cl d' cl'
    | .neu (.fvar l) args, .neu (.fvar l') args' =>
      if l = l' then convArgs E fuel k args args' else some false
    | .neu (.const n us) args, .neu (.const n' us') args' =>
      if n = n' then
        match Level.isEquivList us us' with
        | some true =>
          match convArgs E fuel k args args' with
          | some true => some true
          | some false => convDelta E fuel k n us args n' us' args'
          | none => none
        | some false => convDelta E fuel k n us args n' us' args'
        | none => none
      else convDelta E fuel k n us args n' us' args'
    | .neu (.const n us) args, w =>
      match unfoldNeu E fuel n us args with
      | some x => conv E fuel k x w
      | none => none
    | v, .neu (.const n us) args =>
      match unfoldNeu E fuel n us args with
      | some y => conv E fuel k v y
      | none => none
    | _, _ => some false
termination_by fuel _ _ _ => (fuel, 0)

/-- Domains, then bodies under a shared fresh variable. -/
def convBinder (E : Env) (fuel k : Nat) (d : Value) (cl : Closure)
    (d' : Value) (cl' : Closure) : Option Bool :=
  match conv E fuel k d d' with
  | some true =>
    match applyCl E fuel cl (freshV k), applyCl E fuel cl' (freshV k) with
    | some vb, some vb' => conv E fuel (k + 1) vb vb'
    | _, _ => none
  | r => r
termination_by (fuel, 1)

/-- δ: unfold both glued sides and compare the unfoldings. -/
def convDelta (E : Env) (fuel k : Nat) (n : Name) (us : List Level)
    (args : List Value) (n' : Name) (us' : List Level)
    (args' : List Value) : Option Bool :=
  match unfoldNeu E fuel n us args, unfoldNeu E fuel n' us' args' with
  | some x, some y => conv E fuel k x y
  | _, _ => none
termination_by (fuel, 1)

/-- Pairwise spine conversion (`false` on length mismatch). -/
def convArgs (E : Env) : Nat → Nat → List Value → List Value → Option Bool
  | _, _, [], [] => some true
  | fuel, k, a :: as, b :: bs =>
    match conv E fuel k a b with
    | some true => convArgs E fuel k as bs
    | r => r
  | _, _, _, _ => some false
termination_by fuel _ as _ => (fuel, as.length + 2)

end

end Setlec.NbE
