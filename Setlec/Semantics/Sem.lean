import Setlec.Kernel.ExprOps
import Setlec.Kernel.Basis.Names
import Setlec.Verify.Level
import Setlec.SetModel.Ops

/-!
# `sem` — the set interpretation of a checker term, in one function

`sem cval env φ d ρ e` is the set a checker term `e` denotes, given a set
`cval n ψ` for every constant `n` at every level assignment `ψ`.  It is
the composite of the two-stage reading the proofs use (`denoteP`, which
resolves constants and reads binder annotations into an `AVExpr`, then
`interp2`, which interprets that), written directly on `Expr` so that a
statement about the model needs nothing but this definition and the set
operations it names.  `Setlec/SetP/SemP.lean` proves the two agree
wherever `denoteP` reads.

* `φ` assigns a natural to every universe parameter; `Sort u` denotes the
  universe `univ (u.eval φ)`.
* `d` is the number of enclosing binders and `ρ` their values by de Bruijn
  index; the checker's open variables are `fvar idx` by *level*, so a
  leaf reads `ρ (d - 1 - idx)`, and a binder opens its body with the
  fresh variable `fvar d` and pushes the bound value onto `ρ`.
* A binder's regime — `piR`/`lamR` at `0` is the truth-value regime, at
  `1` the function-graph regime — is read off the binder's validated
  annotation `m.pw` at `φ`: `0` exactly when the annotation says the
  body is a proposition there.  No type inference.
* Anything that does not resolve — an unknown constant, a wrong universe
  arity, a projection out of range — denotes the empty set, which no
  value is a member of.
-/

namespace Setlec.Semantics

open Setlec (Env Expr Name Level PropWhen Literal)
open Setlec.SetModel
open Setlec.SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- Extend a variable environment with a new innermost binding. -/
def push (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

/-- The binder regime at `φ`: `0` (truth values) exactly when the
validated annotation says the body is a proposition at `φ`. -/
def regime (φ : Name → Nat) (pw : PropWhen) : Nat :=
  if pw.holds φ then 0 else 1

/-- The universe parameters of a stored constant (`[]` if absent). -/
def levelParamsOf (env : Env) (n : Name) : List Name :=
  match env.find? n with
  | some ci => ci.toConstantVal.levelParams
  | none => []

/-- The `Nat` literal `k` as `succ^k zero` over the given sets. -/
noncomputable def natLitV (z s : V) : Nat → V
  | 0 => z
  | k + 1 => SetTheory.app s (natLitV z s k)

/-- A character list as `cons (ofNat ⌜c⌝) …` over the given sets. -/
noncomputable def charListV (nil cons ofNat z s : V) : List Char → V
  | [] => nil
  | c :: cs =>
    SetTheory.app (SetTheory.app cons (SetTheory.app ofNat (natLitV z s c.toNat)))
      (charListV nil cons ofNat z s cs)

/-- Field `i` of a nested pair: `sfst ∘ ssnd^i`. -/
noncomputable def projV : Nat → V → V
  | 0, p => sfst p
  | i + 1, p => projV i (ssnd p)

/-- The interpretation.  See the module docstring. -/
noncomputable def sem (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) :
    Nat → (Nat → V) → Expr → V
  | _, _, .sort u => univ (Level.eval φ u)
  | d, ρ, .fvar idx _ _ => ρ (d - 1 - idx)
  | _, _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        cval n (Level.substFn φ ci.toConstantVal.levelParams us)
      else SetTheory.empty
    | none => SetTheory.empty
  | d, ρ, .forallE n ty body m =>
    piR (regime φ m.pw) (sem cval env φ d ρ ty)
      (fun x => sem cval env φ (d + 1) (push x ρ) (body.instantiate1 (.fvar d n ty)))
  | d, ρ, .lam n ty body m =>
    lamR (regime φ m.pw) (sem cval env φ d ρ ty)
      (fun x => sem cval env φ (d + 1) (push x ρ) (body.instantiate1 (.fvar d n ty)))
  | d, ρ, .app f a => SetTheory.app (sem cval env φ d ρ f) (sem cval env φ d ρ a)
  | d, ρ, .letE n ty val body =>
    sem cval env φ (d + 1) (push (sem cval env φ d ρ val) ρ)
      (body.instantiate1 (.fvar d n ty))
  | d, ρ, .proj sn i e =>
    match env.findProj? sn i with
    | some _ => projV i (sem cval env φ d ρ e)
    | none =>
      if i < 2 then
        (if i = 0 then sfst (sem cval env φ d ρ e) else ssnd (sem cval env φ d ρ e))
      else SetTheory.empty
  | _, _, .lit (.natVal k) =>
    natLitV (cval natZeroName (Level.substFn φ [] []))
      (cval natSuccName (Level.substFn φ [] [])) k
  | _, _, .lit (.strVal s) =>
    SetTheory.app (cval stringOfListName (Level.substFn φ [] []))
      (charListV
        (SetTheory.app (cval listNilName
            (Level.substFn φ (levelParamsOf env listNilName) [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (SetTheory.app (cval listConsName
            (Level.substFn φ (levelParamsOf env listConsName) [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (cval charOfNatName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] []))
        (cval natSuccName (Level.substFn φ [] []))
        s.toList)
  | _, _, .bvar _ => SetTheory.empty
termination_by _ _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end Setlec.Semantics
