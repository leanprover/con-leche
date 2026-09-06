import Setlec.Kernel.Core
import Setlec.Verify.Level
import Setlec.SetModel.Ops

/-!
# `Sem` — the set interpretation of a checker term, as a relation

`Sem cval env φ d ρ e v` says: the checker term `e` denotes the set `v`,
given a set `cval n ψ` for every constant `n` at every level assignment
`ψ`.  It is the composite of the two-stage reading the proofs use
(`denoteP`, which resolves constants and reads binder annotations into
an `AVExpr`, then `interp2`, which interprets that), written as one
syntax-directed relation on `Expr` so that a statement about the model
needs nothing but these rules and the set operations they name.
`Setlec/SetP/SemP.lean` proves the rules agree with `interp2` of
`denoteP`'s reading wherever that reads, and that they are functional.

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
* A literal denotes what its constructor form denotes, the checker's own
  `natLitToConstructor` (one `Nat.succ` layer) and `strLitToConstructor`.
* A term that does not resolve — an unknown constant, a wrong universe
  arity, a projection out of range — has no rule, hence no denotation.
-/

namespace Setlec.Semantics

open Setlec (Env Expr Name Level PropWhen Literal BinderMeta)
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

/-- Field `i` of a nested pair: `sfst ∘ ssnd^i`. -/
noncomputable def projV : Nat → V → V
  | 0, p => sfst p
  | i + 1, p => projV i (ssnd p)

/-- The interpretation.  See the module docstring. -/
inductive Sem (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) :
    Nat → (Nat → V) → Expr → V → Prop
  | sort {d : Nat} {ρ : Nat → V} {u : Level} :
      Sem cval env φ d ρ (.sort u) (univ (Level.eval φ u))
  | fvar {d : Nat} {ρ : Nat → V} {idx : Nat} {n : Name} {ty : Expr} :
      Sem cval env φ d ρ (.fvar idx n ty) (ρ (d - 1 - idx))
  | const {d : Nat} {ρ : Nat → V} {n : Name} {us : List Level} {ci : ConstantInfo}
      (hf : env.find? n = some ci)
      (hlen : us.length = ci.toConstantVal.levelParams.length) :
      Sem cval env φ d ρ (.const n us)
        (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
  | pi {d : Nat} {ρ : Nat → V} {n : Name} {ty body : Expr} {m : BinderMeta}
      {A : V} {B : V → V}
      (hA : Sem cval env φ d ρ ty A)
      (hB : ∀ x, Sem cval env φ (d + 1) (push x ρ) (body.instantiate1 (.fvar d n ty)) (B x)) :
      Sem cval env φ d ρ (.forallE n ty body m) (piR (regime φ m.pw) A B)
  | lam {d : Nat} {ρ : Nat → V} {n : Name} {ty body : Expr} {m : BinderMeta}
      {A : V} {F : V → V}
      (hA : Sem cval env φ d ρ ty A)
      (hF : ∀ x, Sem cval env φ (d + 1) (push x ρ) (body.instantiate1 (.fvar d n ty)) (F x)) :
      Sem cval env φ d ρ (.lam n ty body m) (lamR (regime φ m.pw) A F)
  | app {d : Nat} {ρ : Nat → V} {f a : Expr} {F X : V}
      (hf : Sem cval env φ d ρ f F) (ha : Sem cval env φ d ρ a X) :
      Sem cval env φ d ρ (.app f a) (SetTheory.app F X)
  | letE {d : Nat} {ρ : Nat → V} {n : Name} {ty val body : Expr} {X Y : V}
      (hv : Sem cval env φ d ρ val X)
      (hb : Sem cval env φ (d + 1) (push X ρ) (body.instantiate1 (.fvar d n ty)) Y) :
      Sem cval env φ d ρ (.letE n ty val body) Y
  | projTower {d : Nat} {ρ : Nat → V} {sn : Name} {i : Nat} {e : Expr} {entry : ProjEntry}
      {P : V}
      (ht : env.findProj? sn i = some entry) (he : Sem cval env φ d ρ e P) :
      Sem cval env φ d ρ (.proj sn i e) (projV i P)
  | projFst {d : Nat} {ρ : Nat → V} {sn : Name} {e : Expr} {P : V}
      (ht : env.findProj? sn 0 = none) (he : Sem cval env φ d ρ e P) :
      Sem cval env φ d ρ (.proj sn 0 e) (sfst P)
  | projSnd {d : Nat} {ρ : Nat → V} {sn : Name} {e : Expr} {P : V}
      (ht : env.findProj? sn 1 = none) (he : Sem cval env φ d ρ e P) :
      Sem cval env φ d ρ (.proj sn 1 e) (ssnd P)
  | natLit {d : Nat} {ρ : Nat → V} {k : Nat} {X : V}
      (h : Sem cval env φ d ρ (natLitToConstructor k) X) :
      Sem cval env φ d ρ (.lit (.natVal k)) X
  | strLit {d : Nat} {ρ : Nat → V} {s : String} {X : V}
      (h : Sem cval env φ d ρ (strLitToConstructor s) X) :
      Sem cval env φ d ρ (.lit (.strVal s)) X

end Setlec.Semantics
