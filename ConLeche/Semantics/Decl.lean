module

public import ConLeche.Verify.Leaves
public import ConLeche.Verify.Denote.Install
import ConLeche.Kernel.Checker

@[expose] public section

/-!
# The per-declaration RUN records (task #148 T2)

The V-free records `checkDecl`'s per-kind checks produce: the `Nat`
recurrences' runs and the pinned basis install.  Every one is a
statement about the CHECKER — `isDefEqCore … = .ok true` — and
mentions no relation and no valuation.

**Statement conventions**: fuel and mode are carried as
`(μ, F)`; the annotate pass contributes no relation — its calls
(`annotateCore μ env F d e = .ok e'`) are V-free side conditions.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- The structural-`Nat` recurrences' **checker runs** (task #161 P4
H1, extended to the literal tier): `certifyNatEqs`'s verdict is the
conjunction of one `isDefEqCore` run per equation
(`ops.isDefEq env 2 eq.1 eq.2` under `fueledOps μ F`, i.e.
`isDefEqCore` at fuel `F`, depth `2`), so the recorded form is the
checker's literal output, one run per equation.  The model's
establishment route consumes these runs through `DefEqClaim`. -/
def NatEqsRun (μ : CheckMode) (F : Nat) (env : Env)
    (eqs : List (Expr × Expr)) : Prop :=
  ∀ eq ∈ eqs, isDefEqCore μ env F 2 eq.1 eq.2 = .ok true

/-- The pinned basis-block install (`checkDecl`'s basis branch): the
quot-requires-`Eq` guard and the freshness-checked fold. -/
def BasisInstallRun (env : Env) : List ConstantInfo → Env → Prop
  | [], env₂ => env₂ = env
  | ci :: rest, env₂ =>
    (env.find? ci.name).isNone = true ∧
    BasisInstallRun ⟨ci :: env.consts⟩ rest env₂

/-- A pinned basis block (design §1.5, `basis` row): side conditions
only — the pinned declarations are pre-annotated, and their semantic
content is proved once in the model (`Model/Basis*.lean`), not by
per-install premises. -/
def DeclBasisRun (env : Env) (kind : BasisKind) (env₂ : Env) : Prop :=
  (kind = .quotK → env.find? eqName = some eqA) ∧
  BasisInstallRun env kind.declsA env₂

end ConLeche.Semantics
