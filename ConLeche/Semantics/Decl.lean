module

import ConLeche.Verify.Leaves
public import ConLeche.Verify.Denote.Install
import ConLeche.Kernel.Checker

@[expose] public section

/-!
# The per-declaration RUN records (task #148 T2)

The V-free records `checkDecl`'s per-kind checks produce: the `Nat`
recurrences' runs and the pinned basis install.  Every one is a
statement about the CHECKER — `isDefEqCore … = .ok true` — and
mentions no relation and no valuation.

**Statement conventions**: the fuel is carried as `F`; the
mode is `.verified`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- The structural-`Nat` recurrences' **checker runs** (task #161 P4
H1, extended to the literal tier): `certifyNatEqs`'s verdict is the
conjunction of one `isDefEqCore` run per equation
(`ops.isDefEq env 2 eq.1 eq.2` under `fueledOps .verified F`, i.e.
`isDefEqCore` at fuel `F`, depth `2`), so the recorded form is the
checker's literal output, one run per equation.  The model's
establishment route consumes these runs through `DefEqClaim`. -/
def NatEqsRun (F : Nat) (env : Env)
    (eqs : List (Expr × Expr)) : Prop :=
  ∀ eq ∈ eqs, isDefEqCore .verified false env F 2 eq.1 eq.2 = .ok true

/-- The pinned basis-block install (`checkDecl`'s basis branch): the
quot-requires-`Eq` guard and the freshness-checked fold. -/
def BasisInstallRun (env : Env) : List ConstantInfo → Env → Prop
  | [], env₂ => env₂ = env
  | ci :: rest, env₂ =>
    (env.find? ci.name).isNone = true ∧
    BasisInstallRun ⟨ci :: env.consts, env.tables⟩ rest env₂

/-- A pinned basis block (design §1.5, `basis` row): the comparison with
the pin, and each pin stored at the names its record declares.  Their
semantic content is proved once in the model (`Model/Basis*.lean`), not
by per-install premises. -/
def DeclBasisRun (env : Env) (kind : BasisKind) (block : List ConstantInfo) (env₂ : Env) : Prop :=
  pinListOk block kind.decls = true ∧ BasisInstallRun env (kind.atBlock block) env₂

/-- A quotient record: the comparison with its slot's pin, the slots it
needs stored, and the slot's constant stored at the record's names. -/
def DeclQuotRun (env : Env) (k : QuotKind) (cv : ConstantVal) (env₂ : Env) : Prop :=
  quotPinHit k cv = true ∧ quotPredsOk env.find? k cv.levelParams = true ∧
    (env.find? (quotAt k cv).name).isNone = true ∧
    env₂ = ⟨quotAt k cv :: env.consts, env.tables⟩

end ConLeche.Semantics
