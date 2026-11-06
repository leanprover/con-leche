module

public import InLean.IndCheck.Block
/- `Lean.Kernel.Environment.add` and `markQuotInit` are private to
`Lean.Environment`: inside core, the kernel would call them directly;
here `import all` stands in for being part of that module (task #451).
The bodies that use them are therefore not exposed (`public section`,
not `@[expose]`). -/
import all Lean.Environment

/-!
# InLean: the entry points

Task #451.  `addDecl`, the twin of `Lean.Kernel.Environment.addDeclCore`:
check a `Lean.Declaration` with con-leche's checker (`InLean/Decl.lean`)
and add the constants it declares.  `kernelWhnf` and `kernelIsDefEq` are the twins
of `Kernel.whnf`/`Kernel.isDefEq`.

Every declaration kind is InLean's own.  An inductive declaration goes to
`IC.checkInductiveDecl` (`InLean/IndCheck/Block.lean`): the unverified
generator (`InLean/IndGen.lean`) produces the inductive types',
constructors' and recursors' constants, and con-leche's installer and
checked job (`InLean/IndCheck/*`) decide on them.
-/

public section

namespace InLean

open Lean

/-- Add a constant to a kernel environment, unchecked (core's private
`Kernel.Environment.add`). -/
def addConst (env : Kernel.Environment) (ci : ConstantInfo) : Kernel.Environment :=
  env.add ci

/-- The InLean configuration: the mode (verified by default). -/
structure Config where
  mode : CheckMode := .verified
  /-- measurement probe, see `Ctx.probeNoMemo` -/
  probeNoMemo : String := ""
  /-- the axiom policy, see `Ctx.coreAxioms` -/
  coreAxioms : Bool := false
  /-- the Nat-operation stopgap, see `Ctx.uncertifiedNatOps` (on by
  default; the simulation theorem's configuration turns it off) -/
  uncertifiedNatOps : Bool := true

/-- Run a check in a fresh per-declaration state. -/
def runM (env : Kernel.Environment) (x : M α) (probe : String := "")
    (coreAxioms : Bool := false) (uncertifiedNatOps : Bool := true) : Except Err α :=
  match (x.run { env, probeNoMemo := probe, coreAxioms, uncertifiedNatOps }).run {} with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- Check `decl`, returning what it adds. -/
def checkDecl (cfg : Config) (env : Kernel.Environment) (decl : Declaration) :
    Except Err Added :=
  let μ := cfg.mode
  runM env (do
    match decl with
    | .axiomDecl v => checkAxiom μ v
    | .defnDecl v => checkDefn μ addConst v
    | .thmDecl v => checkThm μ v
    | .opaqueDecl v => checkOpaque μ addConst v
    | .mutualDefnDecl vs => checkMutual μ addConst vs
    | .quotDecl => checkQuot
    | .inductDecl lps nparams types isUnsafe =>
      IC.checkInductiveDecl μ addConst lps nparams types isUnsafe)
    cfg.probeNoMemo cfg.coreAxioms cfg.uncertifiedNatOps

/-- **Check `decl` and add the constants it declares** — the twin of
`Lean.Kernel.Environment.addDeclCore`.  A reject, a decline and an
internal error are all `Kernel.Exception.other` (ruling 7), the message
prefixed `(InLean)` and, for a decline, `declined:`. -/
def addDecl (env : Kernel.Environment) (decl : Declaration) (cfg : Config := {}) :
    Except Kernel.Exception Kernel.Environment :=
  match checkDecl cfg env decl with
  | .ok a =>
    let env := a.consts.foldl addConst env
    .ok (if a.quot then env.markQuotInit else env)
  | .error e => .error (.other e.toString)

/-- The twin of `Kernel.whnf` (a closed term; full reduction). -/
def kernelWhnf (env : Kernel.Environment) (e : Expr) (cfg : Config := {}) : Except Kernel.Exception Expr :=
  match runM env (InLean.whnf cfg.mode 0 e) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

/-- The twin of `Kernel.isDefEq` (closed terms). -/
def kernelIsDefEq (env : Kernel.Environment) (a b : Expr) (cfg : Config := {}) :
    Except Kernel.Exception Bool :=
  match runM env (InLean.defeq cfg.mode 0 a b) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

end InLean
