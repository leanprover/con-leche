module

public import InLean.CheckerC
/- `Lean.Kernel.Environment.add` and `markQuotInit` are private to
`Lean.Environment`: inside core, the kernel calls them directly; here
`import all` stands in for being part of that module.  The bodies that
use them are therefore not exposed (`public section`, not `@[expose]`). -/
import all Lean.Environment

/-!
# InLean: the entry points

`addDecl`, the twin of `Lean.Kernel.Environment.addDeclCore`: check a
`Lean.Declaration` with con-leche's checker (`InLean/CheckerC.lean`) and add
the constants it declares, as con-leche's fold step checks a record at the
view below it and then pushes what the record declares
(`ConLeche/Cached/Decls.lean`, `declStep`).  `kernelWhnf` and
`kernelIsDefEq` are the twins of `Kernel.whnf`/`Kernel.isDefEq`.
-/

public section

namespace InLean

open Lean

/-- Add a constant to a kernel environment, unchecked (core's private
`Kernel.Environment.add`). -/
def addConst (env : Kernel.Environment) (ci : ConstantInfo) : Kernel.Environment :=
  env.add ci

/-- Run a check from a fresh per-declaration state. -/
def runC (x : CheckCM α) : Except CheckError α :=
  match x.run {} with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- Check `decl` (twin of `checkDeclStepC`), returning what it adds. -/
def checkDecl (cfg : Config) (env : Kernel.Environment) (decl : Declaration) :
    Except CheckError Added :=
  let μ := cfg.mode
  let fe : FEnv := { env, coreAxioms := cfg.coreAxioms }
  runC do
    match decl with
    | .axiomDecl v => checkAxiomC μ cfg fe v
    | .defnDecl v => checkDefnC μ cfg addConst fe v
    | .thmDecl v => checkThmC μ fe v
    | .opaqueDecl v => checkOpaqueC μ addConst fe v
    | .mutualDefnDecl vs => checkMutualC μ addConst fe vs
    | .quotDecl => checkQuotC fe
    | .inductDecl .. => throw (.internal "inductive declarations: see `addDecl`")

/-- **Check `decl` and add the constants it declares** — the twin of
`Lean.Kernel.Environment.addDeclCore`.  A reject, a decline and an error
are each `Kernel.Exception.other`, the message prefixed `(InLean)` and, for a
decline, `declined:`. -/
def addDecl (env : Kernel.Environment) (decl : Declaration) (cfg : Config := {}) :
    Except Kernel.Exception Kernel.Environment :=
  -- TEMPORARY (the restart, before the inductive job's port): the official kernel
  if decl matches .inductDecl .. then env.addDeclCore 0 0 decl none else
  match checkDecl cfg env decl with
  | .ok a =>
    let env := a.consts.foldl addConst env
    .ok (if a.quot then env.markQuotInit else env)
  | .error e => .error (.other e.toString)

/-- The twin of `Kernel.whnf` (a closed term; full reduction). -/
def kernelWhnf (env : Kernel.Environment) (e : Expr) (cfg : Config := {}) :
    Except Kernel.Exception Expr :=
  match runC (opWhnf cfg.mode { env, coreAxioms := cfg.coreAxioms } 0 e) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

/-- The twin of `Kernel.isDefEq` (closed terms). -/
def kernelIsDefEq (env : Kernel.Environment) (a b : Expr) (cfg : Config := {}) :
    Except Kernel.Exception Bool :=
  match runC (opDefeq cfg.mode { env, coreAxioms := cfg.coreAxioms } 0 a b) with
  | .ok r => .ok r
  | .error err => .error (.other err.toString)

end InLean
