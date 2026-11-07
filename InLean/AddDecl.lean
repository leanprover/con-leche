module

public import InLean.Inductives.Decl

/-!
# InLean: the entry points

`addDecl`, the twin of `Lean.Kernel.Environment.addDeclCore`: check a
`Lean.Declaration` with con-leche's checker (`InLean/CheckerC.lean`) and add
the constants it declares, as con-leche's fold step checks a record at the
view below it and then pushes what the record declares
(`ConLeche/Cached/Decls.lean`, `declStep`).  `kernelWhnf` and
`kernelIsDefEq` are the twins of `Kernel.whnf`/`Kernel.isDefEq`.
-/

@[expose] public section

namespace InLean

open Lean

/-- Run a check from a fresh per-declaration state. -/
def runC (x : CheckCM α) : Except CheckError α :=
  match x.run {} with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- The kinds' checks, at a declaration's own environment. -/
def checkDeclKindC (μ : CheckMode) (cfg : Config) (fe : FEnv) : Declaration → CheckCM Added
  | .axiomDecl v => checkAxiomC μ cfg fe v
  | .defnDecl v => checkDefnC μ cfg fe v
  | .thmDecl v => checkThmC μ fe v
  | .opaqueDecl v => checkOpaqueC μ fe v
  | .mutualDefnDecl vs => checkMutualC μ fe vs
  | .quotDecl => checkQuotC fe
  | .inductDecl lps nparams types isUnsafe => checkInductiveC μ fe lps nparams types isUnsafe

/-- A constant other than an axiom at `sorryAx`'s name.  At con-leche's axiom
policy (`coreAxioms` off) the name is hidden (`FEnv.sees`) and con-leche
installs nothing only for the axiom, so any other constant there is declined
(official's environments declare the axiom in `Init.Prelude`, so no stream
reaches this). -/
def sorryAxSquat (ci : ConstantInfo) : Bool :=
  ci.name == sorryAxName && !(ci matches .axiomInfo _)

/-- Check `decl` (twin of `declStep`: the `And` pin, then `checkDeclStepC`),
returning what it adds; at con-leche's axiom policy, no constant but the axiom
at `sorryAx`'s name (`sorryAxSquat`). -/
def checkDecl (cfg : Config) (env : Kernel.Environment) (decl : Declaration) :
    Except CheckError Added :=
  let fe : FEnv := { env, coreAxioms := cfg.coreAxioms }
  if !andPinOk decl then .error (.invalid "`And` must be the standard `And`") else
  runC do
    let a ← checkDeclKindC cfg.mode cfg fe decl
    if !cfg.coreAxioms && a.consts.any sorryAxSquat then
      throw (.notImplemented "a constant other than an axiom at `sorryAx`'s name")
    return a

/-- **Check `decl` and add the constants it declares** — the twin of
`Lean.Kernel.Environment.addDeclCore`.  A reject, a decline and an error
are each `Kernel.Exception.other`, the message prefixed `(InLean)` and, for a
decline, `declined:`. -/
def addDecl (env : Kernel.Environment) (decl : Declaration) (cfg : Config := {}) :
    Except Kernel.Exception Kernel.Environment :=
  match checkDecl cfg env decl with
  | .ok a =>
    let env := a.consts.foldl addConst env
    .ok (if a.quot then markQuot env else env)
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
