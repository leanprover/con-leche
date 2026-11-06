module

public import InLean.CheckerC

/-!
# InLean: the inductive declaration's monad

An inductive declaration is generated (`InLean/IndGen.lean`, unverified, the
official kernel's construction) and then checked by con-leche's inductive
job (`InLean/IndCheck/*`).  Both run in `M`: the core's `CheckCM` under the
declaration's context (`Ctx`: the environment a stage reads, which grows
as the stages add the block's constants, and the declaration's safety and
policy) and the generator's local context (`IState`).

The entry points the stages call are the core's (`opInfer` …) at the
context's environment.  An environment transition flushes the core's
memos (`withEnv`), as con-leche's block stages do (`flushC`).
-/

@[expose] public section

namespace InLean

open Lean

/-- The inductive declaration's context. -/
structure Ctx where
  env : Kernel.Environment
  safety : DefinitionSafety := .safe
  coreAxioms : Bool := false

/-- The context's environment for the core. -/
def Ctx.fe (c : Ctx) : FEnv := { env := c.env, safety := c.safety, coreAxioms := c.coreAxioms }

/-- The generator's local context: its depth (one local per depth), each
local's binder name and info, and a counter for fresh names. -/
structure IState where
  gdepth : Nat := 0
  fvNames : Std.HashMap Nat (Name × BinderInfo) := {}
  nestCtr : Nat := 0

/-- The inductive declaration's monad. -/
abbrev M := ReaderT Ctx (StateT IState CheckCM)

@[inline] def throwInvalid (msg : String) : M α := throw (.invalid msg)
@[inline] def throwDeclined (msg : String) : M α := throw (.notImplemented msg)
@[inline] def throwInternal (msg : String) : M α := throw (.internal msg)

/-- Run `x` at the environment `env`, the core's memos flushed (an
environment transition). -/
def withEnv (env : Kernel.Environment) (x : M α) : M α := do
  (flushC : CheckCM Unit)
  withReader (fun c => { c with env }) x

/-- The core's entry points at the context's environment. -/
def infer (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := do
  (opInfer μ (← read).fe d e : CheckCM Expr)
def defeq (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  (opDefeq μ (← read).fe d a b : CheckCM Bool)
def whnf (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := do
  (opWhnf μ (← read).fe d e : CheckCM Expr)
def ensureSort (μ : CheckMode) (d : Nat) (e : Expr) : M Level := do
  (opSort μ (← read).fe d e : CheckCM Level)

/-- The interned free variable at depth `d` of type `ty`. -/
def mkFVar (d : Nat) (ty : Expr) : M Expr := (mkFVarM d ty : CheckCM Expr)

/-- An interned free variable's type and depth. -/
def fvarInfo? (id : FVarId) : M (Option (Expr × Nat)) := do
  match fvParts? id with
  | some (d, _) =>
    match ← (fvarTypeM? id : CheckCM (Option Expr)) with
    | some ty => return some (ty, d)
    | none => return none
  | none => return none

/-- Level equivalence (an exhausted comparison declines, `liftFueled`). -/
def isEquivL (l r : Level) : M Bool := do
  let o ← (isEquivLM l r : CheckCM (Option Bool))
  (liftFueled "level comparison" o : CheckCM Bool)

/-- Pointwise `isEquivL`. -/
def isEquivListL (ls rs : List Level) : M Bool := do
  let o ← (isEquivListLM ls rs : CheckCM (Option Bool))
  (liftFueled "level comparison" o : CheckCM Bool)

/-- Twin of `checkConstantValF`: a block member's constant check. -/
def checkConstantVal (μ : CheckMode) (n : Name) (lps : List Name) (ty : Expr) : M Unit := do
  (checkConstantValC μ (← read).fe n lps ty : CheckCM Unit)

/-- A term's syntactic gates (`checkTermWF`). -/
def checkExprWF (what : String) (lps : List Name) (e : Expr) : M Unit := do
  (checkTermWF (← read).fe what lps e : CheckCM Unit)

/-- The level-instantiated type of a stored constant (`constTyAtM`). -/
def constTyAt (ci : ConstantInfo) (us : List Level) : M Expr := do
  (constTyAtM (← read).fe ci.name us : CheckCM Expr)

end InLean
