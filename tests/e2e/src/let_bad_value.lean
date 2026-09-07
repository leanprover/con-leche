--#export letBad1

/- End-to-end fixture (task #208; inductive audit #206, S1 / crack C9 —
   an ACCEPT-SUPERSET, the only unlicensed one the audit found).

   `def letBad1 : Nat := let x : Nat := Bool.true; Nat.zero`, with the
   bound variable UNUSED.  Official runs `infer_let`
   (type_checker.cpp): `ensure_sort (infer ty)`, `infer v`,
   `is_def_eq (infer v) ty` — and REJECTS with "(kernel)
   let-declaration type mismatch 'x'".

   con-leche never runs those three checks: `annotate`'s `.letE` clause
   returns the zeta-reduct (Kernel/Core.lean:2577-2596) and the annotated
   term is let-free, so the `.letE` arms of `whnfCore`/`infer`
   (Core.lean:1756/1975/2114, CoreC.lean:941/1323/1778) are dead code.
   With `x` unused the reduct is `Nat.zero`, which checks, and the stream
   ACCEPTS.  NOT a soundness problem — the zeta-reduct is what is checked
   and stored, and the capstone covers the stored term — but official
   rejects.  let_bad_value_used is the twin the reduct does catch.

   THE EXPECTATION BELOW PINS TODAY'S BEHAVIOUR (0).  The conformance fix
   (audit follow-up 1: run the `infer_let` triple in `annotate`'s `.letE`
   clause on the annotated `ty'`/`v'`, then delete the six dead arms)
   flips it to 1 deliberately.

   official: 1.  con-leche at master 700a06ca: 0 piped, 0 raw, 0 --trusted.
   Probe of record: _tmp/indaudit/probes/P/LetValueType.lean. -/

import Lean
open Lean Elab Command

/-! The probe kit (task #206/#208): declarations the official kernel
accepts but Lean's *elaborator* refuses to write down are added with the
kernel type check skipped, so that they exist in the environment and
therefore in the export.  Inductive declarations still go through
`add_inductive`, so an inductive here is one the kernel really admits. -/
namespace Probe

def probeAdd (d : Declaration) : CommandElabM Unit := do
  liftCoreM <| withOptions (debug.skipKernelTC.set · true) <| addDecl d

def pi (n : Name) (d b : Expr) : Expr := mkForall n .default d b
def lam (n : Name) (d b : Expr) : Expr := mkLambda n .default d b
def sort (l : Level) : Expr := mkSort l
def c (n : Name) (ls : List Level := []) : Expr := mkConst n ls
def bv (i : Nat) : Expr := mkBVar i
def ap (f : Expr) (as : List Expr) : Expr := mkAppN f as.toArray
def u : Level := .param `u
def v : Level := .param `v
def eq (l : Level) (a b d : Expr) : Expr := ap (c ``Eq [l]) [a, b, d]
def rfl' (l : Level) (a b : Expr) : Expr := ap (c ``Eq.refl [l]) [a, b]
def nat : Expr := c ``Nat
def natLit (n : Nat) : Expr := mkRawNatLit n

def indDecl (lps : List Name) (nP : Nat) (types : List InductiveType) : Declaration :=
  .inductDecl lps nP types false

def thm (n : Name) (lps : List Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := lps, type := ty, value := val }

def defn (n : Name) (lps : List Name) (ty val : Expr) : Declaration :=
  .defnDecl { name := n, levelParams := lps, type := ty, value := val,
              hints := .abbrev, safety := .safe }

end Probe

open Probe

elab "mk_lets" : command => do
  probeAdd (defn `letBad1 [] nat (mkLet `x nat (c ``Bool.true) (c ``Nat.zero)))
mk_lets
