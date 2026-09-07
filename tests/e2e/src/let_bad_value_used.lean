--#export letBad2

/- End-to-end fixture (task #208; inductive audit #206, S1 / crack C9 —
   the CONTROL that already agrees with official).

   `def letBad2 : Nat := let x : Nat := Bool.true; x`, with the bound
   variable USED.  Official rejects at `infer_let`; lech rejects too, but
   only incidentally — the zeta-reduct is `Bool.true`, whose type does
   not match the declared `Nat`, so the definition's own type check
   fails ("type mismatch in definition letBad2").  Committed beside
   let_bad_value / let_bad_type / let_bad_thm so the conformance fix is
   visibly a widening of an existing rejection rather than a new one.

   official: 1.  lech at master 700a06ca: 1 piped, 1 raw, 1 --trusted.
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
  probeAdd (defn `letBad2 [] nat (mkLet `x nat (c ``Bool.true) (bv 0)))
mk_lets
