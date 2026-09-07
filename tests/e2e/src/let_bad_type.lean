--#export letBadTy

/- End-to-end fixture (task #208; inductive audit #206, S1 / crack C9 —
   an ACCEPT-SUPERSET).

   `def letBadTy : Nat := let x : Bool.true := Nat.zero; Nat.zero`: the
   let's declared TYPE is not a type at all.  Official's `infer_let`
   starts with `ensure_sort (infer ty)` and rejects ("type expected …
   Bool.true").  lech's `annotate` drops the let before anything looks at
   its type, the reduct is `Nat.zero`, and the stream ACCEPTS.  This is
   the arm the conformance fix's `ensureSort` restores.

   THE EXPECTATION BELOW PINS TODAY'S BEHAVIOUR (0); the fix flips it
   to 1.

   official: 1.  lech at master 700a06ca: 0 piped, 0 raw, 0 --trusted.
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
  probeAdd (defn `letBadTy [] nat (mkLet `x (c ``Bool.true) (c ``Nat.zero) (c ``Nat.zero)))
mk_lets
