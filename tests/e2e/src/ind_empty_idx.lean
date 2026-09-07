--#export EmptyIdx.elim EmptyIdxP.elim

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): ZERO-CONSTRUCTOR INDEXED families, `Type`- and `Prop`-valued.
   Hand-built with `numParams = 0`: the `inductive` command promotes an
   unused index to a parameter, which would turn them into plain
   zero-constructor sums.  The direct sum/indexed route takes both
   (`EmptyIdx sum`, `EmptyIdxP sum`); official agrees.

   official: 0.  lech at master 700a06ca: 0 piped, 0 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/EmptyIdx.lean. -/

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

elab "mk_emptyidx" : command => do
  probeAdd (indDecl [] 0 [⟨`EmptyIdx, pi `n nat (sort 1), []⟩])
  probeAdd (indDecl [] 0 [⟨`EmptyIdxP, pi `n nat (sort 0), []⟩])
  -- EmptyIdx.elim : ∀ x : EmptyIdx Nat.zero, False
  let E0 := ap (c `EmptyIdx) [c ``Nat.zero]
  let mot := lam `a nat (lam `t (ap (c `EmptyIdx) [bv 0]) (c ``False))
  probeAdd (defn `EmptyIdx.elim [] (pi `x E0 (c ``False))
    (lam `x E0 (ap (c `EmptyIdx.rec [0]) [mot, c ``Nat.zero, bv 0])))
  let P0 := ap (c `EmptyIdxP) [c ``Nat.zero]
  let motP := lam `a nat (lam `t (ap (c `EmptyIdxP) [bv 0]) (c ``False))
  probeAdd (thm `EmptyIdxP.elim [] (pi `h P0 (c ``False))
    (lam `h P0 (ap (c `EmptyIdxP.rec [0]) [motP, c ``Nat.zero, bv 0])))
mk_emptyidx
