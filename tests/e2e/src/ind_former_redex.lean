--#export SR.self

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): a one-constructor block whose FORMER'S TYPE IS A β-REDEX,
   `(fun x => x) Type` — official whnf's it; no definition is involved,
   so no def-headed exemption applies.  The installer whnf's the former
   and the stream accepts.  The regression guard beside
   ind_defhead_struct / ind_defhead_k / ind_defhead_mutual.

   official: 0.  con-leche: 0 (both modes).
   Probe of record: _tmp/indaudit/probes/P/FormerRedex.lean. -/

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

elab "mk_redex" : command => do
  let ty := ap (lam `x (sort 2) (bv 0)) [sort 1]
  probeAdd (indDecl [] 0 [⟨`SR, ty, [⟨`SR.mk, pi `n nat (c `SR)⟩]⟩])
  probeAdd (thm `SR.self [] (pi `s (c `SR) (eq 1 (c `SR) (bv 0) (bv 0)))
    (lam `s (c `SR) (rfl' 1 (c `SR) (bv 0))))
mk_redex
