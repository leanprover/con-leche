--#export S.x S.x_mk

/- Task #480: a def-headed family at `Sort u`: the projection's guard walks the
   stored type to `Sort u` at the use.  Official's `is_prop` says no; here the row's
   sort lies under the walked sort, so the use is accepted too.

   official: 0 (Lean's kernel checked the block and, below, the projection).
   con-leche: 0. -/

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

universe w

def MySort := Sort w

elab "mk_block" : command => liftCoreM do
  let ctor : Constructor := ⟨`S.mk, pi `x (c ``PUnit [u]) (c `S [u])⟩
  let ty : InductiveType := ⟨`S, c `MySort [u], [ctor]⟩
  addDecl (indDecl [`u] 0 [ty])
mk_block

elab "mk_proj" : command => liftCoreM do
  addDecl (defn `S.x [`u] (pi `s (c `S [u]) (c ``PUnit [u]))
    (lam `s (c `S [u]) (mkProj `S 0 (bv 0))))
  addDecl (thm `S.x_mk [`u]
    (pi `y (c ``PUnit [u]) (eq u (c ``PUnit [u]) (ap (c `S.x [u]) [ap (c `S.mk [u]) [bv 0]]) (bv 0)))
    (lam `y (c ``PUnit [u]) (rfl' u (c ``PUnit [u]) (bv 0))))
mk_proj
