--#export Chain.eta Chain.eta_use

/- End-to-end fixture (task #210 Part A): structure η at a RECURSIVE
   structure-like block — a conformance guard.  Official's
   `is_structure_like` (kernel/inductive.cpp) requires one constructor,
   no index AND `!is_rec()`, so its `try_eta_struct` never fires on
   `Chain` and `c = Chain.mk c.h c.t := rfl` is REJECTED ("Not a
   definitional equality").  con-leche's fixpoint route stores the
   block's projection table (its `.proj` nodes type and reduce, as
   official's `infer_proj` does) but its capability record
   (`nativeCaps`) claims η only at a block with no recursive or
   reflexive field, so the theorems are REJECTED too.  Granting η here
   was tried — the P tier proves the η law at the one-constructor fibre
   (`fixEntryEtaCore`) — and withdrawn: on `ind_nest_via_refl` the
   tool's nested model over a reflexive structure-like made `isDefEq`
   spin through η-expansion; official's `!is_rec` is load-bearing.

   The elaborator refuses to write the statements down, so they are
   added through the probe kit of task #208 (kernel check skipped).

   official: 1.  con-leche: 1. -/

import Lean
open Lean Elab Command

namespace Probe

def probeAdd (d : Declaration) : CommandElabM Unit := do
  liftCoreM <| withOptions (debug.skipKernelTC.set · true) <| addDecl d

def pi (n : Name) (d b : Expr) : Expr := mkForall n .default d b
def lam (n : Name) (d b : Expr) : Expr := mkLambda n .default d b
def c (n : Name) (ls : List Level := []) : Expr := mkConst n ls
def bv (i : Nat) : Expr := mkBVar i
def ap (f : Expr) (as : List Expr) : Expr := mkAppN f as.toArray
def eq (l : Level) (a b d : Expr) : Expr := ap (c ``Eq [l]) [a, b, d]
def rfl' (l : Level) (a b : Expr) : Expr := ap (c ``Eq.refl [l]) [a, b]
def nat : Expr := c ``Nat

def thm (n : Name) (lps : List Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := lps, type := ty, value := val }

end Probe

open Probe

structure Chain where
  h : Nat
  t : Chain

/-- `Chain.eta : ∀ c, c = Chain.mk c.1 c.2` by `Eq.refl c`, and
`Chain.eta_use : ∀ c f, f c = f (Chain.mk c.1 c.2)` by `Eq.refl (f c)`
— raw `.proj` nodes on the right. -/
elab "mk_eta" : command => do
  let chain := c `Chain
  let mkc (x : Expr) : Expr := ap (c `Chain.mk) [mkProj `Chain 0 x, mkProj `Chain 1 x]
  probeAdd (thm `Chain.eta []
    (pi `c chain (eq 1 chain (bv 0) (mkc (bv 0))))
    (lam `c chain (rfl' 1 chain (bv 0))))
  probeAdd (thm `Chain.eta_use []
    (pi `c chain (pi `f (pi `x chain nat)
      (eq 1 nat (ap (bv 0) [bv 1]) (ap (bv 0) [mkc (bv 1)]))))
    (lam `c chain (lam `f (pi `x chain nat) (rfl' 1 nat (ap (bv 0) [bv 1])))))
mk_eta
