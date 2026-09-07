--#export S.n S.b S.n_mk S.eta

/- End-to-end fixture (task #208; inductive audit #206, A1 / crack C1):
   a one-constructor, index-free, NON-Prop block (structure-like for
   official: `is_non_rec_structure`) whose type former is declared at a
   DEFINITION unfolding to `Type`.  Official whnf's the former
   (`check_inductive_types`, inductive.cpp:222-245), types `.proj` on the
   block and does structure eta on it, so all four consumers below are
   accepted.

   con-leche's structure recogniser needs a SYNTACTIC `∀ p⃗, Sort`
   (Kernel/Direct/Parts.lean:469), the sum route refuses `n = 1 ∧
   nIdx = 0` and the fixpoint route wants recursion, so no direct route
   takes the block; the preprocessor models it, but
   `ProjRec.projRecOwners` also requires `tty.stripPis nP` to end in a
   `.sort` (Frontend/ProjRec.lean:255), so the projection functions are
   not rewritten and the raw `.proj` declines at `S.n`.  Task #195 taught
   the SUM arm to whnf the former (fixture direct_idx_defhead); the
   structure arm and the projection-owner test were not taught.

   official: 0.  con-leche at master 700a06ca: 2 piped ("projection on a
   non-structure-like type" at `def S.n`), 2 raw ("missing model for S";
   both modes).
   Probe of record: _tmp/indaudit/probes/P/DefHeadStruct.lean. -/

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

def MyType := Type

inductive S : MyType
  | mk (n : Nat) (b : Bool)

/-- The elaborator's own spelling of the projection functions and their
consumers: `S.n := fun s => s.1` (a raw `Expr.proj`), its iota on `mk`,
and kernel structure eta. -/
elab "mk_proj" : command => do
  probeAdd (defn `S.n [] (pi `s (c `S) nat) (lam `s (c `S) (mkProj `S 0 (bv 0))))
  probeAdd (defn `S.b [] (pi `s (c `S) (c ``Bool)) (lam `s (c `S) (mkProj `S 1 (bv 0))))
  let mk1 := ap (c `S.mk) [natLit 1, c ``Bool.true]
  probeAdd (thm `S.n_mk [] (eq 1 nat (ap (c `S.n) [mk1]) (natLit 1)) (rfl' 1 nat (natLit 1)))
  let lhs := ap (c `S.mk) [ap (c `S.n) [bv 0], ap (c `S.b) [bv 0]]
  probeAdd (thm `S.eta [] (pi `s (c `S) (eq 1 (c `S) lhs (bv 0)))
    (lam `s (c `S) (rfl' 1 (c `S) (bv 0))))
mk_proj
