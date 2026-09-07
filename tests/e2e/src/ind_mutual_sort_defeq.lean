--#export MC.self

/- End-to-end fixture (task #208; inductive audit #206, A4 / crack C4,
   the SORT variant): a mutual block whose members' RESULT SORTS are
   definitionally but not syntactically equal — `MC : Sort (max u v)`,
   `MD : Sort (max v u)`.  Official compares them with `is_equivalent`
   (`check_inductive_types`, inductive.cpp:250) and accepts the block and
   its recursors.

   con-leche's in-process modeller compares them with `==`
   (Frontend/InModel/Mutual.lean:164, Nested.lean:351) and declines:
   "member MD: parameter telescope or sort differs from MC's".  The
   preprocessor's native predicate checks only counts, so the block stays
   in-process and the generator's decline is the run's — piped and raw.

   The parameter variant is ind_mutual_param_defeq.  Only the sort half
   of the probe is exported here: the probe file also carried an
   `id Type` mutual pair whose first member the v4.29.1 kernel rejects,
   which would have masked this verdict.

   official: 0.  con-leche at master 700a06ca: 2 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/MutualDefEq.lean. -/

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

/-- `MC.{u,v} : Sort (max u v) | mk (d : MD)` together with
`MD.{u,v} : Sort (max v u) | nil` — one mutual block, no parameters. -/
elab "mk_mutual_defeq" : command => do
  let s1 := sort (.max u v)
  let s2 := sort (.max v u)
  let Cmk := pi `d (c `MD [u, v]) (c `MC [u, v])
  probeAdd (indDecl [`u, `v] 0
    [⟨`MC, s1, [⟨`MC.mk, Cmk⟩]⟩, ⟨`MD, s2, [⟨`MD.nil, c `MD [u, v]⟩]⟩])
  probeAdd (thm `MC.self [`u, `v]
    (pi `x (c `MC [u, v]) (eq (.max u v) (c `MC [u, v]) (bv 0) (bv 0)))
    (lam `x (c `MC [u, v]) (rfl' (.max u v) (c `MC [u, v]) (bv 0))))
mk_mutual_defeq
