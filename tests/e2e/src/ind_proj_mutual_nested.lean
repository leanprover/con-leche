--#export MA.n_mk NT.lbl_mk MA.n_proj NT.lbl_proj

/- End-to-end fixture (task #208; inductive audit #206, A7 / crack C7):
   raw `.proj` nodes OUTSIDE the projection functions, on a MUTUAL member
   structure and on a NESTED structure.  Official's `infer_proj` needs
   one constructor and `nparams + nindices` arguments and types both.
   con-leche rewrites the projection FUNCTIONS from the `_model.proj_i.iota`
   artifacts (Frontend/ProjRec.lean) — `MA.n_mk`/`NT.lbl_mk` exercise
   those and would accept on their own — but a raw `.proj` anywhere else
   has no table and declines by design (W5, Core.lean:2596-2622).

   official: 0.  con-leche at master 700a06ca: 2 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/ProjMutualNested.lean. -/

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

mutual
  structure MA where
    n : Nat
    b : MB
  structure MB where
    s : Bool
    a : MA
end

structure NT where
  lbl : Nat
  kids : List NT

theorem MA.n_mk (b : MB) : (MA.mk 3 b).n = 3 := rfl
theorem NT.lbl_mk : (NT.mk 3 []).lbl = 3 := rfl

/-- The raw `.proj` probes: `X.f_proj : ∀ x, X.f x = x.1`. -/
elab "mk_projs" : command => do
  probeAdd (thm `MA.n_proj []
    (pi `x (c `MA) (eq 1 nat (ap (c `MA.n) [bv 0]) (mkProj `MA 0 (bv 0))))
    (lam `x (c `MA) (rfl' 1 nat (ap (c `MA.n) [bv 0]))))
  probeAdd (thm `NT.lbl_proj []
    (pi `x (c `NT) (eq 1 nat (ap (c `NT.lbl) [bv 0]) (mkProj `NT 0 (bv 0))))
    (lam `x (c `NT) (rfl' 1 nat (ap (c `NT.lbl) [bv 0]))))
mk_projs
