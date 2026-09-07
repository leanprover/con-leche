--#export T.size_node

/- End-to-end fixture (task #208; inductive audit #206, A5's clean twin):
   a recursive occurrence hidden under a definition, FINITARY case —
   `T | leaf | node (x : Id' T)` with `Id' α := α`.  Official whnf's the
   field and sees a plain recursive argument.  lech's fixpoint route is
   syntactic and reports `.unsupported`, but the preprocessor models the
   block and the stream accepts; raw it declines for a missing model.
   The regression guard beside ind_pos_whnf_fn, where the tool errors.

   official: 0.  lech at master 700a06ca: 0 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/WhnfPosId.lean. -/

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

def Id' (α : Type) := α

elab "mk_whnfpos" : command => do
  let T := c `T
  probeAdd (indDecl [] 0
    [⟨`T, sort 1, [⟨`T.leaf, T⟩, ⟨`T.node, pi `x (ap (c `Id') [T]) T⟩]⟩])
mk_whnfpos

noncomputable def T.size : T → Nat := fun t => T.rec 0 (fun _ ih => ih + 1) t

theorem T.size_node : T.size (T.node T.leaf) = 1 := rfl
