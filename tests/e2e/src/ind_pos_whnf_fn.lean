--#export R.size_node

/- End-to-end fixture (task #208; inductive audit #206, A5 / crack C5):
   a recursive occurrence HIDDEN UNDER A DEFINITION, reflexive case —
   `R | leaf | node (f : Fn R)` with `Fn α := Nat → α`.  Official whnf's
   the field type before classifying it (`is_positive`/`is_rec_argument`,
   inductive.cpp:383-409) and sees a reflexive recursive argument, so it
   accepts the block and its recursor.

   con-leche's fixpoint positivity check is SYNTACTIC
   (Kernel/Direct/RecParts.lean:102-114): the head `Fn` is neither the
   block nor block-free after one look, so the block is `.unsupported`
   and falls to the preprocessor, whose structural check ("a field of R
   mentions it other than as `∀ z⃗, R p⃗ e⃗` after full head
   normalisation") errors -> exit 3.  Raw the stream declines for a
   missing model.  The finitary twin is ind_pos_whnf_id, which the tool
   does model.

   official: 0.  con-leche at master 700a06ca: 3 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/WhnfPosFn.lean. -/

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

def Fn (α : Type) := Nat → α

/-- The elaborator's positivity check refuses to write this block down;
`add_inductive` accepts it. -/
elab "mk_whnfpos" : command => do
  let R := c `R
  probeAdd (indDecl [] 0
    [⟨`R, sort 1, [⟨`R.leaf, R⟩, ⟨`R.node, pi `f (ap (c `Fn) [R]) R⟩]⟩])
mk_whnfpos

noncomputable def R.size : R → Nat := fun r => R.rec 0 (fun _ ih => ih 0 + 1) r

theorem R.size_node : R.size (R.node (fun _ => R.leaf)) = 1 := rfl
