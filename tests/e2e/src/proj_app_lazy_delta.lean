--#export proj_app_lazy_delta
/- End-to-end fixture (task #633; lean4#16613, arena test perf/proj-app-lazy-delta):
   two applied projections whose structures become syntactically equal after
   one delta step, while reducing either structure to a constructor never ends.

   The declaration is `fun a h => h : ∀ a, a ∈ small → a ∈ big (2^32)`.
   `a ∈ s` unfolds to the applied projection `s.1 a` (`PSet` is a structure
   with one predicate field, like Mathlib's `Set`), and `small` unfolds to
   `big (2^32)`.  Official compares bare projections `s.1 =?= t.1` lazily
   (`lazy_delta_proj_reduction`), but reduces the structures of applied ones
   `s.1 a =?= t.1 a` with `whnf` first; here that evaluates `slow (2^32)`,
   about four billion steps.  Con-leche runs the lazy-delta loop on the
   structures of applied projections too, and then compares the arguments.

   A performance fixture: accepted at once (con-leche with task #633,
   2026-11-25).  `tests/arena.sh` runs it under a timeout of 10 s, so a
   checker that reduces the structures fails it (exit 124).

   The theorem is added with `addDecl` under `debug.skipKernelTC`: the
   official kernel would evaluate `slow (2^32)`.  The stream is checked by
   the checkers that read it. -/
import Lean

open Lean Meta Elab Term

/-- A structure with one predicate field, like Mathlib's `Set`. -/
structure PSet (α : Type) where
  Mem : α → Prop

instance : Membership α (PSet α) := ⟨fun s a => s.Mem a⟩

def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop n (acc + 1)

/-- Θ(n) to evaluate. -/
def slow (n : Nat) : Nat := loop n 0

/-- Reducing `big n` to a constructor evaluates `slow n`. -/
def big (n : Nat) : PSet Nat :=
  match slow n with
  | 0 => ⟨fun _ => True⟩
  | _ => ⟨fun a => a = 0⟩

/-- `small` unfolds to `big (2^32)` in one delta step. -/
def small : PSet Nat := big (2^32)

/-- Add the theorem `fun xs h => h : ∀ xs, P → Q` with `addDecl`. -/
def addIdentityTheorem (name : Name) (stmt : Term) : TermElabM Unit := do
  let type ← elabType stmt
  synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  let value ← forallTelescope type fun xs _ => mkLambdaFVars xs xs.back!
  addDecl (.thmDecl { name, levelParams := [], type, value })

elab "#add_identity_theorem " name:ident " : " stmt:term : command =>
  Command.liftTermElabM <| addIdentityTheorem name.getId stmt

set_option debug.skipKernelTC true
-- `a ∈ small` unfolds to the applied projection `small.1 a`.
#add_identity_theorem proj_app_lazy_delta : ∀ a : Nat, a ∈ small → a ∈ big (2^32)
