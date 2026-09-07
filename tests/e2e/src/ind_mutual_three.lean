--#export TA.self TC.self PB.self

/- End-to-end fixture (task #218; inductive audit #206, A4 / crack C4,
   the UNIVERSAL-COVERAGE probe): mutual blocks whose members spell a
   DEPENDENT parameter telescope and their sorts in definitionally but
   not syntactically equal ways, exactly as the kernel admits them:

   * `TA (α : Type) (β : α → Type) : Type`,
     `TB (α : Type) (β : (fun x => x) α → Type) : Type` — the second
     member spells `β`'s domain as a β-REDEX —,
     `TC (α : id Type) (β : α → Type) : Nat → Sort (max 1 1)` — the third
     spells `α`'s domain through `id` and its sort as `max 1 1`, and
     carries an INDEX; three members with cross recursion
     (`TA.mk … (t : TB α β)`, `TB.mk … (c : TC α β n)`, `TC.mk … (a : TA α β)`),
     `TA` structure-like (its projection artifacts at a large
     eliminator), `TB` with two constructors;
   * `PA : Prop`, `PB : Sort (max 0 0)` — a Prop pair with the small
     eliminator, cross recursion and a nullary constructor.

   Official compares the parameter domains with `is_def_eq` and the
   sorts with `is_equivalent` (`check_inductive_types`, inductive.cpp:230
   and :250) and accepts.  con-leche's modeller (task #218) builds the tag
   and the auxiliary family over the FIRST member's telescope and sort and
   emits every public slot at the member's own declared type; the fold's
   typing of those slots is the comparison, and the block accepts.

   The blocks are added through the probe kit (`debug.skipKernelTC` for
   the theorems, `add_inductive` proper for the blocks) so the spellings
   are exactly these — Lean's elaborator would β-reduce or would refuse
   `Sort (max 0 0)`.  `(h : id True)` on the first member makes `id` a
   dependency of the block's first member (the arena's official checker
   replays constants by dependency).

   official: 0.  con-leche: 0 (both modes; sibling twins
   ind_mutual_param_bad / ind_mutual_sort_bad reject with 1). -/

import Lean
open Lean Elab Command

namespace Probe

def probeAdd (d : Declaration) : CommandElabM Unit := do
  liftCoreM <| withOptions (debug.skipKernelTC.set · true) <| addDecl d

def pi (n : Name) (d b : Expr) : Expr := mkForall n .default d b
def lam (n : Name) (d b : Expr) : Expr := mkLambda n .default d b
def sort (l : Level) : Expr := mkSort l
def c (n : Name) (ls : List Level := []) : Expr := mkConst n ls
def bv (i : Nat) : Expr := mkBVar i
def ap (f : Expr) (as : List Expr) : Expr := mkAppN f as.toArray
def eq (l : Level) (a b d : Expr) : Expr := ap (c ``Eq [l]) [a, b, d]
def rfl' (l : Level) (a b : Expr) : Expr := ap (c ``Eq.refl [l]) [a, b]
def nat : Expr := c ``Nat
def one : Level := .succ .zero
def two : Level := .succ one

def indDecl (lps : List Name) (nP : Nat) (types : List InductiveType) : Declaration :=
  .inductDecl lps nP types false

def thm (n : Name) (lps : List Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := lps, type := ty, value := val }

end Probe

open Probe

/-- The three-member block at the spellings described in the header. -/
elab "mk_mutual_three" : command => do
  let Type1 := sort one
  -- `(fun (x : Type) => x) α` — the redex spelling of `α`
  let redexα := ap (lam `x Type1 (bv 0)) [bv 0]
  -- `@id.{3} (Type 1) Type` — the `id` spelling of `Type` (`Type : Type 1`)
  let idType := ap (c ``id [.succ two]) [sort two, Type1]
  -- TA : (α : Type) → (β : α → Type) → Type
  let tyTA := pi `α Type1 (pi `β (pi `x (bv 0) Type1) Type1)
  -- TA.mk : ∀ α β (a : α) (b : β a) (t : TB α β) (h : id True), TA α β
  let tyTAmk := pi `α Type1 (pi `β (pi `x (bv 0) Type1)
    (pi `a (bv 1) (pi `b (ap (bv 1) [bv 0]) (pi `t (ap (c `TB) [bv 3, bv 2])
      (pi `h (ap (c ``id [one]) [sort .zero, c ``True]) (ap (c `TA) [bv 5, bv 4]))))))
  -- TB : (α : Type) → (β : (fun x => x) α → Type) → Type
  let tyTB := pi `α Type1 (pi `β (pi `x redexα Type1) Type1)
  -- TB.mk : ∀ α β (n : Nat) (c : TC α β n), TB α β ;  TB.nil : ∀ α β, TB α β
  let tyTBmk := pi `α Type1 (pi `β (pi `x redexα Type1)
    (pi `n nat (pi `c (ap (c `TC) [bv 2, bv 1, bv 0]) (ap (c `TB) [bv 3, bv 2]))))
  let tyTBnil := pi `α Type1 (pi `β (pi `x redexα Type1) (ap (c `TB) [bv 1, bv 0]))
  -- TC : (α : id Type) → (β : α → Type) → Nat → Sort (max 1 1)
  let tyTC := pi `α idType (pi `β (pi `x (bv 0) Type1) (pi `n nat (sort (.max one one))))
  -- TC.mk : ∀ α β (n : Nat) (a : TA α β), TC α β n
  let tyTCmk := pi `α idType (pi `β (pi `x (bv 0) Type1)
    (pi `n nat (pi `a (ap (c `TA) [bv 2, bv 1]) (ap (c `TC) [bv 3, bv 2, bv 1]))))
  probeAdd (indDecl [] 2
    [⟨`TA, tyTA, [⟨`TA.mk, tyTAmk⟩]⟩,
     ⟨`TB, tyTB, [⟨`TB.mk, tyTBmk⟩, ⟨`TB.nil, tyTBnil⟩]⟩,
     ⟨`TC, tyTC, [⟨`TC.mk, tyTCmk⟩]⟩])
  -- theorems mentioning the members (the export's roots)
  let constNat := lam `x nat nat
  let TAn := ap (c `TA) [nat, constNat]
  probeAdd (thm `TA.self [] (pi `x TAn (eq one TAn (bv 0) (bv 0)))
    (lam `x TAn (rfl' one TAn (bv 0))))
  let TCn := ap (c `TC) [nat, constNat, c ``Nat.zero]
  probeAdd (thm `TC.self [] (pi `x TCn (eq one TCn (bv 0) (bv 0)))
    (lam `x TCn (rfl' one TCn (bv 0))))
  -- PA : Prop | mk (b : PB) ;  PB : Sort (max 0 0) | mk (a : PA) | triv
  probeAdd (indDecl [] 0
    [⟨`PA, sort .zero, [⟨`PA.mk, pi `b (c `PB) (c `PA)⟩]⟩,
     ⟨`PB, sort (.max .zero .zero), [⟨`PB.mk, pi `a (c `PA) (c `PB)⟩, ⟨`PB.triv, c `PB⟩]⟩])
  probeAdd (thm `PB.self [] (pi `x (c `PB) (eq .zero (c `PB) (bv 0) (bv 0)))
    (lam `x (c `PB) (rfl' .zero (c `PB) (bv 0))))
mk_mutual_three
