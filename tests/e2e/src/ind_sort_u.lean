--#export W.x W.eta S.small

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): `Sort u`-valued blocks that MAY be `Prop` — the elaborator
   refuses to declare them, the kernel admits them:

     W.{u} (α : Sort u) : Sort u | mk (x : α)   -- 1 ctor, SMALL eliminator
     S.{u} (α : Sort u) : Sort u | a | b        -- 2 ctors, SMALL eliminator

   Consumers: `.proj` on `W α` (official allows it — `W α` is not
   syntactically a Prop), kernel structure eta on `W`, and `S`'s small
   recursor.  The direct structure and sum routes take them
   (`W struct`, `S sum`) and the elimination-level recogniser
   (Parts.lean:475-483) accepts the small eliminators.

   official: 0.  con-leche at master 700a06ca: 0 piped, 0 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/SortU.lean. -/

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

elab "mk_sortu" : command => do
  let Wt := pi `α (sort u) (sort u)
  let Wct := mkForall `α .implicit (sort u) (pi `x (bv 0) (ap (c `W [u]) [bv 1]))
  probeAdd (indDecl [`u] 1 [⟨`W, Wt, [⟨`W.mk, Wct⟩]⟩])
  let St := pi `α (sort u) (sort u)
  let Sa := mkForall `α .implicit (sort u) (ap (c `S [u]) [bv 0])
  probeAdd (indDecl [`u] 1 [⟨`S, St, [⟨`S.a, Sa⟩, ⟨`S.b, Sa⟩]⟩])
  -- W.x : ∀ {α : Sort u} (w : W α), α := fun α w => w.1
  let Wa := ap (c `W [u]) [bv 0]
  probeAdd (defn `W.x [`u] (mkForall `α .implicit (sort u) (pi `w Wa (bv 1)))
    (mkLambda `α .implicit (sort u) (lam `w Wa (mkProj `W 0 (bv 0)))))
  -- W.eta : ∀ {α} (w : W α), W.mk (W.x w) = w
  let Wa1 := ap (c `W [u]) [bv 1]
  let lhs := ap (c `W.mk [u]) [bv 1, ap (c `W.x [u]) [bv 1, bv 0]]
  probeAdd (thm `W.eta [`u] (mkForall `α .implicit (sort u) (pi `w Wa (eq u Wa1 lhs (bv 0))))
    (mkLambda `α .implicit (sort u) (lam `w Wa (rfl' u Wa1 (bv 0)))))
  -- S.small: the small eliminator at `True`
  let Sα := ap (c `S [u]) [bv 0]
  let motS := lam `t (ap (c `S [u]) [bv 1]) (c ``True)
  let recS := ap (c `S.rec [u]) [bv 1, motS, c ``True.intro, c ``True.intro, bv 0]
  probeAdd (thm `S.small [`u]
    (mkForall `α .implicit (sort u) (pi `x Sα (eq 0 (c ``True) recS (c ``True.intro))))
    (mkLambda `α .implicit (sort u) (lam `x Sα (rfl' 0 (c ``True) (c ``True.intro)))))
mk_sortu
