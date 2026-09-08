--#export Chain.h_mk Chain.t_mk Chain.t_h Chain.h2_mk Dep.a_mk Dep.b_mk Dep.next_mk PChain.p_mk PChain.use

/- End-to-end fixture (task #210 Part A): the projection FUNCTIONS and
   raw `.proj` nodes of RECURSIVE structure-like blocks on the fixpoint
   route.  Official types `.proj` on any one-constructor, index-free
   family (`infer_proj`; recursion is irrelevant), so the elaborator's
   `Chain.h := fun self => self.1` type-checks and its iota reduces.

   con-leche installs the block natively (`Chain fix`) and, since task
   #210 Part A, conses the PROJECTION TABLE of a structure-like block
   at the fixpoint route's carrier (`checkNativeTable`: the fields
   sit at projection offset 1 of the TAGGED tower, `ProjTable.off`).
   The shapes: `Chain` (a data field before the recursive one: iota on
   both, a nested `.t.h`, a definition through projections), `Dep α β`
   (two parameters, a DEPENDENT field `b : β a` — its projection's type
   reads the earlier field through `.proj 0` — and a recursive field),
   and `PChain P : Prop` (a proof field and a recursive one: the SQUASH
   regime, every value the point, the projection typed under the
   `Prop` guard).  No structure η here: official's `is_structure_like`
   excludes recursive blocks (see direct_fix_struct_eta).

   official: 0.  con-leche before #210 Part A: 2 ("projection on a
   non-structure-like type" at def Chain.h), cf. ind_rec_struct_proj. -/

universe u

structure Chain where
  h : Nat
  t : Chain

theorem Chain.h_mk (t : Chain) : (Chain.mk 3 t).h = 3 := rfl
theorem Chain.t_mk (t : Chain) : (Chain.mk 3 t).t = t := rfl
theorem Chain.t_h (c : Chain) : (Chain.mk 1 (Chain.mk 2 c)).t.h = 2 := rfl

def Chain.h2 (c : Chain) : Nat := c.t.h
theorem Chain.h2_mk (c : Chain) : Chain.h2 (Chain.mk 1 (Chain.mk 2 c)) = 2 := rfl

structure Dep (α : Type u) (β : α → Type u) where
  a : α
  b : β a
  next : Dep α β

theorem Dep.a_mk {α : Type u} {β : α → Type u} (x : α) (y : β x) (n : Dep α β) :
    (Dep.mk x y n).a = x := rfl
theorem Dep.b_mk {α : Type u} {β : α → Type u} (x : α) (y : β x) (n : Dep α β) :
    (Dep.mk x y n).b = y := rfl
theorem Dep.next_mk {α : Type u} {β : α → Type u} (x : α) (y : β x) (n : Dep α β) :
    (Dep.mk x y n).next = n := rfl

structure PChain (P : Prop) : Prop where
  p : P
  rest : PChain P

theorem PChain.p_mk (P : Prop) (h : P) (r : PChain P) : (PChain.mk h r).p = h := rfl
theorem PChain.use (P : Prop) (c : PChain P) : P := c.p
