--#export Tree.mirror_node Tree.mirror_leaf Tree.depth_node Tree.depth_leaf Chain.head_mk Chain.small Tree.small_node

/- End-to-end test (task #188): recursive types with SEVERAL recursive
   fields in one constructor and a one-constructor recursive type.
   `Tree α` is the binary tree (two recursive fields around a data
   field; the recursor's minor takes two inductive hypotheses in field
   order), `Chain α` the one-constructor recursive type — the
   "structure with a recursive field", which the official kernel does
   NOT treat as structure-like (`is_structure_like` excludes recursive
   blocks): no projections, no eta; it is empty, so its consumers only
   exercise the recursor's typing and its fixed-point equation. -/

universe u

inductive Tree (α : Type u) : Type u where
  | leaf : Tree α
  | node (l : Tree α) (a : α) (r : Tree α) : Tree α

noncomputable def Tree.mirror {α : Type u} (t : Tree α) : Tree α :=
  Tree.rec (motive := fun _ => Tree α) Tree.leaf (fun _ a _ ihl ihr => Tree.node ihr a ihl) t

theorem Tree.mirror_leaf {α : Type u} : Eq (Tree.mirror (Tree.leaf : Tree α)) Tree.leaf := rfl
theorem Tree.mirror_node {α : Type u} (l : Tree α) (a : α) (r : Tree α) :
    Eq (Tree.mirror (Tree.node l a r)) (Tree.node (Tree.mirror r) a (Tree.mirror l)) := rfl

noncomputable def Tree.depth {α : Type u} (t : Tree α) : Nat :=
  Tree.rec (motive := fun _ => Nat) Nat.zero (fun _ _ _ ihl _ => Nat.succ ihl) t

theorem Tree.depth_leaf {α : Type u} : Eq (Tree.depth (Tree.leaf : Tree α)) Nat.zero := rfl
theorem Tree.depth_node {α : Type u} (l : Tree α) (a : α) (r : Tree α) :
    Eq (Tree.depth (Tree.node l a r)) (Nat.succ (Tree.depth l)) := rfl

theorem Tree.small {α : Type u} (t : Tree α) (p : Prop) (hp : p) : p :=
  Tree.rec (motive := fun _ => p) hp (fun _ _ _ ihl _ => ihl) t

theorem Tree.small_node {α : Type u} (l : Tree α) (a : α) (r : Tree α) (p : Prop) (hp : p) :
    Eq (Tree.small (Tree.node l a r) p hp) (Tree.small l p hp) := rfl

inductive Chain (α : Type u) : Type u where
  | mk (head : α) (tail : Chain α) : Chain α

noncomputable def Chain.head {α : Type u} (c : Chain α) : α :=
  Chain.rec (motive := fun _ => α) (fun a _ _ => a) c

theorem Chain.head_mk {α : Type u} (a : α) (c : Chain α) : Eq (Chain.head (Chain.mk a c)) a := rfl

theorem Chain.small {α : Type u} (c : Chain α) (p : Prop) : p :=
  Chain.rec (motive := fun _ => p) (fun _ _ ih => ih) c
