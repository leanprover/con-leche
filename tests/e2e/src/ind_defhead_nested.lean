--#export Tree.size_node Rose.depth_node

/- End-to-end fixture (task #431): a DEF-HEADED family as the CONTAINER
   of a nested block.  `Box`'s former is declared at `MyType := Type`,
   `Vec'`'s at `Fam := Nat → Type` (an indexed family whose index
   appears only after unfolding); `Tree` nests through `Box`, `Rose`
   through `Vec'` at a literal index.  Official whnf's the container's
   type when it builds the auxiliary block (`elim_nested_inductive`,
   then `check_inductive_types` on it), so it accepts both, with their
   recursors' ι-reductions below.  (A container whose definition takes
   the PARAMETERS, `Fam α := Nat → Type` at `Vec' α : Fam α`, is
   rejected by the official kernel itself: the auxiliary block's former
   `Fam Rose` names the block before it exists, "unknown constant".)
   The stored install puts the formers
   at their reduced telescopes, which the container readers read.

   official: 0.  con-leche: 0. -/
def MyType := Type

inductive Box (α : Type) : MyType
  | mk (a : α)

inductive Tree : Type
  | leaf
  | node (cs : Box Tree)

noncomputable def Tree.size : Tree → Nat :=
  fun t => Tree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    1 (fun _ ih => ih + 1) (fun _ ih => ih) t

theorem Tree.size_node : Tree.size (Tree.node (Box.mk Tree.leaf)) = 2 := rfl

def Fam := Nat → Type

inductive Vec' (α : Type) : Fam
  | nil : Vec' α 0
  | cons {n : Nat} (a : α) (v : Vec' α n) : Vec' α (n + 1)

inductive Rose : Type
  | tip
  | node (cs : Vec' Rose 1)

noncomputable def Rose.depth : Rose → Nat :=
  fun r => Rose.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ ih => ih + 1) 0 (fun _ _ iha ihv => max iha ihv) r

theorem Rose.depth_node : Rose.depth (Rose.node (Vec'.cons Rose.tip Vec'.nil)) = 1 := rfl
