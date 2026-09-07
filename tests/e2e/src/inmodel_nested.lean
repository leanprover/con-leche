--#export InModelNested.size_example InModelNested.tv_example InModelNested.op_example InModelNested.w_example InModelNested.p_example InModelNested.NTree.use_label InModelNested.NTree.use_kids InModelNested.ab_example

/- End-to-end test: NESTED inductive blocks modelled IN-PROCESS (task
   #200, B3).  The kernel's nested→mutual reduction is read off the
   exported recursor family (mimic members from the motives, their
   constructors from the minors), the auxiliary family gets one member
   per motive, and the public slots go through the pack/unpack
   isomorphisms with `Eq.rec` transports.

   Shapes: `Tree` nesting through `List` (structural recursion via
   below/brecOn, `rfl` forcing iota through `Tree.rec` and `Tree.rec_1`),
   `TV` through the INDEXED family `Vec`, `Op` through `Option` and `Prod`
   (two mimics, one constructor with two packed fields), `W` through a
   structure `Wrap` whose field is `List W` (a mimic depending on another
   mimic), `PT` through a container at a DEPENDENT pin
   (`DMap α (fun _ => PT α)`), the nested structure `NTree` (projection
   functions rewritten at the generated artifacts' levels), and a
   MUTUAL-AND-NESTED pair `A`/`B` (B4's class, same code path). -/

namespace InModelNested

inductive Tree (α : Type) where
  | node : α → List (Tree α) → Tree α

mutual
  def Tree.size {α : Type} : Tree α → Nat
    | .node _ ts => Tree.sizeList ts + 1
  def Tree.sizeList {α : Type} : List (Tree α) → Nat
    | [] => 0
    | t :: ts => t.size + Tree.sizeList ts
end

theorem size_example :
    Eq (Tree.node true [Tree.node false [], Tree.node true []]).size 3 := rfl

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

inductive TV (α : Type) where
  | node : α → {n : Nat} → Vec (TV α) n → TV α

noncomputable def TV.count {α : Type} (t : TV α) : Nat :=
  TV.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (fun _ {_} _ ih => ih + 1) 0 (fun {_} _ _ ih1 ih2 => ih1 + ih2) t

theorem tv_example : TV.count (TV.node 0 (Vec.cons (TV.node 1 Vec.nil) Vec.nil)) = 2 := rfl

inductive Op where
  | leaf : Nat → Op
  | pair : Option Op → Prod Op Nat → Op

noncomputable def Op.sum (o : Op) : Nat :=
  Op.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun n => n) (fun _ _ ih1 ih2 => ih1 + ih2)
    0 (fun _ ih => ih) (fun _ _ ih => ih) o

theorem op_example : Op.sum (Op.pair (some (Op.leaf 2)) (Op.leaf 3, 7)) = 5 := rfl

structure Wrap (β : Type) where
  items : List β

inductive W where
  | mk : Wrap W → W

noncomputable def W.depth (w : W) : Nat :=
  W.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ ih => ih) 0 (fun _ _ ih1 ih2 => Nat.max ih1 ih2) w

theorem w_example : W.depth (W.mk ⟨[W.mk ⟨[]⟩]⟩) = 2 := rfl

inductive DMap (α : Type) (β : α → Type) where
  | leaf
  | node (k : α) (v : β k) (rest : DMap α β)

inductive PT (α : Type) where
  | mk : Nat → DMap α (fun _ => PT α) → PT α

noncomputable def PT.total {α : Type} (t : PT α) : Nat :=
  PT.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun n _ ih => n + ih) 0 (fun _ _ _ ih1 ih2 => ih1 + ih2) t

theorem p_example : PT.total (PT.mk 1 (DMap.node () (PT.mk 2 DMap.leaf) DMap.leaf)) = 3 := rfl

structure NTree where
  label : Nat
  kids : List NTree

def NTree.use_label (t : NTree) : Nat := t.label
def NTree.use_kids (t : NTree) : List NTree := t.kids

mutual
inductive A where
  | mk : List B → A
inductive B where
  | mk : Nat → A → B
  | leaf : B
end

noncomputable def A.count (a : A) : Nat :=
  A.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ _ ih => ih) 0 0 (fun _ _ ih1 ih2 => ih1 + ih2) a

theorem ab_example : A.count (A.mk [B.mk 0 (A.mk []), B.leaf]) = 2 := rfl

end InModelNested
