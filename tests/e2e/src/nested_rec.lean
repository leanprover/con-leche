--#export Tree.size_example

/- End-to-end test: verified firing of nested-auxiliary recursor rules
   (task #48).

   `Tree` is a nested inductive with a parameter: the auxiliary
   recursors (`Tree.rec_1` over `List (Tree α)`) have rules whose
   constructor parameters are fixed instantiations (`List.nil.{0}`/
   `List.cons.{0}` at `Tree α`), i.e. `.nested`-certified iota rules
   with an *open* stored parameter instantiation (referencing the
   recursor's `α` binder).  `Tree.size`'s equation-compiler output goes
   through `Tree.below_1`/`Tree.brecOn_1`, whose bodies only typecheck
   when those rules fire — the exact shape that blocked init-prelude at
   `Lean.Syntax.brecOn_1.go` — and `size_example`'s `rfl` additionally
   forces the rules to fire on concrete majors. -/

inductive Tree (α : Type) where
  | node : α → List (Tree α) → Tree α

mutual
  def Tree.size {α : Type} : Tree α → Nat
    | .node _ ts => Tree.sizeList ts + 1
  def Tree.sizeList {α : Type} : List (Tree α) → Nat
    | [] => 0
    | t :: ts => t.size + Tree.sizeList ts
end

theorem Tree.size_example :
    Eq (Tree.node true [Tree.node false [], Tree.node true []]).size 3 :=
  rfl
