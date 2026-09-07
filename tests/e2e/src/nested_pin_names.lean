--#export PTree.total_example

/- End-to-end test: nested-auxiliary iota rules whose stored parameter
   instantiations contain *binders* (a dependent nested occurrence:
   `DMap α (fun _ => PTree α)`) — the shape that declined the Mathlib
   stream at `Lean.PrefixTreeNode.rec_3`.  `PTree.total`'s
   below/brecOn machinery only typechecks when the auxiliary rules
   fire, and `total_example`'s `rfl` forces them on concrete majors.

   RAW since task #219 (`scripts/export-fixture.sh`).  The committed
   stream used to be this export run through the preprocessor and then
   perturbed (`scripts/mk_nested_pin_fixture.py`), so that the iota
   theorems' majors spelled the pin lambda under a *different binder
   name* than the recursor type — the drift the export format permits.
   That perturbation is gone twice over: the models are generated in
   process, by the same code that writes the recursor type, and since
   task #205 `Expr` carries no binder name at all. -/

inductive DMap (α : Type) (β : α → Type) where
  | leaf
  | node (k : α) (v : β k) (rest : DMap α β)

inductive PTree (α : Type) where
  | mk : Nat → DMap α (fun _ => PTree α) → PTree α

mutual
  def PTree.total {α : Type} : PTree α → Nat
    | .mk n m => n + PTree.totalMap m
  def PTree.totalMap {α : Type} : DMap α (fun _ => PTree α) → Nat
    | .leaf => 0
    | .node _ v rest => v.total + PTree.totalMap rest
end

theorem PTree.total_example :
    Eq (PTree.mk 2 (.node true (.mk 3 .leaf)
      (.node false (.mk 4 .leaf) .leaf)) : PTree Bool).total 9 :=
  rfl
