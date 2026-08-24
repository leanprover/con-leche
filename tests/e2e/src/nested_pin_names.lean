--#export PTree.total_example

/- End-to-end test: nested-auxiliary iota rules whose stored parameter
   instantiations contain *binders* (a dependent nested occurrence:
   `DMap α (fun _ => PTree α)`), with the iota theorems' majors
   spelling the pin lambda under a *different binder name* than the
   recursor type (post-export perturbation, see
   `scripts/mk_nested_pin_fixture.py`) — the drift the export format
   permits (arenas intern name-insensitively) and the shape that
   declined the Mathlib stream at `Lean.PrefixTreeNode.rec_3`.
   `checkIotaThmN` must pin the major up to display-only binder names.
   `PTree.total`'s below/brecOn machinery only typechecks when the
   auxiliary rules fire, and `total_example`'s `rfl` forces them on
   concrete majors. -/

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
