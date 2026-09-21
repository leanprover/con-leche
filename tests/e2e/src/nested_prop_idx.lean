--#export T

/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's Prop-indexed-container witness; on master it is a plain `tests/e2e-expected.txt` fixture, and the DESIGN section named below exists on that branch only.

   End-to-end test: a nested block whose CONTAINER's indices are
   PROP-sorted while the block's own member is TYPE-indexed (task #315
   M6, the model lane's DESIGN §U.17 (g) 1).

   `C α p` is indexed by a PROOF (`p : Prop`, index `h : p`), so its
   index universe is 0 — `towerSet` of its index telescope is a truth
   value.  `T` is indexed by `Nat`, so the auxiliary block's index
   universe is ≥ 1.  `T`'s constructor nests through `C` at `T 0` in
   `C`'s type PARAMETER, so the elimination copies `C`'s group into a
   block whose index universe is the larger one.

   OFFICIAL'S VERDICT: **ACCEPTED** (`lean` v4.33.0 elaborates and
   kernel-checks the block; `#print axioms T` reports none).  The shape
   is therefore NOT vacuous.  What this fixture pins is what OUR route
   does with it. -/

inductive C (α : Type) (p : Prop) : p → Type where
  | mk : α → (h : p) → C α p h

inductive T : Nat → Type where
  | mk : C (T 0) True True.intro → T 1
