--#export CompTower.self

/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's witness that a copy field's `Pi`-tower is the MINT's and not the container's; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow`, `tests/nested-shadow-expected.txt` and the K-records named below exist on that branch only.

   A COPY FIELD WHOSE `Π`-TOWER IS THE MINT'S AND NOT THE CONTAINER'S
   (task #315, lane LE) — the witness that refutes the one-comparison
   spelling of step 4's object (3) (DESIGN, "WIDE (f3) STEP 4 (3)
   DESIGNED AGAINST THE TREE").

     K α  | mk   (a : α)                 -- the stored domain is the bvar `α`
     J β  | node (k : K (Nat → J β))     -- J's own pin is `K (Nat → J β)`
     CompTower | mk (j : J CompTower)

   `K` calls its only field ORDINARY (the domain `α` mentions no member
   of `K`) and `J`'s own elimination REWROTE it, because the component
   `Nat → J β` is an occurrence of `J`'s member.  So the copy of `K.mk`
   in `J`'s block has the field `Nat → <J-copy>` — depth `1` — while
   the CONTAINER's stored domain `Expr.bvar 0` has depth `0`.

   `nested_bvar_field` is the same family at the degenerate instance
   (`K (J β)`, both depths `0`) and `nested_pi_field` is the other arm
   (the tower is the CONTAINER's, `K α | mk (f : Nat → α)`, and the two
   depths agree).  This source is the one where they DISAGREE, which is
   why a K.72 that compares them would fire on an input official
   accepts.

   official (Lean v4.29.1): accepts.

   No `tests/e2e-expected.txt` row: the stream is here for the shadow
   gate, where the uniform route is measured.  It is committed beside
   this source and regenerates with
   `scripts/export-fixture.sh nested_comp_tower` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive K (α : Type) where
  | mk (a : α)

inductive J (β : Type) where
  | node (k : K (Nat → J β))

inductive CompTower where
  | mk (j : J CompTower)

theorem CompTower.self (x : CompTower) : x = x := rfl
