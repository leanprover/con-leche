--#export BvarField.self

/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's witness that a shared container's STORED field domain need not be constant-headed at the owner's arm; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow`, `tests/nested-shadow-expected.txt`, `docs/NESTED.md` and the K-records named below exist on that branch only.

   A CONTAINER FIELD WHOSE STORED DOMAIN IS A BARE PARAMETER (task
   #315, lane LE) — the MINIMAL witness that the shared container's
   stored field domain need not be constant-headed where the OWNER's
   copy rewrote it.

     K α  | mk   (a : α)            -- the field is the bvar `α`
     J β  | node (k : K (J β))      -- J's own pin is `K (J β)`
     BvarField | mk (j : J BvarField)

   `K` calls its only field ORDINARY (the domain mentions no member of
   `K`), and `J`'s own elimination REWROTE it: `α := J β` is an
   occurrence of `J`'s member, so the copy of `K.mk` in `J`'s block has
   a RECURSIVE field.  The outer block copies both groups, so the copy
   of `K` there has `J`'s own pin as its OWNER — which is the arm K.67
   and K.69 speak at.  The stored domain at that arm is `Expr.bvar 0`,
   and its `getAppFn` is no `.const`.

   What the RECOMPUTATION reads there IS constant-headed: the bvar is
   instantiated at the owner's component `J β`, so `ordRootFired`
   answers `true` and both K.67's and K.68's lookups succeed.  The
   distinction — the STORED domain's head against the RECOMPUTATION's —
   is the one DESIGN's "THE STORED DOMAIN'S HEAD IS NOT THE
   RECOMPUTATION'S" row is about.

   `nested_pin_nocollide` (`Pair α β | mk (a : α) (b : β)`) and
   `nested_p04` exhibit the same shape inside larger fixtures; this
   source is the smallest one that does, and the only one whose OUTER
   block is measured in the shadow gate.

   official (Lean v4.29.1): accepts.  con-leche: accepts (exit 0), and
   the uniform route accepts both nested blocks in shadow —
   `J=accept,BvarField=accept,` in `tests/nested-shadow-expected.txt`.

   No `tests/e2e-expected.txt` row: the stream is here for the shadow
   gate, where the uniform route is measured.  It is committed beside
   this source and regenerates with
   `scripts/export-fixture.sh nested_bvar_field` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive K (α : Type) where
  | mk (a : α)

inductive J (β : Type) where
  | node (k : K (J β))

inductive BvarField where
  | mk (j : J BvarField)

theorem BvarField.self (x : BvarField) : x = x := rfl
