--#export H
/- End-to-end fixture (task #543; found in task #451): a 25-member mutual block —
   a hub `H` with one constructor per member `Tᵢ` and members that point
   back — whose recursors close telescopes of 25 motives and 49 minors.  The
   radar benchmark `deriving_mutual_block`'s block at a smaller size.

   The pattern: a recursor type is closed binder by binder
   (`closeTelescope`, the innermost-first `abstract1` chain).  con-leche's
   abstraction stops at a subterm whose cached free-variable range is below
   the binder, so each pass walks only what mentions the binder's own
   variable; a checker without that cutoff walks every subterm that
   mentions an outer variable (the motives, everywhere) once per binder,
   quadratic in the telescope.  The finding came from InLean (task #451,
   the twin on `Lean.Expr`, which caches `hasFVar` but no range): it now
   closes the telescope directly, one bulk pass per domain.

   A performance fixture: the block compiled as a module and added to the
   kernel environment of `Init` again, InLean's heartbeats were 4.7M with the
   chain and 1.8M with the direct closing (official 0.13M); at the radar
   file's 42 members, 29.4M and 8.2M (official 2.1M, con-leche 17.6M).

   official: 0.  con-leche: 0. -/

mutual
inductive H where
  | c0 : T0 → H
  | c1 : T1 → H
  | c2 : T2 → H
  | c3 : T3 → H
  | c4 : T4 → H
  | c5 : T5 → H
  | c6 : T6 → H
  | c7 : T7 → H
  | c8 : T8 → H
  | c9 : T9 → H
  | c10 : T10 → H
  | c11 : T11 → H
  | c12 : T12 → H
  | c13 : T13 → H
  | c14 : T14 → H
  | c15 : T15 → H
  | c16 : T16 → H
  | c17 : T17 → H
  | c18 : T18 → H
  | c19 : T19 → H
  | c20 : T20 → H
  | c21 : T21 → H
  | c22 : T22 → H
  | c23 : T23 → H
  | leaf : H
inductive T0 where
  | mk : H → T0
inductive T1 where
  | mk : H → T1
inductive T2 where
  | mk : H → T2
inductive T3 where
  | mk : H → T3
inductive T4 where
  | mk : H → T4
inductive T5 where
  | mk : H → T5
inductive T6 where
  | mk : H → T6
inductive T7 where
  | mk : H → T7
inductive T8 where
  | mk : H → T8
inductive T9 where
  | mk : H → T9
inductive T10 where
  | mk : H → T10
inductive T11 where
  | mk : H → T11
inductive T12 where
  | mk : H → T12
inductive T13 where
  | mk : H → T13
inductive T14 where
  | mk : H → T14
inductive T15 where
  | mk : H → T15
inductive T16 where
  | mk : H → T16
inductive T17 where
  | mk : H → T17
inductive T18 where
  | mk : H → T18
inductive T19 where
  | mk : H → T19
inductive T20 where
  | mk : H → T20
inductive T21 where
  | mk : H → T21
inductive T22 where
  | mk : H → T22
inductive T23 where
  | mk : H → T23
end
