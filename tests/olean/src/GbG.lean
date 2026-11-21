module
-- Guards task #501 (a group's stored names): G's structure S.  The gate drops its recursor
-- S.rec from G's exported part, which no other name of the group reads.
public structure S where
  x : Nat
