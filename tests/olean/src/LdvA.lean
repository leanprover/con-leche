module
-- (task #421 cont. 25) an exported block whose positivity check unfolds a
-- definition of LdvQ.  tests/lazy.sh makes the import of LdvQ private in a
-- copy of the file (as for LdgA): LdvA's exported view then lacks ldvW,
-- the completed exported view holds it as a statement only, where the
-- block's check cannot unfold it: the block degrades -- its type former
-- and constructors to the assumptions of their statements, its recursor
-- nothing.
public import LdvQ
set_option genSizeOf false in
public inductive LdvB : Type where
  | mk : ldvW LdvB → LdvB
