module
-- (task #421) an exported block reading a constant of LdgQ.  tests/lazy.sh
-- makes the import of LdgQ private in a copy of the file (a header Lean
-- does not write for a public statement reading LdgQ): LdgA's exported
-- view then lacks `ldgT`, and the block is installed at the completed
-- exported view (with `ldgT`'s statement, #421 cont. 25), at LdgA and at
-- every importer alike; with the import dropped, a reject.
public import LdgQ
public inductive LdgB : Type where
  | mk : ldgT → LdgB
