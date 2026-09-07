--#export Bad.self

/- End-to-end fixture (task #208; inductive audit #206, A10 / crack C8):
   an `unsafe inductive`.  Official skips positivity for unsafe blocks
   (inductive.cpp:443) and accepts.  con-leche's parser throws
   "unsafe inductive" (Frontend/ExportC.lean:550) -> exit 3, where unsafe
   DEFINITIONS decline positively with exit 2 (arena 141/142): the
   inductive path is the odd one out.

   The export needs lean4export's `--export-unsafe` flag, which
   scripts/export-fixture.sh does not pass; regenerate with

     LEAN_PATH=<work>:<exporter LEAN_PATH> lean4export IndUnsafe \
       --export-unsafe -- Bad.self

   at lean4export caccfbe / leanprover/lean4:v4.29.1 (the exporter every
   other fixture here uses).

   official: 0.  con-leche at master 700a06ca: 3 raw (our parser throws) and
   3 piped (the preprocessor fails on the block as well); both modes.
   Probe of record: _tmp/indaudit/probes/P/UnsafeInd.lean. -/
unsafe inductive Bad
  | mk (f : Bad → Nat)

unsafe def Bad.self (b : Bad) : Bad := b
