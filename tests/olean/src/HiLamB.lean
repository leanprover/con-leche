module
-- Guards task #409: the importer's `rfl` compares the two λs, whose
-- bodies differ and read the hole `hlEq` (Lean accepts: its kernel never
-- infers `hlEq`).  The verified mode infers the two bodies' types after
-- their comparison (`defeqLamsInnerI`) and meets the hole: declined
-- (task #409, interim; target: accept, once the hole design is revisited).
public import HiLamA
public theorem hlB : hlF = hlF2 := rfl
