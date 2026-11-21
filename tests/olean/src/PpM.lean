module
public import PpA
public import PpB

public section

-- task #500: both `pp`s meet here, two proofs of one proposition with different bodies.
-- Lean merges them (`isPropCheap` of `2 + 2 = 4`), and so does the modular check: the two
-- copies agree in every model because the statement is a proposition (inferred here).
theorem pp_use : 2 + 2 = 4 := pp

end
