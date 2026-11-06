module
prelude
-- Guards task #464 (the clash rule): ClashA and ClashX loaded together; with ClashB's files
-- as ClashX's, two different constants `clash` meet: rejected (as Lean's import does).
public import ClashA
public import ClashX
