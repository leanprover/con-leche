module
prelude

public import Init.Prelude

public section

-- a definition of a proposition whose statement Lean's cheap test
-- (`isPropCheap`) does not see as one: `id True`; exported as the
-- assumption of its statement (its value is not exposed)
def pd : id True := True.intro

end
