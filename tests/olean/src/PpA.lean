module

public section

-- task #500: a definition of a proposition, its value not exposed (exported as the
-- assumption of its statement)
set_option linter.defProp false in
def pp : 2 + 2 = 4 := rfl

end
