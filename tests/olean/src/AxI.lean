module
prelude
-- Guards task #444: an axiom of a proposition Lean's cheap test does not recognise
-- (`id True`), meeting AxIT's theorem of its name and statement in AxIM.
public import Init.Prelude
public section
axiom axi : id True
end
