module
prelude
-- Guards task #444: AxNA and AxNX loaded together; with AxNB's files as AxNX's, two axioms
-- `axn : Nat` meet: rejected, as Lean's import does (`isPropCheap` fails, and `Nat` is not
-- a proposition, so the two need not be one constant).
public import Init.Prelude
public import AxNA
public import AxNX
public section
noncomputable def axn_use : Nat := axn
end
