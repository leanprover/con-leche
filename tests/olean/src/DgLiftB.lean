module
-- Guards task #399: importer goes by rfl through liftV (Lean accepts).
public import DgLiftA
public theorem liftB : liftV = 6 := rfl
