module
-- Guards task #399: importer unfolds flagV by rfl (Lean accepts).
public import DgFlagA
public theorem flagB : flagV = 3 := by unfold flagV; rfl
public theorem flagB' : flagV = 3 := rfl
