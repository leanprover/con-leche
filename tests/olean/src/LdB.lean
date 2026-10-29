module
prelude

public import Init.Prelude
import LdX

public section

-- a definition whose value reads a module this module imports privately
-- (its value is not exported: an importer at the exported level reads it
-- as an assumption)
def ldb : Nat := ldx

end
