module
prelude

public import Init.Prelude

public section

-- not exported (private)
private def po_secret : Nat := 7

-- private but exported with its value (Lean's `privateInPublic`), a value
-- that reads the private-only `po_secret` (Mathlib's WittVector case):
-- an importer at the exported level reads `po_pub` as an assumption
set_option backward.privateInPublic true in
private def po_pub : Nat := po_secret

def po_use : Nat := 1

end
