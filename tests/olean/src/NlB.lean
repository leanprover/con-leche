module
prelude

public import Init.Prelude
-- a private import: an importer of NlB does not load NlX
import NlX

public section

def nlb : Nat := 3

private theorem nlb_x : Eq nl nl := rfl

end
