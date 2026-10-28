module
prelude

public import Init.Prelude
import all LdB

public section

-- `import all LdB` loads LdB's private import LdX too (Lean's rule), so
-- `ldb` unfolds to `ldx` and on to `5`
private theorem ldm : Eq ldb 5 := rfl

end
