module
prelude

public import NlB
public import NlY

public section

-- `nl` is NlY's: NlX, in the closure through NlB's private import, is not
-- loaded, and its `nl` never meets this one
theorem nlm : Eq nl nl := rfl

end
