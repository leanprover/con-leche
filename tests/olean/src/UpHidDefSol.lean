-- con-leche's own (see UpHidDef): UpKindDef's definition hole filled by a
-- definition the solution re-exports from UpHidDef, whose value is hidden
-- there: the challenge's context sees an assumption whose record's kind
-- it cannot see, and accepts it (the definition is checked in its home).
module
prelude

public import UpHidDef
