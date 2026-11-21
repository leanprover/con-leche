module
prelude
public import Init.Prelude

-- task #618: see CxM.  CxX1 is a private import: an importer of CxA does not load it
import CxX1
public import CxZ

public section

def cn : cc := True

end
