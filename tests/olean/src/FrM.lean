module
prelude
-- Guards task #464 (freshness): with FrY's files as FrX's, the module declares a name a
-- loaded module stores: rejected (Lean's kernel refuses to declare it twice).
public import Tiny
public import FrX
public section
def fresh : T := T.a
end
