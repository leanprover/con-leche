module
prelude

/- Task #424: an importer of `RbH` (see there): its worker reads RbH's
   exported part alone, with `Lean.reduceBool` an assumption, and accepts;
   a closure check through RbH declines at RbH. -/

public import RbH

public section

def useRb : Bool := Lean.reduceBool Bool.true

end
