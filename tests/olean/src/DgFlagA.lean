module
-- Guards task #399 (CompleteFlag pattern): an exposed public def whose value
-- reads a private auxiliary theorem of the same module (via Eq.mpr), so the
-- exported body mentions a name the importer does not load.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
public section
private theorem aux : (1 : Nat) + 1 = 2 := rfl
@[expose] def flagV : Nat := Eq.mpr (congrArg (fun _ => Nat) aux) (3 : Nat)
end
