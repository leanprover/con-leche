module
-- Guards task #399 (infer pattern): exposed def reads a private DEF.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
public section
private def pv : Nat := 7
@[expose] def inferV : Nat := pv
end
