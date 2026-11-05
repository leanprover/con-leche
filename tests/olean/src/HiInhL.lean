module
-- Guards task #409: `Lean.Server.Logging`, which imports HiInhX (and so HiInhD) privately;
-- a private constant exported with its value reads HiInhD's `hiD`.
import HiInhX
public section
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
private def hiL : Nat := hiD
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[expose] def hiLx : Nat := hiL
end
