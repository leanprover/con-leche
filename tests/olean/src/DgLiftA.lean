module
-- Guards task #399 (groupLift pattern): exposed def taking a proof argument
-- filled by a private theorem.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
public section
@[expose] def liftF (n : Nat) (_h : n = n) : Nat := n + 1
private theorem selfEq : (5 : Nat) = 5 := rfl
@[expose] def liftV : Nat := liftF 5 selfEq
end
