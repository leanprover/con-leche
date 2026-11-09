module
-- Guards task #415: P2 declares a theorem of the same name and statement,
-- by another proof (two proofs of one statement are one constant).
public theorem teq : (1 : Nat) + 1 = 2 := by decide
