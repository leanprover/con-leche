module

public import UsA

-- an own unsafe definition reading an imported unsafe one: it is no record of this module,
-- and what it reads is checked by nobody (Lean's kernel checks unsafe definitions only as
-- unsafe); the safe theorem is this module's one record
public unsafe def usUse (n : Nat) : Nat := usPeek n

public theorem usSafe_eq : usSafe = 3 := rfl
