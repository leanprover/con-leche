module

-- an unsafe definition: no record of its module, read by an importer's own unsafe definition
public unsafe def usPeek (n : Nat) : Nat := (unsafeCast n : Nat) + 1

@[expose] public def usSafe : Nat := 3
