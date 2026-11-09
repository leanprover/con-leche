--#export Bool

/- `Bool` stored at a definition: declined.  The frontend puts a stream's `Bool` at the front of the
   fold, ahead of the definition it is declared at, so past the decline it would be an unknown
   constant, a reject official does not make.  Accepting it asks the frontend to hoist what the
   record depends on.
   official: 0 (run).  con-leche: 2. -/

prelude

def T := Type

inductive Bool : T
  | false
  | true
