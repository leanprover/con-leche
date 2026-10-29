-- con-leche's own (see UpKindThm): the theorem hole filled by an opaque
-- constant of its statement.  Comparator's verdict on a kind mismatch
-- (challenge-simple-mismatch): rejected, exit 1.
prelude
import Init.Data.Nat.Basic

opaque t : True := True.intro
