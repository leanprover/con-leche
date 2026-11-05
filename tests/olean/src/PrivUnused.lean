module
prelude

/- A private theorem nothing refers to, and a definition whose value a corrupted copy of
   the theorem reads: every constant of the closure is checked, whatever its name. -/

public section

inductive Yes : Prop where
  | intro

inductive Two : Type where
  | a
  | b

def two : Two := Two.a

end

private theorem secret : Yes := Yes.intro
