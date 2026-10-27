module
prelude

public section

inductive T : Type where
  | a
  | b

def idT (x : T) : T := x

inductive Yes : Prop where
  | intro

theorem yes : Yes := Yes.intro

end
