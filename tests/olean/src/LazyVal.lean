module
prelude

/- A theorem whose value holds an object nothing else holds (the `bvar` of the deep lambda): a
   corrupted copy has a bad value only that theorem's check reads (task #481: a theorem's value
   stays in the file until then). -/

public section

inductive Yes : Prop where
  | intro

inductive Two : Type where
  | a
  | b

def other : Two := Two.a

theorem lazyProof : Yes :=
  (fun (a _ _ _ _ _ _ _ : Yes) => a) Yes.intro Yes.intro Yes.intro Yes.intro Yes.intro Yes.intro
    Yes.intro Yes.intro

end
