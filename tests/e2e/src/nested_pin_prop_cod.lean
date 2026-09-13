--#export T.rec T.rec_1

-- a pin component that is a ∀ with a Prop CODOMAIN: the datum is
-- `ifAllZero []`, not `.never`, so the annotator rewrites the raw one.
inductive Wrap (A : Prop) : Prop where
  | mk : A → Wrap A
inductive T : Prop where
  | mk : Wrap (True → T) → T
