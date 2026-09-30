--#export T.rec T.rec_1

-- A pin component that is a λ over a Prop domain.
inductive Wrap (f : True → Type) where
  | mk : f trivial → Wrap f
inductive T where
  | mk : Wrap (fun (h : True) => T) → T
