--#export U.k U.uniq

/- End-to-end fixture (task #208; inductive audit #206, A2 / crack C2):
   a K-TARGET / unit-like `Prop` block whose type former is declared at a
   DEFINITION (`MyProp := Prop`).  Official whnf's the former's type
   (`check_inductive_types`, inductive.cpp:222-245) and reads K-likeness
   off the whnf'd sort (`init_K_target`, :551-573), so it accepts the
   block, its K reduction and proof irrelevance on it.

   lech's structure route needs a SYNTACTIC `∀ p⃗, Sort` (Parts.lean:469),
   so the block is not `St`; the preprocessor models it instead, and the
   tool's own `U._model.unitlike` statement check fails -> the tool exits
   3 and "a preprocessor reject is our reject".  With the preprocessor
   unavailable the raw stream declines for a missing model.

   official: 0.  lech at master 700a06ca: 3 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/DefHeadK.lean. -/
def MyProp := Prop

inductive U : MyProp
  | u

/-- K use: the recursor on a neutral major reduces to the minor. -/
theorem U.k (h : U) : @U.rec (fun _ => Nat) 5 h = 5 := rfl

/-- Unit-likeness / proof irrelevance. -/
theorem U.uniq (a b : U) : a = b := rfl
