--#export TwoPins.self

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): the same container at TWO pins, and doubly nested
   (`List TwoPins`, `List (Option TwoPins)`, `List (List TwoPins)`).
   The in-process modeller's B3/B4 arms take it; official agrees.

   official: 0.  lech at master 700a06ca: 0 piped, 0 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/NestTwoPins.lean. -/
inductive TwoPins
  | a (l : List TwoPins)
  | b (l : List (Option TwoPins))
  | c (l : List (List TwoPins))

theorem TwoPins.self (x : TwoPins) : x = x := rfl
