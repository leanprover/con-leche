--#export T.rec T.rec_1

-- COLLECTED FROM `agent/nested-279m` (byte-identical on `agent/direct-nested`), where it was the nested lane's K.8 counterexample; on master it is a plain `tests/e2e-expected.txt` fixture and the K-record named below exists on those branches only.
-- K.8 counterexample: a pin component that is a λ over a Prop domain.
inductive Wrap (f : True → Type) where
  | mk : f trivial → Wrap f
inductive T where
  | mk : Wrap (fun (h : True) => T) → T
