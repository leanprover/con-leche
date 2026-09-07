--#export MA.self

/- End-to-end fixture (task #208; inductive audit #206, A3 / crack C3):
   a MUTUAL block whose formers are declared at a definition unfolding to
   `Type`.  Official whnf's each member's former before counting
   parameters and comparing result sorts (inductive.cpp:222-250), so it
   accepts.

   lech's in-process modeller requires a syntactic `stripPis … .sort`
   (Frontend/InModel/Mutual.lean:158-166), and the preprocessor's native
   predicate (`lechFormerTelescope`) leaves the block to the tool, whose
   own generator then reports "a mutual one-layer owner does not end in a
   sort" -> exit 3.  Raw, the in-process modeller declines: "former MA is
   not a telescope ending in a sort".

   official: 0.  lech at master 700a06ca: 3 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/DefHeadMutualOnly.lean. -/
def MyType := Type

mutual
  inductive MA : MyType
    | leaf
    | node (b : MB)
  inductive MB : MyType
    | node (a : MA)
end

theorem MA.self (a : MA) : a = a := rfl
