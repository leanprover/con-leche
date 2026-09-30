--#export MA.self

/- End-to-end fixture (task #208; inductive audit #206, A3 / crack C3):
   a MUTUAL block whose formers are declared at a definition unfolding to
   `Type`.  Official whnf's each member's former before counting
   parameters and comparing result sorts (inductive.cpp:222-250), so it
   accepts.

   official: 0.  con-leche: 0.
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
