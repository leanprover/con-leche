--#export A.self

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): a MUTUAL block with an index whose DOMAIN's type is not a
   syntactic sort (`MyIdx : U`, `U := Type`).  The in-process modeller's
   syntactic sort inferer (Frontend/InModel/Kit.sortOf) has to read the
   tag's universe off it; both official and lech accept, piped and raw.

   official: 0.  lech at master 700a06ca: 0 piped, 0 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/IdxDefHeadSort.lean. -/
def U := Type
def MyIdx : U := Nat

mutual
  inductive A : MyIdx → Prop
    | mk (n : MyIdx) (b : B n) : A n
  inductive B : MyIdx → Prop
    | mk (n : MyIdx) : B n
end

theorem A.self (n : MyIdx) (a : A n) : a = a := rfl
