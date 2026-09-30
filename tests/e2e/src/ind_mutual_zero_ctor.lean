--#export ZA.self ZB.elim

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): a mutual block with a ZERO-CONSTRUCTOR member.

   official: 0.  con-leche: 0.
   Probe of record: _tmp/indaudit/probes/P/MutualZeroCtor.lean. -/
mutual
  inductive ZA
    | mk (b : ZB)
  inductive ZB
end

theorem ZA.self (a : ZA) : a = a := rfl

def ZB.elim (b : ZB) : False :=
  ZB.rec (motive_1 := fun _ => False) (motive_2 := fun _ => False) (fun _ ih => ih) b
