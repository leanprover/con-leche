--#export ZA.self ZB.elim

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): a mutual block with a ZERO-CONSTRUCTOR member.  Both official
   and con-leche (in-process modeller, route `ZA inmodel`) accept, piped and
   raw.  A regression guard for the in-process modeller's empty-member
   arm.

   official: 0.  con-leche at master 700a06ca: 0 piped, 0 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/MutualZeroCtor.lean. -/
mutual
  inductive ZA
    | mk (b : ZB)
  inductive ZB
end

theorem ZA.self (a : ZA) : a = a := rfl

def ZB.elim (b : ZB) : False :=
  ZB.rec (motive_1 := fun _ => False) (motive_2 := fun _ => False) (fun _ ih => ih) b
