--#export t0 t1 tu tProp

/- Corner case (lane PUNIT, 2026-09-29): unit-η at the stream's `PUnit`,
   which is an ordinary installed structure since `PUnit` is not pinned
   (the pinned-name unit-like branch `isUnitLikeTy` is gone): any two
   inhabitants are definitionally equal through the capability
   certificate `structUnitCert` (`caps.unitlike`, official's
   `is_def_eq_unit_like`) at a concrete universe, at a universe
   variable, and — at `PUnit.{0}`, a proposition — through proof
   irrelevance.  Official 0.  Today 0. -/

theorem t0 (a b : PUnit.{1}) : a = b := rfl
theorem t1 (a b : PUnit.{2}) : a = b := rfl
universe u in
theorem tu (a b : PUnit.{u+1}) : a = b := rfl
theorem tProp (a b : PUnit.{0}) : a = b := rfl
