--#export t_quot0
/- End-to-end fixture (task #423 soundness): ι case 3 at `Quot.lift` on
   `Quot.{0}` — a quotient of a proposition, itself a proposition — at the
   ground site.  The constructor `Quot.mk` is written in the theorem's
   type, so the elaborator does not abstract it into a theorem.

   Official accepts (v4.35 and the nightly: `Quot.lift` reduces on
   `Quot.mk` with no check).  Con-leche today (engine off) accepts: the
   incumbent fires case 3 with its certificates.  Engine on (task #423
   soundness, no hand-back): **decline (2)**, because `Red.iota`'s case 3
   asks for the constructor's full-grade certificates, which the engine
   does not build.  Target 0; after Lean's kernel renovation (lean4#14977
   and successors: `Quot` is never a proposition) the case disappears. -/

theorem t_quot0 :
    @Quot.lift True (fun _ _ => True) Bool (fun _ => true) (fun _ _ _ => rfl)
      (Quot.mk _ trivial) = true := rfl
