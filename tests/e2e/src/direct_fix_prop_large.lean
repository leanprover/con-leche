--#export Loop.elim

/- End-to-end test (task #188): a ONE-constructor recursive `Prop`.  The
   official kernel gives it the LARGE eliminator (every field is a
   proposition — the recursive field itself), so `Loop.rec` eliminates
   into `Sort u`; the direct fixed-point route DECLINES the block
   positively (exit 2): at a squash instantiation the recursor would be
   the fixed point of its own unfolding on the proof point, which the
   route does not model yet (DESIGN.md, task #188).  The type is empty
   (no base constructor). -/

universe u

inductive Loop : Prop where
  | mk (h : Loop) : Loop

noncomputable def Loop.elim {α : Sort u} (h : Loop) : α :=
  Loop.rec (motive := fun _ => α) (fun _ ih => ih) h
