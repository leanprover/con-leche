--#export NestedStructProj.use_label NestedStructProj.use_kids NestedStructProj.use_sum NestedStructProj.use_width NestedStructProj.Stream'.second

/- End-to-end test: the projection functions of a NESTED structure
   (`kids : List Tree`) and of a directly RECURSIVE one (`Stream'.tail :
   Unit → Stream'`), rewritten to recursor applications by the frontend
   (`Lech/Frontend/ProjRec.lean`, 2026-09-06; the mutual twin is
   `mutual_struct_proj.lean`).

   `Tree.rec` carries two motives (the tree's and the auxiliary one
   over `List Tree`) and four minors (`node`, then `List.nil`/`List.cons`
   at the container); `Tree.label`/`Tree.kids` become
   `Tree.rec (motive_1 := fun _ => F_i) (motive_2 := fun _ => PUnit)
   … self`, and the constructor minor ignores the auxiliary inductive
   hypothesis.  `Stream'` is a reflexive recursive structure with no
   base case (uninhabited), so its projections are checked but never
   reduced.  `sum` is the nested-recursion consumer whose
   equation-compiler output reads `Tree.kids` inside `brecOn`, and the
   `rfl`s force iota through the rewritten projections. -/

namespace NestedStructProj

structure Tree where
  label : Nat
  kids : List Tree

structure Stream' where
  head : Nat
  tail : Unit → Stream'

def theTree : Tree := ⟨1, [⟨2, []⟩, ⟨3, []⟩]⟩

theorem use_label : Eq theTree.label 1 := rfl
theorem use_kids : Eq theTree.kids.length 2 := rfl

mutual
  def Tree.sum : Tree → Nat
    | .mk l ts => l + Tree.sumList ts
  def Tree.sumList : List Tree → Nat
    | [] => 0
    | t :: ts => t.sum + Tree.sumList ts
end

theorem use_sum : Eq theTree.sum 6 := rfl

def Tree.width (t : Tree) : Nat := t.kids.length
theorem use_width : Eq theTree.width 2 := rfl

def Stream'.second (s : Stream') : Nat := (s.tail ()).head

end NestedStructProj
