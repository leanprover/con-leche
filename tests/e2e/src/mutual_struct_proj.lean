--#export MutualStructProj.use_n MutualStructProj.use_v MutualStructProj.use_h MutualStructProj.use_kids MutualStructProj.use_size MutualStructProj.use_nodes MutualStructProj.Node.kidsSize MutualStructProj.use_kidsSize

/- End-to-end test: the projection functions of a MUTUAL pair of
   structures.

   `Node`/`Forest` are `structure`s in one `mutual` block, so the
   elaborator emits `Node.n := fun self => self.1` (a `.proj` node) for
   every field; the official kernel types `.proj` on any
   structure-like type (one constructor, zero indices), and a `.proj`
   on a mutual member occurs in the Mathlib stream (at
   `Lean.Meta.Grind.AC.DiseqCnstr.lhs`).

   The block exercises, per field: a dependent field (`v : Fin n`,
   whose projection's type mentions the earlier projection `Node.n
   self`), a *proof* field (`h`, field sort `Prop`), and a recursive
   field across the block (`kids : Forest`).  `Forest.nodes : Fin 0 →
   Node` keeps the pair inhabited without a nested occurrence.  The
   `rfl` theorems force iota through the projections on constructor
   applications; `kidsSize` uses a projection inside a later
   definition. -/

namespace MutualStructProj

mutual
structure Node where
  n : Nat
  v : Fin n
  h : v.val < n
  kids : Forest
structure Forest where
  size : Nat
  nodes : Fin 0 → Node
end

def theForest : Forest := ⟨3, fun x => x.elim0⟩
def theNode : Node := ⟨2, ⟨1, by decide⟩, by decide, theForest⟩

theorem use_n : Eq theNode.n 2 := rfl
theorem use_v : Eq theNode.v.val 1 := rfl
theorem use_h : theNode.v.val < theNode.n := theNode.h
theorem use_kids : Eq theNode.kids.size 3 := rfl
theorem use_size : Eq theForest.size 3 := rfl
theorem use_nodes : Eq (theForest.nodes) (fun x => x.elim0) := rfl

def Node.kidsSize (x : Node) : Nat := x.kids.size
theorem use_kidsSize : Eq theNode.kidsSize 3 := rfl

end MutualStructProj
