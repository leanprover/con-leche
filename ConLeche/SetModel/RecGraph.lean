module

public import ConLeche.SetTheory.Derive.LfpFam
import ConLeche.SetTheory.Derive.Pt
@[expose] public section

/-!
# The recursion theorem by lfp induction (task #202, Stage A2)

The recursive squash regime's large eliminator: the family lives at
`Prop` (its fibres are truth values, the sole proof the point) and the
recursor eliminates into `Sort ℓ`, `ℓ ≠ 0`.  The recursor's value at an
index `i` is determined by the recursion equation `R i = st i (R on the
predecessors of i)` — well-founded along the family's least fixed
point, which is why it exists and is unique.

This module states that abstractly, `Expr`-free: over an index set `I`
with predecessor sets `pred i ⊆ I`, a bound `B i ∈ univ ℓ` and a step
`st i g` (`g` a choice function of predecessor values), the GRAPH
functor `recGraphStep` sends a family `S` to the family of values
`st i g` for `g ∈ Π_{j ∈ pred i} S j` (within `B i`); it is monotone
and `B` is a closed family, so its least fixed point `recGraph` exists,
and at every index whose `Acc`-family fibre (`accFam`: inhabited iff
`Cond i` and every predecessor's fibre is) is inhabited, `recGraph`'s
fibre is a SINGLETON (`recGraph_exists_unique`) — by
`lfpFamSet_induction` on the `Acc` family: the predecessors' fibres
are singletons, the graph of their elements witnesses existence
(`app_lfpFamSet_eq`), and any element is the step at that same choice
function, by function extensionality on `piSet`.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

section RecGraph

variable (ℓ : Nat) (I : V) (pred : V → V) (B : V → V) (st : V → V → V)


variable {ℓ I pred B st}


end RecGraph

/-! ## The `Acc` family -/

section AccFam

variable (I : V) (pred : V → V) (Cond : V → Prop)


variable {I pred Cond}


end AccFam

/-! ## The recursion theorem -/

section RecTheorem

variable {ℓ : Nat} {I : V} {pred : V → V} {B : V → V} {st : V → V → V} {Cond : V → Prop}


/-- The graph's selector: the fibre's element (the point off the graph). -/
noncomputable def recSel (G : V) (i : V) : V :=
  open Classical in
  if h : ∃ v, v ∈ˢ app G i then Classical.choose h else pt

theorem recSel_mem {G i : V} (h : ∃ v, v ∈ˢ app G i) : recSel G i ∈ˢ app G i := by
  unfold recSel
  rw [dif_pos h]
  exact Classical.choose_spec h


end RecTheorem


end ConLeche.SetTheory
