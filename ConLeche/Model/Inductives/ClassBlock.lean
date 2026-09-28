module

public import ConLeche.Model.Inductives.ClassNode
public import ConLeche.Model.Inductives.ClassSpace

public section

/-!
# The class facts' block: the class system of a class check's run (P2d, DESIGN CLASSCHECK / P2D4)

`ClassBlock` gathers what the class facts read of a class check's run at
a level assignment and a parameter frame, in SEMANTIC form: the
valuation space (one position per hole, `classSpace`), one container
node per container class (`ClassNode`: its container's recorded clause
at the key's frame), the ranks of the coherent reads, and the fill order.
From it:

* `ClassBlock.sys` — the class system (`ClassSys`): the container
  classes' operators are their nodes', nothing filled in them, a class
  spliced in at its own position (`spl`), ordered by rank;
* `ClassBlock.fill` — a container class's FILLER: the stage classes read
  through their representatives (`norm`), then its coherent reads
  spliced in, in the fill order, each as its node's carrier at the
  valuation so far;
* `ClassBlock.fill_ok` — the filler is a good operator as soon as every
  class of a smaller rank spliced in is (the rank induction's step);
* `ClassBlock.good` — every container class's operator, and every class
  spliced in, is good, given each node's identification with its crest's
  fit at the filled valuation, monotone and accessible
  (`ClassNode.Ident`, `sys_good`'s premises).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Name ClassInfo)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **A class check's run, as the class facts read it** (see the module
docstring).  The container classes are indexed by their POSITIONS (their
holes). -/
structure ClassBlock {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) where
  /-- the classes -/
  cls : List ClassInfo
  /-- the holes (positions), the members' first -/
  nh : Nat
  /-- the valuation space: level, parameter telescope, each hole's own
  telescope and index sort, the parameter frame -/
  w : Nat
  params : List AnnotTerm
  pars : Nat → List AnnotTerm
  ids : Nat → List AnnotTerm
  u : Nat → Nat
  ρp : Nat → V
  /-- the ranks of the coherent reads -/
  rank : Nat → Nat
  /-- the coherent reads, in the fill order -/
  fl : Nat → List Nat
  /-- a container class's node over the space -/
  node : Nat → ClassNode mp.base2.acval w nh
    ((classSpace nh w params pars ids u : LfpDatum V).idx φ ρp)
  /-- the representatives of a container class's stage positions -/
  rep : Nat → Nat → Nat
  hrep : ∀ c t, t < nh → rep c t < nh ∧
    (classSpace nh w params pars ids u : LfpDatum V).idx φ ρp (rep c t)
      = (classSpace nh w params pars ids u : LfpDatum V).idx φ ρp t

namespace ClassBlock

variable {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env} {φ : Name → Nat}
  (B : ClassBlock mp φ)

/-- The valuation space as an lfp datum over the holes. -/
@[expose] noncomputable def Dv : LfpDatum V := classSpace B.nh B.w B.params B.pars B.ids B.u

/-- The index sets of the positions. -/
@[expose] noncomputable def Is : Nat → V := B.Dv.idx φ B.ρp

theorem emptyT_mem : InTupleSpace B.w B.nh B.Is (ClassNode.emptyT B.Is) := ClassNode.emptyT_mem

/-- **The class system of the block**: the container nodes' operators,
nothing filled in them, a class spliced in at its own position. -/
@[expose] noncomputable def sys : ClassSys V where
  w := B.w
  K := B.nh
  Is := B.Is
  base := ClassNode.emptyT B.Is
  hbase := B.emptyT_mem
  grp := fun c => (B.node c).G
  free := fun c => (B.node c).F
  Φ := fun c => (B.node c).op
  fl := fun _ => []
  rk := B.rank
  spl := fun c t => t = c

/-- **The stage positions read through their representatives.** -/
@[expose] noncomputable def norm (c : Nat) (X : Nat → V) : Nat → V := fun t => X (B.rep c t)

/-- **A container class's filler**: its stage positions through their
representatives, then its coherent reads spliced in, in the fill order —
only those of a smaller rank. -/
@[expose] noncomputable def fill (c : Nat) (X : Nat → V) : Nat → V :=
  ClassSys.fillL (fun d => if _h : B.rank d < B.rank c then B.sys.T d else fun v => v) (B.fl c)
    (B.norm c X)

theorem norm_ok (c : Nat) : OpOk B.w B.nh B.Is (B.norm c) :=
  OpOk.through (rep := B.rep c) fun t ht => B.hrep c t ht

/-- **The filler is good** as soon as every class of a smaller rank
spliced in is. -/
theorem fill_ok (c : Nat) (hlow : ∀ d, B.rank d < B.rank c → OpOk B.w B.nh B.Is (B.sys.T d)) :
    OpOk B.w B.nh B.Is (B.fill c) := by
  refine OpOk.comp (Ψ := B.norm c) (B.norm_ok c) ?_
  refine B.sys.fillL_ok (fun d => ?_) (B.fl c)
  by_cases h : B.rank d < B.rank c
  · simp only [dif_pos h]; exact hlow d h
  · simp only [dif_neg h]; exact OpOk.id

/-- **Every container class's operator is good, and every class spliced
in**, given each node's identification at its filler, monotone and
accessible. -/
theorem good (I : ∀ c, (B.node c).Ident) (hfill : ∀ c, (I c).fill = B.fill c)
    (hmono : ∀ c Z Z', InTupleSpace B.w B.nh B.Is Z → InTupleSpace B.w B.nh B.Is Z' →
      TupleLe B.nh B.Is Z Z' → ∀ g, g < B.nh → (B.node c).G g → ∀ t, t ∈ˢ B.Is g → ∀ j fs,
        (I c).P Z g t j fs → (I c).P Z' g t j fs)
    (hacc : ∀ c, B.w ≠ 0 → ∃ A, A ∈ˢ (univ B.w : V) ∧ AccPred B.w B.nh B.Is (I c).Pel A) :
    ∀ c, OpOk B.w B.nh B.Is ((B.node c).op) ∧ OpOk B.w B.nh B.Is (B.sys.T c) :=
  ClassNode.sys_good B.sys B.node (fun _ => rfl) I
    (fun c hlow => by rw [hfill c]; exact B.fill_ok c hlow) hmono hacc

end ClassBlock

end ConLeche.Model
