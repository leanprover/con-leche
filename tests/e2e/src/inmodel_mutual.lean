--#export InModelMutual.even_two InModelMutual.odd_one InModelMutual.Node.valOf InModelMutual.Forest.firstVal InModelMutual.Node.kidsSize InModelMutual.noA InModelMutual.a_of_b InModelMutual.Even.isZero InModelMutual.zero_isZero

/- End-to-end test: MUTUAL inductive blocks modelled IN-PROCESS (task
   #200, B1: index-free).  The raw export carries no `_model` artifacts
   for these blocks; the frontend's in-process modeller
   (`ConLeche/Frontend/InModel/Mutual.lean`) generates the tag and auxiliary
   families and the `_model` slots ahead of each block, and the modeled
   install consumes them exactly as it consumes lean-inductive-models'.

   Three shapes: a data pair with recursion across the members and
   several constructors (`Even`/`Odd`; `even_two`/`odd_one` force iota
   through the two recursors on concrete majors), a structure-like pair
   with a universe-polymorphic parameter (`Node`/`Forest`, whose
   elaborated projection functions are `.proj` nodes the frontend
   rewrites to recursor applications at the field sort the generated
   `proj_i.iota` artifacts name), and a `Prop` pair (`A`/`B`, small
   eliminator: `noA` eliminates by mutual induction into `False`). -/

namespace InModelMutual

mutual
inductive Even : Type where
  | zero : Even
  | succ : Odd → Even
inductive Odd : Type where
  | succ : Even → Odd
end

mutual
def Even.toNat : Even → Nat
  | .zero => 0
  | .succ o => o.toNat + 1
def Odd.toNat : Odd → Nat
  | .succ e => e.toNat + 1
end

theorem even_two : (Even.succ (Odd.succ Even.zero)).toNat = 2 := rfl
theorem odd_one : (Odd.succ Even.zero).toNat = 1 := rfl

def Even.isZero : Even → Bool
  | .zero => true
  | .succ _ => false

theorem zero_isZero : Even.zero.isZero = true := rfl

mutual
structure Node (α : Type u) where
  val : α
  kids : Forest α
structure Forest (α : Type u) where
  size : Nat
  first : Node α
end

def Node.valOf {α : Type u} (n : Node α) : α := n.val
def Forest.firstVal {α : Type u} (f : Forest α) : α := f.first.val
def Node.kidsSize {α : Type u} (n : Node α) : Nat := n.kids.size

mutual
inductive A : Prop where
  | mk : B → A
inductive B : Prop where
  | mk : A → B
end

theorem a_of_b (b : B) : A := A.mk b

theorem noA : ∀ a : A, False := fun a =>
  A.rec (motive_1 := fun _ => False) (motive_2 := fun _ => False)
    (fun _ ih => ih) (fun _ ih => ih) a

end InModelMutual
