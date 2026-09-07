--#export InModelGroups.m_example InModelGroups.n_example InModelGroups.h_example InModelGroups.p_example

/- End-to-end test: CONTAINER GROUPS modelled IN-PROCESS (task #200,
   B4).  A block nesting through a container that is itself nested or
   mutual: the kernel flattens the container's whole recursor family into
   the block's mimics, and the in-process modeller packs/unpacks such a
   group with one application of each family member's recursor at the
   group's motives.

   `TT` is `Lean.Widget.TaggedText`-shaped (nested through `List`), `M`
   nests through `TT M` (group `{TT M, List (TT M)}`); `F`/`G` are a
   mutual pair, `N` nests through `F N` (group `{F N, G N}`); `H` nests
   through `TT (List H)` (a group whose pin is another mimic's carrier:
   `List H`, `TT (List H)`, `List (TT (List H))`). -/

namespace InModelGroups

inductive TT (α : Type) where
  | text : α → TT α
  | node : List (TT α) → TT α

inductive M where
  | mk : TT M → M

noncomputable def M.size (m : M) : Nat :=
  M.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ ih => ih) (fun _ ih => ih) 0 (fun _ _ ih1 ih2 => ih1 + ih2) m

theorem m_example : M.size (M.mk (TT.node [TT.text (M.mk (TT.text (M.mk (TT.node [])))), TT.node []])) = 3 := rfl

mutual
inductive F (α : Type) where
  | mk : G α → F α
inductive G (α : Type) where
  | nil : G α
  | cons : α → F α → G α → G α
end

inductive N where
  | mk : F N → N

noncomputable def N.size (n : N) : Nat :=
  N.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ ih => ih) 0 (fun _ _ _ ih1 ih2 ih3 => ih1 + ih2 + ih3) n

theorem n_example : N.size (N.mk (F.mk (G.cons (N.mk (F.mk G.nil)) (F.mk G.nil) G.nil))) = 2 := rfl

inductive H where
  | mk : TT (List H) → H

noncomputable def H.size (h : H) : Nat :=
  H.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ ih => ih) (fun _ ih => ih) 0 (fun _ _ ih1 ih2 => ih1 + ih2)
    0 (fun _ _ ih1 ih2 => ih1 + ih2) h

theorem h_example : H.size (H.mk (TT.node [TT.text [H.mk (TT.text [])]])) = 2 := rfl

structure Box (α : Type u) where
  val : α

inductive P (α : Type u) where
  | leaf : α → P α
  | wrap : Box (P α) → P α

noncomputable def P.depth {α : Type u} (p : P α) : Nat :=
  P.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ => 0) (fun _ ih => ih + 1) (fun _ ih => ih) p

theorem p_example : P.depth (P.wrap ⟨P.wrap ⟨P.leaf (7 : Nat)⟩⟩) = 2 := rfl

end InModelGroups
