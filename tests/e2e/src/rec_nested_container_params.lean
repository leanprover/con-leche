--#export T.rec T.rec_1 T.useLeaf T.useMk

/- A nested block whose container has a different parameter count: the
   block `T` has one parameter, the container `P2` two.  An auxiliary
   recursor's firing data are read off its record alone (task #480): the
   major's domain `P2 γ (T γ)` has no index variables, so all of its
   arguments are the pins, without looking `P2` up.  The ι laws below fire
   the auxiliary recursor's rule.  Official 0.  Target 0. -/

set_option autoImplicit false
universe u

inductive P2 (α β : Type u) : Type u where
  | mk : α → β → P2 α β

inductive T (γ : Type) : Type where
  | leaf : γ → T γ
  | node : P2 γ (T γ) → T γ

/-- `T.rec` with a large motive: the number of nodes. -/
noncomputable def T.count {γ : Type} : T γ → Nat :=
  @T.rec γ (fun _ => Nat) (fun _ => Nat) (fun _ => 0) (fun _ ih => ih + 1) (fun _ _ ih => ih)

/-- `T.rec_1` with the same minors, at the container. -/
noncomputable def P2.count {γ : Type} : P2 γ (T γ) → Nat :=
  @T.rec_1 γ (fun _ => Nat) (fun _ => Nat) (fun _ => 0) (fun _ ih => ih + 1) (fun _ _ ih => ih)

theorem T.useLeaf : T.count (T.leaf true) = 0 := rfl

theorem T.useMk :
    P2.count (P2.mk true (T.node (P2.mk false (T.leaf true)))) = 1 := rfl
