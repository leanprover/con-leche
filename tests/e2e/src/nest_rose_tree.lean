--#export T.rec T.rec_1 T.rec_2 T.useMk T.useNode T.useCons

/- A block nested through a container
   that is ITSELF nested — `T` through `R T` (a rose tree), which is
   `L (R T)` (a list) inside.  Official's family is `T.rec` (major
   `T`), `T.rec_1` (major `R T`, matching `node` and calling
   `T.rec`/`T.rec_2`) and `T.rec_2` (major `L (R T)`, matching
   `nil`/`cons` and calling `T.rec_1`/`T.rec_2`), all with `Sort u`
   motives (large elimination).  The three `use*` theorems pin one ι
   law of each recursor by `rfl`. -/

set_option autoImplicit false
universe u

inductive L (α : Type u) : Type u where
  | nil : L α
  | cons : α → L α → L α

inductive R (α : Type u) : Type u where
  | node : α → L (R α) → R α

inductive T : Type where
  | leaf : T
  | mk : R T → T

/-- `T.rec` with a large motive: the number of leaves. -/
noncomputable def T.count : T → Nat :=
  @T.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    1 (fun _ ih => ih) (fun _ _ ih₁ ih₂ => ih₁ + ih₂) 0 (fun _ _ ih₁ ih₂ => ih₁ + ih₂)

/-- `T.rec_1` with the same minors: the number of leaves in a rose tree. -/
noncomputable def R.count : R T → Nat :=
  @T.rec_1 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    1 (fun _ ih => ih) (fun _ _ ih₁ ih₂ => ih₁ + ih₂) 0 (fun _ _ ih₁ ih₂ => ih₁ + ih₂)

/-- `T.rec_2` with the same minors: the number of leaves in a forest. -/
noncomputable def L.count : L (R T) → Nat :=
  @T.rec_2 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    1 (fun _ ih => ih) (fun _ _ ih₁ ih₂ => ih₁ + ih₂) 0 (fun _ _ ih₁ ih₂ => ih₁ + ih₂)

theorem T.useMk : T.count (T.mk (R.node T.leaf L.nil)) = 1 := rfl

theorem T.useNode : R.count (R.node (T.mk (R.node T.leaf L.nil)) (L.cons (R.node T.leaf L.nil) L.nil)) = 2 := rfl

theorem T.useCons : L.count (L.cons (R.node T.leaf L.nil) (L.cons (R.node T.leaf L.nil) L.nil)) = 2 := rfl
