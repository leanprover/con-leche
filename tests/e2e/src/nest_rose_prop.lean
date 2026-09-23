--#export P.rec P.rec_1 P.rec_2 P.useMk

/- Lane NESTTREE (2026-09-23): the `Prop` twin of `nest_rose_tree` —
   `P` nested through `RP P`, which is `LP (RP P)` inside.  Official's
   family `P.rec`/`P.rec_1`/`P.rec_2` has `Prop` motives ONLY
   (`elim_only_at_universe_zero`: the auxiliary block has three types),
   even though `P`'s own constructors alone would not forbid a large
   motive.  The set-level model (`GraphRecRose.lean`,
   `rs_prop_huniq_fails`) shows the restriction is forced at the
   CONTAINER class: `LP (RP P)`'s point decodes as `nil` and as
   `cons pt pt`. -/

set_option autoImplicit false

inductive LP (α : Prop) : Prop where
  | nil : LP α
  | cons : α → LP α → LP α

inductive RP (α : Prop) : Prop where
  | node : α → LP (RP α) → RP α

inductive P : Prop where
  | leaf : P
  | mk : RP P → P

theorem P.useMk : (P.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True) (motive_3 := fun _ => True)
    True.intro (fun _ ih => ih) (fun _ _ ih₁ _ => ih₁) True.intro (fun _ _ _ ih₂ => ih₂)
    (P.mk (RP.node P.leaf LP.nil)) : True) = True.intro := rfl
