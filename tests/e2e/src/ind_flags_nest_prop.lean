--#export FlagNestBox FlagNestEx FlagNestTree FlagNestExTree

/- Task #630: `Prop` blocks nested through `Prop` containers, for the
   feature flags' auxiliary-type rules (lean4 PR #16595).  The official
   kernel's auxiliary type for a nested occurrence `J …` takes
   `isImpredicative` from the block's first type and `hasProjections`
   from `J`, and is checked like any type of the block:
   * `FlagNestTree` nests `FlagNestBox`, a proposition with
     projections: accepted when the block is not impredicative, rejected
     when it is (the auxiliary type would be impredicative with
     projections) — `ind_flags_nest_impred_proj_bad`;
   * `FlagNestExTree` nests `FlagNestEx`, an impredicative proposition
     with a field in `Type`: accepted when the block is impredicative,
     rejected when it is not (the auxiliary type's constructor would
     have a field outside `Prop`) — `ind_flags_nest_bound_bad`.
   The stream here carries no flags; `scripts/mk_ind_flags_install.py`
   patches them in. -/

inductive FlagNestBox (p : Prop) : Prop where
  | mk (h : p)

inductive FlagNestEx (α : Type) (p : α → Prop) : Prop where
  | intro (w : α) (h : p w)

inductive FlagNestTree : Prop where
  | node (b : FlagNestBox FlagNestTree)
  | leaf

inductive FlagNestExTree : Prop where
  | mk (e : FlagNestEx Bool (fun _ => FlagNestExTree))
  | leaf
