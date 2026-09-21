--#export P7.rec P7.rec_1

/- Task #279 probe p07: the index DOMAIN mentions a parameter (#227's docketed wrong verdict).  Official (Lean v4.33.0) ACCEPTS. -/
inductive P7 (α : Type) (a₀ : α) : α → Type where
  | mk : List (P7 α a₀ a₀) → P7 α a₀ a₀
