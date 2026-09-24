--#export T.rec T2.rec
/- RESTRICT a49: field sorts `imax u v` / `u` against result sorts
   `max 1 (imax u v)` / `max 1 u` (`Level.leq` vs official `is_geq`). -/
universe u v
inductive T (α : Sort u) (β : Sort v) : Sort (max 1 (imax u v)) where
  | mk : (α → β) → T α β
inductive T2 (α : Sort u) : Sort (max 1 u) where
  | mk : α → T2 α
