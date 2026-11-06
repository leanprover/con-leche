module
-- (task #421) user containers for NsH's nested blocks: a plain one and
-- one that is itself nested (through List); NsBox.fin's field reads Fin,
-- which only the generated auxiliary recursor of NsH.NsU reads.
public inductive NsBox (α : Type) : Type where
  | one : α → NsBox α
  | two : α → α → NsBox α
  | fin : Fin 2 → α → NsBox α
public inductive NsRose (α : Type) : Type where
  | node : α → List (NsRose α) → NsRose α
