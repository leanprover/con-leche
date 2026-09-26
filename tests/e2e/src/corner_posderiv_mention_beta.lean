--#export ET.rec ET.rec_1 ET.rec_2
/- Corner case (lane POSDERIV, the item-9 adversarial pass for the
   MEMBER-MENTION check on outside recursor majors): the SECOND auxiliary
   type comes from the container's constructor instantiated at the first
   one's parameters, `List (f α)` at `α := ET`, `f := fun _ => Nat`.
   Whatever official's instantiation leaves there (`(fun _ => Nat) ET`,
   or `Nat` after a β-step), its `is_nested` (inductive.cpp v4.34.0
   :1033–1051) decides on that very syntax, and `restore_nested` puts it
   back verbatim: an auxiliary recursor on it mentions `ET`, or there is
   none.  The stream carries what official generated.  Official 0. -/
inductive EC (α : Type) (f : Type → Type) where
  | mk : List (f α) → EC α f
inductive ET where
  | leaf : ET
  | mk : EC ET (fun _ => Nat) → ET
