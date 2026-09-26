--#export SA.depth

/- Corner case (conformance gap, accept-subset): the REFLEXIVE twin of
   `corner_mutual_redex_other`.  `SA`'s field is `Fn SB`, a reducible
   head whose whnf is the Π `Unit → SB` — a reflexive occurrence of the
   OTHER member.  Official whnf's the domain, walks the Π, finds `SB`
   a valid member application at its codomain and ACCEPTS.

   con-leche's positivity walk (Kernel/Inductives/Positivity.lean) is
   given the whole member list, so it whnf's the domain, which mentions
   only `SB`.  Today 0, target 0. -/

abbrev Fn (α : Type) : Type := Unit → α

mutual
  inductive SA : Type where
    | leaf : SA
    | node : Fn SB → SA
  inductive SB : Type where
    | wrap : SA → SB
end

noncomputable def SA.depth (a : SA) : Nat :=
  SA.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    0 (fun _ ih => ih () + 1) (fun _ ih => ih + 1) a
