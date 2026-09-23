--#export SA.depth

/- Corner case (conformance gap, accept-subset): the REFLEXIVE twin of
   `corner_mutual_redex_other`.  `SA`'s field is `Fn SB`, a reducible
   head whose whnf is the Π `Unit → SB` — a reflexive occurrence of the
   OTHER member.  Official whnf's the domain, walks the Π, finds `SB`
   a valid member application at its codomain and ACCEPTS.

   con-leche DECLINED (exit 2) until lane NESTPOS gave the walk the member
   list (Kernel/Inductives/Positivity.lean; exit 0 since): `normPosDom` was called with
   `SA`'s name only (SumInstall.lean:162 via BlockInstall.lean:191), so
   the domain — which does not mention `SA` — is kept as declared;
   `blockPositivity` sees head `Fn` (not a member) → `.unsupported`.
   Target verdict 0 (same fix: the walk's member list). -/

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
