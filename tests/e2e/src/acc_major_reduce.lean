--#export Acc'.idx_def Acc'.idx_beta
/- Task #333 audit: the one place a proof IS reduced — the major premise
of a recursor over an inductive proposition with large elimination and
no K rule.  `Acc'` is an `Acc` clone (one constructor, the data field an
index, the recursive field a `Prop`-valued function); its recursor
eliminates into `Type`, and the value it computes (`Acc'.idx`) reads the
index through the constructor the major head-normalizes to.  The majors
here are proofs that are NOT syntactically constructor applications: a
`def`-proved one (delta) and a β-redex.  Iota must reduce them to
`Acc'.intro`; proof irrelevance cannot help, since the recursor's value
is data.  Today (and in the official kernel): accept.  Target: accept
(the exception stays; see DESIGN.md, task #333). -/
inductive Acc' {α : Type} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : ∀ y, r y x → Acc' r y) : Acc' r x

/-- Large elimination into `Nat`, reading the index. -/
noncomputable def Acc'.idx {r : Nat → Nat → Prop} {x : Nat} (a : Acc' r x) : Nat :=
  Acc'.rec (motive := fun _ _ => Nat) (fun x _ _ => x) a

/-- A proof by `def` (not a theorem: it delta-unfolds). -/
def accDef : Acc' (fun (_ _ : Nat) => False) 3 := Acc'.intro 3 (fun _ h => h.elim)

theorem Acc'.idx_def : Acc'.idx accDef = 3 := rfl

theorem Acc'.idx_beta :
    Acc'.idx ((fun (h : Acc' (fun (_ _ : Nat) => False) 3) => h)
      (Acc'.intro 3 (fun _ h => h.elim))) = 3 := rfl
