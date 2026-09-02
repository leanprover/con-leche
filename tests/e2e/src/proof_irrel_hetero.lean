/-
The proof-irrelevance heterogeneity fixture, in Lean source form
(task #161, the verdict-relevance round).

`proof_irrel_hetero.ndjson` is the same declaration hand-built over a
stripped `Acc` + `Eq` prelude (scripts/mk_proofirrel_hetero.py) — the
elaborated form below is what establishes the OFFICIAL verdict:

  $ lean proof_irrel_hetero.lean
  error: (kernel) declaration type mismatch, 'propIrrelHetero' …

i.e. the official kernel REJECTS.  `Acc`'s large elimination breaks
algorithmic congruence: `h1`'s type is a stuck `Acc.rec` application
(the major `a` is a variable) while `h2`'s type is the spelling of the
same `Acc.rec`'s iota reduct at the *constructor* major, and the two
are not definitionally equal by the algorithm.  Both are Prop-sorted,
so a proof-irrelevance rule without the final `is_def_eq(t_type,
s_type)` equates `h1` and `h2` and accepts.

`propIrrelHomo` is the positive control: both kernels accept it
(lean4lean: "checked 1 declarations").
-/

theorem propIrrelHetero {α : Type} {r : α → α → Prop} {x : α}
    (Ps : α → Prop)
    (g : ∀ y, r y x → Acc r y)
    (E : (p : Acc r x) → (@Acc.rec α r (fun _ _ => Prop) (fun z _ _ => Ps z) x p) → α)
    (a : Acc r x)
    (h1 : @Acc.rec α r (fun _ _ => Prop) (fun z _ _ => Ps z) x a)
    (h2 : Ps x) :
    E a h1 = E (Acc.intro x g) h2 := rfl

theorem propIrrelHomo {α : Type} {r : α → α → Prop} {x : α}
    (Ps : α → Prop)
    (E : (p : Acc r x) → (@Acc.rec α r (fun _ _ => Prop) (fun z _ _ => Ps z) x p) → α)
    (a : Acc r x)
    (h1 h2 : @Acc.rec α r (fun _ _ => Prop) (fun z _ _ => Ps z) x a) :
    E a h1 = E a h2 := rfl
