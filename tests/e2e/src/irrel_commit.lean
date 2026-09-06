/-
The proof-irrelevance COMMIT fixture, in Lean source form (task #161,
residual round 2 — Bool fall-through vs official's commit semantics).

`irrel_commit.ndjson` is the same declaration hand-built over a
stripped `Acc` + `Eq` prelude (scripts/mk_irrel_commit.py); the
elaborated form below is what establishes the OFFICIAL verdict:

  $ lean irrel_commit.lean
  error: (kernel) declaration type mismatch, 'irrelCommit' …

i.e. the official kernel REJECTS, while lech ACCEPTS (exit 0) — with
AND without the pending `proofIrrel` common-type restriction
(branch `agent/proofirrel-check`).

WHY.  At the second argument pair, `F a` versus `F (Acc.intro x g)`,
both comparands are proofs, and their propositions are

  M a                = @Acc.rec … x a                 -- STUCK
  M (Acc.intro x g)  = @Acc.rec … x (Acc.intro x g)   -- iota-fires to `Ps x`

which are not definitionally equal.  So proof irrelevance FAILS in
every kernel.  The official kernel treats that failure as a COMMIT:

  -- type_checker.cpp:1202-1203 / lean4lean TypeChecker.lean:855-856
  let r ← isDefEqProofIrrel tn sn
  if r != .undef then return r == .true

`is_def_eq_core` returns `false` outright — it never reaches
`is_def_eq_app`.  lech's `proofIrrel` returns a `Bool`, and a `false`
falls through to the rest of the cascade, where the spine congruence
succeeds: the head `F` is the same free variable and the argument pair
is `a` versus `Acc.intro x g`, two proofs of the SAME proposition
`Acc r x`, which proof irrelevance equates in every kernel.

`typeCommitControl` is the DISCRIMINATING control: the identical shape
with a `Type`-valued motive.  Then the comparands are not proofs, no
kernel's proof-irrelevance rule fires, nothing commits, and the SAME
congruence decides — official ACCEPTS it (exit 0).  The pair therefore
isolates the divergence to the commit and to nothing else.
-/

theorem irrelCommit {α : Type} {r : α → α → Prop} {x : α}
    (Ps : α → Prop)
    (g : ∀ y, r y x → Acc r y)
    (F : (p : Acc r x) → (@Acc.rec α r (fun _ _ => Prop) (fun z _ _ => Ps z) x p))
    (G : (p : Acc r x) → (@Acc.rec α r (fun _ _ => Prop) (fun z _ _ => Ps z) x p) → α)
    (a : Acc r x) :
    G a (F a) = G (Acc.intro x g) (F (Acc.intro x g)) := rfl

theorem typeCommitControl {α : Type} {r : α → α → Prop} {x : α}
    (Ts : α → Type)
    (g : ∀ y, r y x → Acc r y)
    (F : (p : Acc r x) → (@Acc.rec α r (fun _ _ => Type) (fun z _ _ => Ts z) x p))
    (G : (p : Acc r x) → (@Acc.rec α r (fun _ _ => Type) (fun z _ _ => Ts z) x p) → α)
    (a : Acc r x) :
    G a (F a) = G (Acc.intro x g) (F (Acc.intro x g)) := rfl
