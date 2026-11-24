--#export elim elim_mk squash_self squash_sound

/-! Quotients of propositions are types (lean4#15023): `Quot` is declared at
`Sort (max 1 u)` and `Quot.sound`'s equation at `Eq.{max 1 u}`.  `Quot.lift` still reduces on
`Quot.mk`.  Exported with the PR release toolchain of lean4#15023
(`leanprover/lean4-pr-releases:pr-release-15023`) and its `lean4export`, not with the pinned
toolchain of `scripts/export-fixture.sh`, which would write the released form.
`scripts/mk_quot_lifted_fixtures.py` derives the variants from the stream. -/

def elim (s : Squash True) : Nat := Quot.lift (fun _ => 1) (fun _ _ _ => rfl) s

theorem elim_mk : elim (Squash.mk True.intro) = 1 := rfl

theorem squash_self (s : Squash True) : s = s := rfl

theorem squash_sound (s : Squash True) : s = Squash.mk True.intro :=
  Quot.ind (β := fun s => s = Squash.mk True.intro) (fun _ => Quot.sound trivial) s
