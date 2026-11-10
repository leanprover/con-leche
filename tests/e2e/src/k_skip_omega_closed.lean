--#export k_skip_omega_closed
/- Task #552 (the K rule without the index check): a CLOSED proof with
no weak-head normal form once casts reduce unchecked.

`X` is an inhabited proposition, so `propext` gives the closed
`hX : (X → X) = X`.  `ω := fun x : X => (cast hX.symm x) x` and
`Ω := ω (cast hX ω)` then loop: `Ω` β-reduces to
`cast hX.symm (cast hX ω) (cast hX ω)`, and each `cast` is a K-like
`Eq.rec` whose index check fails (`X` against `X → X`), so with the
check the head is stuck, without it the two casts vanish and `Ω`
comes back.

`Ω` is a proof, and proof irrelevance never opens it; what forces its
head normal form is the major premise of `Acc.rec` (not K, not an η
family: the major must reduce to `Acc.intro`).
`k_skip_omega_closed` claims the eliminator's value is `7` by
`Eq.refl`; hand-patched as `k_skip_funext_rfl` (`scripts/splice-rfl.py
k_skip_omega_closed.ndjson k_skip_omega_closed`).

**Verdict.**  Today: reject (exit 1), as official: the major's whnf
stops at the stuck cast.  With the check skipped at closed majors
(`.skipClosed`, `.skipAll`): the major's whnf does not terminate
(timeout).  Target: reject. -/
def X : Prop := Acc (fun _ _ : Nat => False) 0

theorem X_inh : X := Acc.intro 0 (fun _ h => h.elim)

theorem hX : (X → X) = X := propext ⟨fun _ => X_inh, fun x _ => x⟩

def ω : X → X := fun x : X => (cast hX.symm x) x

def Ω : X := ω (cast hX ω)

noncomputable def k_skip_omega_val : Nat :=
  @Acc.rec Nat (fun _ _ => False) (fun _ _ => Nat) (fun _ _ _ => 7) 0 Ω

theorem k_skip_omega_closed : k_skip_omega_val = 7 := sorry
