--#export k_skip_omega_open
/- Task #552 (the K rule without the index check): the Ω loop under a
hypothesis `h : (A → A) = A` for a TYPE `A` — an equation with no
closed proof (no closed `A` makes it true), so only the variant that
skips the check at OPEN majors can loop here.

`ω := fun x : A => (cast h.symm x) x`, `Ω := ω (cast h ω) : A`, a term,
not a proof.  The claim `Ω = cast h ω` makes the checker compare the
two sides; `Ω` β-reduces to `cast h.symm (cast h ω) (cast h ω)`.  With
the index check the cast on `h.symm` is stuck (`A` against `A → A`, an
fvar against a Π-type) and the comparison fails; without it both casts
vanish and `Ω` returns.  Hand-patched as `k_skip_funext_rfl`, the value
`fun A h => Eq.refl (cast h ω)` (`scripts/splice-rfl.py
k_skip_omega_open.ndjson k_skip_omega_open`).

**Verdict.**  Today and with `.skipClosed`: reject (exit 1), as
official.  With `.skipAll`: the comparison does not terminate
(timeout).  Target: reject. -/
theorem k_skip_omega_open (A : Type) (h : (A → A) = A) :
    (fun x : A => (cast h.symm x) x) (cast h (fun x : A => (cast h.symm x) x)) =
      cast h (fun x : A => (cast h.symm x) x) := sorry
