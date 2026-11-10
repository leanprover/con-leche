--#export k_skip_open_cast_lit
/- Task #552 (the K rule without the index check): an unchecked cast
moves a term to a type it does not inhabit.  Under `h : Nat = Bool`,
`cast h 5 : Bool` reduces, without the index check (`Nat` against
`Bool`), to the literal `5`, which then sits as the major of `Bool.rec`.
The checker must stay well-behaved: the literal's constructor form
`Nat.succ 4` has no rule in `Bool.rec`, so the redex is stuck.  The
claim `Bool.rec 0 1 (cast h 5) = 0` by `Eq.refl` (hand-patched as
`k_skip_funext_rfl`: `scripts/splice-rfl.py k_skip_open_cast_lit.ndjson
k_skip_open_cast_lit`).

**Verdict.**  Reject (exit 1) at every switch value, as official: no
crash, no internal error. -/
theorem k_skip_open_cast_lit (h : Nat = Bool) :
    @Bool.rec (fun _ => Nat) 0 1 (cast h 5) = 0 := sorry
