--#export proj_cheap_struct
/-! Projection of an expensive structure (from the Palomar submission
roos-j/lean-spherical, `Auto.Spherical.RS.lintegral_pow_iSup_waveInt_le`:
`Complex.re (∑ ν ∈ Finset.range (2 ^ 17), …)` on both sides, differing only
in an instance argument).  `.re` unfolds on both sides to a `.proj` of
`S u` and `S ()`.  Official's `is_def_eq_core` takes `whnf_core` with
`cheap_proj = true`: the struct is only `whnf_core`'d, stays stuck at `S _`,
and the two projections are compared by their structs, where lazy delta
compares the arguments of `S` (5 kernel unfoldings in all).  Reducing the
struct with full `whnf` evaluates `S`, Θ(2^17) steps through the
tail-recursive `List.range.loop`, beyond the whnf loop's fuel (exit 3). -/
structure C where
  re : Nat
  im : Nat

def N : Nat := 2 ^ 17

def S (_ : Unit) : C := (List.range N).foldr (fun i acc => ⟨i + acc.re, 0⟩) ⟨0, 0⟩

def u : Unit := ()

theorem proj_cheap_struct : (S u).re = (S ()).re := rfl
