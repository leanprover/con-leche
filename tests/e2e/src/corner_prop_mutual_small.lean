--#export MA.const MB.const

/- Corner case: a MUTUAL `Prop` pair at `w = 0`, eliminating into
   `Prop` only.  Official's `elim_only_at_universe_zero` returns true
   at `m_ind_types.size() > 1` before it ever looks at the
   constructors, so both recursors are SMALL; the two theorems fire
   both of them, on both members' constructors and on the
   non-recursive one.  Official ACCEPTS.  The single-member
   two-constructor instance of the same regime is `direct_fix_prop`
   (`Ev`/`Chain'`); this is the `k = 2` one, and the base of the
   forged `corner_mutual_prop_large_bad`. -/

mutual
  inductive MA : Prop where
    | base : MA
    | step : MB → MA
  inductive MB : Prop where
    | step : MA → MB
end

theorem MA.const (h : MA) (p : Prop) (hp : p) : p :=
  MA.rec (motive_1 := fun _ => p) (motive_2 := fun _ => p)
    hp (fun _ ih => ih) (fun _ ih => ih) h

theorem MB.const (h : MB) (p : Prop) (hp : p) : p :=
  MB.rec (motive_1 := fun _ => p) (motive_2 := fun _ => p)
    hp (fun _ ih => ih) (fun _ ih => ih) h
